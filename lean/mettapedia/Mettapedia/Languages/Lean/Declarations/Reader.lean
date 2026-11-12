import Lean
import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax
import Mettapedia.Languages.Lean.Declarations.NaturalSyntax

/-!
# Reading elaborated Lean inductives as authored declaration syntax

An elaborated inductive type is read into the shared declaration syntax
`InductiveSyntax.Family`: its parameters, indices and sort, and every
constructor's fields in source order with its result type.  The grammar-driven
`.module` reader produces the same syntax, so both front ends meet the same
admission (`IndexedInductive`, `PositiveInductiveBlock`) and the same MeTTa
authoring forms.

Terms keep Lean's global names. Natural literals have a proved compact
arithmetic presentation. Zero, one and an offset `t + 1` keep their constructor
forms, so an index such as `n + 1` is `Nat.succ n`. Dependent function types
retain their binders; a nondependent one is kept as an arrow. Admission is
separate and may refuse a function field or a proposition outside its guard profile.

Besides the syntax, a reading records two facts the consumers need:

* which fields code extraction keeps: a field is erased when its type is a
  proposition, a type or a type former (`erasedType`), the predicate the code
  equation exporter uses for every constant;
* how the type may be eliminated: into any sort when Lean's recursor has its
  own universe parameter for the motive, otherwise into `Prop` only.

The single-family entry point refuses mutual blocks and nested occurrences
by name; `BlockReader` reads those through their recursor motives. Reading
grants no positivity or computation authority; admission supplies those.
-/

set_option autoImplicit false

open Lean Meta Elab

namespace Mettapedia.Languages.Lean.Declarations

/-! The shared declaration syntax, under short names that do not collide with
Lean's own `Term`, `Binder` and `Constructor`. -/
abbrev STerm := Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Term
abbrev SBinder := Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Binder
abbrev SConstructor := Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Constructor
abbrev SFamily := Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Family

/-- Whether a value of this type is erased by code extraction: a proof, a
type, or a type former. -/
def erasedType (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  isTypeFormerType t

/-- How a type may be eliminated, as Lean's recursor allows. -/
inductive Elimination where
  /-- The motive may land in any sort. -/
  | anySort
  /-- The motive lands in `Prop` only. -/
  | propOnly
  deriving DecidableEq, Repr

/-- Why a declaration is not read. -/
inductive Refusal where
  | notInductive (name : String)
  | mutualBlock (names : List String)
  | nestedOccurrences (name : String) (count : Nat)
  | dependentFunctionType (constructor : String) (type : String)
  | unsupportedTerm (constructor : String) (term : String)
  deriving DecidableEq, Repr

/-- A Lean inductive read as authored syntax. -/
structure Reading where
  family : SFamily
  universes : List String
  elimination : Elimination
  /-- For each constructor, in order, whether each field is kept. -/
  keptFields : List (List Bool)
  /-- For each constructor, in order, the proposition of each proof field,
  in weak head normal form (Lean's definitional unfolding to its inductive
  head: `val < n` is `Nat.le (Nat.succ val) n`); `none` for other fields. -/
  proofFields : List (List (Option STerm))
  deriving Repr

abbrev ReadM := ExceptT Refusal MetaM

/-- Names given to the variables of one telescope. -/
abbrev Names := Std.HashMap FVarId String

/-- `Nat.succ` applied `count` times. -/
def successors : Nat → STerm → STerm
  | 0, term => term
  | count + 1, term => .app (.name "Nat.succ") (successors count term)

/-- A raw or `OfNat` natural literal. -/
def natLiteral? (e : Expr) : MetaM (Option Nat) := do
  match e with
  | .lit (.natVal n) => return some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      if (← whnfR (e.getArg! 0)).isConstOf ``Nat then
        if let .lit (.natVal n) := e.getArg! 1 then return some n
    return none

/-- A Lean term as declaration syntax, in a context naming its variables. -/
partial def toTerm (names : Names) (owner : String) (e : Expr)
    (normalizeProjections : Bool := false) : ReadM STerm := do
  let e ← instantiateMVars e
  if let some n ← natLiteral? e then
    return NaturalSyntax.encode n
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if (← whnfR (e.getArg! 0)).isConstOf ``Nat then
      if let some k ← natLiteral? (e.getArg! 5) then
        let term ← toTerm names owner (e.getArg! 4) normalizeProjections
        if k ≤ 1 then return successors k term
        else return .app (.app (.name "Nat.add") term) (NaturalSyntax.encode k)
  if normalizeProjections then
    if let some name := e.getAppFn.constName? then
      if let some projection ← getProjectionFnInfo? name then
        if let some reduced ← unfoldProjInst? e then
          if reduced != e then return ← toTerm names owner reduced true
        let arguments := e.getAppArgs
        if projection.numParams < arguments.size then
          let constructor ← getConstInfoCtor projection.ctorName
          let mut result : STerm := .project constructor.induct.toString projection.i
            (← toTerm names owner arguments[projection.numParams]! true)
          for argument in arguments.extract (projection.numParams + 1) arguments.size do
            result := .app result (← toTerm names owner argument true)
          return result
  match e with
  | .fvar id =>
    match names[id]? with
    | some name => return .name name
    | none => throwThe Refusal (.unsupportedTerm owner (toString (← ppExpr e)))
  | .const c _ => return .name c.toString
  | .sort u => return .name (if u.isZero then "Prop" else "Type")
  | .app f a =>
      return .app (← toTerm names owner f normalizeProjections)
        (← toTerm names owner a normalizeProjections)
  | .proj structureName field record =>
      return .project structureName.toString field (← toTerm names owner record normalizeProjections)
  | .forallE _ domain body _ =>
    if body.hasLooseBVars then
      let taken := names.toList.map (·.2)
      let environment ← getEnv
      let mut serial := 0
      let mut binder := s!"pi{serial}"
      while taken.contains binder || environment.contains binder.toName do
        serial := serial + 1
        binder := s!"pi{serial}"
      let domainTerm ← toTerm names owner domain normalizeProjections
      withLocalDeclD binder.toName domain fun x => do
        return .pi binder domainTerm
          (← toTerm (names.insert x.fvarId! binder) owner (body.instantiate1 x) normalizeProjections)
    else
      return .arrow (← toTerm names owner domain normalizeProjections)
        (← toTerm names owner body normalizeProjections)
  | .mdata _ inner => toTerm names owner inner normalizeProjections
  | _ => throwThe Refusal (.unsupportedTerm owner (toString (← ppExpr e)))

/-- A readable, distinct name for a bound variable. -/
def binderName (fvar : Expr) (fallback : String) (taken : List String) : MetaM String := do
  let user := (← fvar.fvarId!.getDecl).userName.eraseMacroScopes
  let base := if user.isAnonymous || user.hasMacroScopes || user.isInaccessibleUserName
    then fallback else user.toString
  if taken.contains base then return fallback else return base

/-- Name the variables of a telescope, starting from earlier names. -/
def nameAll (names : Names) (taken : List String) (xs : Array Expr) (prefix_ : String) :
    MetaM (Names × List String) := do
  let mut names := names
  let mut taken := taken
  for i in [0:xs.size] do
    let name ← binderName xs[i]! s!"{prefix_}{i}" taken
    names := names.insert xs[i]!.fvarId! name
    taken := taken ++ [name]
  return (names, taken)

def binders (names : Names) (owner : String) (xs : Array Expr) (normalizeTypes : Bool := false) : ReadM (List SBinder) :=
  xs.toList.mapM fun x => do
    let type ← inferType x
    let type ← if normalizeTypes && !(← isProp type) then whnfR type else pure type
    return ⟨names[x.fvarId!]!, ← toTerm names owner type⟩

/-- For each field of a constructor (its parameters excluded), whether code
extraction keeps it.  The code equation exporter reads constructors through
this function, so both consumers share one erasure decision. -/
def keptConstructorFields (c : Name) : MetaM (List Bool) := do
  let info ← getConstInfoCtor c
  forallTelescopeReducing info.type fun xs _ =>
    (xs.extract info.numParams xs.size).toList.mapM fun x => do
      return !(← erasedType (← inferType x))

/-- A proposition in weak head normal form, unless that form is a quotient
primitive stuck at a variable: `s.Nodup` on a multiset unfolds to `Quot.lift`
at `s`, an elimination that has not computed, not a form of the proposition.
Such a proposition is the function applied to its arguments, as written, and
the function is read by its equations. -/
def propositionForm (type : Expr) : MetaM Expr := do
  let normal ← whnfD type
  if let some c := normal.getAppFn.constName? then
    if let some (.quotInfo _) := (← getEnv).find? c then return type
  return normal

/-- Read one constructor, naming its parameters as the family does: its
syntax, which fields are kept, and the propositions of its proof fields. -/
def readConstructor (parameterNames : List String) (c : Name) (normalizeTypes : Bool := false) :
    ReadM (SConstructor × List Bool × List (Option STerm)) := do
  let some (.ctorInfo info) := (← getEnv).find? c
    | throwThe Refusal (.notInductive c.toString)
  let read : ReadM (SConstructor × List Bool × List (Option STerm)) := ExceptT.mk <|
    forallTelescopeReducing info.type fun xs result => ExceptT.run do
      let mut known : Names := {}
      for i in [0:info.numParams] do
        known := known.insert xs[i]!.fvarId! (parameterNames[i]?.getD s!"p{i}")
      let fields := xs.extract info.numParams xs.size
      let (names, _) ← nameAll known parameterNames fields "field"
      let fieldBinders ← binders names c.toString fields normalizeTypes
      let proofs ← fields.toList.mapM fun x => do
        let type ← inferType x
        if ← isProp type then
          return some (← toTerm names c.toString (← propositionForm type) true)
        else return none
      return (⟨c.toString, fieldBinders, ← toTerm names c.toString result⟩,
        ← keptConstructorFields c, proofs)
  read

/-- Read one family shape. This grants no single-family or block admission;
the caller must retain and validate its recursive dependencies. -/
def readFamilyShape (typeName : Name) (normalizeTypes : Bool := false) : MetaM (Except Refusal Reading) := ExceptT.run do
  let some (.inductInfo info) := (← getEnv).find? typeName
    | throwThe Refusal (.notInductive typeName.toString)
  let header : ReadM (List SBinder × List SBinder × STerm) := ExceptT.mk <|
    forallTelescopeReducing info.type fun xs sort => ExceptT.run do
      let params := xs.extract 0 info.numParams
      let indices := xs.extract info.numParams xs.size
      let (names, taken) ← nameAll {} [] params "p"
      let (names, _) ← nameAll names taken indices "index"
      return (← binders names typeName.toString params,
        ← binders names typeName.toString indices,
        ← toTerm names typeName.toString sort)
  let (parameters, indices, sort) ← header
  let parameterNames := parameters.map (·.name)
  let constructors ← info.ctors.mapM (fun name => readConstructor parameterNames name normalizeTypes)
  let recursor ← getConstInfoRec (typeName ++ `rec)
  let elimination :=
    if recursor.levelParams.length > info.levelParams.length then .anySort else .propOnly
  return {
    family := ⟨typeName.toString, parameters, indices, sort, constructors.map (·.1)⟩
    universes := info.levelParams.map toString
    elimination
    keptFields := constructors.map (·.2.1)
    proofFields := constructors.map (·.2.2) }

/-- The original single-family profile. Block reading is a separate entry
point, so previously qualified single-family exports remain stable. -/
def read (typeName : Name) (normalizeTypes : Bool := false) : MetaM (Except Refusal Reading) := do
  let some (.inductInfo info) := (← getEnv).find? typeName
    | return .error (.notInductive typeName.toString)
  if info.all.length > 1 then return .error (.mutualBlock (info.all.map toString))
  if info.numNested > 0 then return .error (.nestedOccurrences typeName.toString info.numNested)
  readFamilyShape typeName normalizeTypes

/-! ## Readings as terms -/

deriving instance ToExpr for Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Term
deriving instance ToExpr for Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Binder
deriving instance ToExpr for Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Constructor
deriving instance ToExpr for Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax.Family

deriving instance ToExpr for Elimination
deriving instance ToExpr for Reading

/-- `lean_reading% T` is the whole reading of the inductive `T`. -/
elab "lean_reading% " id:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  match ← read name with
  | .ok reading => return toExpr reading
  | .error refusal => throwError "lean_reading%: {name} is not read: {repr refusal}"

/-- `lean_family% T` is the declaration syntax read from the inductive `T`. -/
elab "lean_family% " id:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  match ← read name with
  | .ok reading =>
    return toExpr reading.family
  | .error refusal => throwError "lean_family%: {name} is not read: {repr refusal}"

end Mettapedia.Languages.Lean.Declarations
