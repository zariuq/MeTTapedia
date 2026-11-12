import Mettapedia.Languages.Lean.Declarations.Reader
import Mettapedia.Languages.Lean.Declarations.QuotientProfile

/-!
# Lean terms and equations as first-order data, types kept

The Egal interpretation reads closed Lean terms and the statements of
equation theorems as first-order applications of constants. Every argument is
kept, type arguments included, because Egal's families take their parameters
as sets.

* A natural literal (`5`, `OfNat.ofNat Nat 5 _`) is the numeral `num 5`;
  the constructor `Nat.zero` stays a constructor.
* A class method applied to a closed instance is the instance's field
  (`unfoldProjInst?`), so `a + b` on naturals is `Nat.add a b`, as in the
  code-equation export.
* A constant applied to arguments is `app c args`, its universe levels
  dropped after profile checks. Quotient primitives require successor
  universes: their Type-carrier interpretation does not cover Prop carriers.
* A bound variable is `var x`; a variable or an abstraction applied to
  arguments is `apv f args`.
* An abstraction `fun x : T => b` is `lam x T b`, and a non-dependent
  function type `A → B` is `arrow A B`.

An equation theorem `∀ binders, lhs = rhs` is read with its binders: a type
variable `α : Type u`, or a term variable `x : T`.

* A function constant applied to fewer arguments than its type takes is
  eta-expanded (`Nat.add` is `fun x y => Nat.add x y`).
* A structure projection whose structure is not a constructor application
  (an instance variable) stays a projection: `Add.add α inst`, with any
  further arguments applied to its value.
* An instance binder is a term binder of its class.
* An equation between functions is read pointwise: its binders are extended
  by the arguments both sides take (`List.sum l = List.foldr … l`); the
  number of such arguments is recorded, since the statement is Lean's up to
  function extensionality.

* A proposition is read in weak head normal form (`¬p` is `p → False`),
  unless that form is a quotient primitive stuck at a variable: then it stays
  the function applied to its arguments (`propositionForm`).
* A sort other than `Prop` is `sort L`, its level kept: a level parameter,
  a numeral, or a successor (`Sort u` is the type of a matcher's motive).
* `let x := v; b` and `have x := v; b` are read as `b` with `v` for `x`.
* A hypothesis binder `h : P` of an equation theorem is kept as `hyp h P`:
  Lean states an equation after an overlapping pattern under the hypotheses
  that the earlier patterns do not match.

Anything else is refused, with its reason: binders of other sorts, and
terms that are not first-order applications.

A proof is irrelevant as a value, and is written `proof`.  Where Lean's proof
term is an abstraction, a hypothesis or a theorem applied to arguments
(`Quot.sound` and `propext` among the theorems), or a projection onto a proof
field, the term is kept beside it (`proofBy`): it says which theorems the
proposition follows from, so that a target can follow the same steps.
-/

open Lean Meta

namespace Mettapedia.Languages.Lean.Declarations

/-- A universe level: a parameter, a numeral, or a successor. -/
inductive FLevel where
  | param (name : String)
  | num (n : Nat)
  | succ (level : FLevel)
  deriving Repr, BEq, Inhabited

/-- A level as `FLevel`, when it is built from parameters, zero and successors. -/
def FLevel.of? : Level → Option FLevel
  | .zero => some (.num 0)
  | .param u => some (.param u.toString)
  | .succ l => match FLevel.of? l with
    | some (.num n) => some (.num (n + 1))
    | some other => some (.succ other)
    | none => none
  | _ => none

/-- A first-order Lean term with its type arguments kept. -/
inductive FTerm where
  | var (name : String)
  | num (n : Nat)
  | app (c : Name) (args : List FTerm)
  | apv (function : FTerm) (args : List FTerm)
  | lam (name : String) (type : FTerm) (body : FTerm)
  | arrow (domain codomain : FTerm)
  /-- A dependent function type `(x : A) → B`. -/
  | pi (name : String) (domain codomain : FTerm)
  /-- The sort `Prop`. -/
  | prop
  /-- A sort `Sort L` other than `Prop`, with its level. -/
  | sort (level : FLevel)
  /-- A proof: its value is irrelevant (in the set model, 0). -/
  | proof
  /-- A proof with the term Lean records for it.  Its value is as irrelevant
  as `proof`'s; the term says how the proposition follows. -/
  | proofBy (term : FTerm)
  /-- In a proof term: a theorem applied to as many arguments as its
  statement binds. -/
  | cite (name : Name) (args : List FTerm)
  deriving Repr, BEq, Inhabited

/-- A binder of an equation theorem. -/
inductive FBinder where
  /-- `α : Type u`, with `u` a level parameter or `0`. -/
  | type (name : String) (level : String)
  /-- `x : T`. -/
  | term (name : String) (type : FTerm)
  /-- `α : Sort u`, with `u` a level parameter. -/
  | sort (name : String) (level : String)
  /-- A hypothesis `h : P`, `P` a proposition. -/
  | hyp (name : String) (proposition : FTerm)
  deriving Repr, BEq, Inhabited

/-- The statement of an equation theorem `∀ binders, lhs = rhs`, both sides
of type `type`. -/
structure FEquation where
  name : Name
  binders : List FBinder
  type : FTerm
  lhs : FTerm
  rhs : FTerm
  /-- How many arguments the pointwise reading added. -/
  pointwise : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Reading refuses with a reason. -/
abbrev FReadM := ExceptT String MetaM

/-- Read a term in a context naming its variables. -/
partial def readTerm (names : Names) (e : Expr) : FReadM FTerm := do
  let e := (← instantiateMVars e).consumeMData
  if let .sort u := e then
    if e.isProp then return .prop
    match FLevel.of? u with
    | some level => return .sort level
    | none => throwThe String s!"a sort at a level outside parameters and successors: {← ppExpr e}"
  if ← Meta.isProof e then
    let attempt : MetaM (Except String FTerm) :=
      try (readProof names e).run catch _ => pure (.error "not readable")
    match ← (monadLift attempt : FReadM (Except String FTerm)) with
    | .ok term => return .proofBy term
    | .error _ => return .proof
  -- `let x := v; b` and `have x := v; b`: the binding `(fun x => b) v`, so
  -- that `v` is computed once however often `b` uses `x`.
  if let .letE binderName type value body _ := e then
    return ← readBinding names type value (.lam binderName type body .default)
  if e.isAppOfArity ``letFun 4 then
    return ← readBinding names (e.getArg! 0) (e.getArg! 2) (e.getArg! 3)
  -- A proposition, in weak head normal form: `¬p` is `p → False`, `a < b` on
  -- naturals is `Nat.le (a + 1) b`.
  if ← Meta.isProp e then
    let e' ← propositionForm e
    -- Not when it only exposes a projection of an instance variable.
    if e' != e && !e'.getAppFn.isProj then return ← readTerm names e'
  -- A type given by a definition (`DecidableEq α`), in weak head normal form.
  -- (A proposition's form was decided above.)
  if let some c := e.getAppFn.constName? then
    if let some (.defnInfo _) := (← getEnv).find? c then
      if (← Meta.isType e) && !(← Meta.isProp e) then
        let e' ← whnfD e
        if e' != e && !e'.getAppFn.isProj then return ← readTerm names e'
  if e.isConstOf ``Nat.zero then return .app ``Nat.zero []
  if let some n ← natLiteral? e then return .num n
  match e with
  | .lam binderName type body _ =>
      let typeTerm ← readTerm names type
      Meta.withLocalDeclD binderName type fun x => do
        let name ← binderName' names x
        let body ← readTerm (names.insert x.fvarId! name) (body.instantiate1 x)
        return .lam name typeTerm body
  | .forallE binderName domain body _ =>
      if body.hasLooseBVars then
        let domainTerm ← readTerm names domain
        Meta.withLocalDeclD binderName domain fun x => do
          let name ← binderName' names x
          return .pi name domainTerm (← readTerm (names.insert x.fvarId! name) (body.instantiate1 x))
      else
        return .arrow (← readTerm names domain) (← readTerm names body)
  | _ =>
  match e.getAppFn.consumeMData with
  | .fvar id =>
    let some name := names[id]? | throwThe String s!"an unnamed variable: {← ppExpr e}"
    if e.getAppNumArgs == 0 then return .var name
    return .apv (.var name) (← e.getAppArgs.toList.mapM (readTerm names))
  | .lam .. => readTerm names e.headBeta
  | .const c levels =>
    if let some reason ← QuotientProfile.refusal? c levels then
      throwThe String reason
    -- A constant applied to fewer arguments than it takes: a function, a
    -- constructor, or a family of propositions used as a value (`Nat.le`).
    if (← whnfD (← inferType e)).isForall then
      let expanded ← etaExpand e
      if expanded != e then return ← readTerm names expanded
    if let some info ← getProjectionFnInfo? c then
      if let some e' ← unfoldProjInst? e then
        if e'.getAppFn.constName? != some c then return ← readTerm names e'
      let args := e.getAppArgs
      let own := info.numParams + 1
      if args.size < own then
        throwThe String s!"a projection without its structure: {← ppExpr e}"
      let head := FTerm.app c (← (args.extract 0 own).toList.mapM (readTerm names))
      if args.size == own then return head
      return .apv head (← (args.extract own args.size).toList.mapM (readTerm names))
    return .app c (← e.getAppArgs.toList.mapM (readTerm names))
  | _ => throwThe String s!"not a first-order application: {← ppExpr e}"
where
  /-- A binding of `value` in `body` (a function of the bound variable).  A
  proof or a type is put in place: proofs are irrelevant and types are not
  computed. -/
  readBinding (names : Names) (type value body : Expr) : FReadM FTerm := do
    if (← Meta.isProp type) || (← Meta.isType value) then
      return ← readTerm names (mkApp body value).headBeta
    let .lam .. := body.consumeMData
      | return ← readTerm names (mkApp body value).headBeta
    return .apv (← readTerm names body.consumeMData) [← readTerm names value]
  /-- A readable name for a bound variable, distinct from the names in use. -/
  binderName' (names : Names) (x : Expr) : MetaM String := do
    let taken := names.toList.map (·.2)
    binderName x s!"x{taken.length}" taken
  /-- Read a proof by the term Lean records for it: abstractions, and
  hypotheses, theorems and projections onto proof fields applied to
  arguments.  A theorem is applied to as many arguments as its statement
  binds (fewer are eta-expanded).  Anything else is refused. -/
  readProof (names : Names) (e : Expr) : FReadM FTerm := do
    let e := (← instantiateMVars e).consumeMData
    if let .letE _ _ value body _ := e then
      return ← readProof names (body.instantiate1 value)
    if e.isAppOfArity ``letFun 4 then
      return ← readProof names (mkApp (e.getArg! 3) (e.getArg! 2)).headBeta
    if let .lam binderName type body _ := e then
      let typeTerm ← readTerm names type
      return ← Meta.withLocalDeclD binderName type fun x => do
        let name ← binderName' names x
        return .lam name typeTerm (← readProof (names.insert x.fvarId! name) (body.instantiate1 x))
    let readArgument (a : Expr) : FReadM FTerm := do
      if ← Meta.isProof a then readProof names a else readTerm names a
    match e.getAppFn.consumeMData with
    | .fvar id =>
      let some name := names[id]? | throwThe String s!"an unnamed hypothesis: {← ppExpr e}"
      if e.getAppNumArgs == 0 then return .var name
      return .apv (.var name) (← e.getAppArgs.toList.mapM readArgument)
    | .lam .. => readProof names e.headBeta
    | .const c levels =>
      let info ← getConstInfo c
      let citable ← match info with
        | .thmInfo _ => pure true
        | .axiomInfo _ => pure (c == ``propext || c == ``Quot.sound)
        | _ => pure (← getProjectionFnInfo? c).isSome
      unless citable do
        throwThe String s!"a proof by {c}, which is not a theorem"
      -- As the quotient primitives: only instances at carriers in `Type`.
      if c == ``Quot.sound then
        for level in levels do
          unless level.normalize matches .succ _ do
            throwThe String s!"Quot.sound at level {level}, which is not a successor"
      let arity := info.type.getForallBinderNames.length
      let args := e.getAppArgs
      if args.size < arity then
        let expanded ← forallBoundedTelescope (← inferType e) (some (arity - args.size)) fun xs _ =>
          mkLambdaFVars xs (mkAppN e xs)
        unless expanded.isLambda do
          throwThe String s!"{c} applied to fewer arguments than its statement binds"
        return ← readProof names expanded
      let own ← (args.extract 0 arity).toList.mapM readArgument
      if args.size == arity then return .cite c own
      return .apv (.cite c own) (← (args.extract arity args.size).toList.mapM readArgument)
    | _ => throwThe String s!"a proof outside the readable profile: {← ppExpr e}"

/-- Read the statement of a theorem: as `readTerm`, except that a proposition
given by a definition that is not an abbreviation (`Final s`, `Presents w s st`)
stays folded, under `∀`, implication, `∧` and `∃`. With `projections`, a
proposition whose head is a structure projection (`a < b` is `LT.lt` at an
instance) is read as a term reads it, in its proposition form
(`Nat.le (a + 1) b`): a theorem cited from a proof term then states its
hypotheses as the definitions that cite it state theirs. -/
partial def readStatement (names : Names) (e : Expr) (projections : Bool := false) : FReadM FTerm := do
  let e := (← instantiateMVars e).consumeMData
  match e with
  | .forallE binderName domain body _ =>
      if body.hasLooseBVars then
        let domainTerm ← readTerm names domain
        Meta.withLocalDeclD binderName domain fun x => do
          let name ← readTerm.binderName' names x
          return .pi name domainTerm
            (← readStatement (names.insert x.fvarId! name) (body.instantiate1 x) projections)
      else
        return .arrow (← readStatement names domain projections) (← readStatement names body projections)
  | _ =>
    if let some c := e.getAppFn.constName? then
      if let some (.defnInfo _) := (← getEnv).find? c then
        unless (← isReducible c) || (projections && (← getEnv).isProjectionFn c) do
          return .app c (← e.getAppArgs.toList.mapM (readTerm names))
    if e.isAppOfArity ``And 2 then
      return .app ``And [← readStatement names (e.getArg! 0) projections,
        ← readStatement names (e.getArg! 1) projections]
    if e.isAppOfArity ``Exists 2 then
      if let .lam binderName domain body _ := (e.getArg! 1).consumeMData then
        let domainTerm ← readTerm names domain
        return ← Meta.withLocalDeclD binderName domain fun x => do
          let name ← readTerm.binderName' names x
          return .app ``Exists [← readTerm names (e.getArg! 0),
            .lam name domainTerm
              (← readStatement (names.insert x.fvarId! name) (body.instantiate1 x) projections)]
    readTerm names e

/-- The level of `Type u`, when `u` is a parameter or `0`. -/
def typeLevel? : Level → Option String
  | .succ .zero => some "0"
  | .succ (.param u) => some u.toString
  | _ => none

/-- Read a declaration's actual binders and result type. -/
def readSignature (type : Expr) : FReadM (List FBinder × FTerm) := do
  let go : MetaM (Except String (List FBinder × FTerm)) := forallTelescope type fun xs body => do
    let (names, _) ← nameAll {} [] xs "x"
    ExceptT.run do
      let binders ← xs.toList.mapM fun x => do
        let name := names[x.fvarId!]!
        let ty ← inferType x
        if let .sort u := ty then
          if u.isZero then return FBinder.term name .prop
          if let .param l := u then return FBinder.sort name l.toString
          match typeLevel? u with
          | some level => return FBinder.type name level
          | none => throwThe String s!"a binder of sort {u}: {name}"
        if ← isProp ty then return FBinder.hyp name (← readTerm names ty)
        return FBinder.term name (← readTerm names ty)
      return (binders, ← readTerm names body)
  ExceptT.mk go

/-- Read an equation, optionally at successor-universe instances of its
actual declaration. The exporter records this specialization explicitly. -/
def readEquation (thm : Name) (typeProfile : Bool := false) : FReadM FEquation := do
  let statement ← if typeProfile then pure (← QuotientProfile.typeInstance thm).1
    else pure (← getConstInfo thm).type
  let go : MetaM (Except String FEquation) := forallTelescope statement fun xs body => do
    let (names, _) ← nameAll {} [] xs "x"
    ExceptT.run do
      let binders ← xs.toList.mapM fun x => do
        let name := names[x.fvarId!]!
        let ty ← inferType x
        if let .sort u := ty then
          if u.isZero then return FBinder.term name .prop
          if let .param l := u then return FBinder.sort name l.toString
          match typeLevel? u with
          | some level => return FBinder.type name level
          | none => throwThe String s!"a binder of sort {u}: {name}"
        if ← isProp ty then return FBinder.hyp name (← readTerm names ty)
        return FBinder.term name (← readTerm names ty)
      let some (ty, lhs, rhs) := body.eq? | throwThe String s!"not an equation: {thm}"
      -- The left side is the function applied to its patterns, never unfolded.
      let readLhs (names : Names) (e : Expr) : FReadM FTerm := do
        match e.getAppFn.consumeMData with
        | .const c _ => return .app c (← e.getAppArgs.toList.mapM (readTerm names))
        | _ => readTerm names e
      -- An equation between functions, read pointwise.
      let pointwise : MetaM (Except String FEquation) :=
        forallTelescopeReducing ty fun ys result => do
          let (names, _) ← nameAll names (names.toList.map (·.2)) ys "y"
          ExceptT.run do
            let extra ← ys.toList.mapM fun y => do
              return FBinder.term names[y.fvarId!]! (← readTerm names (← inferType y))
            return { name := thm, binders := binders ++ extra, type := ← readTerm names result,
                     lhs := ← readLhs names (mkAppN lhs ys).headBeta,
                     rhs := ← readTerm names (mkAppN rhs ys).headBeta,
                     pointwise := ys.size }
      ExceptT.mk pointwise
  ExceptT.mk go

/-- Read a closed term with its type. -/
def readClosed (e : Expr) : FReadM (FTerm × FTerm) := do
  return (← readTerm {} e, ← readTerm {} (← inferType e))

/-- Namespaces left out of Egal identifiers: a carried development's own
namespace, so that `Mettapedia.Machines.CEK.evalV` is `Lean_CEK_evalV`. -/
def egalDroppedPrefixes : List String := ["Mettapedia.Machines."]

/-- A Lean name without the prefix Lean gives private declarations
(`_private.<module>.0.`), which depends on the module, not the declaration. -/
def withoutPrivatePrefix (name : String) : String :=
  if name.startsWith "_private." then
    match name.splitOn ".0." with
    | _ :: rest@(_ :: _) => ".0.".intercalate rest
    | _ => name
  else name

/-- The Egal identifier of a Lean name: `Lean_` then its components joined by
`_`, other characters spelled by their code points; a private prefix and the
namespaces of `egalDroppedPrefixes` are left out. -/
def egalIdent (name : String) : String :=
  let name := withoutPrivatePrefix name
  let name := match egalDroppedPrefixes.find? (name.startsWith ·) with
    | some p => (name.drop p.length).toString
    | none => name
  "Lean_" ++ String.join (name.toList.map fun c =>
    if c == '.' then "_"
    else if c.isAlphanum && c.toNat < 128 then c.toString
    else if c == '_' then "_"
    else s!"u{c.toNat}")

/-- The Egal identifier of a bound variable (`v_`) or a universe level
parameter (`l_`); the level `0` is itself. -/
def egalVar (name : String) : String := "v_" ++ (egalIdent name).drop 5
def egalLevel (level : String) : String :=
  if level == "0" then level else "l_" ++ (egalIdent level).drop 5

/-! ## As MeTTa atoms

Variables and levels are written as Egal identifiers. -/

/-- A level as an atom: `(lvl l_u)`, `(lvl k)`, `(lsucc L)`. -/
def FLevel.atom : FLevel → String
  | .param u => s!"(lvl {egalLevel u})"
  | .num n => s!"(lvl {n})"
  | .succ l => s!"(lsucc {FLevel.atom l})"

/-- A term as an atom: `(var x)`, `(num n)`, `(app c (args ..))`,
`(apv f (args ..))`, `(lam x T b)`, `(arrow A B)`. -/
partial def FTerm.atom : FTerm → String
  | .var x => s!"(var {egalVar x})"
  | .num n => s!"(num {n})"
  | .app c args => s!"(app {c} ({" ".intercalate (args.map FTerm.atom)}))"
  | .apv f args => s!"(apv {f.atom} ({" ".intercalate (args.map FTerm.atom)}))"
  | .lam x type body => s!"(lam {egalVar x} {type.atom} {body.atom})"
  | .arrow domain codomain => s!"(arrow {domain.atom} {codomain.atom})"
  | .pi x domain codomain => s!"(pi {egalVar x} {domain.atom} {codomain.atom})"
  | .prop => "(prop)"
  | .sort level => s!"(sort {level.atom})"
  | .proof | .proofBy _ => "(proof)"
  | .cite c args => s!"(cite {c} ({" ".intercalate (args.map FTerm.atom)}))"

/-- A term as an atom with its proof terms written out: a proof Lean's term
is kept for is `(by term)`, and a theorem applied to its arguments is
`(cite thm (args ..))`. -/
partial def FTerm.atomWithProofs : FTerm → String
  | .var x => s!"(var {egalVar x})"
  | .num n => s!"(num {n})"
  | .app c args => s!"(app {c} ({" ".intercalate (args.map FTerm.atomWithProofs)}))"
  | .apv f args => s!"(apv {f.atomWithProofs} ({" ".intercalate (args.map FTerm.atomWithProofs)}))"
  | .lam x type body => s!"(lam {egalVar x} {type.atomWithProofs} {body.atomWithProofs})"
  | .arrow domain codomain => s!"(arrow {domain.atomWithProofs} {codomain.atomWithProofs})"
  | .pi x domain codomain => s!"(pi {egalVar x} {domain.atomWithProofs} {codomain.atomWithProofs})"
  | .prop => "(prop)"
  | .sort level => s!"(sort {level.atom})"
  | .proof => "(proof)"
  | .proofBy term => s!"(by {term.atomWithProofs})"
  | .cite c args => s!"(cite {c} ({" ".intercalate (args.map FTerm.atomWithProofs)}))"

/-- The proofs of a term in the order its atom writes them: for each, the
term Lean records, when it was read. -/
partial def FTerm.proofTerms : FTerm → List (Option FTerm)
  | .var _ | .num _ | .prop | .sort _ => []
  | .app _ args | .cite _ args => args.flatMap FTerm.proofTerms
  | .apv f args => (f :: args).flatMap FTerm.proofTerms
  | .lam _ type body => type.proofTerms ++ body.proofTerms
  | .arrow domain codomain | .pi _ domain codomain => domain.proofTerms ++ codomain.proofTerms
  | .proof => [none]
  | .proofBy term => [some term]

/-- The theorems a term's proofs cite, in order of first use. -/
partial def FTerm.cited : FTerm → List Name
  | .var _ | .num _ | .prop | .sort _ | .proof => []
  | .app _ args => args.foldl (fun acc a => acc ++ (a.cited.filter (!acc.contains ·))) []
  | .cite c args => args.foldl (fun acc a => acc ++ (a.cited.filter (!acc.contains ·))) [c]
  | .apv f args => (f :: args).foldl (fun acc a => acc ++ (a.cited.filter (!acc.contains ·))) []
  | .lam _ type body => [type, body].foldl (fun acc a => acc ++ (a.cited.filter (!acc.contains ·))) []
  | .arrow domain codomain | .pi _ domain codomain =>
      [domain, codomain].foldl (fun acc a => acc ++ (a.cited.filter (!acc.contains ·))) []
  | .proofBy term => term.cited

def FBinder.atom : FBinder → String
  | .type x level => s!"(type {egalVar x} {egalLevel level})"
  | .sort x level => s!"(sort {egalVar x} {egalLevel level})"
  | .term x ty => s!"(term {egalVar x} {ty.atom})"
  | .hyp x proposition => s!"(hyp {egalVar x} {proposition.atom})"

/-- `(LeanEquation thm (binders ..) type lhs rhs)`, and `(LeanPointwise thm k)`
when the reading added `k` arguments. -/
def FEquation.atom (eqn : FEquation) : String :=
  s!"(LeanEquation {eqn.name} ({" ".intercalate (eqn.binders.map FBinder.atom)}) " ++
    s!"{eqn.type.atom} {eqn.lhs.atom} {eqn.rhs.atom})" ++
    (if eqn.pointwise == 0 then "" else s!"\n(LeanPointwise {eqn.name} {eqn.pointwise})")

/-- The constants a term applies, in order of first use. -/
partial def FTerm.constants : FTerm → List Name
  | .var _ | .num _ => []
  | .app c args => args.foldl (fun acc a => acc ++ (a.constants.filter (!acc.contains ·)))
      (if c.isAnonymous then [] else [c])
  | .apv f args => (f :: args).foldl (fun acc a => acc ++ (a.constants.filter (!acc.contains ·))) []
  | .lam _ type body => [type, body].foldl (fun acc a => acc ++ (a.constants.filter (!acc.contains ·))) []
  | .arrow domain codomain =>
      [domain, codomain].foldl (fun acc a => acc ++ (a.constants.filter (!acc.contains ·))) []
  | .pi _ domain codomain =>
      [domain, codomain].foldl (fun acc a => acc ++ (a.constants.filter (!acc.contains ·))) []
  -- A proof's term adds no function to the closure: what it cites is
  -- recorded separately (`FTerm.cited`).
  | .prop | .proof | .proofBy _ | .cite _ _ | .sort _ => []

end Mettapedia.Languages.Lean.Declarations
