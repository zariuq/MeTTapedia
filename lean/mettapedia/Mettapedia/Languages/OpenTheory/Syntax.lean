import Mathlib.Data.List.GetD

/-!
# OpenTheory source syntax and checked canonical terms

This file models the typed term syntax used by OpenTheory at revision
`f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`.  In particular, it follows
`src/Name.sml`, `src/TypeTerm.sml`, and the alpha comparison in `src/Term.sml`.

`SourceTerm` is deliberately untrusted.  Constants and variables carry source
type annotations, while applications can be ill typed.  Symbol identity also
retains the provenance variants used by OpenTheory.  Only `SourceTerm.check`
produces a `CanonicalTerm`: a de Bruijn term together with evidence that its
type checker succeeds.

At this raw-syntax boundary, terms stored inside symbol provenance are
identity-bearing payloads.  Upstream OpenTheory provenance contains terms that
were already constructed by its typed constructors; `SourceTerm.check` validates
the displayed term but does not recursively validate provenance payloads or
definition/theory-state admissibility.  Those checks belong at the later
kernel-state ingress.
-/

namespace Mettapedia.Languages.OpenTheory

/-- An OpenTheory name is a namespace followed by one component. -/
structure Name where
  namespaceComponents : List String
  component : String
deriving Repr, DecidableEq

/-- A typed variable, identified by both its name and its type. -/
structure Var (Ty : Type) where
  name : Name
  ty : Ty
deriving Repr

/-!
OpenTheory places definitions directly in the provenance of type operators and
constants.  These declarations are therefore mutually recursive with types
and terms.  Runtime sharing identifiers from `TypeTerm.sml` are intentionally
absent: they are caches, not part of structural source identity.
-/

mutual
  inductive Ty where
    | var : Name → Ty
    | op : TypeOp → List Ty → Ty
  deriving Repr

  inductive TypeOp where
    | mk : Name → TypeOpProvenance → TypeOp
  deriving Repr

  inductive TypeOpProvenance where
    | undefined
    | defined : SourceTerm → List Name → TypeOpProvenance
  deriving Repr

  inductive Const where
    | mk : Name → ConstProvenance → Const
  deriving Repr

  inductive ConstProvenance where
    | undefined
    | defined : SourceTerm → ConstProvenance
    | abstraction : TypeOp → ConstProvenance
    | representation : TypeOp → ConstProvenance
  deriving Repr

  /-- Untrusted, source-facing typed syntax.  Application typing is unchecked. -/
  inductive SourceTerm where
    | const : Const → Ty → SourceTerm
    | var : Name → Ty → SourceTerm
    | app : SourceTerm → SourceTerm → SourceTerm
    | abs : Name → Ty → SourceTerm → SourceTerm
  deriving Repr
end

/-!
The automatically derived Boolean equality for a mutually inductive family
does not expose the recursive reduction needed here.  These transparent
functions instead implement the structural comparisons in `TypeTerm.sml`,
including recursive provenance.
-/

mutual
  def Ty.same : Ty → Ty → Bool
    | .var left, .var right => decide (left = right)
    | .op leftOp leftArgs, .op rightOp rightArgs =>
        TypeOp.same leftOp rightOp && Ty.listSame leftArgs rightArgs
    | _, _ => false
  termination_by left _ => sizeOf left

  def Ty.listSame : List Ty → List Ty → Bool
    | [], [] => true
    | left :: lefts, right :: rights => Ty.same left right && Ty.listSame lefts rights
    | _, _ => false
  termination_by left _ => sizeOf left

  def TypeOp.same : TypeOp → TypeOp → Bool
    | .mk leftName leftProvenance, .mk rightName rightProvenance =>
        decide (leftName = rightName) &&
          TypeOpProvenance.same leftProvenance rightProvenance
  termination_by left _ => sizeOf left

  def TypeOpProvenance.same : TypeOpProvenance → TypeOpProvenance → Bool
    | .undefined, .undefined => true
    | .defined leftPredicate leftVars, .defined rightPredicate rightVars =>
        SourceTerm.same leftPredicate rightPredicate && decide (leftVars = rightVars)
    | _, _ => false
  termination_by left _ => sizeOf left

  def Const.same : Const → Const → Bool
    | .mk leftName leftProvenance, .mk rightName rightProvenance =>
        decide (leftName = rightName) && ConstProvenance.same leftProvenance rightProvenance
  termination_by left _ => sizeOf left

  def ConstProvenance.same : ConstProvenance → ConstProvenance → Bool
    | .undefined, .undefined => true
    | .defined leftDefinition, .defined rightDefinition =>
        SourceTerm.same leftDefinition rightDefinition
    | .abstraction leftOp, .abstraction rightOp => TypeOp.same leftOp rightOp
    | .representation leftOp, .representation rightOp => TypeOp.same leftOp rightOp
    | _, _ => false
  termination_by left _ => sizeOf left

  def SourceTerm.same : SourceTerm → SourceTerm → Bool
    | .const leftConst leftTy, .const rightConst rightTy =>
        Const.same leftConst rightConst && Ty.same leftTy rightTy
    | .var leftName leftTy, .var rightName rightTy =>
        decide (leftName = rightName) && Ty.same leftTy rightTy
    | .app leftFunction leftArgument, .app rightFunction rightArgument =>
        SourceTerm.same leftFunction rightFunction &&
          SourceTerm.same leftArgument rightArgument
    | .abs leftName leftTy leftBody, .abs rightName rightTy rightBody =>
        decide (leftName = rightName) && Ty.same leftTy rightTy &&
          SourceTerm.same leftBody rightBody
    | _, _ => false
  termination_by left _ => sizeOf left
end

/-- Transparent structural comparison of typed variables. -/
def sourceVarSame (left right : Var Ty) : Bool :=
  decide (left.name = right.name) && Ty.same left.ty right.ty

mutual
  @[simp] theorem Ty.same_eq_true_iff (left right : Ty) :
      Ty.same left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [Ty.same, TypeOp.same_eq_true_iff, Ty.listSame_eq_true_iff]
  termination_by structural left

  @[simp] theorem Ty.listSame_eq_true_iff (left right : List Ty) :
      Ty.listSame left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [Ty.listSame, Ty.same_eq_true_iff, Ty.listSame_eq_true_iff]
  termination_by structural left

  @[simp] theorem TypeOp.same_eq_true_iff (left right : TypeOp) :
      TypeOp.same left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [TypeOp.same, TypeOpProvenance.same_eq_true_iff]
  termination_by structural left

  @[simp] theorem TypeOpProvenance.same_eq_true_iff
      (left right : TypeOpProvenance) :
      TypeOpProvenance.same left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [TypeOpProvenance.same, SourceTerm.same_eq_true_iff]
  termination_by structural left

  @[simp] theorem Const.same_eq_true_iff (left right : Const) :
      Const.same left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [Const.same, ConstProvenance.same_eq_true_iff]
  termination_by structural left

  @[simp] theorem ConstProvenance.same_eq_true_iff
      (left right : ConstProvenance) :
      ConstProvenance.same left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [ConstProvenance.same, SourceTerm.same_eq_true_iff,
        TypeOp.same_eq_true_iff]
  termination_by structural left

  @[simp] theorem SourceTerm.same_eq_true_iff (left right : SourceTerm) :
      SourceTerm.same left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [SourceTerm.same, Const.same_eq_true_iff, Ty.same_eq_true_iff,
        SourceTerm.same_eq_true_iff, and_assoc]
  termination_by structural left
end

@[simp] theorem sourceVarSame_eq_true_iff (left right : Var Ty) :
    sourceVarSame left right = true ↔ left = right := by
  cases left
  cases right
  simp [sourceVarSame, Ty.same_eq_true_iff]

namespace Name

/-- The global OpenTheory name with the given component. -/
def global (component : String) : Name := ⟨[], component⟩

end Name

namespace TypeOp

/-- The distinguished, undefined function-space operator from `TypeTerm.sml`. -/
def function : TypeOp := .mk (Name.global "->") .undefined

end TypeOp

namespace Ty

/-- OpenTheory function space. -/
def function (domain codomain : Ty) : Ty := .op TypeOp.function [domain, codomain]

/-- Recognize the exact OpenTheory function-space form. -/
def destFunction? : Ty → Option (Ty × Ty)
  | .op operator arguments =>
      match arguments with
      | [domain, codomain] =>
          if TypeOp.same operator TypeOp.function then some (domain, codomain) else none
      | _ => none
  | _ => none

@[simp] theorem destFunction?_function (domain codomain : Ty) :
    destFunction? (function domain codomain) = some (domain, codomain) := by
  simp [destFunction?, function, TypeOp.function]

end Ty

abbrev SourceVar := Var Ty

namespace SourceTerm

/-- The source variable exposed by a variable node. -/
def asVar : SourceTerm → Option SourceVar
  | .var name ty => some ⟨name, ty⟩
  | _ => none

/-- Executable source type checking, corresponding to `TypeTerm.mk`. -/
def inferType : SourceTerm → Option Ty
  | .const _ ty => some ty
  | .var _ ty => some ty
  | .app function argument => do
      let functionTy ← inferType function
      let argumentTy ← inferType argument
      let (domain, codomain) ← functionTy.destFunction?
      if Ty.same domain argumentTy then some codomain else none
  | .abs _ domain body => do
      let codomain ← inferType body
      pure (.function domain codomain)
termination_by term => sizeOf term

end SourceTerm

/-- Canonical terms use de Bruijn indices for bound variables. -/
inductive DBTerm where
  | const : Const → Ty → DBTerm
  | free : SourceVar → DBTerm
  | bound : Nat → DBTerm
  | app : DBTerm → DBTerm → DBTerm
  | abs : Ty → DBTerm → DBTerm
deriving Repr

/-- The nearest matching binder, counting outward from zero. -/
def boundIndex (needle : SourceVar) : List SourceVar → Option Nat
  | [] => none
  | binder :: binders =>
      if sourceVarSame needle binder then some 0 else (boundIndex needle binders).map Nat.succ

namespace SourceTerm

/-- Erase binder names while retaining free names, types, and symbol provenance. -/
def toDB (binders : List SourceVar) : SourceTerm → DBTerm
  | .const constant ty => .const constant ty
  | .var name ty =>
      let sourceVar : SourceVar := ⟨name, ty⟩
      match boundIndex sourceVar binders with
      | some index => .bound index
      | none => .free sourceVar
  | .app function argument => .app (toDB binders function) (toDB binders argument)
  | .abs name domain body =>
      .abs domain (toDB (⟨name, domain⟩ :: binders) body)
termination_by term => sizeOf term

end SourceTerm

namespace DBTerm

/-- Type check a de Bruijn term under the types of its enclosing binders. -/
def inferType (context : List Ty) : DBTerm → Option Ty
  | .const _ ty => some ty
  | .free sourceVar => some sourceVar.ty
  | .bound index => context[index]?
  | .app function argument => do
      let functionTy ← inferType context function
      let argumentTy ← inferType context argument
      let (domain, codomain) ← functionTy.destFunction?
      if Ty.same domain argumentTy then some codomain else none
  | .abs domain body => do
      let codomain ← inferType (domain :: context) body
      pure (.function domain codomain)
termination_by term => sizeOf term

attribute [simp]
  SourceTerm.inferType.eq_1 SourceTerm.inferType.eq_2
  SourceTerm.inferType.eq_3 SourceTerm.inferType.eq_4
  SourceTerm.toDB.eq_1 SourceTerm.toDB.eq_2 SourceTerm.toDB.eq_3 SourceTerm.toDB.eq_4
  DBTerm.inferType.eq_1 DBTerm.inferType.eq_2 DBTerm.inferType.eq_3
  DBTerm.inferType.eq_4 DBTerm.inferType.eq_5

theorem boundIndex_preserves_var
    {needle : SourceVar} {binders : List SourceVar} {index : Nat}
    (h : boundIndex needle binders = some index) :
    binders[index]? = some needle := by
  induction binders generalizing index with
  | nil => simp [boundIndex] at h
  | cons binder binders ih =>
      by_cases same : needle = binder
      · subst binder
        simp [boundIndex] at h
        subst index
        rfl
      · simp [boundIndex, same] at h
        obtain ⟨previous, hprevious, rfl⟩ := h
        simpa using ih hprevious

theorem boundIndex_preserves_type
    {needle : SourceVar} {binders : List SourceVar} {index : Nat}
    (h : boundIndex needle binders = some index) :
    (binders.map Var.ty)[index]? = some needle.ty := by
  have found := congrArg (Option.map Var.ty) (boundIndex_preserves_var h)
  simpa using found

/-- De Bruijn conversion preserves the independent source type checker. -/
theorem inferType_toDB (binders : List SourceVar) (term : SourceTerm) :
    DBTerm.inferType (binders.map Var.ty) (term.toDB binders) = term.inferType := by
  fun_induction SourceTerm.toDB with
  | case1 => simp
  | case2 binders _ _ _ _ found =>
      simpa using boundIndex_preserves_type found
  | case3 _ _ ty sourceVar _ =>
      rw [DBTerm.inferType.eq_2, SourceTerm.inferType.eq_2]
  | case4 => simp_all
  | case5 => simp_all

/-- Structural equality of canonical syntax, including symbol provenance. -/
def same : DBTerm → DBTerm → Bool
  | .const leftConst leftTy, .const rightConst rightTy =>
      Const.same leftConst rightConst && Ty.same leftTy rightTy
  | .free leftVar, .free rightVar => sourceVarSame leftVar rightVar
  | .bound leftIndex, .bound rightIndex => leftIndex == rightIndex
  | .app leftFunction leftArgument, .app rightFunction rightArgument =>
      same leftFunction rightFunction && same leftArgument rightArgument
  | .abs leftTy leftBody, .abs rightTy rightBody =>
      Ty.same leftTy rightTy && same leftBody rightBody
  | _, _ => false
termination_by left _ => sizeOf left

/-- Propositional structural equality for canonical syntax. -/
def Same (left right : DBTerm) : Prop := same left right = true

@[simp] theorem same_eq_true_iff (left right : DBTerm) :
    same left right = true ↔ left = right := by
  induction left generalizing right with
  | const leftConst leftTy =>
      cases right <;> simp [same]
  | free leftVar =>
      cases right <;> simp [same]
  | bound leftIndex =>
      cases right <;> simp [same]
  | app leftFunction leftArgument functionIH argumentIH =>
      cases right <;> simp [same, functionIH, argumentIH]
  | abs leftTy leftBody bodyIH =>
      cases right <;> simp [same, bodyIH]

/-- Canonical structural identity coincides with Lean equality. -/
theorem same_iff_eq (left right : DBTerm) : Same left right ↔ left = right := by
  exact same_eq_true_iff left right

end DBTerm

/-- A canonical term can only be constructed after de Bruijn type checking. -/
structure CanonicalTerm where
  term : DBTerm
  ty : Ty
  checked : term.inferType [] = some ty

namespace SourceTerm

/-- Validate source syntax and return its typed, alpha-canonical image. -/
def check (term : SourceTerm) : Option CanonicalTerm :=
  let canonical := term.toDB []
  match h : canonical.inferType [] with
  | some ty => some ⟨canonical, ty, h⟩
  | none => none

theorem check_eq_none_iff (term : SourceTerm) :
    check term = none ↔ term.inferType = none := by
  have agreement : DBTerm.inferType [] (term.toDB []) = term.inferType := by
    simpa using DBTerm.inferType_toDB [] term
  simp only [check]
  split
  · rename_i ty hcanonical
    have hsource : term.inferType = some ty := agreement.symm.trans hcanonical
    simp [hsource]
  · rename_i hcanonical
    have hsource : term.inferType = none := agreement.symm.trans hcanonical
    simp [hsource]

theorem check_isSome_iff (term : SourceTerm) :
    (check term).isSome = true ↔ term.inferType.isSome = true := by
  have agreement : DBTerm.inferType [] (term.toDB []) = term.inferType := by
    simpa using DBTerm.inferType_toDB [] term
  simp only [check]
  split
  · rename_i ty hcanonical
    have hsource : term.inferType = some ty := agreement.symm.trans hcanonical
    simp [hsource]
  · rename_i hcanonical
    have hsource : term.inferType = none := agreement.symm.trans hcanonical
    simp [hsource]

/-!
`alphaEqAux` is an independent named-term definition of alpha equivalence.  It
tracks a binder environment on each side, just as OpenTheory's
`Term.alphaCompare` does; it is not defined by canonicalization.
-/

def alphaEqAux (leftBinders rightBinders : List SourceVar) :
    SourceTerm → SourceTerm → Bool
  | .const leftConst leftTy, .const rightConst rightTy =>
      Const.same leftConst rightConst && Ty.same leftTy rightTy
  | .var leftName leftTy, .var rightName rightTy =>
      match boundIndex ⟨leftName, leftTy⟩ leftBinders,
          boundIndex ⟨rightName, rightTy⟩ rightBinders with
      | some leftIndex, some rightIndex => leftIndex == rightIndex
      | none, none => sourceVarSame ⟨leftName, leftTy⟩ ⟨rightName, rightTy⟩
      | _, _ => false
  | .app leftFunction leftArgument, .app rightFunction rightArgument =>
      alphaEqAux leftBinders rightBinders leftFunction rightFunction &&
        alphaEqAux leftBinders rightBinders leftArgument rightArgument
  | .abs leftName leftTy leftBody, .abs rightName rightTy rightBody =>
      Ty.same leftTy rightTy &&
        alphaEqAux (⟨leftName, leftTy⟩ :: leftBinders)
          (⟨rightName, rightTy⟩ :: rightBinders) leftBody rightBody
  | .const .., .var .. | .const .., .app .. | .const .., .abs ..
  | .var .., .const .. | .var .., .app .. | .var .., .abs ..
  | .app .., .const .. | .app .., .var .. | .app .., .abs ..
  | .abs .., .const .. | .abs .., .var .. | .abs .., .app .. => false
termination_by left _ => sizeOf left

/-- Alpha equivalence of source terms. -/
def AlphaEq (left right : SourceTerm) : Prop := alphaEqAux [] [] left right = true

theorem alphaEqAux_eq_same_toDB
    (leftBinders rightBinders : List SourceVar) (left right : SourceTerm) :
    alphaEqAux leftBinders rightBinders left right =
      DBTerm.same (left.toDB leftBinders) (right.toDB rightBinders) := by
  fun_induction alphaEqAux <;>
    simp_all [toDB, DBTerm.same] <;>
    (repeat' split) <;>
    simp_all [DBTerm.same]

/-- Named alpha equivalence is exactly structural equality of canonical syntax. -/
theorem alphaEq_iff_toDB_same (left right : SourceTerm) :
    AlphaEq left right ↔ DBTerm.Same (left.toDB []) (right.toDB []) := by
  simp only [AlphaEq, DBTerm.Same, alphaEqAux_eq_same_toDB]

/-- Independent named alpha equivalence is exactly canonical structural identity. -/
theorem alphaEq_iff_toDB_eq (left right : SourceTerm) :
    AlphaEq left right ↔ left.toDB [] = right.toDB [] := by
  rw [alphaEq_iff_toDB_same, DBTerm.same_iff_eq]

end SourceTerm

/-! ## Executable calibration examples -/

namespace Examples

def individual : Ty := .op (.mk (Name.global "ind") .undefined) []

def bool : Ty := .op (.mk (Name.global "bool") .undefined) []

def x : Name := Name.global "x"

def y : Name := Name.global "y"

def z : Name := Name.global "z"

def identityX : SourceTerm := .abs x individual (.var x individual)

def identityY : SourceTerm := .abs y individual (.var y individual)

def constantZ : SourceTerm := .abs y individual (.var z individual)

example : SourceTerm.AlphaEq identityX identityY := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  simp [identityX, identityY, SourceTerm.toDB, boundIndex, sourceVarSame]

example : ¬ SourceTerm.AlphaEq identityX constantZ := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  simp [identityX, constantZ, x, y, z, individual, SourceTerm.toDB, boundIndex,
    sourceVarSame, Name.global]

/-- The nearest exactly typed binder wins under repeated names. -/
def shadowedX : SourceTerm :=
  .abs x individual (.abs x bool (.var x bool))

def shadowedYZ : SourceTerm :=
  .abs y individual (.abs z bool (.var z bool))

example : SourceTerm.AlphaEq shadowedX shadowedYZ := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  simp [shadowedX, shadowedYZ, SourceTerm.toDB, boundIndex, sourceVarSame,
    x, y, z, individual, bool, Name.global]

/-- Reusing a printed name at a different type does not capture the variable. -/
def sameNameDifferentTypeFree : SourceTerm :=
  .abs x individual (.var x bool)

example :
    sameNameDifferentTypeFree.toDB [] =
      .abs individual (.free (⟨x, bool⟩ : SourceVar)) := by
  simp [sameNameDifferentTypeFree, SourceTerm.toDB, boundIndex, sourceVarSame,
    x, individual, bool, Name.global]

/-- A free variable is not alpha-equivalent to a captured occurrence. -/
def freeXUnderY : SourceTerm := .abs y individual (.var x individual)

example : ¬ SourceTerm.AlphaEq identityX freeXUnderY := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  simp [identityX, freeXUnderY, SourceTerm.toDB, boundIndex, sourceVarSame,
    x, y, individual, Name.global]

example : (SourceTerm.check identityX).isSome = true := by
  rw [SourceTerm.check_isSome_iff]
  simp [identityX, SourceTerm.inferType]

/-- A well-typed source application remains untrusted data until checked. -/
def wellTypedApplication : SourceTerm :=
  .app (.var (Name.global "f") (.function individual bool)) (.var x individual)

example : SourceTerm.inferType wellTypedApplication = some bool := by
  simp [wellTypedApplication, SourceTerm.inferType]

example : (SourceTerm.check wellTypedApplication).isSome = true := by
  rw [SourceTerm.check_isSome_iff]
  simp [wellTypedApplication, SourceTerm.inferType]

/-- An application whose function has a non-function type remains expressible. -/
def illTypedApplication : SourceTerm := .app (.var x individual) (.var y individual)

example : SourceTerm.check illTypedApplication = none := by
  rw [SourceTerm.check_eq_none_iff]
  simp [illTypedApplication, individual, SourceTerm.inferType, Ty.destFunction?]

/-- A function application also rejects an argument of the wrong domain. -/
def wrongDomainApplication : SourceTerm :=
  .app (.var (Name.global "f") (.function individual bool)) (.var x bool)

example : SourceTerm.check wrongDomainApplication = none := by
  rw [SourceTerm.check_eq_none_iff]
  simp [wrongDomainApplication, individual, bool, SourceTerm.inferType,
    Ty.destFunction?, Ty.function, TypeOp.function, Ty.same, Name.global]

def sameNameUndefined : Const := .mk (Name.global "c") .undefined

def sameNameDefined : Const :=
  .mk (Name.global "c") (.defined (.var z individual))

/-- Equal printed names do not erase OpenTheory symbol provenance. -/
example :
    ¬ SourceTerm.AlphaEq (.const sameNameUndefined individual)
      (.const sameNameDefined individual) := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  simp [sameNameUndefined, sameNameDefined, SourceTerm.toDB]

def sameNameDefinedIdentityX : Const :=
  .mk (Name.global "id") (.defined identityX)

def sameNameDefinedIdentityY : Const :=
  .mk (Name.global "id") (.defined identityY)

/-- Definition provenance uses nominal source identity, not alpha identity. -/
example :
    ¬ SourceTerm.AlphaEq
      (.const sameNameDefinedIdentityX (.function individual individual))
      (.const sameNameDefinedIdentityY (.function individual individual)) := by
  rw [SourceTerm.alphaEq_iff_toDB_eq]
  simp [sameNameDefinedIdentityX, sameNameDefinedIdentityY, identityX, identityY,
    x, y, Name.global, SourceTerm.toDB]

end Examples

end Mettapedia.Languages.OpenTheory
