import Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement

/-!
# Presentation-preserving human type substitutions

Solution theory is sufficient for positive type evidence, but it cannot
determine the syntax emitted by application-result inference.  In particular,
an unconstrained return variable remains that variable; it is not replaced by
an arbitrary model value.  This module therefore gives the runtime-refinement
lane an executable-independent finite substitution presentation.

The relations below are type-specific and declarative.  They mention neither
the LeaTTa matcher nor the HE executable matcher.  `%Undefined%` is a wildcard
recursively, while `Atom` is a wildcard only at the outer type-match boundary.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec

/-! ## Finite substitutions -/

/-- A finite, ordered type-variable substitution.  The first entry for a key
is authoritative. -/
abbrev TypeSubst := List (String × Atom)

namespace TypeSubst

mutual

/-- Type variables occurring in an atom, with multiplicity. -/
def typeVars : Atom → List String
  | .var name => [name]
  | .expression atoms => typeVarsList atoms
  | _ => []

/-- List companion of `typeVars`. -/
def typeVarsList : List Atom → List String
  | [] => []
  | atom :: atoms => typeVars atom ++ typeVarsList atoms

end

/-- First-hit lookup in a finite type substitution. -/
def lookup : TypeSubst → String → Option Atom
  | [], _ => none
  | (key, value) :: rest, name =>
      if name = key then some value else lookup rest name

/-- Variables assigned by a finite substitution. -/
def keys (substitution : TypeSubst) : List String :=
  substitution.map Prod.fst

/-- Homomorphic, one-pass application.  Normal substitutions contain no
assigned variable in a stored value, so one pass is their total application. -/
def apply (substitution : TypeSubst) : Atom → Atom
  | .symbol name => .symbol name
  | .var name => (substitution.lookup name).getD (.var name)
  | .grounded value => .grounded value
  | .expression atoms => .expression (atoms.map (apply substitution))

/-- Remove every entry for one key. -/
def erase (substitution : TypeSubst) (name : String) : TypeSubst :=
  substitution.filter (fun entry => entry.1 != name)

/-- Apply one new assignment to the values of an older substitution. -/
def applyAssignment (name : String) (value : Atom) : Atom → Atom :=
  TypeSubst.apply [(name, value)]

/-- Extend a substitution and compose the new assignment through all older
values.  This preserves the syntactic spelling of every still-unassigned
variable. -/
def bind (substitution : TypeSubst) (name : String) (value : Atom) :
    TypeSubst :=
  let resolvedValue := substitution.apply value
  (name, resolvedValue) ::
    (substitution.erase name).map fun entry =>
      (entry.1, applyAssignment name resolvedValue entry.2)

/-- Idempotent finite-substitution presentation: keys are unique and no
stored value contains a variable assigned by the same substitution. -/
def Normal (substitution : TypeSubst) : Prop :=
  substitution.keys.Nodup ∧
    ∀ name value, (name, value) ∈ substitution →
      ∀ candidate ∈ typeVars value, candidate ∉ substitution.keys

@[simp] theorem lookup_empty (name : String) :
    lookup [] name = none := rfl

mutual

@[simp] theorem apply_empty (atom : Atom) :
    apply [] atom = atom := by
  cases atom with
  | symbol | var | grounded => simp [apply, lookup, Option.getD]
  | expression atoms =>
      simp only [apply]
      exact congrArg Atom.expression (apply_empty_list atoms)
termination_by 2 * sizeOf atom

@[simp] theorem apply_empty_list (atoms : List Atom) :
    atoms.map (apply []) = atoms := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons (apply_empty atom) (apply_empty_list atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

theorem normal_empty : Normal [] := by
  simp [Normal, keys]

end TypeSubst

/-! ## Presentation-preserving reduced-type matching -/

mutual

/-- Ordinary matching after the incoming substitution has already been
applied.  This layer has no wildcard constructor: a `%Undefined%` produced
by substitution is an ordinary symbol at every depth.  Distinct variables
orient left-to-right and compounds recurse in source order. -/
inductive AppliedReducedTypeMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | identical (substitution : TypeSubst) (atom : Atom) :
      AppliedReducedTypeMatchRel substitution atom atom substitution
  | bindLeft {substitution : TypeSubst} {name : String} {right : Atom} :
      name ∉ TypeSubst.typeVars right →
      AppliedReducedTypeMatchRel substitution (.var name) right
        (substitution.bind name right)
  | bindRight {substitution : TypeSubst} {left : Atom} {name : String} :
      (∀ other, left ≠ .var other) →
      name ∉ TypeSubst.typeVars left →
      AppliedReducedTypeMatchRel substitution left (.var name)
        (substitution.bind name left)
  | expression {substitution output : TypeSubst}
      {left right : List Atom} :
      AppliedReducedTypeListMatchRel substitution left right output →
      AppliedReducedTypeMatchRel substitution
        (.expression left) (.expression right) output

/-- Resolve one ordinary (non-wildcard) child through the substitution
accumulated by earlier siblings, then take one applied unification step. -/
inductive AppliedTypePresentationMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | ordinary {substitution output : TypeSubst}
      {left right resolvedLeft resolvedRight : Atom} :
      substitution.apply left = resolvedLeft →
      substitution.apply right = resolvedRight →
      AppliedReducedTypeMatchRel substitution resolvedLeft resolvedRight output →
      AppliedTypePresentationMatchRel substitution left right output

/-- Pointwise companion for already-applied ordinary atoms.  In particular,
this relation deliberately has no recursive `%Undefined%` wildcard. -/
inductive AppliedReducedTypeListMatchRel :
    TypeSubst → List Atom → List Atom → TypeSubst → Prop where
  | nil (substitution : TypeSubst) :
      AppliedReducedTypeListMatchRel substitution [] [] substitution
  | cons {substitution next output : TypeSubst}
      {left right : Atom} {lefts rights : List Atom} :
      AppliedTypePresentationMatchRel substitution left right next →
      AppliedReducedTypeListMatchRel next lefts rights output →
      AppliedReducedTypeListMatchRel substitution
        (left :: lefts) (right :: rights) output

end

/-- The ordinary leaf lane applies only when the two raw atoms are not both
expressions.  Raw expression pairs must recurse before substitution so that
literal wildcard provenance is preserved child by child. -/
def ReducedTypeLeafShape : Atom → Atom → Prop
  | .expression _, .expression _ => False
  | _, _ => True

mutual

/-- Literal recursive `%Undefined%` is a wildcard before substitution.
Raw expression pairs recurse before substitution.  Every other shape resolves
through the current presentation and takes one ordinary declarative unifier
step.  Consequently a variable presented as `%Undefined%` by earlier
constraints never becomes a wildcard, including below an expression. -/
inductive ReducedTypePresentationMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | undefinedLeft (substitution : TypeSubst) (right : Atom) :
      ReducedTypePresentationMatchRel substitution
        Atom.undefinedType right substitution
  | undefinedRight (substitution : TypeSubst) (left : Atom) :
      ReducedTypePresentationMatchRel substitution
        left Atom.undefinedType substitution
  | expression {substitution output : TypeSubst}
      {left right : List Atom} :
      ReducedTypePresentationListMatchRel substitution left right output →
      ReducedTypePresentationMatchRel substitution
        (.expression left) (.expression right) output
  | ordinary {substitution output : TypeSubst}
      {left right resolvedLeft resolvedRight : Atom} :
      left ≠ Atom.undefinedType →
      right ≠ Atom.undefinedType →
      ReducedTypeLeafShape left right →
      substitution.apply left = resolvedLeft →
      substitution.apply right = resolvedRight →
      AppliedReducedTypeMatchRel substitution resolvedLeft resolvedRight output →
      ReducedTypePresentationMatchRel substitution left right output

/-- Left-to-right list companion, threading the finite substitution. -/
inductive ReducedTypePresentationListMatchRel :
    TypeSubst → List Atom → List Atom → TypeSubst → Prop where
  | nil (substitution : TypeSubst) :
      ReducedTypePresentationListMatchRel substitution [] [] substitution
  | cons {substitution next output : TypeSubst}
      {left right : Atom} {lefts rights : List Atom} :
      ReducedTypePresentationMatchRel substitution left right next →
      ReducedTypePresentationListMatchRel next lefts rights output →
      ReducedTypePresentationListMatchRel substitution
        (left :: lefts) (right :: rights) output

end

/-- Away from literal recursive wildcards, a reduced presentation derivation
exposes its ordinary post-substitution matching step. -/
theorem ReducedTypePresentationMatchRel.ordinary_of_nonUndefined
    {substitution output : TypeSubst} {left right : Atom}
    (leftNotUndefined : left ≠ Atom.undefinedType)
    (rightNotUndefined : right ≠ Atom.undefinedType)
    (leafShape : ReducedTypeLeafShape left right)
    (derivation : ReducedTypePresentationMatchRel
      substitution left right output) :
    ∃ resolvedLeft resolvedRight,
      substitution.apply left = resolvedLeft ∧
        substitution.apply right = resolvedRight ∧
        AppliedReducedTypeMatchRel
          substitution resolvedLeft resolvedRight output := by
  cases derivation with
  | undefinedLeft => exact (leftNotUndefined rfl).elim
  | undefinedRight => exact (rightNotUndefined rfl).elim
  | expression children => exact leafShape.elim
  | ordinary _ _ _ leftApply rightApply applied =>
      exact ⟨_, _, leftApply, rightApply, applied⟩

/-- Published top-level gradual wildcards plus the presentation-preserving R2
reduced matcher. -/
inductive CorePlusR2TypePresentationMatchRel :
    TypeSubst → Atom → Atom → TypeSubst → Prop where
  | undefinedLeft (substitution : TypeSubst) (right : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        Atom.undefinedType right substitution
  | undefinedRight (substitution : TypeSubst) (left : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        left Atom.undefinedType substitution
  | atomLeft (substitution : TypeSubst) (right : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        Atom.atomType right substitution
  | atomRight (substitution : TypeSubst) (left : Atom) :
      CorePlusR2TypePresentationMatchRel substitution
        left Atom.atomType substitution
  | reduced {substitution output : TypeSubst} {left right : Atom} :
      left ≠ Atom.undefinedType →
      right ≠ Atom.undefinedType →
      left ≠ Atom.atomType →
      right ≠ Atom.atomType →
      ReducedTypePresentationMatchRel substitution left right output →
      CorePlusR2TypePresentationMatchRel substitution left right output

/-- Away from the four published top-level wildcards, a type-presentation
match is exactly one reduced-type presentation match. -/
theorem CorePlusR2TypePresentationMatchRel.reduced_of_nonWildcard
    {substitution output : TypeSubst} {left right : Atom}
    (hLeftUndefined : left ≠ Atom.undefinedType)
    (hRightUndefined : right ≠ Atom.undefinedType)
    (hLeftAtom : left ≠ Atom.atomType)
    (hRightAtom : right ≠ Atom.atomType)
    (hmatch : CorePlusR2TypePresentationMatchRel
      substitution left right output) :
    ReducedTypePresentationMatchRel substitution left right output := by
  cases hmatch with
  | undefinedLeft => exact (hLeftUndefined rfl).elim
  | undefinedRight => exact (hRightUndefined rfl).elim
  | atomLeft => exact (hLeftAtom rfl).elim
  | atomRight => exact (hRightAtom rfl).elim
  | reduced _ _ _ _ hreduced => exact hreduced

/-- Two distinct ordinary symbols have no applied reduced-type match. -/
theorem AppliedReducedTypeMatchRel.no_distinct_symbols
    {substitution output : TypeSubst} {left right : String}
    (hDistinct : left ≠ right) :
    ¬AppliedReducedTypeMatchRel substitution
      (.symbol left) (.symbol right) output := by
  intro hmatch
  cases hmatch with
  | identical => exact hDistinct rfl

/-! ## Lawful presented candidates -/

/-- One exact runtime candidate: `rawTerm` records the declared provenance,
`substitution` records the type fold, and `observed` is its definite syntactic
presentation. -/
structure RuntimeTypePackage where
  observed : Atom
  rawTerm : Atom
  substitution : TypeSubst
  presentation : observed = substitution.apply rawTerm

/-- A published candidate has an empty private substitution. -/
def RuntimeTypePackage.published (type : Atom) : RuntimeTypePackage :=
  ⟨type, type, [], (TypeSubst.apply_empty type).symm⟩

/-- Later consumers match only the definite observed presentation.  The
package-local substitution is provenance and cannot capture the outer fold. -/
def PackagedTypePresentationMatchRel
    (incoming : TypeSubst) (expected : Atom)
    (actual : RuntimeTypePackage) (output : TypeSubst) : Prop :=
  CorePlusR2TypePresentationMatchRel incoming expected actual.observed output

/-! ## Positive and negative boundary examples -/

private def tToA : TypeSubst := [("t", .symbol "A")]
private def tToB : TypeSubst := [("t", .symbol "B")]

/-- Positive: matching `$t` against `A` records the definite substitution. -/
theorem variable_matches_symbol_presentation :
    CorePlusR2TypePresentationMatchRel [] (.var "t") (.symbol "A")
      tToA := by
  apply CorePlusR2TypePresentationMatchRel.reduced
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.atomType]
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .var "t") (resolvedRight := .symbol "A")
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · exact TypeSubst.apply_empty (.var "t")
  · exact TypeSubst.apply_empty (.symbol "A")
  simpa [tToA, TypeSubst.bind, TypeSubst.apply, TypeSubst.erase,
    TypeSubst.lookup] using
    (AppliedReducedTypeMatchRel.bindLeft
      (substitution := []) (name := "t") (right := .symbol "A")
      (by simp [TypeSubst.typeVars]))

/-- Negative: after `$t` is fixed to `B`, `A` cannot match the same spelling. -/
theorem fixed_variable_rejects_distinct_symbol :
    ¬∃ output,
      CorePlusR2TypePresentationMatchRel tToB
        (.symbol "A") (.var "t") output := by
  rintro ⟨output, hmatch⟩
  have hreduced := hmatch.reduced_of_nonWildcard
    (by simp [Atom.undefinedType]) (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) (by simp [Atom.atomType])
  obtain ⟨resolvedLeft, resolvedRight, hleft, hright, happlied⟩ :=
    hreduced.ordinary_of_nonUndefined
      (by simp [Atom.undefinedType]) (by simp [Atom.undefinedType])
      (by simp [ReducedTypeLeafShape])
  simp [tToB, TypeSubst.apply, TypeSubst.lookup,
    Option.getD] at hleft hright
  rw [← hleft, ← hright] at happlied
  exact AppliedReducedTypeMatchRel.no_distinct_symbols
    (by decide) happlied

/-- An unconstrained raw return variable has exactly its syntactic variable
presentation under the empty substitution. -/
theorem unresolved_variable_presentation_is_rigid :
    (RuntimeTypePackage.published (.var "t")).observed = .var "t" := rfl

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentation
