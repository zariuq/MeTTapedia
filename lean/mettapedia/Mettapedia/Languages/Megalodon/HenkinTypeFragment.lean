import Mettapedia.Languages.Megalodon.MathdataKernel
import Mettapedia.Logic.HOL.Syntax.TypeSubstitution

/-!
# Which Megalodon types the monomorphic Henkin institution expresses

The fixed-base Henkin institution has monomorphic simple types: propositions,
base types, and arrows.  Megalodon's kernel is polymorphic: its types carry
type variables and a prefix type quantifier.  This module records the exact
boundary.

* A plain Megalodon type instantiates once a type environment interprets its
  variables. This constructorwise interpretation rejects the prefix quantifier;
  it is not a non-encodability theorem about polymorphic logic.
* Plain types of type depth zero contain no variables, and their
  instantiation does not depend on the environment.  This is the fragment of
  Megalodon's type language that the Henkin institution expresses directly.
* No single translation agrees with every environment on the first type
  variable. Environment-indexed interpretations respect the kernel's shifting
  and capture-avoiding type instantiation. A semantics for entire polymorphic
  sentences requires more than these type-level laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTypeFragment

open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Logic.HOL

universe u

variable {Base : Type u}

/-- Instantiate a Megalodon type at a type environment and a base-type
interpretation. This interpretation rejects the prefix quantifier. -/
def instantiate (environment : Nat → Ty Base) (base : Nat → Base) : Tp → Option (Ty Base)
  | .var index => some (environment index)
  | .prop => some .prop
  | .base index => some (.base (base index))
  | .arr domain codomain => do
      let domainType ← instantiate environment base domain
      let codomainType ← instantiate environment base codomain
      pure (.arr domainType codomainType)
  | .all _ => none

/-- The constructorwise interpretation rejects the prefix type quantifier. -/
@[simp] theorem instantiate_all (environment : Nat → Ty Base) (base : Nat → Base) (body : Tp) :
    instantiate environment base (.all body) = none :=
  rfl

/-- A well-scoped plain type instantiates at any type-context depth. -/
theorem instantiate_isSome_of_plain (environment : Nat → Ty Base) (base : Nat → Base)
    {depth : Nat} :
    (type : Tp) → Tp.plainWellFormed depth type = true →
      (instantiate environment base type).isSome = true
  | .var _, _ => rfl
  | .prop, _ => rfl
  | .base _, _ => rfl
  | .arr domain codomain, plain => by
      simp only [Tp.plainWellFormed, Bool.and_eq_true] at plain
      obtain ⟨domainType, domainEq⟩ := Option.isSome_iff_exists.1
        (instantiate_isSome_of_plain environment base domain plain.1)
      obtain ⟨codomainType, codomainEq⟩ := Option.isSome_iff_exists.1
        (instantiate_isSome_of_plain environment base codomain plain.2)
      simp [instantiate, domainEq, codomainEq]
  | .all _, plain => by simp [Tp.plainWellFormed] at plain

/-- Only the variables in the declared type context affect interpretation. -/
theorem instantiate_congr_of_plain (base : Nat → Base)
    (first second : Nat → Ty Base) {depth : Nat}
    (agree : ∀ index, index < depth → first index = second index) :
    (type : Tp) → Tp.plainWellFormed depth type = true →
      instantiate first base type = instantiate second base type
  | .var index, plain => by
      simp only [Tp.plainWellFormed, decide_eq_true_eq] at plain
      simp [instantiate, agree index plain]
  | .prop, _ => rfl
  | .base _, _ => rfl
  | .arr domain codomain, plain => by
      simp only [Tp.plainWellFormed, Bool.and_eq_true] at plain
      simp [instantiate,
        instantiate_congr_of_plain base first second agree domain plain.1,
        instantiate_congr_of_plain base first second agree codomain plain.2]
  | .all _, plain => by simp [Tp.plainWellFormed] at plain

/-- The depth-zero case is independent of the type-variable environment. -/
theorem instantiate_plain_environment_independent (base : Nat → Base)
    (first second : Nat → Ty Base) (type : Tp)
    (plain : Tp.plainWellFormed 0 type = true) :
    instantiate first base type = instantiate second base type :=
  instantiate_congr_of_plain base first second (by intro index h; omega) type plain

/-- Syntactic weakening is semantic reindexing, including nonzero cutoffs. -/
theorem instantiate_shift (environment : Nat → Ty Base) (base : Nat → Base)
    (cutoff amount : Nat) (type : Tp) :
    instantiate environment base (Tp.shift cutoff amount type) =
      instantiate (fun index => environment (if index < cutoff then index else index + amount))
        base type := by
  induction type with
  | var index => by_cases h : index < cutoff <;> simp [Tp.shift, instantiate, h]
  | prop => rfl
  | base _ => rfl
  | arr domain codomain ihd ihc => simp [Tp.shift, instantiate, ihd, ihc]
  | all _ _ => rfl

/-- Interpret the kernel's capture-avoiding substitution by inserting one
semantic type. The replacement is interpreted beyond the intervening binders. -/
theorem instantiate_instantiateAt (environment : Nat → Ty Base) (base : Nat → Base)
    (depth : Nat) (replacement type : Tp) (value : Ty Base)
    (replaced : instantiate (fun index => environment (index + depth)) base replacement =
      some value) :
    instantiate environment base (Tp.instantiateAt depth replacement type) =
      instantiate (fun index => if index < depth then environment index
        else if index = depth then value else environment (index - 1)) base type := by
  induction type with
  | var index =>
      by_cases below : index < depth
      · simp [Tp.instantiateAt, instantiate, below]
      · by_cases atDepth : index = depth
        · subst index
          simpa [Tp.instantiateAt, instantiate, instantiate_shift] using replaced
        · simp [Tp.instantiateAt, instantiate, below, atDepth]
  | prop => rfl
  | base _ => rfl
  | arr domain codomain ihd ihc => simp [Tp.instantiateAt, instantiate, ihd, ihc]
  | all _ _ => rfl

/-- At a type application, syntactic instantiation and semantic instantiation
give the same monomorphic result type. -/
theorem instantiate_typeApplication (environment : Nat → Ty Base) (base : Nat → Base)
    (replacement body : Tp) (value : Ty Base)
    (replaced : instantiate environment base replacement = some value) :
    instantiate environment base (Tp.instantiate replacement body) =
      instantiate (fun index => if index = 0 then value else environment (index - 1))
        base body := by
  simpa [Tp.instantiate] using
    instantiate_instantiateAt environment base 0 replacement body value (by simpa using replaced)

/-- Regard free type variables and declared base names as disjoint HOL base
symbols. This uses existing HOL syntax, not an additional intermediate language. -/
def schematicType (type : Tp) : Option (Ty (Nat ⊕ Nat)) :=
  instantiate (fun index => .base (.inl index)) Sum.inr type

/-- Native type-environment interpretation is exactly specialization of the
schematic HOL type by a type-derived substitution. -/
theorem schematicType_specialize (environment : Nat → Ty Base) (base : Nat → Base)
    (type : Tp) :
    (schematicType type).map
        (Ty.substitute (Sum.elim environment (fun index => .base (base index)))) =
      instantiate environment base type := by
  induction type with
  | var _ => rfl
  | prop => rfl
  | base _ => rfl
  | all _ _ => rfl
  | arr domain codomain ihd ihc =>
      change (do
        let d ← schematicType domain
        let c ← schematicType codomain
        pure (Ty.arr d c)).map _ = _
      simp only [instantiate]
      rw [← ihd, ← ihc]
      cases schematicType domain <;> cases schematicType codomain <;> rfl

/-- The result of a native type application is the corresponding specialization
of the body's schematic HOL type. -/
theorem schematicType_typeApplication (environment : Nat → Ty Base) (base : Nat → Base)
    (replacement body : Tp) (value : Ty Base)
    (replaced : instantiate environment base replacement = some value) :
    instantiate environment base (Tp.instantiate replacement body) =
      (schematicType body).map (Ty.substitute
        (Sum.elim (fun index => if index = 0 then value else environment (index - 1))
          (fun index => .base (base index)))) := by
  rw [schematicType_specialize, instantiate_typeApplication environment base replacement body value replaced]

/-- Type weakening inserts a variable rather than capturing an existing one. -/
theorem nonzero_instantiation_avoids_capture :
    instantiate (fun index => if index = 0 then Ty.prop else Ty.arr Ty.prop Ty.prop)
        (fun _ => ()) (Tp.instantiateAt 1 (.var 0) (.arr (.var 0) (.var 1))) =
      some (Ty.arr Ty.prop (Ty.arr Ty.prop Ty.prop)) := by decide

/-- Omitting the replacement's shift changes the resulting interpreted type. -/
theorem unshifted_instantiation_disagrees :
    instantiate (fun index => if index = 0 then Ty.prop else Ty.arr Ty.prop Ty.prop)
        (fun _ => ()) (Tp.instantiateAt 1 (.var 0) (.arr (.var 0) (.var 1))) ≠
      instantiate (fun index => if index = 0 then Ty.prop else Ty.arr Ty.prop Ty.prop)
        (fun _ => ()) (.arr (.var 0) (.var 0)) := by decide

/-- No environment-free translation of Megalodon types into Henkin types
agrees with instantiation at every environment: the first type variable
would have to be every Henkin type. -/
theorem no_uniform_translation (distinct : ∃ left right : Ty Base, left ≠ right) :
    ¬ ∃ translate : Tp → Ty Base,
      ∀ environment : Nat → Ty Base, translate (.var 0) = environment 0 := by
  rintro ⟨translate, uniform⟩
  obtain ⟨left, right, different⟩ := distinct
  have atLeft := uniform (fun _ => left)
  have atRight := uniform (fun _ => right)
  exact different (atLeft.symm.trans atRight)

/-- Henkin types are never a single type: propositions differ from every
arrow type. -/
theorem henkin_types_distinct : ∃ left right : Ty Base, left ≠ right :=
  ⟨.prop, .arr .prop .prop, by intro equal; cases equal⟩

#print axioms instantiate_isSome_of_plain
#print axioms instantiate_plain_environment_independent
#print axioms instantiate_shift
#print axioms instantiate_instantiateAt
#print axioms instantiate_typeApplication
#print axioms schematicType_specialize
#print axioms schematicType_typeApplication
#print axioms nonzero_instantiation_avoids_capture
#print axioms unshifted_instantiation_disagrees
#print axioms no_uniform_translation

end Mettapedia.Languages.Megalodon.HenkinTypeFragment
