import Mettapedia.TypeTheory.SimpleDependentInstitutionBridge

/-!
# Weakest sufficient simple/dependent family semantics

The choice between a contextual simple family semantics and a genuinely
dependent one is made here by a semantic property, not by a global language
default.  A simple profile is sufficient for an indexed family exactly when
that family is isomorphic to a constant family.  The dependent profile is
always sufficient, but is least only when the simple representation is
impossible.

This is deliberately narrower than a comparison of complete simple and
dependent type theories.  It isolates the exact family-varying capability
used by that comparison.  In particular, it neither postulates a decision
procedure for essential-image membership nor chooses identity, universe, or
extensionality principles.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SimpleDependentCapabilitySelection

open CategoryTheory
open Mettapedia.TypeTheory.SetFamilyChangeOfBaseAdjunction
open Mettapedia.TypeTheory.SimpleDependentInstitutionBridge

universe u

/-- The two semantic capability levels relevant to constancy of fibres. -/
inductive Profile where
  | simple
  | dependent
  deriving DecidableEq, Repr

/-- Simple family semantics is weaker than dependent family semantics. -/
def Profile.le : Profile → Profile → Prop
  | .dependent, .simple => False
  | _, _ => True

instance : PartialOrder Profile where
  le := Profile.le
  le_refl profile := by cases profile <;> trivial
  le_trans first middle last := by
    cases first <;> cases middle <;> cases last <;>
      simp_all [Profile.le]
  le_antisymm first second := by
    cases first <;> cases second <;> simp_all [Profile.le]

theorem simple_le (profile : Profile) : .simple ≤ profile := by
  cases profile <;> trivial

theorem dependent_le_iff (profile : Profile) :
    .dependent ≤ profile ↔ profile = .dependent := by
  cases profile with
  | simple =>
      constructor
      · intro impossible
        change False at impossible
        exact impossible.elim
      · intro impossible
        cases impossible
  | dependent =>
      constructor
      · intro _
        rfl
      · intro _
        exact le_rfl

/-- A dependent family can be represented without genuinely varying fibres
exactly when it lies in the essential image of constant-family inclusion. -/
def SimpleRepresentable {Index : Type u} (family : FamilyOver Index) : Prop :=
  ∃ Value : Type u,
    Nonempty ((constantFamilyOver Index).obj Value ≅ family)

/-- Sufficiency of one profile for one indexed family. -/
def Sufficient {Index : Type u} (family : FamilyOver Index) : Profile → Prop
  | .simple => SimpleRepresentable family
  | .dependent => True

/-- A selected profile is sufficient and no stronger than any other
sufficient profile. -/
def IsLeastSufficient {Index : Type u} (family : FamilyOver Index)
    (profile : Profile) : Prop :=
  Sufficient family profile ∧
    ∀ alternative, Sufficient family alternative → profile ≤ alternative

/-- Least sufficient profiles are unique. -/
theorem leastSufficient_unique {Index : Type u} {family : FamilyOver Index}
    {first second : Profile}
    (firstLeast : IsLeastSufficient family first)
    (secondLeast : IsLeastSufficient family second) :
    first = second :=
  le_antisymm (firstLeast.2 second secondLeast.1)
    (secondLeast.2 first firstLeast.1)

/-- Every literal constant family has the simple profile as its least
sufficient semantics. -/
theorem constantFamily_simple_isLeast (Index Value : Type u) :
    IsLeastSufficient ((constantFamilyOver Index).obj Value) .simple := by
  constructor
  · exact ⟨Value, ⟨CategoryTheory.eqToIso rfl⟩⟩
  · intro alternative _sufficient
    exact simple_le alternative

/-- The dependent profile is available for every indexed family. -/
theorem dependent_sufficient {Index : Type u} (family : FamilyOver Index) :
    Sufficient family .dependent :=
  trivial

/-! ## A genuine-dependency discriminator -/

/-- The varying Boolean family cannot use the simple profile. -/
theorem boolVarying_simple_not_sufficient :
    ¬ Sufficient boolVaryingFamily .simple := by
  simpa [Sufficient, SimpleRepresentable] using
    boolVaryingFamily_not_in_essentialImage

/-- Hence the dependent profile is the least sufficient choice for the
varying Boolean family. -/
theorem boolVarying_dependent_isLeast :
    IsLeastSufficient boolVaryingFamily .dependent := by
  constructor
  · exact dependent_sufficient boolVaryingFamily
  · intro alternative sufficient
    cases alternative with
    | simple => exact False.elim (boolVarying_simple_not_sufficient sufficient)
    | dependent => exact le_rfl

/-- Negative control: simple family semantics is not a universal host for
dependent signatures. -/
theorem not_every_family_is_simple_representable :
    ¬ ∀ family : FamilyOver Bool, SimpleRepresentable family := by
  intro allSimple
  exact boolVarying_simple_not_sufficient (allSimple boolVaryingFamily)

/-- On the constant-family image, the existing institution comorphism makes
semantic consequence exact in both directions. -/
theorem simple_consequence_exact_on_constant_family
    (Index Value : Type u)
    (premises : Set (Sigma fun _ : Index => Value))
    (conclusion : Sigma fun _ : Index => Value) :
    (simpleInstitution Index).Entails Value premises conclusion ↔
      (dependentInstitution Index).Entails
        ((simpleToDependent Index).mapSignature.obj Value)
        (Set.image
          ((simpleToDependent Index).mapSentence.app Value) premises)
        ((simpleToDependent Index).mapSentence.app Value conclusion) :=
  entails_iff_constantFamily Index Value premises conclusion

#print axioms leastSufficient_unique
#print axioms constantFamily_simple_isLeast
#print axioms dependent_sufficient
#print axioms boolVarying_simple_not_sufficient
#print axioms boolVarying_dependent_isLeast
#print axioms not_every_family_is_simple_representable
#print axioms simple_consequence_exact_on_constant_family

end Mettapedia.TypeTheory.SimpleDependentCapabilitySelection
