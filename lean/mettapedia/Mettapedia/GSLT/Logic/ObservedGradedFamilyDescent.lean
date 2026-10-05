import Mettapedia.GSLT.Distinction.Constructive.DepthBound
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent

/-!
# Constructed material families for exact finite-depth observations

The observer reads every scaled formula of the declared depth. Its exact
kernel is zero distance in the authored finite-depth bound. Material family
and selected-term descent are separate necessary and sufficient conditions
on that kernel. The existing constructive graph and term decoders realize
both conditions without selecting observation representatives.

Forgetting greater depth constructs actual maps of observation classes.
Their identity, composition, family and term comparisons follow from the
complete class predicates. This does not reflect finite-depth agreement
into infinite bisimilarity or turn a nonzero approximation into identity
transport. Finite successor enumerations and complete finite vocabularies
remain explicit data of the presented system.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedGradedFamilyDescent

open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassFamilyDescent

universe uS uAtom uLabel uObs uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{uS}} {K : Scale V}
variable (system : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)
variable (vocabulary : system.Vocabulary)

abbrev BoundedFormula (depth : Nat) := {formula : system.Formula // formula.depth ≤ depth}

def readout (depth : Nat) (source : S.Term) : BoundedFormula system depth → V :=
  fun formula => system.val formula.val source

theorem readout_eq_iff (depth : Nat) (left right : S.Term) :
    readout system depth left = readout system depth right ↔
      system.depthBound vocabulary depth left right = 0 := by
  constructor
  · intro same
    exact (system.depthBound_eq_zero_iff vocabulary depth left right).mpr
      (fun formula bounded => congrFun same ⟨formula, bounded⟩)
  · intro zero
    funext formula
    exact (system.depthBound_eq_zero_iff vocabulary depth left right).mp zero formula.val formula.property

theorem readout_respects_equations (depth : Nat) {left right : S.Term}
    (same : S.Equiv left right) : readout system depth left = readout system depth right := by
  funext formula
  exact system.val_resp formula.val same

variable (graphs : S.Term → AccessiblePointedGraph.{uS})

theorem familyInvariant_iff_zeroInvariant (depth : Nat) :
    FamilyInvariant (readout system depth) graphs ↔
      ∀ ⦃left right⦄, system.depthBound vocabulary depth left right = 0 →
        HSet.mk (graphs left) = HSet.mk (graphs right) := by
  constructor
  · intro invariant left right zero
    exact invariant ((readout_eq_iff system vocabulary depth left right).mpr zero)
  · intro invariant left right same
    exact invariant ((readout_eq_iff system vocabulary depth left right).mp same)

theorem family_decode_exact_iff (depth : Nat) :
    (∀ source, decodedFamily graphs (classOf (readout system depth) source) = HSet.mk (graphs source)) ↔
      ∀ ⦃left right⦄, system.depthBound vocabulary depth left right = 0 →
        HSet.mk (graphs left) = HSet.mk (graphs right) :=
  (familyInvariant_iff_beta (readout system depth) graphs).symm.trans
    (familyInvariant_iff_zeroInvariant system vocabulary graphs depth)

theorem termCompatible_iff_zeroInvariant (depth : Nat) (term : SourceSection graphs) :
    TermCompatible (readout system depth) graphs term ↔
      ∀ ⦃left right⦄, system.depthBound vocabulary depth left right = 0 →
        (term left).1 = (term right).1 := by
  constructor
  · intro compatible left right zero
    exact compatible ((readout_eq_iff system vocabulary depth left right).mpr zero)
  · intro compatible left right same
    exact compatible ((readout_eq_iff system vocabulary depth left right).mp same)

theorem selected_value_exact_iff (depth : Nat) (term : SourceSection graphs) :
    (∀ source, termValue graphs term (classOf (readout system depth) source) = (term source).1) ↔
      ∀ ⦃left right⦄, system.depthBound vocabulary depth left right = 0 →
        (term left).1 = (term right).1 :=
  (termCompatible_iff_beta (readout system depth) graphs term).symm.trans
    (termCompatible_iff_zeroInvariant system vocabulary graphs depth term)

variable (depth : Nat)
variable (invariant : ∀ ⦃left right⦄, system.depthBound vocabulary depth left right = 0 →
  HSet.mk (graphs left) = HSet.mk (graphs right))

/-- The whole observed section carrier is constructed by the existing
family and term graph decoders, rather than supplied as a smallness field. -/
def sectionEquiv :
    (∀ observed : ObservationClass (readout system depth), El (· ∈ ·) (decodedFamily graphs observed)) ≃
      {term : SourceSection graphs // ∀ ⦃left right⦄,
        system.depthBound vocabulary depth left right = 0 → (term left).1 = (term right).1} :=
  (materialSectionEquiv (readout system depth) graphs
      ((familyInvariant_iff_zeroInvariant system vocabulary graphs depth).mpr invariant)).trans {
    toFun term := ⟨term.val, (termCompatible_iff_zeroInvariant system vocabulary graphs depth term.val).mp term.property⟩
    invFun term := ⟨term.val, (termCompatible_iff_zeroInvariant system vocabulary graphs depth term.val).mpr term.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }

theorem sectionEquiv_inverse_value
    (term : {term : SourceSection graphs // ∀ ⦃left right⦄,
      system.depthBound vocabulary depth left right = 0 → (term left).1 = (term right).1})
    (source : S.Term) :
    ((sectionEquiv system vocabulary graphs depth invariant).symm term
      (classOf (readout system depth) source)).1 = (term.val source).1 :=
  descendTerm_beta_value (readout system depth) graphs
    ((familyInvariant_iff_zeroInvariant system vocabulary graphs depth).mpr invariant)
    term.val ((termCompatible_iff_zeroInvariant system vocabulary graphs depth term.val).mpr term.property) source

def forgetReading {less more : Nat} (bounded : less ≤ more)
    (reading : BoundedFormula system more → V) : BoundedFormula system less → V :=
  fun formula => reading ⟨formula.val, formula.property.trans bounded⟩

theorem readout_forget {less more : Nat} (bounded : less ≤ more) (source : S.Term) :
    readout system less source = forgetReading system bounded (readout system more source) := rfl

def forgetClass {less more : Nat} (bounded : less ≤ more) :
    ObservationClass (readout system more) → ObservationClass (readout system less) :=
  classMap (readout system less) (readout system more) id (forgetReading system bounded)
    (readout_forget system bounded)

theorem forgetClass_beta {less more : Nat} (bounded : less ≤ more) (source : S.Term) :
    forgetClass system bounded (classOf (readout system more) source) =
      classOf (readout system less) source :=
  classMap_beta (readout system less) (readout system more) id (forgetReading system bounded)
    (readout_forget system bounded) source

theorem forgetClass_id (observed : ObservationClass (readout system depth)) :
    forgetClass system (Nat.le_refl depth) observed = observed := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system depth) observed
  exact forgetClass_beta system _ source

theorem forgetClass_comp {first second third : Nat} (one : first ≤ second) (two : second ≤ third)
    (observed : ObservationClass (readout system third)) :
    forgetClass system one (forgetClass system two observed) = forgetClass system (one.trans two) observed := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system third) observed
  rw [forgetClass_beta, forgetClass_beta, forgetClass_beta]

theorem familyInvariant_more {less more : Nat} (bounded : less ≤ more)
    (stable : FamilyInvariant (readout system less) graphs) :
    FamilyInvariant (readout system more) graphs := by
  intro left right same
  exact stable (congrArg (forgetReading system bounded) same)

theorem termCompatible_more {less more : Nat} (bounded : less ≤ more)
    (term : SourceSection graphs) (stable : TermCompatible (readout system less) graphs term) :
    TermCompatible (readout system more) graphs term := by
  intro left right same
  exact stable (congrArg (forgetReading system bounded) same)

theorem decoded_family_coarsening {less more : Nat} (bounded : less ≤ more)
    (stable : FamilyInvariant (readout system less) graphs)
    (observed : ObservationClass (readout system more)) :
    decodedFamily graphs (forgetClass system bounded observed) = decodedFamily graphs observed := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system more) observed
  rw [forgetClass_beta, family_beta (readout system less) graphs stable,
    family_beta (readout system more) graphs (familyInvariant_more system graphs bounded stable)]

theorem selected_value_coarsening {less more : Nat} (bounded : less ≤ more)
    (term : SourceSection graphs) (stable : TermCompatible (readout system less) graphs term)
    (observed : ObservationClass (readout system more)) :
    termValue graphs term (forgetClass system bounded observed) = termValue graphs term observed := by
  obtain ⟨source, rfl⟩ := classOf_surjective (readout system more) observed
  rw [forgetClass_beta, termValue_beta (readout system less) graphs term stable,
    termValue_beta (readout system more) graphs term (termCompatible_more system graphs bounded term stable)]

end Mettapedia.GSLT.ObservedGradedFamilyDescent
