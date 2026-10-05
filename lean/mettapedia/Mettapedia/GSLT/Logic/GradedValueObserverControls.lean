import Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent

/-!
# Fine and coarse observation signatures on the same authored cycle

The two-state system advances by Boolean negation. Its original atoms name
the state bit. A fine integer reading retains that bit, with explicit modal
interpretations in both directions. A coarse reading hides the bit even
though all original atoms and actions remain authored data. Its graded bound
stabilizes at depth zero; exact-value modal native predicates descend, while
the old atom naming the true state provably does not.

The exact-value atoms include every integer value, even though the numeric
reading has only two possible results. No finite atomic vocabulary or
classical modal reflection is used.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GradedValueObserverControls

open HennessyMilner Distinction.Constructive GradedValueObserver
open Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

def unitScale : Scale ℤ := Scale.integers 1 (by decide)

theorem unitScale_positive : unitScale.Positive := Scale.integers_positive 1 _

def cycleTheory : GSLT := equalityGSLT Bool (fun source target => target = !source)

def cycleDynamics : System.{0, 0} cycleTheory where
  Atom := Bool
  observes atom source := source = atom
  observes_resp _ _ _ same := by
    cases same
    rfl
  Label := Unit
  act _ source target := target = !source
  act_resp_left := by
    intro label left right target same action
    cases same
    exact ⟨_, action, rfl⟩
  act_resp_right := by
    intro label source target target' action same
    cases same
    exact action

def coarse : PresentedSystem.{0, 0, 0, 0, 0} cycleTheory unitScale where
  dynamics := cycleDynamics
  Obs := Unit
  value _ _ := 0
  value_nonneg _ _ := by decide
  value_le_one _ _ := by decide
  value_resp _ _ _ _ := rfl
  successors _ source := [!source]
  successors_act member := List.mem_singleton.mp member
  successors_cover action := ⟨_, List.mem_singleton_self _, action⟩

def fine : PresentedSystem.{0, 0, 0, 0, 0} cycleTheory unitScale where
  dynamics := cycleDynamics
  Obs := Unit
  value _ source := match (show Bool from source) with
    | false => 0
    | true => 1
  value_nonneg _ source := by cases source <;> decide
  value_le_one _ source := by cases source <;> decide
  value_resp _ _ _ same := by cases same; rfl
  successors _ source := [!source]
  successors_act member := List.mem_singleton.mp member
  successors_cover action := ⟨_, List.mem_singleton_self _, action⟩

def coarseVocabulary : coarse.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

def fineVocabulary : fine.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

theorem coarse_stabilizes : coarse.Stabilizes coarseVocabulary 0 := by
  intro left right
  cases left <;> cases right <;> decide

theorem fine_stabilizes : fine.Stabilizes fineVocabulary 0 := by
  intro left right
  cases left <;> cases right <;> decide

/-- The coarse observer has an explicit bisimulation covering the cycle. -/
theorem coarse_graded (left right : Bool) : coarse.GradedBisimilar left right := by
  refine ⟨fun _ _ => True, ⟨?_, ?_, ?_⟩, True.intro⟩
  · intro first second related label target action
    exact ⟨!second, rfl, True.intro⟩
  · intro first second related label target action
    exact ⟨!first, rfl, True.intro⟩
  · intro first second related observation
    rfl

theorem coarse_value_bisimilar : (valueSystem coarse).Bisimilar false true :=
  (bisimilar_iff_graded coarse false true).mpr (coarse_graded false true)

theorem original_not_bisimilar : ¬ cycleDynamics.Bisimilar false true := by
  rintro ⟨relation, bisimulation, related⟩
  have agreement := bisimulation.2.2 related true
  have impossible : false = true := agreement.mpr rfl
  cases impossible

theorem inherited_atoms_are_not_the_graded_signature :
    coarse.GradedBisimilar false true ∧ ¬ coarse.dynamics.Bisimilar false true :=
  ⟨coarse_graded false true, original_not_bisimilar⟩

theorem coarse_readout_equal :
    ObservedGradedFamilyDescent.readout coarse 0 false =
      ObservedGradedFamilyDescent.readout coarse 0 true :=
  (readout_eq_iff_graded coarse coarseVocabulary 0 unitScale_positive coarse_stabilizes
    false true).mpr (coarse_graded false true)

theorem coarse_readout_equal_at_every_depth (depth : Nat) :
    ObservedGradedFamilyDescent.readout coarse depth false =
      ObservedGradedFamilyDescent.readout coarse depth true :=
  (ObservedGradedFamilyDescent.readout_eq_iff coarse coarseVocabulary depth false true).mpr
    (coarse.depthBound_eq_zero_of_gradedBisimilar coarseVocabulary (coarse_graded false true) depth)

theorem coarse_has_authored_action : coarse.dynamics.act () false true := rfl

theorem coarse_modal_native_accepts :
    (formulaPredicate (stageSystem coarse 0) (.dia () (.atom ((), (0 : ℤ))))).1
      (stateOf coarse 0 false) := by
  apply (native_predicate_stage_iff coarse coarseVocabulary 0 unitScale_positive coarse_stabilizes
    (.dia () (.atom ((), (0 : ℤ)))) false).mpr
  exact ⟨true, rfl, rfl⟩

theorem coarse_full_formula_native_descent
    (formula : Formula (valueSystem coarse).Atom coarse.dynamics.Label) :
    ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout coarse 0)
      (formulaPredicate (valueSystem coarse) formula).1 :=
  formula_native_predicate_descends coarse coarseVocabulary 0 unitScale_positive coarse_stabilizes formula

/-- The old state atom cannot factor through this actual stabilized readout. -/
theorem original_atom_no_descent :
    ¬ ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout coarse 0)
      (formulaPredicate coarse.dynamics (.atom true)).1 := by
  rintro ⟨observed, exactness⟩
  have holds := (exactness true).mpr (show coarse.dynamics.sat (.atom true) true from rfl)
  have acceptsFalse := (exactness false).mp (coarse_readout_equal.symm ▸ holds)
  have impossible : false = true := acceptsFalse
  cases impossible

theorem original_atom_no_descent_at_any_depth (depth : Nat) :
    ¬ ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout coarse depth)
      (formulaPredicate coarse.dynamics (.atom true)).1 := by
  rintro ⟨observed, exactness⟩
  have holds := (exactness true).mpr (show coarse.dynamics.sat (.atom true) true from rfl)
  have acceptsFalse := (exactness false).mp ((coarse_readout_equal_at_every_depth depth).symm ▸ holds)
  have impossible : false = true := acceptsFalse
  cases impossible

theorem coarse_no_original_atom_interpretation : ¬ Nonempty (OriginalAtomInterpretation coarse) := by
  rintro ⟨interpretation⟩
  exact original_atom_no_descent
    (original_native_predicate_descends coarse coarseVocabulary 0 unitScale_positive
      coarse_stabilizes interpretation (.atom true))

def fineOriginalAtoms : OriginalAtomInterpretation fine where
  formula atom := match (show Bool from atom) with
    | false => .atom ((), (0 : ℤ))
    | true => .atom ((), (1 : ℤ))
  correct atom source := by
    cases atom <;> cases source
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · constructor
      · intro impossible
        exact ((show (1 : ℤ) ≠ 0 by decide) impossible).elim
      · intro impossible
        cases impossible
    · constructor
      · intro impossible
        exact ((show (0 : ℤ) ≠ 1 by decide) impossible).elim
      · intro impossible
        cases impossible
    · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- All integer equality tests have explicit old-signature formulas, including
the constantly false tests for values outside the actual reading range. -/
def fineValueAtoms : ValueAtomInterpretation fine where
  formula atom := if atom.2 = 0 then .atom false else
    if atom.2 = 1 then .atom true else .neg .top
  correct atom source := by
    rcases atom with ⟨observation, value⟩
    by_cases zero : value = 0
    · rw [if_pos zero]
      cases source
      · exact ⟨fun _ => zero.symm, fun _ => rfl⟩
      · constructor
        · intro impossible
          cases impossible
        · intro equal
          exact ((show (1 : ℤ) ≠ 0 by decide) (equal.trans zero)).elim
    · rw [if_neg zero]
      by_cases one : value = 1
      · rw [if_pos one]
        cases source
        · constructor
          · intro impossible
            cases impossible
          · intro equal
            exact ((show (0 : ℤ) ≠ 1 by decide) (equal.trans one)).elim
        · exact ⟨fun _ => one.symm, fun _ => rfl⟩
      · rw [if_neg one]
        cases source
        · exact ⟨fun impossible => (impossible True.intro).elim,
            fun equal _ => zero equal.symm⟩
        · exact ⟨fun impossible => (impossible True.intro).elim,
            fun equal _ => one equal.symm⟩

theorem fine_signature_agreement (left right : Bool) :
    fine.dynamics.Bisimilar left right ↔ fine.GradedBisimilar left right :=
  original_bisimilar_iff_graded fine fineOriginalAtoms fineValueAtoms left right

theorem fine_full_formula_translation
    (formula : Formula fine.dynamics.Atom fine.dynamics.Label) (source : Bool) :
    (valueSystem fine).sat (translateOriginal fine fineOriginalAtoms formula) source ↔
      fine.dynamics.sat formula source :=
  translateOriginal_sat fine fineOriginalAtoms formula source

theorem fine_original_native_descent
    (formula : Formula fine.dynamics.Atom fine.dynamics.Label) :
    ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout fine 0)
      (formulaPredicate fine.dynamics formula).1 :=
  original_native_predicate_descends fine fineVocabulary 0 unitScale_positive fine_stabilizes
    fineOriginalAtoms formula

theorem fine_readout_separates :
    ObservedGradedFamilyDescent.readout fine 0 false ≠
      ObservedGradedFamilyDescent.readout fine 0 true := by
  intro same
  have values := congrFun same ⟨.atom (), Nat.zero_le 0⟩
  exact (show (0 : ℤ) ≠ 1 by decide) values

theorem fine_modal_atom_distinguishes :
    (valueSystem fine).sat (.atom ((), (0 : ℤ))) false ∧
      ¬ (valueSystem fine).sat (.atom ((), (0 : ℤ))) true := by
  constructor
  · rfl
  · change (1 : ℤ) ≠ 0
    decide

end Mettapedia.GSLT.GradedValueObserverControls
