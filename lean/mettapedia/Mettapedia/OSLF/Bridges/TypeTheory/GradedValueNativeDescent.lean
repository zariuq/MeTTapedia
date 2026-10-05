import Mettapedia.GSLT.Logic.GradedValueObserver
import Mettapedia.GSLT.Logic.ObservedGradedFamilyDescent
import Mettapedia.GSLT.Logic.ObservationSpans
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-!
# Native modal predicates on stabilized graded observation classes

The target is an actual labelled modal system on the represented classes of
the finite-depth readout. Its atoms are existential images of the exact-value
tests, and its actions are the authored labelled actions with class endpoints.
A positive discount and an actual stabilization certificate identify the
readout kernel with graded bisimilarity. Successor lifting is derived from
that bisimulation, and all full Hennessy--Milner formulas consequently preserve
and reflect satisfaction across the class map.

This gives exact descent for the existing formula-generated native predicates.
Arbitrary native predicates require their own kernel constancy, proved here to
be necessary as well as sufficient. There is no assertion about predecessor
box, old atomic signatures, selected terms, or occurrence identity.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.Constructive Mettapedia.GSLT.GradedValueObserver
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

universe uS uAtom uLabel uObs uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{uS}} {K : Scale V}
variable (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)

abbrev StageState (stage : Nat) :=
  ObservationClass (ObservedGradedFamilyDescent.readout Q stage)

def stateOf (stage : Nat) (source : S.Term) : StageState Q stage :=
  classOf (ObservedGradedFamilyDescent.readout Q stage) source

theorem stateOf_surjective (stage : Nat) : Function.Surjective (stateOf Q stage) :=
  classOf_surjective (ObservedGradedFamilyDescent.readout Q stage)

/-- The labelled action relation retains the actual authored source and target
as witnesses; its public endpoints are complete observation classes. -/
def stageAction (stage : Nat) (label : Q.dynamics.Label)
    (source target : StageState Q stage) : Prop :=
  ∃ left right, stateOf Q stage left = source ∧ stateOf Q stage right = target ∧
    Q.dynamics.act label left right

def stageTheory (stage : Nat) : GSLT.{uS} :=
  equalityGSLT (StageState Q stage) (fun source target =>
    ∃ label, stageAction Q stage label source target)

def stageSystem (stage : Nat) : System.{max uObs uV, uLabel} (stageTheory Q stage) where
  Atom := (valueSystem Q).Atom
  observes atom state := ∃ source, stateOf Q stage source = state ∧
    (valueSystem Q).observes atom source
  observes_resp _ _ _ same := by
    cases same
    rfl
  Label := Q.dynamics.Label
  act := stageAction Q stage
  act_resp_left := by
    intro label left right target same action
    cases same
    exact ⟨_, action, rfl⟩
  act_resp_right := by
    intro label source target target' action same
    cases same
    exact action

theorem action_to_stage (stage : Nat) (label : Q.dynamics.Label)
    {source target : S.Term} (action : Q.dynamics.act label source target) :
    (stageSystem Q stage).act label (stateOf Q stage source) (stateOf Q stage target) :=
  ⟨source, target, rfl, rfl, action⟩

variable (vocabulary : Q.Vocabulary) (stage : Nat)
variable (positive : K.Positive) (stable : Q.Stabilizes vocabulary stage)

include vocabulary positive stable in
theorem readout_eq_iff_graded (left right : S.Term) :
    ObservedGradedFamilyDescent.readout Q stage left =
      ObservedGradedFamilyDescent.readout Q stage right ↔ Q.GradedBisimilar left right :=
  (ObservedGradedFamilyDescent.readout_eq_iff Q vocabulary stage left right).trans
    (Q.gradedBisimilar_iff_of_stabilizes vocabulary positive stable left right).2.symm

include vocabulary positive stable in
theorem stateOf_eq_iff_graded (left right : S.Term) :
    stateOf Q stage left = stateOf Q stage right ↔ Q.GradedBisimilar left right :=
  (classOf_eq_iff (ObservedGradedFamilyDescent.readout Q stage) left right).trans
    (readout_eq_iff_graded Q vocabulary stage positive stable left right)

include vocabulary positive stable in
theorem value_eq_of_stateOf_eq {left right : S.Term}
    (same : stateOf Q stage left = stateOf Q stage right) (observation : Q.Obs) :
    Q.value observation left = Q.value observation right := by
  obtain ⟨relation, bisimulation, related⟩ :=
    (stateOf_eq_iff_graded Q vocabulary stage positive stable left right).mp same
  exact bisimulation.2.2 related observation

include vocabulary positive stable in
theorem atom_stage_iff (atom : (valueSystem Q).Atom) (source : S.Term) :
    (stageSystem Q stage).observes atom (stateOf Q stage source) ↔
      (valueSystem Q).observes atom source := by
  constructor
  · rintro ⟨other, same, holds⟩
    change Q.value atom.1 other = atom.2 at holds
    change Q.value atom.1 source = atom.2
    exact (value_eq_of_stateOf_eq Q vocabulary stage positive stable same atom.1).symm.trans holds
  · intro holds
    exact ⟨source, rfl, holds⟩

include vocabulary positive stable in
/-- This lifting is derived from the graded bisimulation witness and is about
successors. It supplies no incoming-action lifting. -/
theorem action_from_stage (label : Q.dynamics.Label) (source : S.Term)
    {target : StageState Q stage}
    (action : (stageSystem Q stage).act label (stateOf Q stage source) target) :
    ∃ actual, Q.dynamics.act label source actual ∧ stateOf Q stage actual = target := by
  obtain ⟨left, right, sourceEq, targetEq, authored⟩ := action
  obtain ⟨relation, bisimulation, related⟩ :=
    (stateOf_eq_iff_graded Q vocabulary stage positive stable left source).mp sourceEq
  obtain ⟨actual, lifted, targetRelated⟩ := bisimulation.1 related label authored
  have same : stateOf Q stage right = stateOf Q stage actual :=
    (stateOf_eq_iff_graded Q vocabulary stage positive stable right actual).mpr
      ⟨relation, bisimulation, targetRelated⟩
  exact ⟨actual, lifted, same.symm.trans targetEq⟩

include vocabulary positive stable in
/-- A bisimulation of the constructed class dynamics lifts back to an actual
graded bisimulation, using the derived action lift at both related sources. -/
theorem graded_pullback_of_stage_bisimulation
    {relation : StageState Q stage → StageState Q stage → Prop}
    (bisimulation : (stageSystem Q stage).IsBisimulation relation) :
    Q.IsGradedBisimulation (fun left right =>
      relation (stateOf Q stage left) (stateOf Q stage right)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right related label target action
    obtain ⟨observed, observedAction, relatedTarget⟩ := bisimulation.1 related label
      (action_to_stage Q stage label action)
    obtain ⟨actual, lifted, same⟩ :=
      action_from_stage Q vocabulary stage positive stable label right observedAction
    rw [← same] at relatedTarget
    exact ⟨actual, lifted, relatedTarget⟩
  · intro left right related label target action
    obtain ⟨observed, observedAction, relatedTarget⟩ := bisimulation.2.1 related label
      (action_to_stage Q stage label action)
    obtain ⟨actual, lifted, same⟩ :=
      action_from_stage Q vocabulary stage positive stable label left observedAction
    rw [← same] at relatedTarget
    exact ⟨actual, lifted, relatedTarget⟩
  · intro left right related
    apply (atomic_agreement_iff Q left right).mp
    intro atom
    exact (atom_stage_iff Q vocabulary stage positive stable atom left).symm.trans
      ((bisimulation.2.2 related atom).trans
        (atom_stage_iff Q vocabulary stage positive stable atom right))

include vocabulary positive stable in
/-- The represented stage classes are already separated by the constructed
ordinary bisimulation. This is derived from action lifting, not modal
reflection or an identification of the old atomic signature. -/
theorem stage_bisimilar_iff_eq (left right : StageState Q stage) :
    (stageSystem Q stage).Bisimilar left right ↔ left = right := by
  constructor
  · obtain ⟨sourceLeft, rfl⟩ := stateOf_surjective Q stage left
    obtain ⟨sourceRight, rfl⟩ := stateOf_surjective Q stage right
    rintro ⟨relation, bisimulation, related⟩
    exact (stateOf_eq_iff_graded Q vocabulary stage positive stable sourceLeft sourceRight).mpr
      ⟨fun first second => relation (stateOf Q stage first) (stateOf Q stage second),
        graded_pullback_of_stage_bisimulation Q vocabulary stage positive stable bisimulation, related⟩
  · intro same
    exact same ▸ (stageSystem Q stage).bisimilar_refl left

include vocabulary positive stable in
theorem source_bisimilar_iff_stage_bisimilar (left right : S.Term) :
    (valueSystem Q).Bisimilar left right ↔
      (stageSystem Q stage).Bisimilar (stateOf Q stage left) (stateOf Q stage right) :=
  (bisimilar_iff_graded Q left right).trans
    ((stateOf_eq_iff_graded Q vocabulary stage positive stable left right).symm.trans
      (stage_bisimilar_iff_eq Q vocabulary stage positive stable _ _).symm)

include vocabulary positive stable in
/-- Preservation and reflection for the complete formula language follow by
induction, with genuine lifting in the diamond case. -/
theorem formula_stage_iff :
    ∀ (formula : Formula (valueSystem Q).Atom Q.dynamics.Label) (source : S.Term),
      (stageSystem Q stage).sat formula (stateOf Q stage source) ↔
        (valueSystem Q).sat formula source
  | .top, _ => Iff.rfl
  | .atom atom, source => atom_stage_iff Q vocabulary stage positive stable atom source
  | .conj left right, source =>
      and_congr (formula_stage_iff left source) (formula_stage_iff right source)
  | .neg inner, source => not_congr (formula_stage_iff inner source)
  | .dia label inner, source => by
      constructor
      · rintro ⟨target, action, holds⟩
        obtain ⟨actual, lifted, same⟩ :=
          action_from_stage Q vocabulary stage positive stable label source action
        rw [← same] at holds
        exact ⟨actual, lifted, (formula_stage_iff inner actual).mp holds⟩
      · rintro ⟨actual, action, holds⟩
        exact ⟨stateOf Q stage actual, action_to_stage Q stage label action,
          (formula_stage_iff inner actual).mpr holds⟩

include vocabulary positive stable in
/-- The existing native predicates, rather than an independently supplied
predicate interpretation, commute across the constructed observation map. -/
theorem native_predicate_stage_iff
    (formula : Formula (valueSystem Q).Atom Q.dynamics.Label) (source : S.Term) :
    (formulaPredicate (stageSystem Q stage) formula).1 (stateOf Q stage source) ↔
      (formulaPredicate (valueSystem Q) formula).1 source :=
  formula_stage_iff Q vocabulary stage positive stable formula source

/-- The actual existential image of an arbitrary equation-invariant native
predicate on the represented stage classes. -/
def nativeImage (predicate : EquationPredicate S) : StageState Q stage → Prop :=
  fun observed => ∃ source, stateOf Q stage source = observed ∧ predicate.1 source

theorem nativeImage_exact_iff (predicate : EquationPredicate S) :
    (∀ source, nativeImage Q stage predicate (stateOf Q stage source) ↔ predicate.1 source) ↔
      ∀ ⦃left right⦄, ObservedGradedFamilyDescent.readout Q stage left =
        ObservedGradedFamilyDescent.readout Q stage right →
          (predicate.1 left ↔ predicate.1 right) := by
  constructor
  · intro exactImage left right same
    have classEq := (classOf_eq_iff (ObservedGradedFamilyDescent.readout Q stage) left right).mpr same
    exact ⟨fun holds => (exactImage right).mp ⟨left, classEq, holds⟩,
      fun holds => (exactImage left).mp ⟨right, classEq.symm, holds⟩⟩
  · intro constant source
    constructor
    · rintro ⟨other, same, holds⟩
      exact (constant ((classOf_eq_iff (ObservedGradedFamilyDescent.readout Q stage) other source).mp same)).mp holds
    · intro holds
      exact ⟨source, rfl, holds⟩

include vocabulary positive stable in
theorem nativeImage_exact_iff_graded (predicate : EquationPredicate S) :
    (∀ source, nativeImage Q stage predicate (stateOf Q stage source) ↔ predicate.1 source) ↔
      ∀ ⦃left right⦄, Q.GradedBisimilar left right → (predicate.1 left ↔ predicate.1 right) := by
  rw [nativeImage_exact_iff]
  constructor
  · intro invariant left right related
    exact invariant ((readout_eq_iff_graded Q vocabulary stage positive stable left right).mpr related)
  · intro invariant left right same
    exact invariant ((readout_eq_iff_graded Q vocabulary stage positive stable left right).mp same)

include vocabulary positive stable in
theorem formula_nativeImage_beta
    (formula : Formula (valueSystem Q).Atom Q.dynamics.Label) (source : S.Term) :
    nativeImage Q stage (formulaPredicate (valueSystem Q) formula) (stateOf Q stage source) ↔
      (formulaPredicate (valueSystem Q) formula).1 source := by
  have exactImage := (nativeImage_exact_iff_graded Q vocabulary stage positive stable
    (formulaPredicate (valueSystem Q) formula)).mpr
      (fun {left right} related => logicallyEquivalent_of_graded Q related formula)
  exact exactImage source

include vocabulary positive stable in
theorem formula_native_predicate_descends
    (formula : Formula (valueSystem Q).Atom Q.dynamics.Label) :
    ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout Q stage)
      (formulaPredicate (valueSystem Q) formula).1 := by
  apply (ObservationSpans.predicateDescends_iff _ _).mpr
  intro left right same
  exact propext (logicallyEquivalent_of_graded Q
    ((readout_eq_iff_graded Q vocabulary stage positive stable left right).mp same) formula)

include vocabulary positive stable in
/-- Exact descent of an arbitrary native predicate is an additional
observational law, not a consequence of respecting authored equations. -/
theorem native_predicate_descends_iff_graded (predicate : EquationPredicate S) :
    ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout Q stage) predicate.1 ↔
      ∀ ⦃left right⦄, Q.GradedBisimilar left right → (predicate.1 left ↔ predicate.1 right) := by
  rw [ObservationSpans.predicateDescends_iff]
  constructor
  · intro constant left right related
    exact Iff.of_eq (constant left right
      ((readout_eq_iff_graded Q vocabulary stage positive stable left right).mpr related))
  · intro invariant left right same
    exact propext (invariant
      ((readout_eq_iff_graded Q vocabulary stage positive stable left right).mp same))

include vocabulary positive stable in
/-- On every represented class the actual native image agrees with the
independently interpreted formula of the constructed stage system. -/
theorem formula_nativeImage_stage_iff
    (formula : Formula (valueSystem Q).Atom Q.dynamics.Label) (observed : StageState Q stage) :
    nativeImage Q stage (formulaPredicate (valueSystem Q) formula) observed ↔
      (formulaPredicate (stageSystem Q stage) formula).1 observed := by
  obtain ⟨source, rfl⟩ := stateOf_surjective Q stage observed
  exact (formula_nativeImage_beta Q vocabulary stage positive stable formula source).trans
    (native_predicate_stage_iff Q vocabulary stage positive stable formula source).symm

include vocabulary positive stable in
theorem original_native_predicate_descends (interpretation : OriginalAtomInterpretation Q)
    (formula : Formula Q.dynamics.Atom Q.dynamics.Label) :
    ObservationSpans.PredicateDescends (ObservedGradedFamilyDescent.readout Q stage)
      (formulaPredicate Q.dynamics formula).1 := by
  obtain ⟨observed, exactness⟩ := formula_native_predicate_descends Q vocabulary stage positive stable
    (translateOriginal Q interpretation formula)
  exact ⟨observed, fun source =>
    (exactness source).trans (translateOriginal_sat Q interpretation formula source)⟩

end Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
