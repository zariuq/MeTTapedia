import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEvents
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalControls

/-!
# Overlapping beta firings in the generic event presheaf

The general beta declaration and its identity-body specialization are the
existing rule-local declarations. Their closed identity application is moved
to the actual equation-class classifier and then represented in its generic
event presheaf. Its two witnesses remain distinct, while their endpoint pairs
have the same reduction-image membership.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheafMultiplicityControl

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

abbrev sourceSignature := IntrinsicScopedLocalControls.sig
abbrev sourceRules := IntrinsicScopedLocalControls.family
abbrev noEquations : List (EqAxiom sourceSignature []) := []
abbrev sourceBase : Base noEquations := ⟨⟨[]⟩⟩
abbrev sourceStage : Classifier sourceRules noEquations :=
  (programSection sourceRules noEquations).obj sourceBase
abbrev programs := modelAt noEquations sourceBase

/-- The existing initial binding-clone interpretation into the actual
classifier's equation-class program model. -/
def programMap : FreeBindingClone.Hom IntrinsicScopedLocalControls.algebra programs :=
  FreeBindingClone.interpretHom programs

abbrev argument : IntrinsicScopedLocalControls.Tm [] :=
  IntrinsicScopedLocalControls.symbol 0
abbrev rawJudgment : Judgment IntrinsicScopedLocalControls.algebra :=
  conclusionJudgment sourceRules IntrinsicScopedLocalControls.algebra
    (IntrinsicScopedLocalControls.identityOccurrence argument)
def judgment : Judgment programs :=
  ⟨[], (), programMap.raw.map
    (IntrinsicScopedLocalControls.app (IntrinsicScopedLocalControls.lam (.var .zero)) argument),
    programMap.raw.map argument⟩

/-- The displayed endpoints are obtained from the original specialization,
not selected independently of its rule constructor. -/
theorem identityJudgment : mapJudgment programMap rawJudgment = judgment :=
  congrArg (mapJudgment programMap)
    (IntrinsicScopedLocalControls.identity_conclusion argument)
abbrev eventSeeds := seeds sourceRules programs (events sourceRules noEquations sourceStage)
abbrev Firing := IntrinsicScopedLocalActedFree.Tree sourceRules programs eventSeeds

/-- The general beta rule's existing closed derivation, with the canonical
program interpretation and closed-tree embedding applied to it. -/
def generalFiringUncast : Firing (mapJudgment programMap
    (conclusionJudgment sourceRules IntrinsicScopedLocalControls.algebra
      (IntrinsicScopedLocalControls.betaOccurrence (.var .zero) argument))) :=
  IntrinsicScopedLocalActedFree.embedClosed sourceRules programs eventSeeds _
    (mapTree sourceRules programMap _
      (IntrinsicScopedLocalControls.betaTree (.var .zero) argument))

/-- The existing endpoint equality is transported by the same program map. -/
theorem overlappingJudgments :
    mapJudgment programMap
        (conclusionJudgment sourceRules IntrinsicScopedLocalControls.algebra
          (IntrinsicScopedLocalControls.betaOccurrence (.var .zero) argument)) = judgment :=
  congrArg (mapJudgment programMap)
    (IntrinsicScopedLocalControls.overlapping_endpoints argument) |>.trans identityJudgment

def generalFiring : Firing judgment := overlappingJudgments ▸ generalFiringUncast

def identityFiringUncast : Firing (mapJudgment programMap rawJudgment) :=
  IntrinsicScopedLocalActedFree.embedClosed sourceRules programs eventSeeds _
    (mapTree sourceRules programMap _ (IntrinsicScopedLocalControls.identityTree argument))

def identityFiring : Firing judgment := identityJudgment ▸ identityFiringUncast

/-- Observe only the actual root declaration address, without inspecting
its endpoints or the values of unrelated metavariables. -/
def rootRule {j : Judgment programs} (tree : Firing j) : Option (Fin sourceRules.length) :=
  match (IndexedPolynomial.Fix.out
      ((rules sourceRules programs).withHoles
        (fun _ j => IntrinsicScopedLocalActedFree.Holes programs eventSeeds j)) tree).1 with
  | .inl _ => none
  | .inr constructor => some constructor.1.index

theorem rootRule_cast {j k : Judgment programs} (same : j = k) (tree : Firing j) :
    rootRule (same ▸ tree) = rootRule tree := by
  cases same
  rfl

/-- Base interpretation and the closed-tree embedding retain the general
rule's original address. -/
theorem general_root : rootRule generalFiring = some ⟨0, by decide⟩ := by
  exact (rootRule_cast overlappingJudgments generalFiringUncast).trans (by rfl)

/-- The specialization retains its different original declaration address. -/
theorem identity_root : rootRule identityFiring = some ⟨1, by decide⟩ := by
  exact (rootRule_cast identityJudgment identityFiringUncast).trans (by rfl)

/-- Actual overlapping rule firings stay distinct in the substitution-closed
free model over the classifier's program base. -/
theorem firings_distinct : generalFiring ≠ identityFiring := by
  intro same
  have addresses := congrArg rootRule same
  rw [general_root, identity_root] at addresses
  cases addresses

abbrev generalSection :
    (event.{0} sourceRules noEquations [] ()).obj (Opposite.op sourceStage) :=
  ULift.up (rep sourceRules noEquations (a := sourceStage) judgment generalFiring)
abbrev identitySection :
    (event.{0} sourceRules noEquations [] ()).obj (Opposite.op sourceStage) :=
  ULift.up (rep sourceRules noEquations (a := sourceStage) judgment identityFiring)

/-- The actual presheaf embedding keeps both complete constructor histories. -/
theorem event_sections_distinct : generalSection ≠ identitySection :=
  generic_tree_sections_distinct (R := sourceRules) (equations := noEquations) (a := sourceStage) judgment generalFiring identityFiring firings_distinct

/-- Both sections have the same source program. -/
theorem sources_equal :
    (genericEventSource sourceRules noEquations [] ()).app (Opposite.op sourceStage) generalSection =
      (genericEventSource sourceRules noEquations [] ()).app (Opposite.op sourceStage) identitySection := by
  apply ULift.ext
  exact generic_tree_source_equal (R := sourceRules) (equations := noEquations) (a := sourceStage) judgment generalFiring identityFiring

/-- Both sections have the same target program. -/
theorem targets_equal :
    (genericEventTarget sourceRules noEquations [] ()).app (Opposite.op sourceStage) generalSection =
      (genericEventTarget sourceRules noEquations [] ()).app (Opposite.op sourceStage) identitySection := by
  apply ULift.ext
  exact generic_tree_target_equal (R := sourceRules) (equations := noEquations) (a := sourceStage) judgment generalFiring identityFiring

abbrev endpointPair (e : (event.{0} sourceRules noEquations [] ()).obj
    (Opposite.op sourceStage)) :=
  ((genericEventSource sourceRules noEquations [] ()).app (Opposite.op sourceStage) e,
    (genericEventTarget sourceRules noEquations [] ()).app (Opposite.op sourceStage) e)

/-- The reduction image observes the same pair even though the two event
sections remain distinct. -/
theorem endpoint_pairs_equal : endpointPair generalSection = endpointPair identitySection :=
  Prod.ext sources_equal targets_equal

theorem general_reduction_member : endpointPair generalSection ∈
    (genericReduction sourceRules noEquations [] ()).obj (Opposite.op sourceStage) :=
  generic_tree_reduction_member (R := sourceRules) (equations := noEquations) (a := sourceStage) judgment generalFiring

theorem identity_reduction_member : endpointPair identitySection ∈
    (genericReduction sourceRules noEquations [] ()).obj (Opposite.op sourceStage) :=
  generic_tree_reduction_member (R := sourceRules) (equations := noEquations) (a := sourceStage) judgment identityFiring

/-- A single reduction-image element has two different actual authored
firing witnesses in the generic event presheaf. -/
theorem two_firings_same_reduction :
    generalSection ≠ identitySection ∧
      endpointPair generalSection = endpointPair identitySection ∧
      endpointPair generalSection ∈
        (genericReduction sourceRules noEquations [] ()).obj (Opposite.op sourceStage) ∧
      endpointPair identitySection ∈
        (genericReduction sourceRules noEquations [] ()).obj (Opposite.op sourceStage) :=
  ⟨event_sections_distinct, endpoint_pairs_equal, general_reduction_member, identity_reduction_member⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheafMultiplicityControl
