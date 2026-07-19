import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromStability

/-!
# Routed CAROM: convex step closure and legal-action inheritance

This file closes the structural routed-decoder boundary.  A simplex mixture
of `GatedOperatorFamily` steps is a pointwise convex mixture of those steps;
the theorem does not claim that the router or expert mechanisms were learned
well.  A routed legal-action adapter then allows arbitrary route types,
temperature values, state-dependent schedules, recurrence depths, and routed
workspace steps while retaining the sealed checker-owned action support.

Consequently routing may change scores and search order, but cannot add an
illegal action, change accepted-language semantics, or remove in-budget recall.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function Set
open Mettapedia.GSLT.LanguageDef.AtomicRefinement

namespace RoutedCarom

universe uExpert uSlot uOperator uContent uRead uLatent
  uRoute uTemperature uParams

/-! ## Convex closure of expert steps -/

section ConvexSteps

variable {Expert : Type uExpert} [Fintype Expert]
variable {Slot : Type uSlot} {Operator : Type uOperator}
  {Content : Type uContent} {Read : Type uRead} {Latent : Type uLatent}
variable [Fintype Operator] [Nonempty Operator]
  [NormedAddCommGroup Content] [NormedSpace ℝ Content]

/-- One routed step is the simplex mixture of the expert-family increments.
Every expert may have arbitrary state-dependent reads, gates, and writes. -/
noncomputable def routedGatedStep
    (routing : SimplexWeights Expert)
    (expert : Expert → GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) : Workspace Slot Content :=
  fun slot => workspace slot + ∑ item,
    routing.weight item •
      ((expert item).step workspace slot - workspace slot)

omit [Nonempty Operator] in
/-- T5 convex-closure crown: the increment presentation is exactly the
pointwise convex mixture of complete expert steps. -/
theorem routedGatedStep_eq_convexMixture
    (routing : SimplexWeights Expert)
    (expert : Expert → GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) :
    routedGatedStep routing expert workspace =
      ∑ item, routing.weight item • (expert item).step workspace := by
  funext slot
  unfold routedGatedStep
  simp only [Finset.sum_apply, Pi.smul_apply]
  change workspace slot +
      ∑ item, routing.weight item •
        ((expert item).step workspace slot - workspace slot) =
    ∑ item, routing.weight item • (expert item).step workspace slot
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, routing.sum_eq_one, one_smul]
  module

omit [Nonempty Operator] in
/-- If all experts implement the same workspace step, routing is immaterial. -/
theorem routedGatedStep_constantExperts
    (routing : SimplexWeights Expert)
    (family : GatedOperatorFamily Slot Operator Content Read Latent)
    (workspace : Workspace Slot Content) :
    routedGatedStep routing (fun _ => family) workspace = family.step workspace := by
  rw [routedGatedStep_eq_convexMixture]
  rw [← Finset.sum_smul, routing.sum_eq_one, one_smul]

end ConvexSteps

/-! ## Arbitrary routed legal-action decoder -/

/-- A routed workspace scorer.  `Temperature` and `Route` are deliberately
opaque: softmax logits, hard routing, annealing, and hand-written schedules
all instantiate the same trust-boundary theorem. -/
structure RoutedLegalActionDecoder
    (root : AtomicRoot) (Slot : Type uSlot) (Content : Type uContent)
    (Route : Type uRoute) (Temperature : Type uTemperature) where
  Params : Type uParams
  parameters : Params
  temperature : Temperature
  recurrenceDepth : Nat
  routeSchedule : Params → Temperature → Nat → root.State → List Route
  initialWorkspace : root.State → Workspace Slot Content
  routedStep : Params → Temperature → Route →
    Workspace Slot Content → Workspace Slot Content
  score : Params → Workspace Slot Content → root.State →
    RefineAction root.Hole root.Head → ℝ

namespace RoutedLegalActionDecoder

variable {root : AtomicRoot} {Route : Type uRoute}
  {Temperature : Type uTemperature}
  (decoder : RoutedLegalActionDecoder root Slot Content Route Temperature)

/-- Workspace reached by the decoder's state-dependent routed schedule. -/
def settledWorkspace (state : root.State) : Workspace Slot Content :=
  (decoder.routeSchedule decoder.parameters decoder.temperature
      decoder.recurrenceDepth state).foldl
    (fun workspace route =>
      decoder.routedStep decoder.parameters decoder.temperature route workspace)
    (decoder.initialWorkspace state)

/-- Structural adapter to the sealed legal-action scoring contract. -/
noncomputable def toLegalActionWorkspaceDecoder :
    LegalActionWorkspaceDecoder root where
  Params := decoder.Params
  Gates := Temperature
  parameters := decoder.parameters
  gates := decoder.temperature
  recurrenceDepth := decoder.recurrenceDepth
  score := fun parameters temperature depth state action =>
    decoder.score parameters
      ((decoder.routeSchedule parameters temperature depth state).foldl
        (fun workspace route =>
          decoder.routedStep parameters temperature route workspace)
        (decoder.initialWorkspace state)) state action

/-- T5 inheritance crown: every route, temperature, schedule, workspace
content, and recurrence depth preserves accepted-language equivalence,
soundness, and in-budget recall. -/
theorem inheritanceCrown
    (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program ↔
      root.asRefinementInterface.Accepts budget trace program) ∧
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program →
      root.wellFormed program) ∧
    (root.budgetOK budget → root.wellFormed program →
      root.programCost program ≤ budget →
      root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget
        (root.encode program) program) := by
  exact ⟨decoder.toLegalActionWorkspaceDecoder.rankedAccepts_iff_accepts laws,
    decoder.toLegalActionWorkspaceDecoder.rankedAccepts_sound laws,
    decoder.toLegalActionWorkspaceDecoder.wellFormed_rankedAccepts laws⟩

/-- Swapping every routed architecture field can change scores and ordering,
but it cannot change accepted-language semantics or the inherited safety and
recall guarantees. -/
theorem architectureSwap_safe
    (laws : AtomicRootLaws root)
    (other : RoutedLegalActionDecoder root Slot Content Route Temperature)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program ↔
      root.asRefinementInterface.RankedAccepts
        other.toLegalActionWorkspaceDecoder.ranking budget trace program) ∧
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program →
      root.wellFormed program) ∧
    (root.budgetOK budget → root.wellFormed program →
      root.programCost program ≤ budget →
      root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget
        (root.encode program) program) := by
  exact decoder.toLegalActionWorkspaceDecoder.architectureSwap_safe laws
    other.toLegalActionWorkspaceDecoder

end RoutedLegalActionDecoder

#print axioms routedGatedStep_eq_convexMixture
#print axioms routedGatedStep_constantExperts
#print axioms RoutedLegalActionDecoder.inheritanceCrown
#print axioms RoutedLegalActionDecoder.architectureSwap_safe

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
