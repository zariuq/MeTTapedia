import Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Languages.MeTTa.Prime.NativeAgentInteractionExample

/-!
# Prime-native fibred parallel interaction

This example gives a proof-carrying sufficient condition for parallel
execution: the operational theory factors as a product of two independent
interaction fibres.  The corresponding native term is a binary superposition
whose two components lower separately.  Component events then form an exact
commuting square, so either chronological order reaches the same endpoint.
Product factorization is not claimed to be necessary for every safe parallel
execution; it is the sufficient criterion proved by this module.

Disjoint names alone are not used as a proof of independence.  Product
factorization is the license.  The concrete Cost-rho route is supplied by
`NativeInteractionEffectAnalysis`: it checks exact linear occurrences and
returns the separation certificate from which the product square and
one-wave schedule are derived.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeFibredInteractionExample

open Mettapedia.Algebra
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.MeTTaInteraction
open Mettapedia.Languages.MeTTa.MeTTaInteraction.Canary
open Mettapedia.Languages.MeTTa.MeTTaInteractionBind.Canary
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeAgentInteractionExample
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionCost
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation

universe uLeftSite uRightSite uLeftEvent uRightEvent

abbrev siteTheory := siteGSLT model authorityWorld false
abbrev sitePresentation := presentation model authorityWorld false

def pairedInterpretation :
    EndpointInterpretation (GSLT.interleavingProduct siteTheory siteTheory) :=
  productInterpretation (siteInterpretation false) (siteInterpretation false)

def pairedNativeTerm
    (left right : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : StagedReflectiveTm 0 0 :=
  .superpose (.pattern left) (.pattern right)

def pairedEndpoint
    (left right : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    pairedInterpretation.Endpoint (pairedNativeTerm left right) :=
  ⟨(left, right), rfl⟩

abbrev pairedPresentation :
    InteractionPresentation (GSLT.interleavingProduct siteTheory siteTheory) :=
  fibredPresentation sitePresentation sitePresentation

def pairedComputationTy (source target : StagedReflectiveTm 0 0) :
    familiesCwF.Ty PrimeContext :=
  pairedInterpretation.computationTy pairedPresentation source target

/-! ## The commuting agent actions -/

def leftFirst : FibredEvent sitePresentation sitePresentation (.inl cheap)
    (a, a) (b, a) :=
  .left cheapEvent rfl

def rightAfter : FibredEvent sitePresentation sitePresentation (.inr dear)
    (b, a) (b, b) :=
  .right rfl dearEvent

def rightFirst : FibredEvent sitePresentation sitePresentation (.inr dear)
    (a, a) (a, b) :=
  .right rfl dearEvent

def leftAfter : FibredEvent sitePresentation sitePresentation (.inl cheap)
    (a, b) (b, b) :=
  .left cheapEvent rfl

/-- Left-then-right and right-then-left are distinct chronological witnesses
with the same exact product endpoints. -/
def leftThenRightPath : EventPath pairedPresentation (a, a) (b, b) :=
  .cons leftFirst
    (.cons rightAfter (.nil (presentation := pairedPresentation) (b, b)))

def rightThenLeftPath : EventPath pairedPresentation (a, a) (b, b) :=
  .cons rightFirst
    (.cons leftAfter (.nil (presentation := pairedPresentation) (b, b)))

def leftThenRight : familiesCwF.Tm PrimeContext
    (pairedComputationTy (pairedNativeTerm a a) (pairedNativeTerm b b)) :=
  fun _ => ⟨pairedEndpoint a a, pairedEndpoint b b, by
    simpa [pairedEndpoint] using leftThenRightPath⟩

def rightThenLeft : familiesCwF.Tm PrimeContext
    (pairedComputationTy (pairedNativeTerm a a) (pairedNativeTerm b b)) :=
  fun _ => ⟨pairedEndpoint a a, pairedEndpoint b b, by
    simpa [pairedEndpoint] using rightThenLeftPath⟩

/-- The semantic product theorem supplies the commuting square underlying
the two exact paths. -/
theorem independent_site_steps_commute :
    (GSLT.interleavingProduct siteTheory siteTheory).Step
        (a, a) (b, a) ∧
      (GSLT.interleavingProduct siteTheory siteTheory).Step
        (b, a) (b, b) ∧
      (GSLT.interleavingProduct siteTheory siteTheory).Step
        (a, a) (a, b) ∧
      (GSLT.interleavingProduct siteTheory siteTheory).Step
        (a, b) (b, b) :=
  GSLT.interleavingProduct_commutingSquare
    ((sitePresentation).sound cheapEvent)
    ((sitePresentation).sound dearEvent)

/-! ## Provenance order and work/span -/

abbrev laneValuation := chronological fun occurrence :
    Occurrence pairedPresentation =>
  match occurrence.2.site with
  | .inl _ => false
  | .inr _ => true

@[simp] theorem leftThenRight_lane_order :
    EventPath.grade pairedPresentation laneValuation leftThenRightPath =
      some [false, true] :=
  by
    simp [EventPath.grade, EventPath.events, leftThenRightPath,
      leftFirst, rightAfter, laneValuation, chronological,
      Valuation.historyGrade, chronologicalListPartialMonoid]

@[simp] theorem rightThenLeft_lane_order :
    EventPath.grade pairedPresentation laneValuation rightThenLeftPath =
      some [true, false] :=
  by
    simp [EventPath.grade, EventPath.events, rightThenLeftPath,
      rightFirst, leftAfter, laneValuation, chronological,
      Valuation.historyGrade, chronologicalListPartialMonoid]

/-- Chronological observation has work two and span two. -/
theorem chronological_pair_workSpan :
    pathWorkSpan
      (fun _ => leftThenRightPath) PUnit.unit = ⟨2, 2⟩ :=
  by
    simp [pathWorkSpan, leftThenRightPath, EventPath.pathLength]

/-- Product independence licenses one two-event wave: work remains two while
span falls to one. -/
def parallelPairWorkSpan : WorkSpan :=
  WorkSpan.parallel ⟨1, 1⟩ ⟨1, 1⟩

theorem parallel_pair_workSpan : parallelPairWorkSpan = ⟨2, 1⟩ :=
  rfl

/-- Negative control: forgetting wave structure would conflate genuinely
parallel and sequential executions. -/
theorem parallel_pair_ne_chronological :
    parallelPairWorkSpan ≠
      pathWorkSpan (fun _ => leftThenRightPath) PUnit.unit := by
  intro equal
  rw [chronological_pair_workSpan] at equal
  norm_num [parallelPairWorkSpan, WorkSpan.parallel] at equal

#print axioms independent_site_steps_commute
#print axioms leftThenRight_lane_order
#print axioms rightThenLeft_lane_order
#print axioms chronological_pair_workSpan
#print axioms parallel_pair_workSpan
#print axioms parallel_pair_ne_chronological

end Mettapedia.Languages.MeTTa.Prime.NativeFibredInteractionExample
