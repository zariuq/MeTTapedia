import Mettapedia.GSLT.Meredith.InteractiveReducesNBridge
import Mettapedia.GSLT.Synthesis.MainConservation

/-!
# Continued-Cost Bridge for the ρ Example

This file ties the current continued-cut rho layer to the existing
`MainConservation` trace/account machinery.

The bridge is now intrinsic:

- one-step cost is derived from the actual rho COMM redex via
  `rhoIntrinsicStepCost`
- rewrite-path cost is recorded by the shared `rhoIntrinsicCostMap`
- concrete bridge theorems are clients of the shared `RewritePath` and
  `traceAccount` infrastructure
-/

namespace Mettapedia.GSLT.Meredith.RhoExample

open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The concrete rho COMM redex used for the one-step bridge. -/
def commSource (chan payload body : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "POutput" [chan, payload],
     .apply "PInput" [chan, .lambda none body]]
    none

/-- The concrete rho COMM contractum used for the one-step bridge. -/
def commTarget (body payload : Pattern) : Pattern :=
  .collection .hashBag [semanticCommSubst body payload] none

/-- The canonical one-step rho COMM proof for the bridge redex. -/
def rhoCommStep (chan payload body : Pattern) :
    rhoGSLT.Step (commSource chan payload body) (commTarget body payload) :=
  ⟨@Reduces.comm chan payload body []⟩

/-- The bridge keeps amplitudes inert while focusing on the cost/account layer. -/
def continuedBridgeWeightMap : WeightMap rhoGSLT Complex :=
  rhoBridgeWeightMap

/-- The canonical one-step path for the concrete COMM bridge redex. -/
def continuedCommPath (chan payload body : Pattern) :
    rhoGSLT.RewritePath (commSource chan payload body) (commTarget body payload) :=
  oneStepPath (S := rhoGSLT) (rhoCommStep chan payload body)

/-- The shared rewrite-path trace for the one-step COMM bridge. -/
noncomputable def continuedCommTrace
    (chan payload body : Pattern) :
    QuantumTrace rhoGSLT Nat 2 :=
  rewritePathTrace (S := rhoGSLT) (A := Nat) (k := 2)
    continuedBridgeWeightMap
    rhoIntrinsicCostMap
    (continuedCommPath chan payload body)

/-- The one-step COMM trace is exactly the shared rewrite-path trace. -/
theorem continuedCommTrace_eq_rewritePathTrace
    (chan payload body : Pattern) :
    continuedCommTrace chan payload body =
      rewritePathTrace (S := rhoGSLT) (A := Nat) (k := 2)
        continuedBridgeWeightMap
        rhoIntrinsicCostMap
        (continuedCommPath chan payload body) := by
  rfl

/-- The one-step trace account agrees with the corresponding one-step path cost. -/
theorem continuedCommTraceAccount_eq_totalCost_oneStepPath
    (chan payload body : Pattern) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (continuedCommTrace chan payload body) =
        totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) := by
  simpa [continuedCommTrace] using
    (traceAccount_rewritePathTrace (S := rhoGSLT) (A := Nat) (k := 2)
      continuedBridgeWeightMap
      rhoIntrinsicCostMap
      (continuedCommPath chan payload body))

/-- The richer ordered spent ledger on the one-step bridge projects to the
shared vector-cost accumulation. -/
theorem continuedCommLedgerPublicTemporalSemanticBridge
    (chan payload body : Pattern) :
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body)) =
        totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body))) =
          totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) ∧
    (totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body)).temporalList.length =
      (continuedCommPath chan payload body).length := by
  exact ⟨rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost
      (continuedCommPath chan payload body),
    rhoIntrinsicLedgerTotalAction_spentSyntax_eq_totalCost
      (continuedCommPath chan payload body),
    rhoIntrinsicLedgerTotalAction_temporalLength_eq_length
      (continuedCommPath chan payload body)⟩

/-- The richer ordered spent ledger on the one-step bridge projects to the
shared vector-cost accumulation. -/
theorem continuedCommTotalAction_shadow_eq_totalCost_oneStepPath
    (chan payload body : Pattern) :
    rhoLedgerShadow
      (totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body)) =
        totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) := by
  rcases continuedCommLedgerPublicTemporalSemanticBridge chan payload body with
    ⟨hshadow, _, _⟩
  exact hshadow

/-- The one-step bridge also admits a paper-facing spent-syntax witness whose
account agrees with the accumulated path cost. -/
theorem continuedCommTotalAction_spentSyntax_eq_totalCost_oneStepPath
    (chan payload body : Pattern) :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body))) =
          totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) := by
  rcases continuedCommLedgerPublicTemporalSemanticBridge chan payload body with
    ⟨_, hacc, _⟩
  exact hacc

/-- The richer ordered spent ledger on the one-step bridge records exactly one
temporal entry, matching path length. -/
theorem continuedCommTotalAction_temporalLength_eq_length
    (chan payload body : Pattern) :
    (totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body)).temporalList.length =
      (continuedCommPath chan payload body).length := by
  rcases continuedCommLedgerPublicTemporalSemanticBridge chan payload body with
    ⟨_, _, hlen⟩
  exact hlen

/-- Direct spent-stack witness for the one-step COMM bridge. -/
noncomputable def continuedCommDirectSpent
    (chan payload body : Pattern) : RhoDirectStack :=
  rhoIntrinsicDirectSpentStack (continuedCommPath chan payload body)

theorem continuedCommDirectSpentSemanticBridge
    (chan payload body : Pattern) :
    (continuedCommDirectSpent chan payload body).toLedger =
      totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body) ∧
    rhoLedgerShadow ((continuedCommDirectSpent chan payload body).toLedger) =
      totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) ∧
    (continuedCommDirectSpent chan payload body).depth =
      (continuedCommPath chan payload body).length ∧
    rhoSpentSyntaxAccount (continuedCommDirectSpent chan payload body).toPattern =
      totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) ∧
    rhoSpentSyntaxTicks (continuedCommDirectSpent chan payload body).toPattern =
      (continuedCommPath chan payload body).length := by
  exact ⟨by
      simpa [continuedCommDirectSpent] using
        rhoIntrinsicDirectSpentStack_toLedger (continuedCommPath chan payload body),
    by
      simpa [continuedCommDirectSpent] using
        rhoIntrinsicDirectSpentStack_shadow_eq_totalCost (continuedCommPath chan payload body),
    by
      simpa [continuedCommDirectSpent] using
        rhoIntrinsicDirectSpentStack_depth_eq_length (continuedCommPath chan payload body),
    by
      simpa [continuedCommDirectSpent] using
        rhoIntrinsicDirectSpentStack_spentSyntax_eq_totalCost
          (continuedCommPath chan payload body),
    by
      simpa [continuedCommDirectSpent] using
        rhoIntrinsicDirectSpentStack_ticks_eq_length
          (continuedCommPath chan payload body)⟩

theorem continuedCommDirectSpent_toLedger
    (chan payload body : Pattern) :
    (continuedCommDirectSpent chan payload body).toLedger =
      totalAction rhoIntrinsicLedgerAction (continuedCommPath chan payload body) := by
  rcases continuedCommDirectSpentSemanticBridge chan payload body with
    ⟨hledger, _, _, _, _⟩
  exact hledger

theorem continuedCommDirectSpent_shadow_eq_totalCost
    (chan payload body : Pattern) :
    rhoLedgerShadow ((continuedCommDirectSpent chan payload body).toLedger) =
      totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) := by
  rcases continuedCommDirectSpentSemanticBridge chan payload body with
    ⟨_, hshadow, _, _, _⟩
  exact hshadow

theorem continuedCommDirectSpent_depth_eq_length
    (chan payload body : Pattern) :
    (continuedCommDirectSpent chan payload body).depth =
      (continuedCommPath chan payload body).length := by
  rcases continuedCommDirectSpentSemanticBridge chan payload body with
    ⟨_, _, hdepth, _, _⟩
  exact hdepth

theorem continuedCommDirectSpent_spentSyntax_eq_totalCost
    (chan payload body : Pattern) :
    rhoSpentSyntaxAccount (continuedCommDirectSpent chan payload body).toPattern =
      totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) := by
  rcases continuedCommDirectSpentSemanticBridge chan payload body with
    ⟨_, _, _, hacc, _⟩
  exact hacc

theorem continuedCommDirectSpent_ticks_eq_length
    (chan payload body : Pattern) :
    rhoSpentSyntaxTicks (continuedCommDirectSpent chan payload body).toPattern =
      (continuedCommPath chan payload body).length := by
  rcases continuedCommDirectSpentSemanticBridge chan payload body with
    ⟨_, _, _, _, hticks⟩
  exact hticks

/-- The singleton trace contributes one temporal tick. -/
theorem continuedCommTraceAccount_ticks
    (chan payload body : Pattern) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (continuedCommTrace chan payload body) 1 = 1 := by
  rw [continuedCommTraceAccount_eq_totalCost_oneStepPath]
  calc
    totalCost rhoIntrinsicCostMap (continuedCommPath chan payload body) 1 =
        (continuedCommPath chan payload body).length := by
          exact totalCost_coord_eq_length_of_step_unit_cost
            (S := rhoGSLT) (cm := rhoIntrinsicCostMap) (i := 1)
            (by
              intro a b h
              exact rhoIntrinsicStepCost_apply_one h)
            (continuedCommPath chan payload body)
    _ = 1 := by
        simp [continuedCommPath]

/-- The temporal coordinate of the one-step bridge is exactly the path length. -/
theorem continuedCommTotalCost_ticks_eq_length
    (chan payload body : Pattern) :
    totalCost rhoIntrinsicCostMap
      (continuedCommPath chan payload body) 1 =
        (continuedCommPath chan payload body).length := by
  exact totalCost_coord_eq_length_of_step_unit_cost
    (S := rhoGSLT) (cm := rhoIntrinsicCostMap) (i := 1)
    (by
      intro a b h
      exact rhoIntrinsicStepCost_apply_one h)
    (continuedCommPath chan payload body)

/-- The singleton trace carries one temporal tick, matching the one-step path
length. -/
theorem continuedCommTraceAccount_ticks_eq_length
    (chan payload body : Pattern) :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      (continuedCommTrace chan payload body) 1 =
        (continuedCommPath chan payload body).length := by
  rw [continuedCommTraceAccount_eq_totalCost_oneStepPath]
  exact continuedCommTotalCost_ticks_eq_length chan payload body

/-- Empty process used in the concrete two-step bridge. -/
def twoStepNil : Pattern :=
  .collection .hashBag [] none

/-- The first channel in the concrete two-step bridge. -/
def twoStepOuterChan : Pattern := .fvar "outer"

/-- The second channel in the concrete two-step bridge. -/
def twoStepInnerChan : Pattern := .fvar "inner"

/-- The forwarded payload exposed by the first COMM. -/
def twoStepForwarder : Pattern :=
  .apply "POutput" [twoStepInnerChan, twoStepNil]

/-- The outer continuation reveals the forwarded payload as a process. -/
def twoStepOuterBody : Pattern :=
  .apply "PDrop" [.bvar 0]

/-- The inner continuation is inert after the second COMM. -/
def twoStepInnerBody : Pattern :=
  twoStepNil

/-- The inner receive that waits for the revealed forwarded payload. -/
def twoStepInnerRecv : Pattern :=
  .apply "PInput" [twoStepInnerChan, .lambda none twoStepInnerBody]

/-- Concrete source state whose first COMM reveals a second COMM. -/
def continuedTwoStepSource : Pattern :=
  .collection .hashBag
    [.apply "POutput" [twoStepOuterChan, twoStepForwarder],
     .apply "PInput" [twoStepOuterChan, .lambda none twoStepOuterBody],
     twoStepInnerRecv]
    none

/-- Intermediate state after the first COMM in the two-step bridge. -/
def continuedTwoStepMid : Pattern :=
  .collection .hashBag [twoStepForwarder, twoStepInnerRecv] none

/-- Final state after the second COMM in the two-step bridge. -/
def continuedTwoStepFinal : Pattern :=
  .collection .hashBag [twoStepNil] none

private theorem continuedTwoStep_outer_contract :
    semanticCommSubst twoStepOuterBody twoStepForwarder = twoStepForwarder := by
  simpa [twoStepOuterBody, twoStepForwarder, twoStepInnerChan, twoStepNil] using!
    semanticCommSubst_collapses_bound_drop twoStepForwarder

private theorem continuedTwoStep_inner_contract :
    semanticCommSubst twoStepInnerBody twoStepNil = twoStepNil := by
  simp [twoStepInnerBody, twoStepNil, semanticCommSubst, semanticSubstProc,
    semanticSubstProcList, semanticNormalizeProc, semanticNormalizeProcList]

/-- The first concrete rho COMM step in the two-step bridge. -/
def continuedTwoStepFirstStep :
    rhoGSLT.Step continuedTwoStepSource continuedTwoStepMid :=
  ⟨by
    simpa [continuedTwoStepSource, continuedTwoStepMid, twoStepInnerRecv,
      twoStepOuterBody, continuedTwoStep_outer_contract] using!
      (@Reduces.comm twoStepOuterChan twoStepForwarder twoStepOuterBody [twoStepInnerRecv])⟩

/-- The second concrete rho COMM step in the two-step bridge. -/
def continuedTwoStepSecondStep :
    rhoGSLT.Step continuedTwoStepMid continuedTwoStepFinal :=
  ⟨by
    simpa [continuedTwoStepMid, continuedTwoStepFinal, twoStepForwarder,
      twoStepInnerRecv, twoStepInnerBody, twoStepNil, continuedTwoStep_inner_contract] using!
      (@Reduces.comm twoStepInnerChan twoStepNil twoStepInnerBody ([] : List Pattern))⟩

/-- The concatenated two-step rho rewrite path used for the accumulated bridge. -/
def continuedTwoStepPath :
    rhoGSLT.RewritePath continuedTwoStepSource continuedTwoStepFinal :=
  rewritePathAppend
    (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)
    (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)

/-- The richer ordered spent ledger along the concrete two-step path is exactly
the sum of the two intrinsic per-step spent ledgers. -/
theorem continuedTwoStepTotalAction_eq_stepSpentSum :
    totalAction rhoIntrinsicLedgerAction continuedTwoStepPath =
      rhoIntrinsicStepLedger continuedTwoStepFirstStep +
        rhoIntrinsicStepLedger continuedTwoStepSecondStep := by
  simpa [continuedTwoStepPath, rhoIntrinsicLedgerAction, totalAction, oneStepPath] using
    (totalAction_append (S := rhoGSLT) (am := rhoIntrinsicLedgerAction)
      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)
      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))

/-- The concrete two-step quantum trace carrying intrinsic per-step accounts. -/
noncomputable def continuedTwoStepTrace : QuantumTrace rhoGSLT Nat 2 :=
  rhoIntrinsicRewritePathTrace continuedTwoStepPath

/-- The two-step trace contributes one temporal tick per cut. -/
theorem continuedTwoStepTraceAccount_ticks :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace 1 = 2 := by
  calc
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace 1 =
        continuedTwoStepPath.length := by
          simpa [continuedTwoStepTrace] using
            rhoIntrinsicRewritePathTrace_ticks_eq_length continuedTwoStepPath
    _ = 2 := by
      simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]

/-- The concrete two-step trace is the shared rewrite-path trace for the chosen
bridge weight and intrinsic rho cost map. -/
theorem continuedTwoStepTrace_eq_rewritePathTrace :
    continuedTwoStepTrace =
      rewritePathTrace (S := rhoGSLT) (A := Nat) (k := 2)
        continuedBridgeWeightMap
        rhoIntrinsicCostMap
        continuedTwoStepPath := by
  simp [continuedTwoStepTrace, rhoIntrinsicRewritePathTrace, continuedBridgeWeightMap,
    rhoBridgeWeightMap]

/-- Concrete accumulated ledger/public/temporal scalar semantic package for the
continued two-step bridge. This gathers the nearby path-level cost, public
spent-syntax, and temporal facts so the scalar corollaries project from one
local owner theorem instead of repeating direct generic source calls. -/
theorem continuedTwoStepLedgerPublicTemporalSemanticBridge :
    totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 =
      continuedTwoStepPath.length ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        continuedTwoStepPath.length ∧
    (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).temporalList.length =
      continuedTwoStepPath.length ∧
    RhoLedger.TraceCoherent
      (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) := by
  rcases rhoIntrinsicLedgerPublicSpentSyntax_semantics continuedTwoStepPath with
    ⟨hacc, hwidth, hticks, hlen, hcoh⟩
  exact ⟨rhoIntrinsicTotalCost_ticks_eq_length continuedTwoStepPath,
    rhoIntrinsicLedgerTotalAction_shadow_eq_totalCost continuedTwoStepPath,
    hacc,
    rhoIntrinsicLedgerTotalAction_publicSpentSyntax_width_eq_spatialCard
      continuedTwoStepPath,
    hwidth,
    hticks,
    hlen,
    rhoIntrinsicLedgerTotalAction_temporalLength_eq_length continuedTwoStepPath,
    hcoh⟩

/-- The temporal coordinate of the accumulated path cost is exactly the length
of the concrete two-step rewrite path. This is the first explicit modulus-style
statement for the intrinsic continued rho bridge. -/
theorem continuedTwoStepTotalCost_ticks_eq_length :
    totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 =
      continuedTwoStepPath.length := by
  rcases continuedTwoStepLedgerPublicTemporalSemanticBridge with
    ⟨hticks, _, _, _, _, _, _, _, _⟩
  exact hticks

/-- The accumulated trace records one temporal tick per COMM in the concrete
two-step bridge, exactly matching path length. -/
theorem continuedTwoStepTraceAccount_ticks_eq_length :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace 1 =
        continuedTwoStepPath.length := by
  simpa [continuedTwoStepTrace] using
    rhoIntrinsicRewritePathTrace_ticks_eq_length continuedTwoStepPath

/-- Concrete trace-account/shadow bridge facts for the continued two-step path.
This isolates the scalar relation between the shared rewrite-path trace and the
accumulated ledger shadow, so later owner theorems do not need to reach back
into the generic source layer for these two equations. -/
theorem continuedTwoStepTraceShadowSemanticBridge :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
        traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace := by
  constructor
  · simpa [continuedTwoStepTrace] using
      rhoIntrinsicRewritePathTraceAccount_eq_totalCost continuedTwoStepPath
  · simpa [continuedTwoStepTrace] using
      rhoIntrinsicLedgerTotalAction_shadow_eq_traceAccount continuedTwoStepPath

/-- The richer ordered spent ledger along the concrete two-step path projects
to the same accumulated vector cost as the shared path-cost map. -/
theorem continuedTwoStepTotalAction_shadow_eq_totalCost :
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath := by
  rcases continuedTwoStepLedgerPublicTemporalSemanticBridge with
    ⟨_, hshadow, _, _, _, _, _, _, _⟩
  exact hshadow

/-- Concrete public spent-syntax semantic package for the accumulated ledger
along the continued two-step path. This gives the nearby scalar public facts one
local owner theorem instead of repeated direct calls into the generic source
layer. -/
theorem continuedTwoStepPublicSpentSyntaxFullSemanticBridge :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          continuedTwoStepPath.length ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) := by
  rcases continuedTwoStepLedgerPublicTemporalSemanticBridge with
    ⟨_, _, hacc, _, hwidth, hticks, hlen, _, hcoh⟩
  exact ⟨hacc, hwidth, hticks, hlen, hcoh⟩

/-- The paper-facing spent-syntax encoding of the accumulated two-step ledger
agrees with the same shared accumulated path cost. -/
theorem continuedTwoStepTotalAction_spentSyntax_eq_totalCost :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath := by
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge with
    ⟨hacc, _, _, _, _⟩
  exact hacc

theorem continuedTwoStepTotalAction_publicSpentSyntax_width_eq_spatialCard :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card := by
  rcases continuedTwoStepLedgerPublicTemporalSemanticBridge with
    ⟨_, _, _, hwidth, _, _, _, _, _⟩
  exact hwidth

theorem continuedTwoStepTotalAction_publicSpentSyntax_ticks_eq_length :
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        continuedTwoStepPath.length := by
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge with
    ⟨_, _, _, hlen, _⟩
  exact hlen

theorem continuedTwoStepTotalAction_publicSpentSyntax_width_eq_totalCost_zero :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 := by
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge with
    ⟨_, hwidth, _, _, _⟩
  exact hwidth

theorem continuedTwoStepTotalAction_publicSpentSyntax_ticks_eq_totalCost_one :
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 := by
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge with
    ⟨_, _, hticks, _, _⟩
  exact hticks

theorem continuedTwoStepTotalAction_publicSpentSyntax_modulus :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          continuedTwoStepPath.length := by
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge with
    ⟨_, hwidth, hticks, hlen, _⟩
  exact ⟨hwidth, hticks, hlen⟩

/-- The richer ordered spent ledger along the concrete two-step path records
one temporal entry per step, exactly matching path length. -/
theorem continuedTwoStepTotalAction_temporalLength_eq_length :
    (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).temporalList.length =
      continuedTwoStepPath.length := by
  rcases continuedTwoStepLedgerPublicTemporalSemanticBridge with
    ⟨_, _, _, _, _, _, _, htemporal, _⟩
  exact htemporal

theorem continuedTwoStepTemporalSemanticBridge :
    (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).temporalList.length =
        continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        continuedTwoStepPath.length ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 = continuedTwoStepPath.length ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 = 2 := by
  rcases rhoIntrinsicTemporalSemanticBridge_rewritePathAppend_steps
      continuedTwoStepFirstStep
      continuedTwoStepSecondStep with
    ⟨htemporal, hpublicTicksLen, hdirectTicksLen, hpublicTicksTwo, hdirectTicksTwo,
      htraceTicksTwo, htraceTicksLen⟩
  constructor
  · simpa [continuedTwoStepPath] using htemporal
  · constructor
    · simpa [continuedTwoStepPath] using hpublicTicksLen
    · constructor
      · simpa [continuedTwoStepPath] using hdirectTicksLen
      · constructor
        · simpa [continuedTwoStepTrace, continuedTwoStepPath] using htraceTicksLen
        · simpa [continuedTwoStepTrace, continuedTwoStepPath] using htraceTicksTwo

/-- Direct spent-stack witness for the concrete two-step bridge. -/
noncomputable def continuedTwoStepDirectSpent : RhoDirectStack :=
  rhoIntrinsicDirectSpentStack continuedTwoStepPath

theorem continuedTwoStepStepAppendSemanticBridge :
    continuedTwoStepDirectSpent.toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      rhoLedgerShadow continuedTwoStepDirectSpent.toLedger =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      continuedTwoStepDirectSpent.depth = continuedTwoStepPath.length ∧
      rhoSpentSyntaxAccount continuedTwoStepDirectSpent.toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxTicks continuedTwoStepDirectSpent.toPattern =
        continuedTwoStepPath.length ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoIntrinsicDirectSpentTrace continuedTwoStepPath =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) := by
  rcases
      (rhoIntrinsicDirectSpentStack_semantics_rewritePathAppend_steps
        continuedTwoStepFirstStep
        continuedTwoStepSecondStep) with
    ⟨hledger, hshadow, hdepth, haccount, hticksLen, happend, hsteps, htrace⟩
  rcases
      (rhoIntrinsicLedgerTotalAction_publicSpentSyntax_no_leak_rewritePathAppend
        (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)
        (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) with
    ⟨hpublicAcc, hpublicWidth, hpublicTicks⟩
  rcases
      (rhoIntrinsicDirectSpentTrace_no_leak_rewritePathAppend
        (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)
        (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) with
    ⟨hdirectAcc, hdirectWidth, hdirectTicks, hcoherent⟩
  exact
    ⟨by simpa [continuedTwoStepDirectSpent, continuedTwoStepPath] using hledger,
      by simpa [continuedTwoStepDirectSpent, continuedTwoStepPath] using hshadow,
      by simpa [continuedTwoStepDirectSpent, continuedTwoStepPath] using hdepth,
      by simpa [continuedTwoStepDirectSpent, continuedTwoStepPath] using haccount,
      by simpa [continuedTwoStepDirectSpent, continuedTwoStepPath] using hticksLen,
      by simpa [continuedTwoStepDirectSpent, continuedTwoStepPath] using happend,
      by simpa [continuedTwoStepDirectSpent, continuedTwoStepPath] using hsteps,
      by simpa [continuedTwoStepPath] using htrace,
      by simpa [continuedTwoStepPath] using hpublicAcc,
      by simpa [continuedTwoStepPath] using hpublicWidth,
      by simpa [continuedTwoStepPath] using hpublicTicks,
      by simpa [continuedTwoStepPath] using hdirectAcc,
      by simpa [continuedTwoStepPath] using hdirectWidth,
      by simpa [continuedTwoStepPath] using hdirectTicks,
      by
        exact hcoherent⟩

theorem continuedTwoStepStepAppendFullSemanticBridge :
    (continuedTwoStepDirectSpent.toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      rhoLedgerShadow continuedTwoStepDirectSpent.toLedger =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      continuedTwoStepDirectSpent.depth = continuedTwoStepPath.length ∧
      rhoSpentSyntaxAccount continuedTwoStepDirectSpent.toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxTicks continuedTwoStepDirectSpent.toPattern =
        continuedTwoStepPath.length ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoIntrinsicDirectSpentTrace continuedTwoStepPath =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger)) ∧
    ((totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).temporalList.length =
        continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) = 2 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 = continuedTwoStepPath.length) := by
  rcases continuedTwoStepStepAppendSemanticBridge with
    ⟨hledger, hshadow, hdepth, haccount, hstackTicksLen, happend, hsteps, htrace,
      hpublicAcc, hpublicWidth, hpublicTicksAppend, hdirectAcc, hdirectWidth,
      hdirectTicksAppend, hdirectCoherent⟩
  rcases continuedTwoStepTemporalSemanticBridge with
    ⟨htemporalLen, hpublicTicksLen, hdirectTicksLen, htraceTicksLen, htraceTicksTwo⟩
  have hpublicTicksTwo :
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) = 2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            continuedTwoStepPath.length := hpublicTicksLen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  have hdirectTicksTwo :
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern = 2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
            continuedTwoStepPath.length := hdirectTicksLen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  exact
    ⟨⟨hledger, hshadow, hdepth, haccount, hstackTicksLen, happend, hsteps, htrace,
        hpublicAcc, hpublicWidth, hpublicTicksAppend, hdirectAcc, hdirectWidth,
        hdirectTicksAppend, hdirectCoherent⟩,
      ⟨htemporalLen, hpublicTicksLen, hdirectTicksLen, hpublicTicksTwo, hdirectTicksTwo,
        htraceTicksTwo, htraceTicksLen⟩⟩

/-- Concrete public spent-syntax append package for the continued two-step bridge.
This is the append/no-leak slice of the full step-append bridge. -/
theorem continuedTwoStepStepAppendPublicSemanticBridge :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) := by
  rcases continuedTwoStepStepAppendSemanticBridge with
    ⟨_, _, _, _, _, _, _, _, hacc, hwidth, hticks, _, _, _, _⟩
  exact ⟨hacc, hwidth, hticks⟩

/-- Concrete direct spent-trace append package for the continued two-step bridge.
This is the append/no-leak slice of the full step-append bridge. -/
theorem continuedTwoStepStepAppendDirectTraceSemanticBridge :
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) := by
  rcases continuedTwoStepStepAppendSemanticBridge with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hacc, hwidth, hticks, hcoh⟩
  exact ⟨hacc, hwidth, hticks, hcoh⟩

theorem continuedTwoStepDirectSpent_stepAppendSemantics :
    continuedTwoStepDirectSpent.toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      rhoLedgerShadow (continuedTwoStepDirectSpent.toLedger) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      continuedTwoStepDirectSpent.depth = continuedTwoStepPath.length ∧
      rhoSpentSyntaxAccount continuedTwoStepDirectSpent.toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxTicks continuedTwoStepDirectSpent.toPattern =
        continuedTwoStepPath.length ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoIntrinsicDirectSpentTrace continuedTwoStepPath =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) := by
  rcases continuedTwoStepStepAppendSemanticBridge with
    ⟨hledger, hshadow, hdepth, haccount, hticks, happend, hsteps, htrace, _, _, _, _, _, _, _⟩
  exact ⟨hledger, hshadow, hdepth, haccount, hticks, happend, hsteps, htrace⟩

theorem continuedTwoStepDirectSpent_toLedger :
    continuedTwoStepDirectSpent.toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨hledger, _, _, _, _, _, _, _⟩
  simpa [continuedTwoStepDirectSpent] using hledger

theorem continuedTwoStepDirectSpent_shadow_eq_totalCost :
    rhoLedgerShadow (continuedTwoStepDirectSpent.toLedger) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨_, hshadow, _, _, _, _, _, _⟩
  exact hshadow

theorem continuedTwoStepDirectSpent_depth_eq_length :
    continuedTwoStepDirectSpent.depth = continuedTwoStepPath.length := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨_, _, hdepth, _, _, _, _, _⟩
  exact hdepth

theorem continuedTwoStepDirectSpent_spentSyntax_eq_totalCost :
    rhoSpentSyntaxAccount continuedTwoStepDirectSpent.toPattern =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨_, _, _, haccount, _, _, _, _⟩
  exact haccount

theorem continuedTwoStepDirectSpent_ticks_eq_length :
    rhoSpentSyntaxTicks continuedTwoStepDirectSpent.toPattern =
      continuedTwoStepPath.length := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨_, _, _, _, hticks, _, _, _⟩
  exact hticks

theorem continuedTwoStepDirectSpent_eq_append_steps :
    continuedTwoStepDirectSpent =
      RhoDirectStack.append
        (rhoIntrinsicDirectSpentStack
          (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))
        (rhoIntrinsicDirectSpentStack
          (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨_, _, _, _, _, happ, _, _⟩
  exact happ

theorem continuedTwoStepDirectSpent_eq_traceSteps :
    continuedTwoStepDirectSpent =
      RhoDirectStack.append
        (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
        (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨_, _, _, _, _, _, htrace, _⟩
  exact htrace

theorem continuedTwoStepDirectSpentTrace_eq_traceSteps :
    rhoIntrinsicDirectSpentTrace continuedTwoStepPath =
      RhoDirectStack.append
        (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
        (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨_, _, _, _, _, _, _, htrace⟩
  exact htrace

/-- Concrete direct spent-trace semantic package for the continued two-step bridge.
This gathers the full path-level spent-trace semantic facts at the concrete path
so nearby projection lemmas do not depend directly on the generic source theorem. -/
theorem continuedTwoStepDirectSpentTraceFullSemanticBridge :
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
        totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          continuedTwoStepPath.length := by
  exact ⟨rhoIntrinsicDirectSpentTrace_surfaceLike continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_toLedger continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_toPublicPattern_eq_publicSpentSyntax continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_traceCoherent continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_account_eq_publicSpentSyntax continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_spentSyntax_eq_totalCost continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_width_eq_publicSpentSyntax_width continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_width_eq_totalCost_zero continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_ticks_eq_publicSpentSyntax_ticks continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_ticks_eq_totalCost_one continuedTwoStepPath,
    rhoIntrinsicDirectSpentTrace_ticks_eq_length continuedTwoStepPath⟩

theorem continuedTwoStepDirectSpentTrace_account_eq_publicSpentSyntax :
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) := by
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨_, _, _, _, hacc, _, _, _, _, _, _⟩
  exact hacc

theorem continuedTwoStepDirectSpentTrace_width_eq_totalCost_zero :
    rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 := by
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨_, _, _, _, _, _, _, hwidth, _, _, _⟩
  exact hwidth

theorem continuedTwoStepDirectSpentTrace_ticks_eq_totalCost_one :
    rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 := by
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨_, _, _, _, _, _, _, _, _, hticks, _⟩
  exact hticks

theorem continuedTwoStepDirectSpentTrace_modulus :
    rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        continuedTwoStepPath.length := by
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨_, _, _, _, _, _, _, hwidth, _, hticks, hlen⟩
  exact ⟨hwidth, hticks, hlen⟩

theorem continuedTwoStepPublicSpentSyntax_no_leak_append :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) := by
  exact continuedTwoStepStepAppendPublicSemanticBridge

theorem continuedTwoStepDirectSpentTrace_no_leak_append :
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) := by
  exact continuedTwoStepStepAppendDirectTraceSemanticBridge

theorem continuedTwoStepPublicSpentSyntax_semantics :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            continuedTwoStepPath.length ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) := by
  exact continuedTwoStepPublicSpentSyntaxFullSemanticBridge

theorem continuedTwoStepDirectSpentTrace_semantics :
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
        totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          continuedTwoStepPath.length := by
  exact continuedTwoStepDirectSpentTraceFullSemanticBridge

theorem continuedTwoStepDirectSpentTrace_toPublicPattern_eq_publicSpentSyntax :
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) := by
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨_, _, hpublic, _, _, _, _, _, _, _, _⟩
  exact hpublic

noncomputable def continuedTwoStepReducesN :
    continuedTwoStepSource ⇝[2] continuedTwoStepFinal :=
  .succ
    (Classical.choice continuedTwoStepFirstStep)
    (.succ
      (Classical.choice continuedTwoStepSecondStep)
      (.zero continuedTwoStepFinal))

theorem continuedTwoStepReducesN_path_eq :
    rhoRewritePathOfReducesN continuedTwoStepReducesN = continuedTwoStepPath := by
  rfl

noncomputable def continuedTwoStepFirstReducesN :
    continuedTwoStepSource ⇝[1] continuedTwoStepMid :=
  .succ
    (Classical.choice continuedTwoStepFirstStep)
    (.zero continuedTwoStepMid)

theorem continuedTwoStepFirstReducesN_path_eq :
    rhoRewritePathOfReducesN continuedTwoStepFirstReducesN =
      oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep := by
  dsimp [continuedTwoStepFirstReducesN]
  exact rhoRewritePathOfReducesN_oneStep
    (step := Classical.choice continuedTwoStepFirstStep)

noncomputable def continuedTwoStepSecondReducesN :
    continuedTwoStepMid ⇝[1] continuedTwoStepFinal :=
  .succ
    (Classical.choice continuedTwoStepSecondStep)
    (.zero continuedTwoStepFinal)

theorem continuedTwoStepSecondReducesN_path_eq :
    rhoRewritePathOfReducesN continuedTwoStepSecondReducesN =
      oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep := by
  dsimp [continuedTwoStepSecondReducesN]
  exact rhoRewritePathOfReducesN_oneStep
    (step := Classical.choice continuedTwoStepSecondStep)

theorem continuedTwoStepReducesN_concat_eq :
    reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN =
      continuedTwoStepReducesN := by
  simp [continuedTwoStepFirstReducesN, continuedTwoStepSecondReducesN,
    continuedTwoStepReducesN, reducesN_concat]

theorem continuedTwoStepReducesN_concat_path_eq :
    rhoRewritePathOfReducesN
      (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN) =
        continuedTwoStepPath := by
  simpa [continuedTwoStepPath] using!
    (rhoRewritePathOfReducesN_concat
      continuedTwoStepFirstReducesN
      continuedTwoStepSecondReducesN)

theorem continuedTwoStepNativeSemanticBundle :
    (traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        continuedTwoStepPath.length ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        continuedTwoStepPath.length) ∧
    (traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        2 ∧
    RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        2) := by
  rcases continuedTwoStepTraceShadowSemanticBridge with
    ⟨hTrace, hShadowTrace⟩
  rcases continuedTwoStepLedgerPublicTemporalSemanticBridge with
    ⟨_, hShadowCost, hPublicAccCost, hPublicWidthSpatial, hPublicWidthCost,
      hPublicTicksCost, hPublicTicksLen, _, _⟩
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge with
    ⟨_, _, _, _, hPublicCoherent⟩
  rcases continuedTwoStepStepAppendPublicSemanticBridge with
    ⟨hPublicAccAppend, hPublicWidthAppend, hPublicTicksAppend⟩
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨hDirectSurface, hDirectLedger, hDirectPublic, hDirectCoherent,
      hDirectAccPublic, hDirectAccCost, hDirectWidthPublic, hDirectWidthCost,
      hDirectTicksPublic, hDirectTicksCost, hDirectTicksLen⟩
  rcases continuedTwoStepStepAppendDirectTraceSemanticBridge with
    ⟨hDirectAccAppend, hDirectWidthAppend, hDirectTicksAppend, _⟩
  have hPublicTicksTwo :
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
              continuedTwoStepPath.length := hPublicTicksLen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  have hDirectTicksTwo :
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
            continuedTwoStepPath.length := hDirectTicksLen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  exact
    ⟨⟨hTrace, hShadowCost, hPublicAccCost, hPublicWidthSpatial, hPublicTicksLen,
        hPublicWidthCost, hPublicTicksCost, hShadowTrace, hDirectSurface,
        hDirectLedger, hDirectPublic, hDirectCoherent, hDirectAccPublic,
        hDirectAccCost, hDirectWidthPublic, hDirectWidthCost, hDirectTicksPublic,
        hDirectTicksCost, hDirectTicksLen⟩,
      ⟨hTrace, hShadowCost, hShadowTrace, hPublicAccAppend, hPublicWidthAppend,
        hPublicTicksAppend, hPublicTicksTwo, hPublicCoherent, hDirectSurface,
        hDirectLedger, hDirectPublic, hDirectCoherent, hDirectAccAppend,
        hDirectWidthAppend, hDirectTicksAppend, hDirectTicksTwo⟩⟩

theorem continuedTwoStepNativeConcatSemanticBridge :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        2 ∧
    RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        2 := by
  exact continuedTwoStepNativeSemanticBundle.2

/-- Concrete exact-step public spent-syntax concat package for the continued
two-step bridge. This gives the `reducesN_concat` public wrappers a local owner
theorem built from the earlier path-level public owners. -/
theorem continuedTwoStepPublicSpentSyntaxConcatSemanticBridge :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            2 ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) := by
  rcases continuedTwoStepStepAppendPublicSemanticBridge with
    ⟨hacc, hwidth, hticks⟩
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge with
    ⟨_, _, _, hlen, hcoh⟩
  have htwo :
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
              continuedTwoStepPath.length := hlen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  exact ⟨hacc, hwidth, hticks, htwo, hcoh⟩

/-- Concrete exact-step direct spent-trace concat package for the continued
two-step bridge. This gives the `reducesN_concat` direct wrappers a local owner
theorem built from the earlier path-level direct owners. -/
theorem continuedTwoStepDirectSpentTraceConcatSemanticBridge :
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
        totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          2 := by
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨hsurf, hledger, hpublic, hcoh, _, _, _, _, _, _, hlen⟩
  rcases continuedTwoStepStepAppendDirectTraceSemanticBridge with
    ⟨hacc, hwidth, hticks, _⟩
  have htwo :
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
            continuedTwoStepPath.length := hlen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  exact ⟨hsurf, hledger, hpublic, hcoh, hacc, hwidth, hticks, htwo⟩

theorem continuedTwoStepPublicSpentSyntax_no_leak_reducesN_concat :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
              rhoSpentSyntaxAccount
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
              rhoSpentSyntaxAccount
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN
              (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
                rhoSpentSyntaxWidth
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
                rhoSpentSyntaxWidth
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN
              (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
                rhoSpentSyntaxTicks
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
                rhoSpentSyntaxTicks
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) := by
  simpa [continuedTwoStepReducesN_concat_path_eq] using
    (show
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)))
      from
        let ⟨hacc, hwidth, hticks, _, _⟩ :=
          continuedTwoStepPublicSpentSyntaxConcatSemanticBridge
        ⟨hacc, hwidth, hticks⟩)

theorem continuedTwoStepDirectSpentTrace_no_leak_reducesN_concat :
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN
          (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
            rhoSpentSyntaxAccount
              (rhoIntrinsicDirectSpentTrace
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
            rhoSpentSyntaxAccount
              (rhoIntrinsicDirectSpentTrace
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxWidth
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxWidth
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxTicks
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxTicks
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toLedger) := by
  simpa [continuedTwoStepReducesN_concat_path_eq] using
    (show
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger)
      from
        let ⟨_, _, _, hcoh, hacc, hwidth, hticks, _⟩ :=
          continuedTwoStepDirectSpentTraceConcatSemanticBridge
        ⟨hacc, hwidth, hticks, hcoh⟩)

theorem continuedTwoStepPublicSpentSyntax_semantics_reducesN_concat :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            2 ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) := by
  exact continuedTwoStepPublicSpentSyntaxConcatSemanticBridge

theorem continuedTwoStepDirectSpentTrace_semantics_reducesN_concat :
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
        totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          2 := by
  exact continuedTwoStepDirectSpentTraceConcatSemanticBridge

/-- Concrete exact-step concat semantic package for the continued two-step
bridge. This gathers the `reducesN_concat` public and direct no-leak facts so
the top semantic bridge can consume one exact-step owner theorem instead of
reconstructing that slice from path-level append facts. -/
theorem continuedTwoStepReducesNConcatSemanticBridge :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
              rhoSpentSyntaxAccount
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
              rhoSpentSyntaxAccount
                (rhoLedgerToSpentSyntax
                  (totalAction rhoIntrinsicLedgerAction
                    (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN
              (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
                rhoSpentSyntaxWidth
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
                rhoSpentSyntaxWidth
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN
              (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
                rhoSpentSyntaxTicks
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
                rhoSpentSyntaxTicks
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxAccount
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxAccount
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxWidth
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxWidth
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxTicks
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxTicks
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toLedger) := by
  rcases continuedTwoStepPublicSpentSyntax_no_leak_reducesN_concat with
    ⟨hpublicAcc, hpublicWidth, hpublicTicks⟩
  rcases continuedTwoStepDirectSpentTrace_no_leak_reducesN_concat with
    ⟨hdirectAcc, hdirectWidth, hdirectTicks, hcoherent⟩
  exact ⟨hpublicAcc, hpublicWidth, hpublicTicks,
    hdirectAcc, hdirectWidth, hdirectTicks, hcoherent⟩

/-- Concrete exact-step public spent-syntax semantic package for the continued
two-step `ReducesN` bridge. This gives the nearby exact-step public wrappers one
local owner theorem instead of repeated direct calls into the generic source
layer. -/
theorem continuedTwoStepPublicSpentSyntaxFullSemanticBridge_reducesN :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              totalCost rhoIntrinsicCostMap
                (rhoRewritePathOfReducesN continuedTwoStepReducesN) 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              totalCost rhoIntrinsicCostMap
                (rhoRewritePathOfReducesN continuedTwoStepReducesN) 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              2 ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)) := by
  simpa [continuedTwoStepReducesN_path_eq] using!
    continuedTwoStepPublicSpentSyntaxFullSemanticBridge

/-- Concrete exact-step direct spent-trace semantic package for the continued
two-step `ReducesN` bridge. This gives the nearby exact-step direct wrappers one
local owner theorem instead of repeated direct calls into the generic source
layer. -/
theorem continuedTwoStepDirectSpentTraceFullSemanticBridge_reducesN :
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN continuedTwoStepReducesN)).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toLedger =
          totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN) ∧
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPublicPattern =
          rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (rhoRewritePathOfReducesN continuedTwoStepReducesN)) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN continuedTwoStepReducesN))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN continuedTwoStepReducesN))) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN continuedTwoStepReducesN))) ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) 1 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            2 := by
  simpa [continuedTwoStepReducesN_path_eq] using!
    continuedTwoStepDirectSpentTraceFullSemanticBridge

theorem continuedTwoStepPublicSpentSyntax_modulus_reducesN :
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              totalCost rhoIntrinsicCostMap
                (rhoRewritePathOfReducesN continuedTwoStepReducesN) 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              2 := by
  rcases continuedTwoStepPublicSpentSyntaxFullSemanticBridge_reducesN with
    ⟨_, hwidth, hticks, htwo, _⟩
  exact ⟨hwidth, hticks, htwo⟩

theorem continuedTwoStepDirectSpentTrace_modulus_reducesN :
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
          totalCost rhoIntrinsicCostMap
            (rhoRewritePathOfReducesN continuedTwoStepReducesN) 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) 1 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            2 := by
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge_reducesN with
    ⟨_, _, _, _, _, _, _, hwidth, _, hticks, htwo⟩
  exact ⟨hwidth, hticks, htwo⟩

theorem continuedTwoStepPublicSpentSyntax_semantics_reducesN :
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              totalCost rhoIntrinsicCostMap
                (rhoRewritePathOfReducesN continuedTwoStepReducesN) 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              totalCost rhoIntrinsicCostMap
                (rhoRewritePathOfReducesN continuedTwoStepReducesN) 1 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN))) =
              2 ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)) := by
  exact continuedTwoStepPublicSpentSyntaxFullSemanticBridge_reducesN

theorem continuedTwoStepDirectSpentTrace_semantics_reducesN :
    (rhoIntrinsicDirectSpentTrace
      (rhoRewritePathOfReducesN continuedTwoStepReducesN)).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toLedger =
          totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN continuedTwoStepReducesN) ∧
      (rhoIntrinsicDirectSpentTrace
        (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPublicPattern =
          rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (rhoRewritePathOfReducesN continuedTwoStepReducesN)) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN continuedTwoStepReducesN))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN continuedTwoStepReducesN))) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (rhoRewritePathOfReducesN continuedTwoStepReducesN))) ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            totalCost rhoIntrinsicCostMap
              (rhoRewritePathOfReducesN continuedTwoStepReducesN) 1 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN continuedTwoStepReducesN)).toPattern =
            2 := by
  exact continuedTwoStepDirectSpentTraceFullSemanticBridge_reducesN

theorem continuedTwoStepNativeSemanticBridge :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        continuedTwoStepPath.length ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        continuedTwoStepPath.length := by
  exact continuedTwoStepNativeSemanticBundle.1

theorem continuedTwoStepNativeFullSemanticBridge :
    (traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        continuedTwoStepPath.length ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        continuedTwoStepPath.length) ∧
    (traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        2 ∧
    RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        2) := by
  exact continuedTwoStepNativeSemanticBundle

theorem continuedTwoStepCombinedFullSemanticBridge :
    ((traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        continuedTwoStepPath.length ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        continuedTwoStepPath.length) ∧
    (traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
    rhoSpentSyntaxAccount
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxAccount
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxWidth
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxWidth
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
        rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax
            (totalAction rhoIntrinsicLedgerAction
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
    rhoSpentSyntaxTicks
      (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
        2 ∧
    RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
    (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
      rhoLedgerToSpentSyntax
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
    RhoLedger.TraceCoherent
      ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
    rhoSpentSyntaxAccount
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxAccount
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxWidth
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxWidth
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
        rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
    rhoSpentSyntaxTicks
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        2)) ∧
    ((continuedTwoStepDirectSpent.toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      rhoLedgerShadow continuedTwoStepDirectSpent.toLedger =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      continuedTwoStepDirectSpent.depth = continuedTwoStepPath.length ∧
      rhoSpentSyntaxAccount continuedTwoStepDirectSpent.toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxTicks continuedTwoStepDirectSpent.toPattern =
        continuedTwoStepPath.length ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoIntrinsicDirectSpentTrace continuedTwoStepPath =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger)) ∧
    ((totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).temporalList.length =
        continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          continuedTwoStepPath.length ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) = 2 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 = continuedTwoStepPath.length)) := by
  exact ⟨continuedTwoStepNativeFullSemanticBridge,
    continuedTwoStepStepAppendFullSemanticBridge⟩

/-- Concrete public spent-syntax semantic package for the continued two-step bridge.
This gathers the path-level public cost facts together with the additive two-step
public no-leak facts. -/
theorem continuedTwoStepPublicFullSemanticBridge :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          continuedTwoStepPath.length ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
        traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxWidth
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
          rhoSpentSyntaxTicks
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction
                (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          2 ∧
      RhoLedger.TraceCoherent (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) := by
  rcases continuedTwoStepTraceShadowSemanticBridge with
    ⟨hTrace, hShadowTrace⟩
  rcases continuedTwoStepLedgerPublicTemporalSemanticBridge with
    ⟨_, hShadowCost, hPublicAccCost, hPublicWidthSpatial, hPublicWidthCost,
      hPublicTicksCost, hPublicTicksLen, _, hPublicCoherent⟩
  rcases continuedTwoStepStepAppendPublicSemanticBridge with
    ⟨hConcatPublicAcc, hConcatPublicWidth, hConcatPublicTicks⟩
  have hConcatPublicTicksTwo :
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            continuedTwoStepPath.length := hPublicTicksLen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  exact ⟨hTrace, hShadowCost, hPublicAccCost, hPublicWidthSpatial, hPublicTicksLen,
    hPublicWidthCost, hPublicTicksCost, hShadowTrace, hConcatPublicAcc,
    hConcatPublicWidth, hConcatPublicTicks, hConcatPublicTicksTwo,
    hPublicCoherent⟩

/-- Concrete direct-spent semantic package for the continued two-step bridge.
This gathers the direct-stack step-append facts together with the direct spent-trace
surface, modulus, and additive two-step no-leak facts. -/
theorem continuedTwoStepDirectFullSemanticBridge :
    continuedTwoStepDirectSpent.toLedger =
      totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      rhoLedgerShadow continuedTwoStepDirectSpent.toLedger =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      continuedTwoStepDirectSpent.depth = continuedTwoStepPath.length ∧
      rhoSpentSyntaxAccount continuedTwoStepDirectSpent.toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxTicks continuedTwoStepDirectSpent.toPattern =
        continuedTwoStepPath.length ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoIntrinsicDirectSpentTrace continuedTwoStepPath =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
        totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          2 := by
  rcases continuedTwoStepDirectSpent_stepAppendSemantics with
    ⟨hStepDirectLedger, hStepDirectShadow, hStepDirectDepth, hStepDirectAccCost,
      hStepDirectTicksLen, hStepDirectAppendStack, hStepDirectAppendSteps,
      hStepTraceAppend⟩
  rcases continuedTwoStepDirectSpentTraceFullSemanticBridge with
    ⟨hDirectSurface, hDirectLedger, hDirectPublicPattern, hDirectCoherent,
      hDirectAccPublic, _, _, hDirectWidthCost, _, hDirectTicksCost, hDirectTicksLen⟩
  rcases continuedTwoStepStepAppendDirectTraceSemanticBridge with
    ⟨hConcatDirectAcc, hConcatDirectWidth, hConcatDirectTicks, _⟩
  have hConcatDirectTicksTwo :
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          2 := by
    calc
      rhoSpentSyntaxTicks
          (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
            continuedTwoStepPath.length := hDirectTicksLen
      _ = 2 := by
        simp [continuedTwoStepPath, rewritePathAppend, GSLT.RewritePath.length, oneStepPath]
  exact ⟨hStepDirectLedger, hStepDirectShadow, hStepDirectDepth, hStepDirectAccCost,
    hStepDirectTicksLen, hStepDirectAppendStack, hStepDirectAppendSteps,
    hStepTraceAppend, hDirectAccPublic, hDirectWidthCost, hDirectTicksCost,
    hDirectSurface, hDirectLedger, hDirectPublicPattern, hDirectCoherent,
    hConcatDirectAcc, hConcatDirectWidth, hConcatDirectTicks,
    hConcatDirectTicksTwo⟩

/-- The shadow of the accumulated spent ledger agrees with the accumulated
trace account on the concrete two-step bridge. -/
theorem continuedTwoStepTotalAction_shadow_eq_traceAccount :
    rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace := by
  rcases continuedTwoStepTraceShadowSemanticBridge with
    ⟨_, hshadowTrace⟩
  exact hshadowTrace

/-- The accumulated continued trace account agrees with the accumulated path cost. -/
theorem continuedTwoStepTraceAccount_eq_totalCost :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath := by
  rcases continuedTwoStepTraceShadowSemanticBridge with
    ⟨htrace, _⟩
  exact htrace

theorem continuedTwoStepSemanticBridge :
    traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
      continuedTwoStepTrace =
        totalCost rhoIntrinsicCostMap
          continuedTwoStepPath ∧
      rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).spatial.card ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          continuedTwoStepPath.length ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
          totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoLedgerShadow (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) =
        traceAccount (S := rhoGSLT) (A := Nat) (k := 2) continuedTwoStepTrace ∧
      continuedTwoStepDirectSpent.toLedger =
        totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      rhoLedgerShadow continuedTwoStepDirectSpent.toLedger =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      continuedTwoStepDirectSpent.depth = continuedTwoStepPath.length ∧
      rhoSpentSyntaxAccount continuedTwoStepDirectSpent.toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath ∧
      rhoSpentSyntaxTicks continuedTwoStepDirectSpent.toPattern =
        continuedTwoStepPath.length ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))
          (rhoIntrinsicDirectSpentStack
            (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)) ∧
      continuedTwoStepDirectSpent =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoIntrinsicDirectSpentTrace continuedTwoStepPath =
        RhoDirectStack.append
          (rhoIntrinsicDirectStepSpent continuedTwoStepFirstStep)
          (rhoIntrinsicDirectStepSpent continuedTwoStepSecondStep) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoLedgerToSpentSyntax
              (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) ∧
      rhoSpentSyntaxWidth (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 0 ∧
      rhoSpentSyntaxTicks (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
        totalCost rhoIntrinsicCostMap continuedTwoStepPath 1 ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN
              (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
                rhoSpentSyntaxAccount
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
                rhoSpentSyntaxAccount
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN
              (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
                rhoSpentSyntaxWidth
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
                rhoSpentSyntaxWidth
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction
            (rhoRewritePathOfReducesN
              (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN)))) =
                rhoSpentSyntaxTicks
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
                rhoSpentSyntaxTicks
                  (rhoLedgerToSpentSyntax
                    (totalAction rhoIntrinsicLedgerAction
                      (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxAccount
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxAccount
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxWidth
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxWidth
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toPattern =
              rhoSpentSyntaxTicks
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
              rhoSpentSyntaxTicks
                (rhoIntrinsicDirectSpentTrace
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace
          (rhoRewritePathOfReducesN
            (reducesN_concat continuedTwoStepFirstReducesN continuedTwoStepSecondReducesN))).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxAccount
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxWidth
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxWidth
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep))) +
            rhoSpentSyntaxTicks
              (rhoLedgerToSpentSyntax
                (totalAction rhoIntrinsicLedgerAction
                  (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep))) ∧
      rhoSpentSyntaxTicks
        (rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath)) =
            2 ∧
      RhoLedger.TraceCoherent
        (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).SurfaceLike ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger =
        totalAction rhoIntrinsicLedgerAction continuedTwoStepPath ∧
      (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPublicPattern =
        rhoLedgerToSpentSyntax
          (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath) ∧
      RhoLedger.TraceCoherent
        ((rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toLedger) ∧
      rhoSpentSyntaxAccount
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxAccount
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxWidth
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxWidth
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepFirstStep)).toPattern +
          rhoSpentSyntaxTicks
            (rhoIntrinsicDirectSpentTrace
              (oneStepPath (S := rhoGSLT) continuedTwoStepSecondStep)).toPattern ∧
      rhoSpentSyntaxTicks
        (rhoIntrinsicDirectSpentTrace continuedTwoStepPath).toPattern =
          2 ∧
      (totalAction rhoIntrinsicLedgerAction continuedTwoStepPath).temporalList.length =
        continuedTwoStepPath.length ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 = 2 ∧
      traceAccount (S := rhoGSLT) (A := Nat) (k := 2)
        continuedTwoStepTrace 1 =
          continuedTwoStepPath.length := by
  rcases continuedTwoStepCombinedFullSemanticBridge with
    ⟨hnativeFull, hstepAppendFull⟩
  rcases hnativeFull with
    ⟨hnativeSemantic, hnativeConcat⟩
  rcases hstepAppendFull with
    ⟨hstepAppendSemantic, htemporal⟩
  rcases hnativeSemantic with
    ⟨hTrace, hShadowCost, hPublicAccCost, hPublicWidthSpatial, hPublicTicksLen,
      hPublicWidthCost, hPublicTicksCost, hShadowTrace, _, _, _, _, hDirectAccPublic,
      _, _, hDirectWidthCost, _, hDirectTicksCost, _⟩
  rcases hnativeConcat with
    ⟨_, _, _, hStepPublicAcc, hStepPublicWidth, hStepPublicTicks,
      hConcatPublicTicksTwo, hConcatPublicCoherent, hDirectSurface, hDirectLedger,
      hDirectPublicPattern, hDirectCoherent, hStepDirectAccAppend,
      hStepDirectWidthAppend, hStepDirectTicksAppend, hConcatDirectTicksTwo⟩
  rcases hstepAppendSemantic with
    ⟨hStepDirectLedger, hStepDirectShadow, hStepDirectDepth, hStepDirectAccCost,
      hStepDirectTicksLen, hStepDirectAppendStack, hStepDirectAppendSteps,
      hStepTraceAppend, _, _, _, _, _, _, _⟩
  rcases continuedTwoStepReducesNConcatSemanticBridge with
    ⟨hReducesNPublicAcc, hReducesNPublicWidth, hReducesNPublicTicks,
      hReducesNDirectAcc, hReducesNDirectWidth, hReducesNDirectTicks,
      hReducesNDirectCoherent⟩
  rcases htemporal with
    ⟨hTemporalLen, _, _, _, _, hTraceTicksTwo, hTraceTicksLen⟩
  constructor
  · exact hTrace
  · constructor
    · exact hShadowCost
    · constructor
      · exact hPublicAccCost
      · constructor
        · exact hPublicWidthSpatial
        · constructor
          · exact hPublicTicksLen
          · constructor
            · exact hPublicWidthCost
            · constructor
              · exact hPublicTicksCost
              · constructor
                · exact hShadowTrace
                · constructor
                  · exact hStepDirectLedger
                  · constructor
                    · exact hStepDirectShadow
                    · constructor
                      · exact hStepDirectDepth
                      · constructor
                        · exact hStepDirectAccCost
                        · constructor
                          · exact hStepDirectTicksLen
                          · constructor
                            · exact hStepDirectAppendStack
                            · constructor
                              · exact hStepDirectAppendSteps
                              · constructor
                                · exact hStepTraceAppend
                                · constructor
                                  · exact hDirectAccPublic
                                  · constructor
                                    · exact hDirectWidthCost
                                    · constructor
                                      · exact hDirectTicksCost
                                      · constructor
                                        · exact hReducesNPublicAcc
                                        · constructor
                                          · exact hReducesNPublicWidth
                                          · constructor
                                            · exact hReducesNPublicTicks
                                            · constructor
                                              · exact hReducesNDirectAcc
                                              · constructor
                                                · exact hReducesNDirectWidth
                                                · constructor
                                                  · exact hReducesNDirectTicks
                                                  · constructor
                                                    · exact hReducesNDirectCoherent
                                                    · constructor
                                                      · exact hStepPublicAcc
                                                      · constructor
                                                        · exact hStepPublicWidth
                                                        · constructor
                                                          · exact hStepPublicTicks
                                                          · constructor
                                                            · exact hConcatPublicTicksTwo
                                                            · constructor
                                                              · exact hConcatPublicCoherent
                                                              · constructor
                                                                · exact hDirectSurface
                                                                · constructor
                                                                  · exact hDirectLedger
                                                                  · constructor
                                                                    · exact hDirectPublicPattern
                                                                    · constructor
                                                                      · exact hDirectCoherent
                                                                      · constructor
                                                                        · exact hStepDirectAccAppend
                                                                        · constructor
                                                                          · exact hStepDirectWidthAppend
                                                                          · constructor
                                                                            · exact hStepDirectTicksAppend
                                                                            · constructor
                                                                              · exact hConcatDirectTicksTwo
                                                                              · constructor
                                                                                · exact hTemporalLen
                                                                                · constructor
                                                                                  · exact hTraceTicksTwo
                                                                                  · exact hTraceTicksLen

end Mettapedia.GSLT.Meredith.RhoExample
