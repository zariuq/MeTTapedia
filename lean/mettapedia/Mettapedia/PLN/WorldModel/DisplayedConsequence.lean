import Mettapedia.Logic.DisplayedAnytimeEvidence
import Mettapedia.PLN.WorldModel.WorldModelCalculus

/-!
# Proof-relevant staged evidence for world-model rules

World-model consequence and rewrite rules carry explicit side conditions.
This module lets an open-ended authority expose those conditions gradually
without turning a timeout, score, or provenance label into a proof.

`MonotoneEvidence.map` transports the original evidence fibre through the
rule's soundness theorem.  Thus the thin observer eventually reports that a
rule is usable, while auditors retain the actual side-condition witness that
licensed it.  Products compose two guarded consequence rules at a common
finite stage.  The same construction applies to sort-indexed higher-order
world-model queries.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.DisplayedConsequence

open Mettapedia.Logic.DisplayedAnytimeEvidence
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModel

universe u

/-! ## Global strength consequences -/

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Apply a guarded WM consequence theorem to staged evidence for its side
condition.  The evidence values themselves are unchanged. -/
def consequenceEvidence
    (rule : WMConsequenceRule State Query)
    (sideEvidence : MonotoneEvidence.{u} rule.side) :
    MonotoneEvidence.{u}
      (WMStrengthLE (State := State) (Query := Query)
        rule.premise rule.conclusion) :=
  sideEvidence.map rule.sound

/-- Specialize a guarded consequence to one selected world-model state. -/
def consequenceEvidenceAt
    (rule : WMConsequenceRule State Query)
    (sideEvidence : MonotoneEvidence.{u} rule.side) (world : State) :
    MonotoneEvidence.{u}
      (BinaryWorldModel.queryStrength
          (State := State) (Query := Query) world rule.premise ≤
        BinaryWorldModel.queryStrength
          (State := State) (Query := Query) world rule.conclusion) :=
  sideEvidence.map (fun side => rule.sound side world)

@[simp] theorem consequenceEvidence_EvidenceAt
    (rule : WMConsequenceRule State Query)
    (sideEvidence : MonotoneEvidence.{u} rule.side) (stage : Nat) :
    (consequenceEvidence rule sideEvidence).EvidenceAt stage =
      sideEvidence.EvidenceAt stage :=
  rfl

/-- A rule application cannot identify distinct side-condition witnesses:
the displayed fibre is retained exactly even when the result proposition is
only a strength inequality. -/
theorem consequenceEvidence_retains_distinct
    (rule : WMConsequenceRule State Query)
    (sideEvidence : MonotoneEvidence.{u} rule.side) {stage : Nat}
    {first second : sideEvidence.EvidenceAt stage}
    (different : first ≠ second) :
    (show (consequenceEvidence rule sideEvidence).EvidenceAt stage from first) ≠
      (show (consequenceEvidence rule sideEvidence).EvidenceAt stage from second) :=
  different

/-- Compose two guarded strength consequences.  Their semantic composition
is transitivity; their side condition is conjunction. -/
def transRule
    (first second : WMConsequenceRule State Query)
    (middle : first.conclusion = second.premise) :
    WMConsequenceRule State Query where
  side := first.side ∧ second.side
  premise := first.premise
  conclusion := second.conclusion
  sound sides world := by
    apply le_trans (first.sound sides.1 world)
    simpa [middle] using second.sound sides.2 world

/-- Staged applications compose by synchronizing the two actual witnesses,
not by conjoining two Boolean success flags. -/
def transEvidence
    (first second : WMConsequenceRule State Query)
    (middle : first.conclusion = second.premise)
    (firstEvidence : MonotoneEvidence.{u} first.side)
    (secondEvidence : MonotoneEvidence.{u} second.side) :
    MonotoneEvidence.{u}
      (WMStrengthLE (State := State) (Query := Query)
        first.premise second.conclusion) :=
  consequenceEvidence (transRule first second middle)
    (firstEvidence.prod secondEvidence)

/-- If both side-condition authorities are positively complete, their
composed rule is eventually usable whenever both semantic conditions hold. -/
theorem transEvidence_eventually_accepts_of_sides
    (first second : WMConsequenceRule State Query)
    (middle : first.conclusion = second.premise)
    (firstEvidence : MonotoneEvidence.{u} first.side)
    (secondEvidence : MonotoneEvidence.{u} second.side)
    (firstComplete : firstEvidence.EventuallyComplete)
    (secondComplete : secondEvidence.EventuallyComplete)
    (firstSide : first.side) (secondSide : second.side) :
    ∃ stage,
      (transEvidence first second middle firstEvidence secondEvidence).toCertificate.acceptsAt
        stage := by
  exact (MonotoneEvidence.prod_eventuallyComplete
    firstEvidence secondEvidence firstComplete secondComplete)
      ⟨firstSide, secondSide⟩

/-- Full positive completeness of the consequence stream additionally needs
reflection from the conclusion relation back to the selected rule's side
conditions.  This premise is explicit because an inequality may happen to
hold for reasons unrelated to the chosen proof plan. -/
theorem transEvidence_eventuallyComplete_of_reflectsSides
    (first second : WMConsequenceRule State Query)
    (middle : first.conclusion = second.premise)
    (firstEvidence : MonotoneEvidence.{u} first.side)
    (secondEvidence : MonotoneEvidence.{u} second.side)
    (firstComplete : firstEvidence.EventuallyComplete)
    (secondComplete : secondEvidence.EventuallyComplete)
    (reflectsSides :
      WMStrengthLE (State := State) (Query := Query)
        first.premise second.conclusion → first.side ∧ second.side) :
    (transEvidence first second middle firstEvidence secondEvidence).EventuallyComplete := by
  intro consequence
  exact transEvidence_eventually_accepts_of_sides first second middle
    firstEvidence secondEvidence firstComplete secondComplete
    (reflectsSides consequence).1 (reflectsSides consequence).2

/-! ## Evidence-valued query rewrites -/

/-- A staged side-condition authority turns an untyped WM rewrite into
proof-relevant evidence for its semantic equality at one state. -/
def rewriteEvidenceAt
    (rule : WMRewriteRule State Query)
    (sideEvidence : MonotoneEvidence.{u} rule.side) (world : State) :
    MonotoneEvidence.{u}
      (rule.derive world =
        BinaryWorldModel.evidence
          (State := State) (Query := Query) world rule.conclusion) :=
  sideEvidence.map (fun side => rule.sound side world)

/-- Likewise for a scalar-strength rewrite. -/
def strengthRewriteEvidenceAt
    (rule : WMStrengthRule State Query)
    (sideEvidence : MonotoneEvidence.{u} rule.side) (world : State) :
    MonotoneEvidence.{u}
      (rule.derive world =
        BinaryWorldModel.queryStrength
          (State := State) (Query := Query) world rule.conclusion) :=
  sideEvidence.map (fun side => rule.sound side world)

/-! ## Sort-indexed higher-order queries -/

namespace HigherOrder

variable {HOState Srt : Type*} {HOQuery : Srt → Type*}
variable [EvidenceType HOState] [WorldModelSigma HOState Srt HOQuery]

/-- The same evidence discipline for sort-indexed higher-order query
rewrites.  No first-order or Horn erasure occurs. -/
def rewriteEvidenceAt
    (rule : WorldModelSigma.WMRewriteRuleSigma HOState Srt HOQuery)
    (sideEvidence : MonotoneEvidence.{u} rule.side) (world : HOState) :
    MonotoneEvidence.{u}
      (rule.derive world = WorldModelSigma.evidence world rule.conclusion) :=
  sideEvidence.map (fun side => rule.sound side world)

/-- Sort-indexed strength rewrites retain the same staged witness fibre. -/
def strengthRewriteEvidenceAt
    (rule : WorldModelSigma.WMStrengthRuleSigma HOState Srt HOQuery)
    (sideEvidence : MonotoneEvidence.{u} rule.side) (world : HOState) :
    MonotoneEvidence.{u}
      (rule.derive world = WorldModelSigma.queryStrength world rule.conclusion) :=
  sideEvidence.map (fun side => rule.sound side world)

@[simp] theorem rewriteEvidenceAt_EvidenceAt
    (rule : WorldModelSigma.WMRewriteRuleSigma HOState Srt HOQuery)
    (sideEvidence : MonotoneEvidence.{u} rule.side)
    (world : HOState) (stage : Nat) :
    (rewriteEvidenceAt rule sideEvidence world).EvidenceAt stage =
      sideEvidence.EvidenceAt stage :=
  rfl

end HigherOrder

/-! ## Audited theorem crowns -/

#print axioms consequenceEvidence_retains_distinct
#print axioms transEvidence_eventually_accepts_of_sides
#print axioms transEvidence_eventuallyComplete_of_reflectsSides
#print axioms HigherOrder.rewriteEvidenceAt_EvidenceAt

end Mettapedia.PLN.WorldModel.DisplayedConsequence
