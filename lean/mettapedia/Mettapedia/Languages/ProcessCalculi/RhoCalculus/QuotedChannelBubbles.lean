import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelDetermination
import Mettapedia.GSLT.Logic.ObserverBubble

/-!
# Sealing: two bubbles over the quoted-channel calculus

An observer that may place a process in a code-reading position compares code:
in the quoted-channel calculus its equality is syntactic identity
(`relEquiv_quoteFree_iff_eq`).  A bubble whose equality is behavioural must
therefore *seal* its processes: its observers may not place them in such
positions.  This module packages the two choices as bubbles over the same
calculus.

* `openBubble`: observers may use output payloads.  Its equality is syntactic
  identity, and its verdict decides every judgment (`openBubble_decides`).
* `sealedBubble`: observers are guarded.  Its equality identifies all passive
  processes; its verdict decides the passive fragment and syntactic identity,
  and answers `outsideFragment` elsewhere (`sealedBubble_outside`).

The two bubbles disagree about `nil ∣ nil` and `nil` without contradiction
(`bubbles_disagree`).  The sealed equality is a congruence for the sealed
observers (`sealed_equality_closedUnder`) and not for the open ones
(`sealed_equality_not_closedUnder_open`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass
open Mettapedia.GSLT.ObserverBubble
open Mettapedia.TypeTheory.AuthorityTheory

/-- Passivity, decided. -/
def isPassive : Proc → Bool
  | .nil => true
  | .par left right => isPassive left && isPassive right
  | _ => false

theorem passive_of_isPassive : ∀ {term : Proc}, isPassive term = true → Passive term
  | .nil, _ => .nil
  | .par _ _, passive => by
      simp only [isPassive, Bool.and_eq_true] at passive
      exact .par (passive_of_isPassive passive.1) (passive_of_isPassive passive.2)
  | .out _ _, passive => by simp [isPassive] at passive
  | .inp _ _, passive => by simp [isPassive] at passive
  | .echo _, passive => by simp [isPassive] at passive

/-- The authority of equality judgments for an observer class: evidence is a
proof of the relative equivalence, an obstruction a refutation. -/
def relAuthority (A : AdmissibleClass quotedRules) : Authority (Proc × Proc) where
  Holds judgment := A.RelEquiv barbs judgment.1 judgment.2
  Evidence judgment := A.RelEquiv barbs judgment.1 judgment.2
  Obstruction judgment := ¬ A.RelEquiv barbs judgment.1 judgment.2
  evidenceSound _ evidence := evidence
  obstructionSound _ obstruction := obstruction

/-! ## The open bubble -/

/-- The open verdict: syntactic identity decides the payload-observer
equality. -/
def openVerdict (judgment : Proc × Proc) :
    Outcome (quoteFree.RelEquiv barbs judgment.1 judgment.2)
      (¬ quoteFree.RelEquiv barbs judgment.1 judgment.2) Unit Empty :=
  if same : judgment.1 = judgment.2 then
    .established ((relEquiv_quoteFree_iff_eq _ _).mpr same)
  else
    .refuted fun related => same (eq_of_relEquiv_quoteFree related)

/-- **The open bubble**: observers may send processes as payloads. -/
def openBubble : Bubble quotedGSLT quotedRules ℕ where
  observers := quoteFree
  observations := barbs
  commitments := ∅
  Judgment := Proc × Proc
  authority := relAuthority quoteFree
  Boundary := Unit
  Receipt := Empty
  verdict judgment _ := openVerdict judgment
  verdict_budget_mono _ _ _ _ := Outcome.BudgetRefines.refl _
  equality left right := (left, right)
  equality_holds _ _ := Iff.rfl

/-- **The open bubble decides every equality judgment.** -/
theorem openBubble_decides (left right : Proc) :
    (openBubble.verdict (openBubble.equality left right) 0).isDecided = true := by
  change (openVerdict (left, right)).isDecided = true
  unfold openVerdict
  split <;> rfl

/-! ## The sealed bubble -/

/-- The sealed verdict: established on passive pairs and on identical
processes, `outsideFragment` otherwise. -/
def sealedVerdict (judgment : Proc × Proc) :
    Outcome (guarded.RelEquiv barbs judgment.1 judgment.2)
      (¬ guarded.RelEquiv barbs judgment.1 judgment.2) Unit Empty :=
  if passive : isPassive judgment.1 = true ∧ isPassive judgment.2 = true then
    .established (relEquiv_guarded_of_passive (passive_of_isPassive passive.1)
      (passive_of_isPassive passive.2))
  else if same : judgment.1 = judgment.2 then
    .established (by rw [same]; exact guarded.relEquiv_refl barbs _)
  else
    .outsideFragment ()

/-- **The sealed bubble**: guarded observers only. -/
def sealedBubble : Bubble quotedGSLT quotedRules ℕ where
  observers := guarded
  observations := barbs
  commitments := ∅
  Judgment := Proc × Proc
  authority := relAuthority guarded
  Boundary := Unit
  Receipt := Empty
  verdict judgment _ := sealedVerdict judgment
  verdict_budget_mono _ _ _ _ := Outcome.BudgetRefines.refl _
  equality left right := (left, right)
  equality_holds _ _ := Iff.rfl

/-- The sealed verdict answers `outsideFragment` beyond passive pairs and
identity, even where the sealed equality fails. -/
theorem sealedBubble_outside :
    (sealedBubble.verdict (sealedBubble.equality (.out .nil (.par .nil .nil)) (.out .nil .nil))
        0).asBool = none ∧
      ¬ sealedBubble.authority.Holds
        (sealedBubble.equality (.out .nil (.par .nil .nil)) (.out .nil .nil)) := by
  refine ⟨?_, not_guarded_relEquiv_out_payload .nil⟩
  change (sealedVerdict (.out .nil (.par .nil .nil), .out .nil .nil)).asBool = none
  unfold sealedVerdict
  rw [dif_neg (by simp [isPassive]), dif_neg (by simp)]
  rfl

/-! ## Two bubbles, one pair -/

/-- **The two bubbles disagree** about `nil ∣ nil` and `nil`: the sealed one
establishes the equality, the open one refutes it. -/
theorem bubbles_disagree :
    (sealedBubble.verdict (sealedBubble.equality (.par .nil .nil) .nil) 0).asBool = some true ∧
      (openBubble.verdict (openBubble.equality (.par .nil .nil) .nil) 0).asBool = some false := by
  constructor
  · change (sealedVerdict (.par .nil .nil, .nil)).asBool = some true
    unfold sealedVerdict
    rw [dif_pos (by simp [isPassive])]
    rfl
  · change (openVerdict (.par .nil .nil, .nil)).asBool = some false
    unfold openVerdict
    rw [dif_neg (by simp)]
    rfl

/-- The sealed equality is a congruence for the sealed observers. -/
theorem sealed_equality_closedUnder :
    guarded.ClosedUnder (fun left right =>
      sealedBubble.authority.Holds (sealedBubble.equality left right)) :=
  sealedBubble.equality_closedUnder

/-- **And not for the open observers.** -/
theorem sealed_equality_not_closedUnder_open :
    ¬ quoteFree.ClosedUnder (fun left right =>
      sealedBubble.authority.Holds (sealedBubble.equality left right)) :=
  not_guarded_closedUnder_payload

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel
