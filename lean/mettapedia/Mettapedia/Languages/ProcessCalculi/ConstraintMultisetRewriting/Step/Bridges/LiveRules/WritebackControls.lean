import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.Writeback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting

/-!
# Writeback with two identities, and exhaustion of the identity supply

The named ground link runs with the finite rule-identity type `Bool`.
One identity initially holds the rule and the other receives it. Holding both
identities makes the same writeback profile stuck although the base rule is
admitted. The condition concerns rule identities, not a global infinity law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.WritebackControls

open RuleSyntax RuleSyntax.RuleOccurrences
open OneFrame (Terms frames ext)
open Derived (link)

private abbrev X := frames (Closed.action Nat)
private abbrev E := ext (Closed.action Nat)
private abbrev program : Program (Terms Nat) := {link 1 2}
private def zones (_ : Rule (Terms Nat)) : Unit := ()
private def code (_ : Bool) : Rule (Terms Nat) := link 1 2

theorem offers : Offers program ({false} : Finset Bool) code := by
  intro rule
  constructor
  · intro member
    exact ⟨false, Finset.mem_singleton_self _, (Set.mem_singleton_iff.mp member).symm⟩
  · rintro ⟨_, _, same⟩
    exact Set.mem_singleton_iff.mpr same.symm

def initial := WritingBack.consuming zones Closed.token ({false} : Finset Bool) code

theorem represented : Writeback.Represents zones program Closed.token initial :=
  ⟨{false}, code, offers, ⟨true, by decide⟩, rfl⟩

theorem finite_identity_execution :
    ∃ run : (rstep X Nat Bool E (WritingBack.codes zones) (∅ : Set (Rule (Terms Nat)))).toStep.Run initial,
      run.word.length = 1 ∧ run.last.rules = {true} ∧ run.last.label 1 = 2 := by
  obtain ⟨firing, admitted, endpoint⟩ := WritingBack.lift_admits X (zoneOf := zones)
    (Closed.tokenFiring (P := program) rfl) (Closed.token_admitted rfl)
    (rules := ({false} : Finset Bool)) (code := code) (Finset.mem_singleton_self false) rfl
    (ρ' := true) (by decide)
  refine ⟨.cons firing admitted (.nil _), rfl, ?_, ?_⟩
  · change (firing.result X).rules = {true}
    rw [endpoint]
    simp [WritingBack.consuming]
  · change (firing.result X).label 1 = 2
    rw [endpoint]
    rfl

def full := WritingBack.consuming zones Closed.token (Finset.univ : Finset Bool) code

theorem no_spare_refuses :
    (Closed.tokenFiring (P := program) rfl).Admits X Closed.token ∧
      ¬ ∃ firing, (rstep X Nat Bool E (WritingBack.codes zones) (∅ : Set (Rule (Terms Nat)))).toStep.Admits
        (s := full) firing := by
  refine ⟨Closed.token_admitted rfl, ?_⟩
  rintro ⟨firing, admitted⟩
  exact WritingBack.stuck_of_no_identity X firing (fun identity => Finset.mem_univ identity) admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.WritebackControls
