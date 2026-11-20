import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativeClosedReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNativeRounds
import Mettapedia.OSLF.Syntax.ContextualRigidReflection

/-!
# The existing hosted answer observer descends through native dead-name agreement

At a real alternative occurrence, the existing hosted `stateAnswer` is the conditional-row reading
of the actual adapted native state. Its answer pattern is closed syntax and its knowledge has real
models. Dead-name agreement therefore preserves this observer. The existing every-order hosted
execution theorem supplies actual endpoints to which this law applies.

The observer reads each physical occurrence separately. It does not quotient rigid equation origins,
count alternative histories or discard an ordered-history observation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedAnswerReadings

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open RuleSyntax.StepWeb.HostedNative
open RuleSyntax.StepWeb.HostedNative.Rounds
open NativeClosedReadings

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}

/-- The same completed alternative pattern used by `Hosting.stateAnswer`, before embedding its
closed syntax into a model's declaration frame. -/
def answerPattern (N : Nodes S Γ star) (value : Term S Γ star) : ClosedTerm S Γ star :=
  altN N (valueN N (Rigid.includeTerm (closedArity S) value)) (emptyN N)

theorem empty_node_natural (N : Nodes S Γ star) {V W : Type}
    {source : V → MetaArity S} {target : W → MetaArity S}
    (candidate : Assignment source target) :
    instantiate candidate (emptyN N) = emptyN N := by
  change instantiate candidate (N.node .empty ![]) = N.node .empty ![]
  rw [N.instantiate_node]
  exact congrArg (N.node .empty) (map_vec0 (instantiate candidate))

theorem closedAt_answerPattern (N : Nodes S Γ star) {V : Type} (declaration : V → MetaArity S)
    (value : Term S Γ star) :
    closedAt declaration (answerPattern N value) =
      altN N (valueN N (Rigid.includeTerm declaration value)) (emptyN N) := by
  unfold closedAt answerPattern
  rw [instantiate_altN, instantiate_valueN, Rigid.instantiate_include, empty_node_natural]

theorem answerPattern_injective (N : Nodes S Γ star) : Function.Injective (answerPattern N) := by
  intro first second same
  have focus := (vec2_inj (N.args_eq same)).1
  have datum := vec1_inj (N.args_eq focus)
  exact Rigid.include_injective (closedArity S) first second datum

/-- The actual shared native row of a presented hosted state has exactly the existing source
answer readings. Presence is explicit because `rowReads` alone also reads missing labels. -/
theorem reading_iff_stateAnswer (N : Nodes S Γ star) (hosted : HostState S)
    (presented : Presented Γ star hosted) (occupied : Finset Nat) (occurrence : Nat)
    (present : occurrence ∈ hosted.present) (value : Term S Γ star) :
    Reads (state κ hosted presented occupied) occurrence (answerPattern N value) ↔
      value ∈ stateAnswer N hosted occurrence := by
  constructor
  · rintro ⟨_, target, candidate, model, matched⟩
    change ContextualConditionalRows.Matches (ruleLocals Γ star κ) hosted.frame.arity candidate
      (closedAt target.arity (answerPattern N value))
      (ContextualConditionalRows.ofStored (ruleLocals Γ star κ) hosted.frame.arity
        (.shared (presented.term occurrence))) at matched
    rw [closedAt_answerPattern] at matched
    have shared := (ContextualConditionalRows.ofStored_matches_iff (ruleLocals Γ star κ)
      hosted.frame.arity candidate _ (.shared (presented.term occurrence))).mp matched
    have same := (ContextualGuardMatching.shared_matches_iff (ruleLocals Γ star κ)
      candidate _ (presented.term occurrence)).mp shared
    refine ⟨target, candidate, model, ?_⟩
    rw [presented.label_eq occurrence]
    exact congrArg observe same.symm
  · rintro ⟨target, candidate, model, same⟩
    refine ⟨present, target, candidate, model, ?_⟩
    change ContextualConditionalRows.Matches (ruleLocals Γ star κ) hosted.frame.arity candidate
      (closedAt target.arity (answerPattern N value))
      (ContextualConditionalRows.ofStored (ruleLocals Γ star κ) hosted.frame.arity
        (.shared (presented.term occurrence)))
    rw [closedAt_answerPattern]
    apply (ContextualConditionalRows.ofStored_matches_iff (ruleLocals Γ star κ)
      hosted.frame.arity candidate _ (.shared (presented.term occurrence))).mpr
    apply (ContextualGuardMatching.shared_matches_iff (ruleLocals Γ star κ)
      candidate _ (presented.term occurrence)).mpr
    rw [presented.label_eq occurrence] at same
    exact (observe_injective same).symm

theorem adapted_present_eq {first second : HostState S}
    {left : Presented Γ star first} {right : Presented Γ star second}
    {firstOccupied secondOccupied : Finset Nat}
    (same : NativeDead.DeadEquiv (state κ first left firstOccupied)
      (state κ second right secondOccupied)) :
    first.present = second.present :=
  NativeClosedReadings.deadEquiv_present same

/-- This is equality of the existing source observer, at the same physical alternative occurrence
of two genuinely adapted native states. -/
theorem stateAnswer_deadEquiv (N : Nodes S Γ star) {first second : HostState S}
    {left : Presented Γ star first} {right : Presented Γ star second}
    {firstOccupied secondOccupied : Finset Nat}
    (same : NativeDead.DeadEquiv (state κ first left firstOccupied)
      (state κ second right secondOccupied))
    (occurrence : Nat) (present : occurrence ∈ first.present) :
    stateAnswer N first occurrence = stateAnswer N second occurrence := by
  have nextPresent : occurrence ∈ second.present := by
    rw [← adapted_present_eq same]
    exact present
  ext value
  exact (reading_iff_stateAnswer N first left firstOccupied occurrence present value).symm.trans
    ((NativeClosedReadings.deadEquiv_reads_iff same occurrence (answerPattern N value)).trans
      (reading_iff_stateAnswer N second right secondOccupied occurrence nextPresent value))

/-- A real source representation supplies the alternative's actual present occurrence. -/
theorem stateAnswer_deadEquiv_of_rep (N : Nodes S Γ star) {Ty : Type}
    {P : SourceLanguage.Program κ Γ star Ty} {scope : Nat} {branch : Branch κ Γ star Ty}
    {first second : HostState S} {left : Presented Γ star first} {right : Presented Γ star second}
    {firstOccupied secondOccupied : Finset Nat}
    (same : NativeDead.DeadEquiv (state κ first left firstOccupied)
      (state κ second right secondOccupied))
    {occurrence : Nat} (represented : Represents N P scope branch first occurrence) :
    stateAnswer N first occurrence = stateAnswer N second occurrence := by
  apply stateAnswer_deadEquiv N same occurrence
  rw [represented.present]
  exact Finset.mem_insert_self _ _

/-- Every actual order retains the existing answer observer at every common present occurrence.
The actual hosted runs and their native dead-name agreement are supplied by the existing
`every_order_hosted` theorem. -/
theorem every_order_hosted_answers [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {P : CProgram S}
    (N : Nodes S Γ star) (hosted : HostState S) (presented : Presented Γ star hosted)
    (occupied : Finset Nat) (members : List (Member Γ star κ P))
    (clear : NativeIterated.FamilyClear (state κ hosted presented occupied)
      (members.map (Member.live N hosted presented occupied))) :
    ∃ (first : HostState S) (left : Presented Γ star first) (firstOccupied : Finset Nat),
      HostedRun hosted presented occupied members first left firstOccupied ∧
        ∀ order : List (Member Γ star κ P), order.Perm members →
          ∃ (second : HostState S) (right : Presented Γ star second) (secondOccupied : Finset Nat),
            HostedRun hosted presented occupied order second right secondOccupied ∧
              NativeDead.DeadEquiv (state κ first left firstOccupied)
                (state κ second right secondOccupied) ∧
              first.present = second.present ∧
              ∀ occurrence ∈ first.present,
                stateAnswer N first occurrence = stateAnswer N second occurrence := by
  obtain ⟨first, left, firstOccupied, run, every⟩ :=
    every_order_hosted N hosted presented occupied members clear
  refine ⟨first, left, firstOccupied, run, fun order perm => ?_⟩
  obtain ⟨second, right, secondOccupied, nextRun, same⟩ := every order perm
  exact ⟨second, right, secondOccupied, nextRun, same, adapted_present_eq same,
    fun occurrence present => stateAnswer_deadEquiv N same occurrence present⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedAnswerReadings
