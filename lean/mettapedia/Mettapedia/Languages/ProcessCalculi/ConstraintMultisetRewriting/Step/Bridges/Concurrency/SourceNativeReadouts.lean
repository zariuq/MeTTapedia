import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.CanonicalHistories
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedCanonicalHistories
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedAnswerReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.HostedAnswers

/-!
# The existing source answer classes have actual native reading witnesses

Named histories of the stated plain source fragment are replayed by its
proved canonical representative, with the same rigid equation indices. Their actual hosted
execution is then adapted to an actual native sequential execution.
Answers are read from physical native rows, through their knowledge and
conditional-row matching semantics.

The source names remain in the history certificate. Forgetting those names
is a separate projection and does not count alternative equation origins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SourceNativeReadouts

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open RuleSyntax.StepWeb.HostedNative
open RuleSyntax.StepWeb.HostedNative.Rounds

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  (N : Nodes S Γ star) {D : Discipline S Γ star}

/-- An origin-checked source history with its actual native execution and native row reading.
No source answer value or observer-transport conclusion is a field of the certificate. -/
def NativeShows (P : SourceLanguage.Program κ Γ star D.Ty) (q : Comp κ Γ star D.Ty)
    (word : List RuleName) (occupied : Finset ℕ) (value : Term S Γ star) : Prop :=
  ∃ (replay : HostState S) (port : ℕ) (presented : Presented Γ star replay)
    (members : List (Member Γ star κ (translate N P))) (final : Finset ℕ)
    (last : NativeState S ℕ Γ star),
    Chain (FiresNamedCanonical N P) (Hosting.start N P q) P.equations.length word replay port ∧
      HostedCanonicalHistories.NamedMembers N P word members ∧ members.length = word.length ∧
      HostedRun (Hosting.start N P q) (startPresented N P q) occupied members replay presented final ∧
      NativeIterated.Sequential (state κ (Hosting.start N P q) (startPresented N P q) occupied)
        (members.map (Member.live N (Hosting.start N P q) (startPresented N P q) occupied)) last ∧
      NativeDead.DeadEquiv (state κ replay presented final) last ∧
      NativeClosedReadings.Reads last port (HostedAnswerReadings.answerPattern N value)

theorem classAnswer_iff_native {P : SourceLanguage.Program κ Γ star D.Ty}
    (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty) (plainQ : PlainComp q)
    (unopened : ∀ term ∈ q.data, ∀ name ∈ support term, name.scopes = [])
    (word : List RuleName) (occupied : Finset ℕ) (fuel : RuleName → ℕ) (value : Term S Γ star) :
    value ∈ classAnswer N P q word ↔ NativeShows N P q word occupied value := by
  constructor
  · rintro ⟨original,originalPort,history,shown⟩
    obtain ⟨replay,port,canonical,world,branch,_,represented,_⟩ :=
      canonical_representative N plainP q plainQ unopened history
    obtain ⟨members,presented,final,last,named,length,hosted,nativeRun,same⟩ :=
      HostedCanonicalHistories.canonical_chain_native N canonical (startPresented N P q) occupied fuel
    have answerSame := (answer_of_rule_word N q rfl history (canonical_chain_named N canonical)).1
    have shownReplay : value ∈ stateAnswer N replay port := by rwa [← answerSame]
    have present : port ∈ replay.present := by
      rw [represented.present]
      exact Finset.mem_insert_self _ _
    have read := (HostedAnswerReadings.reading_iff_stateAnswer (κ := κ) N replay presented final port present value).mpr shownReplay
    exact ⟨replay,port,presented,members,final,last,canonical,named,length,hosted,nativeRun,same,
      (NativeClosedReadings.deadEquiv_reads_iff same port (HostedAnswerReadings.answerPattern N value)).mp read⟩
  · rintro ⟨replay,port,presented,members,final,last,canonical,_,_,_,_,same,read⟩
    have adapted := (NativeClosedReadings.deadEquiv_reads_iff same port
      (HostedAnswerReadings.answerPattern N value)).mpr read
    exact ⟨replay,port,canonical_chain_named N canonical,
      (HostedAnswerReadings.reading_iff_stateAnswer (κ := κ) N replay presented final port adapted.1 value).mp adapted⟩

/-- The sequential witness produces a run of the actual native step with
one event per source name and the same physical final-row reading. -/
theorem native_run_of_shows {P : SourceLanguage.Program κ Γ star D.Ty}
    (q : Comp κ Γ star D.Ty) {word : List RuleName} {occupied : Finset ℕ} {value : Term S Γ star}
    (shown : NativeShows N P q word occupied value) :
    ∃ run : native.toStep.Run (state κ (Hosting.start N P q) (startPresented N P q) occupied),
      run.word.length = word.length ∧
        ∃ port, NativeClosedReadings.Reads run.last port (HostedAnswerReadings.answerPattern N value) := by
  obtain ⟨replay,port,presented,members,final,last,_,_,length,_,sequential,_,read⟩ := shown
  obtain ⟨witness⟩ := NativeRoundExecution.Witness.nonempty_iff.mpr sequential
  refine ⟨witness.toRun,?_,port,?_⟩
  · rw [witness.event_count,List.length_map,length]
  · rw [witness.toRun_last]
    exact read

/-- The world path and native execution share the actual canonical source endpoint.
The held execution retains the rigid source origins and exactly the same number of firings. -/
theorem native_shows_world {P : SourceLanguage.Program κ Γ star D.Ty}
    (q : Comp κ Γ star D.Ty) {word : List RuleName} {occupied : Finset ℕ} {value : Term S Γ star}
    (shown : NativeShows N P q word occupied value) :
    ∃ (replay : HostState S) (port : ℕ) (presented : Presented Γ star replay)
      (members : List (Member Γ star κ (translate N P))) (final : Finset ℕ)
      (last : NativeState S ℕ Γ star)
      (held : Worlds.HostedAnswers.Run N P q word.length),
      HostedCanonicalHistories.NamedMembers N P word members ∧ members.length = word.length ∧
      NativeIterated.Sequential (state κ (Hosting.start N P q) (startPresented N P q) occupied)
        (members.map (Member.live N (Hosting.start N P q) (startPresented N P q) occupied)) last ∧
      NativeDead.DeadEquiv (state κ replay presented final) last ∧
      NativeClosedReadings.Reads last port (HostedAnswerReadings.answerPattern N value) ∧
      RuleSyntax.StepWeb.Counted.originsOf N held.val = word.map (RuleSyntax.StepWeb.Counted.origin N) ∧
      held.val.last = RuleSyntax.StepWeb.Counted.heldState N P replay ∧
      Worlds.HostedAnswers.world N P (Worlds.HostedAnswers.projected N q held).val.last =
        Worlds.HostedAnswers.world N P replay ∧
      (Worlds.HostedAnswers.history N q held).length = word.length ∧
      RuleSyntax.Worlds.Shows (fun actual => value ∈ stateAnswer N actual port)
        (Worlds.HostedAnswers.world N P (Worlds.HostedAnswers.projected N q held).val.last) := by
  obtain ⟨replay,port,presented,members,final,last,canonical,named,length,_,nativeRun,same,read⟩ := shown
  have source := canonical_chain_named N canonical
  obtain ⟨held,origins,endpoint,worldEndpoint,historyLength⟩ := Worlds.HostedAnswers.named_history_world N q source
  have adapted := (NativeClosedReadings.deadEquiv_reads_iff same port
    (HostedAnswerReadings.answerPattern N value)).mpr read
  have answer := (HostedAnswerReadings.reading_iff_stateAnswer (κ := κ) N replay presented final port adapted.1 value).mp adapted
  refine ⟨replay,port,presented,members,final,last,held,named,length,nativeRun,same,read,
    origins,endpoint,worldEndpoint,historyLength,?_⟩
  rw [worldEndpoint]
  exact (Worlds.singleton_shows (Hosting.controlRules N) (RuleSyntax.StepWeb.Counted.equationRules N P)
    replay (fun actual => value ∈ stateAnswer N actual port)).mpr answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SourceNativeReadouts
