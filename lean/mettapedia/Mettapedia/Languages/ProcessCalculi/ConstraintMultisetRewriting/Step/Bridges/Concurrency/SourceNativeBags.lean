import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.SourceNativeReadouts

/-!
# Delivered and complete answer bags through origin-checked native histories

The observed value of one rigid source word is the set of its actual native
row readings. Mapping these sets over the source's counted words retains
duplicate answer occurrences. Delivered finite cuts and quiescent complete
executions are separate statements.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SourceNativeBags

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  (N : Nodes S Γ star) {D : Discipline S Γ star}
  {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

def answers (P : SourceLanguage.Program κ Γ star D.Ty) (q : Comp κ Γ star D.Ty)
    (occupied : Finset ℕ) (word : List RuleName) : Set (Term S Γ star) :=
  {value | SourceNativeReadouts.NativeShows N P q word occupied value}

theorem answers_eq_class (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty) (plainQ : PlainComp q)
    (unopened : ∀ term ∈ q.data, ∀ name ∈ support term, name.scopes = [])
    (occupied : Finset ℕ) (fuel : RuleName → ℕ) :
    answers N P q occupied = classAnswer N P q := by
  funext word
  ext value
  exact (SourceNativeReadouts.classAnswer_iff_native N plainP q plainQ unopened word occupied fuel value).symm

theorem delivered_bag (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty) (plainQ : PlainComp q)
    (unopened : ∀ term ∈ q.data, ∀ name ∈ support term, name.scopes = [])
    (occupied : Finset ℕ) (fuel : RuleName → ℕ) {C : Config κ Γ star D.Ty}
    {L : Multiset (Branch κ Γ star D.Ty × List RuleName)} {G : Multiset (List RuleName)}
    (tracing : Tracing N P q C L G) :
    C.answers (D := D) =
      ((L.map Prod.snd).filter fun word => RuleSyntax.StepWeb.Counted.FinishedHeldClass N P q
        (word.map (RuleSyntax.StepWeb.Counted.origin N))).map (answers N P q occupied) := by
  rw [answers_eq_class N plainP q plainQ unopened occupied fuel]
  exact (Worlds.HostedAnswers.delivered_world_bag N q plainP plainQ unopened tracing).2

theorem delivered_prefix (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty) (plainQ : PlainComp q)
    (unopened : ∀ term ∈ q.data, ∀ name ∈ support term, name.scopes = [])
    (occupied : Finset ℕ) (fuel : RuleName → ℕ) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ (L : Multiset (Branch κ Γ star D.Ty × List RuleName)) (G : Multiset (List RuleName)),
      Tracing N P q C L G ∧ C.answers (D := D) =
        ((L.map Prod.snd).filter fun word => RuleSyntax.StepWeb.Counted.FinishedHeldClass N P q
          (word.map (RuleSyntax.StepWeb.Counted.origin N))).map (answers N P q occupied) := by
  obtain ⟨L,G,tracing⟩ := tracing_runs N spaces q plainP plainQ unopened runs
  exact ⟨L,G,tracing,delivered_bag N plainP q plainQ unopened occupied fuel tracing⟩

theorem complete_bag (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty) (plainQ : PlainComp q)
    (unopened : ∀ term ∈ q.data, ∀ name ∈ support term, name.scopes = [])
    (occupied : Finset ℕ) (fuel : RuleName → ℕ) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ words : Multiset (List RuleName),
      (∀ word, words.count word = if RuleSyntax.StepWeb.Counted.CompleteHeldRun N P q
        (word.map (RuleSyntax.StepWeb.Counted.origin N)) then 1 else 0) ∧
      C.answers (D := D) =
        (words.filter fun word => RuleSyntax.StepWeb.Counted.FinishedHeldClass N P q
          (word.map (RuleSyntax.StepWeb.Counted.origin N))).map (answers N P q occupied) := by
  obtain ⟨words,counts,_,observed⟩ := Worlds.HostedAnswers.complete_world_bag N spaces q plainP plainQ unopened runs quiet
  refine ⟨words,counts,?_⟩
  rw [answers_eq_class N plainP q plainQ unopened occupied fuel]
  exact observed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SourceNativeBags
