import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Sets

/-!
# Why a configuration is followed by several states: a reachable state shows one answer

Configuration by configuration, the forward half of the hosting is a frontier of several states
(`Hosting.runs_forward`), not one state. Two facts say why, and which reason is the right one.

* **A reachable state shows at most one answer.** `one_finished_row` (first fragment, any program): a
  state that a run of the translated program reaches from the start has at most one finished present
  row. For the query `choice (ret a) (ret b)` of the program with no equation, a source run reaches a
  configuration with the two answers `{a}` and `{b}` (`two_answers`), and no state the step reaches from
  the start shows both (`no_state_shows_both`). So no relation that carries the answers of a
  configuration to one related state has a forward law.
* **The query `fail` is not that reason.** `Examples.no_forward_at_fail` holds at the relation
  `TracksPlain`, which relates a state to a configuration through one of its alternatives and so relates
  nothing to a configuration without alternatives. At the same program and query there is an
  operational correspondence with both halves (`GSLT.IndexedOperational.OperationalCorrespondence`)
  between the source's configurations and the step's states (`failCorrespondence`): it relates the
  query's configuration and the exhausted configuration to the start state, which has no firing
  (`start_still`, `start_related`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.OneAnswer

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Mettapedia.GSLT.IndexedOperational (OperationalCorrespondence ExecutionPath)
open Classical

/-! ## A reachable state shows one answer -/

section General

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}
  {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  (supply : ℕ → Term S Γ star) (q : Comp κ Γ star D.Ty)

include D supply in
/-- **A reachable state has at most one finished present row.** -/
theorem one_finished_row (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {s : HostState S}
    (run : Relation.ReflTransGen (Fires N P) (start N P q) s) {a a' : ℕ} (present : a ∈ s.present)
    (present' : a' ∈ s.present) (finished : StateFinished N s a) (finished' : StateFinished N s a') :
    a = a' := by
  obtain ⟨C, b, a₀, _, _, rep, _⟩ :=
    runs_reflected N (D := D) (supply := supply) (fun _ => 0) q plainP plainQ unopened run
  exact (Answers.finished_row N rep present finished).trans (Answers.finished_row N rep present' finished').symm

end General

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Examples

def aT : MData := sym "a"
def bT : MData := sym "b"
def aC : MClosed := csym "a"
def bC : MClosed := csym "b"

/-- The query `choice (ret a) (ret b)`. -/
def q2 : Comp mkeys [] () MTy := .choice (.ret aT) (.ret bT)

abbrev W0 : World mkeys [] () := ⟨0, 0, sp⟩
abbrev Xa : Branch mkeys [] () MTy := ⟨[], .eval (.ret aT), [], []⟩
abbrev Xb : Branch mkeys [] () MTy := ⟨[], .eval (.ret bT), [], []⟩
abbrev Ya : Branch mkeys [] () MTy := ⟨[], .value aT, [], []⟩
abbrev Yb : Branch mkeys [] () MTy := ⟨[], .value bT, [], []⟩

/-- The configuration with both answers. -/
def final2 : Config mkeys [] () MTy := ⟨W0, {Yb, Ya}⟩

theorem runs2 : Runs D empty supply (Config.initial sp q2) final2 := by
  refine Relation.ReflTransGen.tail (b := ⟨W0, {Ya, Xb}⟩) ?_
    (Step.of_eq (D := D) (P := empty) (supply := supply) (b := Xb) (rest := {Ya}) (Multiset.cons_swap _ _ _) rfl
      live_nil (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W0, {Xa, Xb}⟩) ?_
    (Step.of_eq (D := D) (P := empty) (supply := supply) (b := Xa) (rest := {Xb}) rfl rfl live_nil
      (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (Step.of_eq (rest := 0) rfl rfl live_nil (.choice W0 [] _ _ [] []))

theorem a_ne_b : ({aC} : Set MClosed) ≠ {bC} := by
  intro same
  have terms : aC = bC := Set.singleton_eq_singleton_iff.mp same
  simp [aC, bC, csym] at terms

/-- **A source run reaches a configuration with two different answers.** -/
theorem two_answers : Runs D empty supply (Config.initial sp q2) final2 ∧
    ({aC} : Set MClosed) ∈ Config.answers (D := D) final2 ∧
    ({bC} : Set MClosed) ∈ Config.answers (D := D) final2 ∧ ({aC} : Set MClosed) ≠ {bC} := by
  have answers : Config.answers (D := D) final2 = {{bC}, {aC}} := by
    show Config.answers (D := D) ⟨W0, Yb ::ₘ {Ya}⟩ = _
    rw [answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ live_nil, answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_nil,
      answer_of_determines (D := D) (b := Yb) (g := bC) rfl ⟨live_nil, fun _ _ _ => rfl⟩,
      answer_of_determines (D := D) (b := Ya) (g := aC) rfl ⟨live_nil, fun _ _ _ => rfl⟩]
    rfl
  refine ⟨runs2, ?_, ?_, a_ne_b⟩
  · rw [answers]
    exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)
  · rw [answers]
    exact Multiset.mem_cons_self _ _

theorem q2_unopened : ∀ t ∈ q2.data, ∀ x ∈ support t, x.scopes = [] := by decide

/-- **No state the step reaches from the start shows both answers.** -/
theorem no_state_shows_both {s : HostState MSig}
    (run : Relation.ReflTransGen (Fires N empty) (Hosting.start N empty q2) s) :
    ¬ ∃ a a', a ∈ s.present ∧ a' ∈ s.present ∧ StateFinished N s a ∧ StateFinished N s a' ∧
      stateAnswer N s a = {aC} ∧ stateAnswer N s a' = {bC} := by
  rintro ⟨a, a', present, present', finished, finished', answerA, answerB⟩
  have same := one_finished_row N (D := D) supply q2 plainEmpty ⟨trivial, trivial⟩ q2_unopened run present
    present' finished finished'
  subst same
  exact a_ne_b (answerA.symm.trans answerB)

/-! ## At the query `fail` a correspondence with both halves exists -/

abbrev failQ : Comp mkeys [] () MTy := .fail

/-- The query's configuration. -/
abbrev C₀ : Config mkeys [] () MTy := Config.initial sp failQ

/-- The configuration with no alternative. -/
abbrev C₁ : Config mkeys [] () MTy := ⟨⟨0, 0, sp⟩, 0⟩

/-- The start of the query. -/
abbrev s₀ : HostState MSig := Hosting.start N empty failQ

theorem fail_unopened : ∀ t ∈ failQ.data, ∀ x ∈ support t, x.scopes = [] := fun _ member => by cases member

theorem move_fail {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {bs : Multiset (Branch mkeys [] () D.Ty)} (move : Move D empty supply w b w' bs)
    (hb : b = ⟨[], .eval .fail, [], []⟩) : bs = 0 ∧ w' = w := by
  cases move <;> cases hb
  exact ⟨rfl, rfl⟩

/-- **The start of the query `fail` has no firing.** -/
theorem start_still (s' : HostState MSig) : ¬ Fires N empty s₀ s' := by
  intro fires
  obtain ⟨w', bs, b', a', move, child, _, _⟩ :=
    reflection N (D := D) (supply := supply) (w := ⟨0, 0, sp⟩) plainEmpty
      (start_represents N empty failQ fail_unopened) ⟨rfl, .inl ⟨failQ, rfl, trivial⟩⟩ fires
  rw [(move_fail move rfl).1] at child
  exact absurd child (Multiset.notMem_zero b')

/-- **The only step of the query's configuration** is to the configuration with no alternative. -/
theorem step_from_start {C C' : Config mkeys [] () MTy} (atStart : C = C₀)
    (step : SourceLanguage.Step D empty supply C C') : C' = C₁ := by
  obtain ⟨w, w', b, rest, bs, _, move⟩ := step
  have world : w = ⟨0, 0, sp⟩ := congrArg Config.world atStart
  have branches : b ::ₘ rest = {⟨[], .eval .fail, [], []⟩} := congrArg Config.branches atStart
  have cardEq := congrArg Multiset.card branches
  simp only [Multiset.card_cons, Multiset.card_singleton] at cardEq
  have noRest : rest = 0 := Multiset.card_eq_zero.mp (by omega)
  subst noRest world
  have isFail : b = ⟨[], .eval .fail, [], []⟩ := Multiset.singleton_inj.mp branches
  obtain ⟨noChild, sameWorld⟩ := move_fail move isFail
  subst noChild sameWorld
  rfl

/-- The configuration with no alternative has no step. -/
theorem exhausted_still {C C' : Config mkeys [] () MTy} (exhausted : C = C₁) :
    ¬ SourceLanguage.Step D empty supply C C' := by
  intro step
  obtain ⟨w, w', b, rest, bs, _, _⟩ := step
  have branches : b ::ₘ rest = 0 := congrArg Config.branches exhausted
  exact Multiset.cons_ne_zero branches

/-- **An operational correspondence, both halves, at the query `fail`**: the query's configuration and
the exhausted configuration are related to the start state. -/
def failCorrespondence : OperationalCorrespondence (sourceSystem D empty supply) (hostSystem N empty) where
  related C s := s = s₀ ∧ (C = C₀ ∨ C = C₁)
  readStep := by
    rintro C s s' ⟨rfl, _⟩ fires
    exact absurd fires (start_still s')
  forward := by
    rintro C C' s ⟨rfl, atStart | exhausted⟩ step
    · exact ⟨s₀, ⟨.refl _⟩, rfl, .inr (step_from_start atStart step)⟩
    · exact absurd step (exhausted_still exhausted)

/-- It relates the query's configuration to the start, and the configuration the source steps to (the
step of `Examples.no_forward_at_fail`) to the same state. -/
theorem start_related :
    failCorrespondence.related C₀ s₀ ∧ SourceLanguage.Step D empty supply C₀ C₁ ∧
      failCorrespondence.related C₁ s₀ :=
  ⟨⟨rfl, .inl rfl⟩, no_forward_at_fail.2.1, ⟨rfl, .inr rfl⟩⟩

#print axioms one_finished_row
#print axioms two_answers
#print axioms no_state_shows_both
#print axioms start_still
#print axioms step_from_start
#print axioms failCorrespondence
#print axioms start_related

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.OneAnswer
