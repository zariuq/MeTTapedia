import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns

/-!
# The answers read from the step alone: the set of answers, not the bag

The run theorems match a configuration of the source by a **frontier**: one represented state for each
live alternative, so the frontier's multiplicities are those of the source's live alternatives
(`Frontier.branches`, `ArrowFrontier.branches`), and the bag `frontierAnswers` is read off states
whose number is taken from the source. What the step determines by itself, from the translation's
start and nothing else, is the **set** of answers:

* `stepAnswers N P q`: the answers shown by finished present rows of states that runs of the
  translated program reach from the start;
* `sourceAnswers D P supply spaces q`: the answers of the configurations that source runs reach;
* `answers_as_sets`: the two sets are equal, for the first fragment and queries whose names are
  unopened; `arrow_answers_as_sets`: the same for the fragment with `let`, under the clauses the run
  theorems use (each equation scoped, with its own site and binder sites distinct; the query scoped
  from its site, with distinct sites).

That the bag is not determined by the step is the exhibit in `Answers.SameStart`: two programs with
the same rules and the same start state have different bags (`Answers.SameStart.bags_differ`). The
exhibit in `Answers.Bags` is weaker: its two programs have one translation and different start states,
and the larger bag is read off one reachable state counted twice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-- **The answers the step shows**: the answers of finished present rows of states that runs of the
translated program reach from the start. -/
def stepAnswers {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    Set (Set (Term S Γ star)) :=
  {A | ∃ s a, Relation.ReflTransGen (Fires N P) (start N P q) s ∧ a ∈ s.present ∧
    StateFinished N s a ∧ stateAnswer N s a = A}

/-- **The answers the source gives**: the answers of the configurations that source runs reach. -/
def sourceAnswers (D : Discipline S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
    (supply : ℕ → Term S Γ star) (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty) :
    Set (Set (Term S Γ star)) :=
  {A | ∃ C, Runs D P supply (Config.initial spaces q) C ∧ A ∈ Config.answers (D := D) C}

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **A finished present row is the alternative's row**: the equation rows read as `eqn(…)`, never as
a finished alternative. -/
theorem finished_row {n : ℕ} {b : Branch κ Γ star D.Ty} {s : HostState S} {a a' : ℕ}
    (rep : Represents N P n b s a) (present : a' ∈ s.present) (finished : StateFinished N s a') :
    a' = a := by
  rw [rep.present, Finset.mem_insert, Finset.mem_range] at present
  rcases present with same | small
  · exact same
  · exfalso
    obtain ⟨⟨B, r, reads⟩, shape⟩ := finished
    obtain ⟨v, rfl⟩ := shape B r reads
    obtain ⟨σ, known, read⟩ := reads
    obtain ⟨θ, row⟩ := rep.rows B σ known a' small
    exact absurd (N.tag_eq (observe_injective (read.symm.trans row))) (by decide)

/-- An answer of a finished live alternative, at the state that represents it. -/
theorem answer_mem {C : Config κ Γ star D.Ty} {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ}
    (member : b ∈ C.branches) (rep : Represents N P C.world.scope b s a) (finished : StateFinished N s a) :
    stateAnswer N s a ∈ Config.answers (D := D) C := by
  obtain ⟨done, live⟩ := (finished_iff N rep).mpr finished
  rw [answer_eq N rep done]
  unfold Config.answers
  exact Multiset.mem_map.mpr ⟨b, Multiset.mem_filter.mpr ⟨member, done, live⟩, rfl⟩

/-- **As sets, the step alone determines the answers** (first fragment): the answers shown by finished
states that runs of the translated program reach from the start are exactly the answers of the
configurations that source runs reach. -/
theorem answers_as_sets (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    stepAnswers N P q = sourceAnswers D P supply spaces q := by
  ext A
  constructor
  · rintro ⟨s, a, run, present, fin, rfl⟩
    obtain ⟨C, b, a', runs, member, rep, _⟩ :=
      runs_reflected N (supply := supply) spaces q plainP plainQ unopened run
    obtain rfl := finished_row N rep present fin
    exact ⟨C, runs, answer_mem N member rep fin⟩
  · rintro ⟨C, runs, member⟩
    unfold Config.answers at member
    obtain ⟨b, inside, rfl⟩ := Multiset.mem_map.mp member
    obtain ⟨bMember, finished, live⟩ := Multiset.mem_filter.mp inside
    obtain ⟨L, frontier, reached⟩ := runs_forward N spaces q plainP plainQ unopened runs
    have bInside : b ∈ L.map Prod.fst := by
      rw [frontier.branches]
      exact Multiset.mem_filter.mpr ⟨bMember, live⟩
    obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp bInside
    obtain ⟨rep, _⟩ := frontier.represents x xMember
    refine ⟨x.2.1, x.2.2, reached x xMember, ?_, (finished_iff N rep).mp ⟨finished, live⟩,
      answer_eq N rep finished⟩
    rw [rep.present]
    exact Finset.mem_insert_self _ _

/-- **As sets, the step alone determines the answers** (the fragment with `let`), under the clauses
the run theorems use: every equation scoped, with its own site and its binder sites distinct, and of
the fragment with arrows; the query scoped from its site, with distinct sites, and of the fragment. -/
theorem arrow_answers_as_sets
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) :
    stepAnswers N P q = sourceAnswers D P supply spaces q := by
  ext A
  constructor
  · rintro ⟨s, a, run, present, fin, rfl⟩
    obtain ⟨C, b, a', runs, member, rep, _⟩ :=
      arrow_runs_reflected_of_scoped N (supply := supply) spaces q equations qScoped qDistinct arrowQ run
    obtain rfl := finished_row N rep present fin
    exact ⟨C, runs, answer_mem N member rep fin⟩
  · rintro ⟨C, runs, member⟩
    unfold Config.answers at member
    obtain ⟨b, inside, rfl⟩ := Multiset.mem_map.mp member
    obtain ⟨bMember, finished, live⟩ := Multiset.mem_filter.mp inside
    obtain ⟨L, frontier, reached⟩ :=
      arrow_runs_forward_of_scoped N spaces q equations qScoped qDistinct arrowQ runs
    have bInside : b ∈ L.map Prod.fst := by
      rw [frontier.branches]
      exact Multiset.mem_filter.mpr ⟨bMember, live⟩
    obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp bInside
    obtain ⟨rep, _⟩ := frontier.represents x xMember
    refine ⟨x.2.1, x.2.2, reached x xMember, ?_, (finished_iff N rep).mp ⟨finished, live⟩,
      answer_eq N rep finished⟩
    rw [rep.present]
    exact Finset.mem_insert_self _ _

#print axioms finished_row
#print axioms answer_mem
#print axioms answers_as_sets
#print axioms arrow_answers_as_sets

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers
