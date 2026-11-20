import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hosting

/-!
# Whole runs, both ways, and answers as bags

An alternative of the source is a run of the step: a state has one knowledge, and the step's choice
of firing is the source's choice of alternative. A configuration of the source, a bag of
alternatives, is represented by a **frontier** (`Frontier`): a multiset holding, for each live
alternative, a state that represents it. Its states are reached from the start by runs of the step.

* `answer_eq`, `finished_iff`: a finished alternative and the state that represents it show the
  same answer, as a set of closed readings.
* `frontier_answers`: **the answers of a configuration are the answers of its frontier**, as a bag.
  The frontier holds one state for each live alternative of the configuration (`Frontier.branches`),
  so its multiplicities are those of the source's live alternatives; the step alone determines the
  set of answers (`Answers.answers_as_sets`).
* `frontier_step`: a source step replaces one frontier state by one state per live alternative the
  step makes, each **one firing** away.
* `runs_forward`: every source run from a query has a frontier whose states are reached from the
  start by runs of the step.
* `runs_reflected`: every run of the step from the start reaches a state that represents an
  alternative of a configuration that a source run reaches.
* `finished_still`: a state that represents a finished alternative has no firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-! ## The answer of one alternative -/

/-- **The answer a state shows**: the closed data `g` such that its alternative's row reads as
`alt(value g, empty)`. -/
def stateAnswer (s : HostState S) (a : ℕ) : Set (Term S Γ star) :=
  {g | ∃ B : Interface.Frames.Frame S,
    rowReads s a B (observe (altN N (valueN N (Rigid.includeTerm B.arity g)) (emptyN N)))}

/-- **A finished state**: its alternative's row has readings, and every one is `alt(value v, empty)`. -/
def StateFinished (s : HostState S) (a : ℕ) : Prop :=
  (∃ (B : Interface.Frames.Frame S) (q : Observation S B.arity), rowReads s a B q) ∧
    ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity), rowReads s a B q →
      ∃ v, q = observe (altN N (valueN N v) (emptyN N))

theorem encStack_nil {V : Type} {Dv : V → MetaArity S} (f : Data κ Γ star → Term (signature S Dv) Γ star) :
    encStack N f ([] : List (SourceLanguage.Frame κ Γ star D.Ty)) = emptyN N := rfl

/-- **A finished alternative and its state show the same answer.** -/
theorem answer_eq {n : ℕ} {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) (finished : b.Finished (D := D)) :
    stateAnswer N s a = b.answer (D := D) := by
  obtain ⟨frames, t, focus⟩ := finished
  ext g
  constructor
  · rintro ⟨B, reads⟩
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp ((rep.reads B _).mp reads)
    rw [encBranch, encAlt, focus, frames] at same
    obtain ⟨onFocus, _⟩ := vec2_inj (N.args_eq same)
    have onValue := vec1_inj (N.args_eq onFocus)
    exact ⟨t, focus, B.Names, B.arity, σ, solved, onValue⟩
  · rintro ⟨t', focus', X, target, σ, solved, read⟩
    rw [focus] at focus'
    cases focus'
    refine ⟨⟨X, target⟩, (rep.reads _ _).mpr ((branchReads_observe N).mpr ⟨σ, solved, ?_⟩)⟩
    rw [encBranch, encAlt, focus, frames]
    show N.node .alt ![N.node .value ![instantiate σ t], _] = _
    rw [read]
    rfl

/-- **Finished means finished**: a live finished alternative is represented by a finished state, and
conversely. -/
theorem finished_iff {n : ℕ} {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) :
    (b.Finished (D := D) ∧ Solvable b.store) ↔ StateFinished N s a := by
  constructor
  · rintro ⟨⟨frames, t, focus⟩, ⟨X, target, σ, solved⟩⟩
    refine ⟨⟨⟨X, target⟩, _, (rep.reads _ _).mpr ⟨σ, solved, rfl⟩⟩, ?_⟩
    intro B q reads
    obtain ⟨σ', _, rfl⟩ := (rep.reads B q).mp reads
    refine ⟨instantiate σ' t, ?_⟩
    rw [encBranch, encAlt, focus, frames]
    rfl
  · rintro ⟨⟨B, q, reads⟩, shape⟩
    obtain ⟨v, rfl⟩ := shape B q reads
    obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp ((rep.reads B _).mp reads)
    obtain ⟨onFocus, onStack⟩ := alt_eq_encAlt N (instantiate σ) same.symm
    obtain ⟨t, focus, _⟩ := value_eq_encFocus N (instantiate σ) onFocus
    exact ⟨⟨empty_eq_encStack N (instantiate σ) onStack, t, focus⟩, B.Names, B.arity, σ, solved⟩

/-! ## Life and stillness -/

/-- A state with a firing represents a live alternative. -/
theorem live_of_fires {n : ℕ} {b : Branch κ Γ star D.Ty} {s s' : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) (fires : Fires N P s s') : Solvable b.store := by
  obtain ⟨f, admitted, _⟩ := fires
  obtain ⟨B, u, solved⟩ := admitted.2.2.1
  have known := RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved
  obtain ⟨σ, solvedσ, _⟩ := (rep.reads B _).mp ⟨_, known, rfl⟩
  exact ⟨B.Names, B.arity, σ, solvedσ⟩

include supply in
/-- **A finished alternative's state has no firing.** -/
theorem finished_still (plainP : PlainProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {s s' : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a) (plain : PlainBranch b)
    (finished : b.Finished (D := D)) : ¬ Fires N P s s' := by
  intro fires
  obtain ⟨w', bs, _, _, move, _⟩ := reflection N (supply := supply) plainP rep plain fires
  obtain ⟨frames, t, focus⟩ := finished
  obtain ⟨K, focus', fs, ps⟩ := b
  simp only at frames focus
  subst frames focus
  exact Move.value_still move

/-! ## Frontiers -/

/-- **A frontier of a configuration**: for each live alternative, a state that represents it. -/
structure Frontier (P : SourceLanguage.Program κ Γ star D.Ty) (C : Config κ Γ star D.Ty)
    (L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)) : Prop where
  branches : L.map Prod.fst = C.branches.filter (fun b => Solvable b.store)
  represents : ∀ x ∈ L, Represents N P C.world.scope x.1 x.2.1 x.2.2 ∧ PlainBranch x.1

/-- **The answers of a frontier**: those of its finished states, as a bag. -/
noncomputable def frontierAnswers (L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)) :
    Multiset (Set (Term S Γ star)) :=
  ((L.map Prod.snd).filter (fun sa => StateFinished N sa.1 sa.2)).map (fun sa => stateAnswer N sa.1 sa.2)

/-- **The answers of a configuration are the answers of its frontier**, as a bag. The frontier's
multiplicities are those of the source's live alternatives (`Frontier.branches`); they are not read
from the step. -/
theorem frontier_answers {C : Config κ Γ star D.Ty} {L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)}
    (frontier : Frontier N P C L) : C.answers (D := D) = frontierAnswers N L := by
  have live : ∀ x ∈ L, Solvable x.1.store := by
    intro x member
    have inside : x.1 ∈ L.map Prod.fst := Multiset.mem_map_of_mem _ member
    rw [frontier.branches] at inside
    exact (Multiset.mem_filter.mp inside).2
  have split : C.branches.filter (fun b => b.Finished (D := D) ∧ Solvable b.store) =
      (C.branches.filter (fun b => Solvable b.store)).filter (fun b => b.Finished (D := D)) := by
    rw [Multiset.filter_filter]
  unfold Config.answers frontierAnswers
  rw [split, ← frontier.branches, Multiset.filter_map, Multiset.map_map, Multiset.filter_map,
    Multiset.map_map]
  have sameFilter : L.filter ((fun b => b.Finished (D := D)) ∘ Prod.fst) =
      L.filter ((fun sa => StateFinished N sa.1 sa.2) ∘ Prod.snd) := by
    apply Multiset.filter_congr
    intro x member
    have := finished_iff N (frontier.represents x member).1
    exact ⟨fun fin => this.mp ⟨fin, live x member⟩, fun fin => (this.mpr fin).1⟩
  rw [sameFilter]
  apply Multiset.map_congr rfl
  intro x member
  have fin := (Multiset.mem_filter.mp member).2
  have finished := ((finished_iff N (frontier.represents x (Multiset.mem_of_mem_filter member)).1).mpr fin).1
  exact (answer_eq N (frontier.represents x (Multiset.mem_of_mem_filter member)).1 finished).symm

theorem Represents.mono {n n' : ℕ} {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) (le : n ≤ n') : Represents N P n' b s a :=
  ⟨rep.notRow, rep.present, rep.reads, rep.rows, rep.independent, rep.fresh.mono le, rep.noPending⟩

theorem Move.scope_le {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (move : Move D P supply w b w' bs) : w.scope ≤ w'.scope := by
  cases move <;> simp [World.fresh]

/-- **A source step moves the frontier by one firing per live alternative it makes.** -/
theorem frontier_step (plainP : PlainProgram P) {C C' : Config κ Γ star D.Ty}
    {L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)} (frontier : Frontier N P C L)
    (step : SourceLanguage.Step D P supply C C') :
    ∃ L', Frontier N P C' L' ∧ ∃ x rest new, L = x ::ₘ rest ∧ L' = new + rest ∧
      ∀ y ∈ new, Fires N P x.2.1 y.2.1 := by
  obtain ⟨w, w', b, rest, bs, live, move⟩ := step
  have bInside : b ∈ L.map Prod.fst := by
    rw [frontier.branches]
    exact Multiset.mem_filter.mpr ⟨Multiset.mem_cons_self _ _, live⟩
  obtain ⟨x, xMember, xb⟩ := Multiset.mem_map.mp bInside
  obtain ⟨L₀, split⟩ := Multiset.exists_cons_of_mem xMember
  have restBranches : L₀.map Prod.fst = rest.filter (fun b => Solvable b.store) := by
    have whole := frontier.branches
    rw [split, Multiset.map_cons, xb] at whole
    change _ = Multiset.filter _ (b ::ₘ rest) at whole
    rw [Multiset.filter_cons_of_pos (p := fun b => Solvable b.store) rest live] at whole
    exact (Multiset.cons_inj_right b).mp whole
  obtain ⟨repX, plainX⟩ := frontier.represents x xMember
  rw [xb] at repX plainX
  have simulate : ∀ b' (inside : b' ∈ bs.filter (fun b => Solvable b.store)),
      ∃ sa : HostState S × ℕ, Fires N P x.2.1 sa.1 ∧ Represents N P w'.scope b' sa.1 sa.2 ∧ PlainBranch b' := by
    intro b' inside
    obtain ⟨child, liveChild⟩ := Multiset.mem_filter.mp inside
    obtain ⟨s', a', fires, rep', plain'⟩ := simulation N plainP move repX plainX child liveChild
    exact ⟨(s', a'), fires, rep', plain'⟩
  let new : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ) :=
    (bs.filter (fun b => Solvable b.store)).attach.map fun b' => (b'.1, Classical.choose (simulate b'.1 b'.2))
  have newBranches : new.map Prod.fst = bs.filter (fun b => Solvable b.store) := by
    simp only [new, Multiset.map_map]
    exact Multiset.attach_map_val _
  refine ⟨new + L₀, ⟨?_, ?_⟩, x, L₀, new, split, rfl, ?_⟩
  · rw [Multiset.map_add, newBranches, restBranches]
    exact (Multiset.filter_add _ _ _).symm
  · intro y member
    rcases Multiset.mem_add.mp member with fresh | old
    · obtain ⟨⟨b', inside⟩, _, rfl⟩ := Multiset.mem_map.mp fresh
      exact (Classical.choose_spec (simulate b' inside)).2
    · obtain ⟨repY, plainY⟩ := frontier.represents y (by rw [split]; exact Multiset.mem_cons_of_mem old)
      exact ⟨repY.mono N (Move.scope_le move), plainY⟩
  · intro y member
    obtain ⟨⟨b', inside⟩, _, rfl⟩ := Multiset.mem_map.mp member
    exact (Classical.choose_spec (simulate b' inside)).1

/-! ## Whole runs -/

variable (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

theorem initial_live : Solvable ([] : List (Constraint κ Γ star)) :=
  ⟨Name κ, fam κ, generator (fam κ), fun _ member => by cases member⟩

/-- The start's frontier: the start state alone. -/
theorem frontier_initial (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    Frontier N P (Config.initial spaces q)
      {(initialBranch q, start N P q, P.equations.length)} := by
  refine ⟨?_, ?_⟩
  · change Multiset.map Prod.fst {(initialBranch q, start N P q, P.equations.length)} =
      Multiset.filter _ {initialBranch q}
    rw [Multiset.filter_singleton,
      if_pos (show Solvable (initialBranch (Ty := D.Ty) q).store from initial_live)]
    rfl
  · intro x member
    rw [Multiset.mem_singleton.mp member]
    exact ⟨start_represents N P q unopened, rfl, .inl ⟨q, rfl, plainQ⟩⟩

/-- **Every source run is followed by runs of the step**: a configuration that a source run reaches
from the query has a frontier, whose states are reached from the start by runs of the step. -/
theorem runs_forward (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L, Frontier N P C L ∧ ∀ x ∈ L, Relation.ReflTransGen (Fires N P) (start N P q) x.2.1 := by
  induction runs with
  | refl =>
      refine ⟨_, frontier_initial N spaces q plainQ unopened, ?_⟩
      intro x member
      rw [Multiset.mem_singleton.mp member]
  | tail _ step ih =>
      obtain ⟨L, frontier, reached⟩ := ih
      obtain ⟨L', frontier', x, rest, new, split, rfl, fires⟩ := frontier_step N plainP frontier step
      refine ⟨_, frontier', ?_⟩
      intro y member
      rcases Multiset.mem_add.mp member with fresh | old
      · exact (reached x (by rw [split]; exact Multiset.mem_cons_self _ _)).tail (fires y fresh)
      · exact reached y (by rw [split]; exact Multiset.mem_cons_of_mem old)

/-- **Every run of the step is a source run**: a state that a run of the step reaches from the start
represents an alternative of a configuration that a source run reaches from the query. -/
theorem runs_reflected (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {s : HostState S}
    (run : Relation.ReflTransGen (Fires N P) (start N P q) s) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Represents N P C.world.scope b s a ∧ PlainBranch b := by
  induction run with
  | refl =>
      exact ⟨_, initialBranch q, _, .refl, Multiset.mem_singleton_self _,
        start_represents N P q unopened, rfl, .inl ⟨q, rfl, plainQ⟩⟩
  | tail _ fires ih =>
      obtain ⟨C, b, a, runs, member, rep, plain⟩ := ih
      obtain ⟨w', bs, b', a', move, child, rep', plain'⟩ := reflection N (supply := supply) plainP rep plain fires
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      refine ⟨⟨w', bs + rest⟩, b', a', runs.tail ?_, Multiset.mem_add.mpr (.inl child), rep', plain'⟩
      obtain ⟨world, branches⟩ := C
      simp only at split
      subst split
      exact .move world w' b rest bs (live_of_fires N rep fires) move

#print axioms answer_eq
#print axioms finished_iff
#print axioms finished_still
#print axioms frontier_answers
#print axioms frontier_step
#print axioms runs_forward
#print axioms runs_reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
