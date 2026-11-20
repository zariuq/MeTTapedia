import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Runs

/-!
# Whole runs of the fragment with arrows, given hygiene

The run-level correspondence of `Runs` for `ret`, `apply`, `let_`, `choice`, `fail`, under one
hypothesis on the source alone: **every alternative of every configuration reachable from the query is
hygienic** (`ReachableHygienic`). For the first fragment the hypothesis holds (no alternative has a
pending frame: `reachableHygienic_of_plain`); for well-formed programs and queries with arrows it is
proved in `Hygiene`, and `WellFormedRuns` states the run theorems without it. `hygiene_needed` shows
that the correspondence of a bind fails without it.

* `arrowFrontier_answers`: the answers of a configuration are those of its frontier, as a bag.
* `arrowFrontier_step`: a source step moves the frontier by one firing per live alternative.
* `arrow_runs_forward_of_hygienic`, `arrow_runs_reflected_of_hygienic`: whole runs, both ways.
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

/-- **A frontier of the fragment with arrows.** -/
structure ArrowFrontier (P : SourceLanguage.Program κ Γ star D.Ty) (C : Config κ Γ star D.Ty)
    (L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)) : Prop where
  branches : L.map Prod.fst = C.branches.filter (fun b => Solvable b.store)
  represents : ∀ x ∈ L, Represents N P C.world.scope x.1 x.2.1 x.2.2 ∧ ArrowBranch x.1

/-- **The answers of a configuration are the answers of its frontier.** -/
theorem arrowFrontier_answers {C : Config κ Γ star D.Ty} {L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)}
    (frontier : ArrowFrontier N P C L) : C.answers (D := D) = frontierAnswers N L := by
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

/-- **A source step moves the frontier by one firing per live alternative it makes**, when the
moving alternatives are hygienic. -/
theorem arrowFrontier_step (arrowP : ArrowProgram P) {C C' : Config κ Γ star D.Ty}
    {L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)} (frontier : ArrowFrontier N P C L)
    (hygienic : ∀ b ∈ C.branches, Hygienic b) (step : SourceLanguage.Step D P supply C C') :
    ∃ L', ArrowFrontier N P C' L' ∧ ∃ x rest new, L = x ::ₘ rest ∧ L' = new + rest ∧
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
  obtain ⟨repX, arrowX⟩ := frontier.represents x xMember
  rw [xb] at repX arrowX
  have hygienicB : Hygienic b := hygienic b (Multiset.mem_cons_self _ _)
  have simulate : ∀ b' (inside : b' ∈ bs.filter (fun b => Solvable b.store)),
      ∃ sa : HostState S × ℕ, Fires N P x.2.1 sa.1 ∧ Represents N P w'.scope b' sa.1 sa.2 ∧ ArrowBranch b' := by
    intro b' inside
    obtain ⟨child, liveChild⟩ := Multiset.mem_filter.mp inside
    obtain ⟨s', a', fires, rep', arrow'⟩ :=
      simulation_arrows N arrowP move repX arrowX hygienicB child liveChild
    exact ⟨(s', a'), fires, rep', arrow'⟩
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
    · obtain ⟨repY, arrowY⟩ := frontier.represents y (by rw [split]; exact Multiset.mem_cons_of_mem old)
      exact ⟨repY.mono N (Move.scope_le move), arrowY⟩
  · intro y member
    obtain ⟨⟨b', inside⟩, _, rfl⟩ := Multiset.mem_map.mp member
    exact (Classical.choose_spec (simulate b' inside)).1

variable (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **The hygiene hypothesis**, on the source alone: every alternative of every configuration that a
run reaches from the query is hygienic. -/
def ReachableHygienic (P : SourceLanguage.Program κ Γ star D.Ty) (supply : ℕ → Term S Γ star) : Prop :=
  ∀ C, Runs D P supply (Config.initial spaces q) C → ∀ b ∈ C.branches, Hygienic b

omit spaces q in
/-- A step of an alternative of the first fragment makes alternatives of the first fragment. -/
theorem plain_children (plainP : PlainProgram P) {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (move : Move D P supply w b w' bs) (plain : PlainBranch b) :
    ∀ b' ∈ bs, PlainBranch b' := by
  obtain ⟨noFrames, shape⟩ := plain
  intro b' child
  cases move
  case ret K t fs ps =>
    rw [Multiset.mem_singleton] at child
    subst child
    exact ⟨noFrames, .inr ⟨t, rfl⟩⟩
  case apply K t fs ps matched =>
    obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp child)
    exact ⟨noFrames, .inl ⟨_, rfl, plainComp_mapData _ _ (plainP e eMember)⟩⟩
  case unmatched K t fs ps none =>
    rw [Multiset.mem_singleton] at child
    subst child
    exact ⟨noFrames, .inr ⟨t, rfl⟩⟩
  case choice K c d fs ps =>
    have plainCD : PlainComp c ∧ PlainComp d := plain_eval shape
    rcases Multiset.mem_cons.mp child with rfl | other
    · exact ⟨noFrames, .inl ⟨c, rfl, plainCD.1⟩⟩
    · rw [Multiset.mem_singleton] at other
      subst other
      exact ⟨noFrames, .inl ⟨d, rfl, plainCD.2⟩⟩
  case fail K fs ps =>
    simp at child
  all_goals first
    | exact False.elim (plain_eval shape)
    | (simp at noFrames)

/-- For the first fragment the hypothesis holds: every reachable alternative is of the first fragment,
so none has a pending frame. -/
theorem reachableHygienic_of_plain (plainP : PlainProgram P) (plainQ : PlainComp q) :
    ReachableHygienic spaces q P supply := by
  have plain : ∀ C', Runs D P supply (Config.initial spaces q) C' → ∀ b' ∈ C'.branches, PlainBranch b' := by
    intro C' runs'
    induction runs' with
    | refl =>
        intro b' member'
        rw [Multiset.mem_singleton.mp member']
        exact ⟨rfl, .inl ⟨q, rfl, plainQ⟩⟩
    | tail _ step ih =>
        obtain ⟨w, w', b₀, rest, bs, _, move⟩ := step
        intro b' member'
        rcases Multiset.mem_add.mp member' with made | kept
        · exact plain_children plainP move (ih b₀ (Multiset.mem_cons_self _ _)) b' made
        · exact ih b' (Multiset.mem_cons_of_mem kept)
  intro C runs b member
  exact hygienic_of_plain (plain C runs b member)

/-- The start's frontier for the fragment with arrows. -/
theorem arrowFrontier_initial (arrowQ : ArrowComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    ArrowFrontier N P (Config.initial spaces q) {(initialBranch q, start N P q, P.equations.length)} := by
  refine ⟨?_, ?_⟩
  · change Multiset.map Prod.fst {(initialBranch q, start N P q, P.equations.length)} =
      Multiset.filter _ {initialBranch q}
    rw [Multiset.filter_singleton,
      if_pos (show Solvable (initialBranch (Ty := D.Ty) q).store from initial_live)]
    rfl
  · intro x member
    rw [Multiset.mem_singleton.mp member]
    exact ⟨start_represents N P q unopened, trivial, .inl ⟨q, rfl, arrowQ⟩⟩

/-- **Every source run is followed by runs of the step**, for the fragment with arrows, given hygiene. -/
theorem arrow_runs_forward_of_hygienic (arrowP : ArrowProgram P) (arrowQ : ArrowComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (hygiene : ReachableHygienic spaces q P supply) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L, ArrowFrontier N P C L ∧ ∀ x ∈ L, Relation.ReflTransGen (Fires N P) (start N P q) x.2.1 := by
  induction runs with
  | refl =>
      refine ⟨_, arrowFrontier_initial N spaces q arrowQ unopened, ?_⟩
      intro x member
      rw [Multiset.mem_singleton.mp member]
  | tail runs step ih =>
      obtain ⟨L, frontier, reached⟩ := ih
      obtain ⟨L', frontier', x, rest, new, split, rfl, fires⟩ :=
        arrowFrontier_step N arrowP frontier (hygiene _ runs) step
      refine ⟨_, frontier', ?_⟩
      intro y member
      rcases Multiset.mem_add.mp member with fresh | old
      · exact (reached x (by rw [split]; exact Multiset.mem_cons_self _ _)).tail (fires y fresh)
      · exact reached y (by rw [split]; exact Multiset.mem_cons_of_mem old)

/-- **Every run of the step is a source run**, for the fragment with arrows, given hygiene. -/
theorem arrow_runs_reflected_of_hygienic (arrowP : ArrowProgram P) (arrowQ : ArrowComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (hygiene : ReachableHygienic spaces q P supply) {s : HostState S}
    (run : Relation.ReflTransGen (Fires N P) (start N P q) s) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Represents N P C.world.scope b s a ∧ ArrowBranch b := by
  induction run with
  | refl =>
      exact ⟨_, initialBranch q, _, .refl, Multiset.mem_singleton_self _,
        start_represents N P q unopened, trivial, .inl ⟨q, rfl, arrowQ⟩⟩
  | tail _ fires ih =>
      obtain ⟨C, b, a, runs, member, rep, arrow⟩ := ih
      obtain ⟨w', bs, b', a', move, child, rep', arrow'⟩ :=
        reflection_arrows N (supply := supply) arrowP rep arrow (hygiene C runs b member) fires
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      refine ⟨⟨w', bs + rest⟩, b', a', runs.tail ?_, Multiset.mem_add.mpr (.inl child), rep', arrow'⟩
      obtain ⟨world, branches⟩ := C
      simp only at split
      subst split
      exact .move world w' b rest bs (live_of_fires N rep fires) move

#print axioms arrowFrontier_answers
#print axioms arrowFrontier_step
#print axioms reachableHygienic_of_plain
#print axioms arrow_runs_forward_of_hygienic
#print axioms arrow_runs_reflected_of_hygienic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
