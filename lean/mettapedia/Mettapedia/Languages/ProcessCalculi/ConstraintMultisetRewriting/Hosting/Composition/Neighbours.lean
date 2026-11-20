import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Beside
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Sets

/-!
# Which neighbours a hosted program survives

A neighbour puts **rows** and **knowledge** into the state and **rules** into the program. The run
correspondence of the hosted program, from a start that represents the query's alternative beside the
neighbour's rows (`Beside`), is unchanged under the following conditions, each with the control that
fails exactly it (`Composition.Controls`). Condition 1 is used by both directions, conditions 2 and 3
by one direction each, and condition 4 by the reflected direction.

**Rows and knowledge.**

1. *The knowledge says nothing more of the hosted rows than the alternative's store* (the clause
   `Beside.hosted`: under the whole knowledge, the alternative's row reads exactly as the alternative,
   and each equation row reads exactly as the instances of its equation's left side, each of them
   together with every reading of the alternative's row). Used by both directions. That the knowledge
   has a solution together with the hosted state's is necessary (`Controls.knowledge_switches_off`:
   without one, no firing) and does not keep the query: knowledge that says more of the alternative's
   unknown makes the state represent an instance of the query, with the source's answers of that
   instance (`Controls.knowledge_changes_answer`, `Composition.Knowledge.constrained_is_instance`,
   `Composition.Knowledge.constrained_answers`); knowledge of an equation row's private unknown adds an
   answer the source never gives (`Composition.Knowledge.RowName.extra_answer`). The clause is
   sufficient and not necessary (`Composition.Knowledge.Discard.discarded_name_same_answers`); the
   representation depends only on the joint readings of the present rows
   (`Composition.Knowledge.represents_of_same_joint_readings`).
2. *No other row matches a call that no equation matches* (`NoMatchingRow`), asked where a run makes
   such a call. Used by the forward direction only: `runs_forward_beside`, from rows that never read as
   equation rows; `runs_forward_beside_of_matched`, from **no condition on rows at all** when no
   reachable call is unmatched (`NoUnmatchedCall`). Control: `Controls.neighbour_stuck`.
3. *No other row reads as an alternative's row* (`NeverReads (IsAlternative N)`). Used by the reflected
   direction only: `runs_reflected_beside`. Control: `Controls.alternative_row_answers`.

With 1, 2 (in the form: no other row reads as an equation row; or no reachable unmatched call) and 3
the answers the step shows from the start, as a set, are the source's (`answers_beside`,
`answers_beside_of_matched`). With 1 and 2 the answers of every configuration a
source run reaches, as a bag, are those of a frontier reached by the step beside the rows
(`besideFrontier_answers`); the frontier holds one state for each live alternative, so its
multiplicities are the source's.

**Rules.** The step of a union of programs is the union of their steps (`firesIn_union`): the rules of a
neighbour add firings and remove none, and a firing of the translated program is admitted or refused
whatever other rules there are. So the neighbour's rules matter only through what their own firings do
to the state:

4. *A firing of the neighbour is apart from the hosted rows* (`Apart`): it takes none of them, and
   every solution of the knowledge extends to a solution of its information that reads them alike.
   Then the state it makes represents the same alternative beside the rows it leaves and makes
   (`beside_after_other`): for the reflected direction it is a silent step. The forward direction after
   it needs more: a rule that makes the row `eqn($T)` from nothing is apart and switches the hosted
   program off (`Composition.NeighbourControls.switched_off`); the condition for both directions is
   `Composition.AlongRuns.DisciplinedBothWays`. A firing that takes and reads no row at all is apart
   (`apart_of_no_selection`, by `RuleSyntax.information_amalgamates`). **Reading is not taking**: one
   firing that reads the equation row is apart and leaves the hosted program's answers the source's
   (`Controls.read_apart`, `Controls.reading_keeps`), and the rule that takes it does not
   (`Controls.rule_takes_row`). A rule that takes none and tells more of one changes the answer too
   (`Controls.pin_changes_answer`): both clauses of `Apart` have their control. Whether all the firings
   of a reading rule are apart depends on its pattern: a rule that reads any row by one unknown is
   disciplined (`Composition.Readers.copy_disciplined`); the rule `Controls.readEqn` is not
   (`Composition.Readers.Flex.readEqn_not_disciplined`), and it is disciplined along the runs from the
   start of every query (`Composition.ReadersAlong.readEqn_bothWays_along`).

`runs_reflected_neighbour`, the reflected direction: every run of the union of the translated program
with a neighbour's rules whose firings are apart and make no row that reads as an alternative's row
(`Disciplined`, asked at every state that represents an alternative beside such rows) reaches a state
that represents, beside some rows, an alternative of a configuration a source run reaches. An instance
of all hypotheses together: the start with one more row (`startWith`, `startWith_beside`,
`outsideRow_never`) and the rule that makes such a row from nothing (`spawnRule`, `spawn_disciplined`),
which fires wherever the knowledge has a solution (`spawn_fires`). Both directions beside a neighbour's
rules, and the conditions asked along the runs, are in `Composition.AlongRuns`.

The frontier of a configuration for any invariant between alternatives and states is `FrontierOf`, and
`frontierOf_step` moves it by one source step given the simulation of one move.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-! ## Frontiers for an invariant -/

section Frontiers

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  {St : Type*}

/-- **A frontier of a configuration for an invariant**: for each live alternative, a state related to
it at the configuration's scope. -/
structure FrontierOf (Inv : ℕ → Branch κ Γ star D.Ty → St → Prop) (C : Config κ Γ star D.Ty)
    (L : Multiset (Branch κ Γ star D.Ty × St)) : Prop where
  branches : L.map Prod.fst = C.branches.filter (fun b => Solvable b.store)
  holds : ∀ x ∈ L, Inv C.world.scope x.1 x.2

/-- **A source step moves a frontier**: the state of the alternative that moves is replaced by one
state per live alternative the move makes, each related to it by `r`, given the simulation of one
move of a live alternative of the configuration. -/
theorem frontierOf_step {Inv : ℕ → Branch κ Γ star D.Ty → St → Prop} {r : St → St → Prop}
    (mono : ∀ {n n' : ℕ} {b : Branch κ Γ star D.Ty} {x : St}, n ≤ n' → Inv n b x → Inv n' b x)
    {C C' : Config κ Γ star D.Ty} {L : Multiset (Branch κ Γ star D.Ty × St)} (frontier : FrontierOf Inv C L)
    (step : SourceLanguage.Step D P supply C C')
    (simulate : ∀ {v' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)},
      Move D P supply C.world b v' bs → b ∈ C.branches → Solvable b.store → ∀ {x : St},
        Inv C.world.scope b x → ∀ {b' : Branch κ Γ star D.Ty}, b' ∈ bs → Solvable b'.store →
          ∃ x', r x x' ∧ Inv v'.scope b' x') :
    ∃ L', FrontierOf Inv C' L' ∧ ∃ x rest new, L = x ::ₘ rest ∧ L' = new + rest ∧ ∀ y ∈ new, r x.2 y.2 := by
  obtain ⟨branches, holds⟩ := frontier
  obtain ⟨w, w', b, rest, bs, live, move⟩ := step
  have bInside : b ∈ L.map Prod.fst := by
    rw [branches]
    exact Multiset.mem_filter.mpr ⟨Multiset.mem_cons_self _ _, live⟩
  obtain ⟨x, xMember, xb⟩ := Multiset.mem_map.mp bInside
  obtain ⟨L₀, split⟩ := Multiset.exists_cons_of_mem xMember
  have restBranches : L₀.map Prod.fst = rest.filter (fun b => Solvable b.store) := by
    have whole := branches
    rw [split, Multiset.map_cons, xb] at whole
    change _ = Multiset.filter _ (b ::ₘ rest) at whole
    rw [Multiset.filter_cons_of_pos (p := fun b => Solvable b.store) rest live] at whole
    exact (Multiset.cons_inj_right b).mp whole
  have invX := holds x xMember
  rw [xb] at invX
  have sim : ∀ b' (_ : b' ∈ bs.filter (fun b => Solvable b.store)), ∃ x' : St, r x.2 x' ∧ Inv w'.scope b' x' := by
    intro b' inside
    obtain ⟨child, liveChild⟩ := Multiset.mem_filter.mp inside
    exact simulate move (Multiset.mem_cons_self _ _) live invX child liveChild
  let new : Multiset (Branch κ Γ star D.Ty × St) :=
    (bs.filter (fun b => Solvable b.store)).attach.map fun b' => (b'.1, Classical.choose (sim b'.1 b'.2))
  have newBranches : new.map Prod.fst = bs.filter (fun b => Solvable b.store) := by
    simp only [new, Multiset.map_map]
    exact Multiset.attach_map_val _
  refine ⟨new + L₀, ⟨?_, ?_⟩, x, L₀, new, split, rfl, ?_⟩
  · rw [Multiset.map_add, newBranches, restBranches]
    exact (Multiset.filter_add _ _ _).symm
  · intro y member
    rcases Multiset.mem_add.mp member with fresh | old
    · obtain ⟨⟨b', inside⟩, _, rfl⟩ := Multiset.mem_map.mp fresh
      exact (Classical.choose_spec (sim b' inside)).2
    · exact mono (Move.scope_le move) (holds y (by rw [split]; exact Multiset.mem_cons_of_mem old))
  · intro y member
    obtain ⟨⟨b', inside⟩, _, rfl⟩ := Multiset.mem_map.mp member
    exact (Classical.choose_spec (sim b' inside)).1

end Frontiers

/-! ## Whole runs beside other rows -/

section Runs

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- The invariant of a frontier beside the rows `others`: the state with its alternative's row
represents the alternative beside them, and the rows never read as `shape`. -/
def BesideAt (P : SourceLanguage.Program κ Γ star D.Ty) (others : Finset ℕ)
    (shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop) (n : ℕ)
    (b : Branch κ Γ star D.Ty) (x : HostState S × ℕ) : Prop :=
  Beside N P n b x.1 x.2 others ∧ ArrowBranch b ∧ NeverReads shape x.1 others

/-- **Every source run is followed by runs of the step beside other rows**, given, at each call that
no equation matches, that no other row matches it (`rows`, which may use that the rows never read as
`shape`). -/
theorem runs_forward_beside_of
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {others : Finset ℕ}
    {shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop}
    (rows : ∀ {C : Config κ Γ star D.Ty} {b : Branch κ Γ star D.Ty} {w : HostState S} {a : ℕ}
      {t : Data κ Γ star}, Runs D P supply (Config.initial spaces q) C → b ∈ C.branches →
      Solvable b.store → b.focus = .eval (.apply t) →
      (∀ e ∈ P.equations, ¬ Solvable (b.store ++ [(instantiate (copyAt κ C.world.scope) e.lhs, t)])) →
      NeverReads shape w others → NoMatchingRow N w a others)
    {w₀ : HostState S} {a₀ : ℕ} (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    (quiet : NeverReads shape w₀ others) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L, FrontierOf (BesideAt N P others shape) C L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N P) w₀ x.2.1 := by
  induction runs with
  | refl =>
      refine ⟨{(initialBranch q, (w₀, a₀))}, ⟨?_, ?_⟩, ?_⟩
      · change Multiset.map Prod.fst {(initialBranch q, (w₀, a₀))} = Multiset.filter _ {initialBranch q}
        rw [Multiset.filter_singleton,
          if_pos (show Solvable (initialBranch (Ty := D.Ty) q).store from initial_live)]
        rfl
      · intro x member
        rw [Multiset.mem_singleton.mp member]
        exact ⟨start, ⟨trivial, .inl ⟨q, rfl, arrowQ⟩⟩, quiet⟩
      · intro x member
        rw [Multiset.mem_singleton.mp member]
  | tail runs step ih =>
      obtain ⟨L, frontier, reached⟩ := ih
      have hygiene := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ _ runs
      obtain ⟨L', frontier', x, rest, new, split, rfl, fires⟩ :=
        frontierOf_step (r := fun x y : HostState S × ℕ => Fires N P x.1 y.1)
          (fun le inv => ⟨inv.1.mono N le, inv.2⟩) frontier step
          (fun {v' b bs} move member live {x} inv {b'} child liveChild => by
            obtain ⟨beside, arrow, never⟩ := inv
            obtain ⟨w', a', fired, beside', kept, arrow'⟩ :=
              simulation_beside N (fun e inside => (equations e inside).2.2) move beside arrow
                (hygiene b member) (fun t focus none => rows runs member live focus none never) child liveChild
            exact ⟨(w', a'), fired, beside', arrow', kept shape never⟩)
      refine ⟨_, frontier', ?_⟩
      intro y member
      rcases Multiset.mem_add.mp member with fresh | old
      · exact (reached x (by rw [split]; exact Multiset.mem_cons_self _ _)).tail (fires y fresh)
      · exact reached y (by rw [split]; exact Multiset.mem_cons_of_mem old)

/-- **Every source run is followed by runs of the step beside rows that never read as equation
rows.** -/
theorem runs_forward_beside
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {others : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    (quiet : NeverReads (IsEquationRow N) w₀ others) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L, FrontierOf (BesideAt N P others (IsEquationRow N)) C L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N P) w₀ x.2.1 :=
  runs_forward_beside_of N spaces q equations qScoped qDistinct arrowQ
    (fun _ _ _ _ _ never => noMatchingRow_of_neverReads N never) start quiet runs

/-- **Every source run is followed by runs of the step beside any rows at all, when no reachable call
is unmatched**: the hosted runs then fire only positive rules, and no condition on the other rows is
asked. -/
theorem runs_forward_beside_of_matched
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) (matched : NoUnmatchedCall D P supply spaces q) {others : Finset ℕ}
    {w₀ : HostState S} {a₀ : ℕ} (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    {C : Config κ Γ star D.Ty} (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ L, FrontierOf (BesideAt N P others (fun _ _ => False)) C L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N P) w₀ x.2.1 :=
  runs_forward_beside_of N spaces q equations qScoped qDistinct arrowQ
    (fun {C b _ _ t} reached member live focus none _ => by
      obtain ⟨e, eMember, solvable⟩ := matched C reached b member live t focus
      exact absurd solvable (none e eMember))
    start (fun _ _ _ _ _ impossible => impossible) runs

/-- **Every run of the step beside rows that never read as alternatives' rows is a source run**: it
reaches a state that represents, beside the same rows, an alternative of a configuration a source run
reaches. -/
theorem runs_reflected_beside
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {others : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    (quiet : NeverReads (IsAlternative N) w₀ others) {w : HostState S}
    (run : Relation.ReflTransGen (Fires N P) w₀ w) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Beside N P C.world.scope b w a others ∧ NeverReads (IsAlternative N) w others ∧ ArrowBranch b := by
  induction run with
  | refl =>
      exact ⟨_, initialBranch q, a₀, .refl, Multiset.mem_singleton_self _, start, quiet, trivial,
        .inl ⟨q, rfl, arrowQ⟩⟩
  | tail _ fires ih =>
      obtain ⟨C, b, a, runs, member, beside, quiet', arrow⟩ := ih
      have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
      obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
        reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside quiet' arrow
          hygienic fires
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      refine ⟨⟨v', bs + rest⟩, b', a', runs.tail ?_, Multiset.mem_add.mpr (.inl child), beside',
        kept _ quiet', arrow'⟩
      obtain ⟨world, branches⟩ := C
      simp only at split
      subst split
      exact .move world v' b rest bs (live_beside N beside fires) move

end Runs

/-! ## The answers beside other rows, as a set -/

section Answers

/-- **The answers the step shows from a state**: the answers of finished present rows of the states
that runs of the translated program reach from it. -/
def stepAnswersFrom {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (w₀ : HostState S) :
    Set (Set (Term S Γ star)) :=
  {A | ∃ s a, Relation.ReflTransGen (Fires N P) w₀ s ∧ a ∈ s.present ∧ StateFinished N s a ∧
    stateAnswer N s a = A}

theorem stepAnswersFrom_start {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    stepAnswersFrom N P (start N P q) = Answers.stepAnswers N P q :=
  rfl

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- A finished present row of a state beside rows that never read as alternatives' rows is the
alternative's row. -/
theorem finished_row_beside {n : ℕ} {b : Branch κ Γ star D.Ty} {s : HostState S} {a a' : ℕ}
    {others : Finset ℕ} (beside : Beside N P n b s a others) (quiet : NeverReads (IsAlternative N) s others)
    (present : a' ∈ s.present) (finished : StateFinished N s a') : a' = a := by
  rw [beside.present, Finset.mem_union, Finset.mem_insert, Finset.mem_range] at present
  obtain ⟨⟨B, r, reads⟩, shape⟩ := finished
  obtain ⟨v, rfl⟩ := shape B r reads
  obtain ⟨σ, known, read⟩ := reads
  rcases present with (same | small) | other
  · exact same
  · obtain ⟨θ, row⟩ := beside.hosted.rows B σ known a' small
    exact absurd (N.tag_eq (observe_injective (read.symm.trans row))) (by decide)
  · exact absurd ⟨_, _, read⟩ (quiet a' other B σ known)

/-- **The answers of a configuration, as a bag, are those of its frontier beside other rows.** The
frontier holds one state for each live alternative: its multiplicities are the source's. -/
theorem besideFrontier_answers {others : Finset ℕ}
    {shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop} {C : Config κ Γ star D.Ty}
    {L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ)}
    (frontier : FrontierOf (BesideAt N P others shape) C L) :
    C.answers (D := D) = frontierAnswers N L := by
  have restricted : ArrowFrontier N P C
      (L.map fun x => (x.1, restrict x.2.1 (hostedRows P x.2.2), x.2.2)) := by
    refine ⟨?_, ?_⟩
    · rw [Multiset.map_map]
      exact frontier.branches
    · intro x member
      obtain ⟨y, inside, rfl⟩ := Multiset.mem_map.mp member
      obtain ⟨beside, arrow, _⟩ := frontier.holds y inside
      exact ⟨beside.hosted, arrow⟩
  rw [arrowFrontier_answers N restricted]
  simp only [frontierAnswers, Multiset.map_map, Multiset.filter_map]
  rfl

/-- The two halves of `answers_beside`, from a forward theorem for some shape. -/
theorem answers_beside_of
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {others : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    (quiet : NeverReads (IsAlternative N) w₀ others)
    {shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop}
    (forward : ∀ {C : Config κ Γ star D.Ty}, Runs D P supply (Config.initial spaces q) C →
      ∃ L, FrontierOf (BesideAt N P others shape) C L ∧
        ∀ x ∈ L, Relation.ReflTransGen (Fires N P) w₀ x.2.1) :
    stepAnswersFrom N P w₀ = Answers.sourceAnswers D P supply spaces q := by
  ext A
  constructor
  · rintro ⟨s, a, run, present, fin, rfl⟩
    obtain ⟨C, b, a', runs, member, beside, quiet', _⟩ :=
      runs_reflected_beside N (supply := supply) spaces q equations qScoped qDistinct arrowQ start quiet run
    obtain rfl := finished_row_beside N beside quiet' present fin
    exact ⟨C, runs, Answers.answer_mem N (s := restrict s (hostedRows P a)) member beside.hosted fin⟩
  · rintro ⟨C, runs, member⟩
    unfold Config.answers at member
    obtain ⟨b, inside, rfl⟩ := Multiset.mem_map.mp member
    obtain ⟨bMember, finished, live⟩ := Multiset.mem_filter.mp inside
    obtain ⟨L, frontier, reached⟩ := forward runs
    have bInside : b ∈ L.map Prod.fst := by
      rw [frontier.branches]
      exact Multiset.mem_filter.mpr ⟨bMember, live⟩
    obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp bInside
    obtain ⟨beside, _, _⟩ := frontier.holds x xMember
    exact ⟨x.2.1, x.2.2, reached x xMember, beside.row_present N,
      (finished_iff N (s := restrict x.2.1 (hostedRows P x.2.2)) beside.hosted).mp ⟨finished, live⟩,
      answer_eq N (s := restrict x.2.1 (hostedRows P x.2.2)) beside.hosted finished⟩

/-- **The answers of a hosted program beside other rows, as a set, are the source's**, when the
knowledge keeps the start's representation and the other rows never read as alternatives' rows or as
equation rows. -/
theorem answers_beside
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {others : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    (noAlternative : NeverReads (IsAlternative N) w₀ others)
    (noEquationRow : NeverReads (IsEquationRow N) w₀ others) :
    stepAnswersFrom N P w₀ = Answers.sourceAnswers D P supply spaces q :=
  answers_beside_of N spaces q equations qScoped qDistinct arrowQ start noAlternative
    (fun runs => runs_forward_beside N spaces q equations qScoped qDistinct arrowQ start noEquationRow runs)

/-- **For a program and query with no reachable unmatched call, the answers beside other rows, as a
set, are the source's whatever equation rows the neighbour adds**: only that no other row reads as an
alternative's row is asked. -/
theorem answers_beside_of_matched
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) (matched : NoUnmatchedCall D P supply spaces q) {others : Finset ℕ}
    {w₀ : HostState S} {a₀ : ℕ} (start : Beside N P 0 (initialBranch q) w₀ a₀ others)
    (noAlternative : NeverReads (IsAlternative N) w₀ others) :
    stepAnswersFrom N P w₀ = Answers.sourceAnswers D P supply spaces q :=
  answers_beside_of N spaces q equations qScoped qDistinct arrowQ start noAlternative
    (fun runs => runs_forward_beside_of_matched N spaces q equations qScoped qDistinct arrowQ matched start runs)

end Answers

/-! ## A start with one more row -/

section Start

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **The representation depends only on the labels of the present rows.** -/
theorem represents_relabel {n : ℕ} {b : Branch κ Γ star Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) (label' : ℕ → Observation S s.frame.arity)
    (same : ∀ o ∈ s.present, label' o = s.label o) :
    Represents N P n b ⟨s.frame, s.knowledge, s.present, label'⟩ a := by
  have aPresent : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have rowPresent : ∀ i, i < P.equations.length → i ∈ s.present := fun i small => by
    rw [rep.present]
    exact Finset.mem_insert_of_mem (Finset.mem_range.mpr small)
  refine ⟨rep.notRow, rep.present, ?_, ?_, ?_, rep.fresh, rep.noPending⟩
  · intro B r
    show (∃ σ : Assignment s.frame.arity B.arity, (Interface.Frames.contextual S).Models σ s.knowledge ∧
      instantiateObservation σ (label' a) = r) ↔ _
    rw [same a aPresent]
    exact rep.reads B r
  · intro B σ solved i hi
    show ∃ θ : Assignment (fam κ) B.arity, instantiateObservation σ (label' i) = _
    rw [same i (rowPresent i hi)]
    exact rep.rows B σ solved i hi
  · intro B σ solved i hi θ
    show ∃ σ' : Assignment s.frame.arity B.arity, (Interface.Frames.contextual S).Models σ' s.knowledge ∧
      instantiateObservation σ' (label' a) = instantiateObservation σ (label' a) ∧
      instantiateObservation σ' (label' i) = _
    rw [same a aPresent, same i (rowPresent i hi)]
    exact rep.independent B σ solved i hi θ

/-- **The representation does not depend on the identity of the alternative's row.** -/
theorem represents_rename {n : ℕ} {b : Branch κ Γ star Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) {a' : ℕ} (notRow : P.equations.length ≤ a') :
    Represents N P n b ⟨s.frame, s.knowledge, insert a' (Finset.range P.equations.length),
      Function.update s.label a' (s.label a)⟩ a' := by
  have other : ∀ i, i < P.equations.length → i ≠ a' := fun i small same => by omega
  refine ⟨notRow, rfl, ?_, ?_, ?_, rep.fresh, rep.noPending⟩
  · intro B r
    show (∃ σ : Assignment s.frame.arity B.arity, (Interface.Frames.contextual S).Models σ s.knowledge ∧
      instantiateObservation σ (Function.update s.label a' (s.label a) a') = r) ↔ _
    rw [Function.update_self]
    exact rep.reads B r
  · intro B σ solved i hi
    show ∃ θ : Assignment (fam κ) B.arity,
      instantiateObservation σ (Function.update s.label a' (s.label a) i) = _
    rw [Function.update_of_ne (other i hi)]
    exact rep.rows B σ solved i hi
  · intro B σ solved i hi θ
    show ∃ σ' : Assignment s.frame.arity B.arity, (Interface.Frames.contextual S).Models σ' s.knowledge ∧
      instantiateObservation σ' (Function.update s.label a' (s.label a) a') =
        instantiateObservation σ (Function.update s.label a' (s.label a) a') ∧
      instantiateObservation σ' (Function.update s.label a' (s.label a) i) = _
    rw [Function.update_self, Function.update_of_ne (other i hi)]
    exact rep.independent B σ solved i hi θ

/-- **The start of a query with one more row**, at the identity after the alternative's. -/
def startWith (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty)
    (row : Observation S (startArity κ)) : HostState S :=
  ⟨startFrame κ, [], hostedRows P P.equations.length ∪ {P.equations.length + 1},
    Function.update (startLabel N P q) (P.equations.length + 1) row⟩

/-- **The start with one more row represents the query's initial alternative beside that row.** -/
theorem startWith_beside (q : Comp κ Γ star Ty) (row : Observation S (startArity κ))
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    Beside N P 0 (initialBranch q) (startWith N P q row) P.equations.length {P.equations.length + 1} := by
  have other : ∀ o ∈ hostedRows P P.equations.length, o ≠ P.equations.length + 1 := by
    intro o inside
    rw [Finset.mem_insert, Finset.mem_range] at inside
    omega
  refine ⟨?_, rfl, ?_⟩
  · exact represents_relabel N (start_represents N P q unopened) _
      (fun o inside => Function.update_of_ne (other o inside) _ _)
  · rw [Finset.disjoint_singleton_right]
    exact fun inside => other _ inside rfl

/-- A row that is neither an alternative's row nor an equation row: the node `outside`. -/
def outsideRow : Observation S (startArity κ) := observe (N.node .outside ![])

/-- **The row `outside` never reads as an alternative's row or as an equation row.** -/
theorem outsideRow_never (q : Comp κ Γ star Ty) :
    NeverReads (IsAlternative N) (startWith N P q (outsideRow N)) {P.equations.length + 1} ∧
    NeverReads (IsEquationRow N) (startWith N P q (outsideRow N)) {P.equations.length + 1} := by
  have label : ∀ {B : Interface.Frames.Frame S} (σ : Assignment (startArity κ) B.arity),
      instantiateObservation σ ((startWith N P q (outsideRow N)).label (P.equations.length + 1)) =
        observe (N.node .outside ![]) := by
    intro B σ
    show instantiateObservation σ (Function.update (startLabel N P q) (P.equations.length + 1) (outsideRow N)
      (P.equations.length + 1)) = _
    rw [Function.update_self]
    exact congrArg observe (instantiate_outside N σ)
  constructor
  · intro o inside B σ _ reads
    rw [Finset.mem_singleton.mp inside, label σ] at reads
    obtain ⟨x, y, same⟩ := reads
    exact absurd (N.tag_eq (observe_injective same)) (by decide)
  · intro o inside B σ _ reads
    rw [Finset.mem_singleton.mp inside, label σ] at reads
    obtain ⟨x, same⟩ := reads
    exact absurd (N.tag_eq (observe_injective same)) (by decide)

end Start

/-! ## The rules of a neighbour -/

section OtherRules

/-- **One firing of a program** at the contextual frames. -/
def FiresIn (Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (s s' : HostState S) : Prop :=
  ∃ f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame,
    f.Admits (Interface.Frames.contextual S) s ∧ f.result (Interface.Frames.contextual S) s = s'

/-- **The step of a union of programs is the union of their steps**: rules added to a program add
firings and remove none. -/
theorem firesIn_union (Prog₁ Prog₂ : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (s s' : HostState S) :
    FiresIn (Prog₁ ∪ Prog₂) s s' ↔ FiresIn Prog₁ s s' ∨ FiresIn Prog₂ s s' := by
  constructor
  · rintro ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, result⟩
    rcases member with left | right
    · exact .inl ⟨⟨rule, left, ext, opening, selection, seen⟩, admitted, result⟩
    · exact .inr ⟨⟨rule, right, ext, opening, selection, seen⟩, admitted, result⟩
  · rintro (⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, result⟩ |
      ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, result⟩)
    · exact ⟨⟨rule, .inl member, ext, opening, selection, seen⟩, admitted, result⟩
    · exact ⟨⟨rule, .inr member, ext, opening, selection, seen⟩, admitted, result⟩

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- The other rows are present. -/
theorem others_sub {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) : others ⊆ w.present := by
  rw [beside.present]
  exact Finset.subset_union_right

/-- The firings of the translated program are the firings of its rules. -/
theorem fires_iff_firesIn (s s' : HostState S) : Fires N P s s' ↔ FiresIn (translate N P) s s' :=
  Iff.rfl

/-- **A firing apart from the hosted rows**: it takes none of them, and every solution of the
knowledge extends to a solution of its information that reads them alike. It may read them. -/
structure Apart (P : SourceLanguage.Program κ Γ star Ty) (a : ℕ) (w : HostState S)
    {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame) : Prop where
  taken : ∀ o ∈ f.selection.taken, o ∉ hostedRows P a
  conservative : ∀ (B : Interface.Frames.Frame S) (g : Assignment w.frame.arity B.arity),
    (Interface.Frames.contextual S).Models g w.knowledge →
      ∃ u : Assignment ((RuleSyntax.Contextual.declarations S).target f.ext).arity B.arity,
        (Interface.Frames.contextual S).Models u (f.information (Interface.Frames.contextual S) w) ∧
        ∀ o ∈ hostedRows P a, instantiateObservation u (f.row (Interface.Frames.contextual S) w o) =
          instantiateObservation g (w.label o)

/-- **A firing that takes and reads no row is apart from the hosted rows**, when its rule's tells have
a solution into every frame: it adds no relation between its new unknowns and what the state mentions
(`RuleSyntax.information_amalgamates`). -/
theorem apart_of_no_selection {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) w)
    (noTake : f.selection.taken = []) (noRead : f.selection.read = [])
    (tells : ∀ B : Interface.Frames.Frame S, ∃ h : Assignment f.rule.locals.arity B.arity,
      (Interface.Frames.contextual S).Models h f.rule.body.tell) : Apart P a w f := by
  refine ⟨?_, ?_⟩
  · intro o inside
    rw [noTake] at inside
    cases inside
  · intro B g known
    obtain ⟨h, told⟩ := tells B
    obtain ⟨u, solved, onState, _⟩ :=
      RuleSyntax.information_amalgamates (X := Interface.Frames.contextual S) f admitted.1.1 noTake noRead g h
        known told
    exact ⟨u, solved, fun o inside => onState _ (.inr (.inr ⟨o, beside.rows_sub N inside, rfl⟩))⟩

/-- **A firing apart from the hosted rows is silent for the reflected direction**: the state it makes
represents the same alternative, beside the rows it leaves and the rows it makes. For the forward
direction the rows it makes must also not match an unmatched call
(`Composition.NeighbourControls.switched_off`). -/
theorem beside_after_other {n : ℕ} {b : Branch κ Γ star Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (beside : Beside N P n b w a others) {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) w) (apart : Apart P a w f) :
    Beside N P n b (f.result (Interface.Frames.contextual S) w) a
      (fire others (f.selection.commit (T := Unit))) := by
  have notMade : ∀ o ∈ hostedRows P a, o ∉ f.selection.made := by
    intro o inside isMade
    exact Finset.disjoint_left.mp admitted.2.1.fresh (List.mem_toFinset.mpr isMade) (beside.rows_sub N inside)
  have aIn : a ∈ hostedRows P a := Finset.mem_insert_self _ _
  have rowIn : ∀ i, i < P.equations.length → i ∈ hostedRows P a := fun i small =>
    Finset.mem_insert_of_mem (Finset.mem_range.mpr small)
  have rep := beside.hosted
  refine ⟨⟨rep.notRow, rfl, ?_, ?_, ?_, rep.fresh, rep.noPending⟩, ?_, ?_⟩
  · intro B r
    constructor
    · rintro ⟨σ, solved, rfl⟩
      have known := RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved
      apply (rep.reads B _).mp
      refine ⟨_, known, ?_⟩
      show instantiateObservation _ (w.label a) =
        instantiateObservation σ ((f.result (Interface.Frames.contextual S) w).label a)
      rw [RuleSyntax.Firing.result_label_other f (notMade a aIn)]
      exact (instantiateObservation_comp _ _ _).symm
    · intro reads
      obtain ⟨g, known, rfl⟩ := (rep.reads B r).mpr reads
      obtain ⟨u, solvedU, onRows⟩ := apart.conservative B g known
      refine ⟨u, solvedU, ?_⟩
      show instantiateObservation u ((f.result (Interface.Frames.contextual S) w).label a) = _
      rw [RuleSyntax.Firing.result_label_other f (notMade a aIn)]
      exact onRows a aIn
  · intro B σ solved i hi
    have known := RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved
    obtain ⟨θ, row⟩ := rep.rows B _ known i hi
    refine ⟨θ, ?_⟩
    show instantiateObservation σ ((f.result (Interface.Frames.contextual S) w).label i) = _
    rw [RuleSyntax.Firing.result_label_other f (notMade i (rowIn i hi)), ← row]
    exact instantiateObservation_comp _ _ _
  · intro B σ solved i hi θ
    have known := RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved
    obtain ⟨g', known', sameAlt, rowI⟩ := rep.independent B _ known i hi θ
    obtain ⟨u', solved', onRows⟩ := apart.conservative B g' known'
    refine ⟨u', solved', ?_, ?_⟩
    · show instantiateObservation u' ((f.result (Interface.Frames.contextual S) w).label a) =
        instantiateObservation σ ((f.result (Interface.Frames.contextual S) w).label a)
      rw [RuleSyntax.Firing.result_label_other f (notMade a aIn), onRows a aIn]
      exact sameAlt.trans (instantiateObservation_comp _ _ _).symm
    · show instantiateObservation u' ((f.result (Interface.Frames.contextual S) w).label i) = _
      rw [RuleSyntax.Firing.result_label_other f (notMade i (rowIn i hi)), onRows i (rowIn i hi)]
      exact rowI
  · change fire w.present (f.selection.commit (T := Unit)) = _
    rw [beside.present]
    ext o
    simp only [mem_fire, Finset.mem_union]
    constructor
    · rintro (⟨inH | inO, notTaken⟩ | made)
      · exact .inl inH
      · exact .inr (.inl ⟨inO, notTaken⟩)
      · exact .inr (.inr made)
    · rintro (inH | ⟨inO, notTaken⟩ | made)
      · exact .inl ⟨.inl inH, fun taken => apart.taken o (List.mem_toFinset.mp taken) inH⟩
      · exact .inl ⟨.inr inO, notTaken⟩
      · exact .inr made
  · rw [Finset.disjoint_left]
    intro o inH inside
    rcases mem_fire.mp inside with ⟨inO, _⟩ | made
    · exact Finset.disjoint_left.mp beside.apart inH inO
    · exact notMade o inH (List.mem_toFinset.mp made)

/-- **What the rows never read as, after a firing of a neighbour**: the rows that stay keep it, and it
is asked of the rows the firing makes. -/
theorem neverReads_fire {shape : ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop}
    {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w : HostState S}
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame} {others : Finset ℕ}
    (admitted : f.Admits (Interface.Frames.contextual S) w) (sub : others ⊆ w.present)
    (quiet : NeverReads shape w others)
    (made : NeverReads shape (f.result (Interface.Frames.contextual S) w) f.selection.made.toFinset) :
    NeverReads shape (f.result (Interface.Frames.contextual S) w)
      (fire others (f.selection.commit (T := Unit))) := by
  intro o inside
  rcases mem_fire.mp inside with ⟨inO, _⟩ | isMade
  · refine neverReads_after f quiet ?_ o inO
    intro o' inO' isMade
    exact Finset.disjoint_left.mp admitted.2.1.fresh (List.mem_toFinset.mpr isMade) (sub inO')
  · exact made o isMade

end OtherRules

/-! ## Runs of the union with a neighbour's rules -/

section NeighbourRuns

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **The discipline of a neighbour's rules**: at every state that represents an alternative beside
rows that never read as alternatives' rows, each of their admitted firings is apart from the hosted
rows and makes no row that reads as an alternative's row. -/
def Disciplined (P : SourceLanguage.Program κ Γ star D.Ty)
    (R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) : Prop :=
  ∀ {n : ℕ} {b : Branch κ Γ star D.Ty} {w : HostState S} {a : ℕ} {others : Finset ℕ}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) R w.frame),
    Beside N P n b w a others → NeverReads (IsAlternative N) w others →
      f.Admits (Interface.Frames.contextual S) w →
        Apart P a w f ∧
          NeverReads (IsAlternative N) (f.result (Interface.Frames.contextual S) w) f.selection.made.toFinset

/-- **Every run of the union of a translated program with a disciplined neighbour's rules is a source
run with silent steps**: it reaches a state that represents, beside some rows that never read as
alternatives' rows, an alternative of a configuration a source run reaches. A firing of the translated
program is one source step; a firing of the neighbour leaves the configuration as it is. -/
theorem runs_reflected_neighbour
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (disciplined : Disciplined N P R) {others₀ : Finset ℕ} {w₀ : HostState S} {a₀ : ℕ}
    (start : Beside N P 0 (initialBranch q) w₀ a₀ others₀)
    (quiet : NeverReads (IsAlternative N) w₀ others₀) {w : HostState S}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ R)) w₀ w) :
    ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty) (a : ℕ) (others : Finset ℕ),
      Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
        Beside N P C.world.scope b w a others ∧ NeverReads (IsAlternative N) w others ∧ ArrowBranch b := by
  induction run with
  | refl =>
      exact ⟨_, initialBranch q, a₀, others₀, .refl, Multiset.mem_singleton_self _, start, quiet, trivial,
        .inl ⟨q, rfl, arrowQ⟩⟩
  | tail _ fires ih =>
      obtain ⟨C, b, a, others, runs, member, beside, quiet', arrow⟩ := ih
      rcases (firesIn_union _ _ _ _).mp fires with hosted | ⟨f, admitted, rfl⟩
      · have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
        obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
          reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside quiet' arrow
            hygienic hosted
        obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
        refine ⟨⟨v', bs + rest⟩, b', a', others, runs.tail ?_, Multiset.mem_add.mpr (.inl child), beside',
          kept _ quiet', arrow'⟩
        obtain ⟨world, branches⟩ := C
        simp only at split
        subst split
        exact .move world v' b rest bs (live_beside N beside hosted) move
      · obtain ⟨apart, made⟩ := disciplined f beside quiet' admitted
        exact ⟨C, b, a, _, runs, member, beside_after_other N beside admitted apart,
          neverReads_fire admitted (others_sub N beside) quiet' made, arrow⟩

/-- **A rule that makes the row `outside` from nothing**: no take, no read, no tell, no check. -/
def spawnRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := ⟨Empty, fun x => x.elim⟩
  body := { take := [], read := [], tell := [], checks := [], produce := [observe (N.node .outside ![])] }
  collect := []

/-- **The spawning rule is disciplined**: each of its firings is apart from the hosted rows, and the
row it makes never reads as an alternative's row. -/
theorem spawn_disciplined : Disciplined N P ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) := by
  intro n b w a others f beside _ admitted
  have rule : f.rule = spawnRule N := f.member
  obtain ⟨rl, member, ext, opening, selection, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  have noTake : selection.taken = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  have noRead : selection.read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.1.symm
  obtain ⟨o', made⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
  refine ⟨apart_of_no_selection N beside admitted noTake noRead
    (fun B => ⟨fun x => x.elim, fun _ inside => by cases inside⟩), ?_⟩
  intro o inside B σ _ reads
  simp only at made
  rw [made, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at inside
  subst inside
  have label : (RuleSyntax.Firing.result (Interface.Frames.contextual S) w
      (⟨spawnRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) {spawnRule N} w.frame)).label o =
      instantiateObservation opening (observe (N.node .outside ![])) := by
    apply RuleSyntax.Firing.result_label_made _ shapes
    simp only [RuleSyntax.Firing.opened, RuleInstance.map, made, spawnRule, List.map_cons, List.map_nil,
      List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
    rfl
  rw [label] at reads
  obtain ⟨x, y, same⟩ := reads
  change observe (instantiate σ (instantiate opening (N.node .outside ![]))) = _ at same
  rw [instantiate_outside, instantiate_outside] at same
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

theorem enabled_make {present : Finset ℕ} {a' : ℕ} (ha' : a' ∉ present) :
    Enabled (fun _ : ℕ => ()) present ((⟨[], [], [a']⟩ : Selection ℕ).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Selection.commit]
  · simp [Selection.commit]
  · simp [Selection.commit]
  · simp [Selection.commit, ha']
  · simp [Selection.commit]

/-- **The spawning rule fires** at every state whose knowledge has a solution, so its discipline is
about firings that exist. -/
theorem spawn_fires {w : HostState S} (solvable : (Interface.Frames.contextual S).Solvable w.knowledge) :
    ∃ w', FiresIn ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) w w' := by
  obtain ⟨B, g, known⟩ := solvable
  let f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S)
      ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) w.frame :=
    RuleSyntax.Contextual.canonical (F := w.frame) (spawnRule N) (Set.mem_singleton _) ⟨[], [], [freshId w]⟩ []
  have fresh : f.Fresh (Interface.Frames.contextual S) w :=
    RuleSyntax.Contextual.canonical_fresh w (spawnRule N) (Set.mem_singleton _) _ _
  have told : (Interface.Frames.contextual S).Models (a := (spawnRule N).locals) (b := B) (fun x => x.elim)
      (spawnRule N).body.tell := by
    intro e member
    exact absurd member List.not_mem_nil
  obtain ⟨u, solved, _⟩ :=
    RuleSyntax.information_amalgamates (X := Interface.Frames.contextual S) f fresh rfl rfl g
      (fun x => x.elim) known told
  exact ⟨_, f, ⟨⟨fresh, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
    enabled_make (freshId_not_mem w), ⟨_, u, solved⟩, entails_of_no_checks rfl rfl⟩, rfl⟩

end NeighbourRuns

#print axioms spawn_fires
#print axioms frontierOf_step
#print axioms runs_forward_beside
#print axioms runs_forward_beside_of_matched
#print axioms runs_reflected_beside
#print axioms besideFrontier_answers
#print axioms answers_beside
#print axioms answers_beside_of_matched
#print axioms represents_relabel
#print axioms represents_rename
#print axioms startWith_beside
#print axioms outsideRow_never
#print axioms firesIn_union
#print axioms apart_of_no_selection
#print axioms beside_after_other
#print axioms neverReads_fire
#print axioms runs_reflected_neighbour
#print axioms spawn_disciplined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
