import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-!
# A neighbour's rules in both directions: the instance, and the control that meets one direction only

Two rules that take nothing, read nothing, tell nothing and check nothing. Each makes one row.

* **The instance.** `spawnRule` makes the row `outside`. It is disciplined for both directions, for
  every program (`spawn_both_ways`): the row never reads as an alternative's row or as an equation
  row. After it has fired at the start of the call `(g)` of the program with no equation, the
  translated program still has its firing (`spawn_keeps_call`), and such a pair of firings exists
  (`spawn_then_call`).
* **The control.** `spawnEqnRule` makes the row `eqn($T)`. It meets `Disciplined`, the condition of the
  reflected direction, for every program (`spawnEqn_disciplined`), and fails the further clause of the
  condition for both directions at the start of every query of every program
  (`spawnEqn_not_both_ways`, `spawnEqn_not_disciplinedBothWays`, `spawnEqn_not_along`): the row it
  makes reads as an equation row at every solution. At the start of the call `(g)` of the program with
  no equation it fires (`spawnFiring_admits`); at the state it makes the translated program has no
  firing (`switched_off`); from that state no run of the union of the translated program with the rule
  reaches a finished present row (`never_answers`), so the union shows no answer from it, and the
  source answers `(g)` (`answer_lost`). That state is one where the call is switched off (`Blocked`,
  `after_blocked`; the start is not: `start_not_blocked`), and it represents no alternative along the
  runs of the union (`after_not_representsAlong`).

So the condition of the reflected direction does not keep the moves of the hosted program, and the one
further clause is what does.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.NeighbourControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
open Classical

/-! ## For every program -/

section Generic

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}
  {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}

/-- The row the spawning rule makes never reads as an equation row. -/
theorem spawn_made_quiet {w : HostState S}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S)
      ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) w.frame)
    (admitted : f.Admits (Interface.Frames.contextual S) w) :
    NeverReads (IsEquationRow N) (f.result (Interface.Frames.contextual S) w) f.selection.made.toFinset := by
  have rule : f.rule = spawnRule N := f.member
  obtain ⟨rl, member, ext, opening, selection, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  obtain ⟨o', made⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
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
  obtain ⟨x, same⟩ := reads
  change observe (instantiate σ (instantiate opening (N.node .outside ![]))) = _ at same
  rw [instantiate_outside, instantiate_outside] at same
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-- **The spawning rule is disciplined for both directions**, for every program. -/
theorem spawn_both_ways :
    DisciplinedBothWays N P ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) :=
  bothWays_of_disciplined N (spawn_disciplined N) (fun f _ _ admitted => spawn_made_quiet N f admitted)

/-- A neighbour's rule: no take, no read, no tell, no check; it makes the row `eqn($T)`. -/
def spawnEqnRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [], read := [], tell := [], checks := [], produce := [observe (eqnN N (unk .datum))] }
  collect := []

/-- **The rule that makes an equation row is disciplined**, for every program: each of its firings is
apart from the hosted rows, and the row it makes never reads as an alternative's row. -/
theorem spawnEqn_disciplined :
    Disciplined N P ({spawnEqnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) := by
  intro n b w a others f beside _ admitted
  have rule : f.rule = spawnEqnRule N := f.member
  obtain ⟨rl, member, ext, opening, selection, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  have noTake : selection.taken = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  have noRead : selection.read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.1.symm
  obtain ⟨o', made⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
  refine ⟨apart_of_no_selection N beside admitted noTake noRead
    (fun B => ⟨fill (N.node .outside ![]) (N.node .outside ![]) (N.node .outside ![]) (N.node .outside ![])
      (N.node .outside ![]), fun _ inside => by cases inside⟩), ?_⟩
  intro o inside B σ _ reads
  simp only at made
  rw [made, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at inside
  subst inside
  have label : (RuleSyntax.Firing.result (Interface.Frames.contextual S) w
      (⟨spawnEqnRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) {spawnEqnRule N} w.frame)).label o =
      instantiateObservation opening (observe (eqnN N (unk .datum))) := by
    apply RuleSyntax.Firing.result_label_made _ shapes
    simp only [RuleSyntax.Firing.opened, RuleInstance.map, made, spawnEqnRule, List.map_cons, List.map_nil,
      List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
    rfl
  rw [label] at reads
  obtain ⟨x, y, same⟩ := reads
  change observe (instantiate σ (instantiate opening (eqnN N (unk .datum)))) = _ at same
  rw [instantiate_eqnN, instantiate_eqnN] at same
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-- The start of a query has knowledge with a solution: it knows nothing. -/
theorem start_solvable {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    (Interface.Frames.contextual S).Solvable (start N P q).knowledge :=
  ⟨startFrame κ, fun x => generator (startArity κ) x, fun _ member => absurd member List.not_mem_nil⟩

/-- **The rule that makes an equation row fails the clause for both directions**, at the start of
every query of every program: the row it makes reads as an equation row at every solution. -/
theorem spawnEqn_not_both_ways (q : Comp κ Γ star D.Ty)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    ¬ BothWaysAt N P ({spawnEqnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (start N P q) := by
  intro both
  let f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S)
      ({spawnEqnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (start N P q).frame :=
    RuleSyntax.Contextual.canonical (F := (start N P q).frame) (spawnEqnRule N) (Set.mem_singleton _)
      ⟨[], [], [freshId (start N P q)]⟩ []
  have fresh : f.Fresh (Interface.Frames.contextual S) (start N P q) :=
    RuleSyntax.Contextual.canonical_fresh (start N P q) (spawnEqnRule N) (Set.mem_singleton _) _ _
  obtain ⟨u, solved, _⟩ :=
    RuleSyntax.information_amalgamates (X := Interface.Frames.contextual S) f fresh rfl rfl
      (b := startFrame κ) (fun x => generator (startArity κ) x)
      (fill (N.node .outside ![]) (N.node .outside ![]) (N.node .outside ![]) (N.node .outside ![])
        (N.node .outside ![]))
      (fun _ member => absurd member List.not_mem_nil) (fun _ member => absurd member List.not_mem_nil)
  have admitted : f.Admits (Interface.Frames.contextual S) (start N P q) :=
    ⟨⟨fresh, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
      enabled_make (freshId_not_mem _), ⟨_, u, solved⟩, entails_of_no_checks rfl rfl⟩
  have beside : Beside N P 0 (initialBranch q) (start N P q) P.equations.length ∅ :=
    (beside_empty N).mpr (start_represents N P q unopened)
  obtain ⟨_, _, madeEqn⟩ := both f beside (fun o inside => absurd inside (Finset.notMem_empty o))
    (fun o inside => absurd inside (Finset.notMem_empty o)) admitted
  have label : (f.result (Interface.Frames.contextual S) (start N P q)).label (freshId (start N P q)) =
      instantiateObservation f.opening (observe (eqnN N (unk .datum))) :=
    RuleSyntax.Firing.result_label_made f admitted.1 (List.mem_singleton_self _)
  refine madeEqn (freshId (start N P q)) (List.mem_toFinset.mpr (List.mem_singleton_self _)) _ u solved
    ⟨instantiate u (instantiate f.opening (unk .datum)), ?_⟩
  rw [label]
  show observe (instantiate u (instantiate f.opening (eqnN N (unk .datum)))) = _
  rw [instantiate_eqnN, instantiate_eqnN]

/-- So it is not disciplined for both directions at every state. -/
theorem spawnEqn_not_disciplinedBothWays (q : Comp κ Γ star D.Ty)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    ¬ DisciplinedBothWays N P ({spawnEqnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) :=
  fun both => spawnEqn_not_both_ways N q unopened (both _)

/-- Nor along the runs from the start of any query: it fails at the start itself. -/
theorem spawnEqn_not_along (q : Comp κ Γ star D.Ty)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    ¬ BothWaysAlong N P ({spawnEqnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S))
      (start N P q) :=
  fun along => spawnEqn_not_both_ways N q unopened (along _ .refl)

end Generic

/-! ## The program with no equation, the query `(g)` -/

section Control

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-- The frame with no names. -/
abbrev B₀ : Interface.Frames.Frame MSig := ⟨Empty, noNames⟩

/-- A closing instantiation of the start's names. -/
def g₀ : Assignment (startArity mkeys) B₀.arity := startFill (closeNames [] (csym "a"))

/-- The rule that makes an equation row, at the MeTTa signature. -/
abbrev eqnMaker : RuleSyntax.Rule (RuleSyntax.Contextual.Terms MSig) := spawnEqnRule N

/-- The neighbour's program: that one rule. -/
abbrev eqnNeighbour : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig) := {eqnMaker}

/-- The firing of the neighbour's rule at the start of the query `(g)`. -/
def spawnFiring : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) eqnNeighbour
    (Hosting.start N P0 q).frame :=
  RuleSyntax.Contextual.canonical (F := (Hosting.start N P0 q).frame) eqnMaker (Set.mem_singleton _)
    ⟨[], [], [freshId (Hosting.start N P0 q)]⟩ []

theorem spawnFiring_fresh :
    spawnFiring.Fresh (Interface.Frames.contextual MSig) (Hosting.start N P0 q) :=
  RuleSyntax.Contextual.canonical_fresh (Hosting.start N P0 q) eqnMaker (Set.mem_singleton _) _ _

theorem no_tell {B : Interface.Frames.Frame MSig} (h : Assignment (unknownArity (S := MSig) [] ()) B.arity) :
    (Interface.Frames.contextual MSig).Models h eqnMaker.body.tell := by
  intro e member
  exact absurd member List.not_mem_nil

theorem start_known {B : Interface.Frames.Frame MSig} (g : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models g (Hosting.start N P0 q).knowledge := by
  intro e member
  exact absurd member List.not_mem_nil

/-- **The neighbour's rule fires at the start.** -/
theorem spawnFiring_admits :
    spawnFiring.Admits (Interface.Frames.contextual MSig) (Hosting.start N P0 q) := by
  obtain ⟨u, solved, _⟩ :=
    RuleSyntax.information_amalgamates (X := Interface.Frames.contextual MSig) spawnFiring spawnFiring_fresh
      rfl rfl (b := B₀) g₀
      (fill (N.node .outside ![]) (N.node .outside ![]) (N.node .outside ![]) (N.node .outside ![])
        (N.node .outside ![])) (start_known _) (no_tell _)
  exact ⟨⟨spawnFiring_fresh, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
    enabled_make (freshId_not_mem _), ⟨_, u, solved⟩, entails_of_no_checks rfl rfl⟩

/-- The state the neighbour's firing makes. -/
abbrev after : HostState MSig :=
  spawnFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 q)

/-- **A state where the call is switched off**: it represents the query's alternative beside rows that
never read as alternatives' rows, one of which matches the call. -/
def Blocked (w : HostState MSig) : Prop :=
  ∃ others, Beside N P0 0 (initialBranch q) w 0 others ∧ NeverReads (IsAlternative N) w others ∧
    ¬ NoMatchingRow N w 0 others

theorem startBeside : Beside N P0 0 (initialBranch q) (Hosting.start N P0 q) 0 ∅ :=
  (beside_empty N).mpr (start_represents N P0 q q_unopened)

theorem quietEmpty (shape : ∀ B : Interface.Frames.Frame MSig, Observation MSig B.arity → Prop)
    (w : HostState MSig) : NeverReads shape w ∅ :=
  fun o inside => absurd inside (Finset.notMem_empty o)

/-- **The state the neighbour's firing makes is one where the call is switched off.** -/
theorem after_blocked : Blocked after := by
  obtain ⟨apart, made⟩ :=
    spawnEqn_disciplined N (D := D) (P := P0) spawnFiring startBeside (quietEmpty _ _) spawnFiring_admits
  refine ⟨_, beside_after_other N startBeside spawnFiring_admits apart,
    neverReads_fire spawnFiring_admits (others_sub N startBeside) (quietEmpty _ _) made, ?_⟩
  intro noRow
  have zeroPresent : (0 : ℕ) ∈ (Hosting.start N P0 q).present := by decide
  have notMade : (0 : ℕ) ∉ spawnFiring.selection.made := fun inside =>
    freshId_not_mem (Hosting.start N P0 q) (List.mem_singleton.mp inside ▸ zeroPresent)
  have inO : freshId (Hosting.start N P0 q) ∈
      fire (∅ : Finset ℕ) (spawnFiring.selection.commit (T := Unit)) :=
    mem_fire.mpr (.inr (List.mem_toFinset.mpr (List.mem_singleton_self _)))
  -- a closing solution of the start's names, and the call it reads
  obtain ⟨σ, _, same⟩ := (startBeside.hosted.reads B₀ _).mp ⟨g₀, start_known g₀, rfl⟩
  have shape : instantiateObservation g₀ ((Hosting.start N P0 q).label 0) =
      observe (altN N (evalN N (applyN N (instantiate σ gT))) (emptyN N)) := same.symm
  obtain ⟨u, solved, onState, onRule⟩ :=
    RuleSyntax.information_amalgamates (X := Interface.Frames.contextual MSig) spawnFiring spawnFiring_fresh
      rfl rfl (b := B₀) g₀
      (fill (instantiate σ gT) (instantiate σ gT) (instantiate σ gT) (instantiate σ gT) (instantiate σ gT))
      (start_known g₀) (no_tell _)
  have row0 : instantiateObservation u
      (spawnFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 q) 0) =
      instantiateObservation g₀ ((Hosting.start N P0 q).label 0) :=
    onState _ (.inr (.inr ⟨0, zeroPresent, rfl⟩))
  have readsA : instantiateObservation u (after.label 0) =
      observe (altN N (evalN N (applyN N (instantiate σ gT))) (emptyN N)) := by
    show instantiateObservation u
      ((spawnFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 q)).label 0) = _
    rw [RuleSyntax.Firing.result_label_other spawnFiring notMade]
    exact row0.trans shape
  have label : after.label (freshId (Hosting.start N P0 q)) =
      instantiateObservation spawnFiring.opening (observe (eqnN N (unk .datum))) :=
    RuleSyntax.Firing.result_label_made spawnFiring spawnFiring_admits.1 (List.mem_singleton_self _)
  have inTerms : (observe (eqnN N (unk .datum)) : Observation MSig (unknownArity (S := MSig) [] ())) ∈
      eqnMaker.terms :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  have opened : instantiateObservation u (instantiateObservation spawnFiring.opening
      (observe (eqnN N (unk .datum)))) =
      instantiateObservation
        (fill (instantiate σ gT) (instantiate σ gT) (instantiate σ gT) (instantiate σ gT) (instantiate σ gT))
        (observe (eqnN N (unk .datum))) := onRule _ inTerms
  have sameRow : instantiateObservation u (after.label (freshId (Hosting.start N P0 q))) =
      observe (eqnN N (instantiate σ gT)) := by
    rw [label, opened]
    show observe (instantiate _ (eqnN N (unk .datum))) = _
    rw [instantiate_eqnN, instantiate_unk]
    rfl
  exact noRow _ inO B₀ u solved _ _ readsA sameRow

/-- **Where the call is switched off, the translated program has no firing.** -/
theorem blocked_still {w : HostState MSig} (blocked : Blocked w) (w' : HostState MSig) :
    ¬ Fires N P0 w w' := by
  obtain ⟨others, beside, quiet, matching⟩ := blocked
  intro fires
  exact matching ((unmatched_beside_iff N beside quiet (fun e member => by cases member) live_nil).mp
    ⟨w', fires⟩)

/-- **After the disciplined neighbour's firing the translated program has no firing.** The source
answers `(g)` (`Controls.p0_answers_g`). -/
theorem switched_off (w' : HostState MSig) : ¬ Fires N P0 after w' :=
  blocked_still after_blocked w'

/-- **Every firing of the union from such a state is the neighbour's and leaves the call switched
off.** -/
theorem blocked_step {w w' : HostState MSig} (blocked : Blocked w)
    (fires : FiresIn (translate N P0 ∪ eqnNeighbour) w w') : Blocked w' := by
  rcases (firesIn_union _ _ _ _).mp fires with hosted | ⟨f, admitted, rfl⟩
  · exact absurd hosted (blocked_still blocked w')
  · obtain ⟨others, beside, quiet, matching⟩ := blocked
    obtain ⟨apart, made⟩ := spawnEqn_disciplined N (D := D) (P := P0) f beside quiet admitted
    refine ⟨_, beside_after_other N beside admitted apart,
      neverReads_fire admitted (others_sub N beside) quiet made, ?_⟩
    intro noRow
    apply matching
    intro o inO B σ known x y readsA sameRow
    have isRule : f.rule = eqnMaker := f.member
    obtain ⟨rl, member, ext, opening, selection, seen⟩ := f
    simp only at isRule
    subst isRule
    have shapes := admitted.1
    have noTake : selection.taken = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
    have noRead : selection.read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.1.symm
    have oPresent : o ∈ w.present := others_sub N beside inO
    have zeroPresent : (0 : ℕ) ∈ w.present := beside.row_present N
    have notMade : ∀ i ∈ w.present, i ∉ selection.made := fun i present isMade =>
      Finset.disjoint_left.mp admitted.2.1.fresh (List.mem_toFinset.mpr isMade) present
    obtain ⟨u, solved, onState, _⟩ :=
      RuleSyntax.information_amalgamates (X := Interface.Frames.contextual MSig)
        (⟨eqnMaker, member, ext, opening, selection, seen⟩ :
          RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) eqnNeighbour w.frame)
        shapes.1 noTake noRead σ (fill x x x x x) known (no_tell _)
    have stays : o ∈ fire others
        ((⟨eqnMaker, member, ext, opening, selection, seen⟩ :
          RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) eqnNeighbour w.frame).selection.commit
          (T := Unit)) :=
      mem_fire.mpr (.inl ⟨inO, fun taken => absurd (noTake ▸ List.mem_toFinset.mp taken) List.not_mem_nil⟩)
    refine noRow o stays B u solved x y ?_ ?_
    · rw [RuleSyntax.Firing.result_label_other _ (notMade 0 zeroPresent)]
      exact (onState _ (.inr (.inr ⟨0, zeroPresent, rfl⟩))).trans readsA
    · rw [RuleSyntax.Firing.result_label_other _ (notMade o oPresent)]
      exact (onState _ (.inr (.inr ⟨o, oPresent, rfl⟩))).trans sameRow

/-- **From the state the neighbour's firing makes, no run of the union reaches a finished present
row**: the hosted program never answers again. -/
theorem never_answers {w : HostState MSig}
    (run : Relation.ReflTransGen (FiresIn (translate N P0 ∪ eqnNeighbour)) after w) :
    ∀ a ∈ w.present, ¬ StateFinished N w a := by
  have blocked : Blocked w := by
    induction run with
    | refl => exact after_blocked
    | tail _ fires ih => exact blocked_step ih fires
  obtain ⟨others, beside, quiet, _⟩ := blocked
  intro a present finished
  obtain rfl := finished_row_beside N (D := D) beside quiet present finished
  obtain ⟨⟨_, t, focus⟩, _⟩ :=
    (finished_iff N (D := D) (s := restrict w (hostedRows P0 0)) beside.hosted).mpr finished
  cases focus

/-- **The neighbour is disciplined for the program**: the hypothesis of
`runs_reflected_neighbour` holds of it. -/
theorem eqnNeighbour_disciplined : Disciplined N (D := D) P0 eqnNeighbour :=
  spawnEqn_disciplined N (D := D) (P := P0)

/-- **The answer is lost**: the source answers `(g)`, and from the state the neighbour's firing makes
the union shows no answer at all. -/
theorem answer_lost :
    ({gC} : Set MClosed) ∈ Answers.sourceAnswers D P0 supply sp q ∧
      unionAnswersFrom N P0 eqnNeighbour after = ∅ := by
  refine ⟨⟨final0, p0_answers_g.1, ?_⟩, ?_⟩
  · rw [p0_answers_g.2]
    exact Multiset.mem_singleton_self _
  · ext A
    constructor
    · rintro ⟨s, a, run, present, finished, _⟩
      exact absurd finished (never_answers run a present)
    · intro inside
      exact False.elim inside

/-- **The start is not a state where the call is switched off**: there the translated program fires. -/
theorem start_not_blocked : ¬ Blocked (Hosting.start N P0 q) := by
  intro blocked
  obtain ⟨w', fires⟩ : ∃ w', Fires N P0 (Hosting.start N P0 q) w' :=
    (unmatched_beside_iff N startBeside (quietEmpty _ _) (fun e member => by cases member) live_nil).mpr
      (noMatchingRow_of_neverReads N (quietEmpty _ _))
  exact blocked_still blocked w' fires

/-- **The state the neighbour's firing makes represents no alternative along the runs** of the union
(`AlongRuns.RepresentsAlong`): the rows beside the alternative are determined by the state
(`AlongRuns.beside_unique`), and one of them reads as an equation row. -/
theorem after_not_representsAlong (x : World mkeys [] () × Branch mkeys [] () MTy) :
    ¬ RepresentsAlong N (D := D) P0 eqnNeighbour (Hosting.start N P0 q) x after := by
  rintro ⟨_, a, others', beside', _, _, quietAlt', quietEqn'⟩
  obtain ⟨others, beside, _, matching⟩ := after_blocked
  obtain ⟨rfl, rfl⟩ := beside_unique N beside beside' quietAlt' spawnFiring_admits.2.2.1
  exact matching (noMatchingRow_of_neverReads N quietEqn')

/-- **Beside the spawning rule the call keeps its firing**: after that neighbour's firing at the start
of the query `(g)`, the translated program has a firing. -/
theorem spawn_keeps_call {w : HostState MSig}
    (fires : FiresIn ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))
      (Hosting.start N P0 q) w) : ∃ w', Fires N P0 w w' := by
  obtain ⟨f, admitted, rfl⟩ := fires
  obtain ⟨apart, madeAlt, madeEqn⟩ :=
    spawn_both_ways N (D := D) (P := P0) (Hosting.start N P0 q) f startBeside (quietEmpty _ _)
      (quietEmpty _ _) admitted
  have beside := beside_after_other N startBeside admitted apart
  have quietAlt := neverReads_fire admitted (others_sub N startBeside) (quietEmpty _ _) madeAlt
  have quietEqn := neverReads_fire admitted (others_sub N startBeside) (quietEmpty _ _) madeEqn
  exact (unmatched_beside_iff N beside quietAlt (fun e member => by cases member) live_nil).mpr
    (noMatchingRow_of_neverReads N quietEqn)

/-- **Such a pair of firings exists**: the spawning rule fires at the start, and then the translated
program fires. -/
theorem spawn_then_call :
    ∃ w w', FiresIn ({spawnRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))
      (Hosting.start N P0 q) w ∧ Fires N P0 w w' := by
  obtain ⟨w, fires⟩ := spawn_fires N (start_solvable N P0 q)
  obtain ⟨w', fires'⟩ := spawn_keeps_call fires
  exact ⟨w, w', fires, fires'⟩

end Control

#print axioms spawn_both_ways
#print axioms spawnEqn_disciplined
#print axioms spawnEqn_not_both_ways
#print axioms spawnEqn_not_disciplinedBothWays
#print axioms spawnEqn_not_along
#print axioms spawnFiring_admits
#print axioms after_blocked
#print axioms switched_off
#print axioms blocked_step
#print axioms never_answers
#print axioms eqnNeighbour_disciplined
#print axioms answer_lost
#print axioms spawn_keeps_call
#print axioms spawn_then_call
#print axioms start_not_blocked
#print axioms after_not_representsAlong

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.NeighbourControls
