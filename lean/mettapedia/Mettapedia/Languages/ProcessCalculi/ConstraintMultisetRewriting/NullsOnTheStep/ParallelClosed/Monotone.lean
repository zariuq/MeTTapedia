import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.NonEmptyPair

/-!
# Over ground terms, success without absence and count checks survives every composable neighbour

The separation `no_uniformTranslation` has the switchability of its source as a hypothesis. This
module shows where switchability comes from over ground terms, and that the hypothesis is needed
by a program that fires.

## Monotonicity

**For every substitution action** (`succeeds_union_of_joint`), with occurrences labelled by their
rows: for a program whose rules have only equality checks and `any` queries (no absence and no count
check, `MonotoneChecks`; rows added beside can only add witnesses to an `any` query) and every success
predicate on rows, if `C` reaches success by firings each of
whose information has a solution that also solves the knowledge of a composable `D` (`JointStep`),
then `C` beside `D` reaches success. The proof replays the run beside the neighbour: each firing
stays admitted (`Composition.positive_admission_monotone`), with the neighbour's occurrences renamed
away from the identities the firing makes (`shift`, a label-preserving involution); reachable success
is invariant under such renamings (`succeeds_rename`) and under equivalent knowledge
(`succeeds_congr`). A firing's predicate queries never matter here: dropping them keeps its
admission and its result (`dropQueries_valid`).

**Over ground terms** every firing's information is solvable together with every solvable knowledge
(`joint_of_ground`), so (`succeeds_union`) **reachable success of a configuration is reachable success
of its union with every composable configuration**.

Hence such a step is **not switchable** (`not_switchable`), and over ground terms a switchable program
has a rule with an absence or a count check (`switchable_has_absence_or_count`).

## The dividing line, with a control for each source of switching

* An absence check: the absence-guarded program is switchable (`source_switchable`, ground terms).
* A count check: `counted` (make `T` where exactly one `V` is present) is switchable over ground terms
  (`counted_switchable`): alone the store holding one `V` succeeds; beside a second `V` it never does.
* A tell on an unknown the neighbour's knowledge constrains: the program of `PositiveTell` has no check
  and is switchable over first-order terms (`PositiveTell.tellSource_switchable`).

Over first-order terms the dividing line is a theorem (`SharedUnknown.switchable_has_guard_or_shared`):
a switchable program has a rule with an absence or a count check, or a switching pair every run to
success of whose first part has a firing whose information mentions an unknown the second part's
knowledge mentions.

## A program that fires and is not switchable, translated uniformly

`relay` takes the trigger `V` and makes `T`; it has no check. It fires (`relay_fires`) and is not
switchable (`relay_not_switchable`). Its reachable success is exactly: `T` is present, or the knowledge
is solvable and `V` is present (`relay_succeeds_iff`). The map `relayMap` sends a configuration with
solvable knowledge to the bag of its rows and any other configuration to the bag of its rows `T`; it
is defined from the rows and a check of the knowledge, never from success. It is a **uniform
translation** into the bag calculus of the positive rule "take `V`, make `T`" (`relayTranslation`), a
persistent calculus (`relayTarget_persistent`). So the source hypothesis of `no_uniformTranslation` is
needed, by a source that fires: dropping switchability alone, a uniform translation into a persistent
calculus exists; and the separation itself gives non-switchability again
(`relay_not_switchable_by_separation`).

The check of the knowledge is needed, and is not a case on success: a configuration whose knowledge is
not solvable is composable with nothing, so homomorphism constrains its image nowhere, and its rows
`V` must not reach `T`. For the program that makes `T` from nothing (`maker`), which is not switchable
either (`maker_not_switchable`), **no uniform translation into any calculus of positive bag rules
exists** (`maker_no_bag_translation`): homomorphism forces the image of the empty store to be the
empty bag, which then succeeds and so makes every bag succeed, while the configuration with no rows
and unsolvable knowledge does not succeed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Monotone

open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
  (unionOf positive_admission_monotone models_problem_unionOf)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Reduces)

/-! ## Replaying a run beside a neighbour, for every substitution action

Occurrences are pairs of a row and a copy number, labelled by their row (`Prod.fst`). -/

section General

variable {T : Type*} {S : Type*} [DecidableEq T]

/-- **A rule without absence and count checks**: each of its checks is an equality. -/
def EqualityChecks (r : RuleInstance T) : Prop := ∀ c ∈ r.checks, ∃ l r', c = Check.equal l r'

/-- **A rule no composable neighbour switches off**: each of its checks is an equality or an `any`
query. A neighbour only adds rows, and added rows can only add witnesses to an `any` query; an absence
(`none`) check and a count can each be falsified by an added row. -/
def MonotoneChecks (r : RuleInstance T) : Prop :=
  ∀ c ∈ r.checks, (∃ l r', c = Check.equal l r') ∨ ∃ p, c = Check.predicate .any p

omit [DecidableEq T] in
/-- A rule whose checks are equalities has monotone checks. -/
theorem EqualityChecks.monotoneChecks {r : RuleInstance T} (equalities : EqualityChecks r) :
    MonotoneChecks r :=
  fun c member => Or.inl (equalities c member)

variable {A : SubstitutionAction T S}

/-- **A firing's predicate queries never matter for reachability**: dropping them keeps its
admission, and its result is the same. -/
theorem dropQueries_valid {C : Configuration T (T × ℕ)} {f : AnnotatedRuns.Firing T S (T × ℕ)}
    (admitted : f.Valid A Prod.fst C) :
    (⟨f.rule, [], f.selection⟩ : AnnotatedRuns.Firing T S (T × ℕ)).Valid A Prod.fst C :=
  PredicateQueryAdmission.regionValid_nil_iff.mpr admitted.firing

variable {P : RuleInstance T → Prop} {row : T → Prop}

/-- **Reachable success is read up to equivalent knowledge and equal present occurrences.** -/
theorem succeeds_congr {C D : Configuration T (T × ℕ)} (same : GuardFreeProcessOrders.SameUpTo A C D)
    (succeeds : (stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds C) :
    (stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds D := by
  obtain ⟨C', run, shows⟩ := succeeds
  induction run using Relation.ReflTransGen.head_induction_on generalizing D with
  | refl =>
      obtain ⟨o, present, holds⟩ := shows
      refine ParallelCalculus.succeeds_of_success _ ⟨o, ?_, holds⟩
      rw [← same.2]
      exact present
  | head step _ ih =>
      obtain ⟨f, inProgram, admitted, rfl⟩ := step
      have admittedD : f.Valid A Prod.fst D :=
        (AnnotatedRuns.Firing.valid_congr A Prod.fst same).mp admitted
      exact ParallelCalculus.succeeds_of_step _ ⟨f, inProgram, admittedD, rfl⟩
        (ih (AnnotatedRuns.Firing.result_congr A Prod.fst f same))

/-- **Reachable success is invariant under label-preserving renamings of occurrence identities.** -/
theorem succeeds_rename (π : T × ℕ ≃ T × ℕ) (keeps : ∀ o, (π o).1 = o.1) {C : Configuration T (T × ℕ)}
    (succeeds : (stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds C) :
    (stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds (AnnotatedRuns.renameConfiguration π C) := by
  obtain ⟨C', run, shows⟩ := succeeds
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
      obtain ⟨o, present, holds⟩ := shows
      refine ParallelCalculus.succeeds_of_success _ ⟨π o, Finset.mem_map_of_mem π.toEmbedding present, ?_⟩
      show row (π o).1
      rw [keeps]
      exact holds
  | head step _ ih =>
      obtain ⟨f, inProgram, admitted, rfl⟩ := step
      have renamed : (f.rename π).Valid A Prod.fst (AnnotatedRuns.renameConfiguration π _) :=
        (AnnotatedRuns.Firing.valid_rename A keeps f _).mpr admitted
      exact ParallelCalculus.succeeds_of_step _
        ⟨f.rename π, inProgram, renamed, AnnotatedRuns.Firing.result_rename keeps f _⟩ ih

/-! ### Moving a neighbour's occurrences out of the way -/

/-- Send each occurrence of `D` to the copy `N` higher, and each such copy back; leave the rest. -/
def shift (D : Finset (T × ℕ)) (N : ℕ) (o : T × ℕ) : T × ℕ :=
  if o ∈ D then (o.1, o.2 + N) else if N ≤ o.2 ∧ ((o.1, o.2 - N) : T × ℕ) ∈ D then (o.1, o.2 - N) else o

theorem shift_fst (D : Finset (T × ℕ)) (N : ℕ) (o : T × ℕ) : (shift D N o).1 = o.1 := by
  unfold shift
  split_ifs <;> rfl

/-- When every copy number of `D` is below `N`, `shift` is an involution. -/
theorem shift_involutive {D : Finset (T × ℕ)} {N : ℕ} (below : ∀ o ∈ D, o.2 < N) :
    Function.Involutive (shift D N) := by
  intro o
  by_cases inD : o ∈ D
  · have up : ((o.1, o.2 + N) : T × ℕ) ∉ D := fun member => by
      have := below _ member
      simp only at this
      omega
    have back : N ≤ o.2 + N ∧ ((o.1, o.2 + N - N) : T × ℕ) ∈ D := by
      refine ⟨Nat.le_add_left _ _, ?_⟩
      rw [Nat.add_sub_cancel]
      exact inD
    have first : shift D N o = (o.1, o.2 + N) := by unfold shift; rw [if_pos inD]
    rw [first]
    unfold shift
    rw [if_neg up]
    simp only at back ⊢
    rw [if_pos back, Nat.add_sub_cancel]
  · by_cases down : N ≤ o.2 ∧ ((o.1, o.2 - N) : T × ℕ) ∈ D
    · have first : shift D N o = (o.1, o.2 - N) := by unfold shift; rw [if_neg inD, if_pos down]
      rw [first]
      unfold shift
      rw [if_pos down.2]
      simp only
      rw [Nat.sub_add_cancel down.1]
    · have first : shift D N o = o := by unfold shift; rw [if_neg inD, if_neg down]
      rw [first, first]

/-- `shift` fixes every occurrence outside `D` whose copy number is below `N`. -/
theorem shift_fixed {D : Finset (T × ℕ)} {N : ℕ} {o : T × ℕ} (outside : o ∉ D) (small : o.2 < N) :
    shift D N o = o := by
  unfold shift
  rw [if_neg outside, if_neg (fun h => by omega)]

/-- `shift` sends `D` to copy numbers at least `N`. -/
theorem shift_large {D : Finset (T × ℕ)} {N : ℕ} {o : T × ℕ} (inside : o ∈ D) :
    N ≤ (shift D N o).2 := by
  unfold shift
  rw [if_pos inside]
  exact Nat.le_add_left _ _

/-- The largest copy number of a finite set of occurrences, plus one. -/
def bound (F : Finset (T × ℕ)) : ℕ := F.sup Prod.snd + 1

omit [DecidableEq T] in
theorem lt_bound {F : Finset (T × ℕ)} {o : T × ℕ} (member : o ∈ F) : o.2 < bound F :=
  Nat.lt_succ_of_le (Finset.le_sup (f := Prod.snd) member)

/-! ### Replaying one firing, and a run -/

/-- **A firing whose checks are equalities or `any` queries stays admitted beside a neighbour whose occurrences
its made identities avoid, when its information has a solution that also solves the neighbour's
knowledge; its result there is its result alone beside the neighbour, up to the order of the
knowledge.** -/
theorem replay_beside {C D : Configuration T (T × ℕ)} {f : AnnotatedRuns.Firing T S (T × ℕ)}
    (monotone : MonotoneChecks f.rule) (admitted : f.Valid A Prod.fst C)
    (joint : ∃ σ, A.Models σ (f.selection.problem Prod.fst f.rule C) ∧ A.Models σ D.equations)
    (apart : Disjoint C.present D.present) (freshInD : ∀ o ∈ f.selection.made, o ∉ D.present) :
    (⟨f.rule, [], f.selection⟩ : AnnotatedRuns.Firing T S (T × ℕ)).Valid A Prod.fst (unionOf C D) ∧
      GuardFreeProcessOrders.SameUpTo A (unionOf (f.result Prod.fst C) D)
        ((⟨f.rule, [], f.selection⟩ : AnnotatedRuns.Firing T S (T × ℕ)).result Prod.fst (unionOf C D)) := by
  have plain := dropQueries_valid admitted
  refine ⟨positive_admission_monotone monotone rfl plain freshInD joint, ?_, ?_⟩
  · intro σ
    show A.Models σ (f.selection.problem Prod.fst f.rule C ++ D.equations) ↔
      A.Models σ (f.selection.problem Prod.fst f.rule (unionOf C D))
    rw [SubstitutionAction.models_append]
    exact (models_problem_unionOf A Prod.fst ⟨f.rule, [], f.selection⟩ C D σ).symm
  · show fire C.present (f.selection.commit (T := T)) ∪ D.present =
      fire (C.present ∪ D.present) (f.selection.commit (T := T))
    ext o
    simp only [Finset.mem_union, mem_fire]
    constructor
    · rintro ((⟨inC, notTaken⟩ | made) | inD)
      · exact Or.inl ⟨Or.inl inC, notTaken⟩
      · exact Or.inr made
      · refine Or.inl ⟨Or.inr inD, fun taken => ?_⟩
        exact Finset.disjoint_left.mp apart (admitted.firing.occurrences.taken_subset taken) inD
    · rintro (⟨inC | inD, notTaken⟩ | made)
      · exact Or.inl (Or.inl ⟨inC, notTaken⟩)
      · exact Or.inr inD
      · exact Or.inl (Or.inr made)

variable (A) in
/-- **A step whose information is solvable together with the knowledge `K`**: a firing of the program,
admitted, whose information has a solution that also solves `K`. -/
def JointStep (P : RuleInstance T → Prop) (K : EquationStore T) (C C' : Configuration T (T × ℕ)) :
    Prop :=
  ∃ f : AnnotatedRuns.Firing T S (T × ℕ), P f.rule ∧ f.Valid A Prod.fst C ∧ f.result Prod.fst C = C' ∧
    ∃ σ, A.Models σ (f.selection.problem Prod.fst f.rule C) ∧ A.Models σ K

/-- **Replaying a run beside a neighbour**, for every substitution action. For a program whose rules
have only equality checks and `any` queries, and every success predicate on rows: if `C` reaches success by firings
each of whose information has a solution that also solves the knowledge of a composable `D`, then `C`
beside `D` reaches success. -/
theorem succeeds_union_of_joint (monotone : ∀ r, P r → MonotoneChecks r) {K : EquationStore T}
    {C D C' : Configuration T (T × ℕ)} (composable : Composable A C D) (knowledgeD : D.equations = K)
    (run : Relation.ReflTransGen (JointStep A P K) C C') (shows : Shows (Prod.fst : T × ℕ → T) row C') :
    (stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds (unionOf C D) := by
  induction run using Relation.ReflTransGen.head_induction_on generalizing D with
  | refl =>
      obtain ⟨o, present, holds⟩ := shows
      exact ParallelCalculus.succeeds_of_success _ ⟨o, Finset.mem_union_left _ present, holds⟩
  | @head C C₁ step _ ih =>
      obtain ⟨f, inProgram, admitted, rfl, σ, solvedC, solvedK⟩ := step
      -- move the neighbour's occurrences above every identity of `C` and of the firing
      let F : Finset (T × ℕ) := C.present ∪ D.present ∪ f.selection.made.toFinset
      let N := bound F
      have belowD : ∀ o ∈ D.present, o.2 < N := fun o member =>
        lt_bound (Finset.mem_union_left _ (Finset.mem_union_right _ member))
      have belowC : ∀ o ∈ C.present, o.2 < N := fun o member =>
        lt_bound (Finset.mem_union_left _ (Finset.mem_union_left _ member))
      have belowMade : ∀ o ∈ f.selection.made, o.2 < N := fun o member =>
        lt_bound (Finset.mem_union_right _ (List.mem_toFinset.mpr member))
      let π : T × ℕ ≃ T × ℕ := Function.Involutive.toPerm (shift D.present N) (shift_involutive belowD)
      have keeps : ∀ o, (π o).1 = o.1 := shift_fst D.present N
      have fixesC : ∀ o ∈ C.present, π o = o := fun o member =>
        shift_fixed (Finset.disjoint_left.mp composable.1 member) (belowC o member)
      let D' : Configuration T (T × ℕ) := AnnotatedRuns.renameConfiguration π D
      have knowledgeD' : D'.equations = K := knowledgeD
      have largeD' : ∀ o ∈ D'.present, N ≤ o.2 := by
        intro o member
        obtain ⟨p, inside, rfl⟩ := Finset.mem_map.mp member
        exact shift_large inside
      have apartCD' : Disjoint C.present D'.present := Finset.disjoint_left.mpr
        fun {o} inC inD' => absurd (largeD' o inD') (Nat.not_le.mpr (belowC o inC))
      have freshInD' : ∀ o ∈ f.selection.made, o ∉ D'.present := fun o made inD' =>
        absurd (largeD' o inD') (Nat.not_le.mpr (belowMade o made))
      have solvedD' : A.Models σ D'.equations := by
        rw [knowledgeD']
        exact solvedK
      -- the firing replayed beside the moved neighbour
      obtain ⟨besideAdmitted, same⟩ :=
        replay_beside (D := D') (monotone f.rule inProgram) admitted ⟨σ, solvedC, solvedD'⟩ apartCD'
          freshInD'
      -- the result alone, beside the moved neighbour, is composable
      have composable₁ : Composable A (f.result Prod.fst C) D' := by
        refine ⟨Finset.disjoint_left.mpr fun {o} inResult inD' => ?_,
          ⟨σ, (SubstitutionAction.models_append A σ _ _).mpr ⟨solvedC, solvedD'⟩⟩⟩
        have small : o.2 < N := by
          change o ∈ fire C.present (f.selection.commit (T := T)) at inResult
          rcases mem_fire.mp inResult with ⟨inC, -⟩ | made
          · exact belowC o inC
          · exact belowMade o (List.mem_toFinset.mp made)
        exact absurd (largeD' o inD') (Nat.not_le.mpr small)
      have movedSucceeds :
          (stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds (unionOf C D') :=
        ParallelCalculus.succeeds_of_step _ ⟨⟨f.rule, [], f.selection⟩, inProgram, besideAdmitted, rfl⟩
          (succeeds_congr same (ih composable₁ knowledgeD'))
      -- rename back
      have back : AnnotatedRuns.renameConfiguration π (unionOf C D') = unionOf C D := by
        show (⟨C.equations ++ D.equations,
            (C.present ∪ D.present.map π.toEmbedding).map π.toEmbedding⟩ : Configuration T (T × ℕ)) =
          ⟨C.equations ++ D.equations, C.present ∪ D.present⟩
        congr 1
        ext o
        simp only [Finset.mem_map, Finset.mem_union, Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨a, inC | ⟨b, inD, rfl⟩, rfl⟩
          · exact Or.inl (by rw [fixesC a inC]; exact inC)
          · exact Or.inr (by
              rw [show π (π b) = b from shift_involutive belowD b]
              exact inD)
        · rintro (inC | inD)
          · exact ⟨o, Or.inl inC, fixesC o inC⟩
          · exact ⟨π o, Or.inr ⟨o, inD, rfl⟩, shift_involutive belowD o⟩
      rw [← back]
      exact succeeds_rename π keeps movedSucceeds

end General

/-! ## Over ground terms -/

section Monotone

variable {P : RuleInstance Expr → Prop} {row : Expr → Prop}

/-- Over ground terms a knowledge is solvable exactly when each of its equations has identical
sides. -/
theorem consistent_iff {L : EquationStore Expr} : ground.Consistent L ↔ ∀ e ∈ L, e.1 = e.2 :=
  ⟨fun ⟨_, solved⟩ e member => solved e member, fun same => ⟨(), same⟩⟩

/-- **Over ground terms every step is solvable together with every solvable knowledge**: the
identity is the only solution. -/
theorem joint_of_ground {K : EquationStore Expr} (solvable : ground.Consistent K) {C C' : Conf}
    (step : ProgramStep ground (Prod.fst : Occ → Expr) P C C') : JointStep ground P K C C' := by
  obtain ⟨f, inProgram, admitted, rfl⟩ := step
  obtain ⟨⟨⟩, solvedC⟩ := (show f.Valid ground Prod.fst C from admitted).firing.consistent
  obtain ⟨⟨⟩, solvedK⟩ := solvable
  exact ⟨f, inProgram, admitted, rfl, (), solvedC, solvedK⟩

/-- Over ground terms every run of the program is a run of steps solvable together with every
solvable knowledge. -/
theorem joint_run_of_ground {K : EquationStore Expr} (solvable : ground.Consistent K) {C C' : Conf}
    (run : Relation.ReflTransGen (ProgramStep ground (Prod.fst : Occ → Expr) P) C C') :
    Relation.ReflTransGen (JointStep ground P K) C C' := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (joint_of_ground solvable step)

/-- **Monotonicity.** Over ground terms, for a program whose rules have only equality checks and `any`
queries, and every success predicate on rows: reachable success of `C` is reachable success of `C` beside every
composable `D`. -/
theorem succeeds_union (monotone : ∀ r, P r → MonotoneChecks r) {C D : Conf}
    (composable : Composable ground C D)
    (succeeds : (stepCalculus ground (Prod.fst : Occ → Expr) P row).Succeeds C) :
    (stepCalculus ground (Prod.fst : Occ → Expr) P row).Succeeds (unionOf C D) := by
  obtain ⟨C', run, shows⟩ := succeeds
  have solvable : ground.Consistent D.equations := by
    obtain ⟨u, solved⟩ := composable.2
    exact ⟨u, fun e member => solved e (List.mem_append_right _ member)⟩
  exact succeeds_union_of_joint monotone composable rfl (joint_run_of_ground solvable run) shows

/-- **Not switchable**: over ground terms, the step under a program whose rules have only equality
checks and `any` queries is not switched off by any composable neighbour, for every success predicate
on rows. -/
theorem not_switchable (monotone : ∀ r, P r → MonotoneChecks r) :
    ¬ (stepCalculus ground (Prod.fst : Occ → Expr) P row).Switchable := by
  rintro ⟨s, s', composable, succeeds, blocked⟩
  exact blocked (succeeds_union monotone composable succeeds)

/-- **The dividing line over ground terms**: a switchable program has a rule with an absence or a
count check. -/
theorem switchable_has_absence_or_count
    (switchable : (stepCalculus ground (Prod.fst : Occ → Expr) P row).Switchable) :
    ∃ r, P r ∧ ∃ c ∈ r.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n := by
  by_contra none
  refine not_switchable (fun r inProgram c member => ?_) switchable
  cases c with
  | equal l r' => exact Or.inl ⟨l, r', rfl⟩
  | predicate quantifier p =>
      cases quantifier with
      | any => exact Or.inr ⟨p, rfl⟩
      | none => exact absurd ⟨r, inProgram, _, member, Or.inl ⟨p, rfl⟩⟩ none
  | count p n => exact absurd ⟨r, inProgram, _, member, Or.inr ⟨p, n, rfl⟩⟩ none

end Monotone

/-! ## A count check switches -/

section Count

/-- `counted`: make `T` where exactly one `V` is present. -/
def counted : RuleInstance Expr := rule [] [] [factT] [.count trigger 1]

/-- The program of that rule. -/
def countedProgram (r : RuleInstance Expr) : Prop := r = counted

/-- The step under it, success "a row `T` is present". -/
abbrev countedSource : ParallelCalculus :=
  stepCalculus ground (Prod.fst : Occ → Expr) countedProgram (· = factT)

/-- A second store holding `V`, with another copy number. -/
def secondTrigger : Conf := ⟨[], {(trigger, 1)}⟩

/-- `counted`, making `T` with copy number `0`. -/
def countedAt : Fir := ⟨counted, [], ⟨[], [], [(factT, 0)]⟩⟩

/-- At the store holding one `V`, exactly one row is `V`. -/
theorem one_trigger : (Check.count trigger 1).Holds ground () Prod.fst triggerStore.present := by
  show (Check.matches ground () Prod.fst triggerStore.present trigger).card = 1
  have same : Check.matches ground () Prod.fst triggerStore.present trigger = triggerStore.present := by
    ext o
    simp only [Check.matches, Finset.mem_filter]
    refine ⟨And.left, fun member => ⟨member, ?_⟩⟩
    simp only [triggerStore, Finset.mem_singleton] at member
    subst member
    exact (rfl : trigger = trigger)
  rw [same]
  exact Finset.card_singleton _

/-- At the union with the second store, two rows are `V`. -/
theorem two_triggers :
    (Check.matches ground () Prod.fst (unionOf triggerStore secondTrigger).present trigger).card = 2 := by
  have same : Check.matches ground () Prod.fst (unionOf triggerStore secondTrigger).present trigger =
      (unionOf triggerStore secondTrigger).present := by
    ext o
    simp only [Check.matches, Finset.mem_filter]
    refine ⟨And.left, fun member => ⟨member, ?_⟩⟩
    simp only [unionOf, triggerStore, secondTrigger, Finset.mem_union, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> exact (rfl : trigger = trigger)
  rw [same]
  decide

/-- **Alone, the store holding one `V` succeeds.** -/
theorem counted_alone : countedSource.Succeeds triggerStore := by
  have admitted : base.Admits (s := triggerStore) countedAt := by
    refine (admits_of (D := fun _ _ _ _ => True) (σ := (triggerStore, ∅)) (fresh := [])
      (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl ?_ trivial).1
    intro c member
    simp only [counted, rule, List.mem_singleton] at member
    subst member
    exact one_trigger
  refine ⟨_, .single ⟨countedAt, rfl, admitted, rfl⟩, (factT, 0), ?_, rfl⟩
  change (factT, 0) ∈ fire triggerStore.present (countedAt.selection.commit (T := Expr))
  rw [mem_fire]
  exact Or.inr (by simp [countedAt, Selection.commit])

/-- The two stores are composable. -/
theorem triggers_composable : countedSource.composable triggerStore secondTrigger :=
  ⟨by decide, ⟨(), fun _ member => absurd member List.not_mem_nil⟩⟩

/-- **Beside a second `V`, success is unreachable**: `counted` is refused there, and no row `T` is
present. -/
theorem counted_beside : ¬ countedSource.Succeeds (unionOf triggerStore secondTrigger) := by
  rintro ⟨C', run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨f, inProgram, admitted, -⟩, -⟩
  · obtain ⟨o, present, isT⟩ := shows
    simp only [unionOf, triggerStore, secondTrigger, Finset.mem_union, Finset.mem_singleton] at present
    rcases present with rfl | rfl <;> exact absurd isT (by decide)
  · have valid : f.Valid ground Prod.fst (unionOf triggerStore secondTrigger) := admitted
    have isCounted : f.rule = counted := inProgram
    obtain ⟨⟨⟩, solved⟩ := valid.firing.consistent
    have holds := valid.firing.checks (.count trigger 1) (by rw [isCounted]; simp [counted, rule]) ()
      solved
    have one : (Check.matches ground () Prod.fst (unionOf triggerStore secondTrigger).present
        trigger).card = 1 := holds
    rw [two_triggers] at one
    exact absurd one (by decide)

/-- **A count check alone makes a program switchable** over ground terms. -/
theorem counted_switchable : countedSource.Switchable :=
  ⟨triggerStore, secondTrigger, triggers_composable, counted_alone, counted_beside⟩

end Count

/-! ## A program that fires, is not switchable, and is translated uniformly -/

section Relay

/-- `relay`: take the trigger `V`, make `T`. No check. -/
def relay : RuleInstance Expr := rule [trigger] [] [factT]

/-- The program of that rule. -/
def relayProgram (r : RuleInstance Expr) : Prop := r = relay

/-- The step under it, success "a row `T` is present". -/
abbrev relaySource : ParallelCalculus :=
  stepCalculus ground (Prod.fst : Occ → Expr) relayProgram (· = factT)

theorem relay_equalityChecks : ∀ r, relayProgram r → EqualityChecks r := by
  rintro r rfl c member
  simp [relay, rule] at member

/-- **Not switchable**, by monotonicity. -/
theorem relay_not_switchable : ¬ relaySource.Switchable :=
  not_switchable fun r inProgram => (relay_equalityChecks r inProgram).monotoneChecks

/-- The firing of `relay` taking the occurrence `o` and making `T` with copy number `k`. -/
def relayAt (o : Occ) (k : ℕ) : Fir := ⟨relay, [], ⟨[o], [], [(factT, k)]⟩⟩

/-- **`relay` fires** wherever the knowledge has identical sides and `V` is present, making `T` with
a copy number above every present one. -/
theorem relay_admitted {C : Conf} (knowledge : ∀ e ∈ C.equations, e.1 = e.2) {o : Occ}
    (present : o ∈ C.present) (isTrigger : o.1 = trigger) :
    base.Admits (s := C) (relayAt o (bound C.present)) ∧
      (factT, bound C.present) ∈ ((relayAt o (bound C.present)).result Prod.fst C).present := by
  have fresh : ((factT, bound C.present) : Occ) ∉ C.present := fun member =>
    absurd (lt_bound member) (Nat.lt_irrefl _)
  have enabled : Enabled Prod.fst C.present
      (Selection.commit (T := Expr) ⟨[o], [], [(factT, bound C.present)]⟩) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p member
      have same : p = o := by simpa [Selection.commit] using member
      rw [same]
      exact present
    · intro p member
      simp [Selection.commit] at member
    · simp [Selection.commit]
    · simpa [Selection.commit] using fresh
    · intro query member
      simp [Selection.commit] at member
  refine ⟨(admits_of (D := fun _ _ _ _ => True) (σ := (C, ∅)) (fresh := []) (List.nodup_singleton _)
    (List.nodup_singleton _) (by simp [relay, rule, isTrigger]) rfl rfl enabled knowledge rfl
    (no_checks rfl) trivial).1, ?_⟩
  change (factT, bound C.present) ∈ fire C.present ((relayAt o (bound C.present)).selection.commit
    (T := Expr))
  rw [mem_fire]
  exact Or.inr (by simp [relayAt, Selection.commit])

/-- **`relay` fires** at the store holding `V`, and that store succeeds. -/
theorem relay_fires :
    base.Admits (s := triggerStore) (relayAt (trigger, 0) (bound triggerStore.present)) ∧
      relaySource.Succeeds triggerStore := by
  obtain ⟨admitted, made⟩ :=
    relay_admitted (C := triggerStore) (by simp [triggerStore]) (o := (trigger, 0)) (by decide) rfl
  exact ⟨admitted,
    ⟨_, .single ⟨relayAt (trigger, 0) (bound triggerStore.present), rfl, admitted, rfl⟩, _, made, rfl⟩⟩

/-- **The reachable success of `relay`**: `T` is present, or the knowledge has identical sides and `V`
is present. -/
theorem relay_succeeds_iff (C : Conf) :
    relaySource.Succeeds C ↔
      (∃ o ∈ C.present, o.1 = factT) ∨
        ((∀ e ∈ C.equations, e.1 = e.2) ∧ ∃ o ∈ C.present, o.1 = trigger) := by
  constructor
  · rintro ⟨C', run, shows⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨f, inProgram, admitted, -⟩, -⟩
    · exact Or.inl shows
    · have valid : f.selection.Valid ground Prod.fst f.rule C :=
        (show f.Valid ground Prod.fst C from admitted).firing
      have isRelay : f.rule = relay := inProgram
      have problem := consistent_iff.mp valid.consistent
      refine Or.inr ⟨fun e member => problem e (by simp [Selection.problem, member]), ?_⟩
      have takes := takes_match valid
      rw [isRelay] at takes
      obtain ⟨o, taken, isTrigger⟩ := match_one takes
      exact ⟨o, taken_present valid (by rw [taken]; simp), isTrigger.symm⟩
  · rintro (now | ⟨knowledge, o, present, isTrigger⟩)
    · exact ParallelCalculus.succeeds_of_success _ now
    · obtain ⟨admitted, made⟩ := relay_admitted knowledge present isTrigger
      exact ⟨_, .single ⟨relayAt o (bound C.present), rfl, admitted, rfl⟩, _, made, rfl⟩

/-- The bag rule "take `V`, make `T`". -/
def relayBag : Rule Expr := ⟨{trigger}, 0, {factT}, fun _ => false⟩

/-- Its bag calculus. -/
abbrev relayTarget : ParallelCalculus := bagCalculus (· = relayBag)

/-- **The target is persistent**: its one rule is positive. -/
theorem relayTarget_persistent : relayTarget.Persistent :=
  bagCalculus_persistent fun ρ isRelay x => by rw [isRelay]; rfl

/-- **The reachable success of the target**: `T` or `V` is in the bag. -/
theorem relayTarget_succeeds_iff (M : Multiset Expr) :
    relayTarget.Succeeds M ↔ factT ∈ M ∨ trigger ∈ M := by
  constructor
  · rintro ⟨M', run, present⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨ρ, isRelay, enabled, -⟩, -⟩
    · exact Or.inl present
    · rw [isRelay] at enabled
      exact Or.inr (Multiset.mem_of_le enabled.1 (by simp [relayBag, Rule.redex]))
  · rintro (now | trig)
    · exact ParallelCalculus.succeeds_of_success _ now
    · refine ⟨relayBag.result M, .single ⟨relayBag, rfl, ⟨?_, fun _ _ => rfl⟩, rfl⟩, ?_⟩
      · simpa [relayBag, Rule.redex] using trig
      · show factT ∈ relayBag.result M
        simp [Rule.result, relayBag]

/-- **The translation**: the bag of rows of a configuration whose knowledge has identical sides, and
the bag of its rows `T` otherwise. -/
def relayMap (C : Conf) : Multiset Expr :=
  if ∀ e ∈ C.equations, e.1 = e.2 then Controls.rows C else (Controls.rows C).filter (· = factT)

theorem trigger_ne_factT : trigger ≠ factT := by decide

/-- What the image holds. -/
theorem mem_relayMap (C : Conf) (e : Expr) :
    e ∈ relayMap C ↔
      (∃ o ∈ C.present, o.1 = e) ∧ ((∀ e ∈ C.equations, e.1 = e.2) ∨ e = factT) := by
  unfold relayMap
  split_ifs with knowledge
  · rw [Controls.mem_rows]
    exact ⟨fun inside => ⟨inside, Or.inl knowledge⟩, fun inside => inside.1⟩
  · rw [Multiset.mem_filter, Controls.mem_rows]
    exact ⟨fun inside => ⟨inside.1, Or.inr inside.2⟩,
      fun inside => ⟨inside.1, inside.2.resolve_left knowledge⟩⟩

/-- **The image succeeds exactly when the configuration does.** -/
theorem relayMap_succeeds_iff (C : Conf) : relayTarget.Succeeds (relayMap C) ↔ relaySource.Succeeds C := by
  rw [relayTarget_succeeds_iff, mem_relayMap, mem_relayMap, relay_succeeds_iff]
  constructor
  · rintro (⟨now, -⟩ | ⟨inside, knowledge | isT⟩)
    · exact Or.inl now
    · exact Or.inr ⟨knowledge, inside⟩
    · exact absurd isT trigger_ne_factT
  · rintro (now | ⟨knowledge, inside⟩)
    · exact Or.inl ⟨now, Or.inr rfl⟩
    · exact Or.inr ⟨inside, Or.inl knowledge⟩

/-- **A uniform translation of `relay`** into the bag calculus of "take `V`, make `T`": homomorphic on
composable configurations, preserving and reflecting reachable success. -/
def relayTranslation : UniformTranslation relaySource relayTarget where
  map := relayMap
  homomorphic s s' composable := by
    have union : ∀ e ∈ s.equations ++ s'.equations, e.1 = e.2 := consistent_iff.mp composable.2
    have left : ∀ e ∈ s.equations, e.1 = e.2 := fun e member => union e (List.mem_append_left _ member)
    have right : ∀ e ∈ s'.equations, e.1 = e.2 := fun e member =>
      union e (List.mem_append_right _ member)
    show relayMap (unionOf s s') = relayMap s + relayMap s'
    unfold relayMap
    rw [if_pos (show ∀ e ∈ (unionOf s s').equations, e.1 = e.2 from union), if_pos left, if_pos right]
    exact Controls.rows_unionOf composable.1
  preserves s succeeds := (relayMap_succeeds_iff s).mpr succeeds
  reflects s succeeds := (relayMap_succeeds_iff s).mp succeeds

/-- **The separation itself, read backwards**: since `relay` has a uniform translation into a
persistent calculus, it is not switchable. -/
theorem relay_not_switchable_by_separation : ¬ relaySource.Switchable := fun switchable =>
  no_uniformTranslation switchable relayTarget_persistent relayTranslation

end Relay

/-! ## Without the check of the knowledge: a program with no uniform translation into bags -/

section Maker

/-- `maker`: make `T` from nothing. -/
def maker : RuleInstance Expr := rule [] [] [factT]

/-- The program of that rule. -/
def makerProgram (r : RuleInstance Expr) : Prop := r = maker

/-- The step under it, success "a row `T` is present". -/
abbrev makerSource : ParallelCalculus :=
  stepCalculus ground (Prod.fst : Occ → Expr) makerProgram (· = factT)

/-- **Not switchable**, by monotonicity. -/
theorem maker_not_switchable : ¬ makerSource.Switchable :=
  not_switchable fun r isMaker c member => by
    rw [isMaker] at member
    simp [maker, rule] at member

/-- The empty store. -/
def empty : Conf := ⟨[], ∅⟩

/-- No rows, and knowledge equating `T` and `U`, which has no solution. -/
def unsolvable : Conf := ⟨[(factT, factU)], ∅⟩

/-- `maker`, making `T` with copy number `0`. -/
def makerAt : Fir := ⟨maker, [], ⟨[], [], [(factT, 0)]⟩⟩

/-- **The empty store succeeds**: `maker` fires. -/
theorem maker_empty_succeeds : makerSource.Succeeds empty := by
  have admitted : base.Admits (s := empty) makerAt :=
    (admits_of (D := fun _ _ _ _ => True) (σ := (empty, ∅)) (fresh := []) (by decide) (by decide) rfl rfl
      rfl (by decide) (by decide) rfl (no_checks rfl) trivial).1
  refine ⟨_, .single ⟨makerAt, rfl, admitted, rfl⟩, (factT, 0), ?_, rfl⟩
  change (factT, 0) ∈ fire empty.present (makerAt.selection.commit (T := Expr))
  rw [mem_fire]
  exact Or.inr (by simp [makerAt, Selection.commit])

/-- **The configuration with unsolvable knowledge never succeeds**: no firing is admitted there, and
it has no rows. -/
theorem unsolvable_never_succeeds : ¬ makerSource.Succeeds unsolvable := by
  rintro ⟨C', run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨f, -, admitted, -⟩, -⟩
  · obtain ⟨o, present, -⟩ := shows
    exact absurd present (Finset.notMem_empty o)
  · have problem := consistent_iff.mp (show f.Valid ground Prod.fst unsolvable from admitted).firing.consistent
    have same := problem (factT, factU) (by simp [Selection.problem, unsolvable])
    exact absurd same (by decide)

/-- **No uniform translation of `maker` into any calculus of positive bag rules.** -/
theorem maker_no_bag_translation {Γ : Rule Expr → Prop} (positive : ∀ ρ, Γ ρ → ρ.Positive) :
    IsEmpty (UniformTranslation makerSource (bagCalculus Γ)) := by
  refine ⟨fun τ => ?_⟩
  obtain ⟨m, image⟩ : ∃ m : Multiset Expr, τ.map empty = m := ⟨_, rfl⟩
  have unit : m = m + m := by
    have split := τ.homomorphic empty empty ⟨Finset.disjoint_empty_left _, ⟨(), fun _ member =>
      absurd member List.not_mem_nil⟩⟩
    have union : makerSource.par empty empty = empty := by
      show (unionOf empty empty) = empty
      simp [unionOf, empty]
    rw [union, image] at split
    exact split
  have zero : m = 0 := by
    have := congrArg Multiset.card unit
    rw [Multiset.card_add] at this
    exact Multiset.card_eq_zero.mp (by omega)
  have emptySucceeds := τ.preserves empty maker_empty_succeeds
  rw [image, zero] at emptySucceeds
  have everything := (bagCalculus_persistent positive).succeeds_par (τ.map unsolvable) emptySucceeds
  have beside : (bagCalculus Γ).par (0 : Multiset Expr) (τ.map unsolvable) = τ.map unsolvable :=
    zero_add (M := Multiset Expr) _
  rw [beside] at everything
  exact unsolvable_never_succeeds (τ.reflects unsolvable everything)

end Maker

#print axioms consistent_iff
#print axioms dropQueries_valid
#print axioms succeeds_congr
#print axioms succeeds_rename
#print axioms shift_involutive
#print axioms replay_beside
#print axioms succeeds_union_of_joint
#print axioms joint_of_ground
#print axioms joint_run_of_ground
#print axioms succeeds_union
#print axioms not_switchable
#print axioms switchable_has_absence_or_count
#print axioms counted_alone
#print axioms counted_beside
#print axioms counted_switchable
#print axioms relay_not_switchable
#print axioms relay_admitted
#print axioms relay_fires
#print axioms relay_succeeds_iff
#print axioms relayTarget_persistent
#print axioms relayTarget_succeeds_iff
#print axioms relayMap_succeeds_iff
#print axioms relayTranslation
#print axioms relay_not_switchable_by_separation
#print axioms maker_not_switchable
#print axioms maker_empty_succeeds
#print axioms unsolvable_never_succeeds
#print axioms maker_no_bag_translation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Monotone
