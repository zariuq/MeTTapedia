import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.NeighbourControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Knowledge

/-!
# Which reading neighbours are disciplined at every state

`Composition.Disciplined` and `AlongRuns.DisciplinedBothWays` are asked at **every** state that represents
an alternative beside rows that never read as alternatives' rows, not only at the states a run reaches.

**Instances.**

* `copyRule`: read **any** row `$R` (the pattern is one unknown) and make the row `value($R)`. It takes
  nothing and tells nothing. It is disciplined for every program (`copy_disciplined`), for both directions
  (`copy_both_ways`), and it reads hosted rows: `copy_reads_alternative` is its firing on the
  alternative's row of the start of any query.
* The union of two disciplined neighbours is disciplined (`disciplined_union`), for both directions too
  (`bothWays_union`); `observer_both_ways`: so is the program of the two rules `copyRule` and
  `Composition.spawnRule`.

**Rules that fail the every-state condition.**

* `Flex.readEqn_not_disciplined`: the rule `Controls.readEqn` (read a row `eqn($T)`, make `outside`). The
  state `Flex.flexState`: the start of the query `ret $x` of the program with no equation, with the
  knowledge `$F[$x] ≐ c` for a one-parameter unknown `$F`, beside the row `$F[eqn((g))]`. Its solutions
  are the projection `$F := x ↦ x` with `$x := c`, and the terms with top operator `c` with `$x` free
  (`Flex.solve`). The state represents the query's alternative beside that row (`Flex.flex_beside`), the
  row never reads as an alternative's row (`Flex.flex_quiet`), the rule's firing on the row is admitted
  (`Flex.read_fires`) and is not apart from the hosted rows (`Flex.read_not_apart`): reading the row as
  `eqn(…)` forces the projection, which tells `$x ≐ c`.
* `Counter.counter_not_disciplined`: the rule `Counter.decRule` (take `value(ret($n))`, make `value($n)`),
  which rewrites its own data. At the start of the query `ret $x` beside the row `value($x)`, which holds
  the query's own name, its firing is admitted (`Counter.dec_fires`) and is not apart
  (`Counter.dec_not_apart`): the take tells that `$x` is `ret(…)`.

Both failures are at states that a run of the union reaches only if it starts there. The condition
asked along the runs from the start of every query holds of both rules (`ReadersAlong`; for `decRule`
with no firing there), and `decRule` started beside its own closed row `value((ret a))` fires and meets
it (`ReadersClosed`); from the two states above it fails at once (`Flex.readEqn_not_along`,
`Counter.counter_not_along`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
open Classical

/-! ## A rule that reads any row -/

section Copy

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-- A neighbour's rule: read any row `$R`, make `value($R)`. -/
def copyRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S) where
  locals := controlFrame Γ star
  body := { take := [], read := [observe (unk .datum)], tell := [], checks := [],
            produce := [observe (valueN N (unk .datum))] }
  collect := []

/-- **A solution of the knowledge extends to a solution of the reading firing's information that reads
every row of the state as before**: reading a row by a pattern that is one unknown tells nothing of
it. -/
theorem copy_amalgamate {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {w : HostState S}
    {member : copyRule N ∈ Prog} {ext : (RuleSyntax.Contextual.declarations S).Ext w.frame}
    {opening : Assignment (copyRule N).locals.arity ((RuleSyntax.Contextual.declarations S).target ext).arity}
    {o o' : ℕ} {seen : List (Finset ℕ)}
    (fresh : RuleSyntax.Firing.Fresh (Interface.Frames.contextual S) w
      (⟨copyRule N, member, ext, opening, ⟨[], [o], [o']⟩, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame))
    (present : o ∈ w.present) {t₀ : Term (signature S w.frame.arity) Γ star} (label : w.label o = observe t₀)
    {B : Interface.Frames.Frame S} (g : Assignment w.frame.arity B.arity)
    (known : (Interface.Frames.contextual S).Models g w.knowledge) :
    ∃ u : Assignment ((RuleSyntax.Contextual.declarations S).target ext).arity B.arity,
      (Interface.Frames.contextual S).Models u
        (RuleSyntax.Firing.information (Interface.Frames.contextual S) w
          (⟨copyRule N, member, ext, opening, ⟨[], [o], [o']⟩, seen⟩ :
            RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog w.frame)) ∧
      ∀ i ∈ w.present, instantiateObservation u
          (instantiateObservation ((RuleSyntax.Contextual.declarations S).weaken ext) (w.label i)) =
        instantiateObservation g (w.label i) := by
  obtain ⟨u, onState, onRule⟩ := fresh B g
    (fill (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀))
  have state : ∀ t, w.Mentions t →
      instantiateObservation u (instantiateObservation ((RuleSyntax.Contextual.declarations S).weaken ext) t) =
        instantiateObservation g t := onState
  have patTerm : (observe (unk .datum) : Observation S (unknownArity Γ star)) ∈ (copyRule N).terms :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))))
  have onPat : instantiateObservation u (instantiateObservation opening (observe (unk .datum))) =
      instantiateObservation
        (fill (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀) (instantiate g t₀))
        (observe (unk .datum)) := onRule _ patTerm
  refine ⟨u, ?_, fun i inside => state _ (Or.inr (Or.inr ⟨i, inside, rfl⟩))⟩
  intro e inside
  have inside' : e ∈ ((Interface.Frames.contextual S).applyStore
        ((RuleSyntax.Contextual.declarations S).weaken ext) w.knowledge ++ [] ++
      [(instantiateObservation opening (observe (unk .datum)),
        instantiateObservation ((RuleSyntax.Contextual.declarations S).weaken ext) (w.label o))]) ++ [] := inside
  rcases List.mem_append.mp inside' with front | none
  · rcases List.mem_append.mp front with front' | read
    · rcases List.mem_append.mp front' with old | none
      · obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp old
        change instantiateObservation u (instantiateObservation _ original.1) =
          instantiateObservation u (instantiateObservation _ original.2)
        rw [state _ (Or.inl (List.mem_map_of_mem inStore)), state _ (Or.inr (Or.inl (List.mem_map_of_mem inStore)))]
        exact known original inStore
      · cases none
    · rw [List.mem_singleton.mp read]
      change instantiateObservation u (instantiateObservation opening (observe (unk .datum))) =
        instantiateObservation u (instantiateObservation _ (w.label o))
      rw [onPat, state _ (Or.inr (Or.inr ⟨o, present, rfl⟩)), label]
      show observe (instantiate _ (unk .datum)) = observe (instantiate g t₀)
      rw [instantiate_unk]
      rfl
  · cases none

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}

/-- **The reading rule is disciplined**, for every program. -/
theorem copy_disciplined :
    Disciplined N P ({copyRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) := by
  intro n b w a others f beside _ admitted
  have rule : f.rule = copyRule N := f.member
  obtain ⟨rl, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  have noTake : taken = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  obtain ⟨o, oneRead⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.1.symm
  obtain ⟨o', oneMade⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
  simp only at oneRead oneMade
  subst noTake oneRead oneMade
  have oPresent : o ∈ w.present :=
    admitted.2.1.kept_subset (List.mem_toFinset.mpr (List.mem_singleton_self o))
  obtain ⟨B₁, u₁, solved₁⟩ := admitted.2.2.1
  have readEq : instantiateObservation u₁ (instantiateObservation opening (observe (unk .datum))) =
      instantiateObservation u₁
        (instantiateObservation ((RuleSyntax.Contextual.declarations S).weaken ext) (w.label o)) :=
    RuleSyntax.Firing.read_solved (X := Interface.Frames.contextual S) _ solved₁
      (p := instantiateObservation opening (observe (unk .datum))) (o := o) (List.mem_singleton_self _)
  rcases hlabel : w.label o with ⟨ctx, sort, t₀⟩
  rw [hlabel] at readEq
  obtain ⟨rfl, rest⟩ := Sigma.mk.inj readEq
  obtain ⟨rfl, _⟩ := Sigma.mk.inj (eq_of_heq rest)
  refine ⟨⟨fun i inside => absurd inside List.not_mem_nil, ?_⟩, ?_⟩
  · intro B g known
    obtain ⟨u, solved, onRows⟩ := copy_amalgamate N shapes.1 oPresent hlabel g known
    exact ⟨u, solved, fun i inside => onRows i (beside.rows_sub N inside)⟩
  · intro i inside B σ _ reads
    rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at inside
    subst inside
    have label : (RuleSyntax.Firing.result (Interface.Frames.contextual S) w
        (⟨copyRule N, member, ext, opening, ⟨[], [o], [i]⟩, seen⟩ :
          RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) {copyRule N} w.frame)).label i =
        instantiateObservation opening (observe (valueN N (unk .datum))) := by
      apply RuleSyntax.Firing.result_label_made _ shapes
      simp only [RuleSyntax.Firing.opened, RuleInstance.map, copyRule, List.map_cons, List.map_nil,
        List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
      rfl
    rw [label] at reads
    obtain ⟨x, y, same⟩ := reads
    change observe (instantiate σ (instantiate opening (valueN N (unk .datum)))) = _ at same
    rw [instantiate_valueN, instantiate_valueN] at same
    exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-- The row the reading rule makes never reads as an equation row. -/
theorem copy_made_quiet {w : HostState S}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S)
      ({copyRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) w.frame)
    (admitted : f.Admits (Interface.Frames.contextual S) w) :
    NeverReads (IsEquationRow N) (f.result (Interface.Frames.contextual S) w) f.selection.made.toFinset := by
  have rule : f.rule = copyRule N := f.member
  obtain ⟨rl, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  obtain ⟨o', oneMade⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
  simp only at oneMade
  subst oneMade
  intro i inside B σ _ reads
  rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at inside
  subst inside
  have label : (RuleSyntax.Firing.result (Interface.Frames.contextual S) w
      (⟨copyRule N, member, ext, opening, ⟨taken, read, [i]⟩, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) {copyRule N} w.frame)).label i =
      instantiateObservation opening (observe (valueN N (unk .datum))) := by
    apply RuleSyntax.Firing.result_label_made _ shapes
    simp only [RuleSyntax.Firing.opened, RuleInstance.map, copyRule, List.map_cons, List.map_nil,
      List.zip_cons_cons, List.zip_nil_left, List.mem_singleton]
    rfl
  rw [label] at reads
  obtain ⟨x, same⟩ := reads
  change observe (instantiate σ (instantiate opening (valueN N (unk .datum)))) = _ at same
  rw [instantiate_valueN, instantiate_valueN] at same
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-- **The reading rule is disciplined for both directions**, for every program. -/
theorem copy_both_ways :
    DisciplinedBothWays N P ({copyRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) :=
  bothWays_of_disciplined N (copy_disciplined N) (fun f _ _ admitted => copy_made_quiet N f admitted)

/-- **The union of two disciplined neighbours is disciplined.** -/
theorem disciplined_union {R₁ R₂ : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (d₁ : Disciplined N P R₁) (d₂ : Disciplined N P R₂) : Disciplined N P (R₁ ∪ R₂) := by
  intro n b w a others f beside quiet admitted
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  rcases member with left | right
  · obtain ⟨apart, made⟩ := d₁ ⟨rule, left, ext, opening, selection, seen⟩ beside quiet admitted
    exact ⟨⟨apart.taken, apart.conservative⟩, made⟩
  · obtain ⟨apart, made⟩ := d₂ ⟨rule, right, ext, opening, selection, seen⟩ beside quiet admitted
    exact ⟨⟨apart.taken, apart.conservative⟩, made⟩

/-- **The union of two neighbours disciplined for both directions is disciplined for both
directions.** -/
theorem bothWays_union {R₁ R₂ : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (d₁ : DisciplinedBothWays N P R₁) (d₂ : DisciplinedBothWays N P R₂) :
    DisciplinedBothWays N P (R₁ ∪ R₂) := by
  intro w n b a others f beside quietAlt quietEqn admitted
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  rcases member with left | right
  · obtain ⟨apart, madeAlt, madeEqn⟩ :=
      d₁ w ⟨rule, left, ext, opening, selection, seen⟩ beside quietAlt quietEqn admitted
    exact ⟨⟨apart.taken, apart.conservative⟩, madeAlt, madeEqn⟩
  · obtain ⟨apart, madeAlt, madeEqn⟩ :=
      d₂ w ⟨rule, right, ext, opening, selection, seen⟩ beside quietAlt quietEqn admitted
    exact ⟨⟨apart.taken, apart.conservative⟩, madeAlt, madeEqn⟩

/-- **A disciplined neighbour of two rules, one of which reads hosted rows.** -/
theorem observer_disciplined :
    Disciplined N P (({copyRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) ∪ {spawnRule N}) :=
  disciplined_union N (copy_disciplined N) (spawn_disciplined N)

/-- **The same neighbour is disciplined for both directions.** -/
theorem observer_both_ways :
    DisciplinedBothWays N P
      (({copyRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) ∪ {spawnRule N}) :=
  bothWays_union N (copy_both_ways N) (NeighbourControls.spawn_both_ways N)

/-- **The reading rule fires on the alternative's row** of the start of every query: it reads a hosted
row. -/
theorem copy_reads_alternative {Ty : Type} (Q : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) :
    ∃ f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S)
        ({copyRule N} : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) (start N Q q).frame,
      f.Admits (Interface.Frames.contextual S) (start N Q q) ∧ f.selection.read = [Q.equations.length] := by
  have present : Q.equations.length ∈ (start N Q q).present := Finset.mem_insert_self _ _
  have label : (start N Q q).label Q.equations.length =
      observe (encAlt N (instantiate queryNames) (.eval q) []) := by
    simp [start, startLabel]
  have fresh := RuleSyntax.Contextual.canonical_fresh (start N Q q) (copyRule N)
    (Set.mem_singleton (copyRule N)) ⟨[], [Q.equations.length], [freshId (start N Q q)]⟩ []
  obtain ⟨u, solved, _⟩ := copy_amalgamate N fresh present label
    (B := startFrame κ) (fun x => generator (startArity κ) x) (fun _ inside => absurd inside List.not_mem_nil)
  exact ⟨_, ⟨⟨fresh, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
    Controls.enabled_read present (freshId_not_mem _), ⟨_, u, solved⟩, entails_of_no_checks rfl rfl⟩, rfl⟩

end Copy

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-! ## The reading rule `readEqn` at a state with a one-parameter unknown -/

namespace Flex

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Knowledge
  (represents_of_same_joint_readings B₀)

/-- The top operator of a term, when it is one of the signature's. -/
def top {X : Type} {T : X → MetaArity MSig} {Δ : Ctx MSig} : Term (signature MSig T) Δ () → Option (MOp ())
  | .op (.inl o) _ => some o
  | _ => none

/-- The one-parameter body `t` applied to `a`. -/
abbrev applied {X : Type} {T : X → MetaArity MSig} (t : Term (signature MSig T) [()] ())
    (a : Term (signature MSig T) [] ()) : Term (signature MSig T) [] () :=
  bind (argsToSub (S := signature MSig T) (bs := [()]) (Γ := []) (.cons a .nil)) t

/-- **What solves `$F[a] ≐ c`**: the projection, with `a = c`; or a body whose top operator is `c`,
whatever it is applied to. -/
theorem solve {X : Type} {T : X → MetaArity MSig} (t : Term (signature MSig T) [()] ())
    (a : Term (signature MSig T) [] ()) (eq : applied t a = symAt "c") :
    (t = .var .zero ∧ a = symAt "c") ∨
      ∀ a' : Term (signature MSig T) [] (), top (applied t a') = some (.sym "c") := by
  cases t with
  | var v =>
      cases v with
      | zero => exact .inl ⟨rfl, eq⟩
      | succ w => cases w
  | op o args =>
      cases o with
      | inl mo =>
          refine .inr fun a' => ?_
          have tops : (some mo : Option (MOp ())) = some (.sym "c") := congrArg top eq
          exact tops
      | inr u =>
          have tops : (none : Option (MOp ())) = some (.sym "c") := congrArg top eq
          cases tops

/-- The neighbour's row `$F[eqn((g))]`. -/
def flexRow : Observation MSig (startArity mkeys) :=
  observe (instantiate queryNames (hoD [] [9] 0 (eqnN N gT)))

/-- The start of the query `ret $x` beside that row, with the knowledge `$F[$x] ≐ c`. -/
def flexState : HostState MSig :=
  ⟨startFrame mkeys,
    [(observe (instantiate queryNames (hoD [] [9] 0 xName)), observe (instantiate queryNames cT))],
    (startWith N P0 qx flexRow).present, (startWith N P0 qx flexRow).label⟩

theorem label_alt : flexState.label 0 = (Hosting.start N P0 qx).label 0 := by
  have ne : (0 : ℕ) ≠ P0.equations.length + 1 := by decide
  show Function.update (startLabel N P0 qx) (P0.equations.length + 1) flexRow 0 = _
  rw [Function.update_of_ne ne]
  rfl

theorem label_row : flexState.label 1 = flexRow := by
  show Function.update (startLabel N P0 qx) (P0.equations.length + 1) flexRow (P0.equations.length + 1) = _
  rw [Function.update_self]

/-- What the knowledge says of a solution. -/
theorem known_iff {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models σ flexState.knowledge ↔
      applied (σ (.inl (ho [] [9] 0))) (instantiate (fun x => σ (.inl x)) xName) = symAt "c" := by
  constructor
  · intro solved
    have same : observe (instantiate σ (instantiate queryNames (hoD [] [9] 0 xName))) =
        observe (instantiate σ (instantiate queryNames cT)) := solved _ (List.mem_singleton_self _)
    have terms := observe_injective same
    rw [read_queryNames, read_queryNames] at terms
    exact terms
  · intro eq e member
    rw [List.mem_singleton.mp member]
    show observe (instantiate σ (instantiate queryNames (hoD [] [9] 0 xName))) =
      observe (instantiate σ (instantiate queryNames cT))
    rw [read_queryNames, read_queryNames]
    exact congrArg observe eq

/-- The neighbour's row, read by an instantiation of the start's names. -/
theorem reads_flex {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    instantiateObservation σ (flexState.label 1) =
      observe (applied (σ (.inl (ho [] [9] 0))) (eqnN N (instantiate (fun x => σ (.inl x)) gT))) := by
  rw [label_row]
  show observe (instantiate σ (instantiate queryNames (hoD [] [9] 0 (eqnN N gT)))) = _
  rw [read_queryNames, instantiate_hoD, instantiate_eqnN]

/-- A solution from any instantiation: every one-parameter name of the query is read as the constant
`c`; every other name as before. -/
def constant {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    Assignment (startArity mkeys) B.arity
  | .inl ⟨_, ⟨_, _, ([()], ())⟩⟩ => symAt "c"
  | y => σ y

theorem constant_known {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models (constant σ) flexState.knowledge :=
  (known_iff (constant σ)).mpr rfl

theorem start_present : (Hosting.start N P0 qx).present = {0} := by decide

/-- **The state represents the query's alternative beside the row.** -/
theorem flex_beside : Beside N P0 0 (initialBranch qx) flexState 0 {1} := by
  refine ⟨?_, rfl, by decide⟩
  refine represents_of_same_joint_readings N (start_represents N P0 qx qx_unopened) rfl ?_ ?_
  · intro B σ _
    refine ⟨constant σ, constant_known σ, ?_⟩
    intro o inside
    have isZero : o = 0 := by
      rw [start_present] at inside
      exact Finset.mem_singleton.mp inside
    subst isZero
    show instantiateObservation (constant σ) (flexState.label 0) =
      instantiateObservation σ ((Hosting.start N P0 qx).label 0)
    rw [label_alt, start_qx_reads, start_qx_reads]
    rfl
  · intro B σ' _
    refine ⟨σ', fun _ member => absurd member List.not_mem_nil, ?_⟩
    intro o inside
    have isZero : o = 0 := by
      rw [start_present] at inside
      exact Finset.mem_singleton.mp inside
    subst isZero
    show instantiateObservation σ' ((Hosting.start N P0 qx).label 0) = instantiateObservation σ' (flexState.label 0)
    rw [label_alt]

/-- **The row never reads as an alternative's row**: it reads as `eqn((g))`, or as a term whose top
operator is `c`. -/
theorem flex_quiet : NeverReads (IsAlternative N) flexState {1} := by
  intro o inside B σ known reads
  obtain ⟨x, y, same⟩ := reads
  rw [Finset.mem_singleton.mp inside, reads_flex] at same
  have terms := observe_injective same
  rcases solve _ _ ((known_iff σ).mp known) with ⟨isVar, _⟩ | tops
  · rw [isVar] at terms
    exact absurd (N.tag_eq terms) (by decide)
  · have both := congrArg top terms
    rw [tops] at both
    have clash : (some (.sym "c") : Option (MOp ())) = some (.tup 3) := both
    simp at clash

/-- The firing of `readEqn` that reads the row. -/
def readF : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig)
    ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) flexState.frame :=
  RuleSyntax.Contextual.canonical (F := flexState.frame) readEqn (Set.mem_singleton _) ⟨[], [1], [freshId flexState]⟩ []

theorem readF_fresh : readF.Fresh (Interface.Frames.contextual MSig) flexState :=
  RuleSyntax.Contextual.canonical_fresh flexState readEqn (Set.mem_singleton _) _ _

theorem present1 : (1 : ℕ) ∈ flexState.present := by decide

/-- The projection: every one-parameter name is the identity, every other name is `c`. -/
def projection : Assignment (fam mkeys) B₀.arity
  | ⟨_, ⟨_, _, ([()], ())⟩⟩ => .var .zero
  | ⟨_, ⟨_, _, (_, _)⟩⟩ => symAt "c"

/-- The constant solution with `$x := d`: every one-parameter name is `c`, every other name is `d`. -/
def constantD : Assignment (fam mkeys) B₀.arity
  | ⟨_, ⟨_, _, ([()], ())⟩⟩ => symAt "c"
  | ⟨_, ⟨_, _, (_, _)⟩⟩ => symAt "d"

theorem projection_known : (Interface.Frames.contextual MSig).Models (startFill projection) flexState.knowledge :=
  (known_iff (startFill projection)).mpr rfl

theorem constantD_known : (Interface.Frames.contextual MSig).Models (startFill constantD) flexState.knowledge :=
  (known_iff (startFill constantD)).mpr rfl

/-- **The reading rule fires on the row**: at the projection the row reads as `eqn((g))`. -/
theorem read_fires : readF.Admits (Interface.Frames.contextual MSig) flexState := by
  obtain ⟨u, onState, onRule⟩ := readF_fresh B₀ (startFill projection)
    (fill (instantiate projection gT) (instantiate projection gT) (instantiate projection gT)
      (instantiate projection gT) (instantiate projection gT))
  have state : ∀ t, flexState.Mentions t →
      instantiateObservation u (instantiateObservation
        ((RuleSyntax.Contextual.declarations MSig).weaken readF.ext) t) =
        instantiateObservation (startFill projection) t := onState
  have patTerm : (observe (eqnN N (unk .datum)) : Observation MSig (unknownArity (S := MSig) [] ())) ∈
      readEqn.terms :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))))
  have onPat : instantiateObservation u (instantiateObservation readF.opening (observe (eqnN N (unk .datum)))) =
      instantiateObservation
        (fill (instantiate projection gT) (instantiate projection gT) (instantiate projection gT)
          (instantiate projection gT) (instantiate projection gT))
        (observe (eqnN N (unk .datum))) := onRule _ patTerm
  refine ⟨⟨readF_fresh, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
    enabled_read present1 (freshId_not_mem flexState), ⟨_, u, ?_⟩, entails_of_no_checks rfl rfl⟩
  intro e inside
  have inside' : e ∈ ((Interface.Frames.contextual MSig).applyStore
        ((RuleSyntax.Contextual.declarations MSig).weaken readF.ext) flexState.knowledge ++ [] ++
      [(instantiateObservation readF.opening (observe (eqnN N (unk .datum))),
        instantiateObservation ((RuleSyntax.Contextual.declarations MSig).weaken readF.ext)
          (flexState.label 1))]) ++ [] := inside
  rcases List.mem_append.mp inside' with front | none
  · rcases List.mem_append.mp front with front' | read
    · rcases List.mem_append.mp front' with old | none
      · obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp old
        change instantiateObservation u (instantiateObservation _ original.1) =
          instantiateObservation u (instantiateObservation _ original.2)
        rw [state _ (Or.inl (List.mem_map_of_mem inStore)), state _ (Or.inr (Or.inl (List.mem_map_of_mem inStore)))]
        exact projection_known original inStore
      · cases none
    · rw [List.mem_singleton.mp read]
      change instantiateObservation u (instantiateObservation readF.opening (observe (eqnN N (unk .datum)))) =
        instantiateObservation u (instantiateObservation _ (flexState.label 1))
      rw [onPat, state _ (Or.inr (Or.inr ⟨1, present1, rfl⟩)), reads_flex]
      show observe (instantiate _ (eqnN N (unk .datum))) = _
      rw [instantiate_eqnN, instantiate_unk]
      rfl
  · cases none

/-- **The firing is not apart from the hosted rows**: every solution of its information reads the row
as `eqn(…)`, so it is the projection, and reads `$x` as `c`; the solution with `$x := d` of the
knowledge has no extension that reads the alternative's row alike. -/
theorem read_not_apart : ¬ Apart P0 0 flexState readF := by
  intro apart
  obtain ⟨u, solved, onRows⟩ := apart.conservative B₀ (startFill constantD) constantD_known
  have known := RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual MSig) readF solved
  have row0 : instantiateObservation
      (Assignment.compose u ((RuleSyntax.Contextual.declarations MSig).weaken readF.ext)) (flexState.label 0) =
      instantiateObservation (startFill constantD) (flexState.label 0) :=
    (instantiateObservation_comp _ _ _).symm.trans (onRows 0 (by decide))
  rw [label_alt, start_qx_reads, start_qx_reads] at row0
  have atX := vec1_inj (N.args_eq (vec1_inj (N.args_eq (vec2_inj (N.args_eq (observe_injective row0))).1)))
  have isD : instantiate (fun x => startFill constantD (.inl x)) xName =
      (symAt "d" : Term (signature MSig B₀.arity) [] ()) := rfl
  have readEq : instantiateObservation u (instantiateObservation readF.opening (observe (eqnN N (unk .datum)))) =
      instantiateObservation u
        (instantiateObservation ((RuleSyntax.Contextual.declarations MSig).weaken readF.ext) (flexState.label 1)) :=
    RuleSyntax.Firing.read_solved (X := Interface.Frames.contextual MSig) readF solved
      (p := instantiateObservation readF.opening (observe (eqnN N (unk .datum)))) (o := 1)
      (List.mem_singleton_self _)
  rw [instantiateObservation_comp _ _ (flexState.label 1), reads_flex] at readEq
  change observe (instantiate u (instantiate readF.opening (eqnN N (unk .datum)))) = _ at readEq
  rw [instantiate_eqnN, instantiate_eqnN] at readEq
  have terms := observe_injective readEq
  rcases solve _ _ ((known_iff _).mp known) with ⟨_, isC⟩ | tops
  · have clash : (symAt "d" : Term (signature MSig B₀.arity) [] ()) = symAt "c" :=
      isD.symm.trans (atX.symm.trans isC)
    simp [symAt] at clash
  · have both := congrArg top terms
    have clash : (some (.tup 2) : Option (MOp ())) = some (.sym "c") := both.trans (tops _)
    simp at clash

/-- **The reading rule is not disciplined** for the program with no equation. -/
theorem readEqn_not_disciplined :
    ¬ Disciplined N (D := D) P0 ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) :=
  fun disciplined => read_not_apart (disciplined readF flex_beside flex_quiet read_fires).1

/-- **Nor along the runs from that state**: it fails at the state itself. -/
theorem readEqn_not_along :
    ¬ DisciplinedAlong N (D := D) P0 ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig))
      flexState :=
  fun along => read_not_apart (along flexState .refl readF flex_beside flex_quiet read_fires).1

end Flex

/-! ## A rule that rewrites its own data -/

namespace Counter

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Knowledge (B₀)

/-- A neighbour's rule that computes on its own data: take `value(ret($n))`, make `value($n)`. -/
def decRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms MSig) where
  locals := controlFrame [] ()
  body := { take := [observe (valueN N (retN N (unk .datum)))], read := [], tell := [], checks := [],
            produce := [observe (valueN N (unk .datum))] }
  collect := []

/-- The neighbour's program: that one rule. -/
abbrev neighbour : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig) := {decRule}

/-- The neighbour's row `value($x)`, holding the query's own name. -/
def sharedValue : Observation MSig (startArity mkeys) := observe (valueN N (instantiate queryNames xName))

/-- The start of the query `ret $x` with that row. -/
abbrev st : HostState MSig := startWith N P0 qx sharedValue

theorem st_beside : Beside N P0 0 (initialBranch qx) st 0 {1} :=
  startWith_beside N (P := P0) qx sharedValue qx_unopened

theorem label_row : st.label 1 = sharedValue := by
  show Function.update (startLabel N P0 qx) (P0.equations.length + 1) sharedValue (P0.equations.length + 1) = _
  rw [Function.update_self]

theorem label_alt : st.label 0 = (Hosting.start N P0 qx).label 0 := by
  have ne : (0 : ℕ) ≠ P0.equations.length + 1 := by decide
  show Function.update (startLabel N P0 qx) (P0.equations.length + 1) sharedValue 0 = _
  rw [Function.update_of_ne ne]
  rfl

theorem st_quiet : NeverReads (IsAlternative N) st {1} := by
  intro o inside B σ _ reads
  obtain ⟨x, y, same⟩ := reads
  rw [Finset.mem_singleton.mp inside, label_row] at same
  change observe (instantiate σ (valueN N (instantiate queryNames xName))) = _ at same
  rw [instantiate_valueN] at same
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-- The firing of the neighbour's rule on the row `value($x)`. -/
def decFiring : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) neighbour st.frame :=
  canonicalAt st decRule (Set.mem_singleton _) 1

/-- `$x := (ret a)`. -/
def gRet : Assignment (startArity mkeys) B₀.arity :=
  startFill (closeNames [(([], [7], 0), ctuple [csym "ret", csym "a"])] (csym "a"))

/-- `$x := a`. -/
def gA : Assignment (startArity mkeys) B₀.arity := startFill (closeNames [] (csym "a"))

theorem st_known (g : Assignment (startArity mkeys) B₀.arity) :
    (Interface.Frames.contextual MSig).Models g st.knowledge :=
  fun _ member => absurd member List.not_mem_nil

theorem dec_matched :
    instantiateObservation (fill (symAt "a") (symAt "a") (symAt "a") (symAt "a") (symAt "a") :
        Assignment (unknownArity (S := MSig) [] ()) B₀.arity)
      (observe (valueN N (retN N (unk .datum)))) = instantiateObservation gRet (st.label 1) := by
  rw [label_row]
  show observe (instantiate _ (valueN N (retN N (unk .datum)))) =
    observe (instantiate gRet (valueN N (instantiate queryNames xName)))
  rw [instantiate_valueN, instantiate_retN, instantiate_unk, instantiate_valueN, read_queryNames]
  rfl

/-- **The neighbour's rule fires on its row.** -/
theorem dec_fires : decFiring.Admits (Interface.Frames.contextual MSig) st :=
  canonical_admits (Set.mem_singleton _) rfl rfl rfl rfl rfl (B := B₀) (by decide) gRet
    (fill (symAt "a") (symAt "a") (symAt "a") (symAt "a") (symAt "a")) (st_known _)
    (fun _ member => absurd member List.not_mem_nil) dec_matched

/-- **The firing is not apart from the hosted rows**: no solution of its information reads the
alternative's row as the solution `$x := a` of the knowledge does. -/
theorem dec_not_apart : ¬ Apart P0 0 st decFiring := by
  intro apart
  obtain ⟨u, solved, onRows⟩ := apart.conservative B₀ gA (st_known gA)
  have simple : Simple decFiring 1 (freshId st) (observe (valueN N (retN N (unk .datum))))
      (observe (valueN N (unk .datum))) := canonical_simple rfl rfl rfl
  obtain ⟨_, _, matched⟩ := simple_restrict simple u solved
  have row0 : instantiateObservation
      (Assignment.compose u ((RuleSyntax.Contextual.declarations MSig).weaken decFiring.ext)) (st.label 0) =
      instantiateObservation gA (st.label 0) :=
    (instantiateObservation_comp _ _ _).symm.trans (onRows 0 (by decide))
  rw [label_alt, start_qx_reads, start_qx_reads] at row0
  have atX := vec1_inj (N.args_eq (vec1_inj (N.args_eq (vec2_inj (N.args_eq (observe_injective row0))).1)))
  rw [label_row] at matched
  change observe (instantiate _ (valueN N (retN N (unk .datum)))) =
    observe (instantiate _ (valueN N (instantiate queryNames xName))) at matched
  rw [instantiate_valueN, instantiate_retN, instantiate_valueN, read_queryNames] at matched
  have isRet := vec1_inj (N.args_eq (observe_injective matched))
  have isA : instantiate (fun x => gA (.inl x)) xName = (symAt "a" : Term (signature MSig B₀.arity) [] ()) := rfl
  have clash := (isRet.trans atX).trans isA
  have heads := congrArg headSymbol clash
  have none : (some "ret" : Option String) = none := heads
  exact Option.some_ne_none _ none

/-- **The rule is not disciplined**: `Disciplined` is asked at this state too. -/
theorem counter_not_disciplined : ¬ Disciplined N (D := D) P0 neighbour :=
  fun disciplined => dec_not_apart (disciplined decFiring st_beside st_quiet dec_fires).1

/-- **Nor along the runs from this start**: it fails at the start itself. -/
theorem counter_not_along : ¬ DisciplinedAlong N (D := D) P0 neighbour st :=
  fun along => dec_not_apart (along st .refl decFiring st_beside st_quiet dec_fires).1

end Counter

#print axioms copy_amalgamate
#print axioms copy_disciplined
#print axioms copy_made_quiet
#print axioms copy_both_ways
#print axioms disciplined_union
#print axioms bothWays_union
#print axioms observer_disciplined
#print axioms observer_both_ways
#print axioms copy_reads_alternative
#print axioms Flex.solve
#print axioms Flex.flex_beside
#print axioms Flex.flex_quiet
#print axioms Flex.read_fires
#print axioms Flex.read_not_apart
#print axioms Flex.readEqn_not_disciplined
#print axioms Flex.readEqn_not_along
#print axioms Counter.dec_fires
#print axioms Counter.dec_not_apart
#print axioms Counter.counter_not_disciplined
#print axioms Counter.counter_not_along

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readers
