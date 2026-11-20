import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersAlong

/-!
# A rule that rewrites its own data, beside its own closed row, along the runs

`Readers.Counter.decRule` takes a row `value(ret($n))` and makes `value($n)`. It is not disciplined at
every state (`Readers.Counter.counter_not_disciplined`): beside the row `value($x)` holding the query's
own name, its firing tells that `$x` is `ret(…)`. From the start of every query it never fires
(`ReadersAlong.counter_never_fires`). Here it is started beside its own **closed** row `value((ret a))`
(`retARow`), where it fires (`counter_fires_closed`), and it meets the condition along the runs of the
union from that start, for every program and every query (`counter_along_closed`).

* `CounterRows w`: every present row of `w` is an alternative's row or an equation row (a node), or the
  row `value((ret a))`, or a row that every solution of the knowledge reads as `value(a)`. The start
  has it (`counter_start`), and every firing of the union keeps it (`counter_fire`): the rule takes only
  the row `value((ret a))` (`dec_takes_retA`), and the row it makes reads as `value(a)` at every solution.
* `dec_at`: at such a state every admitted firing of the rule takes no hosted row, tells nothing of them
  (its take is matched by `$n := a` whatever the solution), and makes a row that never reads as an
  alternative's row.

A negative example of `CounterRows`: the start beside the row `value($x)`, whose row reads as `value(t)`
for every closed `t` (`shared_not_counterRows`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersClosed

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.AlongRuns
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Readers
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersAlong
open Classical

/-- The closed row `value((ret a))`. -/
def retARow {V : Type} {A : V → MetaArity MSig} : Observation MSig A :=
  observe (valueN N (retN N (symAt "a")))

/-- The closed row `value(a)`. -/
def aRow {V : Type} {A : V → MetaArity MSig} : Observation MSig A := observe (valueN N (symAt "a"))

theorem inst_retARow {V W : Type} {A : V → MetaArity MSig} {E : W → MetaArity MSig} (σ : Assignment A E) :
    instantiateObservation σ (retARow (A := A)) = retARow := by
  show observe (instantiate σ (valueN N (retN N (symAt "a")))) = _
  rw [instantiate_valueN, instantiate_retN]
  rfl

/-- **The rows of the states the union with `decRule` reaches from the start beside `value((ret a))`.** -/
def CounterRows (w : HostState MSig) : Prop :=
  ∀ o ∈ w.present,
    (∃ (k : Tag) (args : Fin k.arity → Term (signature MSig w.frame.arity) [] ()),
      (k = .alt ∨ k = .eqn) ∧ w.label o = observe (N.node k args)) ∨
    w.label o = retARow ∨
    ∀ (B : Interface.Frames.Frame MSig) (σ : Assignment w.frame.arity B.arity),
      (Interface.Frames.contextual MSig).Models σ w.knowledge → instantiateObservation σ (w.label o) = aRow

/-- The start of a query beside the row `value((ret a))`. -/
abbrev closedStart (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) : HostState MSig :=
  startWith N P q retARow

/-- **The start has it.** -/
theorem counter_start (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) :
    CounterRows (closedStart P q) := by
  intro o present
  by_cases isRow : o = P.equations.length + 1
  · subst isRow
    refine .inr (.inl ?_)
    show Function.update (startLabel N P q) (P.equations.length + 1) retARow (P.equations.length + 1) = _
    rw [Function.update_self]
  · refine .inl ?_
    have label : (closedStart P q).label o = (Hosting.start N P q).label o := by
      show Function.update (startLabel N P q) (P.equations.length + 1) retARow o = startLabel N P q o
      rw [Function.update_of_ne isRow]
    have present' : o ∈ (Hosting.start N P q).present := by
      rcases Finset.mem_union.mp present with inside | inside
      · exact inside
      · exact absurd (Finset.mem_singleton.mp inside) isRow
    obtain ⟨k, args, tk, same⟩ := headedIn_start N P q o present'
    exact ⟨k, args, tk, label.trans same⟩

/-- A made row carries one of its rule's made rows, opened. -/
theorem made_label_mem {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)} {w : HostState MSig}
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) Prog w.frame}
    (shapes : f.Shapes (Interface.Frames.contextual MSig) w) {o : ℕ} (isMade : o ∈ f.selection.made) :
    ∃ p ∈ f.rule.body.produce,
      (f.result (Interface.Frames.contextual MSig) w).label o = instantiateObservation f.opening p := by
  have lengths : f.selection.made.length = (f.opened (Interface.Frames.contextual MSig)).produce.length := by
    simp only [RuleSyntax.Firing.opened, RuleInstance.map, List.length_map]
    exact shapes.2.2.2.2.2.1.symm
  have inRows := relabel_mem (Obj := Interface.Frames.Frame MSig) (Tm := RuleSyntax.Contextual.Terms MSig)
    (f.row (Interface.Frames.contextual MSig) w) f.selection.made _ lengths isMade
  simp only [RuleSyntax.Firing.opened, RuleInstance.map] at inRows
  obtain ⟨p, pIn, same⟩ := List.mem_map.mp inRows
  exact ⟨p, pIn, same.symm⟩

section Firing

variable {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)} {w : HostState MSig}
  {member : Counter.decRule ∈ Prog} {ext : (RuleSyntax.Contextual.declarations MSig).Ext w.frame}
  {opening : Assignment Counter.decRule.locals.arity ((RuleSyntax.Contextual.declarations MSig).target ext).arity}
  {o o' : ℕ} {seen : List (Finset ℕ)}

/-- The firing of `decRule` that takes `o` and makes `o'`. -/
abbrev decAt (member : Counter.decRule ∈ Prog) (ext : (RuleSyntax.Contextual.declarations MSig).Ext w.frame)
    (opening : Assignment Counter.decRule.locals.arity ((RuleSyntax.Contextual.declarations MSig).target ext).arity)
    (o o' : ℕ) (seen : List (Finset ℕ)) :
    RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) Prog w.frame :=
  ⟨Counter.decRule, member, ext, opening, ⟨[o], [], [o']⟩, seen⟩

theorem decAt_simple : Simple (decAt member ext opening o o' seen) o o'
    (observe (valueN N (retN N (unk .datum)))) (observe (valueN N (unk .datum))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The rule takes only the row `value((ret a))`.** -/
theorem dec_takes_retA (rows : CounterRows w)
    (admitted : (decAt member ext opening o o' seen).Admits (Interface.Frames.contextual MSig) w) :
    w.label o = retARow := by
  have oPresent : o ∈ w.present :=
    admitted.2.1.taken_subset (List.mem_toFinset.mpr (List.mem_singleton_self o))
  obtain ⟨B₁, u₁, solved₁⟩ := admitted.2.2.1
  obtain ⟨known₁, _, matched₁⟩ := simple_restrict decAt_simple u₁ solved₁
  rcases rows o oPresent with ⟨k, args, tk, label⟩ | isRet | reads
  · rw [label] at matched₁
    change observe (instantiate _ (valueN N (retN N (unk .datum)))) =
      observe (instantiate (Assignment.compose u₁ ((RuleSyntax.Contextual.declarations MSig).weaken ext))
        (N.node k args)) at matched₁
    rw [instantiate_valueN, N.instantiate_node
      (Assignment.compose u₁ ((RuleSyntax.Contextual.declarations MSig).weaken ext)) k args] at matched₁
    have isValue : Tag.value = k := N.tag_eq (observe_injective matched₁)
    subst isValue
    rcases tk with clash | clash <;> exact absurd clash (by decide)
  · exact isRet
  · have atA := reads B₁ _ known₁
    rw [← matched₁] at atA
    change observe (instantiate _ (valueN N (retN N (unk .datum)))) = observe (valueN N (symAt "a")) at atA
    rw [instantiate_valueN, instantiate_retN] at atA
    have inner := vec1_inj (N.args_eq (observe_injective atA))
    have tops := congrArg Flex.top inner
    have clash : (some (.tup 2) : Option (MOp ())) = some (.sym "a") := tops
    simp at clash

/-- **The row the rule makes reads as `value(a)` at every solution of its information.** -/
theorem dec_made_reads (rows : CounterRows w)
    (admitted : (decAt member ext opening o o' seen).Admits (Interface.Frames.contextual MSig) w)
    (B : Interface.Frames.Frame MSig) (σ : Assignment ((RuleSyntax.Contextual.declarations MSig).target ext).arity B.arity)
    (solved : (Interface.Frames.contextual MSig).Models σ
      ((decAt member ext opening o o' seen).information (Interface.Frames.contextual MSig) w)) :
    instantiateObservation σ (instantiateObservation opening (observe (valueN N (unk .datum)))) = aRow := by
  have isRet := dec_takes_retA rows admitted
  obtain ⟨_, _, matched⟩ := simple_restrict decAt_simple σ solved
  rw [isRet, inst_retARow] at matched
  change observe (instantiate _ (valueN N (retN N (unk .datum)))) =
    observe (valueN N (retN N (symAt "a"))) at matched
  rw [instantiate_valueN, instantiate_retN] at matched
  have atA := vec1_inj (N.args_eq (vec1_inj (N.args_eq (observe_injective matched))))
  show observe (instantiate σ (instantiate opening (valueN N (unk .datum)))) = _
  rw [instantiate_comp, instantiate_valueN]
  exact congrArg (fun t => observe (valueN N t)) atA

/-- **At such a state every admitted firing of the rule is apart from the hosted rows and makes a row
that never reads as an alternative's row.** -/
theorem dec_at (rows : CounterRows w) {P : SourceLanguage.Program mkeys [] () MTy} {n : ℕ}
    {b : Branch mkeys [] () MTy} {a : ℕ} {others : Finset ℕ} (beside : Beside N P n b w a others)
    (admitted : (decAt member ext opening o o' seen).Admits (Interface.Frames.contextual MSig) w) :
    Apart P a w (decAt member ext opening o o' seen) ∧
      NeverReads (IsAlternative N)
        ((decAt member ext opening o o' seen).result (Interface.Frames.contextual MSig) w) {o'} := by
  have isRet := dec_takes_retA rows admitted
  have oPresent : o ∈ w.present :=
    admitted.2.1.taken_subset (List.mem_toFinset.mpr (List.mem_singleton_self o))
  obtain ⟨B₁, u₁, solved₁⟩ := admitted.2.2.1
  obtain ⟨known₁, _, _⟩ := simple_restrict decAt_simple u₁ solved₁
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the taken row reads as `value((ret a))`; the hosted rows read as alternatives' and equation rows
    intro t taken hosted
    rw [List.mem_singleton.mp taken] at hosted
    rcases Finset.mem_insert.mp hosted with isA | small
    · subst isA
      obtain ⟨ρ, _, same⟩ := (beside.hosted.reads B₁ _).mp ⟨_, known₁, rfl⟩
      rw [isRet, inst_retARow] at same
      exact absurd (N.tag_eq (observe_injective same)) (by decide)
    · obtain ⟨θ, row⟩ := beside.hosted.rows B₁ _ known₁ o (Finset.mem_range.mp small)
      rw [isRet, inst_retARow] at row
      exact absurd (N.tag_eq (observe_injective row)) (by decide)
  · intro B g known
    obtain ⟨u, solved, _, onRows, _⟩ := simple_amalgamate decAt_simple admitted.1.1 oPresent g
      (fill (symAt "a") (symAt "a") (symAt "a") (symAt "a") (symAt "a")) known
      (fun _ member => absurd member List.not_mem_nil) (by
        rw [isRet, inst_retARow]
        show observe (instantiate _ (valueN N (retN N (unk .datum)))) = _
        rw [instantiate_valueN, instantiate_retN, instantiate_unk]
        rfl)
    exact ⟨u, solved, fun i inside => onRows i (beside.rows_sub N inside)⟩
  · intro i inside B σ _ reads
    rw [Finset.mem_singleton.mp inside, simple_label_made decAt_simple admitted.1] at reads
    obtain ⟨x, y, same⟩ := reads
    change observe (instantiate σ (instantiate opening (valueN N (unk .datum)))) = _ at same
    rw [instantiate_valueN, instantiate_valueN] at same
    exact absurd (N.tag_eq (observe_injective same)) (by decide)

end Firing

/-- **Every firing of the union keeps `CounterRows`.** -/
theorem counter_fire (P : SourceLanguage.Program mkeys [] () MTy) {w : HostState MSig} (rows : CounterRows w)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N P ∪ Counter.neighbour) w.frame}
    (admitted : f.Admits (Interface.Frames.contextual MSig) w) :
    CounterRows (f.result (Interface.Frames.contextual MSig) w) := by
  intro o present
  by_cases isMade : o ∈ f.selection.made
  · rcases f.member with hosted | isDec
    · obtain ⟨p, pIn, label⟩ := made_label_mem admitted.1 isMade
      obtain ⟨k, args, isAlt, rfl⟩ := translate_makes N P f.rule hosted p pIn
      refine .inl ⟨k, fun i => instantiate f.opening (args i), .inl isAlt, ?_⟩
      rw [label]
      show observe (instantiate f.opening (N.node k args)) = _
      rw [N.instantiate_node]
    · have rule : f.rule = Counter.decRule := isDec
      obtain ⟨rl, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
      simp only at rule
      subst rule
      have shapes := admitted.1
      obtain ⟨t, oneTake⟩ := List.length_eq_one_iff.mp shapes.2.2.2.1.symm
      have noRead : read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.1.symm
      obtain ⟨t', oneMade⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
      simp only at oneTake noRead oneMade
      subst oneTake noRead oneMade
      have isT' : o = t' := List.mem_singleton.mp isMade
      subst isT'
      refine .inr (.inr ?_)
      intro B σ solved
      rw [simple_label_made decAt_simple admitted.1]
      exact dec_made_reads rows admitted B σ solved
  · have old : o ∈ w.present := by
      rcases mem_fire.mp present with ⟨old, _⟩ | made
      · exact old
      · exact absurd (List.mem_toFinset.mp made) isMade
    rw [show (f.result (Interface.Frames.contextual MSig) w).label o = _ from
      RuleSyntax.Firing.result_label_other f isMade]
    rcases rows o old with ⟨k, args, tk, label⟩ | isRet | reads
    · refine .inl ⟨k, fun i => instantiate ((RuleSyntax.Contextual.declarations MSig).weaken f.ext) (args i), tk, ?_⟩
      show instantiateObservation _ (w.label o) = _
      rw [label]
      show observe (instantiate _ (N.node k args)) = _
      rw [N.instantiate_node]
    · refine .inr (.inl ?_)
      show instantiateObservation _ (w.label o) = _
      rw [isRet, inst_retARow]
    · refine .inr (.inr ?_)
      intro B σ solved
      show instantiateObservation σ (instantiateObservation _ (w.label o)) = _
      rw [instantiateObservation_comp]
      exact reads B _ (RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual MSig) f solved)

/-- Along the runs of the union from the closed start, the rows stay as `CounterRows` says. -/
theorem counter_run (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) {w : HostState MSig}
    (run : Relation.ReflTransGen (FiresIn (translate N P ∪ Counter.neighbour)) (closedStart P q) w) :
    CounterRows w := by
  induction run with
  | refl => exact counter_start P q
  | tail _ fires ih =>
      obtain ⟨f, admitted, rfl⟩ := fires
      exact counter_fire P ih admitted

/-- **The rule that rewrites its own data meets the condition along the runs from the start beside its
own closed row**, for every program and every query. -/
theorem counter_along_closed (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) :
    DisciplinedAlong N (D := D) P Counter.neighbour (closedStart P q) := by
  intro w reached n b a others f beside _ admitted
  have rows := counter_run P q reached
  have rule : f.rule = Counter.decRule := f.member
  obtain ⟨rl, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  simp only at rule
  subst rule
  have shapes := admitted.1
  obtain ⟨t, oneTake⟩ := List.length_eq_one_iff.mp shapes.2.2.2.1.symm
  have noRead : read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.1.symm
  obtain ⟨t', oneMade⟩ := List.length_eq_one_iff.mp shapes.2.2.2.2.2.1.symm
  simp only at oneTake noRead oneMade
  subst oneTake noRead oneMade
  obtain ⟨apart, quiet⟩ := dec_at rows beside admitted
  refine ⟨apart, ?_⟩
  rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  exact quiet

/-- **And it fires there**: at the start beside `value((ret a))` its firing on that row is admitted. -/
theorem counter_fires_closed (P : SourceLanguage.Program mkeys [] () MTy) (q : Comp mkeys [] () MTy) :
    ∃ w', FiresIn Counter.neighbour (closedStart P q) w' := by
  have present : P.equations.length + 1 ∈ (closedStart P q).present :=
    Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have label : (closedStart P q).label (P.equations.length + 1) = retARow := by
    show Function.update (startLabel N P q) (P.equations.length + 1) retARow (P.equations.length + 1) = _
    rw [Function.update_self]
  refine ⟨_, canonicalAt (closedStart P q) Counter.decRule (Set.mem_singleton _) (P.equations.length + 1),
    canonical_admits (Set.mem_singleton _) rfl rfl rfl rfl rfl (B := ⟨Empty, noNames⟩) present
      (startFill (closeNames [] (csym "a"))) (fill (symAt "a") (symAt "a") (symAt "a") (symAt "a") (symAt "a"))
      (fun _ member => absurd member List.not_mem_nil) (fun _ member => absurd member List.not_mem_nil) ?_, rfl⟩
  rw [label, inst_retARow]
  show observe (instantiate _ (valueN N (retN N (unk .datum)))) = _
  rw [instantiate_valueN, instantiate_retN, instantiate_unk]
  rfl

/-- **A negative example**: the start beside the row `value($x)`, which holds the query's own name, does
not have `CounterRows`: that row is neither a node of an alternative or an equation, nor
`value((ret a))`, and the solution `$x := (ret a)` reads it as `value((ret a))`, not as `value(a)`. -/
theorem shared_not_counterRows : ¬ CounterRows Counter.st := by
  intro rows
  rcases rows 1 (by decide) with ⟨k, args, tk, label⟩ | isRet | reads
  · rw [Counter.label_row] at label
    have tag : Tag.value = k := N.tag_eq (observe_injective label)
    subst tag
    rcases tk with clash | clash <;> exact absurd clash (by decide)
  · rw [Counter.label_row] at isRet
    have inner := vec1_inj (N.args_eq (observe_injective isRet))
    have tops := congrArg Flex.top inner
    have clash : (none : Option (MOp ())) = some (.tup 2) := tops
    simp at clash
  · have atRet := reads ⟨Empty, noNames⟩ Counter.gRet (Counter.st_known _)
    rw [Counter.label_row] at atRet
    change observe (instantiate Counter.gRet (valueN N (instantiate queryNames xName))) =
      observe (valueN N (symAt "a")) at atRet
    rw [instantiate_valueN, read_queryNames] at atRet
    have inner := vec1_inj (N.args_eq (observe_injective atRet))
    have tops := congrArg Flex.top inner
    have clash : (some (.tup 2) : Option (MOp ())) = some (.sym "a") := tops
    simp at clash

#print axioms inst_retARow
#print axioms counter_start
#print axioms made_label_mem
#print axioms dec_takes_retA
#print axioms dec_made_reads
#print axioms dec_at
#print axioms counter_fire
#print axioms counter_run
#print axioms counter_along_closed
#print axioms counter_fires_closed
#print axioms shared_not_counterRows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.ReadersClosed
