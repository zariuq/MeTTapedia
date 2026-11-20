import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Bisimulation

/-!
# A program held in the store, run for two steps through the interpreter

**The data fragment** (`DataFragment`): rules of the fragment whose made rows are data rows. It is closed
under what its rules make (`dataFragment_closed`), so the bisimulation applies to it.

**Two rules**, both with their own unknowns:
* `first` takes a token `obj (tok x)`, reads a key `obj (key y)`, tells `x = y`, guards `y = five`, and
  makes `obj (seen x)`;
* `second` takes `obj (seen w)`, guards `w = five`, and makes `obj done`.

**The store** (`start`): a token whose value is the store's own unknown `var 0`, the key `five`, and the
codes of both rules.

**The run.** `first` fires (`firstFiring_admitted`): its take binds its own unknown to the store's,
two ways, and its tell then binds the store's unknown to five. Then `second` fires on the made row
(`secondFiring_admitted`). Both are firings of the stored-rule program, each reading its rule's code
row. **Through the interpreter** (`interpreter_run`): two admitted firings of `U`, with the same
selections, reach a state whose row `5` has the value `obj done` at every solution of its knowledge.

**Controls.**
* A guard that fails: with the key `six`, `first` is refused (`guard_refused`).
* No code, no firing: at a tagged store without code rows, no firing of `U` is admitted
  (`interpreter_idle_without_codes`), and a stored rule fires only while a row holding its code is
  present (`code_present`).
* A wrong shape: an interpreter rule whose shape is not the shape of the code it reads is not admitted
  at a representing store (`shape_of_admitted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Examples

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr

/-! ## The data fragment -/

/-- **The data fragment**: rules of the fragment whose made rows are data rows. -/
def DataFragment : Set (Rule Tm) := {r | Fragment r ∧ ∀ m ∈ r.body.produce, ∃ t, m = obj t}

theorem dataFragment_closed : ClosedFragment DataFragment :=
  ⟨fun _ hr => hr.1, fun _ hr m inside => Or.inl (hr.2 m inside)⟩

/-! ## The program -/

/-- A token. -/
def tok (t : Expr) : Expr := cell (sym 10) t

/-- A key. -/
def key (t : Expr) : Expr := cell (sym 11) t

/-- A seen value. -/
def seen (t : Expr) : Expr := cell (sym 12) t

/-- Done. -/
def done : Expr := sym 13

/-- Five. -/
def five : Expr := sym 15

/-- Six. -/
def six : Expr := sym 16

/-- **Take a token, read a key, tell them equal, guard the key is five, make a seen row.** -/
def first : Rule Tm :=
  ⟨PUnit.unit, ⟨[obj (tok (var 0))], [obj (key (var 1))], [(var 0, var 1)], [.equal (var 1) five],
    [obj (seen (var 0))]⟩, []⟩

/-- **Take a seen row whose value is five, make done.** -/
def second : Rule Tm :=
  ⟨PUnit.unit, ⟨[obj (seen (var 0))], [], [], [.equal (var 0) five], [obj done]⟩, []⟩

/-! ## Deciding the fragment -/

/-- **Whether a rule is in the fragment**, by a finite computation: every term is drop-free. -/
def fragmentCheck (r : Rule Tm) : Bool :=
  r.body.take.all Expr.dropFree && r.body.read.all Expr.dropFree &&
    r.body.tell.all (fun e => e.1.dropFree && e.2.dropFree) &&
    r.body.checks.all (fun c => (checkTerms c).all Expr.dropFree) && r.body.produce.all Expr.dropFree &&
    r.collect.all Expr.dropFree

/-- **The check decides the fragment.** -/
theorem fragment_of_check {r : Rule Tm} (checked : fragmentCheck r = true) : Fragment r := by
  simp only [fragmentCheck, Bool.and_eq_true, List.all_eq_true] at checked
  obtain ⟨⟨⟨⟨⟨take, read⟩, tell⟩, checks⟩, produce⟩, collect⟩ := checked
  exact ⟨take, read, fun e inside => by simpa using tell e inside, checks, produce, collect⟩

/-- A rule that drops is outside the fragment (the check refuses it). -/
theorem fragmentCheck_drop : fragmentCheck ⟨PUnit.unit, ⟨[drop (var 0) (var 1)], [], [], [], []⟩, []⟩ =
    false := rfl

theorem first_mem : first ∈ DataFragment := by
  refine ⟨fragment_of_check rfl, ?_⟩
  intro m inside
  simp only [first, List.mem_singleton] at inside
  exact ⟨_, inside⟩

theorem second_mem : second ∈ DataFragment := by
  refine ⟨fragment_of_check rfl, ?_⟩
  intro m inside
  simp only [second, List.mem_singleton] at inside
  exact ⟨_, inside⟩

/-! ## The store and the first firing -/

/-- The labels of the starting store. -/
def startLabel (o : ℕ) : Expr :=
  if o = 0 then obj (tok (var 0)) else if o = 1 then obj (key five) else
    if o = 2 then ruleCode first else if o = 3 then ruleCode second else nil

/-- **The starting store**: a token valued by the store's unknown `var 0`, the key five, and the codes of
both rules. -/
def start : State Tm ℕ := ⟨PUnit.unit, [], {0, 1, 2, 3}, startLabel⟩

theorem start_tagged : Tagged DataFragment start := by
  intro o present
  simp only [start, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨first, first_mem, rfl⟩
  · exact Or.inr ⟨second, second_mem, rfl⟩

theorem start_bound : stateBound start ≤ 10 := by decide

/-- `first`, opened above the store's unknowns, taking the token, reading its code and the key. -/
def firstFiring : Firing ℕ Ext (Stored DataFragment) start.frame :=
  storedFiring first_mem start.frame (shift 10) ⟨[0], [2, 1], [4]⟩ []

theorem firstFiring_information :
    firstFiring.information X start =
      [(obj (tok (var 10)), obj (tok (var 0))), (ruleCode first, ruleCode first),
        (obj (key (var 11)), obj (key five)), (var 10, var 11)] := rfl

/-- **`first` fires.** -/
theorem firstFiring_admitted : firstFiring.Admits X start := by
  refine ⟨⟨fresh_shift firstFiring rfl start_bound, by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, ?_⟩, ?_⟩
  · rw [firstFiring_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;> rfl
  · intro b σ solved
    rw [firstFiring_information] at solved
    refine (holds_iff firstFiring rfl σ).mpr ?_
    intro c inside
    simp only [firstFiring, storedFiring, stored, first, List.mem_singleton] at inside
    subst inside
    have keyed : nf (subst σ (obj (key (var 11)))) = nf (subst σ (obj (key five))) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [obj, key, five, subst, nf, Expr.cell.injEq, true_and] at keyed
    show nf (subst σ (var 11)) = nf (subst σ five)
    exact keyed

/-- The store after `first`. -/
def middle : State Tm ℕ := firstFiring.result X start

/-- **The tell bound the store's own unknown to five**: at every solution of the knowledge after
`first`, `var 0` is five. -/
theorem middle_binds_store_unknown (σ : ℕ → Expr) (solved : action.Models σ middle.knowledge) :
    nf (σ 0) = five := by
  have known : middle.knowledge = [(obj (tok (var 10)), obj (tok (var 0))),
      (ruleCode first, ruleCode first), (obj (key (var 11)), obj (key five)), (var 10, var 11)] :=
    firstFiring_information
  rw [known] at solved
  have token : nf (subst σ (obj (tok (var 10)))) = nf (subst σ (obj (tok (var 0)))) :=
    solved _ List.mem_cons_self
  have keyed : nf (subst σ (obj (key (var 11)))) = nf (subst σ (obj (key five))) :=
    solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have told : nf (subst σ (var 10)) = nf (subst σ (var 11)) :=
    solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  simp only [obj, tok, key, five, subst, nf, Expr.cell.injEq, true_and] at token keyed told
  rw [← token, told, keyed]
  rfl

/-! ## The second firing -/

theorem middle_present : middle.present = {1, 2, 3, 4} := by decide

theorem middle_bound : stateBound middle ≤ 20 := by decide

/-- `second`, opened above the store's unknowns, taking the seen row and reading its code. -/
def secondFiring : Firing ℕ Ext (Stored DataFragment) middle.frame :=
  storedFiring second_mem middle.frame (shift 20) ⟨[4], [3], [5]⟩ []

theorem secondFiring_information :
    secondFiring.information X middle =
      [(obj (tok (var 10)), obj (tok (var 0))), (ruleCode first, ruleCode first),
        (obj (key (var 11)), obj (key five)), (var 10, var 11),
        (obj (seen (var 20)), obj (seen (var 10))), (ruleCode second, ruleCode second)] := rfl

/-- **`second` fires on the row `first` made.** -/
theorem secondFiring_admitted : secondFiring.Admits X middle := by
  refine ⟨⟨fresh_shift secondFiring rfl middle_bound, by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, ?_⟩, ?_⟩
  · rw [secondFiring_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro b σ solved
    rw [secondFiring_information] at solved
    refine (holds_iff secondFiring rfl σ).mpr ?_
    intro c inside
    simp only [secondFiring, storedFiring, stored, second, List.mem_singleton] at inside
    subst inside
    have keyed : nf (subst σ (obj (key (var 11)))) = nf (subst σ (obj (key five))) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have told : nf (subst σ (var 10)) = nf (subst σ (var 11)) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))
    have seenRow : nf (subst σ (obj (seen (var 20)))) = nf (subst σ (obj (seen (var 10)))) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
    simp only [obj, key, seen, five, subst, nf, Expr.cell.injEq, true_and] at keyed told seenRow
    show nf (subst σ (var 20)) = nf (subst σ five)
    show nf (σ 20) = five
    rw [seenRow, told, keyed]
    rfl

/-- The store after `second`. -/
def finish : State Tm ℕ := secondFiring.result X middle

theorem finish_present : finish.present = {1, 2, 3, 5} := by decide

theorem finish_done : finish.label 5 = obj done := rfl

/-! ## The run, and the same run through the interpreter -/

/-- **A run of length two of the stored-rule program.** -/
theorem stored_run : StoredSucc DataFragment start middle ∧ StoredSucc DataFragment middle finish :=
  ⟨⟨firstFiring, firstFiring_admitted, rfl⟩, ⟨secondFiring, secondFiring_admitted, rfl⟩⟩

/-- **The same run through the interpreter**: two admitted firings of `U` from the same store reach a
state that represents `finish`; its row `5` is present and has the value `obj done` at every solution
of its knowledge. -/
theorem interpreter_run :
    ∃ u₁ u₂ : State Tm ℕ, InterpSucc start u₁ ∧ InterpSucc u₁ u₂ ∧ Represents DataFragment finish u₂ ∧
      5 ∈ u₂.present ∧ ∀ σ, action.Models σ u₂.knowledge → nf (subst σ (u₂.label 5)) = obj done := by
  obtain ⟨u₁, moved₁, rep₁⟩ := (bisimulation dataFragment_closed (represents_refl start_tagged)).1 _
    stored_run.1
  obtain ⟨u₂, moved₂, rep₂⟩ := (bisimulation dataFragment_closed rep₁).1 _ stored_run.2
  refine ⟨u₁, u₂, moved₁, moved₂, rep₂, ?_, fun σ solved => ?_⟩
  · rw [rep₂.present, finish_present]
    decide
  · have present : 5 ∈ finish.present := by rw [finish_present]; decide
    obtain ⟨σ', -, labels⟩ := rep₂.forth σ solved
    rw [labels 5 present, finish_done]
    rfl

/-! ## Controls -/

/-- The labels of a store whose key is six. -/
def sixLabel (o : ℕ) : Expr :=
  if o = 0 then obj (tok (var 0)) else if o = 1 then obj (key six) else
    if o = 2 then ruleCode first else if o = 3 then ruleCode second else nil

/-- The same store with the key six. -/
def startSix : State Tm ℕ := ⟨PUnit.unit, [], {0, 1, 2, 3}, sixLabel⟩

/-- `first` with the same opening and selection at the store with the key six. -/
def sixFiring : Firing ℕ Ext (Stored DataFragment) startSix.frame :=
  storedFiring first_mem startSix.frame (shift 10) ⟨[0], [2, 1], [4]⟩ []

/-- **A guard that fails**: with the key six, every solution sends `first`'s `y` to six, so its guard
`y = five` fails at the solution sending every unknown to six. -/
theorem guard_refused : ¬ sixFiring.Admits X startSix := by
  rintro ⟨-, -, -, asks⟩
  have information : sixFiring.information X startSix =
      [(obj (tok (var 10)), obj (tok (var 0))), (ruleCode first, ruleCode first),
        (obj (key (var 11)), obj (key six)), (var 10, var 11)] := rfl
  have solved : X.Models (a := startSix.frame) (b := PUnit.unit) (fun _ => six)
      (sixFiring.information X startSix) := by
    rw [information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;> rfl
  have holds := (holds_iff sixFiring rfl _).mp (asks PUnit.unit _ solved) (.equal (var 1) five)
    (by simp [sixFiring, storedFiring, stored, first])
  have sixIsFive : six = five := holds
  exact absurd sixIsFive (by decide)

/-- **A stored rule fires only while a row holding its code is present.** -/
theorem code_present {F : Set (Rule Tm)} (closed : ClosedFragment F) {s : State Tm ℕ}
    (tagged : Tagged F s) {r : Rule Tm} (hr : r ∈ F) {ι : ℕ → Expr} {sel : Selection ℕ}
    {seen : List (Finset ℕ)} (admitted : (storedFiring hr s.frame ι sel seen).Admits X s) :
    ∃ c₀ ∈ s.present, s.label c₀ = ruleCode r := by
  obtain ⟨g, -, same, -⟩ := forward_stored closed hr (represents_refl tagged) admitted
  obtain ⟨-, -, -, -, readLength, -, -⟩ := admitted.1
  have readLength' : r.body.read.length + 1 = sel.read.length := readLength
  obtain ⟨c₀, rest, reads, -⟩ := exists_cons_of_length readLength'
  have present := present_of_enabled admitted.2.1
  have c₀present : c₀ ∈ s.present := present c₀ (List.mem_append_right _ (reads ▸ List.mem_cons_self))
  refine ⟨c₀, c₀present, ?_⟩
  obtain ⟨_, τ₀, solved⟩ := admitted.2.2.1
  obtain ⟨-, -, readsF, -⟩ := (models_information (storedFiring hr s.frame ι sel seen)
    admitted.1.2.2.2.1 readLength τ₀).mp solved
  have readsF' : List.Forall₂ (fun p o => nf (subst τ₀ (subst ι p)) = nf (subst τ₀ (s.label o)))
      (ruleCode r :: r.body.read) (c₀ :: rest) := by
    rw [← reads]
    exact readsF
  have codeRead := (List.forall₂_cons.mp readsF').1
  have frag := closed.fragment r hr
  rw [subst_ruleCode frag, subst_ruleCode frag, nf_ruleCode frag] at codeRead
  rcases tagged c₀ c₀present with ⟨t, sameLabel⟩ | ⟨r', hr', sameLabel⟩
  · rw [sameLabel, subst_obj, nf_obj] at codeRead
    exact absurd codeRead.symm (obj_ne_code _ _)
  · rw [sameLabel, subst_ruleCode (closed.fragment r' hr'), nf_ruleCode (closed.fragment r' hr')] at codeRead
    rw [sameLabel, codeRead]

/-- **No code, no firing**: at a tagged store all of whose rows are data rows, no firing of the
interpreter is admitted. -/
theorem interpreter_idle_without_codes {F : Set (Rule Tm)} (closed : ClosedFragment F) {s : State Tm ℕ}
    (data : ∀ o ∈ s.present, ∃ t, s.label o = obj t) (g : Firing ℕ Ext U s.frame) :
    ¬ g.Admits X s := by
  intro admitted
  have tagged : Tagged F s := fun o present => Or.inl (data o present)
  obtain ⟨f, admittedF, -, -⟩ := backward closed (represents_refl tagged) g admitted
  obtain ⟨r, hr, hf⟩ := stored_cases f
  rw [hf] at admittedF
  obtain ⟨c₀, present, coded⟩ := code_present closed tagged hr admittedF
  obtain ⟨t, sameLabel⟩ := data c₀ present
  rw [sameLabel] at coded
  exact obj_ne_code _ _ coded

/-- **A wrong shape is refused**: an admitted interpreter firing that reads the code of a rule of `F`
at a representing store has the shape of that rule. -/
theorem shape_of_admitted {F : Set (Rule Tm)} {s u : State Tm ℕ} (rep : Represents F s u)
    {r : Rule Tm} {sh : Shape} {ι : ℕ → Expr} {c₀ : ℕ} {rest : List ℕ}
    {sel : Selection ℕ} {seen : List (Finset ℕ)} (reads : sel.read = c₀ :: rest)
    (coded : s.label c₀ = ruleCode r) (frag : Fragment r)
    (admitted : (interpFiring sh u.frame ι sel seen).Admits X u) : sh = shapeOf r := by
  obtain ⟨-, -, -, takeLength, readLength, -, -⟩ := admitted.1
  have present := present_of_enabled admitted.2.1
  have c₀present : c₀ ∈ s.present :=
    rep.present ▸ present c₀ (List.mem_append_right _ (reads ▸ List.mem_cons_self))
  obtain ⟨_, τ₀, solved⟩ := admitted.2.2.1
  obtain ⟨known, -, readsG, -⟩ := (models_information (interpFiring sh u.frame ι sel seen)
    takeLength readLength τ₀).mp solved
  have readsG' : List.Forall₂ (fun p o => nf (subst τ₀ (subst ι p)) = nf (subst τ₀ (u.label o)))
      (codePattern sh :: openedColumn sh 1) (c₀ :: rest) := by
    rw [← reads]
    exact readsG
  have codeRead := (List.forall₂_cons.mp readsG').1
  obtain ⟨σ', -, labels⟩ := rep.forth τ₀ known
  have codeH : nf (subst (fun v => subst τ₀ (ι v)) (codePattern sh)) = ruleCode r := by
    rw [← subst_subst, codeRead, labels c₀ c₀present, coded, subst_ruleCode frag, nf_ruleCode frag]
  exact decode_shape codeH

#print axioms dataFragment_closed
#print axioms firstFiring_admitted
#print axioms middle_binds_store_unknown
#print axioms secondFiring_admitted
#print axioms stored_run
#print axioms interpreter_run
#print axioms guard_refused
#print axioms code_present
#print axioms interpreter_idle_without_codes
#print axioms shape_of_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Examples
