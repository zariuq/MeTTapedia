import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Simulation

/-!
# The interpreter and the stored-rule program are strongly bisimilar

For a set `F` of rules of the fragment closed under what its rules make (`ClosedFragment F`):

* `forward`: every admitted firing of the stored-rule program `Stored F` at a state `s` is matched,
  at every state `u` representing `s`, by an admitted firing of the interpreter `U` **with the same
  selection** (the same taken, read and made occurrences), and the results are represented.
* `backward`: every admitted firing of `U` at `u` is matched by an admitted firing of `Stored F` at `s`
  with the same selection, and the results are represented. A firing of `U` whose first read is not
  the code of a rule of `F` is not admitted at a representing state.
* `bisimulation`: `Represents F` is a strong bisimulation between the successor relations of the two
  steps; `runs_forward` and `runs_backward` lift it to runs of any length, step for step. There are no
  administrative firings.

The representation asks the specification's store to be tagged through its knowledge (`SemTagged`): a
row is a code of a rule of `F` when the knowledge makes it one, whatever its syntax.

**Without closure** (`forward_of`, `backward_of`, `step_bisimulation`): for every set of rules of the
fragment, the same holds at a state where every admitted firing of the stored-rule program leaves a
store tagged through its knowledge (`KeepsTags`); a closed fragment keeps the tags at every tagged
store (`keepsTags_of_closed`). Along runs it suffices that an invariant of the stored-rule program
implies the tags (`runs_forward_of`, `runs_backward_of`). This is how a rule that makes a code from a
row it received is covered (`Mobility`).

Both steps are `RuleSyntax.step` at the one-frame action of the code algebra, with the identity
extension. `U` is one fixed program, independent of `F`: one interpreter rule per shape, where a shape
fixes the numbers of takes, reads, made rows, tells and collect patterns and the list of check kinds
with their count numbers, so one arity carries infinitely many rules (`Limits`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr

variable {O : Type*} [DecidableEq O]

omit [DecidableEq O] in
/-- A selection with reads has a first read. -/
theorem exists_cons_of_length {l : List O} {n : ℕ} (length : n + 1 = l.length) :
    ∃ c₀ rest, l = c₀ :: rest ∧ n = rest.length := by
  cases l with
  | nil => simp at length
  | cons c₀ rest => exact ⟨c₀, rest, rfl, Nat.succ.inj length⟩

/-- The taken and read occurrences of an enabled selection are present. -/
theorem present_of_enabled {W : Finset O} {sel : Selection O}
    (enabled : Enabled (fun _ : O => ()) W (sel.commit (T := Unit))) :
    ∀ o ∈ sel.taken ++ sel.read, o ∈ W := by
  intro o member
  rcases List.mem_append.mp member with taken | read
  · exact enabled.taken_subset (by simpa [Selection.commit] using taken)
  · exact enabled.kept_subset (by simpa [Selection.commit] using read)

omit [DecidableEq O] in
/-- **A row read by a code pattern at a represented state is, through the knowledge, the code of a rule
of `F`.** -/
theorem coded_of_read {F : Set (Rule Tm)} {s u : State Tm O} (rep : Represents F s u) {c₀ : O}
    (present : c₀ ∈ s.present) {τ : ℕ → Expr} (known : action.Models τ u.knowledge) {pattern : Expr}
    (codeRead : nf (subst τ pattern) = nf (subst τ (u.label c₀))) (isCode : ∃ c, nf (subst τ pattern) = code c) :
    ∃ r ∈ F, CodedAt s c₀ r := by
  obtain ⟨σ', knownS, labels⟩ := rep.forth τ known
  obtain ⟨c, hc⟩ := isCode
  rcases rep.tagged c₀ present with data | found
  · exfalso
    obtain ⟨t, same⟩ := data σ' knownS
    have := (codeRead.trans (labels c₀ present)).symm
    rw [same, hc] at this
    exact obj_ne_code _ _ this
  · exact found

/-! ## What the stored-rule program must keep -/

/-- **The stored-rule program keeps the tags at `s`**: every admitted firing of `Stored F` at `s` leaves
a store tagged through its knowledge. -/
def KeepsTags (F : Set (Rule Tm)) (s : State Tm O) : Prop :=
  ∀ f : Firing O Ext (Stored F) s.frame, f.Admits X s → SemTagged F (f.result X s)

/-- **A closed fragment keeps the tags at every tagged store**: its made rows are data rows or literal
codes of its rules, and the rows it does not make keep their values at the solutions of the larger
knowledge. -/
theorem keepsTags_of_closed {F : Set (Rule Tm)} (closed : ClosedFragment F) {s : State Tm O}
    (tagged : SemTagged F s) : KeepsTags F s := by
  intro f admitted
  obtain ⟨r, hr, hf⟩ := stored_cases f
  rw [hf] at admitted ⊢
  obtain ⟨-, -, madeNodup, takeLength, readLength, madeLength, -⟩ := admitted.1
  have refines : ∀ σ, action.Models σ
      ((storedFiring hr s.frame f.opening f.selection f.seen).result X s).knowledge →
        action.Models σ s.knowledge := fun σ solved =>
    ((models_information _ takeLength readLength σ).mp solved).1
  have lengths : f.selection.made.length = r.body.produce.length := madeLength.symm
  intro o member
  change o ∈ fire s.present (f.selection.commit (T := Unit)) at member
  by_cases made : o ∈ f.selection.made
  · obtain ⟨j, inside, rfl⟩ := List.mem_iff_getElem.mp made
    have fLabel : ((storedFiring hr s.frame f.opening f.selection f.seen).result X s).label
        f.selection.made[j] = subst f.opening (r.body.produce[j]'(lengths ▸ inside)) := by
      have zipped := Firing.relabel_zip
        (Firing.row X s (storedFiring hr s.frame f.opening f.selection f.seen))
        f.selection.made (r.body.produce.map (subst f.opening)) madeNodup (by simpa using lengths)
        (f.selection.made[j], subst f.opening (r.body.produce[j]'(lengths ▸ inside))) (by
          have below : j < (f.selection.made.zip (r.body.produce.map (subst f.opening))).length := by
            simpa [lengths] using inside
          have entry := List.getElem_mem below
          rw [List.getElem_zip, List.getElem_map] at entry
          exact entry)
      exact zipped
    rcases closed.made r hr _ (List.getElem_mem _) with ⟨t, same⟩ | ⟨r', hr', same⟩
    · refine Or.inl fun σ _ => ⟨nf (subst σ (subst f.opening t)), ?_⟩
      rw [fLabel, same]
      rfl
    · refine Or.inr ⟨r', hr', fun σ _ => ?_⟩
      rw [fLabel, same, subst_ruleCode (closed.fragment r' hr')]
  · have fLabel : ((storedFiring hr s.frame f.opening f.selection f.seen).result X s).label o =
        s.label o :=
      (Firing.result_label_other (storedFiring hr s.frame f.opening f.selection f.seen) made).trans
        (congrFun (row_eq _) o)
    have old : o ∈ s.present := by
      rcases mem_fire.mp member with ⟨present, -⟩ | fresh
      · exact present
      · exact absurd (by simpa [Selection.commit] using fresh) made
    rcases tagged o old with data | ⟨r', hr', coded⟩
    · exact Or.inl fun σ solved => by rw [fLabel]; exact data σ (refines σ solved)
    · exact Or.inr ⟨r', hr', fun σ solved => by rw [fLabel]; exact coded σ (refines σ solved)⟩

/-! ## Forward: the stored-rule program is simulated by the interpreter -/

/-- **Forward, for a firing of a stored rule**, for every set of rules of the fragment, when the
firing's result is tagged through its knowledge. -/
theorem forward_stored_of {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {r : Rule Tm} (hr : r ∈ F)
    {s u : State Tm O} (rep : Represents F s u) {ιP : ℕ → Expr} {sel : Selection O}
    {seen : List (Finset O)} (admitted : (storedFiring hr s.frame ιP sel seen).Admits X s)
    (tags : SemTagged F ((storedFiring hr s.frame ιP sel seen).result X s)) :
    ∃ g : Firing O Ext U u.frame, g.Admits X u ∧ g.selection = sel ∧
      Represents F ((storedFiring hr s.frame ιP sel seen).result X s) (g.result X u) := by
  have fragR := frag r hr
  obtain ⟨freshP, takenNodup, madeNodup, takeLength, readLength, madeLength, -⟩ := admitted.1
  have readLength' : r.body.read.length + 1 = sel.read.length := readLength
  obtain ⟨c₀, rest, reads, restLength⟩ := exists_cons_of_length readLength'
  have present := present_of_enabled admitted.2.1
  have c₀present : c₀ ∈ s.present := present c₀ (List.mem_append_right _ (reads ▸ List.mem_cons_self))
  -- the row read first is, through the knowledge, the rule's own code
  have coded : CodedAt s c₀ r := by
    obtain ⟨_, τ₀, solved⟩ := admitted.2.2.1
    have fRead : (ruleCode r :: r.body.read).length = sel.read.length := readLength
    obtain ⟨known, -, readsF, -⟩ := (models_information (storedFiring hr s.frame ιP sel seen)
      takeLength fRead τ₀).mp solved
    have readsF' : List.Forall₂ (fun p o => nf (subst τ₀ (subst ιP p)) = nf (subst τ₀ (s.label o)))
        (ruleCode r :: r.body.read) (c₀ :: rest) := by
      rw [← reads]
      exact readsF
    have codeRead := (List.forall₂_cons.mp readsF').1
    rw [subst_ruleCode fragR, subst_ruleCode fragR, nf_ruleCode fragR] at codeRead
    rcases rep.tagged c₀ c₀present with data | ⟨r', hr', coded'⟩
    · exfalso
      obtain ⟨t, same⟩ := data τ₀ known
      rw [same] at codeRead
      exact obj_ne_code _ _ codeRead.symm
    · have sameCode : ruleCode r = ruleCode r' := codeRead.trans (coded'.value (frag r' hr') known)
      intro σ knownσ
      rw [coded' σ knownσ, sameCode]
  have comparable : Comparable r s u sel c₀ rest :=
    ⟨reads, coded, present, takeLength, restLength, madeLength.symm, takenNodup, madeNodup⟩
  let g : Firing O Ext U u.frame := interpFiring (shapeOf r) u.frame (shift (stateBound u)) sel seen
  have freshU : g.Fresh X u := fresh_shift g rfl le_rfl
  refine ⟨g, (admits_transfer hr fragR rep comparable freshP freshU).mpr admitted, rfl, ?_⟩
  exact results_represent hr fragR rep comparable freshP freshU tags

/-- **Forward, for a firing of a stored rule of a closed fragment.** -/
theorem forward_stored {F : Set (Rule Tm)} (closed : ClosedFragment F) {r : Rule Tm} (hr : r ∈ F)
    {s u : State Tm O} (rep : Represents F s u) {ιP : ℕ → Expr} {sel : Selection O}
    {seen : List (Finset O)} (admitted : (storedFiring hr s.frame ιP sel seen).Admits X s) :
    ∃ g : Firing O Ext U u.frame, g.Admits X u ∧ g.selection = sel ∧
      Represents F ((storedFiring hr s.frame ιP sel seen).result X s) (g.result X u) :=
  forward_stored_of closed.fragment hr rep admitted (keepsTags_of_closed closed rep.tagged _ admitted)

/-- **Forward, for every set of rules of the fragment, where the stored-rule program keeps the tags.** -/
theorem forward_of {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {s u : State Tm O}
    (rep : Represents F s u) (keeps : KeepsTags F s) (f : Firing O Ext (Stored F) s.frame)
    (admitted : f.Admits X s) :
    ∃ g : Firing O Ext U u.frame, g.Admits X u ∧ g.selection = f.selection ∧
      Represents F (f.result X s) (g.result X u) := by
  have tags := keeps f admitted
  obtain ⟨r, hr, hf⟩ := stored_cases f
  rw [hf] at admitted tags ⊢
  exact forward_stored_of frag hr rep admitted tags

/-- **Forward**: every admitted firing of the stored-rule program is matched by an admitted firing of
the interpreter with the same selection, and the results are represented. -/
theorem forward {F : Set (Rule Tm)} (closed : ClosedFragment F) {s u : State Tm O}
    (rep : Represents F s u) (f : Firing O Ext (Stored F) s.frame) (admitted : f.Admits X s) :
    ∃ g : Firing O Ext U u.frame, g.Admits X u ∧ g.selection = f.selection ∧
      Represents F (f.result X s) (g.result X u) :=
  forward_of closed.fragment rep (keepsTags_of_closed closed rep.tagged) f admitted

/-! ## Backward: the interpreter has no extra behaviour -/

/-- **Backward, for a firing of an interpreter rule**, for every set of rules of the fragment, where
the stored-rule program keeps the tags. -/
theorem backward_interp_of {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {s u : State Tm O}
    (rep : Represents F s u) (keeps : KeepsTags F s) {sh : Shape} {ιU : ℕ → Expr} {sel : Selection O}
    {seen : List (Finset O)} (admitted : (interpFiring sh u.frame ιU sel seen).Admits X u) :
    ∃ f : Firing O Ext (Stored F) s.frame, f.Admits X s ∧ f.selection = sel ∧
      Represents F (f.result X s) ((interpFiring sh u.frame ιU sel seen).result X u) := by
  obtain ⟨freshU, takenNodup, madeNodup, takeLength, readLength, madeLength, -⟩ := admitted.1
  have readLength' : sh.reads + 1 = sel.read.length := by
    have lengths : (codePattern sh :: openedColumn sh 1).length = sel.read.length := readLength
    rw [List.length_cons, length_openedColumn] at lengths
    exact lengths
  obtain ⟨c₀, rest, reads, restLength⟩ := exists_cons_of_length readLength'
  have presentU := present_of_enabled admitted.2.1
  have present : ∀ o ∈ sel.taken ++ sel.read, o ∈ s.present := fun o member => rep.present ▸ presentU o member
  have c₀present : c₀ ∈ s.present := present c₀ (List.mem_append_right _ (reads ▸ List.mem_cons_self))
  -- the row read first is, through the knowledge, the code of a rule of `F` of the interpreter rule's
  -- shape
  obtain ⟨_, τ₀, solved⟩ := admitted.2.2.1
  have gTake : (openedColumn sh 0).length = sel.taken.length := takeLength
  have gRead : (codePattern sh :: openedColumn sh 1).length = sel.read.length := readLength
  obtain ⟨known, -, readsG, -⟩ := (models_information (interpFiring sh u.frame ιU sel seen)
    gTake gRead τ₀).mp solved
  have readsG' : List.Forall₂ (fun p o => nf (subst τ₀ (subst ιU p)) = nf (subst τ₀ (u.label o)))
      (codePattern sh :: openedColumn sh 1) (c₀ :: rest) := by
    rw [← reads]
    exact readsG
  have codeRead := (List.forall₂_cons.mp readsG').1
  have isCode : ∃ c, nf (subst τ₀ (subst ιU (codePattern sh))) = code c := by
    rw [subst_subst, nf_subst_codePattern]
    exact ⟨_, rfl⟩
  obtain ⟨r, hr, coded⟩ := coded_of_read rep c₀present known codeRead isCode
  have fragR := frag r hr
  have codeH : nf (subst (fun v => subst τ₀ (ιU v)) (codePattern sh)) = ruleCode r := by
    rw [← subst_subst, codeRead]
    obtain ⟨σ', knownS, labels⟩ := rep.forth τ₀ known
    rw [labels c₀ c₀present, coded.value fragR knownS]
  have shape := decode_shape codeH
  subst shape
  have comparable : Comparable r s u sel c₀ rest := by
    refine ⟨reads, coded, present, ?_, ?_, ?_, takenNodup, madeNodup⟩
    · rw [length_openedColumn] at gTake
      exact gTake
    · exact restLength
    · have lengths : (openedColumn (shapeOf r) 2).length = sel.made.length := madeLength
      rw [length_openedColumn] at lengths
      exact lengths.symm
  let f : Firing O Ext (Stored F) s.frame := storedFiring hr s.frame (shift (stateBound s)) sel seen
  have freshP : f.Fresh X s := fresh_shift f rfl le_rfl
  have admittedF : f.Admits X s := (admits_transfer hr fragR rep comparable freshP freshU).mp admitted
  refine ⟨f, admittedF, rfl, ?_⟩
  exact results_represent hr fragR rep comparable freshP freshU (keeps f admittedF)

/-- **Backward, for every set of rules of the fragment, where the stored-rule program keeps the
tags.** -/
theorem backward_of {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {s u : State Tm O}
    (rep : Represents F s u) (keeps : KeepsTags F s) (g : Firing O Ext U u.frame) (admitted : g.Admits X u) :
    ∃ f : Firing O Ext (Stored F) s.frame, f.Admits X s ∧ f.selection = g.selection ∧
      Represents F (f.result X s) (g.result X u) := by
  obtain ⟨sh, hg⟩ := interp_cases g
  rw [hg] at admitted ⊢
  exact backward_interp_of frag rep keeps admitted

/-- **Backward**: every admitted firing of the interpreter at a representing state is matched by an
admitted firing of the stored-rule program with the same selection, and the results are represented. -/
theorem backward {F : Set (Rule Tm)} (closed : ClosedFragment F) {s u : State Tm O}
    (rep : Represents F s u) (g : Firing O Ext U u.frame) (admitted : g.Admits X u) :
    ∃ f : Firing O Ext (Stored F) s.frame, f.Admits X s ∧ f.selection = g.selection ∧
      Represents F (f.result X s) (g.result X u) :=
  backward_of closed.fragment rep (keepsTags_of_closed closed rep.tagged) g admitted

/-! ## Strong bisimulation and runs -/

/-- The successor relation of the stored-rule program. -/
abbrev StoredSucc (F : Set (Rule Tm)) : State Tm O → State Tm O → Prop :=
  Succ (step X O Ext (Stored F)).toStep

/-- The successor relation of the interpreter. -/
abbrev InterpSucc : State Tm O → State Tm O → Prop := Succ (step X O Ext U).toStep

/-- **One step of strong bisimulation, for every set of rules of the fragment, where the stored-rule
program keeps the tags.** -/
theorem step_bisimulation {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {s u : State Tm O}
    (rep : Represents F s u) (keeps : KeepsTags F s) :
    (∀ s', StoredSucc F s s' → ∃ u', InterpSucc u u' ∧ Represents F s' u') ∧
      (∀ u', InterpSucc u u' → ∃ s', StoredSucc F s s' ∧ Represents F s' u') := by
  constructor
  · rintro s' ⟨f, admitted, rfl⟩
    obtain ⟨g, admittedG, -, rep'⟩ := forward_of frag rep keeps f admitted
    exact ⟨g.result X u, ⟨g, admittedG, rfl⟩, rep'⟩
  · rintro u' ⟨g, admitted, rfl⟩
    obtain ⟨f, admittedF, -, rep'⟩ := backward_of frag rep keeps g admitted
    exact ⟨f.result X s, ⟨f, admittedF, rfl⟩, rep'⟩

/-- **Strong bisimulation.** -/
theorem bisimulation {F : Set (Rule Tm)} (closed : ClosedFragment F) {s u : State Tm O}
    (rep : Represents F s u) :
    (∀ s', StoredSucc F s s' → ∃ u', InterpSucc u u' ∧ Represents F s' u') ∧
      (∀ u', InterpSucc u u' → ∃ s', StoredSucc F s s' ∧ Represents F s' u') :=
  step_bisimulation closed.fragment rep (keepsTags_of_closed closed rep.tagged)

/-- **Every run of the stored-rule program is a run of the interpreter, step for step.** -/
theorem runs_forward {F : Set (Rule Tm)} (closed : ClosedFragment F) {s u s' : State Tm O}
    (rep : Represents F s u) (run : Relation.ReflTransGen (StoredSucc F) s s') :
    ∃ u', Relation.ReflTransGen InterpSucc u u' ∧ Represents F s' u' := by
  induction run with
  | refl => exact ⟨u, Relation.ReflTransGen.refl, rep⟩
  | tail _ moved ih =>
      obtain ⟨u₁, runU, rep₁⟩ := ih
      obtain ⟨u₂, movedU, rep₂⟩ := (bisimulation closed rep₁).1 _ moved
      exact ⟨u₂, runU.tail movedU, rep₂⟩

/-- **Every run of the interpreter from a representing state is a run of the stored-rule program, step
for step**: the interpreter has no extra behaviour. -/
theorem runs_backward {F : Set (Rule Tm)} (closed : ClosedFragment F) {s u u' : State Tm O}
    (rep : Represents F s u) (run : Relation.ReflTransGen InterpSucc u u') :
    ∃ s', Relation.ReflTransGen (StoredSucc F) s s' ∧ Represents F s' u' := by
  induction run with
  | refl => exact ⟨s, Relation.ReflTransGen.refl, rep⟩
  | tail _ moved ih =>
      obtain ⟨s₁, runS, rep₁⟩ := ih
      obtain ⟨s₂, movedS, rep₂⟩ := (bisimulation closed rep₁).2 _ moved
      exact ⟨s₂, runS.tail movedS, rep₂⟩

/-- An invariant of the stored-rule program that implies the tags keeps them. -/
theorem keepsTags_of_invariant {F : Set (Rule Tm)} {Inv : State Tm O → Prop}
    (tags : ∀ s, Inv s → SemTagged F s) (preserved : ∀ s s', Inv s → StoredSucc F s s' → Inv s')
    {s : State Tm O} (inv : Inv s) : KeepsTags F s :=
  fun f admitted => tags _ (preserved s _ inv ⟨f, admitted, rfl⟩)

/-- **Runs forward, for every set of rules of the fragment and an invariant of the stored-rule program
that implies the tags.** -/
theorem runs_forward_of {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {Inv : State Tm O → Prop}
    (tags : ∀ s, Inv s → SemTagged F s) (preserved : ∀ s s', Inv s → StoredSucc F s s' → Inv s')
    {s u s' : State Tm O} (inv : Inv s) (rep : Represents F s u)
    (run : Relation.ReflTransGen (StoredSucc F) s s') :
    ∃ u', Relation.ReflTransGen InterpSucc u u' ∧ Represents F s' u' ∧ Inv s' := by
  induction run with
  | refl => exact ⟨u, Relation.ReflTransGen.refl, rep, inv⟩
  | tail _ moved ih =>
      obtain ⟨u₁, runU, rep₁, inv₁⟩ := ih
      obtain ⟨u₂, movedU, rep₂⟩ :=
        (step_bisimulation frag rep₁ (keepsTags_of_invariant tags preserved inv₁)).1 _ moved
      exact ⟨u₂, runU.tail movedU, rep₂, preserved _ _ inv₁ moved⟩

/-- **Runs backward, for every set of rules of the fragment and an invariant of the stored-rule
program that implies the tags.** -/
theorem runs_backward_of {F : Set (Rule Tm)} (frag : ∀ r ∈ F, Fragment r) {Inv : State Tm O → Prop}
    (tags : ∀ s, Inv s → SemTagged F s) (preserved : ∀ s s', Inv s → StoredSucc F s s' → Inv s')
    {s u u' : State Tm O} (inv : Inv s) (rep : Represents F s u)
    (run : Relation.ReflTransGen InterpSucc u u') :
    ∃ s', Relation.ReflTransGen (StoredSucc F) s s' ∧ Represents F s' u' ∧ Inv s' := by
  induction run with
  | refl => exact ⟨s, Relation.ReflTransGen.refl, rep, inv⟩
  | tail _ moved ih =>
      obtain ⟨s₁, runS, rep₁, inv₁⟩ := ih
      obtain ⟨s₂, movedS, rep₂⟩ :=
        (step_bisimulation frag rep₁ (keepsTags_of_invariant tags preserved inv₁)).2 _ moved
      exact ⟨s₂, runS.tail movedS, rep₂, preserved _ _ inv₁ movedS⟩

#print axioms keepsTags_of_closed
#print axioms forward_of
#print axioms backward_of
#print axioms forward
#print axioms backward
#print axioms step_bisimulation
#print axioms bisimulation
#print axioms runs_forward
#print axioms runs_backward
#print axioms runs_forward_of
#print axioms runs_backward_of

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows
