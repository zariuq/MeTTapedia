import Mettapedia.Languages.MM0.OnTheStep.TermDeclarations

/-!
# No run strands an accepted file

`TermDeclarations.on_the_step` says that the step reaches a state holding `accepted` from a file exactly when
MM0's rules accept the file. The step chooses among firings; this module shows that no choice strands a file MM0
accepts: **from every state the step reaches from such a file, a state holding `accepted` is still reachable**
(`accepted_stays_reachable`). For a file MM0 refuses no reachable state holds `accepted` (`TermDeclarations`).

* `reaches_of_inTerm`: from every cursor of a term under check whose signature passes, a run reaches the rest of the
  file, by the run lemmas of `TermDeclarations` (`groups_runs`, `bound_names_runs`, `regular_names_runs`,
  `arrow_runs`, the dependency runs), chosen by the verdict equation of the cursor.
* `accepted_reachable_of_phase`: from every bag of the invariant `TermDeclarations.Phase` of an accepted file, a bag
  holding `accepted` is reachable.
* `read_run`, `realize_run`: runs of the step from a state that reads as a bag and runs of rewriting with absence
  from the bag correspond, one firing for one rewrite (`AbsenceRewriting.readsBag_backward_absent`,
  `readsBag_forward_absent`), so the statement holds on the step itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.OnTheStep.AcceptanceStaysReachable

open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open NamesOnTheStep (Expr)
open Presentation.Schematic
open Machines (ReadsBag stepSystem)
open AbsenceRewriting
open DeclarationProgram
open SortDeclarations (fileTree mem_one_add)
open ArrowTermDeclarations (multiStep_append)
open TermDeclarations

universe uO

theorem checkAll_append' : ∀ (env : Env) (a b : List Statement),
    checkAll env (a ++ b) = (checkAll env a).bind fun e => checkAll e b
  | _, [], _ => rfl
  | env, s :: a, b => by
      show (checkStatement env s).bind (fun e => checkAll e (a ++ b)) =
        ((checkStatement env s).bind fun e => checkAll e a).bind fun e => checkAll e b
      cases checkStatement env s with
      | none => rfl
      | some e => exact checkAll_append' e a b

/-- **From every cursor of a term whose signature passes, a run reaches the rest of the file.** -/
theorem reaches_of_inTerm (t : TermStatement) (restTree : Expr) (env : Env) (old : List Expr)
    (shape : LocalsIn env.terms old) (fresh : t.name ∉ env.terms) {bound names : List Expr} {cursor : Expr}
    (inTerm : InTerm env.sorts t restTree bound names cursor) (passes : verdict env.sorts t = true) :
    Reaches t restTree env old cursor bound names := by
  rcases inTerm with ⟨gs, v, rfl⟩ | ⟨xs, s, gs, v, rfl⟩ | ⟨ds, xs, gs, v, rfl⟩ | ⟨xs, gs, v, rfl⟩ |
    ⟨post, v, rfl⟩ | ⟨ds, post, v, rfl⟩ | ⟨ds, v, rfl⟩
  · exact groups_runs t restTree env old shape fresh gs bound names (v ▸ passes)
  · exact bound_names_runs t restTree env old shape fresh s gs (groups_runs t restTree env old shape fresh gs) xs
      bound names (v ▸ passes)
  · have both : depsBound bound ds = true ∧ afterRegular env.sorts t xs gs bound names = true := by
      rw [v] at passes
      exact Bool.and_eq_true_iff.mp passes
    obtain ⟨bound', names', runs⟩ := regular_names_runs t restTree env old shape fresh gs
      (groups_runs t restTree env old shape fresh gs) xs bound names both.2
    exact ⟨bound', names', multiStep_append
      (deps_runs_regular t restTree env old bound names shape fresh xs gs ds both.1) runs⟩
  · exact regular_names_runs t restTree env old shape fresh gs (groups_runs t restTree env old shape fresh gs) xs
      bound names (v ▸ passes)
  · exact ⟨bound, names, arrow_runs t restTree env old bound names shape fresh post (v ▸ passes)⟩
  · have both : depsBound bound ds = true ∧ checkArrow env.sorts bound post t.ret = true := by
      rw [v] at passes
      exact Bool.and_eq_true_iff.mp passes
    exact ⟨bound, names, multiStep_append (deps_runs_arrow t restTree env old bound names shape fresh post ds both.1)
      (arrow_runs t restTree env old bound names shape fresh post both.2)⟩
  · exact ⟨bound, names, deps_runs_return t restTree env old bound names shape fresh ds (v ▸ passes)⟩

/-- **From every bag of the invariant of an accepted file, a bag holding `accepted` is reachable.** -/
theorem accepted_reachable_of_phase {ss₀ : List Statement} {bag : Multiset Expr} (phase : Phase ss₀ bag)
    (accepts : (checkAll empty ss₀).isSome) :
    ∃ bag' : Multiset Expr, (rewritingAbsent program).MultiStep bag bag' ∧ accepted ∈ bag' := by
  obtain ⟨env₀, whole⟩ := Option.isSome_iff_exists.mp accepts
  rcases phase with ⟨done, rest, env, old, decomposed, checked, shape, rfl⟩ |
    ⟨done, t, rest, env, old, bound, names, cursor, decomposed, checked, shape, fresh, inTerm, rfl⟩ |
    ⟨env, old, -, -, rfl⟩
  · rw [decomposed, checkAll_append', checked] at whole
    obtain ⟨old', runs⟩ := runs_of_checkAll rest env env₀ old shape
      (checkAll_nodup (env := empty) List.nodup_nil checked) whole
    exact ⟨_, runs, mem_one_add.mpr (Or.inl rfl)⟩
  · rw [decomposed, checkAll_append', checked] at whole
    have whole' : (checkTerm env t).bind (fun e => checkAll e rest) = some env₀ := whole
    unfold checkTerm at whole'
    split at whole'
    · rename_i conditions
      obtain ⟨-, passes⟩ := conditions
      obtain ⟨bound', names', runs⟩ := reaches_of_inTerm t (fileTree (rest.map Statement.tree)) env old shape fresh
        inTerm passes
      have nodup : (env.sorts.map Prod.fst).Nodup := checkAll_nodup (env := empty) List.nodup_nil checked
      obtain ⟨old', rest'⟩ := runs_of_checkAll rest ⟨env.sorts, t.name :: env.terms⟩ env₀
        (old ++ current t.name bound' names') (localsIn_term shape t.name bound' names') nodup whole'
      exact ⟨_, multiStep_append runs rest', mem_one_add.mpr (Or.inl rfl)⟩
    · cases whole'
  · exact ⟨_, .refl _, mem_one_add.mpr (Or.inl rfl)⟩

/-- **A run of the step from a state that reads as a bag is read back as a run of rewriting with absence.** -/
theorem read_run {O : Type uO} [DecidableEq O] {rules : List SRule} (fragment : ∀ r ∈ rules, AbsenceRestricted r)
    {s s' : (stepSystem O rules).Term} (steps : (stepSystem O rules).MultiStep s s') :
    ∀ {bag : Multiset Expr}, ReadsBag s bag →
      ∃ bag' : Multiset Expr, (rewritingAbsent rules).MultiStep bag bag' ∧ ReadsBag s' bag' := by
  induction steps with
  | refl _ => exact fun reads => ⟨_, .refl _, reads⟩
  | step first _ ih =>
      intro bag reads
      obtain ⟨g, admitted, rfl⟩ := first
      obtain ⟨bag₁, rewritten, reads₁⟩ := readsBag_backward_absent fragment reads g admitted
      obtain ⟨bag', runs, reads'⟩ := ih reads₁
      exact ⟨bag', .step rewritten runs, reads'⟩

/-- **A run of rewriting with absence from the bag a state reads as is realized by a run of the step.** -/
theorem realize_run {O : Type uO} [DecidableEq O] [Infinite O] {rules : List SRule}
    (fragment : ∀ r ∈ rules, AbsenceRestricted r) {bag bag' : (rewritingAbsent rules).Term}
    (runs : (rewritingAbsent rules).MultiStep bag bag') :
    ∀ {s : SState O}, ReadsBag s bag → ∃ s' : SState O, (stepSystem O rules).MultiStep s s' ∧ ReadsBag s' bag' := by
  induction runs with
  | refl _ => exact fun reads => ⟨_, .refl _, reads⟩
  | step first _ ih =>
      intro s reads
      obtain ⟨g, admitted, reads₁⟩ := readsBag_forward_absent fragment reads first
      obtain ⟨s', steps, reads'⟩ := ih reads₁
      exact ⟨s', .step ⟨g, admitted, rfl⟩ steps, reads'⟩

/-- **No run strands an accepted file**: from every state the step reaches from a state that reads as the bag of a
file MM0's rules accept, a state that reads as a bag holding `accepted` is still reachable. -/
theorem accepted_stays_reachable {O : Type uO} [DecidableEq O] [Infinite O] (ss : List Statement)
    (accepts : (checkAll empty ss).isSome) {s : SState O} (reads : ReadsBag s (start ss)) :
    ∀ s' : SState O, (stepSystem O program).MultiStep s s' →
      ∃ s'' : SState O, (stepSystem O program).MultiStep s' s'' ∧ ∃ bag, ReadsBag s'' bag ∧ accepted ∈ bag := by
  intro s' steps
  obtain ⟨bag', runs, reads'⟩ := read_run program_fragment steps reads
  obtain ⟨bag'', toAccepted, inside⟩ := accepted_reachable_of_phase (phase_multi runs (phase_start ss)) accepts
  obtain ⟨s'', steps', reads''⟩ := realize_run program_fragment toAccepted reads'
  exact ⟨s'', steps', bag'', reads'', inside⟩

/-- Existence and a control: the positive test file of `TermDeclarations.Examples` keeps `accepted` reachable from
every state its run reaches; the file with a strict sort for a bound variable reaches no such state at all. -/
theorem examples :
    (∀ s', (stepSystem ℕ program).MultiStep
        (Machines.listState [pending (fileTree (Examples.positive.map Statement.tree))]) s' →
      ∃ s'', (stepSystem ℕ program).MultiStep s' s'' ∧ ∃ bag, ReadsBag s'' bag ∧ accepted ∈ bag) ∧
      ¬ Examples.AcceptedOnTheStep Examples.strictBinder :=
  ⟨accepted_stays_reachable Examples.positive (by decide +kernel) (start_reads _), Examples.strictBinder_refused⟩

#print axioms reaches_of_inTerm
#print axioms accepted_reachable_of_phase
#print axioms read_run
#print axioms realize_run
#print axioms accepted_stays_reachable
#print axioms examples

end Mettapedia.Languages.MM0.OnTheStep.AcceptanceStaysReachable
