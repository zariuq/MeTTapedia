import Mettapedia.GSLT.LanguageDef.Collections.FunctionalEvaluation
import Mettapedia.GSLT.LanguageDef.Collections.EvaluationControls

/-!
# Actual functional programs and exact probe rows

The existing evaluation-control program supplies every functional-program
obligation directly. Exact outcomes below combine its independently derived
positive executions with the general uniqueness theorem. The comparison of the
model's HE setting with HE's interpreter is `HECorrespondence`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.FunctionalEvaluation.Controls

open Mettapedia.Logic.Unification.ListSplice
open Evaluation Evaluation.Controls

theorem clean_call (function : Sym) (arguments : List T) (clean : CleanAll arguments) : Clean (call function arguments) := by
  apply (clean_expr _).mpr
  intro term member
  rcases List.mem_cons.mp member with rfl | later
  · exact clean_symbol function
  · exact clean term later

theorem clean_number (value : Nat) : Clean (n value) := clean_symbol (Sym.num value)

theorem clean_fa : Clean fa := clean_call _ _ (by
  intro term member
  cases List.mem_singleton.mp member
  exact clean_symbol Sym.a)

theorem clean_onePlusTwo : Clean onePlusTwo := clean_call _ _ (by
  intro term member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact clean_number _)

private theorem singleton_rule_unique (arguments : List T) (environment : T → Env Sym Nat) (body : T)
    (firstEnv secondEnv : Env Sym Nat) (firstBody secondBody : T)
    (first : ∃ value, arguments = [value] ∧ firstEnv = environment value ∧ firstBody = body)
    (second : ∃ value, arguments = [value] ∧ secondEnv = environment value ∧ secondBody = body) :
    firstEnv = secondEnv ∧ firstBody = secondBody := by
  obtain ⟨left, leftArgs, rfl, rfl⟩ := first
  obtain ⟨right, rightArgs, rfl, rfl⟩ := second
  have same := (List.cons.inj (leftArgs.symm.trans rightArgs)).1
  subst right
  exact ⟨rfl, rfl⟩

theorem program_functional (dialect : Dialect) : Functional (program dialect) where
  native_unique := by
    intro function arguments first second left right
    cases function <;> simp only [program, nativeOf] at left right
    · obtain ⟨i, j, leftArgs, rfl⟩ := left
      obtain ⟨i', j', rightArgs, rfl⟩ := right
      have same := leftArgs.symm.trans rightArgs
      simp only [n, s, List.cons.injEq, Term.atom.injEq, Leaf.sym.injEq, Sym.num.injEq, and_true] at same
      rw [same.1, same.2]
    · obtain ⟨xs, leftArgs, rfl⟩ := left
      obtain ⟨ys, rightArgs, rfl⟩ := right
      exact congrArg Term.list (Term.expr.inj (List.cons.inj (leftArgs.symm.trans rightArgs)).1)
    · obtain ⟨xs, leftArgs, rfl⟩ := left
      obtain ⟨ys, rightArgs, rfl⟩ := right
      exact congrArg Term.expr (Term.list.inj (List.cons.inj (leftArgs.symm.trans rightArgs)).1)
  rule_unique := by
    intro function arguments firstEnv firstBody secondEnv secondBody first second
    cases function <;> simp [program, ruleOf, isProbe] at first second
    case f =>
      obtain ⟨_, rfl, rfl⟩ := first
      obtain ⟨_, rfl, rfl⟩ := second
      exact ⟨rfl, rfl⟩
    all_goals exact singleton_rule_unique arguments _ _ firstEnv secondEnv firstBody secondBody first second
  disjoint := by
    intro function arguments value environment body native rule
    cases function <;> simp [program, nativeOf, ruleOf, isProbe] at native rule
  native_clean := by
    intro function arguments value clean computed
    cases function <;> simp only [program, nativeOf] at computed
    · obtain ⟨i, j, _, rfl⟩ := computed
      exact clean_number _
    · obtain ⟨xs, rfl, rfl⟩ := computed
      exact (clean_list xs).mpr ((clean_expr xs).mp (clean _ List.mem_cons_self))
    · obtain ⟨xs, rfl, rfl⟩ := computed
      exact (clean_expr xs).mpr ((clean_list xs).mp (clean _ List.mem_cons_self))
  rule_clean := by
    intro function arguments environment body clean rule
    cases function <;> simp [program, ruleOf, isProbe] at rule
    case f =>
      obtain ⟨_, rfl, rfl⟩ := rule
      exact ⟨clean_identity, clean_number 5⟩
    all_goals
      obtain ⟨value, rfl, rfl, rfl⟩ := rule
      refine ⟨clean_bindOne clean_identity (clean value List.mem_cons_self), ?_⟩
      simp [probeBody, call, s, x, n, clean_expr, CleanAll]

theorem probe_p1_exact (result : T) :
    (Eval (program .he) Term.var (call .p1 [onePlusTwo]) result ↔ result = onePlusTwo) ∧
      (Eval (program .petta) Term.var (call .p1 [onePlusTwo]) result ↔ result = onePlusTwo) ∧
      (Eval (program .primeCandidate) Term.var (call .p1 [onePlusTwo]) result ↔ result = onePlusTwo) := by
  have clean : Clean (call .p1 [onePlusTwo]) := clean_call _ _ (by
    intro term member
    cases List.mem_singleton.mp member
    exact clean_onePlusTwo)
  exact ⟨eval_iff_value (program_functional .he) clean_identity clean probe_p1_he result,
    eval_iff_value (program_functional .petta) clean_identity clean probe_p1_petta result,
    eval_iff_value (program_functional .primeCandidate) clean_identity clean probe_p1_candidate result⟩

theorem probe_p3_exact (result : T) :
    (Eval (program .he) Term.var (call .p3 [fa]) result ↔ result = call .h [fa]) ∧
      (Eval (program .petta) Term.var (call .p3 [fa]) result ↔ result = call .h [fa]) ∧
      (Eval (program .primeCandidate) Term.var (call .p3 [fa]) result ↔ result = .expr [s .wrapped, fa]) := by
  have clean : Clean (call .p3 [fa]) := clean_call _ _ (by
    intro term member
    cases List.mem_singleton.mp member
    exact clean_fa)
  exact ⟨eval_iff_value (program_functional .he) clean_identity clean probe_p3_he result,
    eval_iff_value (program_functional .petta) clean_identity clean probe_p3_petta result,
    eval_iff_value (program_functional .primeCandidate) clean_identity clean probe_p3_candidate result⟩

theorem probe_p4_exact (result : T) :
    (Eval (program .he) Term.var (call .p4 [fa]) result ↔ result = .expr [s .wrapped, n 5]) ∧
      (Eval (program .petta) Term.var (call .p4 [fa]) result ↔ result = .expr [s .wrapped, fa]) ∧
      (Eval (program .primeCandidate) Term.var (call .p4 [fa]) result ↔ result = .expr [s .wrapped, fa]) := by
  have clean : Clean (call .p4 [fa]) := clean_call _ _ (by
    intro term member
    cases List.mem_singleton.mp member
    exact clean_fa)
  exact ⟨eval_iff_value (program_functional .he) clean_identity clean probe_p4_he result,
    eval_iff_value (program_functional .petta) clean_identity clean probe_p4_petta result,
    eval_iff_value (program_functional .primeCandidate) clean_identity clean probe_p4_candidate result⟩

theorem map_has_exact_result (result : T) :
    Eval C Term.var (.expr [head .map, calls, .var 4, .var 4]) result ↔ result = .list [n 5, n 3] := by
  apply eval_iff_value (program_functional .primeCandidate) clean_identity _ map_evaluates_elements
  apply (clean_expr _).mpr
  intro term member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact (clean_builtin _).mpr (by simp [Allowed])
  · apply (clean_list _).mpr
    intro term member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact clean_fa
    · exact clean_onePlusTwo
  · exact clean_variable _
  · exact clean_variable _

/-- The successful open-rest unification control has exactly its appended
list result, not merely one derivation producing that result. -/
theorem difference_list_append_exact (result : T) :
    Eval C Term.var
      (.expr [head .let_, .var 3, .rest [s .a, s .b] (.var 2),
        .expr [head .unify, .var 2, .list [s .c, s .d], .var 3, s .no]]) result ↔
      result = .list [s .a, s .b, s .c, s .d] := by
  apply eval_iff_value (program_functional .primeCandidate) clean_identity _ difference_list_append
  simp [clean_expr, clean_rest, clean_list, CleanAll, clean_builtin, Allowed, s]

/-- Occurrence failure is a successful, deterministic execution of the `no`
branch; it is not evaluator absence or an assumed solver failure. -/
theorem occurs_failure_is_functional (result : T) :
    Eval C Term.var
      (.expr [head .unify, .var 2, .rest [s .a] (.var 2), s .yes, s .no]) result ↔
      result = s .no := by
  apply eval_iff_value (program_functional .primeCandidate) clean_identity _
    ((unify_occurs_check _).mpr rfl)
  simp [clean_expr, clean_rest, CleanAll, clean_builtin, Allowed, s]

/-- Merely solving the input equation does not constrain unused variables.
The clean-image theorem needs the actual solver's global MGU guarantee. -/
theorem arbitrary_solution_can_have_unsafe_unused_image :
    ∃ substitution : Env Sym Nat,
      Equivalent (subst substitution (.var 0)) (subst substitution (s .a)) ∧
        ¬ CleanEnv substitution := by
  let substitution : Env Sym Nat := fun name =>
    if name = 0 then s .a else if name = 9 then head .superpose else .var name
  refine ⟨substitution, ?_, ?_⟩
  · simpa [substitution, subst, s] using (Equivalent.refl (s .a))
  · intro clean
    have image := clean 9
    have allowed := (clean_builtin .superpose).mp (by simpa [substitution] using image)
    exact allowed.1 rfl

theorem superpose_is_excluded : ¬ Clean (.expr [head .superpose, .list [s .a, s .b]] : T) := by
  intro clean
  have allowed := (clean_builtin .superpose).mp ((clean_expr _).mp clean _ List.mem_cons_self)
  exact allowed.1 rfl

theorem excluded_superpose_really_has_two_results :
    Eval C Term.var (.expr [head .superpose, .list [s .a, s .b]]) (s .a) ∧
      Eval C Term.var (.expr [head .superpose, .list [s .a, s .b]]) (s .b) ∧ s .a ≠ s .b := by
  have listed : Eval C Term.var (.list [s .a, s .b]) (.list [s .a, s .b]) := by
    convert Eval.list (P := C) (θ := Term.var) (xs := [s .a, s .b]) using 1
    ·
      simp [inst, s, subst, normalize]
  exact ⟨.superpose listed (by simp), .superpose listed (by simp), by intro same; cases same⟩

def overlapping : Program Sym Nat := {program .primeCandidate with
  native := fun function arguments value => nativeOf function arguments value ∨
    function = .f ∧ arguments = [s .a] ∧ value = n 6 }

theorem native_rule_overlap_has_two_results :
    Eval overlapping Term.var (call .f [s .a]) (n 5) ∧
      Eval overlapping Term.var (call .f [s .a]) (n 6) ∧ n 5 ≠ n 6 := by
  refine ⟨?_, ?_, ?_⟩
  · exact .call rfl (.evaluated (.symbol rfl) .nil) ⟨rfl, rfl, rfl⟩ (.once (.symbol rfl))
  · exact .native rfl (.evaluated (.symbol rfl) .nil) (Or.inr ⟨rfl, rfl, rfl⟩) .asWritten
  · intro same
    simp [n, s] at same

theorem overlapping_program_not_functional : ¬ Functional overlapping := by
  intro functional
  exact functional.disjoint .f [s .a] (n 6) Term.var (n 5) (Or.inr ⟨rfl, rfl, rfl⟩) ⟨rfl, rfl, rfl⟩

def firstMatch : Env Sym Nat := fun _ => .rest [] (n 1)
def secondMatch : Env Sym Nat := fun name => if name = 0 then n 1 else n 2

/-- Matching can choose different raw substitutions and unrelated entries.
Only the normalized values at the pattern's variables enter its binder. -/
theorem matching_does_not_require_equal_substitutions :
    firstMatch ≠ secondMatch ∧
      Program.bindPattern Term.var firstMatch (.var 0) = Program.bindPattern Term.var secondMatch (.var 0) := by
  constructor
  · intro same
    have image := congrFun same 0
    change Term.rest [] (n 1) = n 1 at image
    cases image
  · apply bindPattern_congr Term.var firstMatch secondMatch (.var 0) (n 1)
    · simpa [subst, firstMatch] using (Equivalent.emptyRest (n 1))
    · simpa [subst, secondMatch] using (Equivalent.refl (n 1))

end Mettapedia.GSLT.LanguageDef.Collections.FunctionalEvaluation.Controls
