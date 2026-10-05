import Mettapedia.Languages.MM0.Presentation.ArgumentProgram
import Mettapedia.Languages.MM0.Presentation.TypingCorrespondence

/-!
# Computational correspondence for MM0 argument typing

The authored equations compute the independent binder and exact-arity checks.
Boundness, saturation, sort equality and the order of the formal context are
retained. Successful checking is equivalent to the independent typing judgment;
no proof search is used to supply an argument or fill a missing premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalArguments

open Kernel ComputationalContext ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => argumentProgram
local notation "H" => computationalHost

private def typingSuffix : Program := listAppendProgram ++ ComputationalSupport.supportEquations ++
  naturalMembershipProgram ++ ComputationalDependency.dependencyEquations ++ argumentEquations

private theorem typing_disjoint :
    ∀ equation ∈ typingSuffix, equation.head ∉ typingProgram.calledHeads := by decide

private theorem typing_reused (head : String) (called : head ∈ typingProgram.calledHeads)
    (arguments : List Term) (result : Term) (run : Applies typingProgram H head arguments result) :
    Applies P H head arguments result := by
  have larger := (Applies.append_iff typingProgram typingSuffix H typing_disjoint head called _ _).mpr run
  simpa only [argumentProgram, ComputationalDependency.dependencyProgram,
    ComputationalSupport.supportProgram, typingSuffix, List.append_assoc] using larger

private theorem check_sort_computes (actual : Option Nat) (expected : Nat) :
    Applies P H "mm0:check-sort" [encodeSortResult actual, natural expected]
      (boolean (decide (actual = some expected))) := by
  cases actual with
  | none => exact ⟨1, rfl⟩
  | some actual =>
    refine Applies.equation (equation := P[67])
      (environment := [("actual", natural actual), ("expected", natural expected)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ?_
    have scalar : Applies P H "nik:nat-eq" [natural actual, natural expected]
        (boolean (decide (actual = expected))) :=
      .primitive (by rfl) (computationalHost_binary (operation := .equal) rfl actual expected (by decide) (by decide))
    simpa only [Option.some.injEq] using scalar

private theorem saturated_computes (remaining : Context) (actual expected : Nat) :
    Applies P H "mm0:check-saturated" [listView (remaining.map encodeBinder), natural actual, natural expected]
      (boolean (decide ((remaining, actual) = ([], expected)))) := by
  cases remaining with
  | nil =>
    refine Applies.equation (equation := P[70])
      (environment := [("actual", natural actual), ("expected", natural expected)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ?_
    have scalar : Applies P H "nik:nat-eq" [natural actual, natural expected]
        (boolean (decide (actual = expected))) :=
      .primitive (by rfl) (computationalHost_binary (operation := .equal) rfl actual expected (by decide) (by decide))
    simpa only [Prod.mk.injEq, true_and] using scalar
  | cons first rest =>
    have refused : decide (((first :: rest), actual) = ([], expected)) = false := by simp
    rw [refused]
    exact ⟨1, rfl⟩

private theorem check_type_computes (actual : Option ExpressionType) (expected : Nat) :
    Applies P H "mm0:check-type" [encodeType actual, natural expected]
      (boolean (decide (actual = some ([], expected)))) := by
  cases actual with
  | none => exact ⟨1, rfl⟩
  | some pair =>
    obtain ⟨remaining, actual⟩ := pair
    refine Applies.equation (equation := P[69])
      (environment := [("remaining", encodeContext remaining), ("actual", natural actual),
        ("expected", natural expected)]) (by rfl) (by rfl) ?_
    refine Evaluates.call
      (values := [listView (remaining.map encodeBinder), natural actual, natural expected]) (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
    · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
        (.primitive (by rfl) (computationalHost_list_view _))
    · simpa only [Option.some.injEq] using saturated_computes remaining actual expected

theorem binder_computes (table : SignatureTable) (target : Context) (expression : Preterm)
    (binder : Kernel.Binder) :
    Applies P H "mm0:check-binder" [encodeTable table, encodeContext target, encode expression, encodeBinder binder]
      (boolean (Preterm.checkBinder (signatureOf table) target expression binder)) := by
  cases binder with
  | bound sort =>
    refine Applies.equation (equation := P[64])
      (environment := [("table", encodeTable table), ("target", encodeContext target),
        ("expression", encode expression), ("sort", natural sort)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
      (check_sort_computes _ sort)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
      (typing_reused "mm0:bound-sort" (by decide) _ _ (bound_sort_computes target expression))
  | regular sort dependencies =>
    refine Applies.equation (equation := P[65])
      (environment := [("table", encodeTable table), ("target", encodeContext target),
        ("expression", encode expression), ("sort", natural sort),
        ("dependencies", encodeDependencies dependencies)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
      (check_type_computes _ sort)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
      (typing_reused "mm0:infer" (by decide) _ _ (infer_computes table target expression))

theorem binder_accepts_iff (table : SignatureTable) (target : Context) (expression : Preterm)
    (binder : Kernel.Binder) :
    Applies P H "mm0:check-binder" [encodeTable table, encodeContext target, encode expression, encodeBinder binder]
      (.sym "True") ↔ Preterm.FitsBinder (signatureOf table) target expression binder := by
  rw [← Preterm.checkBinder_iff]
  constructor
  · intro run
    have same := run.deterministic (binder_computes table target expression binder)
    cases checked : Preterm.checkBinder (signatureOf table) target expression binder with
    | false => simp [checked, boolean] at same
    | true => rfl
  · intro accepted
    simpa [accepted, boolean] using binder_computes table target expression binder

private theorem arguments_start (table : SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context) (result : Term)
    (next : Applies P H "mm0:check-arguments-view"
      [listView (expressions.map encode), listView (formal.map encodeBinder), encodeTable table, encodeContext target]
      result) :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal] result := by
  refine Applies.equation (equation := P[72])
    (environment := [("table", encodeTable table), ("target", encodeContext target),
      ("expressions", encodeExpressions expressions), ("formal", encodeContext formal)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))

private theorem arguments_cons (table : SignatureTable) (target : Context)
    (expression : Preterm) (expressions : List Preterm) (binder : Kernel.Binder) (formal : Context) (result : Term)
    (next : Applies P H "mm0:check-arguments-next"
      [boolean (Preterm.checkBinder (signatureOf table) target expression binder), encodeTable table,
        encodeContext target, encodeExpressions expressions, encodeContext formal] result) :
    Applies P H "mm0:check-arguments-view"
      [listView ((expression :: expressions).map encode), listView ((binder :: formal).map encodeBinder),
        encodeTable table, encodeContext target] result := by
  refine Applies.equation (equation := P[76])
    (environment := [("expression", encode expression), ("expressions", encodeExpressions expressions),
      ("binder", encodeBinder binder), ("formal", encodeContext formal),
      ("table", encodeTable table), ("target", encodeContext target)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (binder_computes table target expression binder)

private theorem arguments_next (table : SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context) (result : Term)
    (next : Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal] result) :
    Applies P H "mm0:check-arguments-next"
      [.sym "True", encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal]
      result := by
  refine Applies.equation (equation := P[78])
    (environment := [("table", encodeTable table), ("target", encodeContext target),
      ("expressions", encodeExpressions expressions), ("formal", encodeContext formal)]) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next

theorem arguments_computes (table : SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context) :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal]
      (boolean (Substitution.checkArguments (signatureOf table) target expressions formal)) := by
  induction expressions generalizing formal with
  | nil =>
    refine arguments_start table target [] formal _ ?_
    cases formal <;> exact ⟨1, rfl⟩
  | cons expression expressions ih =>
    refine arguments_start table target (expression :: expressions) formal _ ?_
    cases formal with
    | nil => exact ⟨1, rfl⟩
    | cons binder formal =>
      refine arguments_cons table target expression expressions binder formal _ ?_
      cases checked : Preterm.checkBinder (signatureOf table) target expression binder with
      | false => simp only [Substitution.checkArguments, checked, Bool.false_and]; exact ⟨1, rfl⟩
      | true =>
        simpa [Substitution.checkArguments, checked, boolean] using
          arguments_next table target expressions formal _ (ih formal)

theorem arguments_result_exact (table : SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context) (result : Term) :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal] result ↔
      result = boolean (Substitution.checkArguments (signatureOf table) target expressions formal) := by
  constructor
  · exact fun run => run.deterministic (arguments_computes table target expressions formal)
  · rintro rfl
    exact arguments_computes table target expressions formal

theorem arguments_accepts_iff (table : SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context) :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal] (.sym "True") ↔
      List.Forall₂ (Preterm.FitsBinder (signatureOf table) target) expressions formal := by
  rw [arguments_result_exact, ← Substitution.checkArguments_iff]
  cases Substitution.checkArguments (signatureOf table) target expressions formal <;> simp [boolean]

theorem accepted_arguments_have_exact_arity (table : SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context)
    (accepted : Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal] (.sym "True")) :
    expressions.length = formal.length := (arguments_accepts_iff table target expressions formal).mp accepted |>.length_eq

theorem arguments_completed_result (table : SignatureTable) (target : Context)
    (expressions : List Preterm) (formal : Context) (fuel : Nat)
    (finished : apply P H fuel "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal] ≠ .exhausted) :
    apply P H fuel "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal] =
      .value (boolean (Substitution.checkArguments (signatureOf table) target expressions formal)) :=
  (arguments_computes table target expressions formal).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalArguments
