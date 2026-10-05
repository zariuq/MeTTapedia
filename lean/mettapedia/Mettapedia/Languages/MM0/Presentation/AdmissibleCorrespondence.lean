import Mettapedia.Languages.MM0.Presentation.AdmissibleMatrix

/-!
# Exact authored admissible-substitution checking

The full computation composes argument typing, indexed entry construction and
the complete dependency matrix. Its Boolean result agrees with the independent
kernel on all finite inputs. Acceptance is equivalent to independent admissible
substitution, without assuming the requested conclusion as a precondition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissibleProgram
local notation "H" => computationalHost

private theorem matrix_computes (target : Context) (entries : List Substitution.Entry) :
    Applies P H "mm0:admissible-entries" [encodeContext target, encodeEntries entries]
      (boolean (entries.all (Substitution.checkRow target entries))) := by
  refine Applies.equation (equation := P[100])
    (environment := [("target", encodeContext target), ("entries", encodeEntries entries)]) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (rows_computes target entries entries)

private theorem typed_computes (formal target : Context) (expressions : List Preterm) :
    Applies P H "mm0:admissible-typed"
      [.sym "True", encodeContext target, encodeContext formal, encodeExpressions expressions]
      (boolean ((Substitution.entries formal expressions).all
        (Substitution.checkRow target (Substitution.entries formal expressions)))) := by
  refine Applies.equation (equation := P[99])
    (environment := [("target", encodeContext target), ("formal", encodeContext formal),
      ("expressions", encodeExpressions expressions)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (matrix_computes target _)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ⟨1, rfl⟩ .nil)))
    (entries_computes formal expressions)

theorem admissible_computes (table : SignatureTable) (formal target : Context) (expressions : List Preterm) :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions]
      (boolean (Substitution.checkAdmissible (signatureOf table) formal target expressions)) := by
  refine Applies.equation (equation := P[97])
    (environment := [("table", encodeTable table), ("formal", encodeContext formal),
      ("target", encodeContext target), ("expressions", encodeExpressions expressions)]) (by rfl) (by rfl) ?_
  refine Evaluates.call
    (values := [boolean (Substitution.checkArguments (signatureOf table) target expressions formal),
      encodeContext target, encodeContext formal, encodeExpressions expressions]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
      (arguments_reused table target expressions formal)
  · cases checked : Substitution.checkArguments (signatureOf table) target expressions formal with
    | false => simp only [Substitution.checkAdmissible, checked, Bool.false_and]; exact ⟨1, rfl⟩
    | true =>
      simp only [Substitution.checkAdmissible, checked, Bool.true_and]
      exact typed_computes formal target expressions

theorem admissible_result_exact (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (result : Term) :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] result ↔
      result = boolean (Substitution.checkAdmissible (signatureOf table) formal target expressions) := by
  constructor
  · exact fun run => run.deterministic (admissible_computes table formal target expressions)
  · rintro rfl
    exact admissible_computes table formal target expressions

theorem admissible_accepts_iff (table : SignatureTable) (formal target : Context) (expressions : List Preterm) :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] (.sym "True") ↔
      Substitution.Admissible (signatureOf table) formal target expressions := by
  rw [admissible_result_exact, ← Substitution.checkAdmissible_iff]
  cases Substitution.checkAdmissible (signatureOf table) formal target expressions <;> simp [boolean]

theorem admissible_refuses_iff (table : SignatureTable) (formal target : Context) (expressions : List Preterm) :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] (.sym "False") ↔
      ¬ Substitution.Admissible (signatureOf table) formal target expressions := by
  rw [admissible_result_exact, ← Substitution.checkAdmissible_iff]
  cases Substitution.checkAdmissible (signatureOf table) formal target expressions <;> simp [boolean]

theorem admitted_arguments_are_typed (table : SignatureTable) (formal target : Context) (expressions : List Preterm)
    (accepted : Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] (.sym "True")) :
    List.Forall₂ (Preterm.FitsBinder (signatureOf table) target) expressions formal :=
  ((admissible_accepts_iff table formal target expressions).mp accepted).typed

theorem admitted_arguments_preserve_independence (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm)
    (accepted : Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] (.sym "True"))
    {u v sort image : Nat} {binder : Kernel.Binder} {expression : Preterm}
    (formalBound : formal[u]? = some (.bound sort)) (formalOther : formal[v]? = some binder)
    (independent : ¬ Preterm.HasVar formal u (.var v))
    (boundImage : expressions[u]? = some (.var image)) (otherImage : expressions[v]? = some expression) :
    ¬ Preterm.HasVar target image expression :=
  ((admissible_accepts_iff table formal target expressions).mp accepted).preserves_independence
    formalBound formalOther independent boundImage otherImage

theorem admissible_completed_result (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (fuel : Nat)
    (finished : apply P H fuel "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] ≠ .exhausted) :
    apply P H fuel "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] =
      .value (boolean (Substitution.checkAdmissible (signatureOf table) formal target expressions)) :=
  (admissible_computes table formal target expressions).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible
