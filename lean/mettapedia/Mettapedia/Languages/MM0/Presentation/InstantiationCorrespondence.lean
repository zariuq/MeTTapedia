import Mettapedia.Languages.MM0.Presentation.InstantiationProgram

/-!
# Admissible term instantiation computes the independent operation

This connects the actual composed equations, including the replacement-list
adapter, to admissibility and simultaneous substitution. Inputs with an
inadmissible substitution or a missing referenced image return `None`.
Resource exhaustion remains an unfinished computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => instantiationProgram
local notation "H" => computationalHost

private theorem values_start (expressions : List Preterm) (result : Term)
    (next : Applies P H "mm0:substitution-values-view" [listView (expressions.map encode)] result) :
    Applies P H "mm0:substitution-values" [encodeExpressions expressions] result := by
  refine Applies.equation (equation := P[112])
    (environment := [("values", encodeExpressions expressions)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem values_cons (first : Preterm) (rest : List Preterm)
    (child : Applies P H "mm0:substitution-values" [encodeExpressions rest] (encodeValues rest)) :
    Applies P H "mm0:substitution-values-view" [listView ((first :: rest).map encode)]
      (encodeValues (first :: rest)) := by
  refine Applies.equation (equation := P[114])
    (environment := [("first", encode first), ("rest", encodeExpressions rest)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (.constructor (by rfl) (by rfl))
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) child

theorem values_computes (expressions : List Preterm) :
    Applies P H "mm0:substitution-values" [encodeExpressions expressions] (encodeValues expressions) := by
  induction expressions with
  | nil => exact values_start [] _ ⟨1, rfl⟩
  | cons first rest ih => exact values_start (first :: rest) _ (values_cons first rest ih)

theorem values_result_exact (expressions : List Preterm) (result : Term) :
    Applies P H "mm0:substitution-values" [encodeExpressions expressions] result ↔ result = encodeValues expressions := by
  constructor
  · exact fun run => run.deterministic (values_computes expressions)
  · rintro rfl
    exact values_computes expressions

private theorem admitted_computes (body : Preterm) (expressions : List Preterm) :
    Applies P H "mm0:instantiation-admitted" [.sym "True", encode body, encodeExpressions expressions]
      (encodeResult (body.substitute (Substitution.ofList expressions))) := by
  refine Applies.equation (equation := P[117])
    (environment := [("body", encode body), ("expressions", encodeExpressions expressions)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (substitution_reused body expressions)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (values_computes expressions)

theorem instantiation_computes (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (body : Preterm) :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions, encode body]
      (encodeResult (Substitution.instantiate (signatureOf table) formal target expressions body)) := by
  refine Applies.equation (equation := P[115])
    (environment := [("table", encodeTable table), ("formal", encodeContext formal), ("target", encodeContext target),
      ("expressions", encodeExpressions expressions), ("body", encode body)]) (by rfl) (by rfl) ?_
  refine Evaluates.call
    (values := [boolean (Substitution.checkAdmissible (signatureOf table) formal target expressions),
      encode body, encodeExpressions expressions]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
      (admissible_reused table formal target expressions)
  · cases checked : Substitution.checkAdmissible (signatureOf table) formal target expressions with
    | false => simp only [Substitution.instantiate, checked, Bool.false_eq_true, ↓reduceIte]; exact ⟨1, rfl⟩
    | true =>
      simp only [Substitution.instantiate, checked, ↓reduceIte]
      exact admitted_computes body expressions

theorem instantiation_result_exact (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (body : Preterm) (result : Term) :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions, encode body] result ↔
      result = encodeResult (Substitution.instantiate (signatureOf table) formal target expressions body) := by
  constructor
  · exact fun run => run.deterministic (instantiation_computes table formal target expressions body)
  · rintro rfl
    exact instantiation_computes table formal target expressions body

theorem instantiation_accepts_iff (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (body result : Preterm) :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions, encode body]
      (encodeResult (some result)) ↔
      Substitution.Admissible (signatureOf table) formal target expressions ∧
        Preterm.Substitutes (Substitution.ofList expressions) body result := by
  rw [instantiation_result_exact, ← Substitution.instantiate_eq_some_iff]
  constructor
  · exact fun same => (encodeResult_injective same).symm
  · exact fun same => congrArg encodeResult same.symm

theorem instantiation_refuses_iff (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (body : Preterm) :
    Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions, encode body]
      (.sym "None") ↔ Substitution.instantiate (signatureOf table) formal target expressions body = none := by
  rw [instantiation_result_exact]
  constructor
  · exact fun same => (encodeResult_injective (show encodeResult none = _ from same)).symm
  · exact fun same => congrArg encodeResult same.symm

theorem admitted_typed_body_has_a_result (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (body : Preterm) (remaining : Context) (sort : Nat)
    (admitted : Substitution.Admissible (signatureOf table) formal target expressions)
    (typed : Preterm.HasType (signatureOf table) formal body remaining sort) :
    ∃ result, Applies P H "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions, encode body]
      (encodeResult (some result)) := by
  obtain ⟨result, computed⟩ := admitted.instantiate_defined typed
  refine ⟨result, ?_⟩
  simpa only [computed] using instantiation_computes table formal target expressions body

theorem instantiation_completed_result (table : SignatureTable) (formal target : Context)
    (expressions : List Preterm) (body : Preterm) (fuel : Nat)
    (finished : apply P H fuel "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions, encode body] ≠ .exhausted) :
    apply P H fuel "mm0:instantiate-term"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions, encode body] =
      .value (encodeResult (Substitution.instantiate (signatureOf table) formal target expressions body)) :=
  (instantiation_computes table formal target expressions body).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation
