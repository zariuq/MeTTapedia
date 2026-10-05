import Mettapedia.GSLT.LanguageDef.DeterministicEquations.InferenceExtraction

/-! # Complete extracted MM0 inference: typed results and refusal

The controls exercise the complete source computation and its independent
typing judgment. Declaration admission and decoding arbitrary external atoms
remain separate from this typed computation boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Inference.Controls

open Mettapedia.Languages.MM0
open Kernel
open Presentation.ComputationalContext

private def declarations : List (Nat × TermDecl) :=
  [(0, ⟨[], 0, ∅⟩), (1, ⟨[.bound 0], 2, {0}⟩),
    (2, ⟨[.regular 0 ∅], 3, ∅⟩),
    (3, ⟨[.bound 0, .regular 0 {0}], 4, {0}⟩), (4, ⟨[], 1, ∅⟩)]

private def inputs (entries : List (Nat × TermDecl)) (context : Context) (expression : Preterm) :
    List Term :=
  [encodeList (encodePair natural encodeDeclaration) entries, encodeList encodeBinder context,
    Presentation.encode expression]

private theorem accepted (entries : List (Nat × TermDecl)) (context remaining : Context)
    (expression : Preterm) (sort : Nat)
    (source : expression.infer (termTable entries) context = some (remaining, sort)) :
    Applies inferProgram dataEqualityHost inferHead (inputs entries context expression)
      (encodeOption encodeExpressionType (some (remaining, sort))) :=
  (infer_accepts_iff entries context expression remaining sort).mpr
    ((Preterm.infer_eq_some_iff _ _ _ _ _).mp source)

private theorem refused (entries : List (Nat × TermDecl)) (context : Context)
    (expression : Preterm) (source : expression.infer (termTable entries) context = none) :
    Applies inferProgram dataEqualityHost inferHead (inputs entries context expression) (.sym "None") :=
  (infer_refuses_iff entries context expression).mpr ((Preterm.infer_none_iff _ _ _).mp source)

theorem bound_variable :
    Applies inferProgram dataEqualityHost inferHead (inputs declarations [.bound 0] (.var 0))
      (encodeOption encodeExpressionType (some ([], 0))) :=
  accepted _ _ _ _ _ rfl

theorem regular_variable :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [.bound 0, .regular 1 {0}] (.var 1))
      (encodeOption encodeExpressionType (some ([], 1))) :=
  accepted _ _ _ _ _ rfl

theorem partial_constructor :
    Applies inferProgram dataEqualityHost inferHead (inputs declarations [] (.term 1))
      (encodeOption encodeExpressionType (some ([.bound 0], 2))) :=
  accepted _ _ _ _ _ rfl

theorem bound_application :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [.bound 0] (.app (.term 1) (.var 0)))
      (encodeOption encodeExpressionType (some ([], 2))) :=
  accepted _ _ _ _ _ rfl

theorem regular_application :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [.regular 0 ∅] (.app (.term 2) (.var 0)))
      (encodeOption encodeExpressionType (some ([], 3))) :=
  accepted _ _ _ _ _ rfl

theorem nested_application :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [.bound 0] (.app (.app (.term 3) (.var 0)) (.term 0)))
      (encodeOption encodeExpressionType (some ([], 4))) :=
  accepted _ _ _ _ _ rfl

theorem bound_slot_rejects_regular :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [.regular 0 ∅] (.app (.term 1) (.var 0))) (.sym "None") :=
  refused _ _ _ rfl

theorem regular_slot_rejects_partial :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [] (.app (.term 2) (.term 1))) (.sym "None") :=
  refused _ _ _ rfl

theorem regular_slot_rejects_wrong_sort :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [] (.app (.term 2) (.term 4))) (.sym "None") :=
  refused _ _ _ rfl

theorem saturated_function_rejects_argument :
    Applies inferProgram dataEqualityHost inferHead
      (inputs declarations [.bound 0] (.app (.term 0) (.var 0))) (.sym "None") :=
  refused _ _ _ rfl

theorem missing_context_cell :
    Applies inferProgram dataEqualityHost inferHead (inputs declarations [] (.var 0)) (.sym "None") :=
  refused _ _ _ rfl

theorem missing_declaration :
    Applies inferProgram dataEqualityHost inferHead (inputs declarations [] (.term 5)) (.sym "None") :=
  refused _ _ _ rfl

theorem signature_first_occurrence :
    Applies inferProgram dataEqualityHost inferHead
      (inputs [(0, ⟨[.bound 0], 2, ∅⟩), (0, ⟨[], 1, ∅⟩)] [] (.term 0))
      (encodeOption encodeExpressionType (some ([.bound 0], 2))) :=
  accepted _ _ _ _ _ rfl

theorem reordered_signature_changes_result :
    Applies inferProgram dataEqualityHost inferHead
      (inputs [(0, ⟨[], 1, ∅⟩), (0, ⟨[.bound 0], 2, ∅⟩)] [] (.term 0))
      (encodeOption encodeExpressionType (some ([], 1))) :=
  accepted _ _ _ _ _ rfl

theorem unbounded_declaration_index :
    Applies inferProgram dataEqualityHost inferHead
      (inputs [(18446744073709551616, ⟨[], 9, ∅⟩)] [] (.term 18446744073709551616))
      (encodeOption encodeExpressionType (some ([], 9))) :=
  accepted _ _ _ _ _ rfl

theorem wrong_result_refused :
    ¬ Applies inferProgram dataEqualityHost inferHead (inputs declarations [.bound 0] (.var 0))
      (encodeOption encodeExpressionType (some ([], 1))) := by
  intro observed
  have equal := observed.deterministic bound_variable
  have source := encodeOption_injective encodeExpressionType_injective equal
  cases source

/-- A typed variable elsewhere does not rescue a failed bound-slot application. -/
theorem independently_typed_operand_does_not_rescue_application :
    Preterm.HasType (termTable declarations) [.regular 0 ∅] (.var 0) [] 0 ∧
      ¬ Applies inferProgram dataEqualityHost inferHead
        (inputs declarations [.regular 0 ∅] (.app (.term 1) (.var 0)))
        (encodeOption encodeExpressionType (some ([], 2))) := by
  constructor
  · exact Preterm.HasType.var (binder := .regular 0 ∅) rfl
  · intro observed
    have equal := observed.deterministic bound_slot_rejects_regular
    cases equal

theorem zero_fuel_is_exhaustion :
    apply inferProgram dataEqualityHost 0 inferHead (inputs declarations [] (.term 5)) =
      .exhausted := by
  have atZero (first second third : Term) :
      apply inferProgram dataEqualityHost 0 inferHead [first, second, third] = .exhausted := by
    have defined : inferProgram.definesAt inferHead 3 = true := by decide
    unfold apply applyWith
    simp only [List.length_cons, List.length_nil]
    simp only [defined, ↓reduceIte]
    unfold inferHead
    rw [inferProgram.selection_0]
    rfl
  exact atZero _ _ _

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Inference.Controls
