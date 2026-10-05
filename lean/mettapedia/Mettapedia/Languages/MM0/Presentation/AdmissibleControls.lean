import Mettapedia.Languages.MM0.Presentation.AdmissibleCorrespondence

/-! # Whole-computation controls for authored MM0 admissibility -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible.Controls

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissibleProgram
local notation "H" => computationalHost

private def table : SignatureTable :=
  [(0, ⟨[.regular 0 ∅], 1, ∅⟩), (1, ⟨[], 1, ∅⟩), (2, ⟨[.bound 0], 1, ∅⟩)]
private def independent : Context := [.bound 0, .regular 1 ∅]
private def dependent : Context := [.bound 0, .regular 1 {0}]

private theorem checked (formal target : Context) (expressions : List Preterm) (result : Bool)
    (calculation : Substitution.checkAdmissible (signatureOf table) formal target expressions = result) :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions] (boolean result) := by
  simpa only [calculation] using admissible_computes table formal target expressions

theorem closed_image_accepts :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext [.regular 1 ∅, .bound 0],
        encodeExpressions [.var 1, .term 1]] (.sym "True") := checked _ _ _ true (by decide)

theorem confusing_formal_and_target_positions_refuses :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext [.regular 1 ∅, .bound 0],
        encodeExpressions [.var 1, .app (.term 0) (.var 1)]] (.sym "False") := checked _ _ _ false (by decide)

theorem target_dependency_refuses :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext dependent, encodeExpressions [.var 0, .var 1]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem permitted_dependency_accepts :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext dependent, encodeContext dependent, encodeExpressions [.var 0, .var 1]]
      (.sym "True") := checked _ _ _ true (by decide)

theorem independent_variable_accepts :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext independent, encodeExpressions [.var 0, .var 1]]
      (.sym "True") := checked _ _ _ true (by decide)

theorem bound_occurrence_under_binding_constructor_refuses :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext [.bound 0],
        encodeExpressions [.var 0, .app (.term 2) (.var 0)]] (.sym "False") := checked _ _ _ false (by decide)

theorem colliding_bound_images_refuse :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext [.bound 0, .bound 0], encodeContext [.bound 0],
        encodeExpressions [.var 0, .var 0]] (.sym "False") := checked _ _ _ false (by decide)

theorem distinct_bound_images_accept :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext [.bound 0, .bound 0], encodeContext [.bound 0, .bound 0],
        encodeExpressions [.var 1, .var 0]] (.sym "True") := checked _ _ _ true (by decide)

theorem later_bound_image_constrains_earlier_replacement :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext [.regular 1 ∅, .bound 0], encodeContext dependent,
        encodeExpressions [.var 1, .var 0]] (.sym "False") := checked _ _ _ false (by decide)

/-- Retaining only the unvisited suffix would lose this dependency obligation. -/
theorem suffix_only_matrix_loses_an_earlier_dependency :
    Substitution.checkRow dependent [((.bound 0, .var 0), 1)] ((.bound 0, .var 0), 1) = true ∧
    Substitution.checkRow dependent [((.regular 1 ∅, .var 1), 0), ((.bound 0, .var 0), 1)]
      ((.bound 0, .var 0), 1) = false := by decide

theorem extra_argument_refuses :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext independent,
        encodeExpressions [.var 0, .var 1, .term 1]] (.sym "False") := checked _ _ _ false (by decide)

theorem missing_argument_refuses :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext independent,
        encodeExpressions [.var 0]] (.sym "False") := checked _ _ _ false (by decide)

theorem empty_zip_does_not_make_missing_arguments_admissible :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext independent,
        encodeExpressions []] (.sym "False") := checked _ _ _ false (by decide)

theorem dependency_permission_does_not_admit_missing_target_variable :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext [.regular 1 {0}], encodeContext [],
        encodeExpressions [.var 9]] (.sym "False") := checked _ _ _ false (by decide)

theorem nonvariable_bound_image_refuses_before_matrix :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext [.bound 1], encodeContext [],
        encodeExpressions [.term 1]] (.sym "False") := checked _ _ _ false (by decide)

theorem empty_substitution_accepts :
    Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext [], encodeContext [], encodeExpressions []] (.sym "True") :=
  checked _ _ _ true (by decide)

theorem cannot_accept_forbidden_dependency :
    ¬ Applies P H "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext dependent, encodeExpressions [.var 0, .var 1]]
      (.sym "True") := by
  intro accepted
  have impossible := accepted.deterministic target_dependency_refuses
  simp at impossible

theorem zero_fuel_does_not_refuse_an_admissible_substitution :
    apply P H 0 "mm0:check-admissible"
      [encodeTable table, encodeContext independent, encodeContext independent, encodeExpressions [.var 0, .var 1]] =
      .exhausted := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible.Controls
