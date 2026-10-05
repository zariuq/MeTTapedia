import Mettapedia.Languages.MM0.Presentation.FreshDummiesCorrespondence

/-! # Fresh dummy admission distinguishes support, sorts, arity and history -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies.Controls

open Kernel ComputationalContext ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => freshProgram
local notation "H" => computationalHost

private def target : Context := [.bound 0, .bound 0, .bound 1, .regular 2 {0}, .regular 2 ∅]

private theorem checked (arguments : List Preterm) (sorts images : List Nat) (result : Bool)
    (calculation : Definition.checkDummies target arguments sorts images = result) :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images]
      (boolean result) := by
  simpa only [calculation] using dummies_computes target arguments sorts images

theorem distinct_fresh_images_accept :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.term 0], encodeNaturals [0, 0], encodeNaturals [0, 1]]
      (.sym "True") := checked _ _ _ true (by decide)

theorem repeated_image_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.term 0], encodeNaturals [0, 0], encodeNaturals [1, 1]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem repeated_image_cannot_accept :
    ¬ Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.term 0], encodeNaturals [0, 0], encodeNaturals [1, 1]]
      (.sym "True") := by
  intro accepted
  have impossible := accepted.deterministic repeated_image_refuses
  simp at impossible

theorem forgetting_earlier_images_would_admit_collision :
    Definition.checkDummies target [.term 0] [0] [1] = true ∧
      Definition.checkDummies target [.term 0] [0, 0] [1, 1] = false := by decide

theorem direct_parameter_occurrence_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.var 0], encodeNaturals [0], encodeNaturals [0]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem declared_parameter_dependency_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.var 3], encodeNaturals [0], encodeNaturals [0]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem independent_parameter_accepts :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.var 4], encodeNaturals [0], encodeNaturals [0]]
      (.sym "True") := checked _ _ _ true (by decide)

theorem occurrence_inside_application_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.app (.term 7) (.var 0)], encodeNaturals [0], encodeNaturals [0]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem unknown_parameter_variable_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.var 9], encodeNaturals [0], encodeNaturals [0]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem wrong_dummy_sort_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [], encodeNaturals [0], encodeNaturals [2]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem regular_dummy_image_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [], encodeNaturals [2], encodeNaturals [4]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem missing_dummy_image_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [], encodeNaturals [0], encodeNaturals []]
      (.sym "False") := checked _ _ _ false (by decide)

theorem extra_dummy_image_refuses :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [], encodeNaturals [], encodeNaturals [0]]
      (.sym "False") := checked _ _ _ false (by decide)

theorem no_dummy_does_not_replace_argument_typing :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.var 9], encodeNaturals [], encodeNaturals []]
      (.sym "True") := checked _ _ _ true (by decide)

theorem exhaustion_is_not_failed_freshness :
    apply P H 0 "mm0:check-dummies"
      [encodeContext target, encodeExpressions [.term 0], encodeNaturals [0, 0], encodeNaturals [0, 1]] =
      .exhausted := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies.Controls
