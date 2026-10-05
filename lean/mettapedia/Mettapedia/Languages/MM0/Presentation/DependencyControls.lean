import Mettapedia.Languages.MM0.Presentation.DependencyCorrespondence

/-! # Controls for formal and target dependencies in authored MM0 checking -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDependency.Controls

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => dependencyProgram
local notation "H" => computationalHost

private theorem checked (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) (result : Bool)
    (calculation : Substitution.checkPair target formalBound targetBound ((binder, expression), position) = result) :
    Applies P H "mm0:check-pair"
      [encodeContext target, natural formalBound, natural targetBound,
        encodeBinder binder, natural position, encode expression] (boolean result) := by
  simpa only [calculation] using pair_computes target formalBound targetBound binder position expression

theorem independent_closed_image_accepts :
    Applies P H "mm0:check-pair"
      [encodeContext [.bound 0], natural 0, natural 0,
        encodeBinder (.regular 1 ∅), natural 1, encode (.term 3)] (.sym "True") :=
  checked _ _ _ _ _ _ true (by decide)

theorem target_dependency_refuses :
    Applies P H "mm0:check-pair"
      [encodeContext [.bound 0, .regular 1 {0}], natural 0, natural 0,
        encodeBinder (.regular 1 ∅), natural 1, encode (.var 1)] (.sym "False") :=
  checked _ _ _ _ _ _ false (by decide)

theorem declared_formal_dependency_permits_occurrence :
    Applies P H "mm0:check-pair"
      [encodeContext [.bound 0, .regular 1 {0}], natural 0, natural 0,
        encodeBinder (.regular 1 {0}), natural 1, encode (.var 1)] (.sym "True") :=
  checked _ _ _ _ _ _ true (by decide)

theorem formal_and_target_indices_are_distinct :
    Applies P H "mm0:check-pair"
      [encodeContext [.regular 1 ∅, .bound 0], natural 0, natural 1,
        encodeBinder (.regular 1 ∅), natural 1, encode (.app (.term 0) (.var 1))]
      (.sym "False") := checked _ _ _ _ _ _ false (by decide)

theorem same_bound_images_refuse :
    Applies P H "mm0:check-pair"
      [encodeContext [.bound 0], natural 0, natural 0,
        encodeBinder (.bound 0), natural 1, encode (.var 0)] (.sym "False") :=
  checked _ _ _ _ _ _ false (by decide)

theorem distinct_bound_images_accept :
    Applies P H "mm0:check-pair"
      [encodeContext [.bound 0, .bound 0], natural 0, natural 1,
        encodeBinder (.bound 0), natural 1, encode (.var 0)] (.sym "True") :=
  checked _ _ _ _ _ _ true (by decide)

theorem bound_occurrence_under_constructor_still_refuses :
    Applies P H "mm0:check-pair"
      [encodeContext [.bound 0], natural 0, natural 0,
        encodeBinder (.regular 1 ∅), natural 1, encode (.app (.term 2) (.var 0))]
      (.sym "False") := checked _ _ _ _ _ _ false (by decide)

theorem later_bound_variable_constrains_earlier_regular_image :
    Applies P H "mm0:check-pair"
      [encodeContext [.bound 0, .regular 1 {0}], natural 1, natural 0,
        encodeBinder (.regular 1 ∅), natural 0, encode (.var 1)] (.sym "False") :=
  checked _ _ _ _ _ _ false (by decide)

theorem missing_target_variable_refuses_independence :
    Applies P H "mm0:check-pair"
      [encodeContext [], natural 0, natural 0,
        encodeBinder (.regular 1 ∅), natural 1, encode (.var 9)] (.sym "False") :=
  checked _ _ _ _ _ _ false (by decide)

/-- A dependency permission does not replace the separate argument-typing check. -/
theorem pair_permission_alone_does_not_establish_typing :
    Applies P H "mm0:check-pair"
      [encodeContext [], natural 0, natural 0,
        encodeBinder (.regular 1 {0}), natural 1, encode (.var 9)] (.sym "True") ∧
      Preterm.checkBinder (fun _ => none) [] (.var 9) (.regular 1 {0}) = false := by
  exact ⟨checked _ _ _ _ _ _ true (by decide), by decide⟩

theorem cannot_accept_a_forbidden_target_dependency :
    ¬ Applies P H "mm0:check-pair"
      [encodeContext [.bound 0, .regular 1 {0}], natural 0, natural 0,
        encodeBinder (.regular 1 ∅), natural 1, encode (.var 1)] (.sym "True") := by
  intro run
  have impossible := run.deterministic target_dependency_refuses
  simp at impossible

theorem zero_fuel_is_not_a_dependency_answer :
    apply P H 0 "mm0:check-pair"
      [encodeContext [.bound 0], natural 0, natural 0,
        encodeBinder (.regular 1 ∅), natural 1, encode (.term 3)] = .exhausted := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalDependency.Controls
