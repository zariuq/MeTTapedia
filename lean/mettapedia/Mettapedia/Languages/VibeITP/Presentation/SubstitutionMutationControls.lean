import Mettapedia.Languages.VibeITP.Presentation.SubstitutionControls

/-!
# Authored substitution equation mutation

The control changes the parameter-index expression and composes two completed
runs of the unchanged equation evaluator from actual selected equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution.MutationControls

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-- Only the authored reverse-index expression changes. -/
private def forwardIndex (equation : Equation) : Equation :=
  if equation.name = "substitute-parameter" then
    { equation with body := .expr [.sym "vibe:shift", .var "table",
      .expr [.sym "vibe:get-default", .var "images", .var "relative", encode (.bvar 0)],
      .var "offset", natural 0] }
  else equation

private def forwardIndexProgram : Program := shiftProgram ++ substitutionEquations.map forwardIndex

local notation "M" => forwardIndexProgram
local notation "A" => substitutionEquations
local notation "H" => computationalHost

private theorem mutated_head (equation : Equation) : (forwardIndex equation).head = equation.head := by
  unfold forwardIndex
  split <;> rfl

private theorem mutated_disjoint :
    ∀ equation ∈ substitutionEquations.map forwardIndex, equation.head ∉ shiftProgram.calledHeads := by
  intro equation member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  rw [mutated_head]
  exact substitutionEquations_disjoint original originalMember

private theorem first_image (first : Term) (rest : List Term) (default : Term) :
    Applies M H "vibe:get-default" [.list (first :: rest), natural 0, default] first := by
  have selectedFirst : Applies M H "vibe:get-zero"
      [.sym "True", first, .list rest, natural 0, default] first := by
    refine Applies.equation (equation := A[6])
      (environment := [("first", first), ("rest", .list rest), ("index", natural 0), ("default", default)])
      (by rfl) (by rfl) ?_
    exact .variable (by rfl)
  have viewed : Applies M H "vibe:get-view"
      [listView (first :: rest), natural 0, default] first := by
    refine Applies.equation (equation := A[5])
      (environment := [("first", first), ("rest", .list rest), ("index", natural 0), ("default", default)])
      (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) selectedFirst
    exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (Applies.primitive (by rfl) (computationalHost_zero 0))
  refine Applies.equation (equation := A[3])
    (environment := [("values", .list (first :: rest)), ("index", natural 0), ("default", default)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) viewed
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (Applies.primitive (by rfl) (computationalHost_list_view (first :: rest)))

private def images : Term := .list (encodeTerms [.bvar 16, .bvar 17])
private def answer : Term := encodeResult (some (.bvar 16))

private theorem mutated_parameter :
    Applies M H "vibe:subst-bvar-param" [.sym "True", encodeTable [], natural 2, images, natural 0, natural 0]
      answer := by
  have shifted : Applies M H "vibe:shift" [encodeTable [], encode (.bvar 16), natural 0, natural 0] answer := by
    apply (Applies.append_iff shiftProgram (substitutionEquations.map forwardIndex) H mutated_disjoint
      "vibe:shift" (by decide +kernel) _ _).mpr
    exact shift_computes [] 0 0 (.bvar 16)
  refine Applies.equation (equation := forwardIndex A[16])
    (environment := [("table", encodeTable []), ("count", natural 2), ("images", images),
      ("offset", natural 0), ("relative", natural 0)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)))) shifted
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (Evaluates.call (by simp [Special]) (.cons (.literal _ _ _ _) .nil)
        (Applies.constructor (by rfl) (by rfl))) .nil)))
    (first_image (encode (.bvar 16)) [encode (.bvar 17)] (encode (.bvar 0)))

private theorem mutated_variable :
    Applies M H "vibe:subst-go" [encodeTable [], natural 2, images, natural 0, encode (.bvar 0)] answer := by
  have high : Applies M H "vibe:subst-bvar-low"
      [.sym "False", encodeTable [], natural 2, images, natural 0, natural 0] answer := by
    refine Applies.equation (equation := A[15])
      (environment := [("table", encodeTable []), ("count", natural 2), ("images", images),
        ("offset", natural 0), ("i", natural 0)]) (by rfl) (by rfl) ?_
    have relative : Evaluates M H [("table", encodeTable []), ("count", natural 2), ("images", images),
        ("offset", natural 0), ("i", natural 0)]
        (.expr [.sym "nik:nat-monus", .var "i", .var "offset"]) (natural 0) :=
      Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (Applies.primitive (by rfl) (naturalArithmeticHost_monus 0 0))
    refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons relative .nil)))))) mutated_parameter
    exact Evaluates.call (by simp [Special]) (.cons relative (.cons (.variable (by rfl)) .nil))
      (Applies.primitive (by rfl) (naturalArithmeticHost_lt 0 2))
  refine Applies.equation (equation := A[11])
    (environment := [("table", encodeTable []), ("count", natural 2), ("images", images),
      ("offset", natural 0), ("i", natural 0)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) high
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (Applies.primitive (by rfl) (naturalArithmeticHost_le 1 0))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil))
    (Applies.primitive (by rfl) (naturalArithmeticHost_add 0 1))

/-- Both whole calls have finite completed runs; the mutant chooses the
first replacement while the original chooses the final replacement. -/
theorem changed_parameter_equation_changes_completed_result :
    Applies substitutionProgram H "vibe:subst"
      [encodeTable [], natural 2, images, encode (.bvar 0), natural 0] (encodeResult (some (.bvar 17))) ∧
    Applies M H "vibe:subst"
      [encodeTable [], natural 2, images, encode (.bvar 0), natural 0] answer := by
  constructor
  · exact substitution_computes [] 2 [.bvar 16, .bvar 17] (.bvar 0) 0
  · have nonzero : Applies M H "vibe:subst-zero"
        [.sym "False", encodeTable [], natural 2, images, encode (.bvar 0), natural 0] answer := by
      refine Applies.equation (equation := A[10])
        (environment := [("table", encodeTable []), ("count", natural 2), ("images", images),
          ("body", encode (.bvar 0)), ("offset", natural 0)]) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) mutated_variable
    refine Applies.equation (equation := A[8])
      (environment := [("table", encodeTable []), ("count", natural 2), ("images", images),
        ("body", encode (.bvar 0)), ("offset", natural 0)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) nonzero
    exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (Applies.primitive (by rfl) (computationalHost_zero 2))

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution.MutationControls
