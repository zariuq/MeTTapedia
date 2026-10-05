import Mettapedia.Languages.MM0.Presentation.FreeVariablesProgram

/-! # Authored resolution of every declared MM0 binding image -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => freeVariablesProgram
local notation "A" => freeVariablesEquations
local notation "H" => computationalHost

private def targetImage (binder : Option Kernel.Binder) (expected image : Nat) : Option Nat :=
  match binder with
  | some (.bound actual) => if actual = expected then some image else none
  | _ => none

private def argumentImage (target : Context) (expected : Nat) : Option Preterm → Option Nat
  | some (.var image) => targetImage target[image]? expected image
  | _ => none

private def formalImage (target : Context) (arguments : List Preterm) (position : Nat) : Option Kernel.Binder → Option Nat
  | some (.bound expected) => argumentImage target expected arguments[position]?
  | _ => none

private theorem boundImage_form (target formal : Context) (arguments : List Preterm) (position : Nat) :
    boundImage? target formal arguments position = formalImage target arguments position formal[position]? := by
  cases knownFormal : formal[position]? with
  | none => simp [boundImage?, FreeVariables.checkImage, knownFormal, formalImage]
  | some binder =>
      cases binder with
      | regular => simp [boundImage?, FreeVariables.checkImage, knownFormal, formalImage]
      | bound expected =>
          cases knownArgument : arguments[position]? with
          | none => simp [boundImage?, FreeVariables.checkImage, knownFormal, knownArgument, formalImage, argumentImage]
          | some argument =>
              cases argument with
              | term => simp [boundImage?, FreeVariables.checkImage, knownFormal, knownArgument, formalImage, argumentImage]
              | app => simp [boundImage?, FreeVariables.checkImage, knownFormal, knownArgument, formalImage, argumentImage]
              | var image =>
                  cases knownTarget : target[image]? with
                  | none => simp [boundImage?, FreeVariables.checkImage, knownFormal, knownArgument, knownTarget,
                      formalImage, argumentImage, targetImage]
                  | some binder =>
                      cases binder <;>
                        simp [boundImage?, FreeVariables.checkImage, FreeVariables.argumentIndex?, knownFormal,
                          knownArgument, knownTarget, formalImage, argumentImage, targetImage]

private theorem image_equal_computes (same : Bool) (image : Nat) :
    Applies P H "mm0:free-image-equal" [boolean same, natural image]
      (encodeSortResult (if same then some image else none)) := by
  cases same <;> exact ⟨2, by rw [free_apply _ (by decide)]; rfl⟩

private theorem image_target_computes (binder : Option Kernel.Binder) (expected image : Nat) :
    Applies P H "mm0:free-image-target" [encodeBinderResult binder, natural expected, natural image]
      (encodeSortResult (targetImage binder expected image)) := by
  cases binder with
  | none => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | some binder =>
      cases binder with
      | regular => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
      | bound actual =>
          refine free_equation (equation := A[8])
            (environment := [("actual", natural actual), ("expected", natural expected), ("image", natural image)])
            (by decide) (by rfl) (by rfl) ?_
          refine Evaluates.call (values := [boolean (decide (actual = expected)), natural image]) (by simp [Special])
            (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
              (.primitive (by rfl) (computationalHost_binary (operation := .equal) rfl _ _ (by decide) (by decide)))
          · simpa only [targetImage, decide_eq_true_eq] using image_equal_computes (decide (actual = expected)) image

private theorem image_argument_computes (target : Context) (expected : Nat) (argument : Option Preterm) :
    Applies P H "mm0:free-image-argument" [encodeItemResult (argument.map encode), encodeContext target, natural expected]
      (encodeSortResult (argumentImage target expected argument)) := by
  cases argument with
  | none => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | some argument =>
      cases argument with
      | term => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
      | app => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
      | var image =>
          refine free_equation (equation := A[4])
            (environment := [("image", natural image), ("target", encodeContext target), ("sort", natural expected)])
            (by decide) (by rfl) (by rfl) ?_
          refine Evaluates.call (by simp [Special])
            (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
            (image_target_computes target[image]? expected image)
          exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
            (typing_reused _ (by decide) _ _ (context_lookup_computes target image))

private theorem argument_lookup (arguments : List Preterm) (position : Nat) :
    Applies P H "mm0:data-at" [encodeExpressions arguments, natural position]
      (encodeItemResult (arguments[position]?.map encode)) := by
  have computed := at_computes (arguments.map encode) position
  rw [List.getElem?_map] at computed
  apply typing_reused _ (by decide)
  cases known : arguments[position]? <;>
    simpa [encodeExpressions, known, encodeItemResult] using computed

private theorem image_formal_computes (target : Context) (arguments : List Preterm) (position : Nat)
    (binder : Option Kernel.Binder) :
    Applies P H "mm0:free-image-formal"
      [encodeBinderResult binder, encodeContext target, encodeExpressions arguments, natural position]
      (encodeSortResult (formalImage target arguments position binder)) := by
  cases binder with
  | none => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | some binder =>
      cases binder with
      | regular => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
      | bound expected =>
          refine free_equation (equation := A[2])
            (environment := [("sort", natural expected), ("target", encodeContext target),
              ("arguments", encodeExpressions arguments), ("position", natural position)])
            (by decide) (by rfl) (by rfl) ?_
          refine Evaluates.call (by simp [Special])
            (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
            (image_argument_computes target expected arguments[position]?)
          exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (argument_lookup arguments position)

theorem bound_image_computes (target formal : Context) (arguments : List Preterm) (position : Nat) :
    Applies P H "mm0:free-image" [encodeContext target, encodeContext formal, encodeExpressions arguments, natural position]
      (encodeSortResult (boundImage? target formal arguments position)) := by
  rw [boundImage_form]
  refine free_equation (equation := A[0])
    (environment := [("target", encodeContext target), ("formal", encodeContext formal),
      ("arguments", encodeExpressions arguments), ("position", natural position)]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (image_formal_computes target arguments position formal[position]?)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (typing_reused _ (by decide) _ _ (context_lookup_computes formal position))

private theorem images_start (target formal : Context) (arguments : List Preterm) (positions : List Nat) (result : Term)
    (next : Applies P H "mm0:free-images-view"
      [listView (positions.map natural), encodeContext target, encodeContext formal, encodeExpressions arguments] result) :
    Applies P H "mm0:free-images" [encodeContext target, encodeContext formal, encodeExpressions arguments, encodeNaturals positions]
      result := by
  refine free_equation (equation := A[13])
    (environment := [("target", encodeContext target), ("formal", encodeContext formal),
      ("arguments", encodeExpressions arguments), ("positions", encodeNaturals positions)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem images_tail (image : Nat) (images : Option (List Nat)) :
    Applies P H "mm0:free-images-tail" [natural image, ComputationalSupport.encodeResult images]
      (ComputationalSupport.encodeResult (images.map (image :: ·))) := by
  cases images with
  | none => exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
  | some images =>
      refine free_equation (equation := A[19])
        (environment := [("image", natural image), ("images", encodeNaturals images)])
        (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (.constructor (by rfl) (by rfl))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (.primitive (by rfl) (computationalHost_list_cons _ _))

private theorem images_next (target formal : Context) (arguments : List Preterm) (positions : List Nat)
    (image : Nat) (images : Option (List Nat))
    (tail : Applies P H "mm0:free-images" [encodeContext target, encodeContext formal,
      encodeExpressions arguments, encodeNaturals positions] (ComputationalSupport.encodeResult images)) :
    Applies P H "mm0:free-images-first" [encodeSortResult (some image), encodeContext target,
      encodeContext formal, encodeExpressions arguments, encodeNaturals positions]
      (ComputationalSupport.encodeResult (images.map (image :: ·))) := by
  refine free_equation (equation := A[17])
    (environment := [("image", natural image), ("target", encodeContext target), ("formal", encodeContext formal),
      ("arguments", encodeExpressions arguments), ("positions", encodeNaturals positions)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) (images_tail image images)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) tail

private theorem images_cons (target formal : Context) (arguments : List Preterm) (position : Nat)
    (positions : List Nat) (result : Term)
    (next : Applies P H "mm0:free-images-first"
      [encodeSortResult (boundImage? target formal arguments position), encodeContext target,
        encodeContext formal, encodeExpressions arguments, encodeNaturals positions] result) :
    Applies P H "mm0:free-images-view"
      [listView ((position :: positions).map natural), encodeContext target, encodeContext formal, encodeExpressions arguments]
      result := by
  refine free_equation (equation := A[15])
    (environment := [("position", natural position), ("positions", encodeNaturals positions),
      ("target", encodeContext target), ("formal", encodeContext formal), ("arguments", encodeExpressions arguments)])
    (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
    (bound_image_computes target formal arguments position)

theorem images_computes (target formal : Context) (arguments : List Preterm) (positions : List Nat) :
    Applies P H "mm0:free-images" [encodeContext target, encodeContext formal, encodeExpressions arguments, encodeNaturals positions]
      (ComputationalSupport.encodeResult (images? target formal arguments positions)) := by
  induction positions with
  | nil => exact images_start target formal arguments [] _ ⟨3, by rw [free_apply _ (by decide)]; rfl⟩
  | cons position positions ih =>
      apply images_start
      apply images_cons
      cases known : boundImage? target formal arguments position with
      | none =>
          simp only [images?, known, encodeSortResult, ComputationalSupport.encodeResult]
          exact ⟨1, by rw [free_apply _ (by decide)]; rfl⟩
      | some image =>
          cases tail : images? target formal arguments positions <;>
            simpa [images?, known, tail] using images_next target formal arguments positions image _ ih

theorem images_result_exact (target formal : Context) (arguments : List Preterm) (positions : List Nat) (result : Term) :
    Applies P H "mm0:free-images" [encodeContext target, encodeContext formal, encodeExpressions arguments, encodeNaturals positions]
      result ↔ result = ComputationalSupport.encodeResult (images? target formal arguments positions) := by
  constructor
  · exact fun run => run.deterministic (images_computes target formal arguments positions)
  · rintro rfl; exact images_computes target formal arguments positions

theorem images_accepts_iff (target formal : Context) (arguments : List Preterm) (positions : List Nat) (result : Finset Nat) :
    (∃ images, Applies P H "mm0:free-images"
      [encodeContext target, encodeContext formal, encodeExpressions arguments, encodeNaturals positions]
      (ComputationalSupport.encodeResult (some images)) ∧ images.toFinset = result) ↔
      FreeVariables.Images target formal arguments positions.toFinset result := by
  constructor
  · rintro ⟨images, run, rfl⟩
    exact images_sound (ComputationalSupport.encodeResult_injective ((images_result_exact _ _ _ _ _).mp run)).symm
  · intro known
    obtain ⟨images, computed, same⟩ := images_complete known
    exact ⟨images, by simpa only [computed] using images_computes target formal arguments positions, same⟩

end Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables
