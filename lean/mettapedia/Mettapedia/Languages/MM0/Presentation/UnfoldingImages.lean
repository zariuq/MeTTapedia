import Mettapedia.Languages.MM0.Presentation.UnfoldingProgram

/-! # Definition parameters and fresh images feed the authored substitution -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => unfoldingProgram
local notation "H" => computationalHost

private theorem images_start (images : List Nat) (result : Term)
    (next : Applies P H "mm0:variable-images-view" [listView (images.map natural)] result) :
    Applies P H "mm0:variable-images" [encodeNaturals images] result := by
  refine Applies.equation (equation := P[138])
    (environment := [("images", encodeNaturals images)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem images_cons (first : Nat) (rest : List Nat)
    (child : Applies P H "mm0:variable-images" [encodeNaturals rest]
      (encodeExpressions (rest.map Preterm.var))) :
    Applies P H "mm0:variable-images-view" [listView ((first :: rest).map natural)]
      (encodeExpressions ((first :: rest).map Preterm.var)) := by
  refine Applies.equation (equation := P[140])
    (environment := [("first", natural first), ("rest", encodeNaturals rest)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil))
    (.primitive (by rfl) (computationalHost_list_cons (encode (.var first)) _))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.constructor (by rfl) (by rfl))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) child

theorem variable_images_computes (images : List Nat) :
    Applies P H "mm0:variable-images" [encodeNaturals images]
      (encodeExpressions (images.map Preterm.var)) := by
  induction images with
  | nil => exact images_start [] _ ⟨1, rfl⟩
  | cons first rest ih => exact images_start (first :: rest) _ (images_cons first rest ih)

theorem variable_images_result_exact (images : List Nat) (result : Term) :
    Applies P H "mm0:variable-images" [encodeNaturals images] result ↔
      result = encodeExpressions (images.map Preterm.var) := by
  constructor
  · exact fun run => run.deterministic (variable_images_computes images)
  · rintro rfl; exact variable_images_computes images

theorem admitted_body_computes (arguments : List Preterm) (images : List Nat) (body : Preterm) :
    Applies P H "mm0:unfold-dummies"
      [.sym "True", encodeExpressions arguments, encodeNaturals images, encode body]
      (encodeResult (body.substitute (Substitution.ofList (Definition.substitutionValues arguments images)))) := by
  refine Applies.equation (equation := P[149])
    (environment := [("arguments", encodeExpressions arguments), ("images", encodeNaturals images),
      ("expression", encode body)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (instantiation_reused "mm0:subst" (by decide) _ _
      (ComputationalInstantiation.substitution_reused body (Definition.substitutionValues arguments images)))
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil)
    (instantiation_reused "mm0:substitution-values" (by decide) _ _
      (ComputationalInstantiation.values_computes (Definition.substitutionValues arguments images)))
  have appended := fresh_reused "nik:list-append" (by decide) _ _
    (ComputationalFreshDummies.append_reused (arguments.map encode) ((images.map Preterm.var).map encode))
  simp only [← List.map_append] at appended
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) appended
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (variable_images_computes images)

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions
