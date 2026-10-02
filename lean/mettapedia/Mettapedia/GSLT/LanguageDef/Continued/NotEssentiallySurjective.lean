import Mettapedia.GSLT.LanguageDef.Continued.CutShape
import Mettapedia.GSLT.LanguageDef.Continued.Forget
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.DeepContact
import Mettapedia.GSLT.LanguageDef.TypingInversion
import Mettapedia.Languages.Calculator.Cut
import Mettapedia.Languages.InteractionCategory.Interaction

/-!
# The forgetful functor from continued theories is not essentially surjective

Two interactive theories are shown to lie outside its essential image, each
for one clause of the definition of a continued theory, and each by a
statement stronger than non-isomorphism.

* **The dynamics do not factor.**  In the contact theory whose rule unwraps
  the body of the output prefix, the selected rule has no interaction-cut
  form.  There is no morphism of iGSLTs from the underlying theory of a
  continued theory into it.
* **The contractum is headed by an introduction.**  The successor law of
  rewriting arithmetic has cut form, and its contractum is headed by the
  program introduction itself; so has composition in an interaction category
  read visibly.  There is no morphism of iGSLTs from either into the
  underlying theory of a continued theory.  The continuation signature of a
  continued theory excludes both introductions, which is more than asking
  the contraction to map wrapped continuations to wrapped continuations.

A static equivalence with no computable section is treated separately: the
definition of a continued theory here does not ask its section to be
computable.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.CIGSLT

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.Languages.Calculator

/-- A renamed pattern that is a schema variable is that schema variable. -/
theorem mapPattern_eq_fvar_iff (symbols : LanguageDefSymbolMap) (pattern : Pattern)
    (name : String) :
    mapPattern symbols pattern = .fvar name ↔ pattern = .fvar name := by
  cases pattern <;> simp [mapPattern]

/-- A morphism of iGSLTs carries the left side of the selected rule to the
left side of the selected rule. -/
theorem IGSLT.Morphism.maps_left {source target : IGSLT} (morphism : source ⟶ target) :
    mapPattern (IGSLT.Morphism.structural morphism).structural.symbols
        source.presentation.interactionRewrite.1.left =
      target.presentation.interactionRewrite.1.left :=
  congrArg (fun rewrite : DeclaredRewrite target.presentation.presentation => rewrite.1.left)
    (IGSLT.Morphism.structural morphism).mapsInteractionRewrite

/-- And the right side to the right side. -/
theorem IGSLT.Morphism.maps_right {source target : IGSLT} (morphism : source ⟶ target) :
    mapPattern (IGSLT.Morphism.structural morphism).structural.symbols
        source.presentation.interactionRewrite.1.right =
      target.presentation.interactionRewrite.1.right :=
  congrArg (fun rewrite : DeclaredRewrite target.presentation.presentation => rewrite.1.right)
    (IGSLT.Morphism.structural morphism).mapsInteractionRewrite

/-! ## Dynamics that do not factor as contact then contraction -/

/-- **No continued theory maps into the unwrapping theory.**  The image of a
cut-form rule under a renaming has cut form; the unwrapping rule has none,
because the argument of its output prefix is not a continuation. -/
theorem deep_not_underlying (theory : CIGSLT) : IsEmpty (forget.obj theory ⟶ deep) := by
  constructor
  intro morphism
  have left := IGSLT.Morphism.maps_left morphism
  change mapPattern _ theory.theory.presentation.interactionRewrite.1.left =
    join (input (.fvar "x")) (output (wrap (.fvar "y"))) at left
  obtain ⟨contact, arguments, shape, -, images⟩ := (mapPattern_eq_apply_iff _ _ _ _).mp left
  obtain ⟨first, second, rfl, firstImage, secondImage⟩ := map_eq_pair images
  obtain ⟨inputLabel, inputArguments, rfl, -, inputImages⟩ :=
    (mapPattern_eq_apply_iff _ _ _ _).mp firstImage
  obtain ⟨inputBody, rfl, inputBodyImage⟩ := map_eq_single inputImages
  obtain rfl := (mapPattern_eq_fvar_iff _ _ _).mp inputBodyImage
  obtain ⟨outputLabel, outputArguments, rfl, -, outputImages⟩ :=
    (mapPattern_eq_apply_iff _ _ _ _).mp secondImage
  obtain ⟨wrapped, rfl, wrappedImage⟩ := map_eq_single outputImages
  obtain ⟨wrapLabel, wrapArguments, rfl, -, wrapImages⟩ :=
    (mapPattern_eq_apply_iff _ _ _ _).mp wrappedImage
  obtain ⟨inner, rfl, innerImage⟩ := map_eq_single wrapImages
  obtain rfl := (mapPattern_eq_fvar_iff _ _ _).mp innerImage
  obtain ⟨-, environment⟩ := theory.cut.operands_of_binary_left shape
    (by simp [containsContactShape, containsContactShapeList])
    (by simp [containsContactShape, containsContactShapeList])
  obtain ⟨-, selected⟩ := theory.cut.environment.of_apply environment
  match index : theory.cut.environment.continuation.index, selected with
  | 0, selected =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      exact theory.cut.environment.continuationPattern_ne_apply _ _ selected.symm
  | _ + 1, selected => simp at selected

/-! ## A contraction that does not preserve wrapping -/

/-- **A contractum headed by its own program introduction.**  A theory whose
selected rule contracts a binary contact `K(S(…), e)` to a term headed by
`S` maps into the underlying theory of no continued theory: the image rule
would have a contractum headed by the program introduction, and the
contractum of a continued theory never is. -/
theorem no_morphism_of_contractum_headed_by_program {source : IGSLT}
    {contact introduction : String} {programArguments contractumArguments : List Pattern}
    {environment : Pattern}
    (left : source.presentation.interactionRewrite.1.left =
      .apply contact [.apply introduction programArguments, environment])
    (right : source.presentation.interactionRewrite.1.right =
      .apply introduction contractumArguments)
    (programPlain : containsContactShape (.apply introduction programArguments) = false)
    (environmentPlain : containsContactShape environment = false)
    (theory : CIGSLT) : IsEmpty (source ⟶ forget.obj theory) := by
  constructor
  intro morphism
  have mappedLeft := IGSLT.Morphism.maps_left morphism
  have mappedRight := IGSLT.Morphism.maps_right morphism
  rw [left] at mappedLeft
  rw [right] at mappedRight
  simp only [mapPattern, mapPatternList] at mappedLeft mappedRight
  obtain ⟨program, -⟩ := theory.cut.operands_of_binary_left mappedLeft.symm
    (by
      have shape := containsContactShape_mapPattern
        (IGSLT.Morphism.structural morphism).structural.symbols
        (.apply introduction programArguments)
      simp only [mapPattern] at shape
      rw [shape]
      exact programPlain)
    (by rw [containsContactShape_mapPattern]; exact environmentPlain)
  obtain ⟨programLabel, -⟩ := theory.cut.program.of_apply program
  exact (theory.contractum_head_ne_introductions mappedRight.symm).1 programLabel

/-- **Successor arithmetic maps into no continued theory.** -/
theorem successor_not_underlying (theory : CIGSLT) :
    IsEmpty (calculatorRewritingIGSLT ⟶ forget.obj theory) :=
  no_morphism_of_contractum_headed_by_program (source := calculatorRewritingIGSLT)
    (contact := "Add") (introduction := "Succ") (programArguments := [.fvar "m"])
    (contractumArguments := [.apply "Add" [.fvar "m", .fvar "n"]])
    (environment := .fvar "n") rfl rfl (by decide) (by decide) theory

/-- **Visible composition in an interaction category maps into no continued
theory**, for the same reason: the composite is headed by the action prefix
that introduces both operands. -/
theorem visibleComposition_not_underlying (theory : CIGSLT) :
    IsEmpty (Mettapedia.Languages.InteractionCategory.theory .visible ⟶ forget.obj theory) :=
  no_morphism_of_contractum_headed_by_program
    (source := Mettapedia.Languages.InteractionCategory.theory .visible)
    (contact := "Comp") (introduction := "Act")
    (programArguments := [.fvar "a", .fvar "b", .fvar "p"])
    (contractumArguments := [.fvar "a", .fvar "c", .apply "Comp" [.fvar "p", .fvar "q"]])
    (environment := .apply "Act" [.fvar "b", .fvar "c", .fvar "q"]) rfl rfl
    (by decide) (by decide) theory

/-- The successor law does have interaction-cut form: what fails is the
wrapping, not the factoring. -/
theorem successor_has_cut : Nonempty (InteractionCutPresentation calculatorRewritingIGSLT) :=
  ⟨successorCut⟩

/-! ## The essential image -/

/-- **Not essentially surjective.** -/
theorem forget_not_essSurj : ¬ forget.EssSurj := by
  intro surjective
  obtain ⟨theory, ⟨isomorphism⟩⟩ := surjective.mem_essImage deep
  exact (deep_not_underlying theory).false isomorphism.hom

/-- Nor when morphisms are taken up to their underlying theory map. -/
theorem forgetUpToTheoryMap_not_essSurj : ¬ forgetUpToTheoryMap.EssSurj := by
  intro surjective
  obtain ⟨theory, ⟨isomorphism⟩⟩ := surjective.mem_essImage deep
  exact (deep_not_underlying theory.as).false isomorphism.hom

/-- None of the three witnesses is isomorphic to the underlying theory of a
continued theory. -/
theorem witnesses_outside_essImage :
    ¬ forget.essImage deep ∧ ¬ forget.essImage calculatorRewritingIGSLT ∧
      ¬ forget.essImage (Mettapedia.Languages.InteractionCategory.theory .visible) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨theory, ⟨isomorphism⟩⟩
    exact (deep_not_underlying theory).false isomorphism.hom
  · rintro ⟨theory, ⟨isomorphism⟩⟩
    exact (successor_not_underlying theory).false isomorphism.inv
  · rintro ⟨theory, ⟨isomorphism⟩⟩
    exact (visibleComposition_not_underlying theory).false isomorphism.inv

end Mettapedia.GSLT.LanguageDef.CIGSLT
