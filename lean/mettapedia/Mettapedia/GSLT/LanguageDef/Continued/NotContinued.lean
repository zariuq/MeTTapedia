import Mettapedia.GSLT.LanguageDef.Continued.CutShape
import Mettapedia.GSLT.LanguageDef.Continued.Presentation
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.DeepContact
import Mettapedia.Languages.Calculator.Cut
import Mettapedia.Languages.InteractionCategory.Interaction

/-!
# Obstructions to cuts and restrictive continuation plans

Two shapes of selected rule have different consequences.

* The contractum is headed by the constructor of the first operand: every
  cut names that operand as an introduction, and the legacy hereditary
  non-principal plan cannot cover it. Successor arithmetic and visible
  composition have this shape. This does not rule out finite continuation
  decoration whose independent closure contains the rebuilt constructor.
* An operand is a constructor application none of whose arguments is a
  schema variable: no cut exists, because a continuation is a schema
  variable.  The contact rule that unwraps the body of its output prefix has
  this shape.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.Languages.Calculator

/-- A contractum headed by its program introduction has no legacy
non-principal retyping plan. This is a closure obstruction, not a global
failure of continuation decoration. -/
theorem isEmpty_retypingPlan_of_contractum_headed_by_program {theory : IGSLT}
    {contact introduction : String} {programArguments contractumArguments : List Pattern}
    {environment : Pattern}
    (left : theory.presentation.interactionRewrite.1.left =
      .apply contact [.apply introduction programArguments, environment])
    (right : theory.presentation.interactionRewrite.1.right =
      .apply introduction contractumArguments)
    (programPlain : containsContactShape (.apply introduction programArguments) = false)
    (environmentPlain : containsContactShape environment = false)
    (cut : InteractionCutPresentation theory) :
    IsEmpty (ContinuationRetypingPlan cut) := by
  constructor
  intro retyping
  obtain ⟨program, -⟩ :=
    cut.operands_of_binary_left left programPlain environmentPlain
  obtain ⟨programLabel, -⟩ := cut.program.of_apply program
  exact (retyping.contractum_head_ne_introductions right).1 programLabel

/-- **An operand with no schema variable among its arguments admits no cut.** -/
theorem isEmpty_cut_of_opaque_environment {theory : IGSLT}
    {contact introduction : String} {program : Pattern} {arguments : List Pattern}
    (left : theory.presentation.interactionRewrite.1.left =
      .apply contact [program, .apply introduction arguments])
    (programPlain : containsContactShape program = false)
    (environmentPlain : containsContactShape (.apply introduction arguments) = false)
    (applications : ∀ argument ∈ arguments, ∃ label inner, argument = .apply label inner) :
    IsEmpty (InteractionCutPresentation theory) := by
  constructor
  intro cut
  obtain ⟨-, environment⟩ := cut.operands_of_binary_left left programPlain environmentPlain
  obtain ⟨-, selected⟩ := cut.environment.of_apply environment
  obtain ⟨label, inner, shape⟩ := applications _ (List.mem_of_getElem? selected)
  exact cut.environment.continuationPattern_ne_apply label inner shape

/-- The successor rule has no legacy non-principal retyping plan at any cut. -/
theorem successor_legacyRetyping_isEmpty
    (cut : InteractionCutPresentation calculatorRewritingIGSLT) :
    IsEmpty (ContinuationRetypingPlan cut) :=
  isEmpty_retypingPlan_of_contractum_headed_by_program
    (contact := "Add") (introduction := "Succ") (programArguments := [.fvar "m"])
    (contractumArguments := [.apply "Add" [.fvar "m", .fvar "n"]])
    (environment := .fvar "n") rfl rfl (by decide) (by decide) cut

/-- Visible composition has no legacy non-principal retyping plan at any cut. -/
theorem visibleComposition_legacyRetyping_isEmpty
    (cut : InteractionCutPresentation
      (Mettapedia.Languages.InteractionCategory.theory .visible)) :
    IsEmpty (ContinuationRetypingPlan cut) :=
  isEmpty_retypingPlan_of_contractum_headed_by_program
    (contact := "Comp") (introduction := "Act")
    (programArguments := [.fvar "a", .fvar "b", .fvar "p"])
    (contractumArguments := [.fvar "a", .fvar "c", .apply "Comp" [.fvar "p", .fvar "q"]])
    (environment := .apply "Act" [.fvar "b", .fvar "c", .fvar "q"]) rfl rfl
    (by decide) (by decide) cut

/-- The unwrapping contact theory has no interaction cut. -/
theorem deep_no_cut : IsEmpty (InteractionCutPresentation deep) :=
  isEmpty_cut_of_opaque_environment (contact := "Join") (introduction := "Out")
    (program := input (.fvar "x")) (arguments := [wrap (.fvar "y")]) rfl
    (by decide) (by decide)
    (by
      intro argument membership
      obtain rfl := List.mem_singleton.mp membership
      exact ⟨"Wrap", [.fvar "y"], rfl⟩)

/-- So it is not continued. -/
theorem deep_not_continued : ¬ IsContinued deep := by
  rintro ⟨continued⟩
  exact deep_no_cut.false continued.cut

end Mettapedia.GSLT.LanguageDef
