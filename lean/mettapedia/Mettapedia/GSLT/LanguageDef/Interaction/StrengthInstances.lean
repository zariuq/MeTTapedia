import Mettapedia.GSLT.LanguageDef.Interaction.Strength
import Mettapedia.GSLT.LanguageDef.Interaction.BaseInteractions
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactMorphisms
import Mettapedia.Languages.ProcessCalculi.CCS.Interaction
import Mettapedia.Languages.ProcessCalculi.Ambient.Interaction
import Mettapedia.Languages.InteractionCategory.Interaction
import Mettapedia.Languages.TuringMachine.NotInteractive

/-!
# Where the instances stand on the three strengths

* Rho, the lambda calculus, CCS and composition in an interaction category
  have the third strength literally: every rule's left side is a cut.
* Mobile ambients have the first strength and not the second for the family
  of the contact: leaving an ambient is a base rule headed by the boundary.
  They have the third strength only up to the equations, where the unit of
  parallel composition makes it hold of every sorted term.
* The contact theory with one more base rule, a constant that becomes
  another, has the first strength and not the second.
* A Turing machine has the second strength for the family consisting of
  `Run`, and is not interactive: a family of the theory's choosing does not
  supply a same-sort contact.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.LambdaInstance
open Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
open Mettapedia.GSLT.LanguageDef.WellSorted
open EquationSemantics

/-! ## The third strength, literally -/

/-- Every rule of rho has a cut on the left: communication, and reduction of
one component of a composition. -/
theorem rho_everyRuleIsCut : rhoInteractivePresentation.EveryRuleIsCut := by
  intro rewrite membership
  have listed : rewrite ∈ [rhoCommRewrite, rhoParCongRewrite] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩

/-- The lambda calculus has one rule, and its left side is an application. -/
theorem lambda_everyRuleIsCut : lambdaInteractivePresentation.EveryRuleIsCut := by
  intro rewrite membership
  obtain rfl := List.mem_singleton.mp membership
  exact ⟨rfl, rfl⟩

/-- CCS has one rule, and its left side is a parallel composition. -/
theorem ccs_everyRuleIsCut :
    Mettapedia.Languages.ProcessCalculi.CCS.ccsInteractivePresentation.EveryRuleIsCut := by
  intro rewrite membership
  obtain rfl := List.mem_singleton.mp membership
  exact ⟨rfl, by decide⟩

/-- Composition in an interaction category has one rule, and its left side is
a composition. -/
theorem interactionCategory_everyRuleIsCut
    (reading : Mettapedia.Languages.InteractionCategory.Reading) :
    (Mettapedia.Languages.InteractionCategory.presentation reading).EveryRuleIsCut := by
  intro rewrite membership
  obtain rfl := List.mem_singleton.mp membership
  exact ⟨rfl, rfl⟩

/-! ## Mobile ambients: the first strength only -/

section Ambients

open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile

/-- Leaving an ambient is a base rule headed by the boundary, not by parallel
composition. -/
theorem ambient_not_baseRewritesHeaded :
    ¬ BaseRewritesHeadedBy ambientCalc [ambientPresentation.contactHead] :=
  ambientPresentation.not_baseRewritesHeadedBy_of_other_head (rewrite := outRule)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    (isBaseRewrite_of_premises_eq_nil rfl) (head := .constructor "AAmb") rfl (by decide)

/-- Its base rules are headed by parallel composition or by the boundary. -/
theorem ambient_baseRewritesHeaded_family :
    BaseRewritesHeadedBy ambientCalc [.collection .hashBag, .constructor "AAmb"] := by
  intro rewrite membership base
  have listed : rewrite ∈ [openRule, inRule, outRule, parCongRule, ambCongRule] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.Mem.head _, rfl⟩
  · exact ⟨_, List.Mem.head _, rfl⟩
  · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl⟩
  · exact ⟨_, List.Mem.head _, rfl⟩
  · exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl⟩

/-- Not every rule's left side is literally a cut. -/
theorem ambient_not_everyRuleIsCut : ¬ ambientPresentation.EveryRuleIsCut :=
  ambientPresentation.not_everyRuleIsCut_of_rule (rewrite := outRule)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    (by rintro ⟨representation, -⟩; cases representation)

/-- Parallel composition declares the flattening algebra with unit. -/
theorem ambient_algebraRule :
    AlgebraRule ambientCalc ambientPresentation.contactConstructor.1 .hashBag
      { flatten := true, unit := some "AZero" } where
  authored := ambientPresentation.contactConstructor.2
  declared := rfl
  selfSorted := ⟨"ps", rfl⟩
  unitAuthored := by
    intro unit declared
    obtain rfl : "AZero" = unit := Option.some.inj declared
    exact ⟨terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩

/-- A typing of the schema variables of the two boundary-headed rules: the
continuation and the reducing content are processes, every other variable a
name. -/
def boundaryRuleContext : FreeTypeContext := fun name =>
  if name = "p" ∨ name = "S" then some TypeExpr.proc else some TypeExpr.name

/-- An ambient of a name and a process is a process. -/
theorem amb_hasSort {name content : Pattern}
    (nameTyped : HasType ambientCalc boundaryRuleContext [] name TypeExpr.name)
    (contentTyped : HasType ambientCalc boundaryRuleContext [] content TypeExpr.proc) :
    HasSort ambientCalc boundaryRuleContext [] (amb name content) "Proc" :=
  HasType.constructor (rule := terms[5]) (List.getElem_mem (by decide))
    (by rintro ⟨parameterName, collectionType, elementType, shape⟩; cases shape)
    (.cons trivial rfl nameTyped (.cons trivial rfl contentTyped .nil))

/-- A parallel composition of processes is a process, whatever its rest. -/
theorem par_hasSort {components : List Pattern} {rest : Option String}
    (componentsTyped :
      ElementsHaveType ambientCalc boundaryRuleContext [] components TypeExpr.proc) :
    HasSort ambientCalc boundaryRuleContext [] (par components rest) "Proc" :=
  HasType.collectionConstructor (rule := terms[1]) (parameterName := "ps")
    (List.getElem_mem (by decide)) rfl componentsTyped

/-- The left side of the rule for leaving an ambient is a process. -/
theorem outRule_left_sorted :
    HasSort ambientCalc boundaryRuleContext [] outRule.left "Proc" := by
  apply amb_hasSort (HasType.fvar rfl)
  apply par_hasSort
  refine .cons ?_ (.nil _ _)
  apply amb_hasSort (HasType.fvar rfl)
  apply par_hasSort
  refine .cons ?_ (.nil _ _)
  exact HasType.constructor (rule := terms[3]) (List.getElem_mem (by decide))
    (by rintro ⟨parameterName, collectionType, elementType, shape⟩; cases shape)
    (.cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil))

/-- The left side of the contextual rule for ambients is a process. -/
theorem ambCongRule_left_sorted :
    HasSort ambientCalc boundaryRuleContext [] ambCongRule.left "Proc" :=
  amb_hasSort (HasType.fvar rfl) (HasType.fvar rfl)

/-- **Up to the equations every ambient rule is a cut**, the two headed by
the boundary included: each is equal to the composition of itself with the
unit. -/
theorem ambient_everyRuleIsCutUpToEquations :
    ambientPresentation.EveryRuleIsCutUpToEquations base := by
  intro rewrite membership
  have listed : rewrite ∈ [openRule, inRule, outRule, parCongRule, ambCongRule] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Relation.EqvGen.refl _, rfl, by decide⟩
  · exact ⟨_, Relation.EqvGen.refl _, rfl, by decide⟩
  · exact ⟨_, equationEquiv_cut_with_unit ambient_algebraRule rfl rfl outRule_left_sorted,
      rfl, by decide⟩
  · exact ⟨_, Relation.EqvGen.refl _, rfl, by decide⟩
  · exact ⟨_, equationEquiv_cut_with_unit ambient_algebraRule rfl rfl ambCongRule_left_sorted,
      rfl, by decide⟩

end Ambients

/-! ## The first strength without the second -/

section Fire

open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact

/-- The contact theory with the extra rule `B ⟶ A` has a base rule headed by
a constant. -/
theorem fire_not_baseRewritesHeaded :
    ¬ BaseRewritesHeadedBy contactWithFire [firePresentation.contactHead] :=
  firePresentation.not_baseRewritesHeadedBy_of_other_head (rewrite := fireRule)
    (List.Mem.tail _ (List.Mem.head _)) (isBaseRewrite_of_premises_eq_nil rfl)
    (head := .constructor "B") rfl (by decide)

/-- It is interactive all the same. -/
theorem fire_baseInteraction : firePresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

end Fire

/-! ## The second strength without the first -/

section Machines

open Mettapedia.Languages.TuringMachine

/-- Every rule of a Turing machine is a base rule headed by `Run`: the
machine has the second strength for the family consisting of `Run`. -/
theorem turingMachine_baseRewritesHeaded (machine : Machine) :
    BaseRewritesHeadedBy (turingMachine machine) [.constructor "Run"] := by
  intro rewrite membership _
  obtain ⟨control, tape, left⟩ := rewrites_headed_by_run machine rewrite membership
  exact ⟨_, List.Mem.head _, by rw [left]; rfl⟩

/-- **A family of the theory's choosing is not a contact.**  The machine has
the second strength and admits no interactive presentation. -/
theorem turingMachine_second_without_first (machine : Machine) :
    BaseRewritesHeadedBy (turingMachine machine) [.constructor "Run"] ∧
      ¬ AdmitsInteractivePresentation (turingMachine machine) :=
  ⟨turingMachine_baseRewritesHeaded machine, turingMachine_not_interactive machine⟩

end Machines

end Mettapedia.GSLT.LanguageDef
