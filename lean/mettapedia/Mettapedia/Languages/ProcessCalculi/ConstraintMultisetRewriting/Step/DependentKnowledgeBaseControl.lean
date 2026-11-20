import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeConsistency
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# A source-parameter swap invalidated by new knowledge

With two unused type parameters and constant row labels, swapping the
parameters is an isomorphism of the old state. After learning that the newer
parameter is Ground, that same swap does not preserve the knowledge models.
This separates arbitrary state isomorphisms from comparisons over the common
source frame. The latter is a uniform sufficient condition; a particular
added store may also be compatible with a nontrivial source automorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeBaseControl

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull.Controls ContextualDependentParameterExchange
open KnowledgeChange

abbrev domain := context (smallUniverse (empty Tower.rules)) (smallUniverse (empty Tower.rules))

def groundRow : TotalTerm domain := ⟨smallUniverse domain, ⟨ground, ground_typed _⟩⟩
def variableRow : TotalTerm domain := ⟨smallUniverse domain, ⟨.var 0, Derivable.var 0⟩⟩
def added : EquationStore (TotalTerm domain) := [(variableRow, groundRow)]

def state : State Tower.rules Nat := ⟨domain, [], ∅, fun _ => groundRow⟩

def exchange : domain ≅ domain := swapIso (smallUniverse (empty Tower.rules)) (smallUniverse (empty Tower.rules))

def stateIso : PlainIso setting.levels state state where
  frame := exchange
  knowledge := fun _ _ => Iff.rfl
  present := rfl
  label _ := totalTerm_ext (TypeOver.ext rfl rfl) rfl

def assignment : point ⟶ domain :=
  pair (pair (toEmpty point) ⟨arrow, arrow_typed _⟩) ⟨ground, ground_typed _⟩

theorem solves_original : (frames setting.levels).Models assignment added := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change (frames setting.levels).E (variableRow.reindex assignment) (groundRow.reindex assignment)
  have same : variableRow.reindex assignment = groundRow.reindex assignment :=
    totalTerm_ext (TypeOver.ext rfl rfl) rfl
  rw [same]
  exact ((frames setting.levels).equivalence _).refl _

theorem does_not_solve_exchanged :
    ¬ (frames setting.levels).Models assignment ((frames setting.levels).applyStore exchange.hom added) := by
  intro models
  have same := models _ (List.mem_singleton_self _)
  have equality := same.2
  change Equal Tower.rules point.raw arrow ground (.head (.sort Tower.zero)) at equality
  have types : TypeEq Tower.rules point.raw arrow ground := ⟨_, .sort _, equality⟩
  exact ground_arrow_clash point.formed types.symm

theorem added_not_compatible :
    ¬ (frames setting.levels).Equivalent ((frames setting.levels).applyStore exchange.hom added) added :=
  fun same => does_not_solve_exchanged ((same point assignment).mpr solves_original)

def emptyRun : (helperStep setting.levels Nat).toStep.Run state := .nil state

theorem does_not_fix_source : ¬ OverStart (first := emptyRun) (second := emptyRun) stateIso := by
  intro fixed
  change exchange.hom ≫ (𝟙 domain) = 𝟙 domain at fixed
  rw [Category.comp_id] at fixed
  have values := congrArg (fun map : domain ⟶ domain => map.substitution 0) fixed
  rw [show exchange.hom.substitution 0 = .var ⟨1, by decide⟩ from
    swap_zero (smallUniverse (empty Tower.rules)) (smallUniverse (empty Tower.rules))] at values
  have indices := congrArg Fin.val (Tm.var.inj values)
  cases indices

theorem old_comparison_does_not_extend :
    ¬ ∃ comparison : PlainIso setting.levels (strengthen state added) (strengthen state added),
      comparison.frame = exchange := by
  rintro ⟨comparison, same⟩
  have knowledge := comparison.knowledge
  rw [same] at knowledge
  change (frames setting.levels).Equivalent
    ((frames setting.levels).applyStore exchange.hom added) added at knowledge
  exact added_not_compatible knowledge

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeBaseControl

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeBaseControl.old_comparison_does_not_extend
