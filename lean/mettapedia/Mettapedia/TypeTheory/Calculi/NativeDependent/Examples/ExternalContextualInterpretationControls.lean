import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualMorphism
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalModelControls

/-!
# Generated classes through an actual dependent-model morphism

The source has variable-domain function and pair contexts. Its generated
branch class maps to the independently supplied section in a function-indexed
finite family. A substitution exchanges two distinct assumptions and maps to
the actual model exchange. Both computations use the quotient CwF morphism,
with complete annotation and certificate data retained.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.InterpretationControls

open _root_.CategoryTheory
open Interpretation
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations

noncomputable def qualified : QualifiedModel Controls.signature ModelControls.familyModel where
  data := ModelControls.model
  realization := ModelControls.realization
  products_substitution := Families.products_substitution
  products_beta := PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts
  products_eta := ModelControls.products_eta

def branchContext : Contextual.Context Controls.signature :=
  ⟨2, Controls.componentContext 0 .nil,
    derivationContextFormation Controls.branchHeader⟩

def branchType : TypeOver branchContext :=
  ⟨Controls.signature.termResult .fullBranch, ⟨Controls.branchResultFormed⟩⟩

def branchTerm : Term branchContext branchType :=
  ⟨Controls.fullBranch 0, ⟨Controls.fullBranchTyped Controls.emptyContext⟩⟩

def branchClass : QuotientCwf.Tm ((quotientProjection Controls.signature).obj branchContext)
    (QType.mk branchType) := ⟨QTerm.mk branchTerm, rfl⟩

theorem branch_context_readout :
    contextValue qualified branchContext = ModelControls.declarations.componentContext :=
  (Classical.choice branchContext.formed.judgment).contextValue_unique qualified.data qualified.realization
    qualified.products_substitution qualified.products_beta qualified.products_eta _
      ModelControls.declarations.component_header_read

theorem supplied_section_heq {S : Symbols} {D : Signature S}
    {C : CwfWithTerminal} (model : QualifiedModel D C)
    {context : Contextual.Context D} {type : TypeOver context} (term : Term context type)
    (native : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C context.arity)
    (contexts : contextValue model context = native)
    (A : C.toCwf.Ty native.1) (supplied : C.toCwf.Tm native.1 A)
    (read : model.data.evaluateTerm native term.code = some ⟨A, supplied⟩) :
    HEq (rawTerm model term) supplied := by
  cases contexts
  exact (Sigma.mk.inj (Option.some.inj ((term_readout model term).symm.trans read))).2

theorem branch_section_readout : HEq (rawTerm qualified branchTerm) ModelControls.declarations.branch :=
  supplied_section_heq qualified branchTerm _ branch_context_readout _ _ ModelControls.declarations.branch_read

theorem mapped_branch_class : HEq (termValue qualified branchClass) ModelControls.declarations.branch :=
  (termValue_retains_section qualified branchClass).trans branch_section_readout

theorem shared_morphism_retains_branch :
    HEq (((familyMorphism qualified).mapTerm (ULift.up branchClass)).down)
      ModelControls.declarations.branch := mapped_branch_class

abbrev assumptionContext : Contextual.Context Controls.signature :=
  ⟨2, Controls.duplicateContext, derivationContextFormation Controls.duplicateContextFormed⟩

theorem assumption_lookup (position : Fin 2) :
    Controls.duplicateContext.lookup position = Controls.scalar 2 := by
  cases position using Fin.cases with
  | zero => exact Controls.scalar_rename Fin.succ
  | succ prior =>
      have unique : prior = 0 := Subsingleton.elim _ _
      cases unique
      change ((Controls.scalar 0).rename Fin.succ).rename Fin.succ = Controls.scalar 2
      rw [Controls.scalar_rename, Controls.scalar_rename]

def exchange : assumptionContext ⟶ assumptionContext where
  substitution := ModelControls.exchangeRaw
  admitted := componentsSubstitution assumptionContext.formed assumptionContext.formed
    ModelControls.exchangeRaw
    (by
      intro position
      rw [assumption_lookup, Controls.scalar_substitute]
      fin_cases position
      · exact ⟨Controls.duplicateOlder⟩
      · exact ⟨Controls.duplicateNewest⟩)

theorem assumption_context_readout :
    contextValue qualified assumptionContext = ModelControls.booleanContext :=
  (Classical.choice assumptionContext.formed.judgment).contextValue_unique qualified.data qualified.realization
    qualified.products_substitution qualified.products_beta qualified.products_eta _ ModelControls.duplicate_context_read

theorem supplied_arrow_heq {S : Symbols} {D : Signature S}
    {C : CwfWithTerminal} (model : QualifiedModel D C)
    {source target : Contextual.Context D} (morphism : source ⟶ target)
    (nativeSource : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C source.arity)
    (nativeTarget : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C target.arity)
    (sourceContexts : contextValue model source = nativeSource)
    (targetContexts : contextValue model target = nativeTarget)
    (arrow : C.toCwf.Sub nativeSource.1 nativeTarget.1)
    (read : model.data.evaluateSubstitution nativeSource nativeTarget morphism.substitution = some arrow) :
    HEq (rawArrow model morphism) arrow := by
  cases sourceContexts
  cases targetContexts
  exact heq_of_eq (Option.some.inj ((arrow_readout model morphism).symm.trans read))

theorem mapped_exchange_readout : HEq (rawArrow qualified exchange) ModelControls.exchange :=
  supplied_arrow_heq qualified exchange _ _ assumption_context_readout assumption_context_readout _
    ModelControls.exchange_evaluated

theorem mapped_identity_readout :
    HEq (rawArrow qualified (𝟙 assumptionContext)) (fun point : ModelControls.booleanContext.1 => point) :=
  supplied_arrow_heq qualified (𝟙 assumptionContext) _ _ assumption_context_readout assumption_context_readout _
    (qualified.data.evaluateSubstitution_identity ModelControls.booleanContext)

theorem mapped_exchange_is_nonidentity :
    rawArrow qualified exchange ≠ rawArrow qualified (𝟙 assumptionContext) := by
  intro same
  have native := mapped_exchange_readout.symm.trans ((heq_of_eq same).trans mapped_identity_readout)
  have values := congrFun (eq_of_heq native) (⟨⟨PUnit.unit, false⟩, true⟩ : ModelControls.booleanContext.1)
  have newest := congrArg (fun point => point.2) values
  exact Bool.false_ne_true newest

theorem quotient_exchange_is_nonidentity :
    (quotientProjection Controls.signature).map exchange ≠
      (quotientProjection Controls.signature).map (𝟙 assumptionContext) := by
  intro same
  exact mapped_exchange_is_nonidentity (congrArg (quotientFunctor qualified).map same)

def newestType : TypeOver assumptionContext :=
  ⟨Controls.scalar 2, ⟨Controls.scalarFormed Controls.duplicateContextFormed⟩⟩

def suppliedNewest : Term assumptionContext newestType := ⟨.var 0, ⟨Controls.duplicateNewest⟩⟩
def suppliedOlder : Term assumptionContext newestType := ⟨.var 1, ⟨Controls.duplicateOlder⟩⟩

theorem mapped_newest_readout :
    HEq (rawTerm qualified suppliedNewest) (fun point : ModelControls.booleanContext.1 => point.2) :=
  supplied_section_heq qualified suppliedNewest _ assumption_context_readout (fun _ => Bool) _ rfl

theorem mapped_older_readout :
    HEq (rawTerm qualified suppliedOlder) (fun point : ModelControls.booleanContext.1 => point.1.2) :=
  supplied_section_heq qualified suppliedOlder _ assumption_context_readout (fun _ => Bool) _ rfl

theorem duplicate_assumptions_remain_distinct :
    QTerm.mk suppliedNewest ≠ QTerm.mk suppliedOlder := by
  intro same
  have values := congrArg (totalValue qualified) same
  have sections := (Sigma.mk.inj values).2
  have native := mapped_newest_readout.symm.trans (sections.trans mapped_older_readout)
  have atPoint := congrFun (eq_of_heq native) (⟨⟨PUnit.unit, false⟩, true⟩ : ModelControls.booleanContext.1)
  exact (by decide : true ≠ false) atPoint

theorem substitution_retains_supplied_assumption :
    HEq (rawTerm qualified (suppliedNewest.reindex exchange))
      (ModelControls.familyModel.toCwf.tmSub (rawTerm qualified suppliedNewest) (rawArrow qualified exchange)) := by
  have read := rawTotal_reindex qualified (⟨newestType, suppliedNewest⟩ : TotalTerm assumptionContext) exchange
  exact (Sigma.mk.inj read).2

theorem dependent_motive_uses_both_inputs :
    Fintype.card (ModelControls.declarations.fibre ⟨PUnit.unit, ModelControls.falseFunction⟩) = 1 ∧
      Fintype.card (ModelControls.declarations.fibre ⟨PUnit.unit, ModelControls.trueFunction⟩) = 2 ∧
      Fintype.card (ModelControls.declarations.motive ⟨PUnit.unit, ⟨ModelControls.trueFunction, ⟨0, by decide⟩⟩⟩) = 2 ∧
      Fintype.card (ModelControls.declarations.motive ⟨PUnit.unit, ⟨ModelControls.trueFunction, ⟨1, by decide⟩⟩⟩) = 3 :=
  ⟨ModelControls.function_changes_domain.1, ModelControls.function_changes_domain.2,
    ModelControls.full_pair_motive_changes_type.1, ModelControls.full_pair_motive_changes_type.2⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.InterpretationControls
