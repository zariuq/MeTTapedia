import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualSigmaEliminationComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalTypeOperationControls

/-!
# Authored dependent sum-elimination controls

A complete-pair motive applies the declared higher-order family to the first
projection. Elimination retains the supplied second witness and earns its type
conversion. The selected contextual comparison is also exercised on an actual
stored pair variable in a dependent function-family context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.SigmaEliminationControls

open _root_.CategoryTheory Contextual ContextualControls TypeOperationControls
open Contextual.DependentTypes Contextual.QuotientComprehensionSyntax
open Contextual.SigmaEliminationComparison
open Mettapedia.TypeTheory.ContextualSumComprehension

theorem pairBody_code : pairBody.code = .family .indexed (fun _ => .var 0) := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.indexed)
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ prior => exact Fin.elim0 prior

abbrev completeMotive := rawSecondMotive functionDomain pairBody
def completeBranch := (rawSecondSection functionDomain pairBody).reindex (rawPack functionDomain pairBody)
def literalEliminator := rawEliminate functionDomain pairBody completeMotive completeBranch dependentPair

theorem motive_keeps_first_projection : completeMotive.code =
    .family .indexed (fun _ => (rawFirstSection functionDomain pairBody).code) := by
  change (pairBody.code.substitute (rawLift (projectionHom witnessContext (rawSigma functionDomain pairBody))
    functionDomain).substitution).substitute (nativeSection (rawFirstSection functionDomain pairBody)).substitution = _
  rw [pairBody_code, rawLift_substitution, nativeSection_substitution]
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.indexed)
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ prior => exact Fin.elim0 prior

theorem omitted_first_projection_changes_motive : completeMotive.code ≠
    .family .indexed (fun _ => .var (0 : Fin 3)) := by
  rw [motive_keeps_first_projection]
  intro same
  have arguments := eq_of_heq (TypeExpr.family.inj same |>.2)
  have wrong := congrFun arguments 0
  rw [rawFirstSection_code] at wrong
  cases wrong

theorem motive_at_supplied_pair : (completeMotive.reindex (nativeSection dependentPair)).code =
    .family .indexed (fun _ => (Sums.rawFst dependentPair).code) := by
  rw [rawSecondMotive_at]
  change pairBody.code.substitute (nativeSection (Sums.rawFst dependentPair)).substitution = _
  rw [pairBody_code, nativeSection_substitution]
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.indexed)
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ prior => exact Fin.elim0 prior

theorem literal_elimination_retains_supplied_witness : QTerm.mk literalEliminator = QTerm.mk witness :=
  (full_motive_second_readout functionDomain pairBody olderFunction suppliedPairWitness).trans
    (QTerm.mk_cast _ _)

theorem dependent_result_conversion : Holds signature (.typeEq witnessContext.raw
    (completeMotive.reindex (nativeSection dependentPair)).code firstAnnotation.code) :=
  ((QTerm.mk_eq_iff _ _).mp literal_elimination_retains_supplied_witness).1

theorem packing_retains_both_positions :
    (rawPack functionDomain pairBody).substitution 0 =
      .pair (functionDomain.code.rename (Fin.succ ∘ Fin.succ))
        (pairBody.code.rename (liftRenaming (Fin.succ ∘ Fin.succ))) (.var 1) (.var 0) := by
  rw [rawPack_substitution]
  rfl

theorem supplied_pair_substitution_readout :
    ((rawPack functionDomain pairBody).substitution 0).substitute
      (rawComponents olderFunction suppliedPairWitness).substitution = dependentPair.code := by
  rw [rawPack_substitution, rawComponents_substitution]
  exact genericPair_instantiate _ _ _ _

theorem omitted_second_coordinate_is_wrong :
    (.var (1 : Fin 4) : TermExpr symbols 4).substitute
      (rawComponents olderFunction suppliedPairWitness).substitution ≠ witness.code := by
  rw [rawComponents_substitution]
  change (.var (1 : Fin 2) : TermExpr symbols 2) ≠ .var 0
  intro wrong
  exact (by decide : (1 : Fin 2) ≠ 0) (TermExpr.var.inj wrong)

def actualFunctionDomain : TypeOver functionContext := ⟨functionType 1, function_formed functionContext.formed⟩
def nativeFunctionType : QuotientCwf.Ty qFunctionContext := QType.mk actualFunctionDomain
noncomputable abbrev nativeDomainContext := QuotientCwf.ext qFunctionContext nativeFunctionType

noncomputable def nativeNewestFunction :
    Term nativeDomainContext.as
      (actualFunctionDomain.reindex (projectionHom functionContext (QuotientCwf.typeRepresentative nativeFunctionType))) :=
  (newest functionContext (QuotientCwf.typeRepresentative nativeFunctionType)).convertType _
    (reindex_typeEquality
      ((QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class nativeFunctionType))
      (projectionHom functionContext (QuotientCwf.typeRepresentative nativeFunctionType)))

set_option backward.isDefEq.respectTransparency false in
noncomputable def nativeFunctionArguments : nativeDomainContext.as ⟶ functionContext :=
  ⟨extendSubstitution Fin.elim0 nativeNewestFunction.code, by
    have typed := nativeNewestFunction.typed
    change Holds signature (.term nativeDomainContext.as.raw nativeNewestFunction.code
      ((functionType 1).substitute (fun index => .var index.succ))) at typed
    erw [functionType_substitute] at typed
    have atHeader : Holds signature (.term nativeDomainContext.as.raw nativeNewestFunction.code
      ((functionType 0).substitute (Fin.elim0 : Substitution symbols 0 2))) := by
      rw [functionType_substitute]
      exact typed
    exact conclude (.substitutionExtend nativeDomainContext.as.raw .nil (functionType 0) Fin.elim0 nativeNewestFunction.code)
      ⟨conclude (.substitutionNil nativeDomainContext.as.raw) ⟨nativeDomainContext.as.formed.judgment, trivial⟩,
        function_formed .nil, atHeader, trivial⟩⟩

noncomputable def nativeBodyRaw : TypeOver nativeDomainContext.as := firstFamily.reindex nativeFunctionArguments
noncomputable def nativeCodomain : QuotientCwf.Ty nativeDomainContext := QType.mk nativeBodyRaw

theorem native_codomain_has_bound_parameter : nativeBodyRaw.code =
    .family .indexed (fun _ => .var (0 : Fin 2)) := by
  apply congrArg (TypeExpr.family (S := symbols) TypeSymbol.indexed)
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ prior => exact Fin.elim0 prior

noncomputable abbrev storedPairContext := QuotientCwf.ext qFunctionContext (Sums.sigma nativeFunctionType nativeCodomain)
noncomputable abbrev storedProjection := QuotientCwf.wk (Sums.sigma nativeFunctionType nativeCodomain)
noncomputable def storedDomain := QuotientCwf.tySub nativeFunctionType storedProjection
noncomputable def storedCodomain := QuotientCwf.tySub nativeCodomain
  (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
    (C := QuotientCwf.cwf signature) storedProjection nativeFunctionType)
noncomputable def storedPair : QuotientCwf.Tm storedPairContext (Sums.sigma storedDomain storedCodomain) :=
  normalize (SumElimination.stable signature) storedProjection
    (QuotientCwf.vz (Sums.sigma nativeFunctionType nativeCodomain))
noncomputable def actualStoredPair := Sums.pairRepresentative storedPair
noncomputable def storedMotive := rawSecondMotive
  (QuotientCwf.typeRepresentative storedDomain) (QuotientCwf.typeRepresentative storedCodomain)
noncomputable def storedBranch := (rawSecondSection
  (QuotientCwf.typeRepresentative storedDomain) (QuotientCwf.typeRepresentative storedCodomain)).reindex
  (rawPack (QuotientCwf.typeRepresentative storedDomain) (QuotientCwf.typeRepresentative storedCodomain))
noncomputable def storedLiteralEliminator := rawEliminate
  (QuotientCwf.typeRepresentative storedDomain) (QuotientCwf.typeRepresentative storedCodomain)
  storedMotive storedBranch actualStoredPair

theorem stored_pair_variable_retained : storedPair.val =
    (QuotientCwf.vz (Sums.sigma nativeFunctionType nativeCodomain)).val :=
  heq_value (Sums.formation_substitution storedProjection nativeFunctionType nativeCodomain).symm
    (normalize_heq (SumElimination.stable signature) storedProjection
      (QuotientCwf.vz (Sums.sigma nativeFunctionType nativeCodomain)))

theorem actual_stored_pair_class : QTerm.mk actualStoredPair =
    (QuotientCwf.vz (Sums.sigma nativeFunctionType nativeCodomain)).val :=
  (Sums.pairRepresentative_class storedPair).trans stored_pair_variable_retained

theorem stored_pair_elimination_contract : QTerm.mk storedLiteralEliminator =
    QuotientCwf.totalSub
      (eliminate (SumElimination.stable signature) storedDomain storedCodomain
        (nativeMotive storedDomain storedCodomain storedMotive)
        (nativeBranch storedDomain storedCodomain storedMotive storedBranch)).val
      (QuotientCwf.project (nativeSection actualStoredPair) ≫ (sumPresentation storedDomain storedCodomain).inv) :=
  authored_elimination_is_contextual storedDomain storedCodomain storedMotive storedBranch actualStoredPair

theorem stored_pair_retains_second_section : QTerm.mk storedLiteralEliminator = (Sums.snd storedPair).val :=
  (rawEliminate_section_eta _ _ storedMotive (rawSecondSection _ _) actualStoredPair).trans
    (rawSecondSection_at _ _ actualStoredPair)

theorem contextual_eliminator_recovers_stored_second :
    QuotientCwf.totalSub
      (eliminate (SumElimination.stable signature) storedDomain storedCodomain
        (nativeMotive storedDomain storedCodomain storedMotive)
        (nativeBranch storedDomain storedCodomain storedMotive storedBranch)).val
      (QuotientCwf.project (nativeSection actualStoredPair) ≫ (sumPresentation storedDomain storedCodomain).inv) =
        (Sums.snd storedPair).val :=
  stored_pair_elimination_contract.symm.trans stored_pair_retains_second_section

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.SigmaEliminationControls
