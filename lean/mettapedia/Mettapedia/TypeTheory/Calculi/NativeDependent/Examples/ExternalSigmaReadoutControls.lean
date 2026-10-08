import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticSigmaReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalSigmaEliminationControls

/-!
# Mixed packing and complete sum-elimination controls

Generated-equal higher-order annotations give different raw generic pairs.
Their actual packing maps agree after typed comparison. A stored dependent
pair supplies the complete eliminator readout and retains its second witness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.SigmaReadoutControls

open _root_.CategoryTheory Contextual ContextualControls TypeOperationControls SigmaEliminationControls
open Contextual.DependentTypes Contextual.QuotientComprehensionSyntax
open Contextual.SigmaEliminationComparison Contextual.SigmaAnnotationComparison
open Contextual.SyntacticReification
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

theorem mixed_packing_preserves_both_components :
    QuotientCwf.project (rawPack firstFamily firstAnnotation) ≫ QuotientCwf.project
      (extensionComparison (rawSigma firstFamily firstAnnotation) (rawSigma secondFamily rightAnnotation)
        (rawSigma_typeEquality _ _ annotations_equal _ _ body_annotations_equal)).hom =
      QuotientCwf.project
        (tupleComparison firstFamily secondFamily annotations_equal firstAnnotation rightAnnotation body_annotations_equal).hom ≫
      QuotientCwf.project (rawPack secondFamily rightAnnotation) :=
  packing_square _ _ annotations_equal _ _ body_annotations_equal

theorem generic_pair_annotations_really_change :
    (rawGenericPair firstFamily firstAnnotation).code ≠ (rawGenericPair secondFamily rightAnnotation).code := by
  rw [rawGenericPair_code, rawGenericPair_code]
  intro same
  have domains := TermExpr.pair.inj same |>.1
  change TypeExpr.family TypeSymbol.indexed (fun index => (firstArguments index).rename (Fin.succ ∘ Fin.succ)) =
    TypeExpr.family TypeSymbol.indexed (fun index => (secondArguments index).rename (Fin.succ ∘ Fin.succ)) at domains
  have arguments := eq_of_heq (TypeExpr.family.inj domains).2
  have bad := congrFun arguments 0
  cases bad

theorem admitted_pair_equation_does_not_erase_annotations :
    Holds signature (.termEq (rawTuple firstFamily firstAnnotation).raw
      (genericPair firstFamily.code firstAnnotation.code) (genericPair secondFamily.code rightAnnotation.code)
      ((rawSigma firstFamily firstAnnotation).reindex (rawTupleBase firstFamily firstAnnotation)).code) ∧
      (rawGenericPair firstFamily firstAnnotation).code ≠ (rawGenericPair secondFamily rightAnnotation).code :=
  ⟨genericPair_equality _ _ annotations_equal _ _ body_annotations_equal, generic_pair_annotations_really_change⟩

noncomputable def chosenStoredMotive := storedMotive.reindex (rawSumPresentation storedDomain storedCodomain).hom
noncomputable def nativeStoredMotive := nativeMotive storedDomain storedCodomain storedMotive
noncomputable def nativeStoredBranch := nativeBranch storedDomain storedCodomain storedMotive storedBranch
noncomputable def nativeStoredOutput := QuotientCwf.tmSub
  (eliminate (SumElimination.stable signature) storedDomain storedCodomain nativeStoredMotive nativeStoredBranch)
  (selfExtend (QuotientCwf.cwf signature) storedPair)

set_option backward.isDefEq.respectTransparency false in
theorem chosen_stored_motive_class : QType.mk chosenStoredMotive = nativeStoredMotive := rfl

set_option backward.isDefEq.respectTransparency false in
theorem stored_pair_complete_authored_readout :
    TermReadout storedPairContext
      (.sigmaElim (QuotientCwf.typeRepresentative storedDomain).code
        (QuotientCwf.typeRepresentative storedCodomain).code chosenStoredMotive.code
        storedBranch.code actualStoredPair.code)
      ⟨QuotientCwf.tySub nativeStoredMotive (selfExtend (QuotientCwf.cwf signature) storedPair), nativeStoredOutput⟩ := by
  apply sigma_elimination_readout
    ⟨QuotientCwf.typeRepresentative storedDomain, rfl, QuotientCwf.typeRepresentative_class storedDomain⟩
    ⟨QuotientCwf.typeRepresentative storedCodomain, rfl, QuotientCwf.typeRepresentative_class storedCodomain⟩
    ⟨chosenStoredMotive, rfl, chosen_stored_motive_class⟩ nativeStoredBranch storedPair
  · exact ⟨storedMotive.reindex (rawPack _ _), storedBranch, rfl, rfl⟩
  · exact ⟨_, actualStoredPair, rfl, Sums.pairRepresentative_class storedPair⟩

set_option backward.isDefEq.respectTransparency false in
theorem complete_native_readout_keeps_second_witness : nativeStoredOutput.val = (Sums.snd storedPair).val := by
  have returned := contextual_eliminator_recovers_stored_second
  rw [section_presentation (rawSigma (QuotientCwf.typeRepresentative storedDomain)
    (QuotientCwf.typeRepresentative storedCodomain)) storedPair actualStoredPair
    (Sums.pairRepresentative_class storedPair)] at returned
  exact returned

abbrev witnessBase := (quotientProjection signature).obj witnessContext
def witnessDomain : QuotientCwf.Ty witnessBase := QType.mk firstAnnotation
noncomputable def witnessCodomain := QuotientCwf.tySub witnessDomain (QuotientCwf.wk witnessDomain)
def nativeFirstWitness : QuotientCwf.Tm witnessBase witnessDomain := ⟨QTerm.mk witness, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem second_witness_type :
    QuotientCwf.tySub witnessCodomain (selfExtend (QuotientCwf.cwf signature) nativeFirstWitness) = witnessDomain := by
  change QuotientCwf.tySub (QuotientCwf.tySub witnessDomain (QuotientCwf.wk witnessDomain))
    (QuotientCwf.pair (𝟙 witnessBase) witnessDomain _) = _
  rw [← QuotientCwf.tySub_comp, QuotientCwf.wk_pair, QuotientCwf.tySub_id]

noncomputable def nativeSecondWitness : QuotientCwf.Tm witnessBase
    (QuotientCwf.tySub witnessCodomain (selfExtend (QuotientCwf.cwf signature) nativeFirstWitness)) :=
  ⟨QTerm.mk witness, second_witness_type.symm⟩
noncomputable def witnessPair := Sums.pair nativeFirstWitness nativeSecondWitness
noncomputable def witnessMotive := rawSecondMotive
  (QuotientCwf.typeRepresentative witnessDomain) (QuotientCwf.typeRepresentative witnessCodomain)
noncomputable def witnessBranch := (rawSecondSection
  (QuotientCwf.typeRepresentative witnessDomain) (QuotientCwf.typeRepresentative witnessCodomain)).reindex
  (rawPack (QuotientCwf.typeRepresentative witnessDomain) (QuotientCwf.typeRepresentative witnessCodomain))
noncomputable def chosenWitnessMotive := witnessMotive.reindex (rawSumPresentation witnessDomain witnessCodomain).hom
noncomputable def nativeWitnessMotive := nativeMotive witnessDomain witnessCodomain witnessMotive
noncomputable def nativeWitnessBranch := nativeBranch witnessDomain witnessCodomain witnessMotive witnessBranch
noncomputable def actualWitnessPair := Sums.pairRepresentative witnessPair
noncomputable def witnessOutput := QuotientCwf.tmSub
  (eliminate (SumElimination.stable signature) witnessDomain witnessCodomain nativeWitnessMotive nativeWitnessBranch)
  (selfExtend (QuotientCwf.cwf signature) witnessPair)

set_option backward.isDefEq.respectTransparency false in
theorem changed_annotation_complete_readout :
    TermReadout witnessBase
      (.sigmaElim secondAnnotation.code (QuotientCwf.typeRepresentative witnessCodomain).code
        chosenWitnessMotive.code witnessBranch.code actualWitnessPair.code)
      ⟨QuotientCwf.tySub nativeWitnessMotive (selfExtend (QuotientCwf.cwf signature) witnessPair), witnessOutput⟩ := by
  apply sigma_elimination_readout
    ⟨secondAnnotation, rfl, dependent_annotation_retained.symm⟩
    ⟨QuotientCwf.typeRepresentative witnessCodomain, rfl, QuotientCwf.typeRepresentative_class witnessCodomain⟩
    ⟨chosenWitnessMotive, rfl, rfl⟩ nativeWitnessBranch witnessPair
  · exact ⟨witnessMotive.reindex (rawPack _ _), witnessBranch, rfl, rfl⟩
  · exact ⟨_, actualWitnessPair, rfl, Sums.pairRepresentative_class witnessPair⟩

set_option backward.isDefEq.respectTransparency false in
theorem changed_annotation_returns_exact_supplied_witness : witnessOutput.val = QTerm.mk witness := by
  have interpreted := authored_elimination_is_contextual witnessDomain witnessCodomain witnessMotive
    witnessBranch actualWitnessPair
  have literal := (rawEliminate_section_eta _ _ witnessMotive (rawSecondSection _ _) actualWitnessPair).trans
    (rawSecondSection_at _ _ actualWitnessPair)
  rw [section_presentation (rawSigma (QuotientCwf.typeRepresentative witnessDomain)
    (QuotientCwf.typeRepresentative witnessCodomain)) witnessPair actualWitnessPair
    (Sums.pairRepresentative_class witnessPair)] at interpreted
  have secondRead := heq_value
    (congrArg (fun value => QuotientCwf.tySub witnessCodomain (selfExtend (QuotientCwf.cwf signature) value))
      (Sums.fst_pair nativeFirstWitness nativeSecondWitness))
    (Sums.snd_pair nativeFirstWitness nativeSecondWitness)
  exact interpreted.symm.trans (literal.trans secondRead)

theorem changed_domain_annotation_is_visible_in_authored_code :
    (.sigmaElim secondAnnotation.code (QuotientCwf.typeRepresentative witnessCodomain).code
      chosenWitnessMotive.code witnessBranch.code actualWitnessPair.code) ≠
    (TermExpr.sigmaElim firstAnnotation.code (QuotientCwf.typeRepresentative witnessCodomain).code
      chosenWitnessMotive.code witnessBranch.code actualWitnessPair.code) := by
  intro same
  have domains := TermExpr.sigmaElim.inj same |>.1
  change TypeExpr.family TypeSymbol.indexed (fun index => (secondArguments index).substitute olderProjection.substitution) =
    TypeExpr.family TypeSymbol.indexed (fun index => (firstArguments index).substitute olderProjection.substitution) at domains
  have arguments := eq_of_heq (TypeExpr.family.inj domains).2
  have bad := congrFun arguments 0
  cases bad

theorem omitting_motive_dependency_changes_code : completeMotive.code ≠
    .family .indexed (fun _ => .var (0 : Fin 3)) := omitted_first_projection_changes_motive

theorem omitting_the_second_position_loses_the_witness :
    (.var (1 : Fin 4) : TermExpr symbols 4).substitute
      (rawComponents olderFunction suppliedPairWitness).substitution ≠ witness.code :=
  omitted_second_coordinate_is_wrong

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.SigmaReadoutControls
