import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialSections
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualObservedGraphControls

/-!
# Varying observed values in actual material dependent sums and products

The authored task/cycle/terminal execution supplies the actual term
readings. Its domain grows at every stage; its dependent result fibres
vary with the argument index and grow without bound along later stages.
Complete sections define functions on every future argument, while
material matching forgets distinctions that remain observable to native
receipt consumers. A result-sensitive section exhibits the precise
compatibility obstruction to extensional application.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialObservedControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts
open PowerClassPresheafDescent.Controls ConstructiveObservedMaterialControls

def parameters : Stagesᵒᵖ ⥤ Type := ContextualWitnessCover.terminal

def domainNative : parameters.Elements ⥤ Type := restrict (CategoryOfElements.π parameters) raw

def domainReading : NaturalHom (total domainNative) (ContextualGraphDiagrams.values Stagesᵒᵖ) where
  app point receipt := ContextualObservedGraphControls.modelReadout.app point receipt.2
  naturality arrival receipt := ContextualObservedGraphControls.modelReadout.naturality arrival receipt.2

def domainFamily : Family parameters := ⟨domainNative, domainReading⟩

def bodyNative : (total domainNative).Elements ⥤ Type where
  obj point := {result : raw.obj point.1 // result.1.val ≤ point.2.2.1.val + stageIndex point.1 / 2}
  map {first second} step := TypeCat.ofHom fun result =>
    ⟨raw.map step.1 result.val, by
      have indexes := congrArg (fun receipt : (total domainNative).obj second.1 => receipt.2.1.val) step.2
      change first.2.2.1.val = second.2.2.1.val at indexes
      change result.val.1.val ≤ second.2.2.1.val + stageIndex second.1 / 2
      have old := result.property
      have order := growthLe step.1
      omega⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro result
    exact Subtype.ext (raw.map_id_apply point.1 result.val)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro result
    exact Subtype.ext (raw.map_comp_apply earlier.1 later.1 result.val)

def bodyReading : NaturalHom (total bodyNative) (ContextualGraphDiagrams.values Stagesᵒᵖ) where
  app point receipt := ContextualObservedGraphControls.modelReadout.app point receipt.2.val
  naturality arrival receipt := ContextualObservedGraphControls.modelReadout.naturality arrival receipt.2.val

def bodyFamily : Family (total domainFamily.native) := ⟨bodyNative, bodyReading⟩

def parameter (stage : Nat) : parameters.Elements := ⟨world stage, PUnit.unit⟩

def parameterStep {first second : Nat} (order : first ≤ second) : parameter first ⟶ parameter second :=
  CategoryOfElements.homMk _ _ ((homOfLE order).op.op) rfl

theorem domain_grows (stage : Nat) :
    ¬ ∃ previous : domainFamily.native.obj (parameter stage),
      domainFamily.native.map (parameterStep (Nat.le_succ stage)) previous =
        stageValue (stage+1) (stage+1) (by omega) false := by
  rintro ⟨previous, same⟩
  have indexes := congrArg (fun value : raw.obj (world (stage+1)) => value.1.val) same
  have bound := previous.1.isLt
  change previous.1.val = stage+1 at indexes
  change previous.1.val < stage+1 at bound
  omega

def bodyParameter (stage : Nat) : (total domainFamily.native).Elements :=
  ⟨world stage, ⟨PUnit.unit, stageValue stage 0 (by omega) false⟩⟩

def bodyParameterStep {first second : Nat} (order : first ≤ second) : bodyParameter first ⟶ bodyParameter second :=
  CategoryOfElements.homMk _ _ ((homOfLE order).op.op)
    (congrArg (Sigma.mk PUnit.unit) (Prod.ext (Fin.ext rfl) rfl))

def newBody (level : Nat) : bodyFamily.native.obj (bodyParameter (2*(level+1))) :=
  ⟨stageValue (2*(level+1)) (level+1) (by omega) false, by
    change level+1 ≤ 0+2*(level+1)/2
    omega⟩

theorem body_fibres_grow (level : Nat) :
    ¬ ∃ previous : bodyFamily.native.obj (bodyParameter (2*level)),
      bodyFamily.native.map (bodyParameterStep (show 2*level ≤ 2*(level+1) by omega)) previous = newBody level := by
  rintro ⟨previous, same⟩
  have indexes := congrArg (fun value : bodyFamily.native.obj (bodyParameter (2*(level+1))) => value.val.1.val) same
  have bounded := previous.property
  change previous.val.1.val ≤ 0+2*level/2 at bounded
  change previous.val.1.val = level+1 at indexes
  omega

def dependent_result : bodyFamily.native.obj
    ⟨world 2, ⟨PUnit.unit, stageValue 2 1 (by omega) false⟩⟩ :=
  ⟨stageValue 2 2 (by omega) false, by decide⟩

theorem dependent_fibre_distinguished :
    ¬ ∃ result : bodyFamily.native.obj (bodyParameter 2), result.val.1.val = 2 := by
  rintro ⟨result, index⟩
  have bounded := result.property
  change result.val.1.val ≤ 0+2/2 at bounded
  omega

def identityBody : bodyFamily.native.sections :=
  ⟨fun point => ⟨point.2.2, Nat.le_add_right _ _⟩, by
    intro first second step
    apply Subtype.ext
    exact eq_of_heq (Sigma.mk.inj_iff.mp step.2).2⟩

def identityFunction : (nativeProduct domainFamily bodyFamily).sections :=
  ContextualGraphFamilyProducts.nativeLambda domainFamily.native bodyFamily.native identityBody

theorem identity_evaluation (point : parameters.Elements) (argument : domainFamily.native.obj point) :
    evaluated domainFamily bodyFamily point (identityFunction.val point) argument =
      ⟨argument, Nat.le_add_right _ _⟩ := by
  have same := ContextualGraphMaterialSections.native_application_value domainFamily bodyFamily identityFunction point argument
  have original := (ContextualGraphFamilyProducts.nativeLambda domainFamily.native bodyFamily.native).symm_apply_apply identityBody
  exact same.symm.trans (congrArg (fun whole : bodyFamily.native.sections =>
    whole.val ((flatten domainFamily.native).obj ⟨point, argument⟩)) original)

def identityCompatible (point : parameters.Elements) :
    ApplicationCompatible domainFamily bodyFamily point (identityFunction.val point) := by
  intro first second matching
  exact (Equal.ofEq (congrArg (termValue bodyFamily ((flatten domainFamily.native).obj ⟨point, first⟩))
    (identity_evaluation point first))).trans
      (matching.trans (Equal.ofEq (congrArg
        (termValue bodyFamily ((flatten domainFamily.native).obj ⟨point, second⟩))
        (identity_evaluation point second))).symm)

def identityLiteral : (literal (pi domainFamily bodyFamily)).sections :=
  (sectionDecoder (pi domainFamily bodyFamily)).symm identityFunction

def identityPair (stage index : Nat) (bound : index < stage+1) :
    (sigma domainFamily bodyFamily).native.obj (parameter stage) :=
  ⟨stageValue stage index bound false, ⟨stageValue stage index bound false, Nat.le_add_right _ _⟩⟩

def actual_sum_member (stage index : Nat) (bound : index < stage+1) :
    Member (termValue (sigma domainFamily bodyFamily) (parameter stage) (identityPair stage index bound))
      ((carrier (sigma domainFamily bodyFamily)).app (world stage) PUnit.unit) :=
  ContextualGraphMaterialSections.sumMember domainFamily bodyFamily (parameter stage) (identityPair stage index bound)

def actual_product_application (stage index : Nat) (bound : index < stage+1) :
    Member (ContextualGraphOrderedPairs.orderedPair
      (termValue domainFamily (parameter stage) (stageValue stage index bound false))
      (termValue domainFamily (parameter stage) (stageValue stage index bound false)))
      (productElement domainFamily bodyFamily (parameter stage) (identityFunction.val (parameter stage))) :=
  Member.transportChild (ContextualGraphOrderedPairs.orderedPairCongr (Equal.refl _)
      (Equal.ofEq (congrArg (termValue bodyFamily
        ((flatten domainFamily.native).obj ⟨parameter stage, stageValue stage index bound false⟩))
          (identity_evaluation (parameter stage) (stageValue stage index bound false)))))
    (applicationMember domainFamily bodyFamily (parameter stage) (identityFunction.val (parameter stage))
      (stageValue stage index bound false))

def resultTags : parameters.Elements ⥤ Type where
  obj _ := Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def resultTag : NaturalHom domainFamily.native resultTags where
  app _ result := result.1.val
  naturality _ _ := rfl

theorem result_tag_cannot_descend :
    ¬ ∃ decoded : NaturalHom (observed domainFamily) resultTags,
      (observe domainFamily).comp decoded = resultTag := by
  intro factors
  have compatible := (descends_iff domainFamily resultTag).mp factors
  have impossible := compatible (parameter 3)
    (stageValue 3 2 (by omega) false) (stageValue 3 3 (by omega) false)
    ⟨ContextualObservedGraphControls.terminalMatching _ _ (by decide) (by decide)⟩
  exact (by decide : ¬ (2 : Nat) = 3) impossible

def terminal_sum_matching :
    Equal (termValue (sigma domainFamily bodyFamily) (parameter 3) (identityPair 3 2 (by omega)))
      (termValue (sigma domainFamily bodyFamily) (parameter 3) (identityPair 3 3 (by omega))) :=
  ContextualGraphOrderedPairs.orderedPairCongr
    (ContextualObservedGraphControls.terminalMatching _ _ (by decide) (by decide))
    (ContextualObservedGraphControls.terminalMatching _ _ (by decide) (by decide))

theorem terminal_sum_receipts_distinct :
    ContextualGraphFamilyBodies.encode (sigma domainFamily bodyFamily).native (sigma domainFamily bodyFamily).reading
        (parameter 3) (identityPair 3 2 (by omega)) ≠
      ContextualGraphFamilyBodies.encode (sigma domainFamily bodyFamily).native (sigma domainFamily bodyFamily).reading
        (parameter 3) (identityPair 3 3 (by omega)) := by
  intro same
  have native := congrArg (ContextualGraphFamilyBodies.decode (sigma domainFamily bodyFamily).native
    (sigma domainFamily bodyFamily).reading (parameter 3)) same
  exact (by decide : ¬ (2 : Nat) = 3) (congrArg (fun pair => pair.1.1.val) native)

def sensitiveIndex (index : Nat) : Nat := if index = 2 then 1 else index

theorem sensitiveIndex_le (index : Nat) : sensitiveIndex index ≤ index := by
  unfold sensitiveIndex
  split
  · omega
  · exact Nat.le_refl _

def sensitiveValue (point : Stagesᵒᵖ) (argument : raw.obj point) : raw.obj point :=
  (⟨sensitiveIndex argument.1.val, Nat.lt_of_le_of_lt (sensitiveIndex_le _) argument.1.isLt⟩, argument.2)

theorem sensitive_le (point : Stagesᵒᵖ) (argument : raw.obj point) :
    (sensitiveValue point argument).1.val ≤ argument.1.val := by
  exact sensitiveIndex_le _

def sensitive : NaturalHom raw raw where
  app := sensitiveValue
  naturality _ _ := Prod.ext (Fin.ext rfl) rfl

def sensitiveBody : bodyFamily.native.sections :=
  ⟨fun point => ⟨sensitive.app point.1 point.2.2,
    (sensitive_le point.1 point.2.2).trans (Nat.le_add_right _ _)⟩, by
    intro first second step
    apply Subtype.ext
    exact (sensitive.naturality step.1 first.2.2).trans
      (congrArg (sensitive.app second.1) (eq_of_heq (Sigma.mk.inj_iff.mp step.2).2))⟩

def sensitiveFunction : (nativeProduct domainFamily bodyFamily).sections :=
  ContextualGraphFamilyProducts.nativeLambda domainFamily.native bodyFamily.native sensitiveBody

def cyclicReceipt : Child Stagesᵒᵖ
    (ContextualObservedGraphControls.modelReadout.app (world 3) (stageValue 3 1 (by omega) false)) :=
  ⟨projection.app (world 3) (stageValue 3 1 (by omega) false),
    (ConstructiveObservedMaterialFamilies.source_class_continuation_iff worlds arrows dynamics atoms atomCoding
      (world 3) (stageValue 3 1 (by omega) false) _).mpr
        ⟨stageValue 3 1 (by omega) false, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem cyclic_terminal_distinct :
    ¬ Nonempty (Equal
      (ContextualObservedGraphControls.modelReadout.app (world 3) (stageValue 3 1 (by omega) false))
      (ContextualObservedGraphControls.modelReadout.app (world 3) (stageValue 3 3 (by omega) false))) := by
  rintro ⟨same⟩
  let membership := Member.transportParent same
    (Member.atChild (ContextualObservedGraphControls.modelReadout.app (world 3)
      (stageValue 3 1 (by omega) false)) cyclicReceipt)
  exact ContextualObservedGraphControls.no_terminal_member (𝟙 (world 3))
    (stageValue 3 3 (by omega) false) (by decide) _
      ⟨Member.transportParent (Equal.ofEq (move_identity Stagesᵒᵖ (world 3)
        (ContextualObservedGraphControls.modelReadout.app (world 3)
          (stageValue 3 3 (by omega) false)))).symm membership⟩

theorem sensitive_not_material_compatible :
    ¬ Nonempty (ApplicationCompatible domainFamily bodyFamily (parameter 3)
      (sensitiveFunction.val (parameter 3))) := by
  rintro ⟨compatible⟩
  let first := stageValue 3 2 (by omega) false
  let second := stageValue 3 3 (by omega) false
  have equalArguments := ContextualObservedGraphControls.terminalMatching first second (by decide) (by decide)
  have equalResults := compatible first second equalArguments
  have firstValue := ContextualGraphMaterialSections.native_lambda_evaluation domainFamily bodyFamily
    sensitiveBody (parameter 3) first
  have secondValue := ContextualGraphMaterialSections.native_lambda_evaluation domainFamily bodyFamily
    sensitiveBody (parameter 3) second
  exact cyclic_terminal_distinct ⟨(Equal.ofEq (congrArg
      (termValue bodyFamily ((flatten domainFamily.native).obj ⟨parameter 3, first⟩)) firstValue)).symm.trans
    (equalResults.trans (Equal.ofEq (congrArg
      (termValue bodyFamily ((flatten domainFamily.native).obj ⟨parameter 3, second⟩)) secondValue)))⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialObservedControls
