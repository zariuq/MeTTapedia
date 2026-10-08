import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualLogicalMorphism
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualSumElimination
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalContextualInterpretationControls

/-!
# Complete logical sections under the canonical contextual interpreter

The interpreted identity function retains every supplied input. Its Boolean
instance is nonconstant. A function-indexed pair retains its finite second
witness, and its component family changes with the supplied function.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.LogicalMorphismControls

open _root_.CategoryTheory
open Interpretation
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open QuotientComprehensionSyntax DependentTypes

universe u c s t m
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}

noncomputable def identityClass {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) := Products.lam (QuotientCwf.vz domain)

set_option backward.isDefEq.respectTransparency false in
theorem identity_value (model : QualifiedModel D C)
    {context : QuotientCwf.QContext D} (domain : QuotientCwf.Ty context) :
    HEq (termValue model (identityClass domain))
      (model.data.products.lam (C.toCwf.vz (typeValue model domain))) := by
  have endpoint := congrArg Sigma.fst (represented_extension model domain)
  have representative := congrArg (typeValue model) (QuotientCwf.typeRepresentative_class domain)
  have weakening := (raw_projection_heq model context.as (QuotientCwf.typeRepresentative domain)).trans
    (wk_type_heq representative)
  have bodyRead := (heq_of_eq (type_substitution model domain (QuotientCwf.wk domain))).trans
    (tySub_heq endpoint rfl HEq.rfl weakening)
  have variableRead := (termValue_retains_section model (QuotientCwf.vz domain)).trans
    ((raw_variable_heq model context.as (QuotientCwf.typeRepresentative domain)).trans
      (vz_type_heq representative))
  exact product_abstraction_value model (QuotientCwf.vz domain) _ bodyRead _ variableRead

noncomputable abbrev qualified := InterpretationControls.qualified
abbrev scalarContext := (quotientProjection Controls.signature).obj (empty Controls.signature)

def scalarType : TypeOver (empty Controls.signature) :=
  ⟨Controls.scalar 0, ⟨Controls.scalarFormed Controls.emptyContext⟩⟩

def scalarClass : QuotientCwf.Ty scalarContext := QType.mk scalarType

theorem scalar_value : HEq (typeValue qualified scalarClass) ModelControls.scalar := by
  have readouts {n : Nat}
      {first second : Mettapedia.TypeTheory.ContextualModelTelescopes.Context ModelControls.familyModel n}
      (contexts : first = second) (code : TypeExpr Controls.symbols n)
      {A : ModelControls.familyModel.toCwf.Ty first.1}
      {B : ModelControls.familyModel.toCwf.Ty second.1}
      (firstRead : qualified.data.evaluateType first code = some A)
      (secondRead : qualified.data.evaluateType second code = some B) : HEq A B := by
    cases contexts
    exact heq_of_eq (Option.some.inj (firstRead.symm.trans secondRead))
  exact readouts (context_empty qualified) scalarType.code (type_readout qualified scalarType)
    ModelControls.declarations.scalar_empty_read

theorem native_identity_heq (products : PiOperations C.toCwf)
    {first second : C.toCwf.Ctx} (contexts : first = second)
    {A : C.toCwf.Ty first} {B : C.toCwf.Ty second} (domains : HEq A B) :
    HEq (products.lam (C.toCwf.vz A)) (products.lam (C.toCwf.vz B)) := by
  cases contexts
  cases eq_of_heq domains
  rfl

theorem boolean_identity_value :
    HEq (termValue qualified (identityClass scalarClass))
      (fun _ : PUnit.{1} => fun input : Bool => input) := by
  have contexts := congrArg Sigma.fst (context_empty qualified)
  exact (identity_value qualified scalarClass).trans
    (native_identity_heq ModelControls.products contexts scalar_value)

noncomputable def interpretedIdentity : PUnit.{1} → Bool → Bool :=
  cast (type_eq_of_heq boolean_identity_value) (termValue qualified (identityClass scalarClass))

theorem interpreted_identity_all_inputs : interpretedIdentity = fun _ input => input :=
  eq_of_heq ((cast_heq _ _).trans boolean_identity_value)

theorem identity_has_distinct_answers :
    interpretedIdentity PUnit.unit false = false ∧ interpretedIdentity PUnit.unit true = true := by
  rw [interpreted_identity_all_inputs]
  exact ⟨rfl, rfl⟩

theorem replacing_function_by_one_answer_fails :
    interpretedIdentity ≠ (fun _ _ => false) := by
  intro same
  have values := congrFun (congrFun same PUnit.unit) true
  rw [identity_has_distinct_answers.2] at values
  exact (by decide : true ≠ false) values

def functionType : TypeOver (empty Controls.signature) :=
  ⟨Controls.domain 0, ⟨Controls.domainFormed Controls.emptyContext⟩⟩

def functionClass : QuotientCwf.Ty scalarContext := QType.mk functionType

def fibreType : TypeOver (extend (empty Controls.signature) functionType) :=
  ⟨Controls.body 0, ⟨Controls.bodyFormed Controls.emptyContext⟩⟩

noncomputable def selectedFunctionComparison :=
  extensionComparison (QuotientCwf.typeRepresentative functionClass) functionType
    ((QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class functionClass))

noncomputable def selectedFibre := fibreType.reindex selectedFunctionComparison.hom

noncomputable def fibreClass : QuotientCwf.Ty (QuotientCwf.ext scalarContext functionClass) :=
  QType.mk selectedFibre

theorem supplied_type_readout {n : Nat}
    {first second : Mettapedia.TypeTheory.ContextualModelTelescopes.Context ModelControls.familyModel n}
    (contexts : first = second) (code : TypeExpr Controls.symbols n)
    {A : ModelControls.familyModel.toCwf.Ty first.1}
    {B : ModelControls.familyModel.toCwf.Ty second.1}
    (firstRead : qualified.data.evaluateType first code = some A)
    (secondRead : qualified.data.evaluateType second code = some B) : HEq A B := by
  cases contexts
  exact heq_of_eq (Option.some.inj (firstRead.symm.trans secondRead))

theorem function_value : HEq (typeValue qualified functionClass)
    (DeclaredModel.functionDomain ModelControls.products ModelControls.scalar) :=
  supplied_type_readout (context_empty qualified) functionType.code (type_readout qualified functionType)
    ModelControls.declarations.domain_empty_read

theorem telescope_extension_heq {n : Nat}
    {first second : Mettapedia.TypeTheory.ContextualModelTelescopes.Context ModelControls.familyModel n}
    (contexts : first = second)
    {A : ModelControls.familyModel.toCwf.Ty first.1}
    {B : ModelControls.familyModel.toCwf.Ty second.1} (domains : HEq A B) :
    first.snoc A = second.snoc B := by
  cases contexts
  cases eq_of_heq domains
  rfl

theorem selected_function_context :
    contextValue qualified (QuotientCwf.ext scalarContext functionClass).as =
      ModelControls.declarations.functionContext :=
  (represented_extension qualified functionClass).trans
    (telescope_extension_heq (context_empty qualified) function_value)

theorem selected_fibre_code : selectedFibre.code = Controls.body 0 := by
  exact extensionComparison_type_code _ _ _ fibreType

theorem fibre_value : HEq (typeValue qualified fibreClass) ModelControls.declarations.fibre := by
  apply supplied_type_readout selected_function_context selectedFibre.code
    (type_readout qualified selectedFibre)
  rw [selected_fibre_code]
  exact ModelControls.declarations.fibre_read

noncomputable abbrev sourceModel := SourceModel.{0, 1} Controls.signature
abbrev targetModel := TargetModel.{0, 1, 0, 1, 0} ModelControls.familyModel
noncomputable abbrev sourceStableSums : StableSums sourceModel.toCwf :=
  liftStableSums (SumElimination.stable Controls.signature)
abbrev targetStableSums : StableSums targetModel.toCwf := liftStableSums ModelControls.sums

noncomputable def liftedFunction : sourceModel.toCwf.Ty (ULift.up scalarContext) := ULift.up functionClass
noncomputable def liftedFibre : sourceModel.toCwf.Ty
    (sourceModel.toCwf.ext (ULift.up scalarContext) liftedFunction) := ULift.up fibreClass

noncomputable def sourcePacked := sourceModel.toCwf.tmSub
  (sourceModel.toCwf.vz (sourceStableSums.operations.sigma liftedFunction liftedFibre))
  (pack sourceStableSums liftedFunction liftedFibre)

def targetFunction : targetModel.toCwf.Ty targetModel.empty :=
  ULift.up (DeclaredModel.functionDomain ModelControls.products ModelControls.scalar)

def targetFibre : targetModel.toCwf.Ty (targetModel.toCwf.ext targetModel.empty targetFunction) :=
  ULift.up ModelControls.declarations.fibre

def targetPacked := targetModel.toCwf.tmSub
  (targetModel.toCwf.vz (targetStableSums.operations.sigma targetFunction targetFibre))
  (pack targetStableSums targetFunction targetFibre)

set_option backward.isDefEq.respectTransparency false in
theorem interpreted_packing : HEq ((familyMorphism qualified).mapTerm sourcePacked) targetPacked := by
  exact packed_variable_heq (strictMorphism qualified) sourceStableSums targetStableSums
    (sums_preserved qualified)
    (Γ := ULift.up scalarContext) (Γ' := targetModel.empty)
    (congrArg ULift.up (congrArg Sigma.fst (context_empty qualified)))
    (A := liftedFunction) (A' := targetFunction) (up_heq function_value)
    (B := liftedFibre) (B' := targetFibre) (up_heq fibre_value)

noncomputable def interpretedPair :=
  (cast (type_eq_of_heq interpreted_packing) ((familyMorphism qualified).mapTerm sourcePacked)).down

theorem interpreted_pair_all_inputs : interpretedPair =
    (fun point : ModelControls.declarations.componentContext.1 => ⟨point.1.2, point.2⟩) := by
  have sections := eq_of_heq ((cast_heq (type_eq_of_heq interpreted_packing)
    ((familyMorphism qualified).mapTerm sourcePacked)).trans interpreted_packing)
  have values := congrArg ULift.down sections
  exact values

theorem pairing_retains_distinct_witnesses :
    (interpretedPair ModelControls.trueZero).2.val = 0 ∧
      (interpretedPair ModelControls.trueOne).2.val = 1 := by
  rw [interpreted_pair_all_inputs]
  exact ⟨rfl, rfl⟩

theorem pair_function_changes_witness_type :
    Fintype.card (ModelControls.declarations.fibre
      ⟨PUnit.unit, (interpretedPair ModelControls.falsePoint).1⟩) = 1 ∧
    Fintype.card (ModelControls.declarations.fibre
      ⟨PUnit.unit, (interpretedPair ModelControls.trueZero).1⟩) = 2 := by
  rw [interpreted_pair_all_inputs]
  exact ModelControls.function_changes_domain

theorem omitting_the_second_component_fails :
    (interpretedPair ModelControls.trueZero).2.val ≠
      (interpretedPair ModelControls.trueOne).2.val := by
  rw [pairing_retains_distinct_witnesses.1, pairing_retains_distinct_witnesses.2]
  decide

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.LogicalMorphismControls
