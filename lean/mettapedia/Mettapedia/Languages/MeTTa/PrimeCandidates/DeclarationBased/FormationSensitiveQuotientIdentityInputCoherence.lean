import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityGeometry
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientBasedJRepresentation
import Mettapedia.TypeTheory.ContextualBasedIdentityScope

/-!
# Semantic input coherence and the retained motive-function boundary

The existing native conversion has beta but no function eta equation.
Consequently, an applied motive body and its reflexivity method can forget
information still retained by the submitted motive function in native J.
This file compares those exact observations on independently admitted
inputs in one fixed formed context. It does not add eta, change the
declaration environment, or identify an arbitrary semantic body with a
submitted native function.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientIdentityInputCoherence

open _root_.CategoryTheory FormationSensitive QuotientIdentity QuotientCwf
open NativeIndexedFamilies.Intrinsic

variable {signature : Declaration.Signature Tower.Head}
variable {context : Context (OpaqueRelatorExtension.rules signature)}

private theorem method_at_body (input : Based.Admitted context) :
    Typing (OpaqueRelatorExtension.rules signature) context.raw input.method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub input.left) input.motiveType.code) := by
  change Typing _ _ _ (subst (FormationSensitiveBasedIdentity.reflexivitySub input.left)
    (FormationSensitiveBasedIdentity.motiveBody input.motive))
  rw [FormationSensitiveBasedIdentity.reflexivitySub_motiveBody]
  exact input.nativeMethod.typed

/-- Abstracting the actual body constructs another admitted tuple. It is
not asserted to preserve the submitted motive function or native J. -/
def abstractedInput (input : Based.Admitted context) : Based.Admitted context :=
  Based.ofBody input.type input.left input.element.formed input.leftTerm.typed
    input.motiveType.code input.motiveType.formed input.method (method_at_body input)

theorem abstracted_type (input : Based.Admitted context) :
    QType.mk (abstractedInput input).element = QType.mk input.element := rfl

theorem abstracted_left (input : Based.Admitted context) :
    QTerm.mk (abstractedInput input).leftTerm = QTerm.mk input.leftTerm := rfl

theorem abstracted_body (input : Based.Admitted context) :
    QType.mk (abstractedInput input).motiveType = QType.mk input.motiveType := by
  obtain ⟨actual, code, _, same⟩ := Based.ofBody_covers input.type input.left
    input.element.formed input.leftTerm.typed input.motiveType.code input.motiveType.formed
    input.method (method_at_body input)
  exact same.trans ((QType.mk_eq_iff _ _).mpr (by rw [code]; exact .refl _))

theorem abstracted_chosen_motive (input : Based.Admitted context) :
    tySub (QType.mk (abstractedInput input).motiveType) (abstractedInput input).presentation.hom =
      tySub (QType.mk input.motiveType) input.presentation.hom :=
  congrArg (fun type => tySub type input.presentation.hom) (abstracted_body input)

theorem abstracted_method_type (input : Based.Admitted context) :
    QType.mk (abstractedInput input).methodType = QType.mk input.methodType :=
  (abstractedInput input).motive_reflexivity.symm.trans
    ((congrArg (fun type => tySub type (project input.reflSection)) (abstracted_body input)).trans
      input.motive_reflexivity)

theorem abstracted_base (input : Based.Admitted context) :
    (abstractedInput input).base.val = input.base.val := by
  apply (QTerm.mk_eq_iff _ _).mpr
  exact ⟨(QType.mk_eq_iff _ _).mp (abstracted_method_type input), .refl _⟩

theorem abstracted_base_heq (input : Based.Admitted context) :
    HEq (abstractedInput input).base input.base :=
  QuotientComprehensionSyntax.heq_of_value (abstracted_base input)

/-- The existing semantic based-input interface observes the applied
motive family and its method, not the submitted motive function. -/
noncomputable def semanticInput (input : Based.Admitted context) :
    Mettapedia.TypeTheory.ContextualBasedIdentityScope.Input
      (formation (OpaqueRelatorExtension.rules signature))
      (@QuotientIdentityGeometry.reflSection _ (OpaqueRelatorExtension.rules signature)) where
  context := (quotientProjection _).obj context
  type := QType.mk input.element
  left := TermFibre.mk input.leftTerm
  motive := tySub (QType.mk input.motiveType) input.presentation.hom
  base := TermFibre.compare (QuotientIdentityGeometry.admitted_motive_reflexivity input).symm
    input.base

private theorem input_body_ext {semanticContext : QContext (OpaqueRelatorExtension.rules signature)}
    {type : Ty semanticContext} (left : QuotientCwf.Tm semanticContext type)
    (firstMotive secondMotive : Ty
      (Mettapedia.TypeTheory.ContextualBasedIdentityOperations.basedContext
        (formation (OpaqueRelatorExtension.rules signature)) left))
    (firstBase : QuotientCwf.Tm semanticContext
      (tySub firstMotive (QuotientIdentityGeometry.reflSection left)))
    (secondBase : QuotientCwf.Tm semanticContext
      (tySub secondMotive (QuotientIdentityGeometry.reflSection left)))
    (motives : firstMotive = secondMotive) (bases : HEq firstBase secondBase) :
    (⟨semanticContext, type, left, firstMotive, firstBase⟩ :
      Mettapedia.TypeTheory.ContextualBasedIdentityScope.Input
        (formation (OpaqueRelatorExtension.rules signature))
        (@QuotientIdentityGeometry.reflSection _ (OpaqueRelatorExtension.rules signature))) =
      ⟨semanticContext, type, left, secondMotive, secondBase⟩ := by
  cases motives
  cases eq_of_heq bases
  rfl

theorem abstracted_semantic_input (input : Based.Admitted context) :
    semanticInput (abstractedInput input) = semanticInput input := by
  apply input_body_ext
  · exact abstracted_chosen_motive input
  · apply QuotientComprehensionSyntax.heq_of_value
    exact abstracted_base input

/-! ## Retaining the submitted semantic function -/

private theorem motive_function_formed :
    Typing NativeIndexedFamilies.IntrinsicRelator.rules contextAXPD
      (rename wk (rename wk identityMotiveType)) (sortTm identityMotiveLevel) :=
  FormationSensitiveNativeIdentity.identityMotiveType_hasType.weaken.weaken

/-- The independently formed annotation of the submitted motive function,
as distinct from the applied motive family in `semanticInput`. -/
def motiveFunctionType (input : Based.Admitted context) : TypeOver context where
  code := subst (identitySchemaSubstitution input.type input.left input.motive input.method)
    (rename wk (rename wk identityMotiveType))
  level := .sort identityMotiveLevel
  universeWitness := .sort identityMotiveLevel
  formed := (OpaqueRelatorExtension.relator_typing motive_function_formed).substitute input.typed

def motiveFunction (input : Based.Admitted context) : Term context (motiveFunctionType input) :=
  ⟨input.motive, input.typed (1 : Fin 4)⟩

/-- All four native conversions are recovered from equality of actual
semantic classes. No conversion of a submitted argument is a premise. -/
theorem parameter_conversions (first second : Based.Admitted context)
    (types : QType.mk first.element = QType.mk second.element)
    (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm)
    (motives : QTerm.mk (motiveFunction first) = QTerm.mk (motiveFunction second))
    (methods : first.base.val = second.base.val) :
    Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation ∧
    Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation ∧
    Conv (OpaqueRelatorExtension.rules signature).headEq first.motive second.motive
      (OpaqueRelatorExtension.rules signature).computation ∧
    Conv (OpaqueRelatorExtension.rules signature).headEq first.method second.method
      (OpaqueRelatorExtension.rules signature).computation :=
  ⟨(QType.mk_eq_iff _ _).mp types, ((QTerm.mk_eq_iff _ _).mp lefts).2,
    ((QTerm.mk_eq_iff _ _).mp motives).2, ((QTerm.mk_eq_iff _ _).mp methods).2⟩

theorem parameter_classes (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation)
    (motives : Conv (OpaqueRelatorExtension.rules signature).headEq first.motive second.motive
      (OpaqueRelatorExtension.rules signature).computation)
    (methods : Conv (OpaqueRelatorExtension.rules signature).headEq first.method second.method
      (OpaqueRelatorExtension.rules signature).computation) :
    QType.mk first.element = QType.mk second.element ∧
    QTerm.mk first.leftTerm = QTerm.mk second.leftTerm ∧
    QTerm.mk (motiveFunction first) = QTerm.mk (motiveFunction second) ∧
    first.base.val = second.base.val := by
  refine ⟨(QType.mk_eq_iff _ _).mpr types, (QTerm.mk_eq_iff _ _).mpr ⟨types, lefts⟩,
    (QTerm.mk_eq_iff _ _).mpr ⟨?_, motives⟩, (QTerm.mk_eq_iff _ _).mpr ⟨?_, methods⟩⟩
  · apply Conv.substitutePointwise
    intro index
    fin_cases index
    · exact methods
    · exact motives
    · exact lefts
    · exact types
  · exact Conv.congApp (Conv.congApp motives lefts)
      (Conv.mapCompatible Tm.refl (fun step => .congRefl step) lefts)

/-- The actual typed comparison between the two chosen presentations is
built from the semantic type and left classes via native context transport. -/
noncomputable def chosenInputMap (first second : Based.Admitted context)
    (types : QType.mk first.element = QType.mk second.element)
    (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm) :
    first.chosenContext ⟶ second.chosenContext :=
  first.presentation.hom ≫
    project (QuotientBasedJRepresentation.inputComparison first second
      ((QType.mk_eq_iff _ _).mp types) (((QTerm.mk_eq_iff _ _).mp lefts).2)).hom ≫
    second.presentation.inv

private theorem tySub_transfer
    {first nativeFirst nativeSecond second : QContext (OpaqueRelatorExtension.rules signature)}
    (firstComparison : first ≅ nativeFirst) (secondComparison : second ≅ nativeSecond)
    (arrow : nativeFirst ⟶ nativeSecond) (type : Ty nativeSecond) :
    tySub (tySub type secondComparison.hom)
      (firstComparison.hom ≫ arrow ≫ secondComparison.inv) =
      tySub (tySub type arrow) firstComparison.hom := by
  have cancel : (firstComparison.hom ≫ arrow ≫ secondComparison.inv) ≫ secondComparison.hom =
      firstComparison.hom ≫ arrow := by
    simp only [Category.assoc, secondComparison.inv_hom_id, Category.comp_id]
  exact (tySub_comp _ _ _).symm.trans
    ((congrArg (tySub type) cancel).trans (tySub_comp _ _ _))

private theorem totalSub_transfer
    {first nativeFirst nativeSecond second : QContext (OpaqueRelatorExtension.rules signature)}
    (firstComparison : first ≅ nativeFirst) (secondComparison : second ≅ nativeSecond)
    (arrow : nativeFirst ⟶ nativeSecond) (value : QTerm nativeSecond.as) :
    totalSub (totalSub value secondComparison.hom)
      (firstComparison.hom ≫ arrow ≫ secondComparison.inv) =
      totalSub (totalSub value arrow) firstComparison.hom := by
  have cancel : (firstComparison.hom ≫ arrow ≫ secondComparison.inv) ≫ secondComparison.hom =
      firstComparison.hom ≫ arrow := by
    simp only [Category.assoc, secondComparison.inv_hom_id, Category.comp_id]
  exact (totalSub_comp _ _ _).symm.trans
    ((congrArg (totalSub value) cancel).trans (totalSub_comp _ _ _))

theorem chosen_motive_transport (first second : Based.Admitted context)
    (types : QType.mk first.element = QType.mk second.element)
    (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm)
    (motives : QTerm.mk (motiveFunction first) = QTerm.mk (motiveFunction second)) :
    tySub (tySub (QType.mk second.motiveType) second.presentation.hom)
      (chosenInputMap first second types lefts) =
      tySub (QType.mk first.motiveType) first.presentation.hom :=
  (tySub_transfer first.presentation second.presentation _ _).trans
    (congrArg (fun type => tySub type first.presentation.hom)
      (QuotientBasedJRepresentation.motive_type_transport first second
        ((QType.mk_eq_iff _ _).mp types) (((QTerm.mk_eq_iff _ _).mp lefts).2)
        (((QTerm.mk_eq_iff _ _).mp motives).2)))

/-- Retaining the function class suffices for every independently
admitted native tuple, including changes to all four raw parameters. -/
theorem chosen_j_transport_value (first second : Based.Admitted context)
    (types : QType.mk first.element = QType.mk second.element)
    (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm)
    (motives : QTerm.mk (motiveFunction first) = QTerm.mk (motiveFunction second))
    (methods : first.base.val = second.base.val) :
    (tmSub second.chosenJ (chosenInputMap first second types lefts)).val = first.chosenJ.val := by
  obtain ⟨nativeTypes, nativeLefts, nativeMotives, nativeMethods⟩ :=
    parameter_conversions first second types lefts motives methods
  exact (totalSub_transfer first.presentation second.presentation _ _).trans
    (congrArg (fun value => totalSub value first.presentation.hom)
      (QuotientBasedJRepresentation.j_transport_value first second
        nativeTypes nativeLefts nativeMotives nativeMethods))

theorem chosen_j_transport (first second : Based.Admitted context)
    (types : QType.mk first.element = QType.mk second.element)
    (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm)
    (motives : QTerm.mk (motiveFunction first) = QTerm.mk (motiveFunction second))
    (methods : first.base.val = second.base.val) :
    TermFibre.compare (chosen_motive_transport first second types lefts motives)
      (tmSub second.chosenJ (chosenInputMap first second types lefts)) = first.chosenJ :=
  Subtype.ext (chosen_j_transport_value first second types lefts motives methods)

private theorem totalSub_inverse
    {source target : QContext (OpaqueRelatorExtension.rules signature)}
    (comparison : source ≅ target) (value : QTerm target.as) :
    totalSub (totalSub value comparison.hom) comparison.inv = value :=
  (totalSub_comp value comparison.inv comparison.hom).symm.trans
    ((congrArg (totalSub value) comparison.inv_hom_id).trans (totalSub_id value))

namespace Controls

def parameterContext : Context HOLNativeRelatorCompatibility.rules :=
  ⟨4, contextAXPD,
    (FormationSensitiveBasedIdentity.canonical_parameters HOLNativeRelatorCompatibility.signature).1⟩

def variableInput : Based.Admitted
    (signature := HOLNativeRelatorCompatibility.signature) parameterContext :=
  ⟨.var (3 : Fin 4), .var (2 : Fin 4), .var (1 : Fin 4), .var (0 : Fin 4),
    (FormationSensitiveBasedIdentity.canonical_parameters HOLNativeRelatorCompatibility.signature).2⟩

private theorem parallel_variable {n : Nat} {index : Fin n} {target : Tower.Tm n}
    (step : NativeRelatorConversionParallel.Par (.var index) target) :
    target = .var index := by
  cases step
  rfl

private theorem parallel_variable_body {n : Nat} (function first second : Fin n)
    {target : Tower.Tm n}
    (step : NativeRelatorConversionParallel.Par
      (.app (.app (.var function) (.var first)) (.var second)) target) :
    target = .app (.app (.var function) (.var first)) (.var second) := by
  cases step with
  | app functionStep secondStep =>
      cases functionStep with
      | app functionStep firstStep =>
          cases functionStep
          cases firstStep
          cases secondStep
          rfl

private theorem parallel_abstracted_variable_body {n : Nat} (function first second : Fin (n + 2))
    {target : Tower.Tm n}
    (step : NativeRelatorConversionParallel.Par
      (.lam (.lam (.app (.app (.var function) (.var first)) (.var second)))) target) :
    target = .lam (.lam (.app (.app (.var function) (.var first)) (.var second))) := by
  cases step with
  | lam inner =>
      cases inner with
      | lam inner =>
          exact congrArg (fun body => Tm.lam (.lam body))
            (parallel_variable_body function first second inner)

private theorem parallel_open_j {n : Nat} (type left method right path : Fin n)
    (motive : Tower.Tm n)
    (motiveFixed : ∀ target, NativeRelatorConversionParallel.Par motive target → target = motive)
    {target : Tower.Tm n}
    (step : NativeRelatorConversionParallel.Par
      (identityEliminateApp (.var type) (.var left) motive (.var method) (.var right) (.var path))
      target) :
    target = identityEliminateApp (.var type) (.var left) motive
      (.var method) (.var right) (.var path) := by
  cases step with
  | app functionStep pathStep =>
      obtain ⟨_, _, _, _, _, shape, typeStep, leftStep, motiveStep, methodStep, rightStep⟩ :=
        NativeRelatorConversionParallel.identityPrefix_inversion functionStep
      rw [shape, parallel_variable typeStep, parallel_variable leftStep,
        motiveFixed _ motiveStep, parallel_variable methodStep, parallel_variable rightStep,
        parallel_variable pathStep]
      rfl

private theorem finite_parallel_fixed {n : Nat} {source target : Tower.Tm n}
    (fixed : ∀ next, NativeRelatorConversionParallel.Par source next → next = source)
    (steps : NativeRelatorConversionParallel.ParStar source target) : target = source := by
  induction steps with
  | refl => rfl
  | tail previous finalStep ih =>
      subst_vars
      exact fixed _ finalStep

private theorem variable_j_fixed {target : Tower.Tm 6}
    (step : NativeRelatorConversionParallel.Par variableInput.nativeJ.code target) :
    target = variableInput.nativeJ.code :=
  parallel_open_j (5 : Fin 6) 4 2 1 0 (.var 3)
    (fun _ => parallel_variable) step

private theorem abstracted_j_fixed {target : Tower.Tm 6}
    (step : NativeRelatorConversionParallel.Par (abstractedInput variableInput).nativeJ.code target) :
    target = (abstractedInput variableInput).nativeJ.code :=
  parallel_open_j (5 : Fin 6) 4 2 1 0
    (.lam (.lam (.app (.app (.var 5) (.var 1)) (.var 0))))
    (fun _ => parallel_abstracted_variable_body (5 : Fin 8) 1 0) step

/-- Both neutral J terms are fixed by every parallel development, and
their submitted motive arguments have different outer constructors. -/
theorem eta_collision_native_j :
    variableInput.j.val ≠ (abstractedInput variableInput).j.val := by
  intro same
  have converted := ((QTerm.mk_eq_iff _ _).mp same).2
  obtain ⟨_, fromFirst, fromSecond⟩ := NativeRelatorConversionParallel.conversion_join
    ((OpaqueRelatorExtension.conversion_iff HOLNativeRelatorCompatibility.opacity).mp converted)
  have syntaxes := (finite_parallel_fixed (fun _ => variable_j_fixed) fromFirst).symm.trans
    (finite_parallel_fixed (fun _ => abstracted_j_fixed) fromSecond)
  cases syntaxes

theorem eta_collision_chosen_j :
    variableInput.chosenJ.val ≠ (abstractedInput variableInput).chosenJ.val := by
  intro same
  apply eta_collision_native_j
  have observed := congrArg (fun value => totalSub value variableInput.presentation.inv) same
  change totalSub (totalSub variableInput.j.val variableInput.presentation.hom)
      variableInput.presentation.inv =
    totalSub (totalSub (abstractedInput variableInput).j.val variableInput.presentation.hom)
      variableInput.presentation.inv at observed
  exact (totalSub_inverse variableInput.presentation variableInput.j.val).symm.trans
    (observed.trans (totalSub_inverse variableInput.presentation
      (abstractedInput variableInput).j.val))

theorem eta_collision_chosen_j_heq :
    ¬ HEq variableInput.chosenJ (abstractedInput variableInput).chosenJ := by
  intro same
  exact eta_collision_chosen_j (QuotientComprehensionSyntax.heq_value
    (abstracted_chosen_motive variableInput).symm same)

theorem eta_collision_semantic_input :
    semanticInput (abstractedInput variableInput) = semanticInput variableInput :=
  abstracted_semantic_input variableInput

/-- The missing function-class equality is itself refuted, not merely
omitted from the coarser input observation. -/
theorem eta_collision_function :
    QTerm.mk (motiveFunction variableInput) ≠
      QTerm.mk (motiveFunction (abstractedInput variableInput)) := by
  intro same
  have converted := ((QTerm.mk_eq_iff _ _).mp same).2
  obtain ⟨_, fromFirst, fromSecond⟩ := NativeRelatorConversionParallel.conversion_join
    ((OpaqueRelatorExtension.conversion_iff HOLNativeRelatorCompatibility.opacity).mp converted)
  have firstFixed := finite_parallel_fixed (fun _ => parallel_variable) fromFirst
  have secondFixed := finite_parallel_fixed
    (fun _ => parallel_abstracted_variable_body (3 : Fin 6) 1 0) fromSecond
  have impossible := firstFixed.symm.trans secondFixed
  cases impossible

/-- Equal type, left value, transported motive family, and method do not
determine this exact native J value. Both requests are actually admitted. -/
theorem eta_collision_inputs :
    QType.mk (abstractedInput variableInput).element = QType.mk variableInput.element ∧
    QTerm.mk (abstractedInput variableInput).leftTerm = QTerm.mk variableInput.leftTerm ∧
    tySub (QType.mk (abstractedInput variableInput).motiveType)
        (abstractedInput variableInput).presentation.hom =
      tySub (QType.mk variableInput.motiveType) variableInput.presentation.hom ∧
    HEq (abstractedInput variableInput).base variableInput.base ∧
    ¬ HEq variableInput.chosenJ (abstractedInput variableInput).chosenJ :=
  ⟨abstracted_type _, abstracted_left _, abstracted_chosen_motive _,
    abstracted_base_heq _, eta_collision_chosen_j_heq⟩

/-- A positive representative change uses the actual mixed HOL/list/wire
input and its independently admitted beta-expanded domain and returned
endpoint. Its motive remains dependent on both endpoint and path. -/
theorem mixed_parameter_classes (wire : NativeWireData.Wire) :
    let first := QuotientIdentity.Controls.mixedInput wire
    let second := QuotientBasedJRepresentation.Controls.convertedMixedInput wire
    QType.mk first.element = QType.mk second.element ∧
    QTerm.mk first.leftTerm = QTerm.mk second.leftTerm ∧
    QTerm.mk (motiveFunction first) = QTerm.mk (motiveFunction second) ∧
    first.base.val = second.base.val :=
  parameter_classes _ _
    (QuotientBasedJRepresentation.Controls.mixed_types_converted wire)
    (QuotientBasedJRepresentation.Controls.mixed_lefts_converted wire)
    (QuotientBasedJRepresentation.Controls.mixed_motives_converted wire)
    (QuotientBasedJRepresentation.Controls.mixed_methods_converted wire)

theorem mixed_chosen_j_transport (wire : NativeWireData.Wire) :
    let first := QuotientIdentity.Controls.mixedInput wire
    let second := QuotientBasedJRepresentation.Controls.convertedMixedInput wire
    ∃ (types : QType.mk first.element = QType.mk second.element)
      (lefts : QTerm.mk first.leftTerm = QTerm.mk second.leftTerm),
      (tmSub second.chosenJ (chosenInputMap first second types lefts)).val = first.chosenJ.val := by
  obtain ⟨types, lefts, motives, methods⟩ := mixed_parameter_classes wire
  exact ⟨types, lefts, chosen_j_transport_value _ _ types lefts motives methods⟩

end Controls

#print axioms abstracted_chosen_motive
#print axioms abstracted_base_heq
#print axioms abstracted_semantic_input
#print axioms parameter_conversions
#print axioms chosen_motive_transport
#print axioms chosen_j_transport
#print axioms Controls.eta_collision_inputs
#print axioms Controls.eta_collision_semantic_input
#print axioms Controls.eta_collision_function
#print axioms Controls.mixed_chosen_j_transport

end FormationSensitiveContextual.QuotientIdentityInputCoherence
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
