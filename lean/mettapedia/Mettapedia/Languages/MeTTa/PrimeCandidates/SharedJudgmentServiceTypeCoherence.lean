import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceRegistry
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseTypeCoherence

/-!
# Accepted service payloads and their native type codes

The required registry fixes the target, request interface and native surface.
An accepted artifact retains its original native payload, type and semantic
section. Independent native formation of that very type permits universe
code totality and decoding to apply; acceptance alone does not provide them.

Two meanings of the same admitted type are compared by the existing scoped
comprehension/projection interface. The resulting display-map isomorphism
does not transport the interpretation's arbitrary term relation. The formed
substitution theorem transports the original code and original payload value
using their separately supplied substitution laws, not by choosing a fresh
code or by applying the isomorphism to the term relation.

All native level expressions remain available. No enclosing-universe
operator, two-level ceiling, common-model inhabitant or language choice is
asserted. The concrete registry controls retain the actual mixed-context
wire workload; its current constructor-only interpretation has no type-code
totality, which is proved as a boundary rather than assumed away.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceTypeCoherence

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef
open KernelAuthority NIKMetalogic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive SharedJudgmentFragment
open SharedJudgmentServiceRegistry (Contract nativeSurface specification requiredSpecification)
open SharedJudgmentTypeInterpretation (ComprehensionCoverage)
open SharedJudgmentInterpretation (Context)
open SharedJudgmentUniverseTypeCoherence (WeakeningProjectionCoherent type_meanings_isomorphic)

universe uIndex uArtifact uEvidence u v w w'

variable {Index : Type uIndex} {assembly : Assembly} {C : Cwf.{u, v, w, w'}}
  {targets : Index → AdmissionObject.{uArtifact}}
  {interpretation : SharedJudgmentInterpretation.Data assembly C}

/-- Recover operational qualification while retaining the caller's complete
required contract in the premise. Neither a required face nor its input
interface is replaced by an implementation-selected one. -/
theorem requiredQualification
    (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
    (registry : SharedJudgmentServiceRegistry.Data targets interpretation)
    (qualified : (requiredSpecification contract interpretation).Satisfies registry) :
    (specification targets (fun index => (contract.request index).face) interpretation).Satisfies registry := by
  obtain ⟨services, native, meaning, inputs, _⟩ :=
    (SharedJudgmentServiceRegistry.required_satisfies_iff contract registry).mp qualified
  exact (SharedJudgmentServiceRegistry.satisfies_iff _ registry).mpr
    ⟨fun index => (inputs index).face, services, native, meaning⟩

section Accepted

variable (contract : Contract.{uIndex, uArtifact, uEvidence} targets)
  (registry : SharedJudgmentServiceRegistry.Data targets interpretation)
  (qualified : (requiredSpecification contract interpretation).Satisfies registry)
  (universes : SharedJudgmentUniverseInterpretation.Operations C)
  (decode : SharedJudgmentUniverseInterpretation.CodesDecode interpretation universes)
  (index : Index)
  (request : NIKServiceInvocation.Request
    (registry.serviceAt (requiredQualification contract registry qualified) index))
  (input : NIKServiceInvocation.InputAdmission request)
  {claim : (targets index).Carrier}
  (accepted : (NIKServiceInvocation.invoke request).acceptedValue = some claim)
  {level : LevelExpr Nat}
  (typeAdmitted : Judgment assembly.rules ((registry.attachment index).context claim)
    ((registry.attachment index).nativeType claim) (sortTm level))

include qualified decode input accepted typeAdmitted

/-- The code belongs to the independently admitted type of the exact
accepted payload, not to an independently chosen native proposition. -/
theorem accepted_type_has_code
    (total : SharedJudgmentUniverseInterpretation.CodeTotal interpretation universes) :
    nativeSurface (registry.attachment index) = contract.surface index ∧
    Judgment assembly.rules ((registry.attachment index).context claim)
      ((registry.attachment index).payload claim) ((registry.attachment index).nativeType claim) ∧
    interpretation.term (Context.ofJudgment typeAdmitted)
      ((registry.attachment index).payload claim) ((registry.attachment index).nativeType claim)
      ((registry.attachment index).semanticType claim typeAdmitted.context)
      ((registry.attachment index).value claim typeAdmitted.context) ∧
    ∃ code : C.Tm (interpretation.ctx (Context.ofJudgment typeAdmitted))
        (universes.universe.univ (interpretation.ctx (Context.ofJudgment typeAdmitted)) level),
      interpretation.term (Context.ofJudgment typeAdmitted)
        ((registry.attachment index).nativeType claim) (sortTm level)
        (universes.universe.univ (interpretation.ctx (Context.ofJudgment typeAdmitted)) level) code ∧
      interpretation.ty (Context.ofJudgment typeAdmitted)
        ((registry.attachment index).nativeType claim) (universes.universe.el code) ∧
      interpretation.ty (Context.ofJudgment typeAdmitted)
        ((registry.attachment index).nativeType claim)
        ((registry.attachment index).semanticType claim typeAdmitted.context) := by
  obtain ⟨native, typeMeaning, termMeaning⟩ := registry.accepted_native_and_meaning
    (requiredQualification contract registry qualified) index request input accepted
  obtain ⟨code, codeMeaning⟩ := total _ (Context.ofJudgment typeAdmitted) _ level typeAdmitted
  exact ⟨((SharedJudgmentServiceRegistry.required_satisfies_iff contract registry).mp qualified).2.2.2.2 index,
    native, termMeaning, code, codeMeaning,
    decode _ (Context.ofJudgment typeAdmitted) _ level code typeAdmitted codeMeaning, typeMeaning⟩

/-- The isomorphism compares decoded and service type meanings only. The
payload's term relation is retained at its original semantic type and value. -/
theorem accepted_code_coherence
    (coverage : ComprehensionCoverage interpretation)
    (code : C.Tm (interpretation.ctx (Context.ofJudgment typeAdmitted))
      (universes.universe.univ (interpretation.ctx (Context.ofJudgment typeAdmitted)) level))
    (codeMeaning : interpretation.term (Context.ofJudgment typeAdmitted)
      ((registry.attachment index).nativeType claim) (sortTm level)
      (universes.universe.univ (interpretation.ctx (Context.ofJudgment typeAdmitted)) level) code)
    (coherent : WeakeningProjectionCoherent interpretation (Context.ofJudgment typeAdmitted)
      ((registry.attachment index).nativeType claim) (universes.universe.el code)
      ((registry.attachment index).semanticType claim typeAdmitted.context)) :
    nativeSurface (registry.attachment index) = contract.surface index ∧
    Judgment assembly.rules ((registry.attachment index).context claim)
      ((registry.attachment index).payload claim) ((registry.attachment index).nativeType claim) ∧
    interpretation.term (Context.ofJudgment typeAdmitted)
      ((registry.attachment index).payload claim) ((registry.attachment index).nativeType claim)
      ((registry.attachment index).semanticType claim typeAdmitted.context)
      ((registry.attachment index).value claim typeAdmitted.context) ∧
    interpretation.ty (Context.ofJudgment typeAdmitted)
      ((registry.attachment index).nativeType claim) (universes.universe.el code) ∧
    Nonempty ((⟨universes.universe.el code⟩ :
      TypeOver C (interpretation.ctx (Context.ofJudgment typeAdmitted))) ≅
      ⟨(registry.attachment index).semanticType claim typeAdmitted.context⟩) := by
  obtain ⟨native, typeMeaning, termMeaning⟩ := registry.accepted_native_and_meaning
    (requiredQualification contract registry qualified) index request input accepted
  have decoded := decode _ (Context.ofJudgment typeAdmitted) _ level code typeAdmitted codeMeaning
  exact ⟨((SharedJudgmentServiceRegistry.required_satisfies_iff contract registry).mp qualified).2.2.2.2 index,
    native, termMeaning, decoded,
    type_meanings_isomorphic interpretation coverage (context := Context.ofJudgment typeAdmitted)
      typeAdmitted (.sort level) _ _ coherent decoded typeMeaning⟩

/-- An actual formed substitution transports the selected source code and
the independently interpreted payload section. The target projection
condition concerns only those two resulting type meanings. -/
theorem accepted_substitution_code_coherence
    (coverage : ComprehensionCoverage interpretation)
    (sorts : SharedJudgmentUniverseInterpretation.SortMeaning interpretation universes)
    (stable : SharedJudgmentInterpretation.SubstitutionStable interpretation)
    (universeStable : universes.universe.SubstitutionStable)
    (code : C.Tm (interpretation.ctx (Context.ofJudgment typeAdmitted))
      (universes.universe.univ (interpretation.ctx (Context.ofJudgment typeAdmitted)) level))
    (codeMeaning : interpretation.term (Context.ofJudgment typeAdmitted)
      ((registry.attachment index).nativeType claim) (sortTm level)
      (universes.universe.univ (interpretation.ctx (Context.ofJudgment typeAdmitted)) level) code)
    {m : Nat} (context : Context assembly m)
    (sigma : Sub Tower.Head ((registry.attachment index).scope claim) m)
    (semantic : C.Sub (interpretation.ctx context)
      (interpretation.ctx (Context.ofJudgment typeAdmitted)))
    (typed : FormationSensitive.CtxMor assembly.rules ((registry.attachment index).context claim) context sigma)
    (related : interpretation.sub (Context.ofJudgment typeAdmitted) context sigma semantic)
    (coherent : WeakeningProjectionCoherent interpretation context
      (subst sigma ((registry.attachment index).nativeType claim))
      (universes.universe.el (SharedJudgmentUniverseInterpretation.substituteCode universes universeStable semantic code))
      (C.tySub ((registry.attachment index).semanticType claim typeAdmitted.context) semantic)) :
    let targetCode := SharedJudgmentUniverseInterpretation.substituteCode universes universeStable semantic code
    Judgment assembly.rules context (subst sigma ((registry.attachment index).payload claim))
      (subst sigma ((registry.attachment index).nativeType claim)) ∧
    Judgment assembly.rules context (subst sigma ((registry.attachment index).nativeType claim)) (sortTm level) ∧
    interpretation.term context (subst sigma ((registry.attachment index).payload claim))
      (subst sigma ((registry.attachment index).nativeType claim))
      (C.tySub ((registry.attachment index).semanticType claim typeAdmitted.context) semantic)
      (C.tmSub ((registry.attachment index).value claim typeAdmitted.context) semantic) ∧
    interpretation.term context (subst sigma ((registry.attachment index).nativeType claim)) (sortTm level)
      (universes.universe.univ (interpretation.ctx context) level) targetCode ∧
    universes.universe.el targetCode = C.tySub (universes.universe.el code) semantic ∧
    interpretation.ty context (subst sigma ((registry.attachment index).nativeType claim))
      (universes.universe.el targetCode) ∧
    Nonempty ((⟨universes.universe.el targetCode⟩ : TypeOver C (interpretation.ctx context)) ≅
      ⟨C.tySub ((registry.attachment index).semanticType claim typeAdmitted.context) semantic⟩) := by
  obtain ⟨native, typeMeaning, termMeaning⟩ := registry.accepted_substitution
    (requiredQualification contract registry qualified) stable index request input accepted
    context sigma semantic typed related
  have admitted : Judgment assembly.rules context
      (subst sigma ((registry.attachment index).nativeType claim)) (sortTm level) :=
    typeAdmitted.substitute context.formed typed
  have transported := SharedJudgmentUniverseInterpretation.substituted_code_meaning
    interpretation universes sorts stable.2 universeStable
      (source := Context.ofJudgment typeAdmitted) (target := context)
      context.formed typed semantic related typeAdmitted code codeMeaning
  have decoded := decode _ context _ level _ admitted transported
  refine ⟨native, admitted, termMeaning, transported, ?_, decoded,
    type_meanings_isomorphic interpretation coverage (context := context)
      admitted (.sort level) _ _ coherent decoded typeMeaning⟩
  exact universeStable.el_sub code semantic

end Accepted

namespace Controls

open SharedJudgmentServiceInterpretation
open NativeWireDataDenotation

/-- Formation of the returned payload's native Data type is constructed
independently of all four service decisions and their supplied evidence. -/
theorem data_type_admitted :
    Judgment common.rules NativeMatchedTransportDenotation.parameterContext
      NativeWireData.dataType (sortTm Tower.zero) :=
  ⟨NativeMatchedTransportDenotation.parameterContext_formed,
    HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _)⟩

theorem common_data_type_admitted :
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      NativeWireData.dataType (sortTm Tower.zero) :=
  ⟨OpaqueRelatorScopedComputation.Common.context_formed,
    HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _)⟩

/-- All four actual required invocations have accepted payloads and an
independently formed type, while retaining their native constructor meaning. -/
theorem four_accepted_and_formed (face : NIK.Face) :
    (NIKServiceInvocation.invoke (SharedJudgmentServiceRegistry.Controls.request face)).acceptedValue =
      some (SharedJudgmentServiceRegistry.Controls.expected face) ∧
    Judgment common.rules NativeMatchedTransportDenotation.parameterContext
      (WireControls.parameterPayload (SharedJudgmentServiceRegistry.Controls.expected face)) NativeWireData.dataType ∧
    Judgment common.rules NativeMatchedTransportDenotation.parameterContext NativeWireData.dataType (sortTm Tower.zero) ∧
    WireControls.interpretation.ty WireControls.parameterContext NativeWireData.dataType
      (fun _ => Value) ∧
    WireControls.interpretation.term WireControls.parameterContext
      (WireControls.parameterPayload (SharedJudgmentServiceRegistry.Controls.expected face)) NativeWireData.dataType
      (fun _ => Value)
      (fun state => .cons (ofWire (SharedJudgmentServiceRegistry.Controls.expected face)) (state 0)) := by
  have accepted := SharedJudgmentServiceRegistry.Controls.four_invocations face
  have interpreted := SharedJudgmentServiceRegistry.Controls.registry.accepted_native_and_meaning
    (requiredQualification SharedJudgmentServiceRegistry.Controls.contract
      SharedJudgmentServiceRegistry.Controls.registry SharedJudgmentServiceRegistry.Controls.required_registry_qualified)
    face (SharedJudgmentServiceRegistry.Controls.request face)
    (SharedJudgmentServiceRegistry.Controls.request_input face) accepted
  exact ⟨accepted, interpreted.1, data_type_admitted, interpreted.2⟩

/-- Each accepted face also supports the actual capture-safe filling of
the Data parameter by an arbitrary constructor-algebra value. -/
theorem four_formed_substitutions (face : NIK.Face) (value : Value) :
    FormationSensitive.CtxMor common.rules NativeMatchedTransportDenotation.parameterContext
      OpaqueRelatorScopedComputation.Common.context (fillParameter value) ∧
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      (subst (fillParameter value) (WireControls.parameterPayload (SharedJudgmentServiceRegistry.Controls.expected face)))
      NativeWireData.dataType ∧
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context NativeWireData.dataType (sortTm Tower.zero) ∧
    WireControls.interpretation.ty WireControls.commonContext NativeWireData.dataType (fun _ => Value) ∧
    WireControls.interpretation.term WireControls.commonContext
      (subst (fillParameter value) (WireControls.parameterPayload (SharedJudgmentServiceRegistry.Controls.expected face)))
      NativeWireData.dataType (fun _ => Value)
      (fun _ => .cons (ofWire (SharedJudgmentServiceRegistry.Controls.expected face)) value) := by
  have interpreted := SharedJudgmentServiceRegistry.Controls.registry.accepted_substitution
    (requiredQualification SharedJudgmentServiceRegistry.Controls.contract
      SharedJudgmentServiceRegistry.Controls.registry SharedJudgmentServiceRegistry.Controls.required_registry_qualified)
    WireControls.interpretation_substitution face (SharedJudgmentServiceRegistry.Controls.request face)
    (SharedJudgmentServiceRegistry.Controls.request_input face)
    (SharedJudgmentServiceRegistry.Controls.four_invocations face)
    WireControls.commonContext (fillParameter value) (WireControls.fillEnvironment value)
    (fillParameter_typed value) (WireControls.fill_related value)
  exact ⟨fillParameter_typed value, interpreted.1, common_data_type_admitted, interpreted.2⟩

theorem fill_is_not_variable : fillParameter (.natural 7) 0 ≠ (.var 0 : Tower.Tm 3) := by decide

/-- Even this accepted payload's formed Data type has no universe-code
meaning in the existing constructor-only relation. Its annotation guard
accepts Data payloads, not terms whose displayed type is a universe. -/
theorem data_has_no_code_meaning
    (semanticType : familiesCwf.Ty (WireControls.interpretation.ctx WireControls.parameterContext))
    (value : familiesCwf.Tm (WireControls.interpretation.ctx WireControls.parameterContext) semanticType) :
    ¬ WireControls.interpretation.term WireControls.parameterContext
      NativeWireData.dataType (sortTm Tower.zero) semanticType value := by
  intro meaning
  have impossible : sortTm Tower.zero = (NativeWireData.dataType : Tower.Tm 4) := meaning.1
  cases impossible

theorem existing_relation_not_code_total
    (universes : SharedJudgmentUniverseInterpretation.Operations familiesCwf) :
    ¬ SharedJudgmentUniverseInterpretation.CodeTotal WireControls.interpretation universes := by
  intro total
  obtain ⟨code, meaning⟩ := total 4 WireControls.parameterContext
    NativeWireData.dataType Tower.zero data_type_admitted
  exact data_has_no_code_meaning _ code meaning

/-- Required service qualification is inhabited, but does not supply the
independent universe interpretation condition at its actual returned type. -/
theorem required_services_do_not_supply_code_total :
    (requiredSpecification SharedJudgmentServiceRegistry.Controls.contract WireControls.interpretation).Satisfies
      SharedJudgmentServiceRegistry.Controls.registry ∧
    Judgment common.rules NativeMatchedTransportDenotation.parameterContext NativeWireData.dataType (sortTm Tower.zero) ∧
    ∀ universes : SharedJudgmentUniverseInterpretation.Operations familiesCwf,
      ¬ SharedJudgmentUniverseInterpretation.CodeTotal WireControls.interpretation universes :=
  ⟨SharedJudgmentServiceRegistry.Controls.required_registry_qualified, data_type_admitted,
    existing_relation_not_code_total⟩

/-! ### An isomorphism is not a term-interpretation transport law -/

/-- Two real results of the same accepted payload at different admitted
parameter substitutions. No replacement evaluator or decoder is introduced. -/
def originalPayload : Tower.Tm 3 :=
  subst (fillParameter .nil) (WireControls.parameterPayload WireControls.actualWire)

def changedPayload : Tower.Tm 3 :=
  subst (fillParameter (.natural 7)) (WireControls.parameterPayload WireControls.actualWire)

def originalValue : Value := .cons (ofWire WireControls.actualWire) .nil
def changedValue : Value := .cons (ofWire WireControls.actualWire) (.natural 7)

theorem values_differ : originalValue ≠ changedValue := by
  intro same
  have tails : Value.nil = .natural 7 := (Value.cons.inj same).2
  cases tails

/-- This automorphism fixes the context and type but exchanges two actual
payload values. Its existence supplies no compatibility with `I.term`. -/
def exchange :
    (⟨fun _ : Fin 3 → Value => Value⟩ : TypeOver familiesCwf (Fin 3 → Value)) ≅
      ⟨fun _ => Value⟩ :=
  SharedJudgmentUniverseTypeCoherence.fibreDisplayIso (fun _ => Equiv.swap originalValue changedValue)

theorem exchange_value :
    TypeOver.transportTerm exchange.hom (fun _ => originalValue) = (fun _ => changedValue) := by
  change TypeOver.transportTerm
    (TypeOver.ofTerm (C := familiesCwf)
      (A := ⟨fun _ : Fin 3 → Value => Value⟩) (B := ⟨fun _ => Value⟩)
      (fun point : Σ _ : Fin 3 → Value, Value =>
        Equiv.swap originalValue changedValue point.2)) (fun _ => originalValue) = _
  simp only [TypeOver.transportTerm]
  rw [TypeOver.toTerm_ofTerm]
  funext state
  exact Equiv.swap_apply_left originalValue changedValue

theorem original_meaning :
    WireControls.interpretation.term WireControls.commonContext originalPayload
      NativeWireData.dataType (fun _ => Value) (fun _ => originalValue) :=
  (WireControls.actual_parameter_substitution .nil).2.2

theorem changed_meaning :
    WireControls.interpretation.term WireControls.commonContext changedPayload
      NativeWireData.dataType (fun _ => Value) (fun _ => changedValue) :=
  (WireControls.actual_parameter_substitution (.natural 7)).2.2

theorem original_does_not_mean_changed :
    ¬ WireControls.interpretation.term WireControls.commonContext originalPayload
      NativeWireData.dataType (fun _ => Value) (fun _ => changedValue) := by
  rintro ⟨_, secondDenotation, second, secondSame⟩
  obtain ⟨_, firstDenotation, first, firstSame⟩ := original_meaning
  have equal : (fun _ : Fin 3 → Value => originalValue) = (fun _ => changedValue) :=
    (eq_of_heq firstSame).trans ((first.functional second).trans (eq_of_heq secondSame).symm)
  exact values_differ (congrFun equal (fun _ => .nil))

/-- Native admission and genuine meanings hold at both endpoints. Applying
the semantic type automorphism to the first section still does not preserve
the meaning of the first native term. -/
theorem isomorphism_does_not_transport_term_meaning :
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context originalPayload NativeWireData.dataType ∧
    Judgment common.rules OpaqueRelatorScopedComputation.Common.context changedPayload NativeWireData.dataType ∧
    WireControls.interpretation.term WireControls.commonContext originalPayload
      NativeWireData.dataType (fun _ => Value) (fun _ => originalValue) ∧
    WireControls.interpretation.term WireControls.commonContext changedPayload
      NativeWireData.dataType (fun _ => Value) (fun _ => changedValue) ∧
    ¬ WireControls.interpretation.term WireControls.commonContext originalPayload
      NativeWireData.dataType (fun _ => Value) (TypeOver.transportTerm exchange.hom (fun _ => originalValue)) := by
  refine ⟨(WireControls.actual_parameter_substitution .nil).1,
    (WireControls.actual_parameter_substitution (.natural 7)).1,
    original_meaning, changed_meaning, ?_⟩
  rw [exchange_value]
  exact original_does_not_mean_changed

end Controls

#print axioms accepted_type_has_code
#print axioms accepted_code_coherence
#print axioms accepted_substitution_code_coherence
#print axioms Controls.four_accepted_and_formed
#print axioms Controls.four_formed_substitutions
#print axioms Controls.required_services_do_not_supply_code_total
#print axioms Controls.isomorphism_does_not_transport_term_meaning

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceTypeCoherence
