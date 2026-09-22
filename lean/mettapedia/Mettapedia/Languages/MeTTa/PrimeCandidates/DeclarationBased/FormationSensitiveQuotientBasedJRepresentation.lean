import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity

/-!
# Representative independence of admitted native based J

Two independently admitted native parameter tuples may use different
convertible type and left-endpoint codes. The actual typed two-binder
comparison transports their motive annotations and J terms. Equality of
the resulting classes is derived from conversion of the four submitted
arguments, not supplied as an operation law.

The inputs retain the fixed native declaration's actual telescope and
universe restrictions. This does not construct an all-level total J,
identify raw contexts, or add a conversion rule or identity principle.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientBasedJRepresentation

open _root_.CategoryTheory FormationSensitive QuotientIdentity
open QuotientCwf

variable {signature : Declaration.Signature Tower.Head}
variable {context : Context (OpaqueRelatorExtension.rules signature)}

private theorem witness_conversion (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation) :
    Conv (OpaqueRelatorExtension.rules signature).headEq
      (nativeWitness first.element first.leftTerm).code
      (nativeWitness second.element second.leftTerm).code
      (OpaqueRelatorExtension.rules signature).computation :=
  Conv.congId (types.substitute projection) (lefts.substitute projection) (.refl _)

/-- Typing is reused from the existing double-extension comparison. The
adapter changes only its explicit telescope presentation, not its variables. -/
private def comparisonHom (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation) :
    first.basedContext ⟶ second.basedContext where
  substitution := ids
  typed := by
    have typed := (doubleExtensionComparison first.element second.element
      (nativeWitness first.element first.leftTerm) (nativeWitness second.element second.leftTerm)
      types (witness_conversion first second types lefts)).hom.typed
    change FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
      (extend (extend context second.element) (nativeWitness second.element second.leftTerm)).raw
      (extend (extend context first.element) (nativeWitness first.element first.leftTerm)).raw ids at typed
    simpa only [extend, nativeWitness, nativeId, TypeOver.reindex, Term.reindex,
      projectionHom, newest, Based.Admitted.element, Based.Admitted.leftTerm, subst_projection,
      Based.Admitted.basedContext, FormationSensitiveBasedIdentity.basedContext] using typed

def inputComparison (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation) :
    first.basedContext ≅ second.basedContext where
  hom := comparisonHom first second types lefts
  inv := comparisonHom second first types.symm lefts.symm
  hom_inv_id := Hom.ext (subComp_ids_left ids)
  inv_hom_id := Hom.ext (subComp_ids_left ids)

@[simp] theorem inputComparison_hom_substitution (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation) :
    (inputComparison first second types lefts).hom.substitution = ids := rfl

@[simp] theorem inputComparison_inv_substitution (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation) :
    (inputComparison first second types lefts).inv.substitution = ids := rfl

theorem motive_type_transport (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation)
    (motives : Conv (OpaqueRelatorExtension.rules signature).headEq first.motive second.motive
      (OpaqueRelatorExtension.rules signature).computation) :
    tySub (QType.mk second.motiveType) (project (inputComparison first second types lefts).hom) =
      QType.mk first.motiveType := by
  apply (QType.mk_eq_iff _ _).mpr
  change Conv _ (subst ids second.motiveType.code) first.motiveType.code _
  rw [subst_ids]
  exact Conv.congApp (Conv.congApp (motives.renameTerms wk |>.renameTerms wk).symm
    (.refl _)) (.refl _)

/-- The native result annotation and the native six-argument J spine both
descend after the independently typed context transport. -/
theorem j_transport_value (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation)
    (motives : Conv (OpaqueRelatorExtension.rules signature).headEq first.motive second.motive
      (OpaqueRelatorExtension.rules signature).computation)
    (methods : Conv (OpaqueRelatorExtension.rules signature).headEq first.method second.method
      (OpaqueRelatorExtension.rules signature).computation) :
    (tmSub second.j (project (inputComparison first second types lefts).hom)).val = first.j.val := by
  apply (QTerm.mk_eq_iff _ _).mpr
  constructor
  · exact (QType.mk_eq_iff _ _).mp (motive_type_transport first second types lefts motives)
  · change Conv _ (subst ids second.nativeJ.code) first.nativeJ.code _
    rw [subst_ids]
    exact Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp
      (.refl _) (types.renameTerms wk |>.renameTerms wk).symm)
      (lefts.renameTerms wk |>.renameTerms wk).symm)
      (motives.renameTerms wk |>.renameTerms wk).symm)
      (methods.renameTerms wk |>.renameTerms wk).symm) (.refl _)) (.refl _)

/-- Equality in the actual dependent fibre, with its motive annotation
comparison derived above rather than erased. -/
theorem j_transport (first second : Based.Admitted context)
    (types : Conv (OpaqueRelatorExtension.rules signature).headEq first.type second.type
      (OpaqueRelatorExtension.rules signature).computation)
    (lefts : Conv (OpaqueRelatorExtension.rules signature).headEq first.left second.left
      (OpaqueRelatorExtension.rules signature).computation)
    (motives : Conv (OpaqueRelatorExtension.rules signature).headEq first.motive second.motive
      (OpaqueRelatorExtension.rules signature).computation)
    (methods : Conv (OpaqueRelatorExtension.rules signature).headEq first.method second.method
      (OpaqueRelatorExtension.rules signature).computation) :
    TermFibre.compare (motive_type_transport first second types lefts motives)
      (tmSub second.j (project (inputComparison first second types lefts).hom)) = first.j :=
  Subtype.ext (j_transport_value first second types lefts motives methods)

namespace Controls

open NativeIndexedFamilies.Intrinsic

def convertedPoint (wire : NativeWireData.Wire) :
    Term Common.context ComparisonControls.expandedWireType :=
  (Common.result wire).convertType ComparisonControls.expandedWireType
    ComparisonControls.expanded_converts_wire.symm

/-- Both the endpoint and its path occur in the family. Its carrier also
retains the independently formed, beta-expanded Data annotation. -/
def convertedBody (wire : NativeWireData.Wire) : Tower.Tm 2 :=
  .id (.id (FormationSensitiveBasedIdentity.doubleWeaken ComparisonControls.expandedWireType.code)
    (FormationSensitiveBasedIdentity.doubleWeaken (Common.result wire).code) (.var 1))
    (.var 0) (.var 0)

theorem convertedBody_formed (wire : NativeWireData.Wire) :
    Typing HOLNativeRelatorCompatibility.rules
      (FormationSensitiveBasedIdentity.basedContext Common.context.raw
        ComparisonControls.expandedWireType.code (Common.result wire).code)
      (convertedBody wire) (sortTm motiveLevel) := by
  have pathType : Typing HOLNativeRelatorCompatibility.rules
      (FormationSensitiveBasedIdentity.basedContext Common.context.raw
        ComparisonControls.expandedWireType.code (Common.result wire).code)
      (.id (FormationSensitiveBasedIdentity.doubleWeaken ComparisonControls.expandedWireType.code)
        (FormationSensitiveBasedIdentity.doubleWeaken (Common.result wire).code) (.var 1))
      (sortTm Tower.zero) :=
    .idForm ComparisonControls.expandedWireType.formed.weaken.weaken (.sort Tower.zero)
      (convertedPoint wire).typed.weaken.weaken (.var 1)
  exact .cumul (.idForm pathType (.sort Tower.zero) (.var 0) (.var 0)) (fun _ => Nat.zero_le _)

theorem convertedMethod_typed (wire : NativeWireData.Wire) :
    Typing HOLNativeRelatorCompatibility.rules Common.context.raw
      (.refl (.refl (Common.result wire).code))
      (subst (FormationSensitiveBasedIdentity.reflexivitySub (Common.result wire).code)
        (convertedBody wire)) := by
  change Typing _ _ _ (.id (.id
    (subst (FormationSensitiveBasedIdentity.reflexivitySub (Common.result wire).code)
      (FormationSensitiveBasedIdentity.doubleWeaken ComparisonControls.expandedWireType.code))
    (subst (FormationSensitiveBasedIdentity.reflexivitySub (Common.result wire).code)
      (FormationSensitiveBasedIdentity.doubleWeaken (Common.result wire).code))
    (Common.result wire).code) (.refl (Common.result wire).code) (.refl (Common.result wire).code))
  rw [FormationSensitiveBasedIdentity.reflexivitySub_doubleWeaken,
    FormationSensitiveBasedIdentity.reflexivitySub_doubleWeaken]
  exact .reflIntro (.reflIntro (convertedPoint wire).typed)

def convertedMixedInput (wire : NativeWireData.Wire) :
    Based.Admitted (signature := HOLNativeRelatorCompatibility.signature) Common.context :=
  Based.ofBody ComparisonControls.expandedWireType.code (Common.result wire).code
    (.cumul ComparisonControls.expandedWireType.formed (fun _ => Nat.zero_le _))
    (convertedPoint wire).typed (convertedBody wire) (convertedBody_formed wire)
    (.refl (.refl (Common.result wire).code)) (convertedMethod_typed wire)

theorem mixed_types_converted (wire : NativeWireData.Wire) :
    Conv HOLNativeRelatorCompatibility.rules.headEq (QuotientIdentity.Controls.mixedInput wire).type
      (convertedMixedInput wire).type HOLNativeRelatorCompatibility.rules.computation :=
  ComparisonControls.expanded_converts_wire.symm

theorem mixed_lefts_converted (wire : NativeWireData.Wire) :
    Conv HOLNativeRelatorCompatibility.rules.headEq (QuotientIdentity.Controls.mixedInput wire).left
      (convertedMixedInput wire).left HOLNativeRelatorCompatibility.rules.computation :=
  Common.projected_converts_result wire

theorem mixed_motives_converted (wire : NativeWireData.Wire) :
    Conv HOLNativeRelatorCompatibility.rules.headEq (QuotientIdentity.Controls.mixedInput wire).motive
      (convertedMixedInput wire).motive HOLNativeRelatorCompatibility.rules.computation := by
  apply Conv.congLam
  apply Conv.congLam
  exact Conv.congId
    (Conv.congId ((ComparisonControls.expanded_converts_wire.renameTerms wk |>.renameTerms wk).symm)
      ((Common.projected_converts_result wire).renameTerms wk |>.renameTerms wk) (.refl _))
    (.refl _) (.refl _)

theorem mixed_methods_converted (wire : NativeWireData.Wire) :
    Conv HOLNativeRelatorCompatibility.rules.headEq (QuotientIdentity.Controls.mixedInput wire).method
      (convertedMixedInput wire).method HOLNativeRelatorCompatibility.rules.computation :=
  Conv.mapCompatible Tm.refl (fun step => .congRefl step)
    (Conv.mapCompatible Tm.refl (fun step => .congRefl step) (Common.projected_converts_result wire))

theorem mixed_motive_transport (wire : NativeWireData.Wire) :
    tySub (QType.mk (convertedMixedInput wire).motiveType)
        (project (inputComparison (QuotientIdentity.Controls.mixedInput wire) (convertedMixedInput wire)
          (mixed_types_converted wire) (mixed_lefts_converted wire)).hom) =
      QType.mk (QuotientIdentity.Controls.mixedInput wire).motiveType :=
  motive_type_transport _ _ (mixed_types_converted wire) (mixed_lefts_converted wire)
    (mixed_motives_converted wire)

/-- All four submitted argument codes change by proved conversion. The
independently formed path-dependent motive remains the result annotation. -/
theorem mixed_j_transport (wire : NativeWireData.Wire) :
    TermFibre.compare (mixed_motive_transport wire)
      (tmSub (convertedMixedInput wire).j
        (project (inputComparison (QuotientIdentity.Controls.mixedInput wire) (convertedMixedInput wire)
          (mixed_types_converted wire) (mixed_lefts_converted wire)).hom)) =
      (QuotientIdentity.Controls.mixedInput wire).j :=
  j_transport _ _ (mixed_types_converted wire) (mixed_lefts_converted wire)
    (mixed_motives_converted wire) (mixed_methods_converted wire)

theorem mixed_contexts_are_not_raw_equal (wire : NativeWireData.Wire) :
    (QuotientIdentity.Controls.mixedInput wire).basedContext.raw ≠
      (convertedMixedInput wire).basedContext.raw := by
  intro same
  have binders := congrArg (fun raw : Tower.Ctx 2 => Ctx.lookup raw 1) same
  change (.const NativeWireData.dataName : Tower.Tm 2) = .app _ _ at binders
  cases binders

/-- Conversion of the left endpoint is a real condition, even when both
candidate tuples are independently admitted in the same common package. -/
theorem altered_endpoint_not_converted :
    ¬ Conv HOLNativeRelatorCompatibility.rules.headEq
      (QuotientIdentity.Controls.mixedInput (.natural 7)).left
      (QuotientIdentity.Controls.mixedInput (.natural 8)).left
      HOLNativeRelatorCompatibility.rules.computation := by
  intro changed
  have results : Conv HOLNativeRelatorCompatibility.rules.headEq
      (NativeWireData.encode (n := 0) (.natural 7)) (NativeWireData.encode (.natural 8))
      HOLNativeRelatorCompatibility.rules.computation :=
    .trans _ _ _ (Common.projected_converts_result (.natural 7)).symm
      (.trans _ _ _ changed (Common.projected_converts_result (.natural 8)))
  have impossible := (QuotientControls.natural_conversion_iff (n := 0) 7 8).mp results
  cases impossible

/-- An independent method-sensitivity control. The constant motive is used
only here to provide two real admitted, unequal Data branches. -/
def methodInput (number : Nat) :
    Based.Admitted (signature := HOLNativeRelatorCompatibility.signature) Common.context :=
  Based.ofBody NativeWireData.dataType (NativeWireData.encode (.natural 0))
    (.cumul Common.wireType.formed (fun _ => Nat.zero_le _)) (Common.result (.natural 0)).typed
    NativeWireData.dataType
    (.cumul (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _))
      (fun _ => Nat.zero_le _))
    (NativeWireData.encode (.natural number)) (Common.result (.natural number)).typed

/-- Forgetting a changed method would change the actual reflexivity result;
the existing native beta equation and constant rigidity refute that equality. -/
theorem altered_method_changes_j : (methodInput 7).j.val ≠ (methodInput 8).j.val := by
  intro same
  have observed := congrArg (fun value => totalSub value (project (methodInput 7).reflSection)) same
  change (tmSub (methodInput 7).j (project (methodInput 7).reflSection)).val =
    (tmSub (methodInput 8).j (project (methodInput 8).reflSection)).val at observed
  rw [(methodInput 7).beta_value, (methodInput 8).beta_value] at observed
  have converted := ((QTerm.mk_eq_iff _ _).mp observed).2
  have impossible := (QuotientControls.natural_conversion_iff (n := 0) 7 8).mp converted
  cases impossible

end Controls

end FormationSensitiveContextual.QuotientBasedJRepresentation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
