import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorQualification

/-!
# Opaque declaration extensions of the native List/J/relator calculus

Opaque declarations may add newly typable terms and contexts even though they
add no computation. Thus equality of reduction relations does not by itself
transfer preservation from the old admitted fragment. The five roots below
recover arguments from arbitrary judgments of the extended package and
instantiate the existing formed schemas there.

The individual native-root proofs need only a Pi conversion boundary, not
opacity. Transparent extensions can therefore reuse them after independently
proving their own conversion boundary. Opacity discharges that boundary for
the specialized full-package theorems in this module.

The theorem is parametric in the opaque signature. It supplies preservation
and reuse of the existing exact conversion checker, not consistency of the
added axioms, their intended model, global normalization, or host adoption.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.OpaqueRelatorExtension

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.FormationSensitive (Typing Judgment ContextFormation DeclarationSpine)

/-- Opacity excludes both definition unfolding and new authored roots.
It does not assert that a declaration's type is inhabited or model-valid. -/
structure Opacity (signature : Signature Tower.Head) : Prop where
  values : ∀ name, signature.valueOf? name = none
  roots : ∀ {n : Nat} {left right : Tower.Tm n},
    ¬ signature.computation.step left right

def rules (signature : Signature Tower.Head) : Rules Tower.Head :=
  extendRules IntrinsicRelator.rules signature

variable {signature : Signature Tower.Head} {n : Nat}

theorem root_iff (opac : Opacity signature) {left right : Tower.Tm n} :
    (rules signature).computation.step left right ↔
      IntrinsicRelator.rules.computation.step left right := by
  constructor
  · intro root
    cases root with
    | inherited root => exact root
    | delta lookup => rw [opac.values] at lookup; cases lookup
    | declared root => exact (opac.roots root).elim
  · exact RootStep.inherited

theorem step_iff (opac : Opacity signature) {left right : Tower.Tm n} :
    Step (rules signature).headEq left right (rules signature).computation ↔
      Step IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation := by
  constructor
  · intro step
    simpa only [Tm.mapHead_id] using step.mapHead
      (targetEq := IntrinsicRelator.rules.headEq) (fun head => head) (fun equal => equal)
      (by intro k a b root; simpa only [Tm.mapHead_id] using (root_iff opac).mp root)
  · exact StepCore.includeSignature IntrinsicRelator.rules signature

theorem conversion_iff (opac : Opacity signature) {left right : Tower.Tm n} :
    Conv (rules signature).headEq left right (rules signature).computation ↔
      Conv IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation := by
  constructor
  · intro conversion
    simpa only [Tm.mapHead_id] using conversion.mapHead
      (targetEq := IntrinsicRelator.rules.headEq) (fun head => head) (fun equal => equal)
      (by intro k a b root; simpa only [Tm.mapHead_id] using (root_iff opac).mp root)
  · exact Conv.includeSignature IntrinsicRelator.rules signature

theorem checked_step_iff (opac : Opacity signature) {left right : Tower.Tm n} :
    Step (rules signature).headEq left right (rules signature).computation ↔
      ∃ code, NativeRelatorConversionChecking.checkStep code left right = true :=
  (step_iff opac).trans NativeRelatorConversionChecking.step_iff_checked

theorem checked_conversion_iff (opac : Opacity signature) {left right : Tower.Tm n} :
    Conv (rules signature).headEq left right (rules signature).computation ↔
      ∃ code, NativeRelatorConversionChecking.check code left right = true :=
  (conversion_iff opac).trans NativeRelatorConversionChecking.conversion_iff_checked

theorem pi_conversion_boundary (opac : Opacity signature) :
    PiConversionBoundary (rules signature) where
  components := by
    intro k A A' B B' conversion
    obtain ⟨domain, codomain⟩ :=
      NativeRelatorConversionParallel.nativePiConversionBoundary.components
        ((conversion_iff opac).mp conversion)
    exact ⟨(conversion_iff opac).mpr domain, (conversion_iff opac).mpr codomain⟩
  headDisjoint := fun conversion =>
    NativeRelatorConversionParallel.nativePiConversionBoundary.headDisjoint
      ((conversion_iff opac).mp conversion)

theorem sigma_conversion_boundary (opac : Opacity signature) :
    SigmaConversionBoundary (rules signature) where
  components := by
    intro k A A' B B' conversion
    obtain ⟨domain, codomain⟩ :=
      NativeRelatorConversionParallel.nativeSigmaConversionBoundary.components
        ((conversion_iff opac).mp conversion)
    exact ⟨(conversion_iff opac).mpr domain, (conversion_iff opac).mpr codomain⟩
  headDisjoint := fun conversion =>
    NativeRelatorConversionParallel.nativeSigmaConversionBoundary.headDisjoint
      ((conversion_iff opac).mp conversion)

theorem relator_typing {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing IntrinsicRelator.rules context term type) :
    Typing (rules signature) context term type :=
  typed.includeSignature signature

theorem universes : FormationSensitive.UniverseRegularity (rules signature) :=
  (FormationSensitive.towerUniverseRegularity.includeSignature IntrinsicRelator.rawSignature).includeSignature signature

private theorem relator_spine {context : Tower.Ctx n} {term type : Tower.Tm n}
    (spine : DeclarationSpine IntrinsicRelator.rules context term type) :
    DeclarationSpine (rules signature) context term type := by
  induction spine with
  | constant known formed universeWitness =>
      exact .constant
        (combinedType_of_base IntrinsicRelator.rules signature known)
        (relator_typing formed) universeWitness
  | app _ argument ih => exact .app ih (relator_typing argument)

/-- A schema's existing formation-sensitive derivation is instantiated by
arguments admitted under the combined (rules signature), not by an old-package environment. -/
private theorem schema_target {k : Nat} {schemaContext : Tower.Ctx k}
    {term type : Tower.Tm k} {context : Tower.Ctx n} {substitution : Sub Tower.Head k n}
    (schema : Judgment IntrinsicRelator.rules schemaContext term type)
    (arguments : FormationSensitive.CtxMor (rules signature) schemaContext context substitution) :
    Typing (rules signature) context (subst substitution term) (subst substitution type) :=
  (relator_typing schema.typing).substitute arguments

/-! ## List roots -/

theorem list_nil_preserves (boundary : PiConversionBoundary (rules signature)) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {element motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing (rules signature) context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.nilApp element)) displayed) :
    Typing (rules signature) context nilCase displayed := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes
    boundary formed
    FormationSensitiveNativeListElimination.eliminatorContext
    FormationSensitiveNativeListElimination.eliminatorResult
    (FormationSensitiveNativeListElimination.eliminatorSubstitution
      element motive nilCase consCase (Intrinsic.nilApp element))
    (relator_spine (FormationSensitiveNativeListElimination.eliminateSpine context)) observed
  exact replay (schema_target FormationSensitiveNativeListElimination.nilIota_judgments.2
    typed.dropNewest)

theorem list_cons_preserves (boundary : PiConversionBoundary (rules signature)) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {element motive nilCase consCase head tail displayed : Tower.Tm n}
    (observed : Typing (rules signature) context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.consApp element head tail))
      displayed) :
    Typing (rules signature) context
      (.app (.app (.app consCase head) tail)
        (Intrinsic.eliminateApp element motive nilCase consCase tail)) displayed := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes
    boundary formed
    FormationSensitiveNativeListElimination.eliminatorContext
    FormationSensitiveNativeListElimination.eliminatorResult
    (FormationSensitiveNativeListElimination.eliminatorSubstitution
      element motive nilCase consCase (Intrinsic.consApp element head tail))
    (relator_spine (FormationSensitiveNativeListElimination.eliminateSpine context)) observed
  obtain ⟨constructor, _, _, _⟩ := DeclarationSpine.recoverTelescope universes
    boundary formed
    FormationSensitiveNativeListElimination.constructorContext
    FormationSensitiveNativeListElimination.constructorResult
    (FormationSensitiveNativeListElimination.constructorSubstitution element head tail)
    (relator_spine (FormationSensitiveNativeListElimination.consSpine context)) (typed (0 : Fin 5))
  have parameters : FormationSensitive.CtxMor (rules signature) Intrinsic.contextAPZS context
      (Intrinsic.nilSchemaSubstitution element motive nilCase consCase) := typed.dropNewest
  have withHead : FormationSensitive.CtxMor (rules signature) Intrinsic.contextAPZSHead context
      (consSub head (Intrinsic.nilSchemaSubstitution element motive nilCase consCase)) :=
    parameters.extend (constructor (1 : Fin 3))
  have arguments : FormationSensitive.CtxMor (rules signature) Intrinsic.contextAPZSHeadTail context
      (Intrinsic.consSchemaSubstitution element motive nilCase consCase head tail) :=
    withHead.extend (constructor (0 : Fin 3))
  exact replay (schema_target FormationSensitiveNativeListElimination.consIota_judgments.2 arguments)

/-! ## J root -/

theorem identity_preserves (boundary : PiConversionBoundary (rules signature)) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {element point motive reflCase displayed : Tower.Tm n}
    (observed : Typing (rules signature) context
      (Intrinsic.identityEliminateApp element point motive reflCase point (.refl point)) displayed) :
    Typing (rules signature) context reflCase displayed := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes
    boundary formed Intrinsic.contextAXPDYQ
    FormationSensitiveNativeIdentity.identityResult
    (FormationSensitiveNativeIdentity.identitySubstitution
      element point motive reflCase point (.refl point))
    (relator_spine (FormationSensitiveNativeIdentity.identitySpine context)) observed
  exact replay (schema_target FormationSensitiveNativeIdentity.identityIota_judgments.2
    typed.dropNewest.dropNewest)

/-! ## Proof-relevant List relator roots -/

theorem relator_nil_preserves (boundary : PiConversionBoundary (rules signature)) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {source target relation motive nilCase consCase displayed : Tower.Tm n}
    (observed : Typing (rules signature) context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.nilApp source) (Intrinsic.nilApp target)
        (IntrinsicRelator.nilRelApp source target relation)) displayed) :
    Typing (rules signature) context nilCase displayed := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes
    boundary formed
    FormationSensitiveNativeRelatorElimination.eliminatorContext
    FormationSensitiveNativeRelatorElimination.eliminatorResult
    (FormationSensitiveNativeRelatorElimination.eliminatorSubstitution
      source target relation motive nilCase consCase (Intrinsic.nilApp source)
      (Intrinsic.nilApp target) (IntrinsicRelator.nilRelApp source target relation))
    (relator_spine (FormationSensitiveNativeRelatorElimination.eliminateSpine context)) observed
  exact replay (schema_target FormationSensitiveNativeRelatorElimination.nilIota_judgments.2
    typed.dropNewest.dropNewest.dropNewest)

theorem relator_cons_preserves (boundary : PiConversionBoundary (rules signature)) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail
      targetTail headEvidence tailEvidence displayed : Tower.Tm n}
    (observed : Typing (rules signature) context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail)
        (IntrinsicRelator.consRelApp source target relation sourceHead targetHead sourceTail
          targetTail headEvidence tailEvidence)) displayed) :
    Typing (rules signature) context
      (.app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead) sourceTail)
        targetTail) headEvidence) tailEvidence)
        (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
          sourceTail targetTail tailEvidence)) displayed := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope universes
    boundary formed
    FormationSensitiveNativeRelatorElimination.eliminatorContext
    FormationSensitiveNativeRelatorElimination.eliminatorResult
    (FormationSensitiveNativeRelatorElimination.eliminatorSubstitution
      source target relation motive nilCase consCase
      (Intrinsic.consApp source sourceHead sourceTail)
      (Intrinsic.consApp target targetHead targetTail)
      (IntrinsicRelator.consRelApp source target relation sourceHead targetHead sourceTail
        targetTail headEvidence tailEvidence))
    (relator_spine (FormationSensitiveNativeRelatorElimination.eliminateSpine context)) observed
  obtain ⟨constructor, _, _, _⟩ := DeclarationSpine.recoverTelescope universes
    boundary formed
    FormationSensitiveNativeRelatorElimination.constructorContext
    FormationSensitiveNativeRelatorElimination.constructorResult
    (FormationSensitiveNativeRelatorElimination.constructorSubstitution
      source target relation sourceHead targetHead sourceTail targetTail headEvidence tailEvidence)
    (relator_spine (FormationSensitiveNativeRelatorElimination.consRelSpine context))
    (typed (0 : Fin 9))
  have parameters : FormationSensitive.CtxMor (rules signature) IntrinsicRelator.contextABRPZS context
      (FormationSensitiveNativeRelatorElimination.parameterSubstitution
        source target relation motive nilCase consCase) :=
    typed.dropNewest.dropNewest.dropNewest
  have withSourceHead : FormationSensitive.CtxMor (rules signature) IntrinsicRelator.contextABRPZSSourceHead context
      (consSub sourceHead (FormationSensitiveNativeRelatorElimination.parameterSubstitution
        source target relation motive nilCase consCase)) :=
    parameters.extend (constructor (5 : Fin 9))
  have withTargetHead : FormationSensitive.CtxMor (rules signature) IntrinsicRelator.contextABRPZSSourceTargetHead context
      (consSub targetHead (consSub sourceHead
        (FormationSensitiveNativeRelatorElimination.parameterSubstitution
          source target relation motive nilCase consCase))) :=
    withSourceHead.extend (constructor (4 : Fin 9))
  have withSourceTail : FormationSensitive.CtxMor (rules signature) IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTail context
      (consSub sourceTail (consSub targetHead (consSub sourceHead
        (FormationSensitiveNativeRelatorElimination.parameterSubstitution
          source target relation motive nilCase consCase)))) :=
    withTargetHead.extend (constructor (3 : Fin 9))
  have withTargetTail : FormationSensitive.CtxMor (rules signature) IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTail context
      (consSub targetTail (consSub sourceTail (consSub targetHead (consSub sourceHead
        (FormationSensitiveNativeRelatorElimination.parameterSubstitution
          source target relation motive nilCase consCase))))) :=
    withSourceTail.extend (constructor (2 : Fin 9))
  have withHeadEvidence : FormationSensitive.CtxMor (rules signature) IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHead
      context (consSub headEvidence (consSub targetTail (consSub sourceTail
        (consSub targetHead (consSub sourceHead
          (FormationSensitiveNativeRelatorElimination.parameterSubstitution
            source target relation motive nilCase consCase)))))) :=
    withTargetTail.extend (constructor (1 : Fin 9))
  have arguments : FormationSensitive.CtxMor (rules signature)
      IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail context
      (FormationSensitiveNativeRelatorElimination.consSchemaSubstitution
        source target relation motive nilCase consCase sourceHead targetHead sourceTail
        targetTail headEvidence tailEvidence) :=
    withHeadEvidence.extend (constructor (0 : Fin 9))
  exact replay (schema_target FormationSensitiveNativeRelatorElimination.consIota_judgments.2 arguments)

/-! ## Full combined-package qualification -/

/-- Every declared root preserves every combined-admitted source at its
original displayed type. Old-package source admission is not a premise. -/
theorem root_preservation (opac : Opacity signature) : FormationSensitive.RootPreservation (rules signature) := by
  intro n context source target type formed observed root
  have inherited := (root_iff opac).mp root
  cases inherited with
  | inherited impossible => exact impossible.elim
  | delta lookup =>
      rw [IntrinsicRelator.rawSignature_valueOf_none] at lookup
      cases lookup
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence with
      | list evidence =>
          cases evidence with
          | nil => exact (list_nil_preserves (pi_conversion_boundary opac)) formed observed
          | cons => exact (list_cons_preserves (pi_conversion_boundary opac)) formed observed
          | identity => exact (identity_preserves (pi_conversion_boundary opac)) formed observed
      | rel evidence =>
          cases evidence with
          | nil => exact (relator_nil_preserves (pi_conversion_boundary opac)) formed observed
          | cons => exact (relator_cons_preserves (pi_conversion_boundary opac)) formed observed

private theorem heads : FormationSensitive.HeadPreservation (rules signature) :=
  FormationSensitive.HeadPreservation.includeSignature
    (FormationSensitive.HeadPreservation.includeSignature
      FormationSensitive.towerHeadPreservation IntrinsicRelator.rawSignature)
    signature

/-- Contextual preservation includes beta, projections, head equality and
all five roots beneath every supported native binder and constructor. -/
theorem step_preserves (opac : Opacity signature) {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    (step : Step (rules signature).headEq source target (rules signature).computation) :
    Judgment (rules signature) context target type :=
  admitted.step_preserves universes (pi_conversion_boundary opac) (sigma_conversion_boundary opac) heads
    (root_preservation opac) step

theorem steps_preserve (opac : Opacity signature) {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    (steps : ConversionCoherence.StepStar (rules signature) source target) :
    Judgment (rules signature) context target type :=
  admitted.steps_preserve universes (pi_conversion_boundary opac) (sigma_conversion_boundary opac) heads
    (root_preservation opac) steps

/-- The original executable step checker can now preserve arbitrary
combined-admitted sources, not only embedded old source derivations. -/
theorem checked_step_preserves (opac : Opacity signature) {context : Tower.Ctx n} {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    Judgment (rules signature) context target type :=
  (step_preserves opac) admitted ((checked_step_iff opac).mpr ⟨code, checked⟩)

theorem checked_step_inside_identity (opac : Opacity signature) {context : Tower.Ctx n}
    {source target type : Tower.Tm n} (admitted : Judgment (rules signature) context source type)
    {code : NativeRelatorConversionChecking.StepCode n}
    (checked : NativeRelatorConversionChecking.checkStep code source target = true) :
    Judgment (rules signature) context (.refl target) (.id type source source) :=
  (step_preserves opac) ⟨admitted.context, .reflIntro admitted.typing⟩
    (.congRefl ((checked_step_iff opac).mpr ⟨code, checked⟩))


/-! ## Opacity is a real boundary, not a naming convention -/

namespace Examples

/-- A well-formed universe alias has a genuine definition-unfolding step.
It is deliberately outside the opaque-extension class. -/
def unfolding : Signature Tower.Head := Signature.ofList
  [(`OpaqueExtension.universeAlias,
    ⟨sortTm (.succ Tower.zero), some (sortTm Tower.zero)⟩)]

theorem unfolding_not_opaque : ¬ Opacity unfolding := by
  intro opac
  have absent := opac.values `OpaqueExtension.universeAlias
  have present : unfolding.valueOf? `OpaqueExtension.universeAlias =
      some (sortTm Tower.zero) := by decide
  rw [present] at absent
  cases absent

theorem unfolding_step :
    Step (rules unfolding).headEq (.const `OpaqueExtension.universeAlias : Tower.Tm 0)
      (sortTm Tower.zero) (rules unfolding).computation := by
  apply Step.root
  change RootStep IntrinsicRelator.rules unfolding 0
    (.const `OpaqueExtension.universeAlias) (sortTm Tower.zero)
  exact RootStep.delta (signature := unfolding)
    (name := `OpaqueExtension.universeAlias) (value := sortTm Tower.zero) (by decide)

/-- The old checker cannot validate the new unfolding rule. Even a harmless
definition therefore needs its own extended computation/checker contract. -/
theorem unfolding_rejected_by_old_checker
    (code : NativeRelatorConversionChecking.StepCode 0) :
    NativeRelatorConversionChecking.checkStep code (.const `OpaqueExtension.universeAlias)
      (sortTm Tower.zero) = false := by
  cases checked : NativeRelatorConversionChecking.checkStep code
      (.const `OpaqueExtension.universeAlias) (sortTm Tower.zero) with
  | false => rfl
  | true =>
      have oldStep := NativeRelatorConversionChecking.step_iff_checked.mpr ⟨code, checked⟩
      have parallel := NativeRelatorConversionParallel.authored_step_to_par oldStep
      cases parallel

theorem opacity_cannot_be_omitted :
    ¬ (∀ (signature : Signature Tower.Head) (left right : Tower.Tm 0),
      Step (rules signature).headEq left right (rules signature).computation →
        ∃ code, NativeRelatorConversionChecking.checkStep code left right = true) := by
  intro complete
  obtain ⟨code, accepted⟩ := complete unfolding _ _ unfolding_step
  rw [unfolding_rejected_by_old_checker code] at accepted
  cases accepted

end Examples

#print axioms Examples.opacity_cannot_be_omitted
#print axioms root_iff
#print axioms checked_conversion_iff
#print axioms root_preservation
#print axioms step_preserves
#print axioms steps_preserve
#print axioms checked_step_preserves
#print axioms checked_step_inside_identity

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.OpaqueRelatorExtension
