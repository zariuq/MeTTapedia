import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension

/-!
# Refined preservation for the completed native List/J/relator relation

The auxiliary completion permits convertible copies of duplicated metadata.
Its five roots preserve the actual formation-sensitive judgment in arbitrary
formed contexts of an opaque declaration extension. Declaration-spine
recovery supplies the dependent arguments; independently formed schemas and
checked type conversion supply the reducts.

Completed parallel reduction is an auxiliary proof relation, not an authored
execution rule. Its typed common reducts do not establish authored confluence,
subject expansion, or a semantic interpretation of native conversion.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveCompletedRelatorPreservation

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.FormationSensitive (Typing Judgment ContextFormation DeclarationSpine)
open NativeRelatorConversionCompletion (AuthoredConv Root)
open OpaqueRelatorExtension (Opacity rules)

variable {signature : Signature Tower.Head} {n : Nat}

private theorem inherited_conv {left right : Tower.Tm n}
    (conversion : AuthoredConv left right) :
    Conv (rules signature).headEq left right (rules signature).computation :=
  Conv.includeSignature IntrinsicRelator.rules signature conversion

private theorem relator_spine {context : Tower.Ctx n} {term type : Tower.Tm n}
    (spine : DeclarationSpine IntrinsicRelator.rules context term type) :
    DeclarationSpine (rules signature) context term type := by
  induction spine with
  | constant known formed universeWitness =>
      exact .constant
        (combinedType_of_base IntrinsicRelator.rules signature known)
        (formed.includeSignature signature) universeWitness
  | app _ argument ih => exact .app ih (argument.includeSignature signature)

private theorem relator_context {context : Tower.Ctx n}
    (formed : ContextFormation IntrinsicRelator.rules context) :
    ContextFormation (rules signature) context := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (typed.includeSignature signature) universeWitness

private theorem context_prefix {R : Rules Tower.Head} {context : Tower.Ctx n}
    {type : Tower.Tm n} (formed : ContextFormation R (.snoc context type)) :
    ContextFormation R context := by
  cases formed with
  | snoc prior _ _ => exact prior

private theorem extend_converted {k : Nat} {R : Rules Tower.Head}
    {schema : Tower.Ctx k} {context : Tower.Ctx n} {domain : Tower.Tm k}
    {substitution : Sub Tower.Head k n} {term oldType : Tower.Tm n}
    (formed : ContextFormation R (.snoc schema domain))
    (typed : FormationSensitive.CtxMor R schema context substitution)
    (argument : Typing R context term oldType)
    (conversion : Conv R.headEq oldType (subst substitution domain) R.computation) :
    FormationSensitive.CtxMor R (.snoc schema domain) context
      (consSub term substitution) := by
  cases formed with
  | snoc _ domainFormed universeWitness =>
      exact typed.extend
        (.conv argument (domainFormed.substitute typed) universeWitness conversion)

private theorem schema_target {k : Nat} {schemaContext : Tower.Ctx k}
    {term type : Tower.Tm k} {context : Tower.Ctx n}
    {substitution : Sub Tower.Head k n}
    (schema : Judgment IntrinsicRelator.rules schemaContext term type)
    (arguments : FormationSensitive.CtxMor (rules signature)
      schemaContext context substitution) :
    Typing (rules signature) context (subst substitution term) (subst substitution type) :=
  (schema.typing.includeSignature signature).substitute arguments

/-! ## The five completed roots -/

/-- Convertible inner List metadata does not alter the dependent nil result. -/
theorem list_nil_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {element motive nilCase consCase innerElement displayed : Tower.Tm n}
    (coherent : AuthoredConv innerElement element)
    (observed : Typing (rules signature) context
      (Intrinsic.eliminateApp element motive nilCase consCase
        (Intrinsic.nilApp innerElement)) displayed) :
    Typing (rules signature) context nilCase displayed := by
  obtain ⟨typed, principal, _, replay⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opac)
    formed FormationSensitiveNativeListElimination.eliminatorContext
    FormationSensitiveNativeListElimination.eliminatorResult
    (FormationSensitiveNativeListElimination.eliminatorSubstitution
      element motive nilCase consCase (Intrinsic.nilApp innerElement))
    (relator_spine (FormationSensitiveNativeListElimination.eliminateSpine context)) observed
  have target := schema_target FormationSensitiveNativeListElimination.nilIota_judgments.2
    typed.dropNewest
  apply replay
  apply target.withResultOf principal.typing OpaqueRelatorExtension.universes formed
  exact inherited_conv (.symm _ _ (Conv.congApp (.refl _)
    (NativeRelatorConversionCompletion.nilApp_congr coherent)))

/-- Both cons payloads are recovered at the inner declaration's types and
transported into the independently formed outer eliminator schema. -/
theorem list_cons_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {element motive nilCase consCase innerElement head tail displayed : Tower.Tm n}
    (coherent : AuthoredConv innerElement element)
    (observed : Typing (rules signature) context
      (Intrinsic.eliminateApp element motive nilCase consCase
        (Intrinsic.consApp innerElement head tail)) displayed) :
    Typing (rules signature) context
      (.app (.app (.app consCase head) tail)
        (Intrinsic.eliminateApp element motive nilCase consCase tail)) displayed := by
  obtain ⟨typed, principal, _, replay⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opac)
    formed FormationSensitiveNativeListElimination.eliminatorContext
    FormationSensitiveNativeListElimination.eliminatorResult
    (FormationSensitiveNativeListElimination.eliminatorSubstitution
      element motive nilCase consCase (Intrinsic.consApp innerElement head tail))
    (relator_spine (FormationSensitiveNativeListElimination.eliminateSpine context)) observed
  obtain ⟨constructor, _, _, _⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opac)
    formed FormationSensitiveNativeListElimination.constructorContext
    FormationSensitiveNativeListElimination.constructorResult
    (FormationSensitiveNativeListElimination.constructorSubstitution innerElement head tail)
    (relator_spine (FormationSensitiveNativeListElimination.consSpine context))
    (typed (0 : Fin 5))
  have schemaFormed := relator_context (signature := signature)
    FormationSensitiveNativeListElimination.contextAPZSHeadTail_formed
  have withHead := extend_converted (context_prefix schemaFormed) typed.dropNewest
    (constructor (1 : Fin 3)) (inherited_conv coherent)
  have arguments := extend_converted schemaFormed withHead (constructor (0 : Fin 3))
    (inherited_conv (Conv.congApp (.refl _) coherent))
  have target := schema_target FormationSensitiveNativeListElimination.consIota_judgments.2
    arguments
  apply replay
  apply target.withResultOf principal.typing OpaqueRelatorExtension.universes formed
  exact inherited_conv (.symm _ _ (Conv.congApp (.refl _)
    (NativeRelatorConversionCompletion.consApp_congr coherent (.refl _) (.refl _))))

/-- J retains its full endpoint- and identity-witness-dependent motive.
Only the completion's two actual conversion guards are used. -/
theorem identity_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {element point motive reflCase endpoint witness displayed : Tower.Tm n}
    (endpointCoherent : AuthoredConv endpoint point)
    (witnessCoherent : AuthoredConv witness point)
    (observed : Typing (rules signature) context
      (Intrinsic.identityEliminateApp element point motive reflCase endpoint (.refl witness))
      displayed) :
    Typing (rules signature) context reflCase displayed := by
  obtain ⟨typed, principal, _, replay⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opac)
    formed Intrinsic.contextAXPDYQ FormationSensitiveNativeIdentity.identityResult
    (FormationSensitiveNativeIdentity.identitySubstitution
      element point motive reflCase endpoint (.refl witness))
    (relator_spine (FormationSensitiveNativeIdentity.identitySpine context)) observed
  have target := schema_target FormationSensitiveNativeIdentity.identityIota_judgments.2
    typed.dropNewest.dropNewest
  apply replay
  apply target.withResultOf principal.typing OpaqueRelatorExtension.universes formed
  exact inherited_conv (.symm _ _ (Conv.congApp
    (Conv.congApp (.refl _) endpointCoherent)
    (Conv.mapCompatible Tm.refl (fun step => .congRefl step) witnessCoherent)))

/-- The completed relator nil contraction preserves the result at the
original two list indices and the original retained relation witness. -/
theorem relator_nil_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {source target relation motive nilCase consCase sourceList targetList
      innerSource innerTarget innerRelation displayed : Tower.Tm n}
    (sourceCoherent : AuthoredConv innerSource source)
    (targetCoherent : AuthoredConv innerTarget target)
    (relationCoherent : AuthoredConv innerRelation relation)
    (sourceListCoherent : AuthoredConv sourceList (Intrinsic.nilApp source))
    (targetListCoherent : AuthoredConv targetList (Intrinsic.nilApp target))
    (observed : Typing (rules signature) context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        sourceList targetList (IntrinsicRelator.nilRelApp innerSource innerTarget innerRelation))
      displayed) :
    Typing (rules signature) context nilCase displayed := by
  obtain ⟨typed, principal, _, replay⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opac)
    formed FormationSensitiveNativeRelatorElimination.eliminatorContext
    FormationSensitiveNativeRelatorElimination.eliminatorResult
    (FormationSensitiveNativeRelatorElimination.eliminatorSubstitution
      source target relation motive nilCase consCase sourceList targetList
      (IntrinsicRelator.nilRelApp innerSource innerTarget innerRelation))
    (relator_spine (FormationSensitiveNativeRelatorElimination.eliminateSpine context)) observed
  have reduct := schema_target FormationSensitiveNativeRelatorElimination.nilIota_judgments.2
    typed.dropNewest.dropNewest.dropNewest
  apply replay
  apply reduct.withResultOf principal.typing OpaqueRelatorExtension.universes formed
  exact inherited_conv (.symm _ _ (Conv.congApp
    (Conv.congApp (Conv.congApp (.refl _) sourceListCoherent) targetListCoherent)
    (NativeRelatorConversionCompletion.nilRel_congr sourceCoherent targetCoherent
      relationCoherent)))

/-- All six cons payloads are admitted under the outer parameters before
the existing dependent relator schema is instantiated. -/
theorem relator_cons_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    (formed : ContextFormation (rules signature) context)
    {source target relation motive nilCase consCase sourceList targetList
      innerSource innerTarget innerRelation sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence displayed : Tower.Tm n}
    (sourceCoherent : AuthoredConv innerSource source)
    (targetCoherent : AuthoredConv innerTarget target)
    (relationCoherent : AuthoredConv innerRelation relation)
    (sourceListCoherent : AuthoredConv sourceList
      (Intrinsic.consApp source sourceHead sourceTail))
    (targetListCoherent : AuthoredConv targetList
      (Intrinsic.consApp target targetHead targetTail))
    (observed : Typing (rules signature) context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        sourceList targetList
        (IntrinsicRelator.consRelApp innerSource innerTarget innerRelation sourceHead targetHead
          sourceTail targetTail headEvidence tailEvidence)) displayed) :
    Typing (rules signature) context
      (.app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead) sourceTail)
        targetTail) headEvidence) tailEvidence)
        (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
          sourceTail targetTail tailEvidence)) displayed := by
  obtain ⟨typed, principal, _, replay⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opac)
    formed FormationSensitiveNativeRelatorElimination.eliminatorContext
    FormationSensitiveNativeRelatorElimination.eliminatorResult
    (FormationSensitiveNativeRelatorElimination.eliminatorSubstitution
      source target relation motive nilCase consCase sourceList targetList
      (IntrinsicRelator.consRelApp innerSource innerTarget innerRelation sourceHead targetHead
        sourceTail targetTail headEvidence tailEvidence))
    (relator_spine (FormationSensitiveNativeRelatorElimination.eliminateSpine context)) observed
  obtain ⟨constructor, _, _, _⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opac)
    formed FormationSensitiveNativeRelatorElimination.constructorContext
    FormationSensitiveNativeRelatorElimination.constructorResult
    (FormationSensitiveNativeRelatorElimination.constructorSubstitution
      innerSource innerTarget innerRelation sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence)
    (relator_spine (FormationSensitiveNativeRelatorElimination.consRelSpine context))
    (typed (0 : Fin 9))
  have allFormed := relator_context (signature := signature)
    FormationSensitiveNativeRelatorElimination.consContext_formed
  have headFormed := context_prefix allFormed
  have targetTailFormed := context_prefix headFormed
  have sourceTailFormed := context_prefix targetTailFormed
  have targetHeadFormed := context_prefix sourceTailFormed
  have sourceHeadFormed := context_prefix targetHeadFormed
  have withSourceHead := extend_converted sourceHeadFormed
    typed.dropNewest.dropNewest.dropNewest (constructor (5 : Fin 9))
    (inherited_conv sourceCoherent)
  have withTargetHead := extend_converted targetHeadFormed withSourceHead
    (constructor (4 : Fin 9)) (inherited_conv targetCoherent)
  have withSourceTail := extend_converted sourceTailFormed withTargetHead
    (constructor (3 : Fin 9)) (inherited_conv (Conv.congApp (.refl _) sourceCoherent))
  have withTargetTail := extend_converted targetTailFormed withSourceTail
    (constructor (2 : Fin 9)) (inherited_conv (Conv.congApp (.refl _) targetCoherent))
  have withHeadEvidence := extend_converted headFormed withTargetTail
    (constructor (1 : Fin 9))
    (inherited_conv (Conv.congApp (Conv.congApp relationCoherent (.refl _)) (.refl _)))
  have arguments := extend_converted allFormed withHeadEvidence
    (constructor (0 : Fin 9))
    (inherited_conv (Conv.congApp (Conv.congApp (Conv.congApp
      (Conv.congApp (Conv.congApp (.refl _) sourceCoherent) targetCoherent)
      relationCoherent) (.refl _)) (.refl _)))
  have reduct := schema_target FormationSensitiveNativeRelatorElimination.consIota_judgments.2
    arguments
  apply replay
  apply reduct.withResultOf principal.typing OpaqueRelatorExtension.universes formed
  exact inherited_conv (.symm _ _ (Conv.congApp
    (Conv.congApp (Conv.congApp (.refl _) sourceListCoherent) targetListCoherent)
    (NativeRelatorConversionCompletion.consRel_congr sourceCoherent targetCoherent
      relationCoherent (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _))))

/-- Every completed root preserves the original refined displayed judgment
under the extended declarations, not merely an embedded old judgment. -/
theorem root_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    (root : Root source target) :
    Judgment (rules signature) context target type := by
  refine ⟨admitted.context, ?_⟩
  cases root with
  | listNil coherent => exact list_nil_preserves opac admitted.context coherent admitted.typing
  | listCons coherent => exact list_cons_preserves opac admitted.context coherent admitted.typing
  | identity endpoint witness =>
      exact identity_preserves opac admitted.context endpoint witness admitted.typing
  | relNil a b r xs ys =>
      exact relator_nil_preserves opac admitted.context a b r xs ys admitted.typing
  | relCons a b r xs ys =>
      exact relator_cons_preserves opac admitted.context a b r xs ys admitted.typing

/-! ## Reusing refined contextual subject reduction -/

/-- This local rule package retains the extended declarations but uses only
the auxiliary completed computation. It is not an authored runtime package. -/
private def completedRules (signature : Signature Tower.Head) : Rules Tower.Head :=
  { rules signature with computation := NativeRelatorConversionCompletion.computation }

private theorem conservative (opac : Opacity signature) :
    ConversionConservativeExtension (rules signature) (completedRules signature) where
  headEq_eq := rfl
  root_inclusion root := NativeRelatorConversionCompletion.root_inclusion
    ((OpaqueRelatorExtension.root_iff opac).mp root)
  root_sound root := inherited_conv root.sound

private theorem typing_to_completed (opac : Opacity signature)
    {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing (rules signature) context term type) :
    Typing (completedRules signature) context term type := by
  apply FormationSensitive.Dependencies.typing_transfer ?_ typed
  intro requirement valid
  cases requirement with
  | rootStep _ _ _ => exact (conservative opac).root_inclusion valid
  | _ => exact valid

private theorem typing_of_completed (opac : Opacity signature)
    {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing (completedRules signature) context term type) :
    Typing (rules signature) context term type := by
  induction typed with
  | headType head => exact .headType head
  | var index => exact .var index
  | const known _ universeWitness ih => exact .const known ih universeWitness
  | piForm _ universeA _ universeB join ihA ihB =>
      exact .piForm ihA universeA ihB universeB join
  | sigmaForm _ universeA _ universeB join ihA ihB =>
      exact .sigmaForm ihA universeA ihB universeB join
  | lamIntro _ universeWitness _ ihPi ihBody => exact .lamIntro ihPi universeWitness ihBody
  | appElim _ _ ihFunction ihArgument => exact .appElim ihFunction ihArgument
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      exact .pairIntro ihSigma universeWitness ihFirst ihSecond
  | fstElim _ ihPair => exact .fstElim ihPair
  | sndElim _ ihPair => exact .sndElim ihPair
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      exact .idForm ihA universeWitness ihLeft ihRight
  | reflIntro _ ihTerm => exact .reflIntro ihTerm
  | cumul _ order ihTerm => exact .cumul ihTerm order
  | conv _ _ universeWitness conversion ihTerm ihTarget =>
      exact .conv ihTerm ihTarget universeWitness
        ((conservative opac).conversion_backward conversion)

private theorem context_to_completed (opac : Opacity signature)
    {context : Tower.Ctx n} (formed : ContextFormation (rules signature) context) :
    ContextFormation (completedRules signature) context := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (typing_to_completed opac typed) universeWitness

private theorem context_of_completed (opac : Opacity signature)
    {context : Tower.Ctx n} (formed : ContextFormation (completedRules signature) context) :
    ContextFormation (rules signature) context := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (typing_of_completed opac typed) universeWitness

private theorem completed_universes : FormationSensitive.UniverseRegularity
    (completedRules signature) where
  head_target := (OpaqueRelatorExtension.universes (signature := signature)).head_target
  join_target := (OpaqueRelatorExtension.universes (signature := signature)).join_target
  cumulative_target := (OpaqueRelatorExtension.universes (signature := signature)).cumulative_target
  universe_typed := (OpaqueRelatorExtension.universes (signature := signature)).universe_typed

private theorem completed_pi_boundary (opac : Opacity signature) :
    PiConversionBoundary (completedRules signature) where
  components conversion := by
    obtain ⟨domain, codomain⟩ := (OpaqueRelatorExtension.pi_conversion_boundary opac).components
      ((conservative opac).conversion_backward conversion)
    exact ⟨(conservative opac).conversion_forward domain,
      (conservative opac).conversion_forward codomain⟩
  headDisjoint conversion := (OpaqueRelatorExtension.pi_conversion_boundary opac).headDisjoint
    ((conservative opac).conversion_backward conversion)

private theorem completed_sigma_boundary (opac : Opacity signature) :
    SigmaConversionBoundary (completedRules signature) where
  components conversion := by
    obtain ⟨domain, codomain⟩ := (OpaqueRelatorExtension.sigma_conversion_boundary opac).components
      ((conservative opac).conversion_backward conversion)
    exact ⟨(conservative opac).conversion_forward domain,
      (conservative opac).conversion_forward codomain⟩
  headDisjoint conversion := (OpaqueRelatorExtension.sigma_conversion_boundary opac).headDisjoint
    ((conservative opac).conversion_backward conversion)

private theorem completed_heads (opac : Opacity signature) :
    FormationSensitive.HeadPreservation (completedRules signature) := by
  intro k context head next universeLevel typed equal
  exact typing_to_completed opac
    (FormationSensitive.HeadPreservation.includeSignature
      (FormationSensitive.towerHeadPreservation.includeSignature IntrinsicRelator.rawSignature)
      signature typed equal)

private theorem completed_roots (opac : Opacity signature) :
    FormationSensitive.RootPreservation (completedRules signature) := by
  intro k context source target type formed observed root
  exact typing_to_completed opac
    (root_preserves opac
      ⟨context_of_completed opac formed, typing_of_completed opac observed⟩ root).typing

/-- Every completed contextual step preserves the authored refined judgment.
The temporary proof package has exactly the same conversion theory and
typing as the authored opaque extension. -/
theorem completed_step_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    (step : Step NativeRelatorConversionCompletion.rules.headEq source target
      NativeRelatorConversionCompletion.rules.computation) :
    Judgment (rules signature) context target type := by
  have sourceTyping := typing_to_completed opac admitted.typing
  exact ⟨admitted.context, typing_of_completed opac
    (sourceTyping.step_preserves completed_universes (completed_pi_boundary opac)
      (completed_sigma_boundary opac) (completed_heads opac) (completed_roots opac)
      (context_to_completed opac admitted.context) step)⟩

theorem completed_steps_preserve (opac : Opacity signature) {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    (steps : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules source target) :
    Judgment (rules signature) context target type := by
  induction steps with
  | refl => exact admitted
  | tail _ finalStep ih => exact completed_step_preserves opac ih finalStep

/-! ## Parallel development is realized by completed contextual steps -/

private theorem steps_map {m : Nat} {source target : Tower.Tm n}
    (map : Tower.Tm n → Tower.Tm m)
    (compatible : ∀ {left right : Tower.Tm n},
      Step NativeRelatorConversionCompletion.rules.headEq left right
        NativeRelatorConversionCompletion.rules.computation →
      Step NativeRelatorConversionCompletion.rules.headEq (map left) (map right)
        NativeRelatorConversionCompletion.rules.computation)
    (steps : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules source target) :
    ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules
      (map source) (map target) := by
  induction steps with
  | refl => exact .refl
  | tail _ finalStep ih => exact .tail ih (compatible finalStep)

private theorem steps_app {function function' argument argument' : Tower.Tm n}
    (functions : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules
      function function')
    (arguments : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules
      argument argument') :
    ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules
      (.app function argument) (.app function' argument') :=
  (steps_map (fun next => .app next argument) (fun step => .congAppFun step) functions).trans
    (steps_map (fun next => .app function' next) (fun step => .congAppArg step) arguments)

private theorem steps_list_elim {a p z s t a' p' z' s' t' : Tower.Tm n}
    (ha : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules a a')
    (hp : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules p p')
    (hz : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules z z')
    (hs : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules s s')
    (ht : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules t t') :
    ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules
      (Intrinsic.eliminateApp a p z s t) (Intrinsic.eliminateApp a' p' z' s' t') :=
  steps_app (steps_app (steps_app (steps_app (steps_app .refl ha) hp) hz) hs) ht

private theorem steps_relator_elim {a b r p z s t u e a' b' r' p' z' s' t' u' e' : Tower.Tm n}
    (ha : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules a a')
    (hb : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules b b')
    (hr : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules r r')
    (hp : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules p p')
    (hz : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules z z')
    (hs : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules s s')
    (ht : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules t t')
    (hu : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules u u')
    (he : ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules e e') :
    ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules
      (IntrinsicRelator.eliminateApp a b r p z s t u e)
      (IntrinsicRelator.eliminateApp a' b' r' p' z' s' t' u' e') :=
  steps_app (steps_app (steps_app (steps_app (steps_app (steps_app (steps_app
    (steps_app (steps_app .refl ha) hb) hr) hp) hz) hs) ht) hu) he

/-- Each actual parallel constructor is a finite forward path of the
completed relation. No forward authored path is asserted. -/
theorem parallel_realizes_completed {source target : Tower.Tm n}
    (parallel : NativeRelatorConversionParallel.Par source target) :
    ConversionCoherence.StepStar NativeRelatorConversionCompletion.rules source target := by
  induction parallel with
  | var _ => exact .refl
  | const _ => exact .refl
  | head _ => exact .refl
  | headRel equal => exact .single (.head equal)
  | pi _ _ first second =>
      exact (steps_map (fun next => .pi next _) (fun step => .congPiDom step) first).trans
        (steps_map (fun next => .pi _ next) (fun step => .congPiCod step) second)
  | sigma _ _ first second =>
      exact (steps_map (fun next => .sigma next _) (fun step => .congSigmaDom step) first).trans
        (steps_map (fun next => .sigma _ next) (fun step => .congSigmaCod step) second)
  | id _ _ _ first second third =>
      exact (steps_map (fun next => .id next _ _) (fun step => .congIdTy step) first).trans
        ((steps_map (fun next => .id _ next _) (fun step => .congIdLeft step) second).trans
          (steps_map (fun next => .id _ _ next) (fun step => .congIdRight step) third))
  | lam _ inner => exact steps_map Tm.lam (fun step => .congLam step) inner
  | app _ _ first second => exact steps_app first second
  | pair _ _ first second =>
      exact (steps_map (fun next => .pair next _) (fun step => .congPairFst step) first).trans
        (steps_map (fun next => .pair _ next) (fun step => .congPairSnd step) second)
  | fst _ inner => exact steps_map Tm.fst (fun step => .congFst step) inner
  | snd _ inner => exact steps_map Tm.snd (fun step => .congSnd step) inner
  | refl _ inner => exact steps_map Tm.refl (fun step => .congRefl step) inner
  | betaPi _ _ body argument =>
      exact (steps_app (steps_map Tm.lam (fun step => .congLam step) body) argument).tail
        (.betaPi _ _)
  | betaSigmaFst _ _ first second =>
      exact (steps_map Tm.fst (fun step => .congFst step)
        ((steps_map (fun next => .pair next _) (fun step => .congPairFst step) first).trans
          (steps_map (fun next => .pair _ next) (fun step => .congPairSnd step) second))).tail
        (.betaSigmaFst _ _)
  | betaSigmaSnd _ _ first second =>
      exact (steps_map Tm.snd (fun step => .congSnd step)
        ((steps_map (fun next => .pair next _) (fun step => .congPairFst step) first).trans
          (steps_map (fun next => .pair _ next) (fun step => .congPairSnd step) second))).tail
        (.betaSigmaSnd _ _)
  | listNil coherent _ _ _ _ _ _ nilCase _ =>
      exact (Relation.ReflTransGen.single (.root (.listNil coherent))).trans nilCase
  | listCons coherent _ _ _ _ _ _ a p z s h t =>
      exact (Relation.ReflTransGen.single (.root (.listCons coherent))).trans
        (steps_app (steps_app (steps_app s h) t) (steps_list_elim a p z s t))
  | identity endpoint witness _ _ _ _ _ _ _ _ _ reflCase _ _ =>
      exact (Relation.ReflTransGen.single (.root (.identity endpoint witness))).trans reflCase
  | relNil a b r xs ys _ _ _ _ _ _ _ _ _ _ _ _ nilCase _ _ _ =>
      exact (Relation.ReflTransGen.single (.root (.relNil a b r xs ys))).trans nilCase
  | relCons ca cb cr cx cy _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b r p z s _ _ h k t u he te =>
      exact (Relation.ReflTransGen.single (.root (.relCons ca cb cr cx cy))).trans
        (steps_app (steps_app (steps_app (steps_app (steps_app (steps_app (steps_app s h) k)
          t) u) he) te) (steps_relator_elim a b r p z s t u te))

/-- Full completed parallel preservation, including reduction under
dependent binders and in code-valued terms of any native universe. -/
theorem parallel_preserves (opac : Opacity signature) {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    (parallel : NativeRelatorConversionParallel.Par source target) :
    Judgment (rules signature) context target type :=
  completed_steps_preserve opac admitted (parallel_realizes_completed parallel)

theorem parallel_steps_preserve (opac : Opacity signature) {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (admitted : Judgment (rules signature) context source type)
    (steps : NativeRelatorConversionParallel.ParStar source target) :
    Judgment (rules signature) context target type := by
  induction steps with
  | refl => exact admitted
  | tail _ finalStep ih => exact parallel_preserves opac ih finalStep

/-- Arbitrary formed endpoints of authored conversion have a completed
common reduct carrying both original displayed typings. Neither the raw
conversion's intermediate terms nor its reversed steps are assumed typed. -/
theorem conversion_typed_join (opac : Opacity signature) {context : Tower.Ctx n}
    {left right leftType rightType : Tower.Tm n}
    (leftAdmitted : Judgment (rules signature) context left leftType)
    (rightAdmitted : Judgment (rules signature) context right rightType)
    (conversion : Conv (rules signature).headEq left right (rules signature).computation) :
    ∃ common,
      NativeRelatorConversionParallel.ParStar left common ∧
      NativeRelatorConversionParallel.ParStar right common ∧
      Judgment (rules signature) context common leftType ∧
      Judgment (rules signature) context common rightType := by
  obtain ⟨common, leftSteps, rightSteps⟩ := NativeRelatorConversionParallel.conversion_join
    ((OpaqueRelatorExtension.conversion_iff opac).mp conversion)
  exact ⟨common, leftSteps, rightSteps,
    parallel_steps_preserve opac leftAdmitted leftSteps,
    parallel_steps_preserve opac rightAdmitted rightSteps⟩

/-! ## Formed positive instances and scope controls -/

namespace Examples

/-- A genuine native beta expansion used in duplicated metadata. -/
def betaCopy (term : Tower.Tm n) : Tower.Tm n := .app (.lam (.var 0)) term

theorem betaCopy_converts (term : Tower.Tm n) : AuthoredConv (betaCopy term) term :=
  .rel _ _ (.betaPi _ _)

private theorem betaCopy_typed {context : Tower.Ctx n} {term type : Tower.Tm n}
    {level : LevelExpr Nat}
    (typed : Typing (rules signature) context term type)
    (typeFormed : Typing (rules signature) context type (sortTm level)) :
    Typing (rules signature) context (betaCopy term) type := by
  have function : Typing (rules signature) context
      (.lam (.var 0)) (.pi type (rename wk type)) := by
    apply Typing.lamIntro (u := .sort (.max level level))
    · exact .piForm typeFormed (.sort level)
        (by simpa only [sortTm, rename] using typeFormed.weaken (extension := type))
        (.sort level) (.sorts level level)
    · exact .sort _
    · exact .var 0
  simpa only [betaCopy, inst0_rename_wk] using Typing.appElim function typed

/-- An actual beta conversion of a native universe code joins endpoints
displayed at different cumulative levels, uniformly in the level expression. -/
theorem universe_conversion_typed_join (opac : Opacity signature) (level : LevelExpr Nat) :
    ∃ common : Tower.Tm 0,
      NativeRelatorConversionParallel.ParStar (betaCopy (sortTm level)) common ∧
      NativeRelatorConversionParallel.ParStar (sortTm level) common ∧
      Judgment (rules signature) .nil common (sortTm (.succ level)) ∧
      Judgment (rules signature) .nil common (sortTm (.succ (.succ level))) := by
  have leftTyped : Judgment (rules signature) .nil
      (betaCopy (sortTm level) : Tower.Tm 0) (sortTm (.succ level)) :=
    ⟨.nil, betaCopy_typed (.headType (.sort level)) (.headType (.sort (.succ level)))⟩
  have rightTyped : Judgment (rules signature) .nil
      (sortTm level : Tower.Tm 0) (sortTm (.succ (.succ level))) := by
    refine ⟨.nil, .cumul (.headType (.sort level)) ?_⟩
    intro valuation
    exact Nat.le_succ _
  exact conversion_typed_join opac leftTyped rightTyped
    (inherited_conv (betaCopy_converts (sortTm level)))

/-- The existing non-diagonal completed nil example is independently
admitted in the full dependent eliminator telescope. -/
theorem mixed_nil_admitted :
    Judgment (rules signature) Intrinsic.contextAPZS
      NativeRelatorConversionCompletion.Examples.mixedNil Intrinsic.nilIotaResultType := by
  have formed := relator_context (signature := signature)
    FormationSensitiveNativeListElimination.contextAPZS_formed
  have element : Typing (rules signature) Intrinsic.contextAPZS
      (betaCopy (.var 3)) (sortTm Intrinsic.elementLevel) :=
    betaCopy_typed (.var 3) (.headType (.sort Intrinsic.elementLevel))
  have nilConstant :=
    (FormationSensitiveNativeList.nilConstant_hasType
      (context := Intrinsic.contextAPZS)).includeSignature signature
  have copiedNil := Typing.appElim nilConstant element
  have canonicalListFormed :=
    (FormationSensitiveNativeList.listApp_hasType
      (FormationSensitive.Typing.var 3 :
        FormationSensitiveNativeList.Typing Intrinsic.contextAPZS (.var 3)
          (sortTm Intrinsic.elementLevel))).includeSignature signature
  have copiedList : Typing (rules signature) Intrinsic.contextAPZS
      (Intrinsic.nilApp (betaCopy (.var 3))) (Intrinsic.listApp (.var 3)) :=
    .conv copiedNil canonicalListFormed (.sort Intrinsic.elementLevel)
      (inherited_conv (Conv.congApp (.refl _) (betaCopy_converts (.var 3))))
  have actual := Typing.appElim
    (FormationSensitiveNativeListElimination.eliminateAtParameters_hasType.includeSignature signature)
    copiedList
  refine ⟨formed, ?_⟩
  apply actual.withResultOf
    (FormationSensitiveNativeListElimination.nilIotaLeft_hasType.includeSignature signature)
    OpaqueRelatorExtension.universes formed
  exact inherited_conv (Conv.congApp (.refl _)
    (NativeRelatorConversionCompletion.nilApp_congr (betaCopy_converts (.var 3))))

/-- Admission and completed preservation do not turn the new contraction
into an exact authored root, nor permit a changed result. -/
theorem mixed_nil_scope (opac : Opacity signature) :
    Judgment (rules signature) Intrinsic.contextAPZS
        NativeRelatorConversionCompletion.Examples.mixedNil Intrinsic.nilIotaResultType ∧
      Judgment (rules signature) Intrinsic.contextAPZS (.var 1) Intrinsic.nilIotaResultType ∧
      (¬ ∃ target, (rules signature).computation.step
        NativeRelatorConversionCompletion.Examples.mixedNil target) ∧
      ¬ Root NativeRelatorConversionCompletion.Examples.mixedNil (.var 0) := by
  refine ⟨mixed_nil_admitted, root_preserves opac mixed_nil_admitted
    NativeRelatorConversionCompletion.Examples.mixed_nil_completed, ?_,
    NativeRelatorConversionCompletion.Examples.changed_nil_result_not_completed⟩
  rintro ⟨target, root⟩
  exact NativeRelatorConversionCompletion.Examples.mixed_nil_not_authored_root
    ((OpaqueRelatorExtension.root_iff opac).mp root)

/-- The motive remains the independent full `P : (y : A) -> Id A x y -> U`
variable of the actual native J telescope. -/
def mixedIdentity : Tower.Tm 4 :=
  Intrinsic.identityEliminateApp (.var 3) (.var 2) (.var 1) (.var 0)
    (betaCopy (.var 2)) (.refl (betaCopy (.var 2)))

def mixedIdentityType : Tower.Tm 4 :=
  .app (.app (.var 1) (betaCopy (.var 2))) (.refl (betaCopy (.var 2)))

theorem mixed_identity_admitted :
    Judgment (rules signature) Intrinsic.contextAXPD mixedIdentity mixedIdentityType := by
  have point : Typing (rules signature) Intrinsic.contextAXPD
      (betaCopy (.var 2)) (.var 3) := betaCopy_typed (.var 2) (.var 3)
  have identityFormed : Typing (rules signature) Intrinsic.contextAXPD
      (.id (.var 3) (.var 2) (betaCopy (.var 2))) (sortTm Intrinsic.elementLevel) :=
    .idForm (.var 3) (.sort Intrinsic.elementLevel) (.var 2) point
  have evidence : Typing (rules signature) Intrinsic.contextAXPD
      (.refl (betaCopy (.var 2))) (.id (.var 3) (.var 2) (betaCopy (.var 2))) :=
    .conv (.reflIntro point) identityFormed (.sort Intrinsic.elementLevel)
      (inherited_conv (Conv.congId (.refl _) (betaCopy_converts (.var 2)) (.refl _)))
  have endpointApplication := Typing.appElim
    (FormationSensitiveNativeIdentity.identityEliminateAtParameters_hasType.includeSignature
      signature) point
  have result := Typing.appElim endpointApplication evidence
  exact ⟨relator_context FormationSensitiveNativeIdentity.contextAXPD_formed, result⟩

theorem mixed_identity_completed : Root mixedIdentity (.var 0) :=
  .identity (betaCopy_converts (.var 2)) (betaCopy_converts (.var 2))

/-- A fresh opaque native type extends the actual J context. -/
def opaqueSignature : Signature Tower.Head := Signature.ofList
  [(`CompletedPreservation.Ambient, ⟨sortTm Tower.zero, none⟩)]

theorem opaque_signature : Opacity opaqueSignature where
  values name := by
    simp [opaqueSignature, Signature.ofList, Signature.valueOf?, Signature.insert,
      Signature.empty]
  roots root := root.elim

def opaqueContext : Tower.Ctx 5 :=
  .snoc Intrinsic.contextAXPD (.const `CompletedPreservation.Ambient)

theorem opaque_context_formed : ContextFormation (rules opaqueSignature) opaqueContext := by
  apply ContextFormation.snoc (u := LevelTower.Head.sort Tower.zero)
  · exact relator_context FormationSensitiveNativeIdentity.contextAXPD_formed
  · apply Typing.const (type := sortTm Tower.zero) (u := LevelTower.Head.sort (.succ Tower.zero))
    · decide
    · exact .headType (.sort Tower.zero)
    · exact .sort _
  · exact .sort Tower.zero

/-- Completed J runs beneath a proof constructor in a genuinely extended
formed context, keeping the unreduced endpoints of the displayed identity. -/
theorem mixed_identity_under_refl :
    Judgment (rules opaqueSignature) opaqueContext
      (.refl (rename wk (.var 0 : Tower.Tm 4)))
      (.id (rename wk mixedIdentityType) (rename wk mixedIdentity) (rename wk mixedIdentity)) := by
  have source : Judgment (rules opaqueSignature) opaqueContext
      (.refl (rename wk mixedIdentity))
      (.id (rename wk mixedIdentityType) (rename wk mixedIdentity) (rename wk mixedIdentity)) :=
    ⟨opaque_context_formed, .reflIntro mixed_identity_admitted.typing.weaken⟩
  exact parallel_preserves opaque_signature source
    (.refl (NativeRelatorConversionParallel.root_to_par (mixed_identity_completed.rename wk)))

/-- Successful completed contraction still supplies no source formation.
The missing declaration remains absent in the same nonempty opaque package. -/
theorem completed_root_does_not_supply_source_admission :
    Root FormationSensitiveNativeRelatorQualification.Examples.unformedRootSource
        FormationSensitiveNativeRelatorQualification.Examples.unformedMethod ∧
      ¬ ∃ type : Tower.Tm 0, Judgment (rules opaqueSignature) .nil
        FormationSensitiveNativeRelatorQualification.Examples.unformedRootSource type := by
  have root : Root FormationSensitiveNativeRelatorQualification.Examples.unformedRootSource
      FormationSensitiveNativeRelatorQualification.Examples.unformedMethod :=
    .relNil (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)
  refine ⟨root, ?_⟩
  rintro ⟨type, admitted⟩
  have result := root_preserves opaque_signature admitted root
  obtain ⟨declaredType, level, known, _, _⟩ := result.typing.constFormation
  have absent : (rules opaqueSignature).constantType
      NativeRelatorConversionChecking.Examples.missingName = none := by decide
  rw [absent] at known
  cases known

private theorem parallel_steps_const {name : DeclName} {target : Tower.Tm n}
    (steps : NativeRelatorConversionParallel.ParStar (.const name) target) :
    target = .const name := by
  induction steps with
  | refl => rfl
  | tail _ finalStep ih =>
      cases ih
      cases finalStep
      rfl

/-- Removing opacity breaks even the formed-endpoint common-reduct result:
a well-typed new delta equation is invisible to the old completed relation. -/
theorem opacity_required_for_typed_join :
    Judgment (rules OpaqueRelatorExtension.Examples.unfolding) .nil
        (.const `OpaqueExtension.universeAlias : Tower.Tm 0) (sortTm (.succ Tower.zero)) ∧
      Judgment (rules OpaqueRelatorExtension.Examples.unfolding) .nil
        (sortTm Tower.zero : Tower.Tm 0) (sortTm (.succ Tower.zero)) ∧
      Conv (rules OpaqueRelatorExtension.Examples.unfolding).headEq
        (.const `OpaqueExtension.universeAlias : Tower.Tm 0) (sortTm Tower.zero)
        (rules OpaqueRelatorExtension.Examples.unfolding).computation ∧
      ¬ ∃ common : Tower.Tm 0,
        NativeRelatorConversionParallel.ParStar (.const `OpaqueExtension.universeAlias) common ∧
        NativeRelatorConversionParallel.ParStar (sortTm Tower.zero) common := by
  have aliasTyped : Typing (rules OpaqueRelatorExtension.Examples.unfolding) .nil
      (.const `OpaqueExtension.universeAlias : Tower.Tm 0) (sortTm (.succ Tower.zero)) := by
    apply Typing.const (type := sortTm (.succ Tower.zero))
      (u := LevelTower.Head.sort (.succ (.succ Tower.zero)))
    · decide
    · exact .headType (.sort (.succ Tower.zero))
    · exact .sort _
  refine ⟨⟨.nil, aliasTyped⟩, ⟨.nil, .headType (.sort Tower.zero)⟩,
    .rel _ _ OpaqueRelatorExtension.Examples.unfolding_step, ?_⟩
  rintro ⟨common, fromConstant, fromHead⟩
  have constantShape := parallel_steps_const fromConstant
  obtain ⟨head, headShape⟩ := NativeRelatorConversionParallel.parStar_head_shape fromHead
  rw [constantShape] at headShape
  cases headShape

end Examples

#print axioms root_preserves
#print axioms parallel_realizes_completed
#print axioms parallel_preserves
#print axioms parallel_steps_preserve
#print axioms conversion_typed_join
#print axioms Examples.universe_conversion_typed_join
#print axioms Examples.mixed_nil_scope
#print axioms Examples.mixed_identity_under_refl
#print axioms Examples.completed_root_does_not_supply_source_admission
#print axioms Examples.opacity_required_for_typed_join

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveCompletedRelatorPreservation
