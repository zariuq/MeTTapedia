import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension

/-!
# The actual based-J context and reflexivity substitution

These are the authored native identity declaration and its existing refined
typing rules, in arbitrary formed contexts of a declaration extension. The
parameter predicate is a typed substitution from the original declaration
telescope; it therefore retains the declared dependent motive and method.
No semantic interpretation or additional conversion rule is assumed.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveBasedIdentity

open Presentation Presentation.Declaration Presentation.FormationSensitive
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic RussellTarski

variable {n m : Nat}

def doubleWeaken (term : Tower.Tm n) : Tower.Tm (n + 2) :=
  rename wk (rename wk term)

def basedContext (context : Tower.Ctx n) (type left : Tower.Tm n) : Tower.Ctx (n + 2) :=
  .snoc (.snoc context type) (.id (rename wk type) (rename wk left) (.var 0))

def motiveBody (motive : Tower.Tm n) : Tower.Tm (n + 2) :=
  .app (.app (doubleWeaken motive) (.var 1)) (.var 0)

def methodType (left motive : Tower.Tm n) : Tower.Tm n :=
  .app (.app motive left) (.refl left)

def genericTerm (type left motive method : Tower.Tm n) : Tower.Tm (n + 2) :=
  identityEliminateApp (doubleWeaken type) (doubleWeaken left)
    (doubleWeaken motive) (doubleWeaken method) (.var 1) (.var 0)

def reflexivitySub (left : Tower.Tm n) : Sub Tower.Head (n + 2) n :=
  consSub (.refl left) (consSub left ids)

def pointSub (right witness : Tower.Tm n) : Sub Tower.Head (n + 2) n :=
  consSub witness (consSub right ids)

def Parameters (signature : Signature Tower.Head) (context : Tower.Ctx n)
    (type left motive method : Tower.Tm n) : Prop :=
  ContextFormation (OpaqueRelatorExtension.rules signature) context ∧
    FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature) contextAXPD context
      (identitySchemaSubstitution type left motive method)

theorem parameters_type {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method : Tower.Tm n}
    (parameters : Parameters signature context type left motive method) :
    Typing (OpaqueRelatorExtension.rules signature) context type (sortTm elementLevel) :=
  parameters.2 3

theorem parameters_left {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method : Tower.Tm n}
    (parameters : Parameters signature context type left motive method) :
    Typing (OpaqueRelatorExtension.rules signature) context left type := parameters.2 2

private theorem identity_spine (signature : Signature Tower.Head) (context : Tower.Ctx n) :
    DeclarationSpine (OpaqueRelatorExtension.rules signature) context
      (.const identityEliminateName) (liftClosed identityEliminateType) := by
  apply DeclarationSpine.constant (u := .sort identityEliminateDeclarationLevel)
  · have known : IntrinsicRelator.rules.constantType identityEliminateName = some identityEliminateType := by
      decide
    exact combinedType_of_base IntrinsicRelator.rules signature known
  · exact OpaqueRelatorExtension.relator_typing
      FormationSensitiveNativeIdentity.identityEliminateType_hasType
  · exact .sort identityEliminateDeclarationLevel

/-- Every admitted application recovers the complete declared motive and
method telescope, even when its displayed result has been adjusted by
native conversion or cumulativity. The principal-result replay is retained. -/
theorem arguments_of_judgment {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) {context : Tower.Ctx n}
    {type left motive method right witness displayed : Tower.Tm n}
    (admitted : Judgment (OpaqueRelatorExtension.rules signature) context
      (identityEliminateApp type left motive method right witness) displayed) :
    Parameters signature context type left motive method ∧
    Typing (OpaqueRelatorExtension.rules signature) context right type ∧
    Typing (OpaqueRelatorExtension.rules signature) context witness (.id type left right) ∧
    (∀ {replacement},
      Typing (OpaqueRelatorExtension.rules signature) context replacement (.app (.app motive right) witness) →
      Typing (OpaqueRelatorExtension.rules signature) context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope
    OpaqueRelatorExtension.universes (OpaqueRelatorExtension.pi_conversion_boundary opacity)
    admitted.context contextAXPDYQ FormationSensitiveNativeIdentity.identityResult
    (FormationSensitiveNativeIdentity.identitySubstitution type left motive method right witness)
    (identity_spine signature context) admitted.typing
  exact ⟨⟨admitted.context, typed.dropNewest.dropNewest⟩, typed 1, typed 0, replay⟩

theorem basedContext_formed {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method : Tower.Tm n}
    (parameters : Parameters signature context type left motive method) :
    ContextFormation (OpaqueRelatorExtension.rules signature) (basedContext context type left) :=
  .snoc (.snoc parameters.1 (parameters_type parameters) (.sort elementLevel))
    (.idForm (parameters_type parameters).weaken (.sort elementLevel)
      (parameters_left parameters).weaken (.var 0)) (.sort elementLevel)

private theorem schema_generic_typed :
    Typing IntrinsicRelator.rules contextAXPDYQ
      (identityEliminateApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (.app (.app (.var 3) (.var 1)) (.var 0)) := by
  have parameters := FormationSensitiveNativeIdentity.identityEliminateAtParameters_hasType
    |>.weaken (extension := .var 3)
    |>.weaken (extension := .id (.var 4) (.var 3) (.var 0))
  have first := Typing.appElim parameters (.var 1)
  have second := Typing.appElim first (.var 0)
  exact second

theorem generic_judgment {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method : Tower.Tm n}
    (parameters : Parameters signature context type left motive method) :
    Judgment (OpaqueRelatorExtension.rules signature) (basedContext context type left)
      (genericTerm type left motive method) (motiveBody motive) := by
  refine ⟨basedContext_formed parameters, ?_⟩
  have lifted := (parameters.2.lift (.var 3)).lift (.id (.var 4) (.var 3) (.var 0))
  have interpreted := (OpaqueRelatorExtension.relator_typing
    (signature := signature) schema_generic_typed).substitute lifted
  exact interpreted

theorem reflexivitySub_typed {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method : Tower.Tm n}
    (parameters : Parameters signature context type left motive method) :
    FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
      (basedContext context type left) context (reflexivitySub left) := by
  have identity : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
      context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (Typing.var (R := OpaqueRelatorExtension.rules signature) (Γ := context) index)
  have point : Typing (OpaqueRelatorExtension.rules signature) context left (subst ids type) := by
    simpa only [subst_ids] using parameters_left parameters
  refine (identity.extend point).extend ?_
  simpa only [subst, subst_consSub_rename_wk, subst_ids, consSub_zero] using
    (Typing.reflIntro (parameters_left parameters))

theorem pointSub_typed {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method right witness : Tower.Tm n}
    (_parameters : Parameters signature context type left motive method)
    (rightTyped : Typing (OpaqueRelatorExtension.rules signature) context right type)
    (witnessTyped : Typing (OpaqueRelatorExtension.rules signature) context witness (.id type left right)) :
    FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
      (basedContext context type left) context (pointSub right witness) := by
  have identity : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
      context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (Typing.var (R := OpaqueRelatorExtension.rules signature) (Γ := context) index)
  have point : Typing (OpaqueRelatorExtension.rules signature) context right (subst ids type) := by
    simpa only [subst_ids] using rightTyped
  refine (identity.extend point).extend ?_
  simpa only [subst, subst_consSub_rename_wk, subst_ids, consSub_zero] using witnessTyped

@[simp] theorem pointSub_doubleWeaken (right witness term : Tower.Tm n) :
    subst (pointSub right witness) (doubleWeaken term) = term := by
  simp only [pointSub, doubleWeaken, subst_consSub_rename_wk, subst_ids]

@[simp] theorem pointSub_motiveBody (right witness motive : Tower.Tm n) :
    subst (pointSub right witness) (motiveBody motive) = .app (.app motive right) witness := by
  change Tm.app (.app (subst (pointSub right witness) (doubleWeaken motive)) right) witness = _
  rw [pointSub_doubleWeaken]

@[simp] theorem pointSub_genericTerm (type left motive method right witness : Tower.Tm n) :
    subst (pointSub right witness) (genericTerm type left motive method) =
      identityEliminateApp type left motive method right witness := by
  change identityEliminateApp (subst (pointSub right witness) (doubleWeaken type))
    (subst (pointSub right witness) (doubleWeaken left))
    (subst (pointSub right witness) (doubleWeaken motive))
    (subst (pointSub right witness) (doubleWeaken method)) right witness = _
  simp only [pointSub_doubleWeaken]

theorem point_judgment {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method right witness : Tower.Tm n}
    (parameters : Parameters signature context type left motive method)
    (rightTyped : Typing (OpaqueRelatorExtension.rules signature) context right type)
    (witnessTyped : Typing (OpaqueRelatorExtension.rules signature) context witness (.id type left right)) :
    Judgment (OpaqueRelatorExtension.rules signature) context
      (identityEliminateApp type left motive method right witness) (.app (.app motive right) witness) := by
  simpa only [pointSub_genericTerm, pointSub_motiveBody] using
    (generic_judgment parameters).substitute parameters.1 (pointSub_typed parameters rightTyped witnessTyped)

@[simp] theorem reflexivitySub_doubleWeaken (left term : Tower.Tm n) :
    subst (reflexivitySub left) (doubleWeaken term) = term := by
  simp only [reflexivitySub, doubleWeaken, subst_consSub_rename_wk, subst_ids]

@[simp] theorem reflexivitySub_motiveBody (left motive : Tower.Tm n) :
    subst (reflexivitySub left) (motiveBody motive) = methodType left motive := by
  change Tm.app (.app (subst (reflexivitySub left) (doubleWeaken motive)) left) (.refl left) = _
  rw [reflexivitySub_doubleWeaken]
  rfl

@[simp] theorem reflexivitySub_genericTerm (type left motive method : Tower.Tm n) :
    subst (reflexivitySub left) (genericTerm type left motive method) =
      identityEliminateApp type left motive method left (.refl left) := by
  change identityEliminateApp (subst (reflexivitySub left) (doubleWeaken type))
    (subst (reflexivitySub left) (doubleWeaken left))
    (subst (reflexivitySub left) (doubleWeaken motive))
    (subst (reflexivitySub left) (doubleWeaken method)) left (.refl left) = _
  simp only [reflexivitySub_doubleWeaken]

theorem reflexivity_judgment {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method : Tower.Tm n}
    (parameters : Parameters signature context type left motive method) :
    Judgment (OpaqueRelatorExtension.rules signature) context
      (identityEliminateApp type left motive method left (.refl left)) (methodType left motive) := by
  simpa only [reflexivitySub_genericTerm, reflexivitySub_motiveBody] using
    (generic_judgment parameters).substitute parameters.1 (reflexivitySub_typed parameters)

theorem method_judgment {signature : Signature Tower.Head} {context : Tower.Ctx n}
    {type left motive method : Tower.Tm n}
    (parameters : Parameters signature context type left motive method) :
    Judgment (OpaqueRelatorExtension.rules signature) context method (methodType left motive) := by
  refine ⟨parameters.1, ?_⟩
  have typed := (OpaqueRelatorExtension.relator_typing (signature := signature)
    FormationSensitiveNativeIdentity.identityIotaRight_hasType).substitute parameters.2
  exact typed

theorem authored_beta (signature : Signature Tower.Head) (type left motive method : Tower.Tm n) :
    (OpaqueRelatorExtension.rules signature).computation.step
      (identityEliminateApp type left motive method left (.refl left)) method :=
  .inherited (.declared ⟨.list (.identity type left motive method)⟩)

private theorem relator_context {signature : Signature Tower.Head} {context : Tower.Ctx n}
    (formed : ContextFormation IntrinsicRelator.rules context) :
    ContextFormation (OpaqueRelatorExtension.rules signature) context := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
    exact .snoc ih (OpaqueRelatorExtension.relator_typing typed) universeWitness

theorem canonical_parameters (signature : Signature Tower.Head) :
    Parameters signature contextAXPD (.var 3) (.var 2) (.var 1) (.var 0) := by
  refine ⟨?_, ?_⟩
  · exact relator_context FormationSensitiveNativeIdentity.contextAXPD_formed
  · intro index
    have identity : identitySchemaSubstitution (.var 3) (.var 2) (.var 1) (.var 0) =
        (ids : Sub Tower.Head 4 4) := by
      funext i
      fin_cases i <;> rfl
    rw [identity, subst_ids]
    exact .var index

#print axioms generic_judgment
#print axioms arguments_of_judgment
#print axioms point_judgment
#print axioms reflexivity_judgment
#print axioms canonical_parameters

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveBasedIdentity
