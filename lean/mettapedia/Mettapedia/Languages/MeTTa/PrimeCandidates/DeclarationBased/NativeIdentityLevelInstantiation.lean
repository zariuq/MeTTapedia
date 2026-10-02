import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMaps

/-!
# Explicit level instances of the native dependent identity declaration

Level substitution is applied to the actual combined List/J/ListRel signature
and, separately, its opaque extension. The constant names and the five authored
iota schemas are retained. This is a transformation of the declaration
environment, not additional polymorphism of the original fixed constant.

The transported formed telescope can be instantiated in arbitrary formed
contexts of the target environment. Target arguments need not be the image of
any source argument. Element and motive levels are independently supplied;
ordinary term substitution still uses the original capture-avoiding machinery.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeIdentityLevelInstantiation

open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic

variable {n m : Nat}

/-- The relational roots, like the existing List/J roots, are structural in
their term arguments and insensitive to a uniform head map. -/
def mapRelatorEvidence (map : Tower.Head → Tower.Head) {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.IotaEvidence n left right) :
    IntrinsicRelator.IotaEvidence n (left.mapHead map) (right.mapHead map) := by
  cases evidence with
  | nil => exact .nil _ _ _ _ _ _
  | cons => exact .cons _ _ _ _ _ _ _ _ _ _ _ _

def mapCombinedEvidence (map : Tower.Head → Tower.Head) {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.CombinedIotaEvidence n left right) :
    IntrinsicRelator.CombinedIotaEvidence n (left.mapHead map) (right.mapHead map) := by
  cases evidence with
  | list evidence => exact .list (IntrinsicMaps.mapIotaEvidence map evidence)
  | rel evidence => exact .rel (mapRelatorEvidence map evidence)

/-- All five existing root schemas are mapped by construction. There is no
new root-preservation assumption on this native signature. -/
def nativeInstance (theta : Nat → LevelExpr Nat) :
    LevelInstance IntrinsicRelator.rawSignature theta where
  computation := IntrinsicRelator.combinedProofRelevantIotaComputation.support
  computationMap := by
    intro k left right root
    rcases root with ⟨evidence⟩
    exact ⟨mapCombinedEvidence (substLevelsHead theta) evidence⟩

def nativeRules (theta : Nat → LevelExpr Nat) : Rules Tower.Head :=
  (nativeInstance theta).rules

/-- The extension's entries undergo the same level substitution. Its roots
are empty; transport from a source extension is licensed only by opacity. -/
def extensionSignature (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    Signature Tower.Head := signature.instantiateLevels theta RootComputation.empty

def rules (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) : Rules Tower.Head :=
  extendRules (nativeRules theta) (extensionSignature theta signature)

theorem native_lookup (theta : Nat → LevelExpr Nat) (name : DeclName) :
    (nativeRules theta).constantType name =
      (IntrinsicRelator.rules.constantType name).map (substLevelsTm theta) := by
  change combinedType Tower.rules (nativeInstance theta).signature name =
    (combinedType Tower.rules IntrinsicRelator.rawSignature name).map _
  simp only [combinedType, LevelTower.rules, LevelInstance.signature,
    Signature.typeOf_instantiateLevels]

def opaqueInstance (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) : LevelInstance signature theta where
  computation := RootComputation.empty
  computationMap := fun root => (opacity.roots root).elim

theorem morphism (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) :
    (OpaqueRelatorExtension.rules signature).Morphism (rules theta signature)
      (substLevelsHead theta) :=
  (opaqueInstance theta opacity).extendMorphism (nativeInstance theta).morphism
    (native_lookup theta)

theorem source_judgment (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {term type : Tower.Tm n}
    (judgment : Judgment (OpaqueRelatorExtension.rules signature) context term type) :
    Judgment (rules theta signature) (substLevelsCtx theta context)
      (substLevelsTm theta term) (substLevelsTm theta type) :=
  judgment.mapHead (morphism theta opacity)

theorem source_substitution (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {replacement : Tower.Ctx m}
    {substitution : Sub Tower.Head n m}
    (typed : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
      context replacement substitution) :
    FormationSensitive.CtxMor (rules theta signature) (substLevelsCtx theta context)
      (substLevelsCtx theta replacement) (fun index => substLevelsTm theta (substitution index)) :=
  typed.mapHead (morphism theta opacity)

theorem native_values_none (theta : Nat → LevelExpr Nat) (name : DeclName) :
    (nativeInstance theta).signature.valueOf? name = none := by
  rw [LevelInstance.signature, Signature.valueOf_instantiateLevels,
    IntrinsicRelator.rawSignature_valueOf_none]
  rfl

theorem extension_values_none (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) (name : DeclName) :
    (extensionSignature theta signature).valueOf? name = none := by
  rw [extensionSignature, Signature.valueOf_instantiateLevels, opacity.values]
  rfl

/-- Instantiation changes declaration types but neither invents nor deletes
any of the five authored native root computations. -/
theorem native_root_iff (theta : Nat → LevelExpr Nat) {left right : Tower.Tm n} :
    (nativeRules theta).computation.step left right ↔
      IntrinsicRelator.rules.computation.step left right := by
  constructor
  · intro root
    cases root with
    | inherited impossible => exact impossible.elim
    | delta known => rw [native_values_none] at known; cases known
    | declared root => exact .declared root
  · intro root
    cases root with
    | inherited impossible => exact impossible.elim
    | delta known => rw [IntrinsicRelator.rawSignature_valueOf_none] at known; cases known
    | declared root => exact .declared root

theorem root_iff (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) {left right : Tower.Tm n} :
    (rules theta signature).computation.step left right ↔
      IntrinsicRelator.rules.computation.step left right := by
  constructor
  · intro root
    cases root with
    | inherited root => exact (native_root_iff theta).mp root
    | delta known => rw [extension_values_none theta opacity] at known; cases known
    | declared impossible => exact impossible.elim
  · intro root
    exact .inherited ((native_root_iff theta).mpr root)

theorem conversion_iff (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) {left right : Tower.Tm n} :
    Conv (rules theta signature).headEq left right (rules theta signature).computation ↔
      Conv IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation := by
  constructor
  · intro conversion
    simpa only [Tm.mapHead_id] using conversion.mapHead
      (targetEq := IntrinsicRelator.rules.headEq) (fun head => head) (fun equal => equal)
      (by intro k a b root; simpa only [Tm.mapHead_id] using (root_iff theta opacity).mp root)
  · intro conversion
    simpa only [Tm.mapHead_id] using conversion.mapHead
      (targetEq := (rules theta signature).headEq) (fun head => head) (fun equal => equal)
      (by intro k a b root; simpa only [Tm.mapHead_id] using (root_iff theta opacity).mpr root)

theorem universes (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    UniverseRegularity (rules theta signature) :=
  (towerUniverseRegularity.includeSignature (nativeInstance theta).signature).includeSignature
    (extensionSignature theta signature)

theorem pi_boundary (theta : Nat → LevelExpr Nat) {signature : Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) : PiConversionBoundary (rules theta signature) where
  components := by
    intro k A A' B B' conversion
    obtain ⟨domain, codomain⟩ :=
      NativeRelatorConversionParallel.nativePiConversionBoundary.components
        ((conversion_iff theta opacity).mp conversion)
    exact ⟨(conversion_iff theta opacity).mpr domain, (conversion_iff theta opacity).mpr codomain⟩
  headDisjoint := fun conversion =>
    NativeRelatorConversionParallel.nativePiConversionBoundary.headDisjoint
      ((conversion_iff theta opacity).mp conversion)

def parametersContext (theta : Nat → LevelExpr Nat) : Tower.Ctx 4 :=
  substLevelsCtx theta contextAXPD

def eliminationContext (theta : Nat → LevelExpr Nat) : Tower.Ctx 6 :=
  substLevelsCtx theta contextAXPDYQ

def declarationType (theta : Nat → LevelExpr Nat) : Tower.Tm 0 :=
  substLevelsTm theta identityEliminateType

theorem declaration_lookup (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    (rules theta signature).constantType identityEliminateName = some (declarationType theta) := by
  change combinedType (nativeRules theta) (extensionSignature theta signature)
    identityEliminateName = some (declarationType theta)
  apply combinedType_of_base
  rw [native_lookup]
  have known : IntrinsicRelator.rules.constantType identityEliminateName = some identityEliminateType := by
    decide
  rw [known]
  rfl

theorem declaration_formed (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    Typing (rules theta signature) .nil (declarationType theta)
      (sortTm (LevelExpr.subst theta identityEliminateDeclarationLevel)) :=
  ((nativeInstance theta).refinedTyping
    FormationSensitiveNativeIdentity.identityEliminateType_hasType).includeSignature
      (extensionSignature theta signature)

theorem parameters_formed (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    ContextFormation (rules theta signature) (parametersContext theta) := by
  change ContextFormation (extendRules (nativeRules theta) (extensionSignature theta signature))
    (substLevelsCtx theta contextAXPD)
  simpa only [Ctx.mapHead_id] using
    ((nativeInstance theta).refinedContext FormationSensitiveNativeIdentity.contextAXPD_formed).mapHead
      (includeMorphism (nativeRules theta) (extensionSignature theta signature))

theorem declaration_judgment (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head)
    {context : Tower.Ctx n} (formed : ContextFormation (rules theta signature) context) :
    Judgment (rules theta signature) context (.const identityEliminateName)
      (liftClosed (declarationType theta)) :=
  ⟨formed, .const (declaration_lookup theta signature) (declaration_formed theta signature) (.sort _)⟩

/-! ## Arbitrary arguments in the actual target environment -/

/-- Admission is a typed substitution into the instantiated declaration
telescope, not a premise asserting that its J application is typable. -/
def Parameters (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head)
    (context : Tower.Ctx n) (type left motive method : Tower.Tm n) : Prop :=
  ContextFormation (rules theta signature) context ∧
    FormationSensitive.CtxMor (rules theta signature) (parametersContext theta) context
      (identitySchemaSubstitution type left motive method)

variable {theta : Nat → LevelExpr Nat} {signature : Signature Tower.Head}
variable {context : Tower.Ctx n} {type left motive method : Tower.Tm n}

theorem parameters_type (parameters : Parameters theta signature context type left motive method) :
    Typing (rules theta signature) context type (sortTm (theta 0)) := parameters.2 3

theorem parameters_left (parameters : Parameters theta signature context type left motive method) :
    Typing (rules theta signature) context left type := parameters.2 2

theorem basedContext_formed
    (parameters : Parameters theta signature context type left motive method) :
    ContextFormation (rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context type left) :=
  .snoc (.snoc parameters.1 (parameters_type parameters) (.sort (theta 0)))
    (.idForm (parameters_type parameters).weaken (.sort (theta 0))
      (parameters_left parameters).weaken (.var 0)) (.sort (theta 0))

private theorem generic_schema :
    Typing IntrinsicRelator.rules contextAXPDYQ
      (identityEliminateApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (.app (.app (.var 3) (.var 1)) (.var 0)) := by
  have parameters := FormationSensitiveNativeIdentity.identityEliminateAtParameters_hasType
    |>.weaken (extension := .var 3)
    |>.weaken (extension := .id (.var 4) (.var 3) (.var 0))
  exact .appElim (.appElim parameters (.var 1)) (.var 0)

/-- The endpoint and equality binders are retained in the actual J motive.
Only the declaration schema is transported; the target context and all four
parameter terms are independently admitted under the new environment. -/
theorem generic_judgment
    (parameters : Parameters theta signature context type left motive method) :
    Judgment (rules theta signature) (FormationSensitiveBasedIdentity.basedContext context type left)
      (FormationSensitiveBasedIdentity.genericTerm type left motive method)
      (FormationSensitiveBasedIdentity.motiveBody motive) := by
  refine ⟨basedContext_formed parameters, ?_⟩
  have schema := ((nativeInstance theta).refinedTyping generic_schema).includeSignature
    (extensionSignature theta signature)
  exact schema.substitute
    ((parameters.2.lift (.var 3)).lift (.id (.var 4) (.var 3) (.var 0)))

theorem reflexivitySub_typed
    (parameters : Parameters theta signature context type left motive method) :
    FormationSensitive.CtxMor (rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context type left) context
      (FormationSensitiveBasedIdentity.reflexivitySub left) := by
  have identity := FormationSensitiveContextual.identityTyped (rules := rules theta signature) context
  have point : Typing (rules theta signature) context left (subst ids type) := by
    simpa only [subst_ids] using parameters_left parameters
  refine (identity.extend point).extend ?_
  simpa only [subst, subst_consSub_rename_wk, subst_ids, consSub_zero] using
    (Typing.reflIntro (parameters_left parameters))

theorem method_judgment
    (parameters : Parameters theta signature context type left motive method) :
    Judgment (rules theta signature) context method
      (FormationSensitiveBasedIdentity.methodType left motive) :=
  ⟨parameters.1,
    (((nativeInstance theta).refinedTyping
      FormationSensitiveNativeIdentity.identityIotaRight_hasType).includeSignature
        (extensionSignature theta signature)).substitute parameters.2⟩

theorem reflexivity_judgment
    (parameters : Parameters theta signature context type left motive method) :
    Judgment (rules theta signature) context
      (identityEliminateApp type left motive method left (.refl left))
      (FormationSensitiveBasedIdentity.methodType left motive) := by
  simpa only [FormationSensitiveBasedIdentity.reflexivitySub_genericTerm,
    FormationSensitiveBasedIdentity.reflexivitySub_motiveBody] using
    (generic_judgment parameters).substitute parameters.1 (reflexivitySub_typed parameters)

/-- The original iota schema still computes to the chosen method, at every
level instance. No evaluation strategy or additional equality rule is used. -/
theorem beta (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head)
    (type left motive method : Tower.Tm n) :
    (rules theta signature).computation.step
      (identityEliminateApp type left motive method left (.refl left)) method :=
  .inherited (.declared ⟨.list (.identity type left motive method)⟩)

theorem beta_judgments
    (parameters : Parameters theta signature context type left motive method) :
    Judgment (rules theta signature) context
        (identityEliminateApp type left motive method left (.refl left))
        (FormationSensitiveBasedIdentity.methodType left motive) ∧
      Judgment (rules theta signature) context method
        (FormationSensitiveBasedIdentity.methodType left motive) ∧
      (rules theta signature).computation.step
        (identityEliminateApp type left motive method left (.refl left)) method :=
  ⟨reflexivity_judgment parameters, method_judgment parameters, beta theta signature ..⟩

theorem parameters_substitute
    (parameters : Parameters theta signature context type left motive method)
    {replacement : Tower.Ctx m} {substitution : Sub Tower.Head n m}
    (formed : ContextFormation (rules theta signature) replacement)
    (typed : FormationSensitive.CtxMor (rules theta signature) context replacement substitution) :
    Parameters theta signature replacement (subst substitution type) (subst substitution left)
      (subst substitution motive) (subst substitution method) := by
  refine ⟨formed, ?_⟩
  have composed := FormationSensitiveContextual.compositionTyped typed parameters.2
  have same : subComp substitution (identitySchemaSubstitution type left motive method) =
      identitySchemaSubstitution (subst substitution type) (subst substitution left)
        (subst substitution motive) (subst substitution method) := by
    funext index
    fin_cases index <;> rfl
  exact same ▸ composed

theorem beta_substitution
    (parameters : Parameters theta signature context type left motive method)
    {replacement : Tower.Ctx m} {substitution : Sub Tower.Head n m}
    (formed : ContextFormation (rules theta signature) replacement)
    (typed : FormationSensitive.CtxMor (rules theta signature) context replacement substitution) :
    Judgment (rules theta signature) replacement
        (subst substitution (identityEliminateApp type left motive method left (.refl left)))
        (subst substitution (FormationSensitiveBasedIdentity.methodType left motive)) ∧
      Judgment (rules theta signature) replacement (subst substitution method)
        (subst substitution (FormationSensitiveBasedIdentity.methodType left motive)) ∧
      (rules theta signature).computation.step
        (subst substitution (identityEliminateApp type left motive method left (.refl left)))
        (subst substitution method) :=
  ⟨(reflexivity_judgment parameters).substitute formed typed,
    (method_judgment parameters).substitute formed typed,
    (rules theta signature).computation.substitute substitution (beta theta signature ..)⟩

theorem arguments_of_judgment (opacity : OpaqueRelatorExtension.Opacity signature)
    {right witness displayed : Tower.Tm n}
    (admitted : Judgment (rules theta signature) context
      (identityEliminateApp type left motive method right witness) displayed) :
    Parameters theta signature context type left motive method ∧
      Typing (rules theta signature) context right type ∧
      Typing (rules theta signature) context witness (.id type left right) ∧
      (∀ {replacement},
        Typing (rules theta signature) context replacement (.app (.app motive right) witness) →
        Typing (rules theta signature) context replacement displayed) := by
  have spine : DeclarationSpine (rules theta signature) context
      (.const identityEliminateName) (liftClosed (declarationType theta)) :=
    .constant (declaration_lookup theta signature) (declaration_formed theta signature) (.sort _)
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope
    (universes theta signature) (pi_boundary theta opacity) admitted.context
    (eliminationContext theta) FormationSensitiveNativeIdentity.identityResult
    (FormationSensitiveNativeIdentity.identitySubstitution type left motive method right witness)
    spine admitted.typing
  exact ⟨⟨admitted.context, typed.dropNewest.dropNewest⟩, typed 1, typed 0, replay⟩

/-- Preservation applies even when conversion or cumulativity changed the
displayed result of the admitted application. -/
theorem identity_preserves (opacity : OpaqueRelatorExtension.Opacity signature)
    {displayed : Tower.Tm n}
    (admitted : Judgment (rules theta signature) context
      (identityEliminateApp type left motive method left (.refl left)) displayed) :
    Judgment (rules theta signature) context method displayed := by
  obtain ⟨parameters, _, _, replay⟩ := arguments_of_judgment opacity admitted
  exact ⟨admitted.context, replay (method_judgment parameters).typing⟩

/-! ## Full admitted motive bodies at independently supplied levels -/

theorem abstract_motive_beta (R : Rules Tower.Head) (body : Tower.Tm (n + 2))
    (right witness : Tower.Tm n) :
    Conv R.headEq (.app (.app (.lam (.lam body)) right) witness)
      (subst (FormationSensitiveBasedIdentity.pointSub right witness) body) R.computation := by
  have first : Conv R.headEq (.app (.app (.lam (.lam body)) right) witness)
      (.app (.lam (subst (liftSub (subst0 right)) body)) witness) R.computation :=
    .rel _ _ (.congAppFun (.betaPi _ _))
  have second : Conv R.headEq (.app (.lam (subst (liftSub (subst0 right)) body)) witness)
      (subst (subst0 witness) (subst (liftSub (subst0 right)) body)) R.computation :=
    .rel _ _ (.betaPi _ _)
  have substitutions : subComp (subst0 witness) (liftSub (subst0 right)) =
      FormationSensitiveBasedIdentity.pointSub right witness := by
    funext index
    refine Fin.cases ?_ (fun prior => Fin.cases ?_ (fun older => ?_) prior) index
    · rfl
    · exact inst0_rename_wk witness right
    · rfl
  rw [subst_subComp, substitutions] at second
  exact .trans _ _ _ first second

/-- Every motive body formed at `theta 1` in the actual based context is
covered; it may depend on both the endpoint and equality witness. Its type
domain is independently formed at `theta 0`. -/
theorem ofBody (formed : ContextFormation (rules theta signature) context)
    (typeFormed : Typing (rules theta signature) context type (sortTm (theta 0)))
    (leftTyped : Typing (rules theta signature) context left type)
    (body : Tower.Tm (n + 2))
    (bodyFormed : Typing (rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context type left) body (sortTm (theta 1)))
    (methodTyped : Typing (rules theta signature) context method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body)) :
    Parameters theta signature context type left (.lam (.lam body)) method := by
  refine ⟨formed, ?_⟩
  have empty : FormationSensitive.CtxMor (rules theta signature) .nil context
      emptySchemaSubstitution := fun index => Fin.elim0 index
  have element : FormationSensitive.CtxMor (rules theta signature)
      (substLevelsCtx theta contextA) context (elementSchemaSubstitution type) :=
    empty.extend typeFormed
  have point : FormationSensitive.CtxMor (rules theta signature)
      (substLevelsCtx theta contextAX) context (consSub left (elementSchemaSubstitution type)) :=
    element.extend leftTyped
  have motiveFormation := (((nativeInstance theta).refinedTyping
    FormationSensitiveNativeIdentity.identityMotiveType_hasType).includeSignature
      (extensionSignature theta signature)).substitute point
  obtain ⟨_, _, _, _, _, innerFormed, innerUniverse, _⟩ := motiveFormation.piFormation
  have motiveTyped : Typing (rules theta signature) context (.lam (.lam body))
      (subst (consSub left (elementSchemaSubstitution type))
        (substLevelsTm theta identityMotiveType)) :=
    .lamIntro motiveFormation (.sort (LevelExpr.subst theta identityMotiveLevel))
      (.lamIntro innerFormed innerUniverse bodyFormed)
  have motive := point.extend motiveTyped
  have methodFormation := (((nativeInstance theta).refinedTyping
    FormationSensitiveNativeIdentity.identityReflCaseType_hasType).includeSignature
      (extensionSignature theta signature)).substitute motive
  exact motive.extend (.conv methodTyped methodFormation (.sort (theta 1))
    (abstract_motive_beta (rules theta signature) body left (.refl left)).symm)

/-- The actual J application and method have the independently supplied
reflexivity-fibre annotation. Two native beta steps connect the lambda motive
to that annotation; the original J iota root supplies the computation. -/
theorem ofBody_beta (formed : ContextFormation (rules theta signature) context)
    (typeFormed : Typing (rules theta signature) context type (sortTm (theta 0)))
    (leftTyped : Typing (rules theta signature) context left type)
    (body : Tower.Tm (n + 2))
    (bodyFormed : Typing (rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context type left) body (sortTm (theta 1)))
    (methodTyped : Typing (rules theta signature) context method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body)) :
    Judgment (rules theta signature) context
        (identityEliminateApp type left (.lam (.lam body)) method left (.refl left))
        (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body) ∧
      Judgment (rules theta signature) context method
        (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body) ∧
      (rules theta signature).computation.step
        (identityEliminateApp type left (.lam (.lam body)) method left (.refl left)) method := by
  have parameters := ofBody formed typeFormed leftTyped body bodyFormed methodTyped
  have resultFormed := bodyFormed.substitute (reflexivitySub_typed parameters)
  refine ⟨⟨formed, ?_⟩, ⟨formed, methodTyped⟩, beta theta signature ..⟩
  exact .conv (reflexivity_judgment parameters).typing resultFormed (.sort (theta 1))
    (abstract_motive_beta (rules theta signature) body left (.refl left))

/-! ## Two independent substitutions and their exact squares -/

/-- This square has two actual substitutions into the two-binder based
context. It retains both the endpoint and its reflexivity witness. -/
theorem reflexivity_substitution_square (substitution : Sub Tower.Head n m) (left : Tower.Tm n) :
    subComp substitution (FormationSensitiveBasedIdentity.reflexivitySub left) =
      subComp (FormationSensitiveBasedIdentity.reflexivitySub (subst substitution left))
        (liftSub (liftSub substitution)) := by
  funext index
  refine Fin.cases ?_ (fun prior => Fin.cases ?_ (fun older => ?_) prior) index
  · rfl
  · rfl
  · exact (FormationSensitiveBasedIdentity.reflexivitySub_doubleWeaken
      (subst substitution left) (substitution older)).symm

theorem motive_reflexivity_substitution (substitution : Sub Tower.Head n m)
    (left : Tower.Tm n) (body : Tower.Tm (n + 2)) :
    subst substitution (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body) =
      subst (FormationSensitiveBasedIdentity.reflexivitySub (subst substitution left))
        (subst (liftSub (liftSub substitution)) body) := by
  rw [subst_subComp, subst_subComp, reflexivity_substitution_square]

theorem ofBody_beta_substitution (formed : ContextFormation (rules theta signature) context)
    (typeFormed : Typing (rules theta signature) context type (sortTm (theta 0)))
    (leftTyped : Typing (rules theta signature) context left type)
    (body : Tower.Tm (n + 2))
    (bodyFormed : Typing (rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context type left) body (sortTm (theta 1)))
    (methodTyped : Typing (rules theta signature) context method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body))
    {replacement : Tower.Ctx m} {substitution : Sub Tower.Head n m}
    (replacementFormed : ContextFormation (rules theta signature) replacement)
    (typed : FormationSensitive.CtxMor (rules theta signature) context replacement substitution) :
    Judgment (rules theta signature) replacement
        (identityEliminateApp (subst substitution type) (subst substitution left)
          (.lam (.lam (subst (liftSub (liftSub substitution)) body)))
          (subst substitution method) (subst substitution left) (.refl (subst substitution left)))
        (subst (FormationSensitiveBasedIdentity.reflexivitySub (subst substitution left))
          (subst (liftSub (liftSub substitution)) body)) ∧
      Judgment (rules theta signature) replacement (subst substitution method)
        (subst (FormationSensitiveBasedIdentity.reflexivitySub (subst substitution left))
          (subst (liftSub (liftSub substitution)) body)) ∧
      (rules theta signature).computation.step
        (identityEliminateApp (subst substitution type) (subst substitution left)
          (.lam (.lam (subst (liftSub (liftSub substitution)) body)))
          (subst substitution method) (subst substitution left) (.refl (subst substitution left)))
        (subst substitution method) := by
  obtain ⟨source, result, root⟩ := ofBody_beta formed typeFormed leftTyped body bodyFormed methodTyped
  refine ⟨?_, ?_, (rules theta signature).computation.substitute substitution root⟩
  · have substituted := source.substitute replacementFormed typed
    rw [motive_reflexivity_substitution] at substituted
    exact substituted
  · have substituted := result.substitute replacementFormed typed
    rw [motive_reflexivity_substitution] at substituted
    exact substituted

/-- Mapping levels before or after an admitted term substitution gives the
same term and type, and both ways are qualified by the refined judgment. -/
theorem source_substitution_square (theta : Nat → LevelExpr Nat)
    (opacity : OpaqueRelatorExtension.Opacity signature)
    {context : Tower.Ctx n} {replacement : Tower.Ctx m}
    {term type : Tower.Tm n} {substitution : Sub Tower.Head n m}
    (source : Judgment (OpaqueRelatorExtension.rules signature) context term type)
    (formed : ContextFormation (OpaqueRelatorExtension.rules signature) replacement)
    (typed : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
      context replacement substitution) :
    Judgment (rules theta signature) (substLevelsCtx theta replacement)
        (substLevelsTm theta (subst substitution term))
        (substLevelsTm theta (subst substitution type)) ∧
      substLevelsTm theta (subst substitution term) =
        subst (fun index => substLevelsTm theta (substitution index)) (substLevelsTm theta term) ∧
      substLevelsTm theta (subst substitution type) =
        subst (fun index => substLevelsTm theta (substitution index)) (substLevelsTm theta type) :=
  ⟨source_judgment theta opacity (source.substitute formed typed),
    Tm.mapHead_subst _ _ _, Tm.mapHead_subst _ _ _⟩

theorem mapped_parameters (theta : Nat → LevelExpr Nat)
    (opacity : OpaqueRelatorExtension.Opacity signature)
    (parameters : FormationSensitiveBasedIdentity.Parameters signature context type left motive method) :
    Parameters theta signature (substLevelsCtx theta context)
      (substLevelsTm theta type) (substLevelsTm theta left)
      (substLevelsTm theta motive) (substLevelsTm theta method) := by
  refine ⟨parameters.1.mapHead (morphism theta opacity), ?_⟩
  have mapped := source_substitution theta opacity parameters.2
  have same : (fun index => substLevelsTm theta
      (identitySchemaSubstitution type left motive method index)) =
      identitySchemaSubstitution (substLevelsTm theta type) (substLevelsTm theta left)
        (substLevelsTm theta motive) (substLevelsTm theta method) := by
    funext index
    fin_cases index <;> rfl
  exact same ▸ mapped

/-- Setting the two declaration levels does not identify them, and leaves
other parameters of the combined native signature untouched. -/
def atLevels (element motive : LevelExpr Nat) : Nat → LevelExpr Nat
  | 0 => element
  | 1 => motive
  | index + 2 => .param (index + 2)

@[simp] theorem atLevels_element (element motive : LevelExpr Nat) : atLevels element motive 0 = element := rfl
@[simp] theorem atLevels_motive (element motive : LevelExpr Nat) : atLevels element motive 1 = motive := rfl
@[simp] theorem atLevels_later (element motive : LevelExpr Nat) (index : Nat) :
    atLevels element motive (index + 2) = .param (index + 2) := rfl

theorem levels_term_comp (later earlier : Nat → LevelExpr Nat) (term : Tower.Tm n) :
    substLevelsTm later (substLevelsTm earlier term) =
      substLevelsTm (fun index => LevelExpr.subst later (earlier index)) term := by
  unfold substLevelsTm
  rw [Tm.mapHead_comp]
  congr 1
  funext head
  cases head with
  | legacyGround => rfl
  | sort level => exact congrArg LevelTower.Head.sort (LevelExpr.subst_subst later earlier level)

theorem levels_context_comp (later earlier : Nat → LevelExpr Nat) (context : Tower.Ctx n) :
    substLevelsCtx later (substLevelsCtx earlier context) =
      substLevelsCtx (fun index => LevelExpr.subst later (earlier index)) context := by
  unfold substLevelsCtx
  rw [Ctx.mapHead_comp]
  congr 1
  funext head
  cases head with
  | legacyGround => rfl
  | sort level => exact congrArg LevelTower.Head.sort (LevelExpr.subst_subst later earlier level)

theorem declaration_comp (later earlier : Nat → LevelExpr Nat) :
    substLevelsTm later (declarationType earlier) =
      declarationType (fun index => LevelExpr.subst later (earlier index)) :=
  levels_term_comp later earlier identityEliminateType

theorem declaration_identity : declarationType LevelExpr.param = identityEliminateType :=
  substLevelsTm_param _

/-! ## Larger-universe and actual mixed-context controls -/

namespace Controls

open FormationSensitiveContextual

/-- The domain itself is a universe. The motive universe is strictly above
its formation level, so the two instantiated J parameters are not identified. -/
def higherLevels (level : LevelExpr Nat) : Nat → LevelExpr Nat :=
  atLevels (.succ level) (.succ (.succ level))

def higherBody (level : LevelExpr Nat) : Tower.Tm (n + 2) :=
  .id (.id (sortTm level) (.head .legacyGround) (.var 1)) (.var 0) (.var 0)

def higherSource (level : LevelExpr Nat) : Tower.Tm n :=
  identityEliminateApp (sortTm level) (.head .legacyGround)
    (.lam (.lam (higherBody level))) (.refl (.refl (.head .legacyGround)))
    (.head .legacyGround) (.refl (.head .legacyGround))

def higherResultType (level : LevelExpr Nat) : Tower.Tm n :=
  .id (.id (sortTm level) (.head .legacyGround) (.head .legacyGround))
    (.refl (.head .legacyGround)) (.refl (.head .legacyGround))

theorem higher_left_typed (level : LevelExpr Nat) (signature : Signature Tower.Head) (context : Tower.Ctx n) :
    Typing (rules (higherLevels level) signature) context (.head .legacyGround) (sortTm level) :=
  .cumul (.headType .legacyGround) (fun _ => Nat.zero_le _)

theorem higher_body_formed (level : LevelExpr Nat) (signature : Signature Tower.Head)
    (context : Tower.Ctx n) :
    Typing (rules (higherLevels level) signature)
      (FormationSensitiveBasedIdentity.basedContext context (sortTm level) (.head .legacyGround))
      (higherBody level) (sortTm (.succ (.succ level))) := by
  have inner : Typing (rules (higherLevels level) signature)
      (FormationSensitiveBasedIdentity.basedContext context (sortTm level) (.head .legacyGround))
      (.id (sortTm level) (.head .legacyGround) (.var 1)) (sortTm (.succ level)) :=
    .idForm (.headType (.sort level)) (.sort (.succ level)) (higher_left_typed level signature _) (.var 1)
  exact .cumul (.idForm inner (.sort (.succ level)) (.var 0) (.var 0))
    (fun _ => Nat.le_succ _)

/-- A genuinely endpoint- and path-dependent motive at arbitrarily large
levels is admitted in every formed target context, not only a mapped source
context or a closed example. -/
theorem higher_beta_crown (level : LevelExpr Nat) (signature : Signature Tower.Head)
    {context : Tower.Ctx n} (formed : ContextFormation (rules (higherLevels level) signature) context) :
    Judgment (rules (higherLevels level) signature) context (higherSource level) (higherResultType level) ∧
      Judgment (rules (higherLevels level) signature) context (.refl (.refl (.head .legacyGround)))
        (higherResultType level) ∧
      (rules (higherLevels level) signature).computation.step
        (higherSource level : Tower.Tm n) (.refl (.refl (.head .legacyGround))) := by
  exact ofBody_beta formed (.headType (.sort level)) (higher_left_typed level signature context)
    (higherBody level) (higher_body_formed level signature context)
    (.reflIntro (.reflIntro (higher_left_typed level signature context)))

/-- This exact same term is admitted after the explicit signature
transformation and rejected by the original fixed J environment. Identity
formation was never the missing capability. -/
theorem higher_requires_new_environment (signature : Signature Tower.Head)
    (opacity : OpaqueRelatorExtension.Opacity signature) :
    Judgment (rules (higherLevels elementLevel) signature) .nil
        (higherSource elementLevel) (higherResultType elementLevel) ∧
      ¬ Judgment (OpaqueRelatorExtension.rules signature) .nil
        (higherSource elementLevel) (higherResultType elementLevel) :=
  ⟨(higher_beta_crown elementLevel signature .nil).1,
    QuotientIdentity.LevelBoundary.no_j_on_own_element_universe opacity _ _ _ _ _ _⟩

theorem higher_wrong_result (level : LevelExpr Nat) (signature : Signature Tower.Head)
    (opacity : OpaqueRelatorExtension.Opacity signature) :
    ¬ (rules (higherLevels level) signature).computation.step
      (higherSource level : Tower.Tm n) (.refl (.head .legacyGround)) := by
  intro root
  have result := (FormationSensitiveNativeIdentity.identity_root_iff.mp
    ((root_iff _ opacity).mp root)).2.2
  cases result

theorem higher_levels_distinct (level : LevelExpr Nat) :
    (∀ valuation, LevelExpr.eval valuation (higherLevels level 0) <
      LevelExpr.eval valuation (higherLevels level 1)) ∧
      higherLevels level 2 = .param 2 :=
  ⟨fun _ => Nat.lt_succ_self _, rfl⟩

/-- Installing another same-named declaration *after* the fixed native base
does not replace the base entry. This is actual lookup priority. -/
theorem appending_keeps_fixed_j (signature added : Signature Tower.Head) :
    (extendRules (OpaqueRelatorExtension.rules signature) added).constantType
      identityEliminateName = some identityEliminateType := by
  have known : IntrinsicRelator.rules.constantType identityEliminateName = some identityEliminateType := by
    decide
  exact combinedType_of_base (OpaqueRelatorExtension.rules signature) added
    (combinedType_of_base IntrinsicRelator.rules signature known)

theorem higher_declaration_differs :
    declarationType (higherLevels elementLevel) ≠ identityEliminateType := by
  intro same
  change Tm.pi _ _ = Tm.pi _ _ at same
  have domain := (Tm.pi.inj same).1
  cases domain

/-- The old mixed HOL/List/wire J, including its path-dependent family,
really transports through the signature morphism. -/
theorem mixed_j_transport (theta : Nat → LevelExpr Nat) (wire : NativeWireData.Wire) :
    let input := QuotientIdentity.Controls.mixedInput wire
    Judgment (rules theta HOLNativeRelatorCompatibility.signature)
      (substLevelsCtx theta input.basedContext.raw)
      (substLevelsTm theta input.nativeJ.code) (substLevelsTm theta input.motiveType.code) :=
  source_judgment theta HOLNativeRelatorCompatibility.opacity
    (QuotientIdentity.Controls.mixedInput wire).nativeJ.judgment

/-- The target substitution here is a real weakening into an extra formed
wire-Data binder of the common environment. Its type and term squares use
the same declaration map as the transported J operation. -/
theorem mixed_weakening_transport (theta : Nat → LevelExpr Nat) (wire : NativeWireData.Wire) :
    let input := QuotientIdentity.Controls.mixedInput wire
    let substitution := projectionHom Common.context Common.wireType
    Judgment (rules theta HOLNativeRelatorCompatibility.signature)
        (substLevelsCtx theta (extend Common.context Common.wireType).raw)
        (substLevelsTm theta (subst substitution.substitution
          (identityEliminateApp input.type input.left input.motive input.method input.left (.refl input.left))))
        (substLevelsTm theta (subst substitution.substitution
          (FormationSensitiveBasedIdentity.methodType input.left input.motive))) ∧
      substLevelsTm theta (subst substitution.substitution
          (identityEliminateApp input.type input.left input.motive input.method input.left (.refl input.left))) =
        subst (fun index => substLevelsTm theta (substitution.substitution index))
          (substLevelsTm theta
            (identityEliminateApp input.type input.left input.motive input.method input.left (.refl input.left))) ∧
      substLevelsTm theta (subst substitution.substitution
          (FormationSensitiveBasedIdentity.methodType input.left input.motive)) =
        subst (fun index => substLevelsTm theta (substitution.substitution index))
          (substLevelsTm theta (FormationSensitiveBasedIdentity.methodType input.left input.motive)) :=
  source_substitution_square theta HOLNativeRelatorCompatibility.opacity
    (FormationSensitiveBasedIdentity.reflexivity_judgment
      (QuotientIdentity.Controls.mixedInput wire).parameters)
    (extend Common.context Common.wireType).formed (projectionHom Common.context Common.wireType).typed

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeIdentityLevelInstantiation
