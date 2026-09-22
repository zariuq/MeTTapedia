import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeIdentityLevelInstantiation

/-!
# Native J in a declaration extension with genuine computation

The extension retains its own declared roots, rather than passing through the
opaque-signature level-instantiation interface. Formation and typed substitution
instantiate the already proved native J schema in that larger environment.
No preservation, normalization or consistency theorem for arbitrary added roots
is asserted here. Those properties require separate qualification of the roots.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeIdentityExtension

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic

variable {n : Nat}

def base (theta : Nat → LevelExpr) : Rules Tower.Head :=
  NativeIdentityLevelInstantiation.rules theta Signature.empty

def rules (theta : Nat → LevelExpr) (signature : Signature Tower.Head) : Rules Tower.Head :=
  extendRules (base theta) signature

variable {theta : Nat → LevelExpr} {signature : Signature Tower.Head}
variable {context : Tower.Ctx n} {type left motive method : Tower.Tm n}

def Parameters (theta : Nat → LevelExpr) (signature : Signature Tower.Head)
    (context : Tower.Ctx n) (type left motive method : Tower.Tm n) : Prop :=
  ContextFormation (rules theta signature) context ∧
    FormationSensitive.CtxMor (rules theta signature)
      (NativeIdentityLevelInstantiation.parametersContext theta) context
      (identitySchemaSubstitution type left motive method)

private theorem includeNative {k : Nat} {source : Tower.Ctx k} {term type : Tower.Tm k}
    (typed : Typing IntrinsicRelator.rules source term type) :
    Typing (rules theta signature) (substLevelsCtx theta source)
      (substLevelsTm theta term) (substLevelsTm theta type) :=
  (((NativeIdentityLevelInstantiation.nativeInstance theta).refinedTyping typed).includeSignature
    (NativeIdentityLevelInstantiation.extensionSignature theta Signature.empty)).includeSignature signature

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

theorem generic_judgment
    (parameters : Parameters theta signature context type left motive method) :
    Judgment (rules theta signature) (FormationSensitiveBasedIdentity.basedContext context type left)
      (FormationSensitiveBasedIdentity.genericTerm type left motive method)
      (FormationSensitiveBasedIdentity.motiveBody motive) := by
  refine ⟨basedContext_formed parameters, ?_⟩
  exact (includeNative generic_schema).substitute
    ((parameters.2.lift (.var 3)).lift (.id (.var 4) (.var 3) (.var 0)))

/-- The datatype motive may use constants and eliminators newly introduced
by the extension. Its formation is checked under those actual rules. -/
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
  have motiveFormation := (includeNative
    FormationSensitiveNativeIdentity.identityMotiveType_hasType).substitute point
  obtain ⟨_, _, _, _, _, innerFormed, innerUniverse, _⟩ := motiveFormation.piFormation
  have motiveTyped : Typing (rules theta signature) context (.lam (.lam body))
      (subst (consSub left (elementSchemaSubstitution type))
        (substLevelsTm theta identityMotiveType)) :=
    .lamIntro motiveFormation (.sort (LevelExpr.subst theta identityMotiveLevel))
      (.lamIntro innerFormed innerUniverse bodyFormed)
  have motive := point.extend motiveTyped
  have methodFormation := (includeNative
    FormationSensitiveNativeIdentity.identityReflCaseType_hasType).substitute motive
  exact motive.extend (.conv methodTyped methodFormation (.sort (theta 1))
    (NativeIdentityLevelInstantiation.abstract_motive_beta (rules theta signature)
      body left (.refl left)).symm)

theorem ofBody_point {right witness : Tower.Tm n}
    (formed : ContextFormation (rules theta signature) context)
    (typeFormed : Typing (rules theta signature) context type (sortTm (theta 0)))
    (leftTyped : Typing (rules theta signature) context left type)
    (body : Tower.Tm (n + 2))
    (bodyFormed : Typing (rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context type left) body (sortTm (theta 1)))
    (methodTyped : Typing (rules theta signature) context method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body))
    (rightTyped : Typing (rules theta signature) context right type)
    (witnessTyped : Typing (rules theta signature) context witness (.id type left right)) :
    Judgment (rules theta signature) context
      (identityEliminateApp type left (.lam (.lam body)) method right witness)
      (subst (FormationSensitiveBasedIdentity.pointSub right witness) body) := by
  have parameters := ofBody formed typeFormed leftTyped body bodyFormed methodTyped
  have identity := FormationSensitiveContextual.identityTyped (rules := rules theta signature) context
  have point : Typing (rules theta signature) context right (subst ids type) := by
    simpa only [subst_ids] using rightTyped
  have actual : FormationSensitive.CtxMor (rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context type left) context
      (FormationSensitiveBasedIdentity.pointSub right witness) := by
    refine (identity.extend point).extend ?_
    simpa only [subst, subst_consSub_rename_wk, subst_ids, consSub_zero] using witnessTyped
  have generic := (generic_judgment parameters).substitute formed actual
  have resultFormed := bodyFormed.substitute actual
  refine ⟨formed, ?_⟩
  exact .conv (by simpa only [FormationSensitiveBasedIdentity.pointSub_genericTerm,
    FormationSensitiveBasedIdentity.pointSub_motiveBody] using generic.typing)
    resultFormed (.sort (theta 1))
    (NativeIdentityLevelInstantiation.abstract_motive_beta _ body right witness)

/-- The inherited native J root is preserved, independently of the new
datatype roots. This does not assert that it is the only possible new root. -/
theorem beta (type left motive method : Tower.Tm n) :
    (rules theta signature).computation.step
      (identityEliminateApp type left motive method left (.refl left)) method :=
  .inherited (NativeIdentityLevelInstantiation.beta theta Signature.empty ..)

/-- A local native proof exports its actual hypothesis as a Pi binder in
the same computational extension. Formation follows from regularity. -/
theorem abstract_judgment {domain : Tower.Tm n} {body result : Tower.Tm (n + 1)}
    (judgment : Judgment (rules theta signature) (.snoc context domain) body result) :
    Judgment (rules theta signature) context (.lam body) (.pi domain result) := by
  obtain ⟨_, resultUniverse, resultFormed⟩ := judgment.regularity
    ((NativeIdentityLevelInstantiation.universes theta Signature.empty).includeSignature signature)
  cases judgment.context with
  | snoc previous domainFormed domainUniverse =>
      cases domainUniverse with
      | sort u =>
          cases resultUniverse with
          | sort v =>
              exact ⟨previous, .lamIntro
                (.piForm domainFormed (.sort u) resultFormed.typing (.sort v) (.sorts u v))
                (.sort (.max u v)) judgment.typing⟩

#print axioms generic_judgment
#print axioms ofBody_point
#print axioms beta
#print axioms abstract_judgment

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeIdentityExtension
