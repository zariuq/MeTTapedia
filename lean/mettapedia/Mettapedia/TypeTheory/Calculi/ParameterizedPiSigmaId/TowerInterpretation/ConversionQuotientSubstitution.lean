import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ConversionQuotient

/-!
# Actual contextual substitution of the model quotient

An independently admitted annotated substitution acts on satisfying
environments by evaluating its actual components. The interpretation of
the formed source conversion classes commutes with that map when the
components erase to the supplied raw contextual arrow. Identity, composition
and passage under a genuine dependent binder use the existing simultaneous
substitution, rather than an assumed semantic action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace ConversionQuotient

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization
open Presentation.FormationSensitiveContextual
open CategoryTheory
open UniverseLevel (LevelOrder)

universe u

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}
variable {P : ChurchRules S.R} {heads : Head → ZFSet.{u}} {constants : DeclName → ZFSet.{u}}
variable (model : SetModel heads constants P)

noncomputable def substitutionEnvironment {n m : Nat} {source : CCtx Head n}
    {target : CCtx Head m} {substitution : CSub Head m n}
    (typed : CSubstMor P target source substitution)
    (environment : Environment (heads := heads) (constants := constants) source) :
    Environment (heads := heads) (constants := constants) target :=
  ⟨fun index => ev heads constants (substitution index) environment.val, fun index => by
    have member := (CDerivable.sound model (typed index)) environment.val environment.property
    rw [ev_subst] at member
    exact member⟩

@[simp] theorem substitutionEnvironment_val {n m : Nat} {source : CCtx Head n}
    {target : CCtx Head m} {substitution : CSub Head m n}
    (typed : CSubstMor P target source substitution)
    (environment : Environment (heads := heads) (constants := constants) source) :
    (substitutionEnvironment model typed environment).val =
      fun index => ev heads constants (substitution index) environment.val := rfl

/-- The actual identity substitution acts as the identity environment map. -/
theorem substitutionEnvironment_identity {n : Nat} {context : CCtx Head n}
    (typed : CSubstMor P context context CTm.ids)
    (environment : Environment (heads := heads) (constants := constants) context) :
    substitutionEnvironment model typed environment = environment := by
  apply Subtype.ext
  rfl

/-- Composition is proved by the evaluator's simultaneous substitution law. -/
theorem substitutionEnvironment_composition {n m k : Nat}
    {first : CCtx Head n} {middle : CCtx Head m} {last : CCtx Head k}
    {earlier : CSub Head m n} {later : CSub Head k m}
    (earlierTyped : CSubstMor P middle first earlier)
    (laterTyped : CSubstMor P last middle later)
    (compositeTyped : CSubstMor P last first (fun index => (later index).subst earlier))
    (environment : Environment (heads := heads) (constants := constants) first) :
    substitutionEnvironment model compositeTyped environment =
      substitutionEnvironment model laterTyped
        (substitutionEnvironment model earlierTyped environment) := by
  apply Subtype.ext
  funext index
  exact ev_subst heads constants earlier (later index) environment.val

noncomputable def extendEnvironment {n : Nat} {context : CCtx Head n}
    (environment : Environment (heads := heads) (constants := constants) context)
    (type : CTm Head n) (value : ZFSet.{u})
    (member : value ∈ ev heads constants type environment.val) :
    Environment (heads := heads) (constants := constants) (.snoc context type) :=
  ⟨extend environment.val value, (sat_snoc heads constants).mpr ⟨environment.property, member⟩⟩

/-- Passage under a dependent binder preserves the new bound value while
evaluating the supplied outer substitution. -/
theorem substitutionEnvironment_binder {n m : Nat} {source : CCtx Head n}
    {target : CCtx Head m} {substitution : CSub Head m n}
    (typed : CSubstMor P target source substitution)
    (environment : Environment (heads := heads) (constants := constants) source)
    (type : CTm Head m) (value : ZFSet.{u})
    (member : value ∈ ev heads constants (type.subst substitution) environment.val) :
    (substitutionEnvironment model (typed.lift type)
        (extendEnvironment environment (type.subst substitution) value member)).val =
      extend (substitutionEnvironment model typed environment).val value :=
  ev_liftSub heads constants substitution environment.val value

variable (lifting : LiftingFacts P) (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (headPreserving : HeadPreserving S.R)
  (church : ConversionCoherence.ChurchRosser S.R)
variable {first last : Context S.R}
  {sourceContext : CCtx Head first.arity} {targetContext : CCtx Head last.arity}
  (sourceFormed : CCtxFormed P sourceContext) (sourceErases : sourceContext.erase = first.raw)
  (targetFormed : CCtxFormed P targetContext) (targetErases : targetContext.erase = last.raw)
  (arrow : first ⟶ last) {substitution : CSub Head last.arity first.arity}
  (typed : CSubstMor P targetContext sourceContext substitution)
  (componentsErase : ∀ index, (substitution index).erase = arrow.substitution index)
include componentsErase

/-- The interpreted set of a reindexed formed type is the original set
evaluated in the actual substituted environment. -/
theorem typeValue_reindex (type : TypeOver last)
    (environment : Environment (heads := heads) (constants := constants) sourceContext) :
    typeValue lifting facts roots headPreserving church sourceFormed sourceErases
        (type.reindex arrow) environment =
      typeValue lifting facts roots headPreserving church targetFormed targetErases type
        (substitutionEnvironment model typed environment) := by
  let chosen := typeAnnotation lifting facts roots headPreserving church targetFormed targetErases type
  have codeErases : (chosen.code.subst substitution).erase = (type.reindex arrow).code := by
    rw [CTm.erase_subst, chosen.erases]
    exact subst_ext (fun index => componentsErase index) type.code
  rw [typeValue_annotation lifting model facts roots headPreserving church
      sourceFormed sourceErases (type.reindex arrow)
      ⟨type.level, type.universeWitness, chosen.typed.substitute typed⟩ codeErases]
  exact ev_subst heads constants substitution chosen.code environment.val

/-- The supplied term, including a lambda or dependent pair, commutes with
the same actual contextual substitution. -/
theorem termValue_reindex {type : TypeOver last} (term : Term last type)
    (environment : Environment (heads := heads) (constants := constants) sourceContext) :
    termValue lifting facts roots headPreserving church sourceFormed sourceErases
        (term.reindex arrow) environment =
      termValue lifting facts roots headPreserving church targetFormed targetErases term
        (substitutionEnvironment model typed environment) := by
  let chosen := termAnnotation lifting facts roots headPreserving church targetFormed targetErases term
  have codeErases : (chosen.code.subst substitution).erase = (term.reindex arrow).code := by
    rw [CTm.erase_subst, chosen.erases]
    exact subst_ext (fun index => componentsErase index) term.code
  have typeErases : (chosen.typeCode.subst substitution).erase = (type.reindex arrow).code := by
    rw [CTm.erase_subst, chosen.typeErases]
    exact subst_ext (fun index => componentsErase index) type.code
  rw [termValue_annotation lifting model facts roots headPreserving church sourceFormed sourceErases
      (term.reindex arrow) (chosen.typed.substitute typed) codeErases typeErases]
  exact ev_subst heads constants substitution chosen.code environment.val

theorem quotientTypeValue_reindex (type : QType last)
    (environment : Environment (heads := heads) (constants := constants) sourceContext) :
    quotientTypeValue lifting model facts roots headPreserving church sourceFormed sourceErases
        (type.reindex arrow) environment =
      quotientTypeValue lifting model facts roots headPreserving church targetFormed targetErases type
        (substitutionEnvironment model typed environment) := by
  induction type using Quotient.inductionOn with
  | h type =>
      exact typeValue_reindex model lifting facts roots headPreserving church
        sourceFormed sourceErases targetFormed targetErases arrow typed componentsErase type environment

theorem quotientTermValue_reindex (term : QTerm last)
    (environment : Environment (heads := heads) (constants := constants) sourceContext) :
    quotientTermValue lifting model facts roots headPreserving church sourceFormed sourceErases
        (term.reindex arrow) environment =
      quotientTermValue lifting model facts roots headPreserving church targetFormed targetErases term
        (substitutionEnvironment model typed environment) := by
  induction term using Quotient.inductionOn with
  | h pair =>
      exact termValue_reindex model lifting facts roots headPreserving church
        sourceFormed sourceErases targetFormed targetErases arrow typed componentsErase pair.2 environment

end ConversionQuotient
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
