import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticNaturalModel
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ProofRelevantStructuralComputation

/-!
# Judgmental dependent products in the Prime natural model

The syntactic natural model supplies formed contexts, displayed types,
intrinsic terms, and exact context comprehension.  This module equips that
model with dependent products without identifying computation with Lean
equality.

There are three deliberately distinct layers.

* `DependentProduct` records the native formation data for a Pi type.
* `lambda`, `application`, and `instantiateTerm` construct typed terms
  directly.  No checker is invoked between these constructors.
* `betaReceipt` records beta computation as proof-relevant evidence inside
  one judgment fibre.  Its support is the established proposition-valued
  `StepCore`, but the receipt itself is not quotiented away.

`RetainedRoot` relates declaration-specific proof-relevant computation to
the exact root relation installed in a presentation.  Every proposition-
valued presentation has a canonical retained lift, while richer declaration
packages may provide more informative evidence with the same support.

The final Tower canary is intentionally non-extensional: application of the
native identity function to `U0` has a beta receipt to `U0`, although the two
raw terms are not equal.  This is the boundary between a judgmental natural
model and an ordinary equality-based CwF.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace SyntacticJudgmentalPi

open CategoryTheory
open SyntacticContextual
open SyntacticNaturalModel
open Declaration
open ProofRelevantStructuralComputation
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.JudgmentalEquality

universe uEvidence

/-! ## Exact retained support for one presentation -/

/-- A proof-relevant root computation whose inhabitation is exactly the root
relation installed in `rules`.  Equality is required only at the level of
support; the evidence type may retain declaration identity, arguments, and
provenance. -/
structure RetainedRoot (rules : Rules Head) where
  computation : ProofRelevantRootComputation.{uEvidence} Head
  support_iff : ∀ {n : Nat} {left right : Tm Head n},
    rules.computation.step left right ↔
      Nonempty (computation.Evidence left right)

/-- Canonical proof-relevant lift of any proposition-valued root relation.
This lift retains the root proof itself.  Authored calculi may replace it by
a richer receipt type while proving the same support theorem. -/
def RetainedRoot.ofRules (rules : Rules Head) : RetainedRoot rules where
  computation :=
    { Evidence := fun left right => PLift (rules.computation.step left right)
      rename := by
        intro n m rho left right evidence
        exact ⟨rules.computation.rename rho evidence.down⟩
      substitute := by
        intro n m substitution left right evidence
        exact ⟨rules.computation.substitute substitution evidence.down⟩ }
  support_iff := by
    intro n left right
    constructor
    · intro supported
      exact ⟨⟨supported⟩⟩
    · rintro ⟨evidence⟩
      exact evidence.down

/-- Exact support comparison for the complete structural relation, not only
its declaration-specific root case. -/
theorem retained_support_iff_nonempty
    (retained : RetainedRoot.{uEvidence} (Head := Head) rules)
    {left right : Tm Head n} :
    StepCore rules.computation rules.headEq left right ↔
      Nonempty
        (StructuralStepReceipt (Head := Head) (n := n)
          retained.computation rules.headEq left right) := by
  constructor
  · intro supported
    induction supported with
    | betaPi body argument => exact ⟨.betaPi body argument⟩
    | betaSigmaFst first second => exact ⟨.betaSigmaFst first second⟩
    | betaSigmaSnd first second => exact ⟨.betaSigmaSnd first second⟩
    | head equality => exact ⟨.head ⟨equality⟩⟩
    | root rootSupport =>
        rcases retained.support_iff.mp rootSupport with ⟨evidence⟩
        exact ⟨.root evidence⟩
    | congPiDom _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPiDom receipt⟩
    | congPiCod _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPiCod receipt⟩
    | congSigmaDom _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congSigmaDom receipt⟩
    | congSigmaCod _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congSigmaCod receipt⟩
    | congIdTy _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congIdTy receipt⟩
    | congIdLeft _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congIdLeft receipt⟩
    | congIdRight _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congIdRight receipt⟩
    | congLam _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congLam receipt⟩
    | congAppFun _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congAppFun receipt⟩
    | congAppArg _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congAppArg receipt⟩
    | congPairFst _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPairFst receipt⟩
    | congPairSnd _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPairSnd receipt⟩
    | congFst _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congFst receipt⟩
    | congSnd _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congSnd receipt⟩
    | congRefl _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congRefl receipt⟩
  · rintro ⟨receipt⟩
    induction receipt with
    | betaPi body argument => exact .betaPi body argument
    | betaSigmaFst first second => exact .betaSigmaFst first second
    | betaSigmaSnd first second => exact .betaSigmaSnd first second
    | head equality => exact .head equality.down
    | root evidence => exact .root (retained.support_iff.mpr ⟨evidence⟩)
    | congPiDom _ ih => exact .congPiDom ih
    | congPiCod _ ih => exact .congPiCod ih
    | congSigmaDom _ ih => exact .congSigmaDom ih
    | congSigmaCod _ ih => exact .congSigmaCod ih
    | congIdTy _ ih => exact .congIdTy ih
    | congIdLeft _ ih => exact .congIdLeft ih
    | congIdRight _ ih => exact .congIdRight ih
    | congLam _ ih => exact .congLam ih
    | congAppFun _ ih => exact .congAppFun ih
    | congAppArg _ ih => exact .congAppArg ih
    | congPairFst _ ih => exact .congPairFst ih
    | congPairSnd _ ih => exact .congPairSnd ih
    | congFst _ ih => exact .congFst ih
    | congSnd _ ih => exact .congSnd ih
    | congRefl _ ih => exact .congRefl ih

/-! ## Intrinsic dependent-product construction -/

/-- Native formation data for a dependent product.  The domain and codomain
are already formed in the appropriate fibres; this record retains the result
universe selected by the presentation's join discipline. -/
structure DependentProduct {rules : Rules Head}
    {context : FormedContext rules} (domain : TypeOver context)
    (codomain : TypeOver (extendContext context domain)) where
  level : Head
  isUniverse : rules.isUniverse level
  join : rules.join domain.level codomain.level level

namespace DependentProduct

/-- The formed Pi type constructed by native formation evidence. -/
def type {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain) : TypeOver context where
  code := .pi domain.code codomain.code
  level := product.level
  isUniverse := product.isUniverse
  formed := .piForm domain.formed domain.isUniverse codomain.formed
    codomain.isUniverse product.join

/-- A native lambda is constructed directly from its body judgment. -/
def lambda {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain)
    (body : Term (extendContext context domain) codomain) :
    Term context product.type where
  code := .lam body.code
  typed := .lamIntro body.typed

end DependentProduct

/-- Substitute one intrinsic argument into a context extension. -/
def argumentSection {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context} (argument : Term context domain) :
    context ⟶ extendContext context domain where
  substitution := subst0 argument.code
  typed := by
    change CtxMor rules (.snoc context.context domain.code) context.context
      (subst0 argument.code)
    have paired := CtxMor.extend
      (CtxMor.identity rules context.context)
      (Term.cast (TypeOver.reindex_id domain).symm argument).typed
    have sameSubstitution :
        consSub argument.code (ids (Head := Head) (n := context.arity)) =
          subst0 argument.code := by
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro prior
        rfl
    rw [← sameSubstitution]
    simpa only [Term.cast_code] using paired

/-- The direct opening section is exactly comprehension pairing with the
identity substitution. -/
theorem argumentSection_eq_extendHom
    {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context} (argument : Term context domain) :
    argumentSection argument =
      extendHom (𝟙 context)
        (Term.cast (TypeOver.reindex_id domain).symm argument) := by
  apply ContextHom.ext
  change subst0 argument.code =
    consSub (Term.cast (TypeOver.reindex_id domain).symm argument).code ids
  rw [Term.cast_code]
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

/-- The raw substitution underlying the intrinsic argument section is the
standard one-variable opening substitution. -/
theorem argumentSection_substitution
    {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context} (argument : Term context domain) :
    (argumentSection argument).substitution = subst0 argument.code :=
  rfl

/-! ## Stability under context substitution -/

/-- Lift a context substitution under one native context extension.  The
newest variable is paired with the weakened base substitution, so this is the
categorical form of `liftSub`. -/
def liftContextHom {rules : Rules Head}
    {source target : FormedContext rules}
    (morphism : source ⟶ target) (type : TypeOver target) :
    extendContext source (type.reindex morphism) ⟶
      extendContext target type :=
  extendHom (projectionHom source (type.reindex morphism) ≫ morphism)
    (Term.cast
      (TypeOver.reindex_comp type
        (projectionHom source (type.reindex morphism)) morphism).symm
      (newestVariable source (type.reindex morphism)))

/-- The categorical lifted context morphism erases exactly to the ordinary
de Bruijn lifted substitution. -/
theorem liftContextHom_substitution {rules : Rules Head}
    {source target : FormedContext rules}
    (morphism : source ⟶ target) (type : TypeOver target) :
    (liftContextHom morphism type).substitution =
      liftSub morphism.substitution := by
  funext index
  refine Fin.cases ?_ ?_ index
  · simp only [liftContextHom, extendHom, consSub_zero, Term.cast_code,
      newestVariable]
    congr 1
  · intro prior
    simp only [liftContextHom, extendHom, consSub_succ, liftSub_succ]
    change subst projection (morphism.substitution prior) =
      rename wk (morphism.substitution prior)
    exact subst_projection (morphism.substitution prior)

/-- Opening a displayed type through the intrinsic argument section is
exactly ordinary de Bruijn instantiation. -/
@[simp] theorem reindex_argumentSection_code
    {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    (codomain : TypeOver (extendContext context domain))
    (argument : Term context domain) :
    (codomain.reindex (argumentSection argument)).code =
      inst0 argument.code codomain.code := by
  change subst (argumentSection argument).substitution codomain.code = _
  rw [argumentSection_substitution]
  rfl

/-- The result type of dependent application. -/
def instantiateType {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    (codomain : TypeOver (extendContext context domain))
    (argument : Term context domain) : TypeOver context :=
  codomain.reindex (argumentSection argument)

/-- Substitute an argument into a term in the extended context.  The output
code is presented canonically as `inst0`, while its typing comes from the
typed context substitution. -/
def instantiateTerm {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (body : Term (extendContext context domain) codomain)
    (argument : Term context domain) :
    Term context (instantiateType codomain argument) where
  code := inst0 argument.code body.code
  typed := by
    have reindexed := body.typed.substitute (argumentSection argument).typed
    exact reindexed

/-- Canonical instantiation agrees exactly with reindexing through context
comprehension.  No term or typing evidence is reconstructed by a checker. -/
theorem instantiateTerm_eq_reindex
    {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (body : Term (extendContext context domain) codomain)
    (argument : Term context domain) :
    instantiateTerm body argument =
      body.reindex (argumentSection argument) := by
  apply Term.ext
  rfl

/-- Native dependent application constructs the correct instantiated result
type directly. -/
def DependentProduct.application
    {rules : Rules Head} {context : FormedContext rules}
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain)
    (function : Term context product.type)
    (argument : Term context domain) :
    Term context (instantiateType codomain argument) where
  code := .app function.code argument.code
  typed := by
    simpa only [instantiateType, reindex_argumentSection_code] using
      (HasType.appElim function.typed argument.typed)

/-- Reindex native Pi-formation data along a typed context substitution. -/
def DependentProduct.reindex
    {rules : Rules Head} {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    DependentProduct (domain.reindex morphism)
      (codomain.reindex (liftContextHom morphism domain)) where
  level := product.level
  isUniverse := product.isUniverse
  join := product.join

/-- Pi formation commutes strictly with reindexing up to equality of the
retained formed-type records. -/
theorem DependentProduct.type_reindex
    {rules : Rules Head} {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (morphism : source ⟶ target) :
    product.type.reindex morphism = (product.reindex morphism).type := by
  apply TypeOver.ext
  · change
      subst morphism.substitution (.pi domain.code codomain.code) =
        .pi (subst morphism.substitution domain.code)
          (subst (liftContextHom morphism domain).substitution codomain.code)
    simp only [Presentation.subst, liftContextHom_substitution]
    rfl
  · rfl

/-- Lambda construction commutes with reindexing.  The cast changes only the
formed-type index established by `type_reindex`; the raw lambda and body are
transported by the ordinary lifted substitution. -/
theorem DependentProduct.lambda_reindex
    {rules : Rules Head} {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (body : Term (extendContext target domain) codomain)
    (morphism : source ⟶ target) :
    Term.cast (product.type_reindex morphism)
        ((product.lambda body).reindex morphism) =
      (product.reindex morphism).lambda
        (body.reindex (liftContextHom morphism domain)) := by
  apply Term.ext
  rw [Term.cast_code]
  change
    subst morphism.substitution (.lam body.code) =
      .lam (subst (liftContextHom morphism domain).substitution body.code)
  simp only [Presentation.subst, liftContextHom_substitution]
  rfl

/-- Instantiating a displayed result type commutes with substitution in the
ambient context.  This is the Beck--Chevalley law for dependent application:
first open the codomain and then reindex, or first lift the context
substitution under the binder and then open it, with the same result. -/
theorem instantiateType_reindex
    {rules : Rules Head} {source target : FormedContext rules}
    {domain : TypeOver target}
    (codomain : TypeOver (extendContext target domain))
    (argument : Term target domain)
    (morphism : source ⟶ target) :
    (instantiateType codomain argument).reindex morphism =
      instantiateType
        (codomain.reindex (liftContextHom morphism domain))
        (argument.reindex morphism) := by
  apply TypeOver.ext
  · change
      subst morphism.substitution (inst0 argument.code codomain.code) =
        inst0 (subst morphism.substitution argument.code)
          (subst (liftContextHom morphism domain).substitution codomain.code)
    rw [liftContextHom_substitution]
    exact subst_inst0 morphism.substitution argument.code codomain.code
  · rfl

/-- Native dependent application is stable under arbitrary typed context
substitution.  The two casts expose only the equalities of formed fibres;
the retained application syntax is transported structurally and no typing
judgment is replayed. -/
theorem DependentProduct.application_reindex
    {rules : Rules Head} {source target : FormedContext rules}
    {domain : TypeOver target}
    {codomain : TypeOver (extendContext target domain)}
    (product : DependentProduct domain codomain)
    (function : Term target product.type)
    (argument : Term target domain)
    (morphism : source ⟶ target) :
    Term.cast (instantiateType_reindex codomain argument morphism)
        ((product.application function argument).reindex morphism) =
      (product.reindex morphism).application
        (Term.cast (product.type_reindex morphism)
          (function.reindex morphism))
        (argument.reindex morphism) := by
  apply Term.ext
  simp only [Term.cast_code, DependentProduct.application, Term.reindex,
    Presentation.subst]

/-! ## Judgment-indexed structural computation -/

/-- In one formed context, the judgment indices are its formed types and the
states in each fibre are the intrinsic terms of that type. -/
def termComputation (retained : RetainedRoot.{uEvidence} rules)
    (context : FormedContext rules) :
    JudgmentalComputation (TypeOver context) where
  State := fun type => Term context type
  Step := fun source target =>
    StructuralStepReceipt retained.computation rules.headEq
      source.code target.code

/-- The proof-relevant beta step between natively constructed endpoints. -/
def DependentProduct.betaReceipt
    {rules : Rules Head} {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain)
    (body : Term (extendContext context domain) codomain)
    (argument : Term context domain) :
    (termComputation retained context).Step
      (product.application (product.lambda body) argument)
      (instantiateTerm body argument) :=
  .betaPi body.code argument.code

/-- Beta conversion retains the exact structural receipt rather than
asserting equality of its endpoint syntax. -/
def DependentProduct.betaConversion
    {rules : Rules Head} {context : FormedContext rules}
    (retained : RetainedRoot.{uEvidence} rules)
    {domain : TypeOver context}
    {codomain : TypeOver (extendContext context domain)}
    (product : DependentProduct domain codomain)
    (body : Term (extendContext context domain) codomain)
    (argument : Term context domain) :
    ConversionEvidence (termComputation retained context)
      (product.application (product.lambda body) argument)
      (instantiateTerm body argument) :=
  .step (product.betaReceipt retained body argument)

/-! ## Tower positive and negative controls -/

namespace TowerExamples

open SyntacticContextual.TowerExamples

private abbrev levelOne : LevelExpr := .succ Tower.zero
private abbrev levelTwo : LevelExpr := .succ levelOne
private abbrev levelThree : LevelExpr := .succ levelTwo

/-- The dependent constant family `U1` over one `U1` variable. -/
def identityCodomain : TypeOver (extendContext empty universeOne) :=
  universeOne.reindex (projectionHom empty universeOne)

/-- Native formation of `(x : U1) -> U1`, retaining its exact maximum
universe expression. -/
def identityProduct : DependentProduct universeOne identityCodomain where
  level := .sort (.max levelTwo levelTwo)
  isUniverse := .sort (.max levelTwo levelTwo)
  join := .sorts levelTwo levelTwo

/-- The native variable body of the polymorphic identity function. -/
def identityBody : Term (extendContext empty universeOne) identityCodomain :=
  newestVariable empty universeOne

/-- Direct native construction of the identity lambda. -/
def identityFunction : Term empty identityProduct.type :=
  identityProduct.lambda identityBody

/-- Direct native application of identity to the universe `U0`. -/
def identityApplication :
    Term empty (instantiateType identityCodomain universeZero) :=
  identityProduct.application identityFunction universeZero

/-- The canonically instantiated beta target. -/
def identityBetaTarget :
    Term empty (instantiateType identityCodomain universeZero) :=
  instantiateTerm identityBody universeZero

/-- The Tower presentation's root relation lifted without inventing any
declaration-specific witness. -/
def retainedTower : RetainedRoot Tower.rules :=
  RetainedRoot.ofRules Tower.rules

/-- Positive control: native identity application carries a proof-relevant
beta conversion to its target. -/
def identityBetaConversion :
    ConversionEvidence (termComputation retainedTower empty)
      identityApplication identityBetaTarget :=
  identityProduct.betaConversion retainedTower identityBody universeZero

@[simp] theorem identityBetaTarget_code :
    identityBetaTarget.code = universeZero.code := by
  rfl

/-- Negative control: beta conversion is genuinely judgmental.  Its source
and target are not equal raw syntax, so an equality-based model would have to
quotient away precisely the computation receipt retained above. -/
theorem identityApplication_code_ne_target :
    identityApplication.code ≠ identityBetaTarget.code := by
  rw [identityBetaTarget_code]
  change
    Tm.app (Tm.lam (newestVariable empty universeOne).code)
        (sortTm Tower.zero) ≠
      sortTm Tower.zero
  intro equality
  cases equality

/-- `U2` as a formed type over the same empty Tower context. -/
def universeTwo : TypeOver empty where
  code := sortTm levelTwo
  level := .sort levelThree
  isUniverse := .sort levelThree
  formed := .headType (.sort levelTwo)

/-- `U1` is a term of `U2`. -/
def universeOneTerm : Term empty universeTwo where
  code := sortTm levelOne
  typed := .headType (.sort levelOne)

theorem universeOne_ne_universeTwo : universeOne ≠ universeTwo := by
  intro equality
  have codeEquality := congrArg TypeOver.code equality
  have headEquality := Tm.head.inj codeEquality
  have levelEquality := Tower.Head.sort.inj headEquality
  cases levelEquality

/-- Negative control: judgmental conversion cannot cross distinct type
fibres even when both states inhabit the same formed context. -/
theorem no_conversion_across_universe_fibres :
    IsEmpty
      (TotalConversion (termComputation retainedTower empty)
        ⟨universeOne, universeZero⟩ ⟨universeTwo, universeOneTerm⟩) := by
  constructor
  intro conversion
  exact universeOne_ne_universeTwo conversion.indexEquality

end TowerExamples

/-! ## Axiom audit -/

#print axioms RetainedRoot.ofRules
#print axioms retained_support_iff_nonempty
#print axioms DependentProduct.type
#print axioms DependentProduct.lambda
#print axioms argumentSection_eq_extendHom
#print axioms liftContextHom_substitution
#print axioms reindex_argumentSection_code
#print axioms instantiateTerm
#print axioms instantiateTerm_eq_reindex
#print axioms DependentProduct.application
#print axioms DependentProduct.type_reindex
#print axioms DependentProduct.lambda_reindex
#print axioms instantiateType_reindex
#print axioms DependentProduct.application_reindex
#print axioms DependentProduct.betaReceipt
#print axioms DependentProduct.betaConversion
#print axioms TowerExamples.identityBetaConversion
#print axioms TowerExamples.identityApplication_code_ne_target
#print axioms TowerExamples.no_conversion_across_universe_fibres

end SyntacticJudgmentalPi
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
