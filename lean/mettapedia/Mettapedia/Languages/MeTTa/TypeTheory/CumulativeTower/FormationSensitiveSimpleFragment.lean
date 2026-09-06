import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PureConversion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentConversionDecision

/-!
# The existing simple fragment in formation-sensitive Tower typing

The existing intrinsic atom/arrow syntax translates with its existing type,
context, term and substitution maps. Formation-sensitive derivations supply
every retained universe premise, including the function type at lambda
introduction. Translated contexts are formed by the same refined judgment.

Substituting before translation and translating before refined substitution
give the identical raw term, with derivations along both routes. The existing
conversion comparison still applies because neither conversion nor syntax
has changed. This is not a full HOL interpretation, inhabitation reflection,
or adoption of the candidate refinement as a global profile. No normalization
hypothesis on the Tower is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveSimpleFragment

open Presentation Presentation.FormationSensitive
open FourFaceBetaExperiment FourFaceBetaExperiment.IntrinsicSTT
open FourFaceBetaExperiment.TowerDTT SimpleFragmentSubstitutionTranslation

variable {Γ Δ : List Ty} {A B : Ty}

/-- The same translated simple type is formed by the refined rules over any
raw context; its universe level is the existing `levelOf` expression. -/
theorem eraseTypeAt_formed (type : Ty) {arity : Nat} (context : Tower.Ctx arity) :
    Typing Tower.rules context (eraseTypeAt arity type) (sortTm (levelOf type)) := by
  induction type generalizing arity with
  | atom => exact .headType .legacyGround
  | arr domain codomain domainIH codomainIH =>
      exact .piForm (domainIH context) (.sort (levelOf domain))
        (codomainIH (.snoc context (eraseTypeAt arity domain)))
        (.sort (levelOf codomain)) (.sorts (levelOf domain) (levelOf codomain))

/-- Every entry of the existing translated telescope is independently formed. -/
theorem eraseContext_formed (context : List Ty) :
    ContextFormation Tower.rules (eraseContext context) := by
  induction context with
  | nil => exact .nil
  | cons head tail ih =>
      exact .snoc ih (eraseTypeAt_formed head (eraseContext tail)) (.sort (levelOf head))

/-- Intrinsic simple derivations construct genuine formation-sensitive
derivations of the unchanged translated term and displayed type. -/
theorem eraseTerm_typed (term : Term Γ A) :
    Typing Tower.rules (eraseContext Γ) (eraseTerm term) (eraseTypeAt Γ.length A) := by
  induction term with
  | var typedVar =>
      simpa only [eraseTerm, lookup_eraseContext] using
        (Typing.var (R := Tower.rules) (Γ := eraseContext _) (eraseVar typedVar))
  | @lam domain context codomain body ih =>
      exact .lamIntro (eraseTypeAt_formed (.arr domain codomain) (eraseContext context))
        (.sort (levelOf (.arr domain codomain))) ih
  | app function argument functionIH argumentIH =>
      have application := Typing.appElim functionIH argumentIH
      simpa only [eraseTerm, eraseTypeAt, inst0, eraseTypeAt_subst] using application

/-- The term translation carries both its refined typing and formed context. -/
theorem eraseTerm_judgment (term : Term Γ A) :
    Judgment Tower.rules (eraseContext Γ) (eraseTerm term) (eraseTypeAt Γ.length A) :=
  ⟨eraseContext_formed Γ, eraseTerm_typed term⟩

/-- The existing raw substitution map is admitted by the refined typing
relation, rather than merely by the older raw relation. -/
theorem eraseSubstitution_typed (substitution : Substitution Γ Δ) :
    FormationSensitive.CtxMor Tower.rules (eraseContext Γ) (eraseContext Δ)
      (eraseSubstitution substitution) := by
  intro index
  have typed := eraseTerm_typed (substitution (typedVarAt Γ index))
  have lookup := lookup_eraseContext (typedVarAt Γ index)
  rw [eraseVar_typedVarAt] at lookup
  change Typing Tower.rules (eraseContext Δ) (eraseSubstitution substitution index)
    (Presentation.subst (eraseSubstitution substitution) ((eraseContext Γ).lookup index))
  rw [lookup, eraseTypeAt_subst]
  simpa only [← eraseSubstitution_apply, eraseVar_typedVarAt] using typed

/-- Translate a source-substituted intrinsic derivation, or substitute its
translation using the refined structural theorem. Both yield formed judgments
and the exact same raw syntax. No proof-irrelevance equality of derivations
is used as a substitute for this term-level comparison. -/
theorem substitution_routes (substitution : Substitution Γ Δ) (term : Term Γ A) :
    Judgment Tower.rules (eraseContext Δ) (eraseTerm (term.substitute substitution))
      (eraseTypeAt Δ.length A) ∧
    Judgment Tower.rules (eraseContext Δ)
      (Presentation.subst (eraseSubstitution substitution) (eraseTerm term))
      (eraseTypeAt Δ.length A) ∧
    eraseTerm (term.substitute substitution) =
      Presentation.subst (eraseSubstitution substitution) (eraseTerm term) := by
  refine ⟨eraseTerm_judgment _, ⟨eraseContext_formed Δ, ?_⟩,
    eraseTerm_substitute substitution term⟩
  simpa only [eraseTypeAt_subst] using
    (eraseTerm_typed term).substitute (eraseSubstitution_typed substitution)

/-- Every existing intrinsic beta claim becomes an actual root step between
formed judgments; target typing is obtained by the proved Tower beta theorem. -/
theorem betaClaim_formed (claim : BetaClaim Γ A B) :
    Step Tower.HeadEq (eraseTerm claim.source) (eraseTerm claim.target) ∧
      Judgment Tower.rules (eraseContext Γ) (eraseTerm claim.source)
        (eraseTypeAt Γ.length B) ∧
      Judgment Tower.rules (eraseContext Γ) (eraseTerm claim.target)
        (eraseTypeAt Γ.length B) := by
  have source := eraseTerm_judgment claim.source
  have target := source.betaPi_tower
  refine ⟨(betaClaim_typed claim).1, source, ?_⟩
  simpa only [BetaClaim.source, BetaClaim.target, eraseTerm,
    eraseTerm_instantiateNewest] using target

/-- The previously established exact conversion comparison now has refined
endpoint judgments. It concerns terms already in the simple image, not all
Tower inhabitants at a translated type. -/
theorem conversion_on_image (left right : Term Γ A) :
    Judgment Tower.rules (eraseContext Γ) (eraseTerm left) (eraseTypeAt Γ.length A) ∧
      Judgment Tower.rules (eraseContext Γ) (eraseTerm right) (eraseTypeAt Γ.length A) ∧
      (Conv Tower.HeadEq (eraseTerm left) (eraseTerm right) ↔ BetaConv left right) :=
  ⟨eraseTerm_judgment left, eraseTerm_judgment right,
    SimpleFragmentConversionDecision.towerConv_iff_betaConv left right⟩

namespace Examples

abbrev endomorphism : Ty := .arr .atom .atom

/-- The body of the higher-order iterator `fun f => fun x => f (f x)`. -/
def twiceBody : Term (endomorphism :: Γ) endomorphism :=
  .lam (.app (.var (.succ .zero)) (.app (.var (.succ .zero)) (.var .zero)))

/-- A function-valued argument retaining an older free function. -/
def functionArgument : Term [endomorphism] endomorphism :=
  .lam (.app (.var (.succ .zero)) (.var .zero))

/-- The independently written capture-avoiding specialization. The older
function is two binders away inside each supplied lambda. -/
def specialized : Term [endomorphism] endomorphism :=
  .lam (.app
    (.lam (.app (.var (.succ (.succ .zero))) (.var .zero)))
    (.app (.lam (.app (.var (.succ (.succ .zero))) (.var .zero))) (.var .zero)))

theorem higher_order_substitution :
    (twiceBody (Γ := [endomorphism])).instantiateNewest functionArgument = specialized := by
  rfl

/-- Both genuine substitution routes retain the same higher-order result,
with formation-sensitive endpoint evidence and explicit syntax equality. -/
theorem higher_order_substitution_routes :
    Judgment Tower.rules (eraseContext [endomorphism]) (eraseTerm specialized)
      (eraseTypeAt 1 endomorphism) ∧
      Judgment Tower.rules (eraseContext [endomorphism])
        (Presentation.subst (eraseSubstitution (newestSubstitution functionArgument))
          (eraseTerm (twiceBody (Γ := [endomorphism])))) (eraseTypeAt 1 endomorphism) ∧
      eraseTerm specialized =
        Presentation.subst (eraseSubstitution (newestSubstitution functionArgument))
          (eraseTerm (twiceBody (Γ := [endomorphism]))) := by
  have computed : (twiceBody (Γ := [endomorphism])).substitute
      (newestSubstitution functionArgument) = specialized := higher_order_substitution
  simpa only [computed, List.length_cons, List.length_nil] using
    substitution_routes (newestSubstitution functionArgument) (twiceBody (Γ := [endomorphism]))

/-- The corresponding application is a real higher-order beta instance. -/
theorem higher_order_beta :
    Step Tower.HeadEq
      (eraseTerm (.app (.lam (twiceBody (Γ := [endomorphism]))) functionArgument))
      (eraseTerm specialized) ∧
      Judgment Tower.rules (eraseContext [endomorphism])
        (eraseTerm specialized) (eraseTypeAt 1 endomorphism) := by
  have claim := betaClaim_formed
    (show BetaClaim [endomorphism] endomorphism endomorphism from
      ⟨twiceBody, functionArgument⟩)
  simpa only [BetaClaim.source, BetaClaim.target, higher_order_substitution,
    List.length_cons, List.length_nil] using
    And.intro claim.1 claim.2.2

/-- Refining target typing does not recover erased application-domain
annotations: these two different source derivations still have identical
raw images, and both images have formed target judgments. -/
theorem refinement_does_not_restore_intrinsic_syntax :
    SimpleFragmentErasureBoundary.discardAtomicIdentity ≠
      SimpleFragmentErasureBoundary.discardFunctionIdentity ∧
      eraseTerm SimpleFragmentErasureBoundary.discardAtomicIdentity =
        eraseTerm SimpleFragmentErasureBoundary.discardFunctionIdentity ∧
      Judgment Tower.rules .nil
        (eraseTerm SimpleFragmentErasureBoundary.discardAtomicIdentity)
        (eraseTypeAt 0 endomorphism) ∧
      Judgment Tower.rules .nil
        (eraseTerm SimpleFragmentErasureBoundary.discardFunctionIdentity)
        (eraseTypeAt 0 endomorphism) :=
  ⟨SimpleFragmentErasureBoundary.discardIdentities_ne,
    SimpleFragmentErasureBoundary.erase_discardIdentities_eq,
    eraseTerm_judgment SimpleFragmentErasureBoundary.discardAtomicIdentity,
    eraseTerm_judgment SimpleFragmentErasureBoundary.discardFunctionIdentity⟩

end Examples

#print axioms eraseTypeAt_formed
#print axioms eraseContext_formed
#print axioms eraseTerm_typed
#print axioms eraseSubstitution_typed
#print axioms substitution_routes
#print axioms betaClaim_formed
#print axioms conversion_on_image
#print axioms Examples.higher_order_substitution_routes
#print axioms Examples.higher_order_beta
#print axioms Examples.refinement_does_not_restore_intrinsic_syntax

end FormationSensitiveSimpleFragment
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
