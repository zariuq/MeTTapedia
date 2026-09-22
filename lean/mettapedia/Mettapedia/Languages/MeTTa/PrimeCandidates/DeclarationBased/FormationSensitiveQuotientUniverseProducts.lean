import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverses
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProducts

/-!
# Universe closure for the same native products and sums

The cumulative hierarchy and dependent operations inhabit the very same
formed quotient CwF. Their connection uses the supplied domain and codomain
level admissions, including native transport across the chosen binder
representative. It does not use the incidental levels of chosen quotient
representatives to guess a universe for the result.

Mixed-level codes decode to the actual product/sum operations. Each fixed
level is consequently closed under those operations, whose beta and
substitution laws have already been proved on this same CwF. This remains
a syntactic constructor model, not an external set/presheaf interpretation
or a runtime code generator.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientUniverseProducts

open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open QuotientUniverses

noncomputable section

variable {signature : Declaration.Signature Tower.Head}

theorem code_membership {context : NativeContext signature} {level : LevelExpr}
    (code : Code context level) : (decode code).AtUniverse (.sort level) :=
  (code_exists_iff_atUniverse level (decode code)).mp ⟨code, rfl⟩

def piCode {context : NativeContext signature} {lower upper : LevelExpr}
    (domain : Code context lower)
    (codomain : Code (QuotientCwf.ext context (decode domain)) upper) :
    Code context (.max lower upper) :=
  Classical.choose ((code_exists_iff_atUniverse (.max lower upper)
    (QuotientProducts.pi (decode domain) (decode codomain))).mpr
      (QuotientProducts.pi_atUniverse (code_membership domain) (code_membership codomain)))

theorem decode_piCode {context : NativeContext signature} {lower upper : LevelExpr}
    (domain : Code context lower)
    (codomain : Code (QuotientCwf.ext context (decode domain)) upper) :
    decode (piCode domain codomain) = QuotientProducts.pi (decode domain) (decode codomain) :=
  Classical.choose_spec ((code_exists_iff_atUniverse (.max lower upper)
    (QuotientProducts.pi (decode domain) (decode codomain))).mpr
      (QuotientProducts.pi_atUniverse (code_membership domain) (code_membership codomain)))

def sigmaCode {context : NativeContext signature} {lower upper : LevelExpr}
    (domain : Code context lower)
    (codomain : Code (QuotientCwf.ext context (decode domain)) upper) :
    Code context (.max lower upper) :=
  Classical.choose ((code_exists_iff_atUniverse (.max lower upper)
    (QuotientProducts.sigma (decode domain) (decode codomain))).mpr
      (QuotientProducts.sigma_atUniverse (code_membership domain) (code_membership codomain)))

theorem decode_sigmaCode {context : NativeContext signature} {lower upper : LevelExpr}
    (domain : Code context lower)
    (codomain : Code (QuotientCwf.ext context (decode domain)) upper) :
    decode (sigmaCode domain codomain) = QuotientProducts.sigma (decode domain) (decode codomain) :=
  Classical.choose_spec ((code_exists_iff_atUniverse (.max lower upper)
    (QuotientProducts.sigma (decode domain) (decode codomain))).mpr
      (QuotientProducts.sigma_atUniverse (code_membership domain) (code_membership codomain)))

def betaProducts (signature : Declaration.Signature Tower.Head) :
    DependentProductBeta (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) where
  pi := QuotientProducts.pi
  lam := QuotientProducts.lam
  app := QuotientProducts.app
  beta := QuotientProducts.pi_beta signature

def betaSums (signature : Declaration.Signature Tower.Head) :
    DependentSumBeta (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)) where
  sigma := QuotientProducts.sigma
  pair := QuotientProducts.pair
  fst := QuotientProducts.fst
  snd := QuotientProducts.snd
  fst_pair := (QuotientProducts.sigma_beta signature).1
  snd_pair := (QuotientProducts.sigma_beta signature).2

private theorem max_self_below (level : LevelExpr) : Below (.max level level) level := by
  intro valuation
  simp only [LevelExpr.eval, max_self]
  exact Nat.le_refl _

/-- Redundant max syntax changes neither the admitted universe meaning
nor the decoded product. -/
def piClosed (signature : Declaration.Signature Tower.Head) :
    (hierarchy signature).PiClosed (betaProducts signature) where
  piCode := by
    intro context level domain codomain
    exact liftCode (max_self_below level) (piCode domain codomain)
  el_piCode := by
    intro context level domain codomain
    exact (decode_liftCode (max_self_below level) (piCode domain codomain)).trans
      (decode_piCode domain codomain)

def sigmaClosed (signature : Declaration.Signature Tower.Head) :
    (hierarchy signature).SigmaClosed (betaSums signature) where
  sigmaCode := by
    intro context level domain codomain
    exact liftCode (max_self_below level) (sigmaCode domain codomain)
  el_sigmaCode := by
    intro context level domain codomain
    exact (decode_liftCode (max_self_below level) (sigmaCode domain codomain)).trans
      (decode_sigmaCode domain codomain)

end

#print axioms decode_piCode
#print axioms decode_sigmaCode
#print axioms piClosed
#print axioms sigmaClosed

end FormationSensitiveContextual.QuotientUniverseProducts
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
