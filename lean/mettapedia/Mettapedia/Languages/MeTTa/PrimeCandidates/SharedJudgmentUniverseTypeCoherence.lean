import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentTypeInterpretation
import Mettapedia.TypeTheory.TarskiDecodedFamilyCoherence

/-!
# Native constructor code values and contextual type isomorphisms

Native code-constructor agreement is distinct from equivalence of decoded
carriers. On the explicitly qualified comparison class below, two meanings
of the same admitted native type give isomorphic display maps: both compare
with the same interpreted native extension and agree on its projection.
Neither equality of type objects nor code uniqueness is required.

The projection condition is a scoped sufficient interface, not a universal
semantic requirement. An explicit nontrivial comparison between the common
context presentations is an alternative. These are interface constructions,
not an inhabitant of a common native model or an unbounded universe model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseTypeCoherence

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.FormationSensitive SharedJudgmentFragment
open SharedJudgmentTypeInterpretation (ContextComparison ComprehensionMeaning ComprehensionCoverage
  Family FamilyMeaning FamilyAdmitted)

universe u v w w'

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-- Only the two actual admitted comprehension projections are compared.
No code uniqueness, global type equality or decoding isomorphism is part
of this independent structural restriction. -/
def WeakeningProjectionCoherent (interpretation : SharedJudgmentInterpretation.Data assembly C)
    {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n) (type : Tower.Tm n)
    (first second : C.Ty (interpretation.ctx context)) : Prop :=
  ∀ (level : Tower.Head)
    (extendedFormed : ContextFormation assembly.rules (.snoc context.raw type))
    (firstComparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw type, extendedFormed⟩)
      (C.ext (interpretation.ctx context) first))
    (secondComparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw type, extendedFormed⟩)
      (C.ext (interpretation.ctx context) second)),
    Judgment assembly.rules context type (.head level) → assembly.rules.isUniverse level →
    interpretation.ty context type first → interpretation.ty context type second →
    ComprehensionMeaning interpretation context type extendedFormed first firstComparison →
    ComprehensionMeaning interpretation context type extendedFormed second secondComparison →
      C.compS (C.wk first) firstComparison.forward =
        C.compS (C.wk second) secondComparison.forward

/-- An invertible comparison of display contexts over the same base is
an isomorphism in the existing type-over-context category. -/
def displayIso {context : C.Ctx} {first second : C.Ty context}
    (comparison : ContextComparison C (C.ext context first) (C.ext context second))
    (inverse : comparison.Inverse)
    (projection : C.compS (C.wk second) comparison.forward = C.wk first) :
    (⟨first⟩ : TypeOver C context) ≅ ⟨second⟩ where
  hom := ⟨comparison.forward, projection⟩
  inv := ⟨comparison.backward, by
    rw [← projection, C.comp_assoc, inverse.1, C.comp_id]⟩
  hom_inv_id := TypeOver.Hom.ext inverse.2
  inv_hom_id := TypeOver.Hom.ext inverse.1

/-- Compose comparisons through the same interpreted native extension.
The type isomorphism is constructed from context maps, not assumed as a
decoding law. -/
def comprehensionTypeIso {context common : C.Ctx} {first second : C.Ty context}
    (firstComparison : ContextComparison C common (C.ext context first))
    (secondComparison : ContextComparison C common (C.ext context second))
    (firstInverse : firstComparison.Inverse) (secondInverse : secondComparison.Inverse)
    (projection : C.compS (C.wk first) firstComparison.forward =
      C.compS (C.wk second) secondComparison.forward) :
    (⟨first⟩ : TypeOver C context) ≅ ⟨second⟩ :=
  displayIso
    ⟨C.compS secondComparison.forward firstComparison.backward,
      C.compS firstComparison.forward secondComparison.backward⟩
    ⟨by
      rw [C.comp_assoc, ← C.comp_assoc firstComparison.backward firstComparison.forward,
        firstInverse.2, C.id_comp, secondInverse.1],
      by
      rw [C.comp_assoc, ← C.comp_assoc secondComparison.backward secondComparison.forward,
        secondInverse.2, C.id_comp, firstInverse.1]⟩
    (by rw [← C.comp_assoc, ← projection, C.comp_assoc, firstInverse.1, C.comp_id])

/-- A supplied comparison can correct unequal projections. This route
does not demand strict agreement of the original two projections. -/
def comprehensionTypeIsoVia {context common : C.Ctx} {first second : C.Ty context}
    (firstComparison : ContextComparison C common (C.ext context first))
    (secondComparison : ContextComparison C common (C.ext context second))
    (connector : ContextComparison C common common)
    (firstInverse : firstComparison.Inverse) (secondInverse : secondComparison.Inverse)
    (connectorInverse : connector.Inverse)
    (projection : C.compS (C.wk first) firstComparison.forward =
      C.compS (C.wk second) (C.compS secondComparison.forward connector.forward)) :
    (⟨first⟩ : TypeOver C context) ≅ ⟨second⟩ :=
  comprehensionTypeIso firstComparison
    ⟨C.compS secondComparison.forward connector.forward,
      C.compS connector.backward secondComparison.backward⟩
    firstInverse
    ⟨by rw [C.comp_assoc, ← C.comp_assoc connector.forward connector.backward,
        connectorInverse.1, C.id_comp, secondInverse.1],
      by rw [C.comp_assoc, ← C.comp_assoc secondComparison.backward secondComparison.forward,
        secondInverse.2, C.id_comp, connectorInverse.2]⟩ projection

theorem type_meanings_isomorphic
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (coverage : ComprehensionCoverage interpretation)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {type : Tower.Tm n} {level : Tower.Head}
    (admitted : Judgment assembly.rules context type (.head level))
    (universeHead : assembly.rules.isUniverse level)
    (first second : C.Ty (interpretation.ctx context))
    (coherent : WeakeningProjectionCoherent interpretation context type first second)
    (firstMeaning : interpretation.ty context type first)
    (secondMeaning : interpretation.ty context type second) :
    Nonempty ((⟨first⟩ : TypeOver C (interpretation.ctx context)) ≅ ⟨second⟩) := by
  obtain ⟨firstComparison, firstLaws⟩ := coverage n context type level first admitted universeHead firstMeaning
  obtain ⟨secondComparison, secondLaws⟩ := coverage n context type level second admitted universeHead secondMeaning
  exact ⟨comprehensionTypeIso firstComparison secondComparison firstLaws.1 secondLaws.1
    (coherent level (.snoc context.formed admitted.typing universeHead) firstComparison secondComparison
      admitted universeHead firstMeaning secondMeaning firstLaws secondLaws)⟩

/-- The codomain code is pulled back from the actual native extension,
using the existing universe-reindex interface. This interface is explicit;
no strict equality of decoded constructor types is introduced. -/
def codomainCode (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C)
    (stable : universes.universe.SubstitutionStable)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {domain : Tower.Tm n}
    {extendedFormed : ContextFormation assembly.rules (.snoc context.raw domain)} {lower upper : LevelExpr}
    (domainCode : C.Tm (interpretation.ctx context) (universes.universe.univ (interpretation.ctx context) lower))
    (nativeCode : C.Tm (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper))
    (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (C.ext (interpretation.ctx context) (universes.universe.el domainCode))) :
    C.Tm (C.ext (interpretation.ctx context) (universes.universe.el domainCode))
      (universes.universe.univ (C.ext (interpretation.ctx context) (universes.universe.el domainCode)) upper) :=
  SharedJudgmentUniverseInterpretation.substituteCode universes stable comparison.backward nativeCode

def decodedFamily (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C)
    (stable : universes.universe.SubstitutionStable)
    {n : Nat} (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1))
    {extendedFormed : ContextFormation assembly.rules (.snoc context.raw domain)}
    {lower upper : LevelExpr}
    (domainCode : C.Tm (interpretation.ctx context) (universes.universe.univ (interpretation.ctx context) lower))
    (nativeCode : C.Tm (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper))
    (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (C.ext (interpretation.ctx context) (universes.universe.el domainCode))) :
    Family interpretation context domain codomain where
  contextFormation := extendedFormed
  semanticDomain := universes.universe.el domainCode
  semanticCodomain := universes.universe.el (codomainCode interpretation universes stable domainCode nativeCode comparison)
  comparison := comparison

/-- The dependent codomain's type meaning survives the round trip through
the actual comprehension comparison. This follows from decoding naturality
and the inverse context equation; it is not an additional meaning premise. -/
theorem decoded_family_meaning
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C)
    (stable : universes.universe.SubstitutionStable)
    (decode : SharedJudgmentUniverseInterpretation.CodesDecode interpretation universes)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {extendedFormed : ContextFormation assembly.rules (.snoc context.raw domain)}
    {lower upper : LevelExpr}
    (domainAdmitted : Judgment assembly.rules context domain (sortTm lower))
    (codomainAdmitted : Judgment assembly.rules (.snoc context domain) codomain (sortTm upper))
    (domainCode : C.Tm (interpretation.ctx context) (universes.universe.univ (interpretation.ctx context) lower))
    (nativeCode : C.Tm (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper))
    (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (C.ext (interpretation.ctx context) (universes.universe.el domainCode)))
    (domainMeaning : interpretation.term context domain (sortTm lower)
      (universes.universe.univ (interpretation.ctx context) lower) domainCode)
    (codomainMeaning : interpretation.term ⟨.snoc context.raw domain, extendedFormed⟩ codomain (sortTm upper)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper) nativeCode)
    (comparisonMeaning : ComprehensionMeaning interpretation context domain extendedFormed
      (universes.universe.el domainCode) comparison) :
    FamilyMeaning interpretation
      (decodedFamily interpretation universes stable context domain codomain domainCode nativeCode comparison) := by
  refine ⟨decode n context domain lower domainCode domainAdmitted domainMeaning, comparisonMeaning, ?_⟩
  have codomainDecoded := decode (n + 1) ⟨.snoc context.raw domain, extendedFormed⟩ codomain upper nativeCode codomainAdmitted codomainMeaning
  have roundTrip : C.tySub
      (universes.universe.el (codomainCode interpretation universes stable domainCode nativeCode comparison))
      comparison.forward = universes.universe.el nativeCode := by
    change C.tySub
      (universes.universe.el (SharedJudgmentUniverseInterpretation.substituteCode universes stable comparison.backward nativeCode))
      comparison.forward = _
    rw [SharedJudgmentUniverseInterpretation.substituteCode, stable.el_sub,
      ← C.tySub_comp, comparisonMeaning.1.2, C.tySub_id]
  change interpretation.ty ⟨.snoc context.raw domain, extendedFormed⟩ codomain
    (C.tySub (universes.universe.el
      (codomainCode interpretation universes stable domainCode nativeCode comparison)) comparison.forward)
  rw [roundTrip]
  exact codomainDecoded

/-! ## Independent agreement of the actual native constructor code values -/

/-- This clause concerns the value of the native Pi code, not an arbitrary
code with an equivalent carrier. The codomain is taken from the actual native
extension and transported by its supplied comprehension comparison. -/
def PiCodeMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C) : Prop :=
  ∀ (stable : universes.universe.SubstitutionStable)
    (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1))
    (lower upper : LevelExpr)
    {extendedFormed : ContextFormation assembly.rules (.snoc context.raw domain)}
    (domainCode : C.Tm (interpretation.ctx context)
      (universes.universe.univ (interpretation.ctx context) lower))
    (nativeCode : C.Tm (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper))
    (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (C.ext (interpretation.ctx context) (universes.universe.el domainCode))),
    Judgment assembly.rules context domain (sortTm lower) →
    Judgment assembly.rules (.snoc context domain) codomain (sortTm upper) →
    interpretation.term context domain (sortTm lower)
      (universes.universe.univ (interpretation.ctx context) lower) domainCode →
    interpretation.term ⟨.snoc context.raw domain, extendedFormed⟩ codomain (sortTm upper)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper) nativeCode →
    ComprehensionMeaning interpretation context domain extendedFormed (universes.universe.el domainCode) comparison →
      interpretation.term context (.pi domain codomain) (sortTm (.max lower upper))
        (universes.universe.univ (interpretation.ctx context) (.max lower upper))
        (universes.piCode domainCode
          (codomainCode interpretation universes stable domainCode nativeCode comparison))

/-- Sigma has its own native value-agreement clause; Pi's agreement does
not license silently substituting the Sigma constructor or its code. -/
def SigmaCodeMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C) : Prop :=
  ∀ (stable : universes.universe.SubstitutionStable)
    (n : Nat) (context : SharedJudgmentInterpretation.Context assembly n) (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1))
    (lower upper : LevelExpr)
    {extendedFormed : ContextFormation assembly.rules (.snoc context.raw domain)}
    (domainCode : C.Tm (interpretation.ctx context)
      (universes.universe.univ (interpretation.ctx context) lower))
    (nativeCode : C.Tm (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper))
    (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
      (C.ext (interpretation.ctx context) (universes.universe.el domainCode))),
    Judgment assembly.rules context domain (sortTm lower) →
    Judgment assembly.rules (.snoc context domain) codomain (sortTm upper) →
    interpretation.term context domain (sortTm lower)
      (universes.universe.univ (interpretation.ctx context) lower) domainCode →
    interpretation.term ⟨.snoc context.raw domain, extendedFormed⟩ codomain (sortTm upper)
      (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper) nativeCode →
    ComprehensionMeaning interpretation context domain extendedFormed (universes.universe.el domainCode) comparison →
      interpretation.term context (.sigma domain codomain) (sortTm (.max lower upper))
        (universes.universe.univ (interpretation.ctx context) (.max lower upper))
        (universes.sigmaCode domainCode
          (codomainCode interpretation universes stable domainCode nativeCode comparison))

theorem family_admitted_at_sorts {n : Nat} {context : Tower.Ctx n}
    {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)} {lower upper : LevelExpr}
    (domainAdmitted : Judgment assembly.rules context domain (sortTm lower))
    (codomainAdmitted : Judgment assembly.rules (.snoc context domain) codomain (sortTm upper)) :
    FamilyAdmitted assembly context domain codomain :=
  ⟨.sort lower, .sort upper, .sort (.max lower upper), domainAdmitted, .sort lower,
    codomainAdmitted, .sort upper, .sorts lower upper⟩

theorem pi_admitted {n : Nat} {context : Tower.Ctx n}
    {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)} {lower upper : LevelExpr}
    (domainAdmitted : Judgment assembly.rules context domain (sortTm lower))
    (codomainAdmitted : Judgment assembly.rules (.snoc context domain) codomain (sortTm upper)) :
    Judgment assembly.rules context (.pi domain codomain) (sortTm (.max lower upper)) :=
  ⟨domainAdmitted.context, .piForm domainAdmitted.typing (.sort lower)
    codomainAdmitted.typing (.sort upper) (.sorts lower upper)⟩

theorem sigma_admitted {n : Nat} {context : Tower.Ctx n}
    {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)} {lower upper : LevelExpr}
    (domainAdmitted : Judgment assembly.rules context domain (sortTm lower))
    (codomainAdmitted : Judgment assembly.rules (.snoc context domain) codomain (sortTm upper)) :
    Judgment assembly.rules context (.sigma domain codomain) (sortTm (.max lower upper)) :=
  ⟨domainAdmitted.context, .sigmaForm domainAdmitted.typing (.sort lower)
    codomainAdmitted.typing (.sort upper) (.sorts lower upper)⟩

section ConstructorCoherence

variable (interpretation : SharedJudgmentInterpretation.Data assembly C)
  (universes : SharedJudgmentUniverseInterpretation.Operations C)
  (operations : SharedJudgmentTypeInterpretation.Operations C)
  (stable : universes.universe.SubstitutionStable)
  (decode : SharedJudgmentUniverseInterpretation.CodesDecode interpretation universes)
  (coverage : ComprehensionCoverage interpretation)
  {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
  {extendedFormed : ContextFormation assembly.rules (.snoc context.raw domain)}
  {lower upper : LevelExpr}
  (domainAdmitted : Judgment assembly.rules context domain (sortTm lower))
  (codomainAdmitted : Judgment assembly.rules (.snoc context domain) codomain (sortTm upper))
  (domainCode : C.Tm (interpretation.ctx context) (universes.universe.univ (interpretation.ctx context) lower))
  (nativeCode : C.Tm (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
    (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper))
  (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
    (C.ext (interpretation.ctx context) (universes.universe.el domainCode)))
  (domainMeaning : interpretation.term context domain (sortTm lower)
    (universes.universe.univ (interpretation.ctx context) lower) domainCode)
  (codomainMeaning : interpretation.term ⟨.snoc context.raw domain, extendedFormed⟩ codomain (sortTm upper)
    (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper) nativeCode)
  (comparisonMeaning : ComprehensionMeaning interpretation context domain extendedFormed
    (universes.universe.el domainCode) comparison)

include decode coverage domainAdmitted codomainAdmitted domainMeaning codomainMeaning comparisonMeaning

/-- Native code agreement, decoding naturality and semantic formation
meet on one actual dependent family. The resulting display-map isomorphism
is derived from two admitted comprehension comparisons. -/
theorem pi_code_decodes_as_product
    (codeMeaning : PiCodeMeaning interpretation universes)
    (formation : SharedJudgmentTypeInterpretation.PiFormationMeaning interpretation operations.products)
    (coherent : WeakeningProjectionCoherent interpretation context (.pi domain codomain)
      (universes.universe.el (universes.piCode domainCode
        (codomainCode interpretation universes stable domainCode nativeCode comparison)))
      (operations.products.pi (universes.universe.el domainCode)
        (universes.universe.el (codomainCode interpretation universes stable domainCode nativeCode comparison)))) :
    let code := universes.piCode domainCode
      (codomainCode interpretation universes stable domainCode nativeCode comparison)
    let product := operations.products.pi (universes.universe.el domainCode)
      (universes.universe.el (codomainCode interpretation universes stable domainCode nativeCode comparison))
    Judgment assembly.rules context (.pi domain codomain) (sortTm (.max lower upper)) ∧
      interpretation.term context (.pi domain codomain) (sortTm (.max lower upper))
        (universes.universe.univ (interpretation.ctx context) (.max lower upper)) code ∧
      interpretation.ty context (.pi domain codomain) product ∧
      Nonempty ((⟨universes.universe.el code⟩ : TypeOver C (interpretation.ctx context)) ≅ ⟨product⟩) := by
  have admitted := pi_admitted domainAdmitted codomainAdmitted
  have codeAgrees := codeMeaning stable n context domain codomain lower upper domainCode nativeCode comparison
    domainAdmitted codomainAdmitted domainMeaning codomainMeaning comparisonMeaning
  have familyMeans := decoded_family_meaning interpretation universes stable decode
    domainAdmitted codomainAdmitted domainCode nativeCode comparison domainMeaning codomainMeaning comparisonMeaning
  have productMeans := formation n context domain codomain _
    (family_admitted_at_sorts domainAdmitted codomainAdmitted) familyMeans
  refine ⟨admitted, codeAgrees, productMeans, ?_⟩
  exact type_meanings_isomorphic interpretation coverage admitted (.sort _) _ _ coherent
    (decode n context (.pi domain codomain) (.max lower upper) _ admitted codeAgrees) productMeans

theorem sigma_code_decodes_as_sum
    (codeMeaning : SigmaCodeMeaning interpretation universes)
    (formation : SharedJudgmentTypeInterpretation.SigmaFormationMeaning interpretation operations.sums)
    (coherent : WeakeningProjectionCoherent interpretation context (.sigma domain codomain)
      (universes.universe.el (universes.sigmaCode domainCode
        (codomainCode interpretation universes stable domainCode nativeCode comparison)))
      (operations.sums.sigma (universes.universe.el domainCode)
        (universes.universe.el (codomainCode interpretation universes stable domainCode nativeCode comparison)))) :
    let code := universes.sigmaCode domainCode
      (codomainCode interpretation universes stable domainCode nativeCode comparison)
    let sum := operations.sums.sigma (universes.universe.el domainCode)
      (universes.universe.el (codomainCode interpretation universes stable domainCode nativeCode comparison))
    Judgment assembly.rules context (.sigma domain codomain) (sortTm (.max lower upper)) ∧
      interpretation.term context (.sigma domain codomain) (sortTm (.max lower upper))
        (universes.universe.univ (interpretation.ctx context) (.max lower upper)) code ∧
      interpretation.ty context (.sigma domain codomain) sum ∧
      Nonempty ((⟨universes.universe.el code⟩ : TypeOver C (interpretation.ctx context)) ≅ ⟨sum⟩) := by
  have admitted := sigma_admitted domainAdmitted codomainAdmitted
  have codeAgrees := codeMeaning stable n context domain codomain lower upper domainCode nativeCode comparison
    domainAdmitted codomainAdmitted domainMeaning codomainMeaning comparisonMeaning
  have familyMeans := decoded_family_meaning interpretation universes stable decode
    domainAdmitted codomainAdmitted domainCode nativeCode comparison domainMeaning codomainMeaning comparisonMeaning
  have sumMeans := formation n context domain codomain _
    (family_admitted_at_sorts domainAdmitted codomainAdmitted) familyMeans
  refine ⟨admitted, codeAgrees, sumMeans, ?_⟩
  exact type_meanings_isomorphic interpretation coverage admitted (.sort _) _ _ coherent
    (decode n context (.sigma domain codomain) (.max lower upper) _ admitted codeAgrees) sumMeans

end ConstructorCoherence

/-- Coverage supplies both codes in their actual native contexts and one
comparison for their shared domain. It does not select an unrelated semantic
family for the Pi and Sigma routes. -/
theorem admitted_family_codes
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C)
    (stable : universes.universe.SubstitutionStable)
    (total : SharedJudgmentUniverseInterpretation.CodeTotal interpretation universes)
    (decode : SharedJudgmentUniverseInterpretation.CodesDecode interpretation universes)
    (coverage : ComprehensionCoverage interpretation)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {extendedFormed : ContextFormation assembly.rules (.snoc context.raw domain)}
    {lower upper : LevelExpr}
    (domainAdmitted : Judgment assembly.rules context domain (sortTm lower))
    (codomainAdmitted : Judgment assembly.rules (.snoc context domain) codomain (sortTm upper)) :
    ∃ (domainCode : C.Tm (interpretation.ctx context)
        (universes.universe.univ (interpretation.ctx context) lower))
      (nativeCode : C.Tm (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
        (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper))
      (comparison : ContextComparison C (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩)
        (C.ext (interpretation.ctx context) (universes.universe.el domainCode))),
      interpretation.term context domain (sortTm lower)
        (universes.universe.univ (interpretation.ctx context) lower) domainCode ∧
      interpretation.term ⟨.snoc context.raw domain, extendedFormed⟩ codomain (sortTm upper)
        (universes.universe.univ (interpretation.ctx ⟨.snoc context.raw domain, extendedFormed⟩) upper) nativeCode ∧
      ComprehensionMeaning interpretation context domain extendedFormed (universes.universe.el domainCode) comparison ∧
      FamilyMeaning interpretation
        (decodedFamily interpretation universes stable context domain codomain domainCode nativeCode comparison) := by
  obtain ⟨domainCode, domainMeaning⟩ := total n context domain lower domainAdmitted
  obtain ⟨nativeCode, codomainMeaning⟩ := total (n + 1) ⟨.snoc context.raw domain, extendedFormed⟩ codomain upper codomainAdmitted
  obtain ⟨comparison, comparisonMeaning⟩ := coverage n context domain (.sort lower)
    (universes.universe.el domainCode) domainAdmitted (.sort lower)
    (decode n context domain lower domainCode domainAdmitted domainMeaning)
  exact ⟨domainCode, nativeCode, comparison, domainMeaning, codomainMeaning, comparisonMeaning,
    decoded_family_meaning interpretation universes stable decode domainAdmitted codomainAdmitted
      domainCode nativeCode comparison domainMeaning codomainMeaning comparisonMeaning⟩

/-- A genuinely wrong decoded carrier cannot be registered as the code
meaning of the admitted source on this qualified comparison class. Merely
changing a code while retaining an equivalent carrier would not suffice. -/
theorem mismatched_code_rejected
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C)
    (decode : SharedJudgmentUniverseInterpretation.CodesDecode interpretation universes)
    (coverage : ComprehensionCoverage interpretation)
    {n : Nat} {context : SharedJudgmentInterpretation.Context assembly n} {type : Tower.Tm n} {level : LevelExpr}
    (admitted : Judgment assembly.rules context type (sortTm level))
    (code : C.Tm (interpretation.ctx context) (universes.universe.univ (interpretation.ctx context) level))
    (semanticType : C.Ty (interpretation.ctx context))
    (meaning : interpretation.ty context type semanticType)
    (coherent : WeakeningProjectionCoherent interpretation context type (universes.universe.el code) semanticType)
    (mismatch : ¬ Nonempty ((⟨universes.universe.el code⟩ : TypeOver C (interpretation.ctx context)) ≅ ⟨semanticType⟩)) :
    ¬ interpretation.term context type (sortTm level)
      (universes.universe.univ (interpretation.ctx context) level) code := by
  intro codeMeaning
  exact mismatch (type_meanings_isomorphic interpretation coverage admitted (.sort level) _ _ coherent
    (decode n context type level code admitted codeMeaning) meaning)

/-! ## Concrete contextual comparison and code controls -/

open Mettapedia.TypeTheory

/-- Existing fibre equivalences give actual display-context comparisons;
their projection equations are independently checked below. -/
def fibreComparison {context : Type u} {first second : context → Type u}
    (equivalence : ∀ point, first point ≃ second point) :
    ContextComparison familiesCwf (Sigma first) (Sigma second) where
  forward := TarskiDecodedFamilyCoherence.Fibrewise.total equivalence
  backward := (TarskiDecodedFamilyCoherence.Fibrewise.total equivalence).symm

theorem fibreComparison_inverse {context : Type u} {first second : context → Type u}
    (equivalence : ∀ point, first point ≃ second point) :
    (fibreComparison equivalence).Inverse := by
  constructor <;> funext point
  · exact (TarskiDecodedFamilyCoherence.Fibrewise.total equivalence).apply_symm_apply point
  · exact (TarskiDecodedFamilyCoherence.Fibrewise.total equivalence).symm_apply_apply point

def fibreDisplayIso {context : Type u} {first second : context → Type u}
    (equivalence : ∀ point, first point ≃ second point) :
    (⟨first⟩ : TypeOver familiesCwf context) ≅ ⟨second⟩ :=
  displayIso (fibreComparison equivalence) (fibreComparison_inverse equivalence) rfl

/-- A display isomorphism is in particular an equivalence of the actual
extended context carriers. This does not discard its additional over-base law. -/
def displayTotalEquiv {context : Type u} {first second : context → Type u}
    (isomorphism : (⟨first⟩ : TypeOver familiesCwf context) ≅ ⟨second⟩) :
    Sigma first ≃ Sigma second where
  toFun := isomorphism.hom.substitution
  invFun := isomorphism.inv.substitution
  left_inv point := congrFun (congrArg TypeOver.Hom.substitution isomorphism.hom_inv_id) point
  right_inv point := congrFun (congrArg TypeOver.Hom.substitution isomorphism.inv_hom_id) point

namespace Controls

open SharedJudgmentUniverseInterpretation.TaggedFormation (formedContext)

/-- The dependent family's native extension carries its actual formation,
independently of every semantic code and comparison below. -/
def variableExtension (level : LevelExpr) : SharedJudgmentInterpretation.Context assembly 3 :=
  .snoc (formedContext level) (.var 1) (.sort level) (.var 1) (.sort level)

/-- The actual arbitrary native family `B x`, in `A : U_l, B : Pi x : A, U_l`.
No closed or constant codomain restriction is made. -/
theorem variable_family_admitted (level : LevelExpr) :
    Judgment assembly.rules (NativeCumulativeFormationCoherenceBoundary.context level)
        (.var 1) (sortTm level) ∧
      Judgment assembly.rules (.snoc (NativeCumulativeFormationCoherenceBoundary.context level) (.var 1))
        (.app (.var 1) (.var 0)) (sortTm level) := by
  have formed := NativeCumulativeFormationCoherenceBoundary.context_formed assembly.declarations level
  exact ⟨⟨formed, .var 1⟩, ⟨.snoc formed (.var 1) (.sort level),
    NativeCumulativeFormationCoherenceBoundary.family_application_formed assembly.declarations level⟩⟩

theorem variable_pi_sigma_admitted (level : LevelExpr) :
    Judgment assembly.rules (NativeCumulativeFormationCoherenceBoundary.context level)
        (.pi (.var 1) (.app (.var 1) (.var 0))) (sortTm (.max level level)) ∧
      Judgment assembly.rules (NativeCumulativeFormationCoherenceBoundary.context level)
        (.sigma (.var 1) (.app (.var 1) (.var 0))) (sortTm (.max level level)) :=
  ⟨pi_admitted (variable_family_admitted level).1 (variable_family_admitted level).2,
    sigma_admitted (variable_family_admitted level).1 (variable_family_admitted level).2⟩

/-- On an inhabited native source, coverage produces the common decoded
family used by both constructor crowns. The semantic assumptions remain
explicit: this is not an independently inhabited full interpretation. -/
theorem variable_family_codes
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C)
    (stable : universes.universe.SubstitutionStable)
    (total : SharedJudgmentUniverseInterpretation.CodeTotal interpretation universes)
    (decode : SharedJudgmentUniverseInterpretation.CodesDecode interpretation universes)
    (coverage : ComprehensionCoverage interpretation) (level : LevelExpr) :
    ∃ (domainCode : C.Tm (interpretation.ctx (formedContext level))
        (universes.universe.univ (interpretation.ctx (formedContext level)) level))
      (nativeCode : C.Tm (interpretation.ctx (variableExtension level))
        (universes.universe.univ (interpretation.ctx (variableExtension level)) level))
      (comparison : ContextComparison C
        (interpretation.ctx (variableExtension level))
        (C.ext (interpretation.ctx (formedContext level))
          (universes.universe.el domainCode))),
      interpretation.term (formedContext level) (.var 1) (sortTm level)
        (universes.universe.univ (interpretation.ctx (formedContext level)) level) domainCode ∧
      interpretation.term (variableExtension level)
        (.app (.var 1) (.var 0)) (sortTm level)
        (universes.universe.univ (interpretation.ctx (variableExtension level)) level) nativeCode ∧
      ComprehensionMeaning interpretation (formedContext level) (.var 1) (variableExtension level).formed
        (universes.universe.el domainCode) comparison ∧
      FamilyMeaning interpretation (decodedFamily interpretation universes stable
        (formedContext level) (.var 1) (.app (.var 1) (.var 0))
          domainCode nativeCode comparison) :=
  admitted_family_codes interpretation universes stable total decode coverage
    (context := formedContext level) (extendedFormed := (variableExtension level).formed)
    (variable_family_admitted level).1 (variable_family_admitted level).2

/-- Both constructor values and both display-map consequences use the same
codes and comparison, obtained from coverage of the actual open family.
The exact two projection hypotheses remain visible at the resulting meanings. -/
theorem variable_constructor_coherence
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (universes : SharedJudgmentUniverseInterpretation.Operations C)
    (operations : SharedJudgmentTypeInterpretation.Operations C)
    (stable : universes.universe.SubstitutionStable)
    (total : SharedJudgmentUniverseInterpretation.CodeTotal interpretation universes)
    (decode : SharedJudgmentUniverseInterpretation.CodesDecode interpretation universes)
    (coverage : ComprehensionCoverage interpretation)
    (piValues : PiCodeMeaning interpretation universes)
    (sigmaValues : SigmaCodeMeaning interpretation universes)
    (products : SharedJudgmentTypeInterpretation.PiFormationMeaning interpretation operations.products)
    (sums : SharedJudgmentTypeInterpretation.SigmaFormationMeaning interpretation operations.sums)
    (level : LevelExpr) :
    let context := formedContext (assembly := assembly) level
    let nativePi : Tower.Tm 2 := .pi (.var 1) (.app (.var 1) (.var 0))
    let nativeSigma : Tower.Tm 2 := .sigma (.var 1) (.app (.var 1) (.var 0))
    ∃ (domainCode : C.Tm (interpretation.ctx context)
        (universes.universe.univ (interpretation.ctx context) level))
      (nativeCode : C.Tm (interpretation.ctx (variableExtension level))
        (universes.universe.univ (interpretation.ctx (variableExtension level)) level))
      (comparison : ContextComparison C (interpretation.ctx (variableExtension level))
        (C.ext (interpretation.ctx context) (universes.universe.el domainCode))),
      let bodyCode := codomainCode interpretation universes stable domainCode nativeCode comparison
      let piCode := universes.piCode domainCode bodyCode
      let sigmaCode := universes.sigmaCode domainCode bodyCode
      let product := operations.products.pi (universes.universe.el domainCode) (universes.universe.el bodyCode)
      let sum := operations.sums.sigma (universes.universe.el domainCode) (universes.universe.el bodyCode)
      interpretation.term context nativePi (sortTm (.max level level))
        (universes.universe.univ (interpretation.ctx context) (.max level level)) piCode ∧
      interpretation.term context nativeSigma (sortTm (.max level level))
        (universes.universe.univ (interpretation.ctx context) (.max level level)) sigmaCode ∧
      interpretation.ty context nativePi product ∧ interpretation.ty context nativeSigma sum ∧
      (WeakeningProjectionCoherent interpretation context nativePi (universes.universe.el piCode) product →
        Nonempty ((⟨universes.universe.el piCode⟩ : TypeOver C (interpretation.ctx context)) ≅ ⟨product⟩)) ∧
      (WeakeningProjectionCoherent interpretation context nativeSigma (universes.universe.el sigmaCode) sum →
        Nonempty ((⟨universes.universe.el sigmaCode⟩ : TypeOver C (interpretation.ctx context)) ≅ ⟨sum⟩)) := by
  obtain ⟨domainCode, nativeCode, comparison, domainMeaning, codomainMeaning, comparisonMeaning, familyMeans⟩ :=
    variable_family_codes interpretation universes stable total decode coverage level
  have admitted := variable_family_admitted (assembly := assembly) level
  have familyAdmitted := family_admitted_at_sorts admitted.1 admitted.2
  refine ⟨domainCode, nativeCode, comparison,
    piValues stable 2 _ _ _ level level domainCode nativeCode comparison
      admitted.1 admitted.2 domainMeaning codomainMeaning comparisonMeaning,
    sigmaValues stable 2 _ _ _ level level domainCode nativeCode comparison
      admitted.1 admitted.2 domainMeaning codomainMeaning comparisonMeaning,
    products 2 _ _ _ _ familyAdmitted familyMeans,
    sums 2 _ _ _ _ familyAdmitted familyMeans, ?_, ?_⟩
  · intro coherent
    exact (pi_code_decodes_as_product interpretation universes operations stable decode coverage
      admitted.1 admitted.2 domainCode nativeCode comparison domainMeaning codomainMeaning comparisonMeaning
      piValues products coherent).2.2.2
  · intro coherent
    exact (sigma_code_decodes_as_sum interpretation universes operations stable decode coverage
      admitted.1 admitted.2 domainCode nativeCode comparison domainMeaning codomainMeaning comparisonMeaning
      sigmaValues sums coherent).2.2.2

/-- Two genuinely invertible presentations can disagree on the base while
reading the same newest variable. Thus variable compatibility alone cannot
replace the projection hypothesis. -/
def baseFlip : ContextComparison familiesCwf (Σ _ : Bool, Bool) (Σ _ : Bool, Bool) where
  forward point := ⟨!point.1, point.2⟩
  backward point := ⟨!point.1, point.2⟩

theorem baseFlip_inverse : baseFlip.Inverse := by
  constructor <;> funext point
  all_goals rcases point with ⟨base, value⟩; cases base <;> rfl

theorem baseFlip_reads_variable :
    familiesCwf.tmSub (familiesCwf.vz (fun _ : Bool => Bool)) baseFlip.forward =
      familiesCwf.vz (fun _ : Bool => Bool) := rfl

theorem baseFlip_projection_disagrees :
    familiesCwf.compS (familiesCwf.wk (fun _ : Bool => Bool)) baseFlip.forward ≠
      familiesCwf.wk (fun _ : Bool => Bool) := by
  intro equal
  have atFalse := congrFun equal ⟨false, true⟩
  change true = false at atFalse
  cases atFalse

/-- The explicitly supplied nonidentity connector repairs the base square;
strict agreement of the original comparisons was not necessary. -/
def repairedBaseFlip :
    (⟨fun _ : Bool => Bool⟩ : TypeOver familiesCwf Bool) ≅ ⟨fun _ => Bool⟩ :=
  comprehensionTypeIsoVia
    ⟨id, id⟩ baseFlip baseFlip ⟨rfl, rfl⟩ baseFlip_inverse baseFlip_inverse
    (by funext point; rcases point with ⟨base, value⟩; cases base <;> rfl)

theorem connector_is_nontrivial : baseFlip.forward ≠ id := by
  intro equal
  apply baseFlip_projection_disagrees
  rw [equal]
  rfl

namespace TwoLevelCodes

open CwfTarskiUniverseHierarchy.TwoLevelSetFamilies
open TarskiDecodedFamilyCoherence

/-- A local mixed-level chart from the independently constructed hierarchy.
It is not an assignment of all native levels to these two semantic levels. -/
def domain (_ : PUnit.{3}) : Code.{0} false := ⟨Bool⟩

def codomain (point : Σ context, decode.{0} false (domain context)) : Code.{0} true :=
  ⟨ULift.{1, 0} (Fin (if (show Bool from point.2.down.down) then 3 else 2))⟩

def productType : PUnit.{3} → Type 2 :=
  SharedJudgmentTypeInterpretation.familiesOperations.products.pi
    (hierarchy.el (level := false) domain) (hierarchy.el (level := true) codomain)

def sumType : PUnit.{3} → Type 2 :=
  SharedJudgmentTypeInterpretation.familiesOperations.sums.sigma
    (hierarchy.el (level := false) domain) (hierarchy.el (level := true) codomain)

/-- Actual mixed-level Pi decoding gives a display-map isomorphism to the
same raw set-family product operation used by the native constructor bridge. -/
def productIso :
    (⟨hierarchy.el (TwoLevel.mixedPi.contextCode domain codomain)⟩ :
      TypeOver familiesCwf PUnit.{3}) ≅ ⟨productType⟩ :=
  fibreDisplayIso (fun point => TwoLevel.mixedPi.fibreEquiv domain codomain point)

def sumIso :
    (⟨hierarchy.el (TwoLevel.mixedSigma.contextCode domain codomain)⟩ :
      TypeOver familiesCwf PUnit.{3}) ≅ ⟨sumType⟩ :=
  fibreDisplayIso (fun point => TwoLevel.mixedSigma.fibreEquiv domain codomain point)

def smallProductEquiv : productType PUnit.unit ≃ ((bit : Bool) → Fin (if bit then 3 else 2)) :=
  (Equiv.ulift.trans Equiv.ulift).piCongr (fun _ => Equiv.ulift.trans Equiv.ulift)

def smallSumEquiv : sumType PUnit.unit ≃ (Σ bit : Bool, Fin (if bit then 3 else 2)) :=
  (Equiv.ulift.trans Equiv.ulift).sigmaCongr (fun _ => Equiv.ulift.trans Equiv.ulift)

theorem dependent_carriers_differ :
    ¬ Nonempty (sumType PUnit.unit ≃ productType PUnit.unit) := by
  rintro ⟨equivalence⟩
  have cardinality := Fintype.card_congr
    ((smallSumEquiv.symm.trans equivalence).trans smallProductEquiv)
  norm_num [Fintype.card_sigma, Fintype.card_pi] at cardinality

/-- The independently available Sigma code is not a valid Pi carrier for
this dependent family: its five inhabitants cannot represent six functions. -/
theorem wrong_constructor_code_not_isomorphic :
    ¬ Nonempty ((⟨hierarchy.el (TwoLevel.mixedSigma.contextCode domain codomain)⟩ :
      TypeOver familiesCwf PUnit.{3}) ≅ ⟨productType⟩) := by
  rintro ⟨isomorphism⟩
  have total := displayTotalEquiv (sumIso.symm.trans isomorphism)
  exact dependent_carriers_differ ⟨
    (ContextualSumComparison.unitSigmaEquiv (sumType PUnit.unit)).symm.trans
      (total.trans (ContextualSumComparison.unitSigmaEquiv (productType PUnit.unit)))⟩

theorem code_values_differ :
    TwoLevel.mixedSigma.contextCode domain codomain ≠
      TwoLevel.mixedPi.contextCode domain codomain := by
  intro equal
  apply wrong_constructor_code_not_isomorphic
  rw [equal]
  exact ⟨productIso⟩

/-- Both inputs have genuinely different dependent fibre sizes. -/
theorem codomain_is_dependent :
    ¬ Nonempty (decode.{0} true (codomain ⟨PUnit.unit, ⟨⟨false⟩⟩⟩) ≃
      decode.{0} true (codomain ⟨PUnit.unit, ⟨⟨true⟩⟩⟩)) := by
  rintro ⟨equivalence⟩
  change ULift.{2, 1} (ULift.{1, 0} (Fin 2)) ≃
    ULift.{2, 1} (ULift.{1, 0} (Fin 3)) at equivalence
  have cardinality := Fintype.card_congr equivalence
  norm_num at cardinality

end TwoLevelCodes

end Controls

#print axioms comprehensionTypeIso
#print axioms comprehensionTypeIsoVia
#print axioms type_meanings_isomorphic
#print axioms decoded_family_meaning
#print axioms pi_code_decodes_as_product
#print axioms sigma_code_decodes_as_sum
#print axioms admitted_family_codes
#print axioms Controls.variable_family_codes
#print axioms Controls.variable_constructor_coherence
#print axioms Controls.baseFlip_projection_disagrees
#print axioms mismatched_code_rejected
#print axioms Controls.TwoLevelCodes.productIso
#print axioms Controls.TwoLevelCodes.wrong_constructor_code_not_isomorphic

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseTypeCoherence
