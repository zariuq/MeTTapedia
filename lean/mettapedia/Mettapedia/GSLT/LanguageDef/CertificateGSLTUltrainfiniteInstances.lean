import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.GSLT.LanguageDef.CertificateGSLTAmbient
import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrainfinite

/-!
# CertificateGSLT instances of the ambient-first GSLT theory

The abstract theory lives in `Mettapedia.GSLT.Core.Ultrainfinite`.  This file
contains only its CertificateGSLT-specific realizations:

* a proof-relevant derivation projects to a chronological article shadow;
* conversion evidence composes as a retained route;
* an accepted article factors through a finite cited-rule support.

The Büchi progress-measure development remains in
`CertificateGSLTUltrainfinite`: it is one application of finite evidence to an
infinitary claim, not the definition of the ambient theory.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite

/-! ## Derivations are primary; articles are checked shadows -/

/-- Linearization preserves the proved judgment as its declared observation.
It does not identify different derivations or claim that an article reconstructs
the original proof tree. -/
def derivationArticleProjection
    {presentation : ValidatedPresentation} {goal : Pattern} :
    PerspectiveProjection
      (Derivation presentation goal) Unit
      (fun _ => WireArticle) (fun _ => Pattern) where
  project _ derivation := articleOfDerivation derivation
  observeWhole _ _ := goal
  observeShadow _ article := article.target
  adequate := by
    intro _ derivation
    simp [articleOfDerivation]

/-- Every article projected from a derivation is accepted by the real checker. -/
theorem derivationArticleProjection_checked
    {presentation : ValidatedPresentation} {goal : Pattern}
    (derivation : Derivation presentation goal) :
    checkWireArticle presentation
      (derivationArticleProjection.project () derivation) = true :=
  checkWireArticle_articleOfDerivation derivation

/-! ## Conversion evidence is a retained path -/

/-- Conversion is not ambient equality.  It is a path of ordinary checked
conversion edges and therefore retains route identity. -/
abbrev ConversionRoute (presentation : ValidatedPresentation)
    (declaration : ConversionDecl) (source target : Pattern) :=
  Route (fun left right =>
    Ambient.ConversionEdge presentation declaration left right) source target

namespace ConversionRoute

/-- Exact rule retention transports every edge of a conversion route. -/
def transport {sourcePresentation targetPresentation : ValidatedPresentation}
    (refines : RuleLookupRefines sourcePresentation targetPresentation)
    {declaration : ConversionDecl} {left right : Pattern} :
    ConversionRoute sourcePresentation declaration left right →
      ConversionRoute targetPresentation declaration left right
  | .refl pattern => .refl pattern
  | .cons edge rest =>
      .cons (edge.transport refines) (transport refines rest)

@[simp] theorem transport_refl
    {sourcePresentation targetPresentation : ValidatedPresentation}
    (refines : RuleLookupRefines sourcePresentation targetPresentation)
    {declaration : ConversionDecl} (pattern : Pattern) :
    transport refines
        (Route.refl pattern :
          ConversionRoute sourcePresentation declaration pattern pattern) =
      Route.refl pattern := rfl

end ConversionRoute

/-! ## Compact article support -/

/-- A concrete finite rule cone supporting one article.  It carries both the
restricted validated presentation and successful replay there. -/
structure ArticleFiniteSupport
    (ambient : ValidatedPresentation) (article : WireArticle) where
  presentation : ValidatedPresentation
  agrees : ArticleRuleAgreement presentation ambient article
  accepted : checkWireArticle presentation article = true

/-- A support replays in every presentation agreeing on its cited rules. -/
theorem ArticleFiniteSupport.replayAt
    {ambient target : ValidatedPresentation} {article : WireArticle}
    (support : ArticleFiniteSupport ambient article)
    (agrees : ArticleRuleAgreement support.presentation target article) :
    checkWireArticle target article = true :=
  (checkWireArticle_iff_articleRuleAgreement agrees).mp support.accepted

/-- Restriction to cited rule identifiers constructs a support when that
restriction remains a validated presentation.  The validation premise is the
still-explicit declaration-cone obligation. -/
def ArticleFiniteSupport.ofRestriction
    {ambient : ValidatedPresentation} {article : WireArticle}
    (accepted : checkWireArticle ambient article = true)
    (restrictedValid :
      (Ambient.restrictRules ambient.1 article.citedRuleIds).isValidV2 = true) :
    ArticleFiniteSupport ambient article where
  presentation :=
    ⟨Ambient.restrictRules ambient.1 article.citedRuleIds, restrictedValid⟩
  agrees := by
    intro id cited
    exact Ambient.lookupRule?_restrictRules article.citedRuleIds
      (by simpa using cited)
  accepted :=
    (Ambient.checkWireArticle_restrictRules ambient.2 restrictedValid).mp
      accepted

#print axioms derivationArticleProjection_checked
#print axioms ArticleFiniteSupport.replayAt
#print axioms ArticleFiniteSupport.ofRestriction

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
