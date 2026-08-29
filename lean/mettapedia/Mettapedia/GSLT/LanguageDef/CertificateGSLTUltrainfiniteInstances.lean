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
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern} :
    PerspectiveProjection
      (Derivation definition goal) Unit
      (fun _ => WireArticle) (fun _ => Pattern) where
  project _ derivation := articleOfDerivation derivation
  observeWhole _ _ := goal
  observeShadow _ article := article.target
  adequate := by
    intro _ derivation
    simp [articleOfDerivation]

/-- Every article projected from a derivation is accepted by the real checker. -/
theorem derivationArticleProjection_checked
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    checkWireArticle definition
      (derivationArticleProjection.project () derivation) = true :=
  checkWireArticle_articleOfDerivation derivation

/-! ## Conversion evidence is a retained path -/

/-- Conversion is not ambient equality.  It is a path of ordinary checked
conversion edges and therefore retains route identity. -/
abbrev ConversionRoute (definition : ValidatedCalculusLanguageDef)
    (declaration : ConversionDecl) (source target : Pattern) :=
  Route (fun left right =>
    Ambient.ConversionEdge definition declaration left right) source target

namespace ConversionRoute

/-- Exact rule retention transports every edge of a conversion route. -/
def transport {sourcePresentation targetPresentation : ValidatedCalculusLanguageDef}
    (refines : RuleLookupRefines sourcePresentation targetPresentation)
    {declaration : ConversionDecl} {left right : Pattern} :
    ConversionRoute sourcePresentation declaration left right →
      ConversionRoute targetPresentation declaration left right
  | .refl pattern => .refl pattern
  | .cons edge rest =>
      .cons (edge.transport refines) (transport refines rest)

@[simp] theorem transport_refl
    {sourcePresentation targetPresentation : ValidatedCalculusLanguageDef}
    (refines : RuleLookupRefines sourcePresentation targetPresentation)
    {declaration : ConversionDecl} (pattern : Pattern) :
    transport refines
        (Route.refl pattern :
          ConversionRoute sourcePresentation declaration pattern pattern) =
      Route.refl pattern := rfl

end ConversionRoute

/-! ## Compact article support -/

/-- A concrete finite rule cone supporting one article.  It carries both the
restricted validated definition and successful replay there. -/
structure ArticleFiniteSupport
    (ambient : ValidatedCalculusLanguageDef) (article : WireArticle) where
  definition : ValidatedCalculusLanguageDef
  agrees : ArticleRuleAgreement definition ambient article
  accepted : checkWireArticle definition article = true

/-- A support replays in every definition agreeing on its cited rules. -/
theorem ArticleFiniteSupport.replayAt
    {ambient target : ValidatedCalculusLanguageDef} {article : WireArticle}
    (support : ArticleFiniteSupport ambient article)
    (agrees : ArticleRuleAgreement support.definition target article) :
    checkWireArticle target article = true :=
  (checkWireArticle_iff_articleRuleAgreement agrees).mp support.accepted

/-- Restriction to cited rule identifiers constructs a support when that
restriction remains a validated definition.  The validation premise is the
still-explicit declaration-cone obligation. -/
def ArticleFiniteSupport.ofRestriction
    {ambient : ValidatedCalculusLanguageDef} {article : WireArticle}
    (accepted : checkWireArticle ambient article = true)
    (restrictedValid :
      (Ambient.restrictRules ambient.1 article.citedRuleIds).isValid = true) :
    ArticleFiniteSupport ambient article where
  definition :=
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
