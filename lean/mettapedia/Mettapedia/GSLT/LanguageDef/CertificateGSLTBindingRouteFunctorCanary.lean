import Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteFunctor
import Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthorityCanary

/-!
# Canary for occurrence-bearing binding-presentation routes

The source edge is the genuinely binder-bearing, namespace-changing semantic
embedding from `CertificateGSLTBindingAuthorityCanary`.  A second authored
edge records a target-side no-op revision.  The direct and revised routes have
the same endpoints and both preserve exact checking, but remain different
paths because the latter retains one additional authored occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteFunctorCanary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthorityCanary
open Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteFunctor

def sourceNode : BindingPresentation := ofSemantic sourcePresentation
def targetNode : BindingPresentation := ofSemantic targetPresentation

/-- The first generator changes every language namespace while preserving a
real binder-bearing theorem. -/
def bindingRename : Quiver.Hom sourceNode targetNode := semanticEmbedding

/-- A separately authored no-op revision is a generator occurrence, not the
empty categorical path. -/
def targetRevision : Quiver.Hom targetNode targetNode :=
  BindingSemanticEmbedding.identity targetPresentation

def directRoute : Route sourceNode targetNode := bindingRename.toPath

def revisedRoute : Route sourceNode targetNode :=
  directRoute.cons targetRevision

@[simp] theorem directRoute_length : directRoute.length = 1 :=
  rfl

@[simp] theorem revisedRoute_length : revisedRoute.length = 2 :=
  rfl

/-- Adding an authored no-op revision does not silently collapse the route to
the earlier history. -/
theorem directRoute_ne_revisedRoute : directRoute ≠ revisedRoute := by
  intro equal
  have lengthEqual := congrArg Quiver.Path.length equal
  simp only [directRoute_length, revisedRoute_length] at lengthEqual
  omega

/-- The singleton route compiles to the existing nontrivial generated
authority translation. -/
theorem directRoute_compiles_exactly :
    generationFunctor.map directRoute =
      BindingSemanticEmbedding.map semanticEmbedding := by
  exact generationFunctor_map_generator bindingRename

/-- The revised route compiles as the ordered composite of both authored
events. -/
theorem revisedRoute_compiles_in_order :
    generationFunctor.map revisedRoute =
      CategoryTheory.CategoryStruct.comp
        (generationFunctor.map directRoute)
        (generatorAuthority.map targetRevision) := by
  exact generationFunctor_map_cons directRoute targetRevision

/-- Exact source acceptance survives the direct binder-renaming route. -/
theorem directRoute_accepts_source_certificate :
    ((contract targetPresentation).checker ()).check
        ((generationFunctor.map directRoute).mapClaim () sourceClaim)
        ((generationFunctor.map directRoute).mapCertificate ()
          sourceCertificate) = true := by
  calc
    _ = ((contract sourcePresentation).checker ()).check sourceClaim
          sourceCertificate :=
      route_check_commutes directRoute sourceClaim sourceCertificate
    _ = true := rfl

/-- Exact source acceptance also survives the longer, occurrence-distinct
revision route. -/
theorem revisedRoute_accepts_source_certificate :
    ((contract targetPresentation).checker ()).check
        ((generationFunctor.map revisedRoute).mapClaim () sourceClaim)
        ((generationFunctor.map revisedRoute).mapCertificate ()
          sourceCertificate) = true := by
  calc
    _ = ((contract sourcePresentation).checker ()).check sourceClaim
          sourceCertificate :=
      route_check_commutes revisedRoute sourceClaim sourceCertificate
    _ = true := rfl

private def wrongClaim : Pattern := .apply "binding-route:wrong" []

/-- Rejection is transported just as exactly as acceptance. -/
theorem directRoute_rejects_wrong_claim :
    ((contract targetPresentation).checker ()).check
        ((generationFunctor.map directRoute).mapClaim () wrongClaim)
        ((generationFunctor.map directRoute).mapCertificate ()
          sourceCertificate) = false := by
  calc
    _ = ((contract sourcePresentation).checker ()).check wrongClaim
          sourceCertificate :=
      route_check_commutes directRoute wrongClaim sourceCertificate
    _ = false := by
      change decide (sourceClaim = wrongClaim) = false
      decide

/-- Independent source meaning is transported along the route without being
defined by the successful checker result above. -/
theorem directRoute_preserves_independent_meaning :
    targetPresentation.Meaning
      ((generationFunctor.map directRoute).mapClaim () sourceClaim) :=
  route_meaning_preserved directRoute sourceClaim rfl

/-- Distinct routes can have the same coarse acceptance observation.  The
observation therefore cannot justify identifying their provenance. -/
theorem distinct_routes_share_acceptance_observation :
    directRoute ≠ revisedRoute ∧
      ((contract targetPresentation).checker ()).check
          ((generationFunctor.map directRoute).mapClaim () sourceClaim)
          ((generationFunctor.map directRoute).mapCertificate ()
            sourceCertificate) =
        ((contract targetPresentation).checker ()).check
          ((generationFunctor.map revisedRoute).mapClaim () sourceClaim)
          ((generationFunctor.map revisedRoute).mapCertificate ()
            sourceCertificate) :=
  ⟨directRoute_ne_revisedRoute,
    directRoute_accepts_source_certificate.trans
      revisedRoute_accepts_source_certificate.symm⟩

#print axioms directRoute_ne_revisedRoute
#print axioms directRoute_compiles_exactly
#print axioms revisedRoute_compiles_in_order
#print axioms directRoute_accepts_source_certificate
#print axioms revisedRoute_accepts_source_certificate
#print axioms directRoute_rejects_wrong_claim
#print axioms directRoute_preserves_independent_meaning
#print axioms distinct_routes_share_acceptance_observation

end Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteFunctorCanary
