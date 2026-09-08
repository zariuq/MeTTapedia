import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView

/-!
# Proof-relevant certificate-bearing theory-profile graphs

Theory views compose, but replacing a route by its composite forgets the
intermediate theories and translations.  This module keeps the authored route
as data and places selected executable artifacts in a separate displayed
layer.  Exact checker replay and artifact adequacy then derive the commuting
execution square.

The graph here is specifically the certificate-transport graph.  It is one
displayed part of NIK, not NIK's universal operational model; native decision,
construction, inference, and transformation services may be admitted and
selected without entering this graph.

The construction is deliberately relative to one `TheoryFamily` and one
`AuthorityContract`.  A heterogeneous graph of different logical frameworks
can package them into a larger family, but is not postulated here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateTransportGraph

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView
open Mettapedia.GSLT.Ultrainfinite

universe uKind uSignature uClaim uCertificate uArtifact

/-! ## A graph of semantic profiles and exact authorities -/

/-- A theory-profile graph retains the authored theory independently of the
certificate authority used to replay its native evidence. -/
structure Graph (Kind : Type uKind) where
  theory : TheoryFamily.{uSignature, uKind, uClaim} Kind
  contract :
    AuthorityContract.{uKind, uCertificate, uSignature, uClaim} theory

namespace Graph

variable {Kind : Type uKind} (graph : Graph Kind)

/-- One authored graph edge transports claims and native certificates with
exact replay, while preserving independently declared meaning. -/
abbrev Edge (source target : Kind) : Type _ :=
  AuthorityView graph.contract source target

/-- A route retains every authored edge and intermediate theory profile. -/
abbrev Path (source target : Kind) : Type _ :=
  Route graph.Edge source target

namespace Path

variable {graph : Graph Kind} {first middle last : Kind}

/-- Collapse a retained route only when a consumer asks for its composite
authority view. -/
def collapse : {source target : Kind} ->
    graph.Path source target -> graph.Edge source target
  | _, _, .refl kind => AuthorityView.identity kind
  | _, _, .cons edge rest => AuthorityView.comp edge (collapse rest)

@[simp] theorem collapse_refl (kind : Kind) :
    collapse (graph := graph) (.refl kind) = AuthorityView.identity kind :=
  rfl

@[simp] theorem collapse_cons
    (edge : graph.Edge first middle) (rest : graph.Path middle last) :
    collapse (.cons edge rest) = AuthorityView.comp edge (collapse rest) :=
  rfl

/-- Route composition agrees with composition of the collapsed claim maps. -/
theorem collapse_append_mapClaim
    (earlier : graph.Path first middle) (later : graph.Path middle last)
    (claim : graph.theory.Claim first) :
    (collapse (Route.append earlier later)).mapClaim claim =
      (collapse later).mapClaim ((collapse earlier).mapClaim claim) := by
  induction earlier with
  | refl => rfl
  | cons edge rest inductionHypothesis =>
      exact inductionHypothesis later (edge.mapClaim claim)

/-- Route composition agrees with composition of the collapsed certificate
maps, retaining native proof-fibre transport. -/
theorem collapse_append_mapCertificate
    (earlier : graph.Path first middle) (later : graph.Path middle last)
    (certificate : graph.contract.Certificate first) :
    (collapse (Route.append earlier later)).mapCertificate certificate =
      (collapse later).mapCertificate
        ((collapse earlier).mapCertificate certificate) := by
  induction earlier with
  | refl => rfl
  | cons edge rest inductionHypothesis =>
      exact inductionHypothesis later (edge.mapCertificate certificate)

/-- Exact replay holds across every retained route. -/
theorem check_commutes (path : graph.Path first last)
    (claim : graph.theory.Claim first)
    (certificate : graph.contract.Certificate first) :
    (graph.contract.checker last).check
        ((collapse path).mapClaim claim)
        ((collapse path).mapCertificate certificate) =
      (graph.contract.checker first).check claim certificate :=
  (collapse path).check_commutes claim certificate

/-- Every retained route preserves the independently declared theorem scope. -/
theorem scope_preserved (path : graph.Path first last)
    (claim : graph.theory.Claim first)
    (inScope : graph.theory.Scope first claim) :
    graph.theory.Scope last ((collapse path).mapClaim claim) :=
  (collapse path).scope_preserved claim inScope

/-- Every retained route preserves the independently declared semantic
meaning. -/
theorem meaning_preserved (path : graph.Path first last)
    (claim : graph.theory.Claim first)
    (meaningful : graph.theory.Meaning first claim) :
    graph.theory.Meaning last ((collapse path).mapClaim claim) :=
  (collapse path).meaning_preserved claim meaningful

/-- Forget certificate transport edge by edge while retaining the same route
shape and intermediate profiles. -/
def toTheoryPath : {source target : Kind} -> graph.Path source target ->
    Route (TheoryView graph.theory) source target
  | _, _, .refl kind => .refl kind
  | _, _, .cons edge rest => .cons edge.toTheoryView (toTheoryPath rest)

@[simp] theorem toTheoryPath_length (path : graph.Path first last) :
    (toTheoryPath path).length = path.length := by
  induction path with
  | refl => rfl
  | cons edge rest inductionHypothesis =>
      simp only [toTheoryPath, Route.length, inductionHypothesis]

end Path

end Graph

/-! ## Selected executable artifacts displayed over a graph -/

/-- A selected executable realization for every profile.  Artifact types may
differ between profiles; choosing them is implementation data, not part of the
theory's meaning. -/
structure RealizedFamily {Kind : Type uKind} (graph : Graph Kind) where
  Artifact : Kind -> Type uArtifact
  realization : (kind : Kind) ->
    AuthorityRealization graph.contract kind (Artifact kind)

namespace RealizedFamily

variable {Kind : Type uKind} {graph : Graph Kind}
    (realized : RealizedFamily graph)

/-- A displayed edge maps the selected source artifact to the selected target
artifact over an already justified authority view. -/
structure Edge (source target : Kind) where
  authority : graph.Edge source target
  mapArtifact : realized.Artifact source -> realized.Artifact target
  maps_selected :
    mapArtifact (realized.realization source).artifact =
      (realized.realization target).artifact

namespace Edge

variable {realized : RealizedFamily graph} {first middle last : Kind}

/-- Identity displayed edge. -/
def identity (kind : Kind) : realized.Edge kind kind where
  authority := AuthorityView.identity kind
  mapArtifact := id
  maps_selected := rfl

/-- Displayed edges compose without discarding either authority transport or
artifact transport. -/
def comp (earlier : realized.Edge first middle)
    (later : realized.Edge middle last) : realized.Edge first last where
  authority := AuthorityView.comp earlier.authority later.authority
  mapArtifact artifact := later.mapArtifact (earlier.mapArtifact artifact)
  maps_selected := by
    rw [earlier.maps_selected, later.maps_selected]

@[simp] theorem identity_mapArtifact (kind : Kind)
    (artifact : realized.Artifact kind) :
    (identity (realized := realized) kind).mapArtifact artifact = artifact :=
  rfl

@[simp] theorem comp_mapArtifact
    (earlier : realized.Edge first middle)
    (later : realized.Edge middle last)
    (artifact : realized.Artifact first) :
    (comp earlier later).mapArtifact artifact =
      later.mapArtifact (earlier.mapArtifact artifact) :=
  rfl

/-- The execution square is derived from endpoint adequacy, exact authority
replay, and preservation of the selected artifacts.  It is not an additional
trusted field of a displayed edge. -/
theorem replay_commutes (edge : realized.Edge first middle)
    (claim : graph.theory.Claim first)
    (certificate : graph.contract.Certificate first) :
    (realized.realization middle).replay
        (edge.mapArtifact (realized.realization first).artifact)
        (edge.authority.mapClaim claim)
        (edge.authority.mapCertificate certificate) =
      (realized.realization first).replay
        (realized.realization first).artifact claim certificate := by
  rw [edge.maps_selected]
  rw [(realized.realization middle).adequate]
  rw [edge.authority.check_commutes]
  rw [(realized.realization first).adequate]

end Edge

/-- A displayed path retains both the theory-profile route and every artifact
translation chosen along it. -/
abbrev Path (source target : Kind) : Type _ :=
  Route realized.Edge source target

namespace Path

variable {realized : RealizedFamily graph} {first middle last : Kind}

/-- Collapse a displayed path only at a consumer boundary. -/
def collapse : {source target : Kind} ->
    realized.Path source target -> realized.Edge source target
  | _, _, .refl kind => Edge.identity kind
  | _, _, .cons edge rest => Edge.comp edge (collapse rest)

/-- Forget executable artifacts edge by edge while retaining the authority
route and all intermediate profiles. -/
def toAuthorityPath : {source target : Kind} ->
    realized.Path source target -> graph.Path source target
  | _, _, .refl kind => .refl kind
  | _, _, .cons edge rest => .cons edge.authority (toAuthorityPath rest)

@[simp] theorem toAuthorityPath_length (path : realized.Path first last) :
    (toAuthorityPath path).length = path.length := by
  induction path with
  | refl => rfl
  | cons edge rest inductionHypothesis =>
      simp only [toAuthorityPath, Route.length, inductionHypothesis]

/-- Collapsing after forgetting artifacts gives the same claim transport as
the authority component of the collapsed displayed path. -/
theorem collapse_toAuthorityPath_mapClaim
    (path : realized.Path first last)
    (claim : graph.theory.Claim first) :
    (Graph.Path.collapse (toAuthorityPath path)).mapClaim claim =
      (collapse path).authority.mapClaim claim := by
  induction path with
  | refl => rfl
  | cons edge rest inductionHypothesis =>
      exact inductionHypothesis (edge.authority.mapClaim claim)

/-- The same projection law retains native certificate transport. -/
theorem collapse_toAuthorityPath_mapCertificate
    (path : realized.Path first last)
    (certificate : graph.contract.Certificate first) :
    (Graph.Path.collapse (toAuthorityPath path)).mapCertificate certificate =
      (collapse path).authority.mapCertificate certificate := by
  induction path with
  | refl => rfl
  | cons edge rest inductionHypothesis =>
      exact inductionHypothesis
        (edge.authority.mapCertificate certificate)

/-- The artifact map of a displayed composite agrees with applying each
retained artifact map in route order. -/
theorem collapse_append_mapArtifact
    (earlier : realized.Path first middle)
    (later : realized.Path middle last)
    (artifact : realized.Artifact first) :
    (collapse (Route.append earlier later)).mapArtifact artifact =
      (collapse later).mapArtifact
        ((collapse earlier).mapArtifact artifact) := by
  induction earlier with
  | refl => rfl
  | cons edge rest inductionHypothesis =>
      exact inductionHypothesis later (edge.mapArtifact artifact)

/-- Every displayed path inherits the derived replay square of its composite. -/
theorem replay_commutes (path : realized.Path first last)
    (claim : graph.theory.Claim first)
    (certificate : graph.contract.Certificate first) :
    (realized.realization last).replay
        ((collapse path).mapArtifact
          (realized.realization first).artifact)
        ((collapse path).authority.mapClaim claim)
        ((collapse path).authority.mapCertificate certificate) =
      (realized.realization first).replay
        (realized.realization first).artifact claim certificate :=
  (collapse path).replay_commutes claim certificate

end Path

end RealizedFamily

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView.ExtensionCanary

abbrev Profile :=
  Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView.ExtensionCanary.Profile

def graph : Graph Profile where
  theory := ExtensionCanary.theory
  contract := ExtensionCanary.contract

/-- One direct retained route from the base profile to its extension. -/
def directPath : graph.Path Profile.base Profile.extension :=
  .cons ExtensionCanary.inclusion (.refl Profile.extension)

/-- An observationally equivalent route that retains an explicit identity
stage before the inclusion. -/
def stagedPath : graph.Path Profile.base Profile.extension :=
  .cons (AuthorityView.identity Profile.base) directPath

/-- The two routes induce the same translated claims. -/
theorem direct_staged_same_claim (claim : Bool) :
    (Graph.Path.collapse directPath).mapClaim claim =
      (Graph.Path.collapse stagedPath).mapClaim claim :=
  rfl

/-- The two routes induce the same translated native certificates. -/
theorem direct_staged_same_certificate (certificate : Unit) :
    (Graph.Path.collapse directPath).mapCertificate certificate =
      (Graph.Path.collapse stagedPath).mapCertificate certificate := by
  cases certificate
  rfl

/-- Route provenance is genuinely retained even when the collapsed transport
is observationally identical. -/
theorem directPath_ne_stagedPath : directPath ≠ stagedPath := by
  intro equalPaths
  have equalLengths := congrArg Route.length equalPaths
  simp [directPath, stagedPath, Route.length] at equalLengths

def Artifact : Profile -> Type
  | .base => Unit
  | .extension => Bool

/-- The target artifact deliberately has a bad mode (`true`); only the
selected artifact `false` faithfully realizes the target checker. -/
def realized : RealizedFamily graph where
  Artifact := Artifact
  realization
    | .base =>
        { artifact := ()
          replay := fun _ claim _ => claim
          adequate := by intro claim certificate; rfl }
    | .extension =>
        { artifact := false
          replay := fun (artifact : Bool) (claim : Bool)
              (certificate : Bool) =>
            if artifact then false else certificate || claim
          adequate := by
            intro claim certificate
            rfl }

/-- The direct authority inclusion has a coherent executable artifact map. -/
def realizedInclusion : realized.Edge .base .extension where
  authority := ExtensionCanary.inclusion
  mapArtifact := fun _ => false
  maps_selected := rfl

/-- Positive control: mapped executable replay agrees exactly with source
replay for every claim. -/
theorem realizedInclusion_replays (claim : Bool) :
    (realized.realization .extension).replay
        (realizedInclusion.mapArtifact
          (realized.realization .base).artifact)
        (realizedInclusion.authority.mapClaim claim)
        (realizedInclusion.authority.mapCertificate ()) =
      (realized.realization .base).replay
        (realized.realization .base).artifact claim () :=
  realizedInclusion.replay_commutes claim ()

/-- Negative control: mapping the selected source artifact to the target's bad
mode cannot form a displayed edge over the same authority inclusion. -/
theorem no_bad_selected_artifact_map :
    ¬ (exists edge : realized.Edge .base .extension,
      edge.authority = ExtensionCanary.inclusion /\
        edge.mapArtifact () = true) := by
  rintro ⟨edge, authorityEqual, mapsTrue⟩
  have mapsFalse : edge.mapArtifact () = false := edge.maps_selected
  rw [mapsTrue] at mapsFalse
  cases mapsFalse

/-- The negative is semantic rather than cosmetic: forcing the bad target
artifact returns `false` even for a claim accepted by the source checker. -/
theorem bad_target_artifact_breaks_replay :
    (realized.realization .extension).replay true true false ≠
      (realized.realization .base).replay () true () := by
  simp [realized]

#print axioms Graph.Path.check_commutes
#print axioms Graph.Path.meaning_preserved
#print axioms RealizedFamily.Edge.replay_commutes
#print axioms RealizedFamily.Path.replay_commutes
#print axioms RealizedFamily.Path.collapse_toAuthorityPath_mapClaim
#print axioms RealizedFamily.Path.collapse_toAuthorityPath_mapCertificate
#print axioms directPath_ne_stagedPath
#print axioms no_bad_selected_artifact_map
#print axioms bad_target_artifact_breaks_replay

end Canary

end Mettapedia.GSLT.LanguageDef.CertificateTransportGraph
