import Mettapedia.GSLT.LanguageDef.NIKTheoryGraph
import Mettapedia.Languages.Megalodon.SignatureEmbedding

/-!
# Megalodon selected environments in the NIK theory graph

Qualified heterogeneous signature embeddings supply the authored edges of the
selected Megalodon theory graph.  A retained path records whether transport
was direct or passed through intermediate selected environments, even when
both paths induce the same native claim and proof maps.

The current `SelectedTheoryProfile` meaning is native Mathdata theoremhood.
This module therefore proves exact native authority transport; it does not
rename that scope as external HOTG validity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SelectedTheoryGraph

open Mettapedia.GSLT.LanguageDef.NIKTheoryGraph
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.SelectedTheoryProfile
open Mettapedia.Languages.Megalodon.SignatureEmbedding

/-! ## The selected-environment graph -/

/-- The existing selected theory and exact native authority, packaged as one
NIK theory graph. -/
def graph : Graph Environment where
  theory := SelectedTheoryProfile.theory
  contract := SelectedTheoryProfile.contract

/-- Every qualified heterogeneous signature embedding gives one authored
edge. -/
def edge {source target : Environment}
    (embedding : SignatureEmbedding.Embedding source target) :
    graph.Edge source target :=
  embedding.authorityView

/-- Retain one qualified embedding as a one-edge route. -/
def path {source target : Environment}
    (embedding : SignatureEmbedding.Embedding source target) :
    graph.Path source target :=
  .cons (edge embedding) (.refl target)

@[simp] theorem path_length {source target : Environment}
    (embedding : SignatureEmbedding.Embedding source target) :
    (path embedding).length = 1 :=
  rfl

/-- Exact native replay is inherited by the retained graph path. -/
theorem path_check_commutes {source target : Environment}
    (embedding : SignatureEmbedding.Embedding source target)
    (claim : ProfileClaim) (proof : Pf) :
    (graph.contract.checker target).check
        ((Graph.Path.collapse (path embedding)).mapClaim claim)
        ((Graph.Path.collapse (path embedding)).mapCertificate proof) =
      (graph.contract.checker source).check claim proof :=
  Graph.Path.check_commutes (path embedding) claim proof

/-- Native theorem scope transports along every qualified retained path. -/
theorem path_scope_preserved {source target : Environment}
    (embedding : SignatureEmbedding.Embedding source target)
    (claim : ProfileClaim)
    (inScope : NativeTheoremScope source claim) :
    NativeTheoremScope target
      ((Graph.Path.collapse (path embedding)).mapClaim claim) :=
  Graph.Path.scope_preserved (path embedding) claim inScope

/-- The presently selected meaning predicate transports along the path.  Its
content is still native theoremhood, as declared by the selected profile. -/
theorem path_meaning_preserved {source target : Environment}
    (embedding : SignatureEmbedding.Embedding source target)
    (claim : ProfileClaim)
    (meaningful : graph.theory.Meaning source claim) :
    graph.theory.Meaning target
      ((Graph.Path.collapse (path embedding)).mapClaim claim) :=
  Graph.Path.meaning_preserved (path embedding) claim meaningful

/-! ## Direct and staged composition -/

/-- Retain two embeddings and their intermediate selected environment. -/
def stagedPath {source middle target : Environment}
    (earlier : SignatureEmbedding.Embedding source middle)
    (later : SignatureEmbedding.Embedding middle target) :
    graph.Path source target :=
  Route.append (path earlier) (path later)

/-- Compile the same pair of embeddings to one direct edge, intentionally
forgetting the intermediate environment. -/
def directCompositePath {source middle target : Environment}
    (earlier : SignatureEmbedding.Embedding source middle)
    (later : SignatureEmbedding.Embedding middle target) :
    graph.Path source target :=
  path (SignatureEmbedding.Embedding.comp earlier later)

@[simp] theorem stagedPath_length {source middle target : Environment}
    (earlier : SignatureEmbedding.Embedding source middle)
    (later : SignatureEmbedding.Embedding middle target) :
    (stagedPath earlier later).length = 2 :=
  rfl

@[simp] theorem directCompositePath_length
    {source middle target : Environment}
    (earlier : SignatureEmbedding.Embedding source middle)
    (later : SignatureEmbedding.Embedding middle target) :
    (directCompositePath earlier later).length = 1 :=
  rfl

/-- Staged and direct composition induce the same claim translation. -/
theorem staged_direct_same_claim {source middle target : Environment}
    (earlier : SignatureEmbedding.Embedding source middle)
    (later : SignatureEmbedding.Embedding middle target)
    (claim : ProfileClaim) :
    (Graph.Path.collapse (stagedPath earlier later)).mapClaim claim =
      (Graph.Path.collapse
        (directCompositePath earlier later)).mapClaim claim := by
  change later.mapProfileClaim (earlier.mapProfileClaim claim) =
    (SignatureEmbedding.Embedding.comp earlier later).mapProfileClaim claim
  exact (SignatureEmbedding.Embedding.mapProfileClaim_comp
    earlier later claim).symm

/-- Staged and direct composition induce the same native proof translation. -/
theorem staged_direct_same_certificate
    {source middle target : Environment}
    (earlier : SignatureEmbedding.Embedding source middle)
    (later : SignatureEmbedding.Embedding middle target)
    (proof : Pf) :
    (Graph.Path.collapse (stagedPath earlier later)).mapCertificate proof =
      (Graph.Path.collapse
        (directCompositePath earlier later)).mapCertificate proof := by
  change mapPf later.map (mapPf earlier.map proof) =
    mapPf (SignatureEmbedding.Embedding.comp earlier later).map proof
  exact (SignatureEmbedding.Embedding.mapPf_comp_embedding
    earlier later proof).symm

/-- The retained staged path is not identified with its direct composite,
despite inducing the same claim and proof transport. -/
theorem stagedPath_ne_directCompositePath
    {source middle target : Environment}
    (earlier : SignatureEmbedding.Embedding source middle)
    (later : SignatureEmbedding.Embedding middle target) :
    stagedPath earlier later ≠ directCompositePath earlier later := by
  intro equalPaths
  have equalLengths := congrArg Route.length equalPaths
  simp at equalLengths

/-! ## Heterogeneous signature canaries -/

namespace Canary

open SignatureEmbedding.Canary

def heterogeneousPath :
    graph.Path sourceEnvironment targetEnvironment :=
  path heterogeneousEmbedding

/-- Positive control through the retained graph: the real proof involving a
name, primitive, and base-type shift is accepted at the target. -/
theorem transported_profile_accepts_via_path :
    (graph.contract.checker targetEnvironment).check
        ((Graph.Path.collapse heterogeneousPath).mapClaim sourceClaim)
        ((Graph.Path.collapse heterogeneousPath).mapCertificate proof) =
      true := by
  rw [Graph.Path.check_commutes heterogeneousPath sourceClaim proof]
  exact source_profile_accepts

/-- Negative structural control is inherited from the underlying qualified
edge: corrupting the mapped primitive table supplies no embedding from which
this path constructor can be built. -/
theorem no_heterogeneous_path_from_prescribed_embedding :
    ¬ (exists embedding :
        SignatureEmbedding.Embedding sourceEnvironment
          wrongPrimitiveEnvironment,
      embedding.map = signatureMap) :=
  no_embedding_with_wrong_primitive

#print axioms path_check_commutes
#print axioms path_scope_preserved
#print axioms staged_direct_same_claim
#print axioms staged_direct_same_certificate
#print axioms stagedPath_ne_directCompositePath
#print axioms transported_profile_accepts_via_path
#print axioms no_heterogeneous_path_from_prescribed_embedding

end Canary

end Mettapedia.Languages.Megalodon.SelectedTheoryGraph
