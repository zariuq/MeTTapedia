import Mettapedia.GSLT.Core.ProofRelevantTranslationCategory
import Mettapedia.TypeTheory.ProofRelevantTranslationDependentAction

/-!
# Proof-relevant GSLTs act on path contexts

Finite occurrence histories are not merely associated with each
proof-relevant GSLT.  A proof-relevant translation maps those histories
functorially, so the free evidence-path context is a compositional semantic
readout of the operational theory.

The construction retains occurrence evidence.  Proposition-valued reachability
is available only after applying a separate erasure or thin-descent operation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ProofRelevantPathContextFunctor

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

universe u

/-- Send a proof-relevant GSLT to its free category of finite occurrence
histories, and a translation to its occurrence-by-occurrence path map. -/
def evidenceContextFunctor :
    CategoryTheory.Functor (ProofRelevantGSLT.{u}) (Cat.{u, u}) where
  obj system := evidenceContext system
  map translation := Cat.Hom.ofFunctor translation.evidenceFunctor
  map_id system := by
    apply Cat.Hom.ext
    change (Translation.id system).evidenceFunctor = 𝟭 _
    refine CategoryTheory.Functor.hext
      (F := (Translation.id system).evidenceFunctor)
      (G := 𝟭 _) (fun _ => rfl) ?_
    intro source target path
    exact heq_of_eq (Translation.mapEvidencePath_id path)
  map_comp earlier later := by
    apply Cat.Hom.ext
    change (earlier.comp later).evidenceFunctor =
      earlier.evidenceFunctor ⋙ later.evidenceFunctor
    refine CategoryTheory.Functor.hext
      (F := (earlier.comp later).evidenceFunctor)
      (G := earlier.evidenceFunctor ⋙ later.evidenceFunctor)
      (fun _ => rfl) ?_
    intro source target path
    exact heq_of_eq
      (Translation.mapEvidencePath_comp earlier later path)

@[simp] theorem evidenceContextFunctor_obj
    (system : ProofRelevantGSLT.{u}) :
    evidenceContextFunctor.obj system = evidenceContext system :=
  rfl

@[simp] theorem evidenceContextFunctor_map_obj
    {source target : ProofRelevantGSLT.{u}}
    (translation : source ⟶ target)
    (term : EvidenceObject source) :
    (evidenceContextFunctor.map translation).toFunctor.obj term =
      translation.mapTerm term :=
  rfl

@[simp] theorem evidenceContextFunctor_map_path
    {source target : ProofRelevantGSLT.{u}}
    (translation : source ⟶ target)
    {first last : EvidenceObject source}
    (path : EvidencePath source first last) :
    (evidenceContextFunctor.map translation).toFunctor.map path =
      translation.mapEvidencePath path :=
  rfl

#print axioms evidenceContextFunctor
#print axioms evidenceContextFunctor_map_path

end Mettapedia.TypeTheory.ProofRelevantPathContextFunctor
