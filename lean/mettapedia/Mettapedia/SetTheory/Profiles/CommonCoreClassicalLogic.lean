import Mettapedia.SetTheory.Profiles.CommonCore
import Mettapedia.SetTheory.CarveOuts.Sites.GSets

/-!
# Ordinary model semantics for retained common-core deductions

The ordinary semantics is the existing `Tarski` interpretation of the
material formula language. Its interpretation is compared with contextual
forcing over one point. The original occurrence-indexed proof is translated
rule by rule to the already checked contextual deduction system; its law
ledger remains the ledger of the original proof.

This logical soundness result needs neither classical logic nor a set axiom.
The concrete set models and their additional host dependencies are separate.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreClassicalLogic

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)

universe u

/-- A constant carrier interpreted over one point. -/
def values (S : Type u) : Discrete PUnit.{1} ⥤ Type u where
  obj _ := S
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def model {S : Type u} (member : S → S → Prop) : Model (values S) where
  member _ := member
  member_transport _ _ := id

theorem force_iff_tarski {S : Type u} (member : S → S → Prop) {count : Nat}
    (body : Formula count) (point : Discrete PUnit.{1}) (environment : Fin count → S) :
    force (values S) (model member) body point environment ↔ Tarski member body environment := by
  induction body generalizing point with
  | bottom => exact Iff.rfl
  | equal => exact Iff.rfl
  | member => exact Iff.rfl
  | both left right leftIH rightIH => exact and_congr (leftIH point _) (rightIH point _)
  | either left right leftIH rightIH => exact or_congr (leftIH point _) (rightIH point _)
  | imply left right leftIH rightIH =>
      constructor
      · intro holds premise
        exact (rightIH point environment).mp
          (holds point (𝟙 point) ((leftIH point environment).mpr premise))
      · intro holds target _ premise
        exact (rightIH target environment).mpr
          (holds ((leftIH target environment).mp premise))
  | all body bodyIH =>
      constructor
      · intro holds value
        exact (bodyIH point (extend (values S) environment value)).mp (holds point (𝟙 point) value)
      · intro holds target _ value
        exact (bodyIH target (extend (values S) environment value)).mpr (holds value)
  | exist body bodyIH =>
      constructor
      · rintro ⟨value, holds⟩
        exact ⟨value, (bodyIH point (extend (values S) environment value)).mp holds⟩
      · rintro ⟨value, holds⟩
        exact ⟨value, (bodyIH point (extend (values S) environment value)).mpr holds⟩

/-- Substitution is interpreted by the actual reindexed assignment. -/
theorem substitute_iff {S : Type u} (member : S → S → Prop) {count other : Nat}
    (indices : Fin count → Fin other) (body : Formula count) (environment : Fin other → S) :
    Tarski member (substitute indices body) environment ↔
      Tarski member body (fun index => environment (indices index)) :=
  (force_iff_tarski member _ ⟨⟨⟩⟩ _).symm.trans
    ((force_substitute (model member) indices body ⟨⟨⟩⟩ environment).trans
      (force_iff_tarski member body ⟨⟨⟩⟩ _))

/-- Forgetting hypothesis positions only at the already sound semantic
deduction boundary. The input remains the actual retained proof tree. -/
def contextualProof {count : Nat} {assumptions : List (Formula count)}
    {conclusion : Formula count} (proof : GraphRealizedDeduction.Proof assumptions conclusion) :
    ContextualMaterialLogic.Derivation assumptions conclusion :=
  match proof with
  | .hypothesis index => .hypothesis (List.getElem_mem index.isLt)
  | .weakening previous positions same => .weakening (contextualProof previous) (by
      intro body included
      obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp included
      rw [← same ⟨index, bound⟩]
      exact List.getElem_mem (positions ⟨index, bound⟩).isLt)
  | .bottomElim previous => .bottomElim (contextualProof previous)
  | .bothIntro left right => .bothIntro (contextualProof left) (contextualProof right)
  | .bothLeft previous => .bothLeft (contextualProof previous)
  | .bothRight previous => .bothRight (contextualProof previous)
  | .eitherLeft previous => .eitherLeft (contextualProof previous)
  | .eitherRight previous => .eitherRight (contextualProof previous)
  | .eitherElim previous left right =>
      .eitherElim (contextualProof previous) (contextualProof left) (contextualProof right)
  | .implyIntro previous => .implyIntro (contextualProof previous)
  | .implyElim previous premise => .implyElim (contextualProof previous) (contextualProof premise)
  | .allIntro previous => .allIntro (contextualProof previous)
  | .allElim previous index => .allElim (contextualProof previous) index
  | .existIntro index previous => .existIntro index (contextualProof previous)
  | .existElim previous branch => .existElim (contextualProof previous) (contextualProof branch)
  | .equalRefl index => .equalRefl index
  | .equalElim same previous => .equalElim (contextualProof same) (contextualProof previous)

/-- Every logical rule, including the quantifier and equality rules, is
interpreted in an arbitrary ordinary membership structure. -/
theorem proof_sound {S : Type u} (member : S → S → Prop) {count : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (proof : GraphRealizedDeduction.Proof assumptions conclusion) (environment : Fin count → S)
    (admitted : (index : Fin assumptions.length) → Tarski member assumptions[index.val] environment) :
    Tarski member conclusion environment := by
  apply (force_iff_tarski member conclusion ⟨⟨⟩⟩ environment).mp
  apply derivation_sound (model member) (contextualProof proof) ⟨⟨⟩⟩ environment
  intro body included
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp included
  exact (force_iff_tarski member _ ⟨⟨⟩⟩ environment).mpr (admitted ⟨index, bound⟩)

end Mettapedia.SetTheory.Profiles.CommonCoreClassicalLogic
