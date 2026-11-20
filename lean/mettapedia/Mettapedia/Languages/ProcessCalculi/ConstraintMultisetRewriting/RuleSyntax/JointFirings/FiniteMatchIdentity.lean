import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MatchIdentity
import Mathlib.Data.Finset.Image

/-!
# Finite admitted representatives at an explicit CMR match identity

A finite covering list of candidate keys suffices for a finite list of actual
admitted representatives. Witness choice is noncomputable. This theorem does
not assume or supply joint admission, fresh namespaces, or a search policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)

universe uO uT uH uE uOcc uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

theorem MatchIdentity.finite_representatives (X : Frames Tm Hom) [DecidableEq O]
    (s : State Tm O) (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (candidates : List identity.Key)
    (covers : ∀ f : Firing O E P s.frame, f.Admits X s → identity.key f ∈ candidates) :
    ∃ representatives : List (Firing O E P s.frame),
      (representatives.map identity.key).Nodup ∧
      (∀ f ∈ representatives, f.Admits X s) ∧
      ∀ f : Firing O E P s.frame, f.Admits X s → identity.key f ∈ representatives.map identity.key := by
  classical
  let keys := candidates.toFinset.filter fun key =>
    ∃ f : Firing O E P s.frame, f.Admits X s ∧ identity.key f = key
  have witness : ∀ key : {key // key ∈ keys},
      ∃ f : Firing O E P s.frame, f.Admits X s ∧ identity.key f = key.val :=
    fun key => (Finset.mem_filter.mp key.property).2
  let choose := fun key : {key // key ∈ keys} => Classical.choose (witness key)
  let representatives := keys.attach.toList.map choose
  have sameKeys : representatives.map identity.key = keys.attach.toList.map Subtype.val := by
    simp only [representatives, List.map_map]
    exact List.map_congr_left fun key _ => (Classical.choose_spec (witness key)).2
  refine ⟨representatives, ?_, ?_, ?_⟩
  · rw [sameKeys]
    exact (Finset.nodup_toList _).map Subtype.val_injective
  · intro f member
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
    exact (Classical.choose_spec (witness key)).1
  · intro f admitted
    rw [sameKeys]
    have member : identity.key f ∈ keys := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (covers f admitted), f, admitted, rfl⟩
    exact List.mem_map.mpr ⟨⟨identity.key f, member⟩,
      Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
