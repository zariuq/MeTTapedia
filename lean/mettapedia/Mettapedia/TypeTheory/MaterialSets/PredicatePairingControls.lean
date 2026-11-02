import Mettapedia.TypeTheory.MaterialSets.PredicatePairing
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Faithful pairing controls and representation boundaries

Ordinary natural pairing is onto; a tagged natural pairing leaves code zero
outside its image. Both satisfy the same projection laws. The tagged control
separates exact admission from mere inhabitance. A finite carrier with more
than one element cannot support these total homogeneous pair projections.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Pairing.Controls

def natural : Pairing Nat where
  pair := Nat.pair
  fst value := value.unpair.1
  snd value := value.unpair.2
  fst_pair first second := by simp only [Nat.unpair_pair]
  snd_pair first second := by simp only [Nat.unpair_pair]

theorem natural_onto : Function.Surjective (fun value : Nat × Nat => natural.pair value.1 value.2) := by
  intro value
  exact ⟨value.unpair, Nat.pair_unpair value⟩

theorem natural_guard_exact (domain : Nat → Prop) (family : Nat → Nat → Prop) (value : Nat) :
    natural.SigmaGuard domain family value ↔ natural.ProjectionGuard domain family value :=
  natural.sigmaGuard_iff_projection_of_surjective natural_onto domain family value

theorem natural_zero_is_pair : natural.pair 0 0 = 0 := by decide +kernel

def tagged : Pairing Nat where
  pair first second := Nat.pair first second + 1
  fst value := value.pred.unpair.1
  snd value := value.pred.unpair.2
  fst_pair first second := by simp only [Nat.pred_succ, Nat.unpair_pair]
  snd_pair first second := by simp only [Nat.pred_succ, Nat.unpair_pair]

theorem tagged_zero_not_image : ¬ tagged.InImage 0 := by
  rintro ⟨first, second, impossible⟩
  change Nat.pair first second + 1 = 0 at impossible
  omega

theorem projection_admits_extra_code : tagged.ProjectionGuard (fun _ => True) (fun _ _ => True) 0 :=
  ⟨True.intro, True.intro⟩

theorem exact_guard_refuses_extra_code : ¬ tagged.SigmaGuard (fun _ => True) (fun _ _ => True) 0 := by
  intro valid
  exact tagged_zero_not_image ((tagged.sigmaGuard_iff _ _ 0).mp valid).1

theorem exact_guard_inhabited : tagged.SigmaGuard (fun _ => True) (fun _ _ => True) (tagged.pair 0 0) :=
  ⟨0, 0, rfl, True.intro, True.intro⟩

theorem wrong_reconstruction : tagged.pair (tagged.fst 0) (tagged.snd 0) ≠ 0 := by decide +kernel

theorem empty_fibre_refused (value : Nat) : ¬ tagged.SigmaGuard (fun _ => True) (fun _ _ => False) value :=
  tagged.empty_fibres (fun _ _ _ impossible => impossible) value

theorem finite_card_atMost_one {S : Type} [Fintype S] (pairing : Pairing S) : Fintype.card S ≤ 1 := by
  have bound := Fintype.card_le_of_injective (fun value : S × S => pairing.pair value.1 value.2) pairing.pair_injective
  simp only [Fintype.card_prod] at bound
  by_contra larger
  have two : 2 ≤ Fintype.card S := by omega
  have growth := Nat.mul_le_mul_right (Fintype.card S) two
  have collapse := growth.trans bound
  omega

theorem boolean_pairing_refused : ¬ Nonempty (Pairing Bool) := by
  rintro ⟨pairing⟩
  have impossible := finite_card_atMost_one pairing
  have count : Fintype.card Bool = 2 := by decide
  omega

#print axioms exact_guard_refuses_extra_code
#print axioms boolean_pairing_refused

end Mettapedia.TypeTheory.MaterialSets.Pairing.Controls
