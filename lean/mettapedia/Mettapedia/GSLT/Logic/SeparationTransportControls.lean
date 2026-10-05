import Mettapedia.GSLT.Logic.SeparationTransport
import Lean.Elab.Tactic.Omega

/-!
# Controls for resource-predicate transport

An injective resource translation may expose new decompositions and compatible
extensions. Conversely, a map on bag occurrences preserves every separating
conjunction without being injective on the payloads. These controls distinguish
the resource laws from preservation of all program observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.SeparationTransportControls

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport

/-- A source token is implemented by two target tokens. -/
def doubleTokens : Hom Nat Nat where
  toFun := fun n => 2 * n
  map_zero := rfl
  map_add _ := by omega
  map_separate _ := trivial

theorem doubleTokens_injective : Function.Injective doubleTokens := by
  intro x y equal
  change 2 * x = 2 * y at equal
  omega

theorem doubleTokens_reflectsZero : doubleTokens.ReflectsZero := by
  intro n empty
  change 2 * n = 0 at empty
  omega

/-- The implementation of one source token can be separated into two units. -/
theorem doubleTokens_target_split :
    doubleTokens.pull (sepConj (fun n => n = 1) (fun n => n = 1)) 1 :=
  ⟨1, 1, trivial, rfl, rfl, rfl⟩

/-- Neither target unit is the image of a source resource. -/
theorem doubleTokens_source_cannot_split :
    ¬ sepConj (doubleTokens.pull (fun n => n = 1))
      (doubleTokens.pull (fun n => n = 1)) 1 := by
  rintro ⟨x, y, _, _, first, _⟩
  change 2 * x = 1 at first
  omega

theorem doubleTokens_not_liftsSplits : ¬ doubleTokens.LiftsSplits := by
  intro lifts
  have preserved := doubleTokens.pull_sepConj lifts (fun n => n = 1) (fun n => n = 1)
  have split := doubleTokens_target_split
  rw [preserved] at split
  exact doubleTokens_source_cannot_split split

/-- The source wand has no compatible extension satisfying the pulled-back
precondition, so it holds. -/
theorem doubleTokens_source_wand :
    wand (doubleTokens.pull (fun n => n = 1))
      (doubleTokens.pull (fun _ => False)) 0 := by
  intro n _ impossible
  change 2 * n = 1 at impossible
  omega

/-- A target context supplies the missing odd token and refutes that wand. -/
theorem doubleTokens_target_not_wand :
    ¬ doubleTokens.pull (wand (fun n => n = 1) (fun _ => False)) 0 := by
  intro holds
  exact holds 1 trivial rfl

theorem doubleTokens_not_liftsExtensions : ¬ doubleTokens.LiftsExtensions := by
  intro lifts
  obtain ⟨n, _, impossible⟩ := lifts 0 1 trivial
  change 2 * n = 1 at impossible
  omega

theorem doubleTokens_preserves_emp : doubleTokens.pull emp = emp :=
  doubleTokens.pull_emp doubleTokens_reflectsZero

/-- Erasing payload tags still preserves the partitioning of bag occurrences. -/
def eraseTags : Hom (Multiset Bool) (Multiset Unit) := bagMap (fun _ => ())

theorem eraseTags_preserves_sepConj (P Q : Multiset Unit → Prop) :
    eraseTags.pull (sepConj P Q) = sepConj (eraseTags.pull P) (eraseTags.pull Q) :=
  bagMap_pull_sepConj (fun _ : Bool => ()) P Q

theorem eraseTags_preserves_wand (Q R : Multiset Unit → Prop) :
    eraseTags.pull (wand Q R) = wand (eraseTags.pull Q) (eraseTags.pull R) :=
  bagMap_pull_wand (fun _ : Bool => ()) (by intro u; cases u; exact ⟨false, rfl⟩) Q R

/-- Preservation of resource connectives does not recover an erased payload. -/
theorem eraseTags_not_injective : ¬ Function.Injective eraseTags := by
  intro injective
  have same : eraseTags ({false} : Multiset Bool) = eraseTags {true} := rfl
  have equal := injective same
  have impossible : false = true := Multiset.singleton_inj.mp equal
  cases impossible

/-- Two occurrences survive the tag erasure, including their multiplicity. -/
theorem eraseTags_duplicate_count : eraseTags ({false, false} : Multiset Bool) = {(), ()} := rfl

end Mettapedia.GSLT.Logic.SeparationTransportControls
