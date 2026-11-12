import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# Payload-relative laws for Cesta's optional region debug notifications

These are interval specifications after admission of the native backing,
address-width and ASan-granule conditions. They model the added notification
API, not C execution, ASan internals or allocation-incarnation provenance.
The real allocator supplies its current live bounds; the adapter stores no
ledger. This file is development evidence and is never a Cesta dependency.
-/

namespace Mettapedia.GSLT.LanguageDef.RegionDebug

set_option autoImplicit false

abbrev Shadow := Nat → Bool

def setInterval (shadow : Shadow) (begin finish : Nat) (value : Bool) : Shadow :=
  fun address => if begin ≤ address ∧ address < finish then value else shadow address

def initializeRegion (capacity live : Nat) (shadow : Shadow) : Option Shadow :=
  if live ≤ capacity then
    some (fun address => if address < capacity then decide (address < live) else shadow address)
  else none

def acquire (capacity oldLive newLive : Nat) (shadow : Shadow) : Option Shadow :=
  if oldLive ≤ newLive ∧ newLive ≤ capacity then some (setInterval shadow oldLive newLive true)
  else none

def reset (capacity oldLive newLive : Nat) (shadow : Shadow) : Option Shadow :=
  if newLive ≤ oldLive ∧ oldLive ≤ capacity then some (setInterval shadow newLive oldLive false)
  else none

def release (capacity : Nat) (shadow : Shadow) : Shadow := setInterval shadow 0 capacity false

theorem interval_outside (shadow : Shadow) (begin finish address : Nat) (value : Bool)
    (outside : address < begin ∨ finish ≤ address) :
    setInterval shadow begin finish value address = shadow address := by
  exact if_neg (by omega)

theorem interval_inside (shadow : Shadow) (begin finish address : Nat) (value : Bool)
    (inside : begin ≤ address ∧ address < finish) :
    setInterval shadow begin finish value address = value := by
  simp [setInterval, inside]

theorem initialize_live_prefix {capacity live : Nat} {before after : Shadow}
    (accepted : initializeRegion capacity live before = some after) {address : Nat}
    (liveAddress : address < live) : after address = true := by
  unfold initializeRegion at accepted
  split at accepted
  · rename_i bounds
    cases Option.some.inj accepted
    simp [show address < capacity by omega, liveAddress]
  · contradiction

theorem initialize_dead_suffix {capacity live : Nat} {before after : Shadow}
    (accepted : initializeRegion capacity live before = some after) {address : Nat}
    (deadAddress : live ≤ address ∧ address < capacity) : after address = false := by
  unfold initializeRegion at accepted
  split at accepted
  · cases Option.some.inj accepted
    simp [deadAddress.2, show ¬address < live by omega]
  · contradiction

theorem acquire_preserves_prefix {capacity oldLive newLive : Nat} {before after : Shadow}
    (accepted : acquire capacity oldLive newLive before = some after) {address : Nat}
    (inPrefix : address < oldLive) : after address = before address := by
  unfold acquire at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact interval_outside before oldLive newLive address true (Or.inl inPrefix)
  · contradiction

theorem acquire_new_interval {capacity oldLive newLive : Nat} {before after : Shadow}
    (accepted : acquire capacity oldLive newLive before = some after) {address : Nat}
    (allocated : oldLive ≤ address ∧ address < newLive) : after address = true := by
  unfold acquire at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact interval_inside before oldLive newLive address true allocated
  · contradiction

theorem reset_preserves_prefix {capacity oldLive newLive : Nat} {before after : Shadow}
    (accepted : reset capacity oldLive newLive before = some after) {address : Nat}
    (inPrefix : address < newLive) : after address = before address := by
  unfold reset at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact interval_outside before newLive oldLive address false (Or.inl inPrefix)
  · contradiction

theorem reset_released_suffix {capacity oldLive newLive : Nat} {before after : Shadow}
    (accepted : reset capacity oldLive newLive before = some after) {address : Nat}
    (released : newLive ≤ address ∧ address < oldLive) : after address = false := by
  unfold reset at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact interval_inside before newLive oldLive address false released
  · contradiction

theorem reset_outside_payload {capacity oldLive newLive : Nat} {before after : Shadow}
    (accepted : reset capacity oldLive newLive before = some after) {address : Nat}
    (outside : capacity ≤ address) : after address = before address := by
  unfold reset at accepted
  split at accepted
  · rename_i bounds
    cases Option.some.inj accepted
    exact interval_outside before newLive oldLive address false (Or.inr (by omega))
  · contradiction

theorem reset_empty (capacity live : Nat) (shadow : Shadow) (bounds : live ≤ capacity) :
    reset capacity live live shadow = some shadow := by
  simp only [reset, bounds, le_refl, and_self, ↓reduceIte]
  congr 1
  funext address
  exact if_neg (by omega)

theorem reset_invalid (capacity oldLive newLive : Nat) (shadow : Shadow)
    (invalid : oldLive < newLive ∨ capacity < oldLive) :
    reset capacity oldLive newLive shadow = none := by
  exact if_neg (by omega)

theorem release_payload (capacity : Nat) (shadow : Shadow) {address : Nat}
    (inside : address < capacity) : release capacity shadow address = false := by
  exact interval_inside shadow 0 capacity address false ⟨Nat.zero_le _, inside⟩

theorem release_frame (capacity : Nat) (shadow : Shadow) {address : Nat}
    (outside : capacity ≤ address) : release capacity shadow address = shadow address := by
  exact interval_outside shadow 0 capacity address false (Or.inr outside)

end Mettapedia.GSLT.LanguageDef.RegionDebug
