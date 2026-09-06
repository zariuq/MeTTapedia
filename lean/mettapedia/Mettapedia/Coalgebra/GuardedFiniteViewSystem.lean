import Mettapedia.Coalgebra.CoherentFiniteViewSystem
import Mettapedia.TypeTheory.GuardedTimeModeTheory

/-!
# Guarded time and coherent finite observations

A depth-indexed finite-view system is a set-valued presheaf on the revision
mode theory: a modality from a later revision to an available earlier revision
acts by restricting observations.  Its coherent towers are exactly the global
sections of that presheaf.

For the natural-number revision category, compatibility with the canonical
one-tick guard already implies compatibility with every past-revision
modality.  Thus the local guarded law and the global inverse-limit law carry
the same information.  This connects guarded recursion to finite observation
without selecting a term calculus, equality discipline, or runtime demand
policy.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.GuardedFiniteViewSystem

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.GuardedTimeModeTheory
open Mettapedia.Coalgebra.CoherentFiniteViewSystem

universe u

/-! ## Set-valued presheaves over a mode theory -/

/-- A contravariant set-valued action of a mode theory.  A modality from a
current mode to an available mode restricts data at the current mode to data
at the available mode. -/
structure ModePresheaf (modes : ModeTheory) where
  Carrier : modes.Mode → Type u
  restrict : {current available : modes.Mode} →
    modes.Hom current available → Carrier current → Carrier available
  restrict_id : ∀ (mode : modes.Mode) (value : Carrier mode),
    restrict (modes.id mode) value = value
  restrict_comp : ∀ {first middle last : modes.Mode}
    (earlier : modes.Hom first middle) (later : modes.Hom middle last)
    (value : Carrier first),
    restrict (modes.comp earlier later) value =
      restrict later (restrict earlier value)

namespace ModePresheaf

variable {modes : ModeTheory} (presheaf : ModePresheaf.{u} modes)

/-- A compatible choice of one value at every mode. -/
structure GlobalSection where
  value : (mode : modes.Mode) → presheaf.Carrier mode
  natural : ∀ {current available : modes.Mode}
    (modality : modes.Hom current available),
    presheaf.restrict modality (value current) = value available

namespace GlobalSection

@[ext]
theorem ext {first second : presheaf.GlobalSection}
    (values : first.value = second.value) : first = second := by
  cases first
  cases second
  cases values
  rfl

end GlobalSection

end ModePresheaf

/-! ## Finite-view systems are presheaves over revision time -/

/-- Restriction of finite observations is the presheaf action of guarded
revision modalities. -/
def revisionPresheaf
    (system : FiniteViewSystem.{u}) :
    ModePresheaf.{u} revisionModes where
  Carrier := system.View
  restrict := fun modality => system.restrict modality.down
  restrict_id := system.restrict_refl
  restrict_comp := by
    intro first middle last earlier later value
    exact (system.restrict_trans later.down earlier.down value).symm

/-- A coherent finite-view tower is exactly a global section of its revision
presheaf. -/
def towerGlobalSectionEquiv
    (system : FiniteViewSystem.{u}) :
    system.Tower ≃ (revisionPresheaf system).GlobalSection where
  toFun := fun tower =>
    { value := tower.view
      natural := fun modality => tower.coherent modality.down }
  invFun := fun global =>
    { view := global.value
      coherent := fun bounded => global.natural ⟨bounded⟩ }
  left_inv := by
    intro tower
    apply FiniteViewSystem.Tower.ext
    rfl
  right_inv := by
    intro global
    apply ModePresheaf.GlobalSection.ext
    rfl

/-! ## One-tick coherence generates all coherence -/

/-- A raw family of views is locally guarded when each successor view
restricts to the preceding view along the canonical one-tick guard. -/
def GuardCoherent (system : FiniteViewSystem.{u})
    (views : (depth : Nat) → system.View depth) : Prop :=
  ∀ depth,
    (revisionPresheaf system).restrict (guard depth) (views (depth + 1)) =
      views depth

/-- Every globally coherent tower satisfies the local one-tick law. -/
theorem tower_guardCoherent
    {system : FiniteViewSystem.{u}} (tower : system.Tower) :
    GuardCoherent system tower.view := by
  intro depth
  exact tower.coherent (Nat.le_succ depth)

/-- Compatibility with the one-tick guard entails compatibility with every
past-revision modality. -/
theorem coherent_of_guard
    {system : FiniteViewSystem.{u}}
    (views : (depth : Nat) → system.View depth)
    (guarded : GuardCoherent system views)
    {earlier later : Nat} (bounded : earlier ≤ later) :
    system.restrict bounded (views later) = views earlier := by
  induction later, bounded using Nat.le_induction with
  | base =>
      exact system.restrict_refl earlier (views earlier)
  | succ later bounded inductionHypothesis =>
      have oneTick :
          system.restrict (Nat.le_succ later) (views (later + 1)) =
            views later := by
        exact guarded later
      calc
        system.restrict (Nat.le.step bounded) (views (later + 1)) =
            system.restrict bounded
              (system.restrict (Nat.le_succ later) (views (later + 1))) := by
                exact
                  (system.restrict_trans bounded (Nat.le_succ later)
                    (views (later + 1))).symm
        _ = system.restrict bounded (views later) := by
              rw [oneTick]
        _ = views earlier := inductionHypothesis

/-- A locally guarded family therefore determines a global coherent tower. -/
def towerOfGuardCoherent
    {system : FiniteViewSystem.{u}}
    (views : (depth : Nat) → system.View depth)
    (guarded : GuardCoherent system views) : system.Tower where
  view := views
  coherent := coherent_of_guard views guarded

/-- Global inverse-limit coherence and local one-tick guarded coherence are
equivalent data. -/
def towerGuardCoherentEquiv
    (system : FiniteViewSystem.{u}) :
    system.Tower ≃
      { views : (depth : Nat) → system.View depth //
        GuardCoherent system views } where
  toFun := fun tower => ⟨tower.view, tower_guardCoherent tower⟩
  invFun := fun guarded =>
    towerOfGuardCoherent guarded.1 guarded.2
  left_inv := by
    intro tower
    apply FiniteViewSystem.Tower.ext
    rfl
  right_inv := by
    intro guarded
    apply Subtype.ext
    rfl

/-! ## Stream canaries -/

/-- Positive control: ordinary finite stream prefixes obey the one-tick
guard law. -/
theorem streamPrefixes_guardCoherent {Label : Type u}
    (stream : Mettapedia.Coalgebra.StreamFinality.Stream Label) :
    GuardCoherent (streamPrefixSystem Label) (fun depth =>
      Mettapedia.Coalgebra.StreamFinality.finiteView depth stream) := by
  intro depth
  exact
    Mettapedia.Coalgebra.StreamFinality.restrictPrefix_finiteView
      (Nat.le_succ depth) stream

/-- Negative control: an arbitrary raw family of finite observations need
not satisfy even the local one-tick coherence law. -/
theorem incoherentBooleanViews_not_guardCoherent :
    ¬ GuardCoherent (streamPrefixSystem Bool)
      Mettapedia.Coalgebra.CoherentPrefixTower.Tower.incoherentBooleanViews := by
  intro guarded
  have atOne := guarded 1
  exact
    Mettapedia.Coalgebra.CoherentPrefixTower.Tower.incoherentBooleanViews_violate_restriction
      atOne

#print axioms ModePresheaf.GlobalSection.ext
#print axioms towerGlobalSectionEquiv
#print axioms coherent_of_guard
#print axioms towerGuardCoherentEquiv
#print axioms streamPrefixes_guardCoherent
#print axioms incoherentBooleanViews_not_guardCoherent

end Mettapedia.Coalgebra.GuardedFiniteViewSystem
