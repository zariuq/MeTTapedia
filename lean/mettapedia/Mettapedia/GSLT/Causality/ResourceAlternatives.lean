import Mettapedia.GSLT.Causality.ResourceProduct

/-!
# Alternative interactions and inert resource frames

Two independently formed systems on the same resources retain disjoint rule
sites. An enabled instance belongs to exactly its authored system; the combined
rewrite relation is the union of the two operational relations. Unlike a
synchronous product, an alternative step fires one of the two instances.

An injectively embedded system may also run beside resources of another kind.
Those resources neither enable an embedded instance nor change its firing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.System

universe u v w z

variable {R : Type u} (first second : System.{u, v} R)

omit second in
/-- Raising rule sites and their fibres retains every authored instance. -/
def raise : System.{u, max v z} R where
  Site := ULift.{z} first.Site
  Instance := fun site => ULift.{z} (first.Instance site.down)
  consume := fun firing => first.consume firing.down
  read := fun firing => first.read firing.down
  produce := fun firing => first.produce firing.down

omit second in
@[simp] theorem raise_enables (resources : Multiset R)
    {site : first.Site} (firing : first.Instance site) :
    first.raise.{u, v, z}.Enables resources (site := ⟨site⟩) ⟨firing⟩ ↔
      first.Enables resources firing := Iff.rfl

omit second in
@[simp] theorem raise_fire [DecidableEq R] (resources : Multiset R)
    {site : first.Site} (firing : first.Instance site) :
    first.raise.{u, v, z}.fire resources (site := ⟨site⟩) ⟨firing⟩ =
      first.fire resources firing := rfl

omit second in
theorem raise_rewrites_iff [DecidableEq R] (source target : Multiset R) :
    first.raise.{u, v, z}.theory.rewrites source target ↔ first.theory.rewrites source target := by
  constructor
  · rintro ⟨⟨site⟩, ⟨firing⟩, enabled, endpoint⟩
    exact ⟨site, firing, enabled, endpoint⟩
  · rintro ⟨site, firing, enabled, endpoint⟩
    exact ⟨⟨site⟩, ⟨firing⟩, enabled, endpoint⟩

def alternatives : System.{u, v} R where
  Site := first.Site ⊕ second.Site
  Instance := Sum.elim first.Instance second.Instance
  consume := fun {site} => match site with
    | .inl _ => first.consume
    | .inr _ => second.consume
  read := fun {site} => match site with
    | .inl _ => first.read
    | .inr _ => second.read
  produce := fun {site} => match site with
    | .inl _ => first.produce
    | .inr _ => second.produce

@[simp] theorem alternatives_enables_left (resources : Multiset R)
    {site : first.Site} (firing : first.Instance site) :
    (first.alternatives second).Enables resources (site := .inl site) firing ↔
      first.Enables resources firing := Iff.rfl

@[simp] theorem alternatives_enables_right (resources : Multiset R)
    {site : second.Site} (firing : second.Instance site) :
    (first.alternatives second).Enables resources (site := .inr site) firing ↔
      second.Enables resources firing := Iff.rfl

section Decidable

variable [DecidableEq R]

@[simp] theorem alternatives_fire_left (resources : Multiset R)
    {site : first.Site} (firing : first.Instance site) :
    (first.alternatives second).fire resources (site := .inl site) firing =
      first.fire resources firing := rfl

@[simp] theorem alternatives_fire_right (resources : Multiset R)
    {site : second.Site} (firing : second.Instance site) :
    (first.alternatives second).fire resources (site := .inr site) firing =
      second.fire resources firing := rfl

theorem alternatives_rewrites_iff (source target : Multiset R) :
    (first.alternatives second).theory.rewrites source target ↔
      first.theory.rewrites source target ∨ second.theory.rewrites source target := by
  constructor
  · rintro ⟨site, firing, enabled, endpoint⟩
    cases site with
    | inl site => exact .inl ⟨site, firing, enabled, endpoint⟩
    | inr site => exact .inr ⟨site, firing, enabled, endpoint⟩
  · rintro (⟨site, firing, enabled, endpoint⟩ | ⟨site, firing, enabled, endpoint⟩)
    · exact ⟨.inl site, firing, enabled, endpoint⟩
    · exact ⟨.inr site, firing, enabled, endpoint⟩

end Decidable

section InertFrame

variable {T : Type w}

omit second in
theorem map_inl_enables_frame (resources : Multiset R) (frame : Multiset T)
    {site : first.Site} (firing : first.Instance site) :
    (first.map (Sum.inl : R → R ⊕ T)).Enables (marking resources frame) firing ↔
      first.Enables resources firing := by
  change (first.consume firing).map Sum.inl + (first.read firing).map Sum.inl ≤
    marking resources frame ↔ _
  have exposed : (first.consume firing).map (Sum.inl : R → R ⊕ T) +
      (first.read firing).map Sum.inl = marking (first.consume firing + first.read firing) 0 := by
    simp [marking, Multiset.disjSum, Multiset.map_add]
  rw [exposed, marking_le_iff]
  exact and_iff_left (zero_le : (0 : Multiset T) ≤ frame)

omit second in
theorem map_inl_fire_frame [DecidableEq R] [DecidableEq T]
    (resources : Multiset R) (frame : Multiset T)
    {site : first.Site} (firing : first.Instance site) :
    (first.map (Sum.inl : R → R ⊕ T)).fire (marking resources frame) firing =
      marking (first.fire resources firing) frame := by
  change marking resources frame - (first.consume firing).map Sum.inl +
      (first.produce firing).map Sum.inl = _
  have consume : (first.consume firing).map (Sum.inl : R → R ⊕ T) =
      marking (first.consume firing) 0 := by simp [marking, Multiset.disjSum]
  have produce : (first.produce firing).map (Sum.inl : R → R ⊕ T) =
      marking (first.produce firing) 0 := by simp [marking, Multiset.disjSum]
  rw [consume, produce, marking_sub, marking_add]
  simp only [tsub_zero, add_zero, fire]

end InertFrame

end Mettapedia.GSLT.Causality.ResourceInteraction.System
