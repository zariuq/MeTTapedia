import Mettapedia.SetTheory.AntiFoundation.Core
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.FixedPoints

/-!
# The child-class step

A reading of a graph is a set-equality that can be the kernel of a decoration of the
quotient. Aczel's regular identifications are the post-fixed points of one step: two nodes
are related by `step R` when they have the same children up to `R`. The fixed points of
that step are the readings. The same child-class condition is a step on every relation,
not only on equivalences.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable {α : Type u}

/-- `a` and `b` have the same children up to `R`. -/
def SameChildren (edge : Edge α) (R : α → α → Prop) (a b : α) : Prop :=
  (∀ a', edge a a' → ∃ b', edge b b' ∧ R a' b') ∧
  (∀ b', edge b b' → ∃ a', edge a a' ∧ R a' b')

theorem sameChildren_mono {edge : Edge α} {R S : α → α → Prop} (h : R ≤ S) {a b : α}
    (hab : SameChildren edge R a b) : SameChildren edge S a b :=
  ⟨fun a' ha =>
      let ⟨b', hb, hR⟩ := hab.1 a' ha
      ⟨b', hb, h a' b' hR⟩,
    fun b' hb =>
      let ⟨a', ha, hR⟩ := hab.2 b' hb
      ⟨a', ha, h a' b' hR⟩⟩

theorem sameChildren_refl (edge : Edge α) (R : Setoid α) (a : α) :
    SameChildren edge (⇑R) a a :=
  ⟨fun a' ha => ⟨a', ha, R.refl' a'⟩, fun a' ha => ⟨a', ha, R.refl' a'⟩⟩

theorem sameChildren_symm (edge : Edge α) (R : Setoid α) {a b : α}
    (hab : SameChildren edge (⇑R) a b) : SameChildren edge (⇑R) b a :=
  ⟨fun b' hb =>
      let ⟨a', ha, hR⟩ := hab.2 b' hb
      ⟨a', ha, R.symm' hR⟩,
    fun a' ha =>
      let ⟨b', hb, hR⟩ := hab.1 a' ha
      ⟨b', hb, R.symm' hR⟩⟩

theorem sameChildren_trans (edge : Edge α) (R : Setoid α) {a b c : α}
    (hab : SameChildren edge (⇑R) a b) (hbc : SameChildren edge (⇑R) b c) :
    SameChildren edge (⇑R) a c :=
  ⟨fun a' ha =>
      let ⟨b', hb, hab'⟩ := hab.1 a' ha
      let ⟨c', hc, hbc'⟩ := hbc.1 b' hb
      ⟨c', hc, R.trans' hab' hbc'⟩,
    fun c' hc =>
      let ⟨b', hb, hcb⟩ := hbc.2 c' hc
      let ⟨a', ha, hba⟩ := hab.2 b' hb
      ⟨a', ha, R.trans' hba hcb⟩⟩

/-- Children up to the underlying relation of a setoid. The result is a setoid. -/
def step (edge : Edge α) : Setoid α →o Setoid α where
  toFun R :=
    { r := SameChildren edge (⇑R)
      iseqv :=
        ⟨sameChildren_refl edge R, sameChildren_symm edge R, sameChildren_trans edge R⟩ }
  monotone' _ _ h _ _ hab :=
    sameChildren_mono (Setoid.le_iff_rel_le.mp h) hab

/-- The same child-class step, on every relation. -/
def relStep (edge : Edge α) : (α → α → Prop) →o (α → α → Prop) where
  toFun R := SameChildren edge R
  monotone' _ _ h _ _ hab := sameChildren_mono h hab

@[simp] theorem step_apply (edge : Edge α) (R : Setoid α) (a b : α) :
    step edge R a b ↔ SameChildren edge (⇑R) a b := by
  unfold step
  rfl

@[simp] theorem relStep_apply (edge : Edge α) (R : α → α → Prop) (a b : α) :
    relStep edge R a b ↔ SameChildren edge R a b := by
  unfold relStep
  rfl

theorem step_monotone (edge : Edge α) : Monotone (step edge) :=
  (step edge).monotone

theorem relStep_monotone (edge : Edge α) : Monotone (relStep edge) :=
  (relStep edge).monotone

/-- A setoid lies below its child-class step exactly when it is a bisimulation. -/
theorem le_step_iff_isBisimulation (edge : Edge α) (R : Setoid α) :
    R ≤ step edge R ↔ IsBisimulation edge edge (⇑R) := by
  constructor
  · intro h a b hab
    simpa [step_apply, SameChildren] using h hab
  · intro h a b hab
    simpa [step_apply, SameChildren] using h hab

/-- Bisimilarity, packaged as the setoid already constructed for it. -/
def bisimilarSetoid (edge : Edge α) : Setoid α :=
  let B := RegularIdentification.bisimilarity edge
  ⟨B.ident, B.equiv⟩

theorem bisimilarSetoid_iff (edge : Edge α) {a b : α} :
    bisimilarSetoid edge a b ↔ Bisimilar edge edge a b :=
  Iff.rfl

/-- An edge of the quotient relates two classes when some representatives are related by `edge`. -/
def quotientEdge (edge : Edge α) (R : Setoid α) : Edge (Quotient R) :=
  fun parent member =>
    ∃ a b, Quotient.mk R a = parent ∧ Quotient.mk R b = member ∧ edge a b

/-- Membership of the quotient: a class is a member when it is a child class. -/
def quotientMem (edge : Edge α) (R : Setoid α) : MemRel (Quotient R) :=
  fun member parent => quotientEdge edge R parent member

theorem memChild_quotientMem (edge : Edge α) (R : Setoid α) :
    memChild (quotientMem edge R) = quotientEdge edge R :=
  rfl

theorem quotientEdge_mk_of_edge (edge : Edge α) (R : Setoid α) {a b : α} (h : edge a b) :
    quotientEdge edge R (Quotient.mk R a) (Quotient.mk R b) :=
  ⟨a, b, rfl, rfl, h⟩

/-- Once `R` is a bisimulation, the children of a class are the classes of the children. -/
theorem quotientEdge_mk_iff (edge : Edge α) (R : Setoid α) (hR : R ≤ step edge R) (a : α)
    (c : Quotient R) :
    quotientEdge edge R (Quotient.mk R a) c ↔ ∃ b, edge a b ∧ Quotient.mk R b = c := by
  constructor
  · intro ⟨a₀, b₀, ha₀, hb₀, h₀⟩
    have hsame : SameChildren edge (⇑R) a a₀ := by
      simpa [step_apply, SameChildren] using hR (R.symm' (Quotient.exact ha₀))
    obtain ⟨b, hb, hbb⟩ := hsame.2 b₀ h₀
    exact ⟨b, hb, (Quotient.sound hbb).trans hb₀⟩
  · intro ⟨b, hb, hc⟩
    exact hc ▸ quotientEdge_mk_of_edge edge R hb

/-- For a bisimulation, the step stays below `R` exactly when the quotient graph is weakly extensional. -/
theorem step_le_iff_quotient_weaklyExtensional (edge : Edge α) (R : Setoid α)
    (hR : R ≤ step edge R) :
    step edge R ≤ R ↔ WeaklyExtensional (quotientEdge edge R) := by
  constructor
  · intro hle p q hsame
    revert hsame
    refine Quotient.inductionOn p ?_
    intro a hsame
    revert hsame
    refine Quotient.inductionOn q ?_
    intro b hsame
    apply Quotient.sound
    apply hle
    simp only [step_apply, SameChildren]
    constructor
    · intro a' ha'
      have hchild : quotientEdge edge R (Quotient.mk R b) (Quotient.mk R a') :=
        (hsame (Quotient.mk R a')).mp (quotientEdge_mk_of_edge edge R ha')
      obtain ⟨b', hb', heq⟩ := (quotientEdge_mk_iff edge R hR b _).mp hchild
      exact ⟨b', hb', R.symm' (Quotient.exact heq)⟩
    · intro b' hb'
      have hchild : quotientEdge edge R (Quotient.mk R a) (Quotient.mk R b') :=
        (hsame (Quotient.mk R b')).mpr (quotientEdge_mk_of_edge edge R hb')
      obtain ⟨a', ha', heq⟩ := (quotientEdge_mk_iff edge R hR a _).mp hchild
      exact ⟨a', ha', Quotient.exact heq⟩
  · intro hwe a b hab
    apply Quotient.exact
    apply hwe
    intro c
    have hab' : SameChildren edge (⇑R) a b := by
      simpa [step_apply, SameChildren] using hab
    constructor
    · intro hc
      obtain ⟨a', ha', hc'⟩ := (quotientEdge_mk_iff edge R hR a c).mp hc
      obtain ⟨b', hb', hrel⟩ := hab'.1 a' ha'
      exact (quotientEdge_mk_iff edge R hR b c).mpr
        ⟨b', hb', (Quotient.sound hrel).symm.trans hc'⟩
    · intro hc
      obtain ⟨b', hb', hc'⟩ := (quotientEdge_mk_iff edge R hR b c).mp hc
      obtain ⟨a', ha', hrel⟩ := hab'.2 b' hb'
      exact (quotientEdge_mk_iff edge R hR a c).mpr ⟨a', ha', (Quotient.sound hrel).trans hc'⟩

end Mettapedia.SetTheory.AntiFoundation
