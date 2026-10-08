import Mettapedia.SetTheory.OpenTower.ZFCStages
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedFormulaComparison

/-!
# What is stable along the tower, and what changes

**Bounded formulas are absolute.** For a transitive set `U` included in a set `V`, every
bounded first-order formula of membership and equality, with parameters in `U`, has the same
truth value read in the members of `U` and in the members of `V` (`bounded_absolute`). This is
an instance of the bounded-formula comparison theorem of the contextual material logic
(`ContextualBoundedFormulaComparison.force_iff`), read at a one-point context category, where
forcing is ordinary truth (`force_iff_holds`). Earlier stages of the ω-tower are transitive
subsets of later ones (`stage_bounded_absolute`).

**Unbounded formulas change.** The first stage over `∅` consists of hereditarily finite sets
(`stage_zero_hereditarilyFinite`), so no nonempty member of it lacks a membership-greatest
element. The sentence "some nonempty set has no member-maximal element" (`weakInfinity`,
unbounded: `weakInfinity_not_bounded`) is therefore false at that stage and true at every later
stage (`weakInfinity_changes`). Its negation is true at the first stage and false at the
second, so neither preservation nor reflection holds for unbounded sentences along a stage
inclusion. The same happens for the Foundation library's axiom of infinity
(`infinity_changes`).

**The eventual theory.** For any sequence of structures for the language of set theory, the
eventual theory is the set of sentences true at all sufficiently late stages
(`eventualTheory`). It is deductively closed in Foundation's calculus (`eventualTheory_closed`;
derivations use finitely many premises) and consistent (`eventualTheory_consistent`). A
sentence is in it exactly when it holds along every free ultrafilter on the stage indices
(`mem_eventualTheory_iff_free`): it is the lower envelope of the free perspectives on the
index set. Nothing here makes it the theory of the union of the stages, or complete. For the
ω-tower it contains `𝗭𝗙𝗖` (`zfc_subset_eventualTheory`) and the axiom of infinity, which the
first stage over `∅` refutes (`infinity_changes`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Stability

open CategoryTheory
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation ZFSetDependentProducts
open InternalTower ExternalTower ZFCStages
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic ContextualBoundedFormulaComparison
open Mettapedia.TypeTheory.ContextualWitnessCover
open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

/-! ## Truth at one point -/

/-- Ordinary truth of a formula of the contextual material logic, for a membership relation on
one carrier. -/
def holds {α : Type v} (mem : α → α → Prop) : {n : ℕ} → Formula n → (Fin n → α) → Prop
  | _, .bottom, _ => False
  | _, .equal first second, e => e first = e second
  | _, .member child parent, e => mem (e child) (e parent)
  | _, .both left right, e => holds mem left e ∧ holds mem right e
  | _, .either left right, e => holds mem left e ∨ holds mem right e
  | _, .imply left right, e => holds mem left e → holds mem right e
  | _, .all body, e => ∀ x, holds mem body (Fin.cases x e)
  | _, .exist body, e => ∃ x, holds mem body (Fin.cases x e)

/-- One carrier, over the one-point context category. -/
def pointValues (α : Type v) : Discrete PUnit.{1} ⥤ Type v where
  obj _ := α
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Membership among the members of a set, as a model of the contextual material logic. -/
def stageMaterial (U : ZFSet.{u}) : Model (pointValues (Elements U)) where
  member _ x a := x.1 ∈ a.1
  member_transport := by
    intro _ _ _ _ _ h
    exact h

/-- Membership among the members of a set. -/
def memberOf (U : ZFSet.{u}) (x a : Elements U) : Prop := x.1 ∈ a.1

/-- At one point, forcing is ordinary truth. -/
theorem force_iff_holds (U : ZFSet.{u}) {n : ℕ} (φ : Formula n) (p : Discrete PUnit.{1})
    (e : Fin n → Elements U) :
    force (pointValues (Elements U)) (stageMaterial U) φ p e ↔ holds (memberOf U) φ e := by
  induction φ generalizing p with
  | bottom => exact Iff.rfl
  | equal => exact Iff.rfl
  | member => exact Iff.rfl
  | both left right ihl ihr => exact and_congr (ihl p e) (ihr p e)
  | either left right ihl ihr => exact or_congr (ihl p e) (ihr p e)
  | imply left right ihl ihr =>
    constructor
    · intro H hl
      exact (ihr p e).mp (H p (𝟙 p) ((ihl p e).mpr hl))
    · intro H t _ hl
      exact (ihr t e).mpr (H ((ihl t e).mp hl))
  | all body ih =>
    constructor
    · intro H x
      exact (ih p (extend (pointValues (Elements U)) e x)).mp (H p (𝟙 p) x)
    · intro H t _ x
      exact (ih t (extend (pointValues (Elements U)) e x)).mpr (H x)
  | exist body ih =>
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (ih p (extend (pointValues (Elements U)) e x)).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (ih p (extend (pointValues (Elements U)) e x)).mpr hx⟩

/-! ## Bounded absoluteness -/

/-- The inclusion of the members of `U` into the members of a larger set. -/
def inclusion {U V : ZFSet.{u}} (hUV : U ⊆ V) :
    NaturalHom (pointValues (Elements U)) (pointValues (Elements V)) where
  app _ x := ⟨x.1, hUV x.2⟩
  naturality _ _ := rfl

/-- A transitive set is an end segment of membership in any larger set. -/
def membershipEmbedding {U V : ZFSet.{u}} (hU : ZFSet.IsTransitive U) (hUV : U ⊆ V) :
    MembershipEmbedding (stageMaterial U) (stageMaterial V) where
  valueMap := inclusion hUV
  injective _ _ _ same := Subtype.ext (congrArg (fun z : Elements V => z.1) same)
  member_iff _ _ _ := Iff.rfl
  member_onto _ parent child belongs := ⟨⟨child.1, hU _ parent.2 belongs⟩, rfl⟩

/-- **Bounded absoluteness.** A bounded formula with parameters in a transitive set has the
same truth value among its members and among the members of any larger set. -/
theorem bounded_absolute {U V : ZFSet.{u}} (hU : ZFSet.IsTransitive U) (hUV : U ⊆ V)
    {n : ℕ} {φ : Formula n} (hφ : Bounded φ) (e : Fin n → Elements U) :
    holds (memberOf U) φ e ↔ holds (memberOf V) φ (fun i => ⟨(e i).1, hUV (e i).2⟩) := by
  have comparison := force_iff (stageMaterial U) (stageMaterial V)
    (membershipEmbedding hU hUV) hφ ⟨⟨⟩⟩ e
  exact (force_iff_holds U φ ⟨⟨⟩⟩ e).symm.trans
    (comparison.trans (force_iff_holds V φ ⟨⟨⟩⟩ _))

/-- Along the ω-tower: an earlier stage and a later one agree on bounded formulas. -/
theorem stage_bounded_absolute (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) {m n : ℕ}
    (hmn : m ≤ n) {k : ℕ} {φ : Formula k} (hφ : Bounded φ) (e : Fin k → Elements (stage h N m)) :
    holds (memberOf (stage h N m)) φ e ↔
      holds (memberOf (stage h N n)) φ (fun i => ⟨(e i).1, stage_subset_of_le h N hmn (e i).2⟩) :=
  bounded_absolute (stage_closed h N m).transitive (stage_subset_of_le h N hmn) hφ e

/-! ## Hereditarily finite sets: the first stage over the empty set -/

/-- Hereditarily finite sets. -/
abbrev HereditarilyFinite (x : ZFSet.{u}) : Prop :=
  ZFSet.Hereditarily (fun y => (y : Set ZFSet.{u}).Finite) x

theorem hereditarilyFinite_empty : HereditarilyFinite (∅ : ZFSet.{u}) :=
  ZFSet.hereditarily_iff.mpr ⟨by simp, fun y hy => absurd hy (ZFSet.notMem_empty y)⟩

theorem hereditarilyFinite_sUnion {x : ZFSet.{u}} (hx : HereditarilyFinite x) :
    HereditarilyFinite (ZFSet.sUnion x) := by
  refine ZFSet.hereditarily_iff.mpr ⟨?_, ?_⟩
  · rw [ZFSet.coe_sUnion]
    refine (hx.self.image _).sUnion ?_
    rintro t ⟨y, hy, rfl⟩
    exact (hx.mem hy).self
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := ZFSet.mem_sUnion.mp hy
    exact (hx.mem hz).mem hyz

theorem hereditarilyFinite_powerset {x : ZFSet.{u}} (hx : HereditarilyFinite x) :
    HereditarilyFinite (ZFSet.powerset x) := by
  refine ZFSet.hereditarily_iff.mpr ⟨?_, ?_⟩
  · have hfin : ((SetLike.coe : ZFSet.{u} → Set ZFSet.{u}) ⁻¹' 𝒫 (x : Set ZFSet.{u})).Finite :=
      hx.self.powerset.preimage SetLike.coe_injective.injOn
    refine hfin.subset ?_
    intro y hy
    simp only [Set.mem_preimage, Set.mem_powerset_iff]
    intro z hz
    exact ZFSet.mem_powerset.mp hy hz
  · intro y hy
    have hyx : y ⊆ x := ZFSet.mem_powerset.mp hy
    exact ZFSet.hereditarily_iff.mpr ⟨hx.self.subset (fun z hz => hyx hz),
      fun z hz => hx.mem (hyx hz)⟩

theorem hereditarilyFinite_replacement {a : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    (ha : HereditarilyFinite a) (hf : ∀ x ∈ a, HereditarilyFinite (f x)) :
    HereditarilyFinite (replacement a f) := by
  refine ZFSet.hereditarily_iff.mpr ⟨?_, ?_⟩
  · have image : (replacement a f : Set ZFSet.{u}) = f '' (a : Set ZFSet.{u}) := by
      ext y
      simp only [SetLike.mem_coe, mem_replacement, Set.mem_image]
    rw [image]
    exact ha.self.image f
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_replacement.mp hy
    exact hf x hx

/-- **The first stage over `∅` is hereditarily finite.** The hereditarily finite members of
that stage form a closed set containing `∅`, which the least closed set is included in. -/
theorem stage_zero_hereditarilyFinite (h : CofinalInaccessibles.{u}) :
    ∀ x ∈ stage h ∅ 0, HereditarilyFinite x := by
  let H : ZFSet.{u} := ZFSet.sep HereditarilyFinite (stage h ∅ 0)
  have hS := stage_closed h (∅ : ZFSet.{u}) 0
  have hH : Closed H := {
    transitive := by
      intro y hy z hz
      obtain ⟨hyS, hyF⟩ := ZFSet.mem_sep.mp hy
      exact ZFSet.mem_sep.mpr ⟨hS.transitive _ hyS hz, hyF.mem hz⟩
    union_mem := by
      intro a ha
      obtain ⟨haS, haF⟩ := ZFSet.mem_sep.mp ha
      exact ZFSet.mem_sep.mpr ⟨hS.union_mem haS, hereditarilyFinite_sUnion haF⟩
    power_mem := by
      intro a ha
      obtain ⟨haS, haF⟩ := ZFSet.mem_sep.mp ha
      exact ZFSet.mem_sep.mpr ⟨hS.power_mem haS, hereditarilyFinite_powerset haF⟩
    replacement_mem := by
      intro a ha f hf
      obtain ⟨haS, haF⟩ := ZFSet.mem_sep.mp ha
      refine ZFSet.mem_sep.mpr ⟨hS.replacement_mem haS f
        (fun x hx => (ZFSet.mem_sep.mp (hf x hx)).1), ?_⟩
      exact hereditarilyFinite_replacement haF (fun x hx => (ZFSet.mem_sep.mp (hf x hx)).2) }
  have hempty : (∅ : ZFSet.{u}) ∈ H :=
    ZFSet.mem_sep.mpr ⟨empty_mem_stage h ∅ 0, hereditarilyFinite_empty⟩
  have below : stage h ∅ 0 ⊆ H := univOf_minimal h hempty hH
  intro x hx
  exact (ZFSet.mem_sep.mp (below hx)).2

/-- A nonempty hereditarily finite set has a member that is a member of no other member. -/
theorem exists_top {z : ZFSet.{u}} (hz : HereditarilyFinite z) {x : ZFSet.{u}} (hx : x ∈ z) :
    ∃ t ∈ z, ∀ y ∈ z, t ∉ y := by
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image (z : Set ZFSet.{u}) ZFSet.rank hz.self ⟨x, hx⟩
  exact ⟨t, ht, fun y hy hty => absurd (hmax y hy) (not_le.mpr (ZFSet.rank_lt_of_mem hty))⟩

/-! ## An unbounded sentence that changes along the tower -/

/-- "Some nonempty set has no member-maximal element": `∃ z, (∃ x ∈ z) ∧ ∀ x ∈ z, ∃ y ∈ z,
x ∈ y`, with the first quantifier unbounded. -/
def weakInfinity : Formula 0 :=
  .exist (.both (.exist (.member 0 1))
    (.all (.imply (.member 0 1) (.exist (.both (.member 0 2) (.member 1 0))))))

theorem weakInfinity_not_bounded : ¬ Bounded weakInfinity := by
  intro hb
  cases hb

theorem weakInfinity_false_at_stage_zero (h : CofinalInaccessibles.{u}) :
    ¬ holds (memberOf (stage h ∅ 0)) weakInfinity Fin.elim0 := by
  rintro ⟨z, ⟨x, hx⟩, hall⟩
  obtain ⟨t, ht, htop⟩ :=
    exists_top (stage_zero_hereditarilyFinite h z.1 z.2) (x := x.1) hx
  obtain ⟨y, hyz, hty⟩ := hall ⟨t, (stage_closed h ∅ 0).transitive _ z.2 ht⟩ ht
  exact htop y.1 hyz hty

theorem weakInfinity_true_at_later_stage (h : CofinalInaccessibles.{u}) (N : ZFSet.{u})
    (n : ℕ) : holds (memberOf (stage h N (n + 1))) weakInfinity Fin.elim0 := by
  have hS := stage_closed h N n
  refine ⟨⟨stage h N n, stage_mem_succ h N n⟩,
    ⟨⟨∅, stage_subset_of_le h N (Nat.le_succ n) (empty_mem_stage h N n)⟩,
      empty_mem_stage h N n⟩, ?_⟩
  intro x hx
  refine ⟨⟨{x.1}, stage_subset_of_le h N (Nat.le_succ n) (hS.singleton_mem hx)⟩,
    hS.singleton_mem hx, ZFSet.mem_singleton.mpr rfl⟩

/-- **An unbounded sentence changes along a stage inclusion.** It is false at the first stage
over `∅` and true at the next, which contains the first. -/
theorem weakInfinity_changes (h : CofinalInaccessibles.{u}) :
    ¬ Bounded weakInfinity ∧
      ¬ holds (memberOf (stage h ∅ 0)) weakInfinity Fin.elim0 ∧
      holds (memberOf (stage h ∅ 1)) weakInfinity Fin.elim0 ∧
      stage h ∅ 0 ⊆ stage h ∅ 1 :=
  ⟨weakInfinity_not_bounded, weakInfinity_false_at_stage_zero h,
    weakInfinity_true_at_later_stage h ∅ 0, stage_subset_of_le h ∅ (Nat.zero_le 1)⟩

/-- The Foundation library's axiom of infinity fails at the first stage over `∅`. -/
theorem infinity_false_at_stage_zero (h : CofinalInaccessibles.{u}) :
    ¬ Members (stage h ∅ 0) ⊧ₘ Axiom.infinity := by
  intro holds_
  simp [models_iff, Axiom.infinity, val_isSucc_iff, SetTheory.IsEmpty] at holds_
  obtain ⟨I, hempty, hsucc⟩ := holds_
  have hS := stage_closed h (∅ : ZFSet.{u}) 0
  have h0 : (∅ : ZFSet.{u}) ∈ I.1 :=
    hempty ⟨∅, empty_mem_stage h ∅ 0⟩ (fun y hy => ZFSet.notMem_empty _ hy)
  obtain ⟨t, ht, htop⟩ := exists_top (stage_zero_hereditarilyFinite h I.1 I.2) h0
  have htS : t ∈ stage h ∅ 0 := hS.transitive _ I.2 ht
  have hnext := hsucc ⟨t, htS⟩ ht ⟨insert t t, closed_insert_mem hS htS htS⟩ (by
    intro z
    constructor
    · intro hz
      rcases ZFSet.mem_insert_iff.mp hz with same | hz'
      · exact Or.inl (Subtype.ext same)
      · exact Or.inr hz'
    · rintro (rfl | hz)
      · exact ZFSet.mem_insert _ _
      · exact ZFSet.mem_insert_of_mem _ hz)
  exact htop _ hnext (ZFSet.mem_insert t t)

/-- **The axiom of infinity changes along the tower**: false at the first stage over `∅`, true
at every later stage. -/
theorem infinity_changes (h : CofinalInaccessibles.{u}) (n : ℕ) :
    ¬ Members (stage h ∅ 0) ⊧ₘ Axiom.infinity ∧ Members (stage h ∅ (n + 1)) ⊧ₘ Axiom.infinity := by
  refine ⟨infinity_false_at_stage_zero h, ?_⟩
  have := stage_models_zfc h ∅ n
  exact models_of_subtheory (U := 𝗭𝗙) this |>.models_set
    (ZermeloFraenkel.axiom_of_infinity)

/-! ## The eventual theory -/

section Eventual

variable (M : ℕ → Type v) [∀ n, SetStructure (M n)] [∀ n, Nonempty (M n)]

/-- The eventual theory: the sentences true at all sufficiently late stages. -/
def eventualTheory : Theory ℒₛₑₜ := {φ | ∀ᶠ n in Filter.atTop, M n ⊧ₘ φ}

theorem mem_eventualTheory {φ : Sentence ℒₛₑₜ} :
    φ ∈ eventualTheory M ↔ ∀ᶠ n in Filter.atTop, M n ⊧ₘ φ :=
  Iff.rfl

/-- Finitely many eventual premises prove only eventual sentences. -/
theorem eventualTheory_of_finite (s : Finset (Sentence ℒₛₑₜ))
    (hs : (s : Set (Sentence ℒₛₑₜ)) ⊆ eventualTheory M) {σ : Sentence ℒₛₑₜ}
    (hσ : (s : Theory ℒₛₑₜ) ⊢ σ) : σ ∈ eventualTheory M := by
  have hall : ∀ᶠ n in Filter.atTop, ∀ φ ∈ s, M n ⊧ₘ φ :=
    (Filter.eventually_all_finset s).mpr (fun φ hφ => hs hφ)
  filter_upwards [hall] with n hn
  exact models_of_provable ⟨fun {φ} hφ => hn φ hφ⟩ hσ

/-- **The eventual theory is deductively closed**: a derivation uses finitely many premises. -/
theorem eventualTheory_closed {σ : Sentence ℒₛₑₜ} (hσ : eventualTheory M ⊢ σ) :
    σ ∈ eventualTheory M := by
  obtain ⟨⟨s, hs⟩, hsσ⟩ := Theory.compact hσ
  exact eventualTheory_of_finite M s hs hsσ

/-- **The eventual theory is consistent.** -/
theorem eventualTheory_consistent : Entailment.Consistent (eventualTheory M) := by
  apply Entailment.consistent_iff_unprovable_bot.mpr
  intro hbot
  obtain ⟨n, hn⟩ := (eventualTheory_closed M hbot).exists
  simp at hn

/-- **The eventual theory is the lower envelope of the free perspectives on the stages**: a
sentence is eventually true exactly when it holds along every free ultrafilter of indices. -/
theorem mem_eventualTheory_iff_free {φ : Sentence ℒₛₑₜ} :
    φ ∈ eventualTheory M ↔
      ∀ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ Filter.cofinite → {n | M n ⊧ₘ φ} ∈ 𝒰 := by
  rw [mem_eventualTheory, ← Nat.cofinite_eq_atTop]
  exact Filter.mem_iff_ultrafilter

end Eventual

/-- For the ω-tower, `𝗭𝗙𝗖` is part of the eventual theory. -/
theorem zfc_subset_eventualTheory (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    (𝗭𝗙𝗖 : Theory ℒₛₑₜ) ⊆ eventualTheory (fun n => Members (stage h N n)) := by
  intro φ hφ
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (stage_models_zfc h N k).models_set hφ

/-- The axiom of infinity is eventual along the ω-tower over `∅`, but false at its first
stage. -/
theorem infinity_eventual_not_initial (h : CofinalInaccessibles.{u}) :
    Axiom.infinity ∈ eventualTheory (fun n => Members (stage h ∅ n)) ∧
      ¬ Members (stage h ∅ 0) ⊧ₘ Axiom.infinity := by
  refine ⟨Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩, infinity_false_at_stage_zero h⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (infinity_changes h k).2

#print axioms force_iff_holds
#print axioms bounded_absolute
#print axioms stage_bounded_absolute
#print axioms stage_zero_hereditarilyFinite
#print axioms weakInfinity_changes
#print axioms infinity_changes
#print axioms eventualTheory_closed
#print axioms eventualTheory_consistent
#print axioms mem_eventualTheory_iff_free
#print axioms zfc_subset_eventualTheory
#print axioms infinity_eventual_not_initial

end Mettapedia.SetTheory.OpenTower.Stability
