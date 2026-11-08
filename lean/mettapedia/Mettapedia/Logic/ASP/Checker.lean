import Mettapedia.Logic.ASP.Kernel
import Mathlib.Data.List.Sublists

/-!
# The executable stable-model checker and enumerator

Everything here computes on `Finset` and `List`, and is proved equal to the
semantics of `Kernel` on `Set`.

* `Program.stepFin` is the immediate-consequence step (`coe_stepFin`).
* `Program.lfpFin P N` iterates `stepFin · N` from `∅` as many times as there
  are rule heads. That many steps reach the fixed point
  (`Finset.iterate_card_fixed`, an instance of `iterate_fixed_of_measure`), so it
  is the least fixed point (`coe_lfpFin`, by `iterate_eq_lfp`).
* `Program.reduct P M` is the Gelfond–Lifschitz reduct, a positive program
  (`reduct_isPositive`) whose operator reads negation against `M`
  (`step_reduct`). Hence `M` is stable exactly when it is the least model of
  its reduct (`stable_iff_leastModel_reduct`).
* `Program.isStable P M` computes the reduct, its least model, and compares
  (`isStable_iff`). `Program.isSupported` is one step and a comparison
  (`isSupported_iff`).
* `Program.stableModelList` enumerates the sublists of the program's head atoms
  and keeps the stable ones. It is sound (`stable_of_mem_stableModelList`),
  complete (`exists_mem_stableModelList`) and repeats no model
  (`stableModelList_nodup`, `stableModelList_toFinset_injective`).
  `Program.stableModels` is the same answer as a finite set of finite sets
  (`mem_stableModels`, `stable_iff_mem_stableModels`).
* `Program.loopCheck` and `Program.externalSupportFin` decide loops and
  external support (`loopCheck_iff`, `externalSupportFin_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

/-! ## Finite iteration reaches a fixed point -/

/-- An increasing iteration whose strict steps raise a bounded natural measure is fixed after
`B` steps, where `B` bounds the measure. -/
theorem iterate_fixed_of_measure {α : Type*} [PartialOrder α] {f : α → α} (mono : Monotone f)
    {p : α} (start : p ≤ f p) (μ : α → ℕ) (B : ℕ)
    (grows : ∀ k, f^[k] p < f^[k + 1] p → μ (f^[k] p) < μ (f^[k + 1] p))
    (bound : ∀ k, μ (f^[k] p) ≤ B) : f (f^[B] p) = f^[B] p := by
  have chain : ∀ k, f^[k] p ≤ f^[k + 1] p := by
    intro k
    induction k with
    | zero => exact start
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' f (k + 1)]
      exact mono ih
  have next : ∀ k, f^[k + 1] p = f (f^[k] p) := fun k => Function.iterate_succ_apply' f k p
  have climbs : ∀ k, f (f^[k] p) = f^[k] p ∨ k + 1 ≤ μ (f^[k + 1] p) := by
    intro k
    induction k with
    | zero =>
      by_cases fixed : f (f^[0] p) = f^[0] p
      · exact Or.inl fixed
      · right
        have strict : f^[0] p < f^[0 + 1] p :=
          lt_of_le_of_ne (chain 0) fun same => fixed (by rw [← next, same])
        have := grows 0 strict
        omega
    | succ k ih =>
      by_cases fixed : f (f^[k + 1] p) = f^[k + 1] p
      · exact Or.inl fixed
      · right
        rcases ih with before | count
        · exfalso
          apply fixed
          rw [next, before, before]
        · have strict : f^[k + 1] p < f^[k + 1 + 1] p :=
            lt_of_le_of_ne (chain (k + 1)) fun same => fixed (by rw [← next, same])
          have := grows (k + 1) strict
          omega
  rcases climbs B with fixed | count
  · exact fixed
  · exfalso
    have := bound (B + 1)
    omega

/-- A monotone operator on finite sets with all values inside `H` is fixed after `|H|` steps
from `∅`. -/
theorem Finset.iterate_card_fixed {α : Type*} [DecidableEq α] {f : Finset α → Finset α}
    (mono : Monotone f) (H : Finset α) (bound : ∀ I, f I ⊆ H) :
    f (f^[H.card] ∅) = f^[H.card] ∅ := by
  apply iterate_fixed_of_measure mono (Finset.empty_subset _) Finset.card H.card
    (fun _ strict => Finset.card_lt_card strict)
  intro k
  cases k with
  | zero => simp
  | succ k =>
    rw [Function.iterate_succ_apply']
    exact Finset.card_le_card (bound _)

/-- A fixed iterate below a least fixed point, along a map that intertwines the steps, is that
least fixed point. -/
theorem iterate_eq_lfp {α β : Type*} [CompleteLattice β] (f : α → α) (F : β →o β) (c : α → β)
    (intertwines : ∀ q, c (f q) = F (c q)) {p : α} (start : c p ≤ F.lfp) (n : ℕ)
    (fixed : f (f^[n] p) = f^[n] p) : c (f^[n] p) = F.lfp := by
  apply le_antisymm
  · have below : ∀ k, c (f^[k] p) ≤ F.lfp := by
      intro k
      induction k with
      | zero => exact start
      | succ k ih =>
        rw [Function.iterate_succ_apply', intertwines]
        exact OrderHom.map_le_lfp _ ih
    exact below n
  · exact OrderHom.lfp_le_fixed _ (by rw [← intertwines, fixed])

variable {A : Type u} [DecidableEq A]

namespace Rule

/-- The executable body test. -/
def holdsFin (r : Rule A) (I N : Finset A) : Bool :=
  r.pos.all (· ∈ I) && r.neg.all (· ∉ N)

theorem holdsFin_iff (r : Rule A) (I N : Finset A) : r.holdsFin I N = true ↔ r.Holds ↑I ↑N := by
  simp [holdsFin, Holds]

end Rule

namespace Program

variable (P : Program A)

/-- The atoms some rule can derive. -/
def heads : Finset A := (P.map Rule.head).toFinset

theorem coe_heads : (↑P.heads : Set A) = P.headSet := by
  ext a
  simp [heads, headSet]

/-- The executable immediate-consequence step. -/
def stepFin (I N : Finset A) : Finset A :=
  ((P.filter fun r => r.holdsFin I N).map Rule.head).toFinset

theorem coe_stepFin (I N : Finset A) : (↑(P.stepFin I N) : Set A) = P.step ↑I ↑N := by
  ext a
  simp only [Finset.mem_coe, stepFin, List.mem_toFinset, List.mem_map, List.mem_filter, step,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, ⟨hr, holds⟩, rfl⟩
    exact ⟨r, hr, rfl, (r.holdsFin_iff I N).mp holds⟩
  · rintro ⟨r, hr, rfl, holds⟩
    exact ⟨r, ⟨hr, (r.holdsFin_iff I N).mpr holds⟩, rfl⟩

theorem stepFin_subset_heads (I N : Finset A) : P.stepFin I N ⊆ P.heads := by
  rw [← Finset.coe_subset, coe_stepFin, coe_heads]
  exact P.step_subset_headSet _ _

theorem stepFin_mono (N : Finset A) : Monotone fun I => P.stepFin I N := by
  intro I I' h
  rw [← Finset.coe_subset, coe_stepFin, coe_stepFin]
  exact P.step_mono (Finset.coe_subset.mpr h) le_rfl

/-- The least model of the reduct by `N`, by Kleene iteration from `∅`, `|heads|` times. -/
def lfpFin (N : Finset A) : Finset A := (fun I => P.stepFin I N)^[P.heads.card] ∅

theorem stepFin_lfpFin (N : Finset A) : P.stepFin (P.lfpFin N) N = P.lfpFin N :=
  Finset.iterate_card_fixed (P.stepFin_mono N) P.heads (fun I => P.stepFin_subset_heads I N)

theorem coe_lfpFin (N : Finset A) : (↑(P.lfpFin N) : Set A) = P.glOp ↑N :=
  iterate_eq_lfp (fun I => P.stepFin I N) (P.reductOp ↑N) (fun I : Finset A => (↑I : Set A))
    (fun I => P.coe_stepFin I N) (by simp) _ (P.stepFin_lfpFin N)

theorem lfpFin_subset_heads (N : Finset A) : P.lfpFin N ⊆ P.heads := by
  rw [← Finset.coe_subset, coe_lfpFin, coe_heads]
  exact P.glOp_subset_headSet _

/-! ## The reduct -/

/-- **The Gelfond–Lifschitz reduct** by `M`: delete every rule with a negated atom in `M`, and
erase the negated atoms of the remaining rules. -/
def reduct (M : Finset A) : Program A :=
  (P.filter fun r => r.neg.all (· ∉ M)).map fun r => ⟨r.head, r.pos, []⟩

theorem reduct_isPositive (M : Finset A) : (P.reduct M).IsPositive := by
  intro r hr
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr
  rfl

/-- The reduct's operator reads negation against `M`, whatever it is given. -/
theorem step_reduct (M : Finset A) (I N : Set A) : (P.reduct M).step I N = P.step I ↑M := by
  ext a
  constructor
  · rintro ⟨_, hr, head, holds⟩
    obtain ⟨r, member, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hr, blocked⟩ := List.mem_filter.mp member
    simp only [List.all_eq_true, decide_eq_true_eq] at blocked
    exact ⟨r, hr, head, holds.1, fun b hb hbM => blocked b hb hbM⟩
  · rintro ⟨r, hr, head, pos, blocked⟩
    refine ⟨⟨r.head, r.pos, []⟩, List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, ?_⟩, rfl⟩, head, pos,
      fun b hb => by simp at hb⟩
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact fun b hb hbM => blocked b hb hbM

theorem glOp_reduct (M : Finset A) (N : Set A) : (P.reduct M).glOp N = P.glOp ↑M := by
  unfold glOp
  congr 1
  apply OrderHom.ext
  funext I
  exact P.step_reduct M I N

/-- **Stability is the Gelfond–Lifschitz condition**: `M` is the least model of its reduct. -/
theorem stable_iff_leastModel_reduct (M : Finset A) : P.Stable ↑M ↔ ↑M = (P.reduct M).leastModel := by
  rw [leastModel, glOp_reduct]
  rfl

/-- The least model of a program read without negation, computed. -/
def leastModelFin : Finset A := P.lfpFin ∅

theorem coe_leastModelFin : (↑P.leastModelFin : Set A) = P.leastModel := by
  rw [leastModelFin, coe_lfpFin, Finset.coe_empty]
  rfl

/-! ## The checkers -/

/-- **The stable-model checker**: compute the reduct, its least model, and compare. -/
def isStable (M : Finset A) : Bool := decide ((P.reduct M).leastModelFin = M)

theorem isStable_iff (M : Finset A) : P.isStable M = true ↔ P.Stable ↑M := by
  rw [isStable, decide_eq_true_iff, stable_iff_leastModel_reduct, ← coe_leastModelFin, eq_comm,
    Finset.coe_inj]

/-- The supported-model checker: one step and a comparison. -/
def isSupported (M : Finset A) : Bool := decide (P.stepFin M M = M)

theorem isSupported_iff (M : Finset A) : P.isSupported M = true ↔ P.Supported ↑M := by
  rw [isSupported, decide_eq_true_iff, Supported, ← coe_stepFin, Finset.coe_inj]

/-! ## The enumerator -/

/-- The head atoms, each once, in order of first occurrence. -/
def atomList : List A := (P.map Rule.head).dedup

theorem atomList_nodup : P.atomList.Nodup := List.nodup_dedup _

theorem mem_atomList {a : A} : a ∈ P.atomList ↔ a ∈ P.headSet := by
  simp [atomList, headSet]

/-- Every set of head atoms is the set of some candidate sublist. -/
theorem exists_sublist (S : Set A) (within : S ⊆ P.headSet) :
    ∃ l ∈ P.atomList.sublists, (↑l.toFinset : Set A) = S := by
  classical
  refine ⟨P.atomList.filter fun a => decide (a ∈ S), List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext a
  simp only [List.coe_toFinset, List.mem_filter, decide_eq_true_eq, Set.mem_ofPred_eq, mem_atomList]
  exact ⟨And.right, fun h => ⟨within h, h⟩⟩

/-- Two candidate sublists with the same atoms are equal. -/
theorem sublist_eq_of_toFinset_eq : ∀ {L l₁ l₂ : List A}, L.Nodup → List.Sublist l₁ L → List.Sublist l₂ L →
    l₁.toFinset = l₂.toFinset → l₁ = l₂
  | [], _, _, _, s₁, s₂, _ => by rw [List.sublist_nil.mp s₁, List.sublist_nil.mp s₂]
  | x :: L, l₁, l₂, nodup, s₁, s₂, same => by
    obtain ⟨notMem, nodup⟩ := List.nodup_cons.mp nodup
    have absent : ∀ {l : List A}, List.Sublist l L → x ∉ l := fun s h => notMem (s.subset h)
    cases s₁ with
    | cons _ s₁ =>
      cases s₂ with
      | cons _ s₂ => exact sublist_eq_of_toFinset_eq nodup s₁ s₂ same
      | cons_cons _ s₂ =>
        exact absurd (List.mem_toFinset.mp (same ▸ List.mem_toFinset.mpr List.mem_cons_self)) (absent s₁)
    | cons_cons _ s₁ =>
      cases s₂ with
      | cons _ s₂ =>
        exact absurd (List.mem_toFinset.mp (same.symm ▸ List.mem_toFinset.mpr List.mem_cons_self))
          (absent s₂)
      | cons_cons _ s₂ =>
        congr 1
        apply sublist_eq_of_toFinset_eq nodup s₁ s₂
        ext a
        have h := Finset.ext_iff.mp same a
        simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at h ⊢
        constructor
        · intro ha
          rcases h.mp (Or.inr ha) with rfl | hb
          · exact absurd ha (absent s₁)
          · exact hb
        · intro hb
          rcases h.mpr (Or.inr hb) with rfl | ha
          · exact absurd hb (absent s₂)
          · exact ha

/-- **The enumerator**: every candidate set of head atoms, kept when it is stable. -/
def stableModelList : List (List A) := P.atomList.sublists.filter fun l => P.isStable l.toFinset

theorem stable_of_mem_stableModelList {l : List A} (h : l ∈ P.stableModelList) :
    P.Stable ↑l.toFinset :=
  (P.isStable_iff _).mp (List.mem_filter.mp h).2

/-- **Completeness of the enumerator**: every stable model is listed. -/
theorem exists_mem_stableModelList {S : Set A} (h : P.Stable S) :
    ∃ l ∈ P.stableModelList, (↑l.toFinset : Set A) = S := by
  obtain ⟨l, hl, same⟩ := P.exists_sublist S h.subset_headSet
  refine ⟨l, List.mem_filter.mpr ⟨hl, (P.isStable_iff _).mpr (same ▸ h)⟩, same⟩

theorem stableModelList_nodup : P.stableModelList.Nodup :=
  (List.nodup_sublists.mpr P.atomList_nodup).filter _

/-- No model is listed twice, even up to order. -/
theorem stableModelList_toFinset_injective {l₁ l₂ : List A} (h₁ : l₁ ∈ P.stableModelList)
    (h₂ : l₂ ∈ P.stableModelList) (same : l₁.toFinset = l₂.toFinset) : l₁ = l₂ :=
  sublist_eq_of_toFinset_eq P.atomList_nodup (List.mem_sublists.mp (List.mem_filter.mp h₁).1)
    (List.mem_sublists.mp (List.mem_filter.mp h₂).1) same

/-- The stable models as a finite set of finite sets. -/
def stableModels : Finset (Finset A) := (P.stableModelList.map List.toFinset).toFinset

theorem mem_stableModels (M : Finset A) : M ∈ P.stableModels ↔ P.Stable ↑M := by
  simp only [stableModels, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact P.stable_of_mem_stableModelList hl
  · intro h
    obtain ⟨l, hl, same⟩ := P.exists_mem_stableModelList h
    exact ⟨l, hl, Finset.coe_inj.mp same⟩

/-- Every stable model, over `Set`, is one of the computed ones. -/
theorem stable_iff_mem_stableModels (S : Set A) : P.Stable S ↔ ∃ M ∈ P.stableModels, ↑M = S := by
  constructor
  · intro h
    obtain ⟨l, hl, same⟩ := P.exists_mem_stableModelList h
    exact ⟨l.toFinset, (P.mem_stableModels _).mpr (same ▸ h), same⟩
  · rintro ⟨M, hM, rfl⟩
    exact (P.mem_stableModels M).mp hM

/-- Supported models, enumerated the same way. -/
def supportedModels : Finset (Finset A) :=
  ((P.atomList.sublists.filter fun l => P.isSupported l.toFinset).map List.toFinset).toFinset

theorem mem_supportedModels (M : Finset A) : M ∈ P.supportedModels ↔ P.Supported ↑M := by
  simp only [supportedModels, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨l, ⟨_, hl⟩, rfl⟩
    exact (P.isSupported_iff _).mp hl
  · intro h
    have within : (↑M : Set A) ⊆ P.headSet := h ▸ P.step_subset_headSet _ _
    obtain ⟨l, hl, same⟩ := P.exists_sublist _ within
    have same := Finset.coe_inj.mp same
    exact ⟨l, ⟨hl, (P.isSupported_iff _).mpr (same ▸ h)⟩, same⟩

/-! ## Loops and external support, decided -/

instance posDepDecidable : DecidableRel P.PosDep := fun b a => by
  unfold PosDep
  infer_instance

/-- The executable loop test of `FiniteLoops.check`, on positive dependency. -/
def loopCheck (L : Finset A) : Bool := NormalProgramLoops.FiniteLoops.check P.PosDep L

theorem loopCheck_iff (L : Finset A) : P.loopCheck L = true ↔ P.IsLoop L :=
  NormalProgramLoops.FiniteLoops.check_correct _ _

/-- The executable test that some rule supports `L` from outside with a body true in `M`. -/
def externalSupportFin (M L : Finset A) : Bool :=
  P.any fun r => decide (r.head ∈ L) && r.pos.all (· ∉ L) && r.holdsFin M M

theorem externalSupportFin_iff (M L : Finset A) :
    P.externalSupportFin M L = true ↔ P.ExternalSupport ↑M L := by
  simp only [externalSupportFin, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Rule.holdsFin_iff, ExternalSupport, ExternalFor, and_assoc]

end Program

end Mettapedia.Logic.ASP
