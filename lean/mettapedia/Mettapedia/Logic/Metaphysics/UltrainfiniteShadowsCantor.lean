import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.BoolIndicator
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Defs

/-!
# Cantor space as the limit of its finite shadows

The **depth-`n` shadow** of a point `f : ℕ → Bool` is its first `n` bits (`depth n f`). Shadows are
quotients of the whole, never parts of it.

* **Inverse system and limit.** Truncation between depths is functorial (`truncate_refl`,
  `truncate_truncate`, `truncate_depth`). The canonical map to the inverse limit `ShadowLimit` is a
  homeomorphism (`shadowLimitHomeomorph`), and Cantor space has the universal property of the
  limit (`existsUnique_lift`, `continuous_lift`).
* **Every shadow class is a copy of the whole.** Each depth projection is surjective
  (`depth_surjective`), and each fibre is homeomorphic to Cantor space (`fibreHomeomorph`), hence
  infinite (`depth_fibre_infinite`).
* **No point is determined by finitely many distinctions**: by finitely many coordinates
  (`exists_ne_agree_on_finset`), by finitely many clopen sets
  (`exists_ne_of_finite_distinctions`), or by any continuous observation with discrete values
  (`exists_ne_observe_eq`). In particular no point is isolated (`cantor_not_isOpen_singleton`).
* **The computable is what finite shadows determine.** A map to a discrete space is continuous
  exactly when it factors through one depth shadow (`continuous_iff_exists_depth_factor`; the
  uniform bound comes from compactness), and exactly when a finite decision tree computes it
  (`continuous_iff_exists_decisionTree`).

No computability notion for functionals on Cantor space is used: mathlib's `RecursiveIn` is
relative to a fixed oracle set, not uniform in the oracle, so the statement here is the
decision-tree form.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Set Function

universe u

/-! ## Depth shadows -/

/-- The **depth-`n` shadow** of a point: the answers to its first `n` bit queries. -/
def depth (n : ℕ) (f : ℕ → Bool) : Fin n → Bool := fun i => f i

theorem depth_eq_depth_iff {n : ℕ} {f g : ℕ → Bool} :
    depth n f = depth n g ↔ ∀ i < n, f i = g i :=
  ⟨fun h i hi => congrFun h ⟨i, hi⟩, fun h => funext fun i => h i i.2⟩

theorem continuous_depth (n : ℕ) : Continuous (depth n) :=
  continuous_pi fun i => continuous_apply (i : ℕ)

/-- Splice a finite answer pattern `p` in front of a point `g`. -/
def splice {n : ℕ} (p : Fin n → Bool) (g : ℕ → Bool) : ℕ → Bool :=
  fun k => if h : k < n then p ⟨k, h⟩ else g (k - n)

theorem depth_splice {n : ℕ} (p : Fin n → Bool) (g : ℕ → Bool) : depth n (splice p g) = p :=
  funext fun i => dif_pos i.2

theorem splice_add {n : ℕ} (p : Fin n → Bool) (g : ℕ → Bool) (k : ℕ) :
    splice p g (k + n) = g k := by
  have hk : ¬ (k + n < n) := by omega
  simp only [splice, dif_neg hk, Nat.add_sub_cancel]

theorem splice_shift_of_depth {n : ℕ} {p : Fin n → Bool} {f : ℕ → Bool} (hf : depth n f = p) :
    splice p (fun k => f (k + n)) = f := by
  subst hf
  funext k
  unfold splice
  split_ifs with h
  · rfl
  · show f (k - n + n) = f k
    rw [Nat.sub_add_cancel (Nat.le_of_not_lt h)]

theorem continuous_splice {n : ℕ} (p : Fin n → Bool) : Continuous (splice p) := by
  refine continuous_pi fun k => ?_
  by_cases h : k < n
  · simp only [splice, dif_pos h]
    exact continuous_const
  · simp only [splice, dif_neg h]
    exact continuous_apply _

/-- **Each projection is surjective**: every finite answer pattern occurs. -/
theorem depth_surjective (n : ℕ) : Surjective (depth n) :=
  fun p => ⟨splice p fun _ => false, depth_splice p _⟩

/-! ## The inverse system and its limit -/

/-- Truncation from depth `n` to depth `m ≤ n`. -/
def truncate {m n : ℕ} (h : m ≤ n) (p : Fin n → Bool) : Fin m → Bool :=
  fun i => p (Fin.castLE h i)

theorem truncate_refl {n : ℕ} (p : Fin n → Bool) : truncate le_rfl p = p := rfl

theorem truncate_truncate {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) (p : Fin n → Bool) :
    truncate h₁ (truncate h₂ p) = truncate (h₁.trans h₂) p := rfl

theorem truncate_depth {m n : ℕ} (h : m ≤ n) (f : ℕ → Bool) :
    truncate h (depth n f) = depth m f := rfl

/-- The **inverse limit of the depth shadows**: compatible families of finite answer patterns. -/
abbrev ShadowLimit : Type :=
  {x : ∀ n, Fin n → Bool // ∀ m n (h : m ≤ n), truncate h (x n) = x m}

/-- A point gives the compatible family of its shadows. -/
def toShadowLimit (f : ℕ → Bool) : ShadowLimit :=
  ⟨fun n => depth n f, fun _ _ h => truncate_depth h f⟩

/-- A compatible family determines a point: bit `k` is read at depth `k + 1`. -/
def ofShadowLimit (x : ShadowLimit) : ℕ → Bool :=
  fun k => x.1 (k + 1) (Fin.last k)

theorem ofShadowLimit_toShadowLimit (f : ℕ → Bool) : ofShadowLimit (toShadowLimit f) = f := rfl

theorem toShadowLimit_ofShadowLimit (x : ShadowLimit) : toShadowLimit (ofShadowLimit x) = x := by
  apply Subtype.ext
  funext n i
  exact (congrFun (x.2 ((i : ℕ) + 1) n i.2) (Fin.last (i : ℕ))).symm

theorem continuous_toShadowLimit : Continuous toShadowLimit :=
  (continuous_pi fun n => continuous_depth n).subtype_mk _

theorem continuous_ofShadowLimit : Continuous ofShadowLimit :=
  continuous_pi fun k =>
    (continuous_apply (Fin.last k)).comp ((continuous_apply (k + 1)).comp continuous_subtype_val)

/-- **The whole is the limit of its shadows**: Cantor space is homeomorphic to the inverse limit
of its depth shadows. -/
def shadowLimitHomeomorph : (ℕ → Bool) ≃ₜ ShadowLimit where
  toFun := toShadowLimit
  invFun := ofShadowLimit
  left_inv := ofShadowLimit_toShadowLimit
  right_inv := toShadowLimit_ofShadowLimit
  continuous_toFun := continuous_toShadowLimit
  continuous_invFun := continuous_ofShadowLimit

/-- **Universal property of the limit.** A compatible family of depth-`n` observations of `X`
comes from exactly one map into Cantor space. -/
theorem existsUnique_lift {X : Type*} (g : ∀ n, X → Fin n → Bool)
    (hg : ∀ m n (h : m ≤ n) x, truncate h (g n x) = g m x) :
    ∃! u : X → ℕ → Bool, ∀ n, depth n ∘ u = g n := by
  refine ⟨fun x => ofShadowLimit ⟨fun n => g n x, fun m n h => hg m n h x⟩, fun n => ?_,
    fun u hu => funext fun x => ?_⟩
  · funext x
    exact congrArg (fun y : ShadowLimit => y.1 n)
      (toShadowLimit_ofShadowLimit ⟨fun n => g n x, fun m n h => hg m n h x⟩)
  · rw [← ofShadowLimit_toShadowLimit (u x)]
    congr 1
    exact Subtype.ext (funext fun n => congrFun (hu n) x)

/-- The lift of a continuous compatible family is continuous. -/
theorem continuous_lift {X : Type*} [TopologicalSpace X] (g : ∀ n, X → Fin n → Bool)
    (hg : ∀ m n (h : m ≤ n) x, truncate h (g n x) = g m x) (hc : ∀ n, Continuous (g n)) :
    Continuous fun x => ofShadowLimit ⟨fun n => g n x, fun m n h => hg m n h x⟩ :=
  continuous_ofShadowLimit.comp ((continuous_pi hc).subtype_mk _)

/-! ## Every shadow class is a copy of the whole -/

/-- **Self-similarity.** The depth-`n` shadow class of `p` is homeomorphic to Cantor space. -/
def fibreHomeomorph {n : ℕ} (p : Fin n → Bool) : (ℕ → Bool) ≃ₜ (depth n ⁻¹' {p}) where
  toFun g := ⟨splice p g, depth_splice p g⟩
  invFun f := fun k => f.1 (k + n)
  left_inv g := funext fun k => splice_add p g k
  right_inv f := Subtype.ext (splice_shift_of_depth f.2)
  continuous_toFun := (continuous_splice p).subtype_mk _
  continuous_invFun :=
    continuous_pi fun k => (continuous_apply (k + n)).comp continuous_subtype_val

/-- **Every shadow class is infinite.** -/
theorem depth_fibre_infinite {n : ℕ} (p : Fin n → Bool) : (depth n ⁻¹' {p}).Infinite :=
  Set.infinite_coe_iff.1 (Infinite.of_injective _ (fibreHomeomorph p).injective)

/-- No shadow class is a singleton: flipping bit `n` keeps the depth-`n` shadow. -/
theorem exists_ne_depth_eq (f : ℕ → Bool) (n : ℕ) : ∃ g ≠ f, depth n g = depth n f := by
  refine ⟨update f n (!f n), fun h => Bool.not_ne_self (f n) ?_, ?_⟩
  · have := congrFun h n
    rwa [update_self] at this
  · exact depth_eq_depth_iff.2 fun i hi => update_of_ne (Nat.ne_of_lt hi) _ _

/-! ## No point is determined by finitely many distinctions -/

/-- Finitely many coordinates never determine a point. -/
theorem exists_ne_agree_on_finset (f : ℕ → Bool) (I : Finset ℕ) :
    ∃ g ≠ f, ∀ i ∈ I, g i = f i := by
  obtain ⟨g, hgf, hg⟩ := exists_ne_depth_eq f (I.sup (· + 1))
  exact ⟨g, hgf, fun i hi => depth_eq_depth_iff.1 hg i
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Finset.le_sup (f := (· + 1)) hi))⟩

/-- **Every open set contains a whole depth class around each of its points.** -/
theorem exists_depth_subset {U : Set (ℕ → Bool)} (hU : IsOpen U) {f : ℕ → Bool} (hf : f ∈ U) :
    ∃ n, ∀ g, depth n g = depth n f → g ∈ U := by
  obtain ⟨I, w, hw, hsub⟩ := isOpen_pi_iff.1 hU f hf
  refine ⟨I.sup (· + 1), fun g hg => hsub fun i hi => ?_⟩
  have hlt : i < I.sup (· + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Finset.le_sup (f := (· + 1)) hi)
  rw [depth_eq_depth_iff.1 hg i hlt]
  exact (hw i hi).2

/-- **No point of Cantor space is isolated.** -/
theorem cantor_not_isOpen_singleton (f : ℕ → Bool) : ¬ IsOpen ({f} : Set (ℕ → Bool)) := by
  intro h
  obtain ⟨n, hn⟩ := exists_depth_subset h (Set.mem_singleton f)
  obtain ⟨g, hgf, hg⟩ := exists_ne_depth_eq f n
  exact hgf (hn g hg)

/-- **A continuous observation with discrete values never separates a point**, on any space
without isolated points. -/
theorem exists_ne_observe_eq {X : Type*} {W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    [DiscreteTopology W] (noIsolated : ∀ x : X, ¬ IsOpen ({x} : Set X)) {obs : X → W}
    (hobs : Continuous obs) (x : X) : ∃ y ≠ x, obs y = obs x := by
  by_contra h
  apply noIsolated x
  have hfib : obs ⁻¹' {obs x} = {x} := by
    ext y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · by_contra hne
      exact h ⟨y, hne, hy⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact Set.mem_singleton _
  rw [← hfib]
  exact (isOpen_discrete _).preimage hobs

/-- **Finitely many clopen distinctions never separate a point**, on any space without isolated
points. -/
theorem exists_ne_of_finite_distinctions {X : Type*} [TopologicalSpace X]
    (noIsolated : ∀ x : X, ¬ IsOpen ({x} : Set X)) (S : Finset (Set X))
    (hS : ∀ C ∈ S, IsClopen C) (x : X) : ∃ y ≠ x, ∀ C ∈ S, (y ∈ C ↔ x ∈ C) := by
  have hobs : Continuous fun y : X => fun C : S => (C : Set X).boolIndicator y :=
    continuous_pi fun C => (continuous_boolIndicator_iff_isClopen _).2 (hS C C.2)
  obtain ⟨y, hyx, hy⟩ := exists_ne_observe_eq noIsolated hobs x
  refine ⟨y, hyx, fun C hC => ?_⟩
  rw [Set.mem_iff_boolIndicator, Set.mem_iff_boolIndicator]
  exact Iff.of_eq (congrArg (· = true) (congrFun hy ⟨C, hC⟩))

/-- On Cantor space: finitely many clopen distinctions never separate a point. -/
theorem cantor_exists_ne_of_finite_distinctions (S : Finset (Set (ℕ → Bool)))
    (hS : ∀ C ∈ S, IsClopen C) (f : ℕ → Bool) : ∃ g ≠ f, ∀ C ∈ S, (g ∈ C ↔ f ∈ C) :=
  exists_ne_of_finite_distinctions cantor_not_isOpen_singleton S hS f

/-! ## The computable is what finite shadows determine -/

/-- **Uniform finite resolution (compactness).** An equivalence relation on Cantor space whose
classes are open is coarser than one depth shadow. -/
theorem exists_depth_of_isOpen_classes (s : Setoid (ℕ → Bool))
    (hs : ∀ f, IsOpen {g | s.r f g}) : ∃ n, ∀ f g, depth n f = depth n g → s.r f g := by
  have hloc : ∀ f, ∃ n, ∀ g, depth n g = depth n f → s.r f g := fun f =>
    exists_depth_subset (f := f) (hs f) (s.iseqv.refl f)
  choose N hN using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun f => depth (N f) ⁻¹' {depth (N f) f})
    (fun f => (isOpen_discrete _).preimage (continuous_depth _))
    (fun g _ => Set.mem_iUnion.2 ⟨g, Set.mem_preimage.2 (Set.mem_singleton _)⟩)
  refine ⟨t.sup N, fun g h hgh => ?_⟩
  obtain ⟨f, hft, hgf⟩ : ∃ f ∈ t, depth (N f) g = depth (N f) f := by
    simpa using ht (Set.mem_univ g)
  have hle : N f ≤ t.sup N := Finset.le_sup hft
  have hhf : depth (N f) h = depth (N f) f := by
    rw [← hgf, ← truncate_depth hle g, ← truncate_depth hle h, hgh]
  exact s.iseqv.trans (s.iseqv.symm (hN f g hgf)) (hN f h hhf)

section Factor

variable {W : Type u} [TopologicalSpace W] [DiscreteTopology W]

omit [DiscreteTopology W] in
/-- A map that depends only on a depth shadow is continuous. -/
theorem continuous_of_depth {F : (ℕ → Bool) → W} {n : ℕ}
    (hF : ∀ f g, depth n f = depth n g → F f = F g) : Continuous F := by
  have hfac : F = (fun p => F (splice p fun _ => false)) ∘ depth n :=
    funext fun f => hF _ _ (depth_splice _ _).symm
  rw [hfac]
  exact continuous_of_discreteTopology.comp (continuous_depth n)

/-- **Uniform finite dependence (compactness).** A continuous map to a discrete space depends only
on one depth shadow. -/
theorem exists_depth_of_continuous {F : (ℕ → Bool) → W} (hF : Continuous F) :
    ∃ n, ∀ f g, depth n f = depth n g → F f = F g := by
  refine exists_depth_of_isOpen_classes ⟨fun f g => F f = F g, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
    fun f => ?_
  show IsOpen {g | F f = F g}
  have hfib : {g | F f = F g} = F ⁻¹' {F f} := Set.ext fun _ => eq_comm
  rw [hfib]
  exact (isOpen_discrete {F f}).preimage hF

/-- **Continuity is factoring through one finite shadow.** -/
theorem continuous_iff_exists_depth {F : (ℕ → Bool) → W} :
    Continuous F ↔ ∃ n, ∀ f g, depth n f = depth n g → F f = F g :=
  ⟨exists_depth_of_continuous, fun ⟨_, hn⟩ => continuous_of_depth hn⟩

theorem continuous_iff_exists_depth_factor {F : (ℕ → Bool) → W} :
    Continuous F ↔ ∃ n, ∃ G : (Fin n → Bool) → W, F = G ∘ depth n := by
  rw [continuous_iff_exists_depth]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, fun p => F (splice p fun _ => false),
    funext fun f => hn _ _ (depth_splice _ _).symm⟩, fun ⟨n, G, hG⟩ => ⟨n, fun f g h => ?_⟩⟩
  rw [hG]
  exact congrArg G h

end Factor

/-! ## Finite interactions: decision trees -/

/-- A **finite interaction** with a point of Cantor space: a tree that queries bits and ends with
an answer. -/
inductive DecisionTree (W : Type u) : Type u
  | answer : W → DecisionTree W
  | query : ℕ → DecisionTree W → DecisionTree W → DecisionTree W

namespace DecisionTree

variable {W : Type u}

/-- Run a tree on a point: `query i t₀ t₁` reads bit `i`, then continues with `t₁` on `true` and
with `t₀` on `false`. -/
def run : DecisionTree W → (ℕ → Bool) → W
  | answer w, _ => w
  | query i t₀ t₁, f => cond (f i) (t₁.run f) (t₀.run f)

/-- A bound on the bits a tree reads: every queried index is below it. -/
def reach : DecisionTree W → ℕ
  | answer _ => 0
  | query i t₀ t₁ => max (i + 1) (max t₀.reach t₁.reach)

theorem run_eq_of_agree (t : DecisionTree W) {f g : ℕ → Bool}
    (h : ∀ i < t.reach, f i = g i) : t.run f = t.run g := by
  induction t with
  | answer _ => rfl
  | query i t₀ t₁ ih₀ ih₁ =>
    simp only [reach] at h
    have hi : f i = g i := h i (lt_max_of_lt_left (Nat.lt_succ_self i))
    have h₀ : ∀ j < t₀.reach, f j = g j := fun j hj =>
      h j (lt_max_of_lt_right (lt_max_of_lt_left hj))
    have h₁ : ∀ j < t₁.reach, f j = g j := fun j hj =>
      h j (lt_max_of_lt_right (lt_max_of_lt_right hj))
    simp only [run, hi, ih₀ h₀, ih₁ h₁]

/-- **Every finite interaction is continuous.** -/
theorem continuous_run [TopologicalSpace W] [DiscreteTopology W] (t : DecisionTree W) :
    Continuous t.run :=
  continuous_of_depth (n := t.reach) fun _ _ h => t.run_eq_of_agree (depth_eq_depth_iff.1 h)

/-- The full tree of depth `n`: it reads bits `n - 1, …, 0` and answers with `F`. -/
def build : ℕ → ((ℕ → Bool) → W) → DecisionTree W
  | 0, F => answer (F fun _ => false)
  | n + 1, F => query n (build n fun f => F (update f n false))
      (build n fun f => F (update f n true))

theorem run_build (n : ℕ) (F : (ℕ → Bool) → W)
    (hF : ∀ f g, (∀ i < n, f i = g i) → F f = F g) : (build n F).run = F := by
  induction n generalizing F with
  | zero =>
    funext f
    simp only [build, run]
    exact hF _ _ fun i hi => absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    have hb : ∀ b : Bool, (build n fun f => F (update f n b)).run = fun f => F (update f n b) :=
      fun b => ih _ fun f g h => hF _ _ fun i hi => by
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
        · rw [update_of_ne (Nat.ne_of_lt hi), update_of_ne (Nat.ne_of_lt hi)]
          exact h i hi
        · rw [update_self, update_self]
    funext f
    simp only [build, run, hb]
    have hself : update f n (f n) = f := update_eq_self n f
    cases hfn : f n
    · rw [hfn] at hself
      simp only [cond_false, hself]
    · rw [hfn] at hself
      simp only [cond_true, hself]

end DecisionTree

/-- **Continuity is computability by a finite interaction.** A map from Cantor space to a discrete
space is continuous exactly when some finite decision tree computes it. -/
theorem continuous_iff_exists_decisionTree {W : Type u} [TopologicalSpace W] [DiscreteTopology W]
    {F : (ℕ → Bool) → W} : Continuous F ↔ ∃ t : DecisionTree W, t.run = F := by
  refine ⟨fun hF => ?_, fun ⟨t, ht⟩ => by rw [← ht]; exact t.continuous_run⟩
  obtain ⟨n, hn⟩ := exists_depth_of_continuous hF
  exact ⟨DecisionTree.build n F,
    DecisionTree.run_build n F fun f g h => hn f g (depth_eq_depth_iff.2 h)⟩

/-- Control: reading bit `0` is computed by a one-query tree. -/
theorem run_query_zero :
    (DecisionTree.query 0 (.answer false) (.answer true)).run = fun f : ℕ → Bool => f 0 := by
  funext f
  cases hf : f 0 <;> simp [DecisionTree.run, hf]

open Classical in
/-- Control: "some bit is `true`" is not continuous, so no finite interaction decides it. -/
theorem not_continuous_exists_true :
    ¬ Continuous fun f : ℕ → Bool => decide (∃ k, f k = true) := by
  intro h
  obtain ⟨n, hn⟩ := exists_depth_of_continuous h
  have hzero : depth n (fun _ => false) = depth n (update (fun _ => false) n true) :=
    depth_eq_depth_iff.2 fun i hi => (update_of_ne (Nat.ne_of_lt hi) true (fun _ : ℕ => false)).symm
  have h1 : decide (∃ k, (fun _ : ℕ => false) k = true) =
      decide (∃ k, update (fun _ : ℕ => false) n true k = true) := hn _ _ hzero
  have hl : ¬ ∃ k, (fun _ : ℕ => false) k = true := by simp
  have hr : ∃ k, update (fun _ : ℕ => false) n true k = true := ⟨n, update_self _ _ _⟩
  rw [decide_eq_false hl, decide_eq_true hr] at h1
  exact Bool.false_ne_true h1

end Mettapedia.Logic.Metaphysics.Ultrainfinite
