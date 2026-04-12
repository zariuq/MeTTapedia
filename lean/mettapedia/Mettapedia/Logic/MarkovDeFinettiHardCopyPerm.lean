import Mettapedia.Logic.MarkovDeFinettiHardEulerTrailFiber

/-! LLM primer:
- `edgeTok G = Σ a : Fin k, Σ b : Fin k, Fin (G a b)` — one token per parallel edge copy.
- `trailVertexSeq G s f` only reads `edgeTgt (f ⟨i, _⟩)`, never the copy index.
- Therefore permuting copy indices preserves vertex sequences.

# Copy-Index Permutations & Fiber Cardinality (Phase B, Step 3)

## Main definitions

- `CopyPerm G` : product of permutation groups `∀ a b, Perm (Fin (G a b))`
- `applyPerm σ e` : apply copy perm to a single edge token
- `applyCopyPerm σ f` : apply pointwise to an edge labeling

## Main results

- `trailVertexSeq_applyCopyPerm` : copy perms preserve vertex sequences
- `applyCopyPerm_isEulerTrail` : copy perms preserve Euler trail property
- `card_copyPerm` : `|CopyPerm G| = ∏ a, ∏ b, (G a b)!`
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardCopyPerm

open Finset
open MarkovDeFinettiHardBESTCore
open MarkovDeFinettiHardEulerTrails
open MarkovDeFinettiHardEulerTrailFiber

variable {k : ℕ}

/-! ## Block A: CopyPerm basics -/

/-- Product of permutation groups, one per edge type `(a, b)`. -/
def CopyPerm (G : EulerGraph k) : Type :=
  ∀ a b : Fin k, Equiv.Perm (Fin (G a b))

/-- Apply a copy-index permutation to a single edge token. Preserves src and tgt. -/
def applyPerm {G : EulerGraph k} (σ : CopyPerm G) (e : edgeTok G) : edgeTok G :=
  ⟨e.1, e.2.1, σ e.1 e.2.1 e.2.2⟩

@[simp] lemma applyPerm_src {G : EulerGraph k} (σ : CopyPerm G) (e : edgeTok G) :
    edgeSrc (applyPerm σ e) = edgeSrc e := rfl

@[simp] lemma applyPerm_tgt {G : EulerGraph k} (σ : CopyPerm G) (e : edgeTok G) :
    edgeTgt (applyPerm σ e) = edgeTgt e := rfl

/-- `applyPerm σ` is injective on `edgeTok G`. -/
lemma applyPerm_injective {G : EulerGraph k} (σ : CopyPerm G) :
    Function.Injective (applyPerm (k := k) σ) := by
  intro e₁ e₂ h
  have hsrc : edgeSrc e₁ = edgeSrc e₂ := by rw [← applyPerm_src σ e₁, ← applyPerm_src σ e₂, h]
  have htgt : edgeTgt e₁ = edgeTgt e₂ := by rw [← applyPerm_tgt σ e₁, ← applyPerm_tgt σ e₂, h]
  rcases e₁ with ⟨a₁, b₁, c₁⟩
  rcases e₂ with ⟨a₂, b₂, c₂⟩
  simp [edgeSrc] at hsrc; simp [edgeTgt] at htgt
  subst hsrc; subst htgt
  have hap : applyPerm σ ⟨a₁, b₁, c₁⟩ = applyPerm σ ⟨a₁, b₁, c₂⟩ := h
  unfold applyPerm at hap
  -- hap : ⟨a₁, ⟨b₁, σ a₁ b₁ c₁⟩⟩ = ⟨a₁, ⟨b₁, σ a₁ b₁ c₂⟩⟩
  have hσ : (σ a₁ b₁) c₁ = (σ a₁ b₁) c₂ :=
    eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hap).2)).2
  have hc := (σ a₁ b₁).injective hσ
  subst hc; rfl

/-- `applyPerm σ` is surjective on `edgeTok G`. -/
lemma applyPerm_surjective {G : EulerGraph k} (σ : CopyPerm G) :
    Function.Surjective (applyPerm (k := k) σ) := by
  intro ⟨a, b, c⟩
  exact ⟨⟨a, b, (σ a b).symm c⟩, by simp [applyPerm, Equiv.apply_symm_apply]⟩

/-- `applyPerm σ` is bijective on `edgeTok G`. -/
lemma applyPerm_bijective {G : EulerGraph k} (σ : CopyPerm G) :
    Function.Bijective (applyPerm (k := k) σ) :=
  ⟨applyPerm_injective σ, applyPerm_surjective σ⟩

/-! ## Block B: applyCopyPerm preserves Euler trails -/

/-- Apply a copy-index permutation pointwise to an edge labeling. -/
def applyCopyPerm {G : EulerGraph k} {N : ℕ} (σ : CopyPerm G)
    (f : Fin N → edgeTok G) : Fin N → edgeTok G :=
  fun i => applyPerm σ (f i)

/-- `applyCopyPerm σ f` is bijective when `f` is. -/
lemma applyCopyPerm_bijective {G : EulerGraph k} (σ : CopyPerm G)
    {f : Fin (totalEdgeTokens G) → edgeTok G} (hf : Function.Bijective f) :
    Function.Bijective (applyCopyPerm (k := k) σ f) :=
  (applyPerm_bijective σ).comp hf

/-- Copy permutations preserve vertex sequences: `trailVertexSeq` only reads `edgeTgt`,
which is unchanged by `applyPerm`. -/
theorem trailVertexSeq_applyCopyPerm {G : EulerGraph k} (σ : CopyPerm G) (s : Fin k)
    (f : Fin (totalEdgeTokens G) → edgeTok G) :
    trailVertexSeq G s (applyCopyPerm (k := k) σ f) = trailVertexSeq G s f := by
  funext ⟨i, hi⟩
  unfold trailVertexSeq applyCopyPerm applyPerm
  simp only
  split <;> rfl

/-- Copy permutations preserve the Euler trail property. -/
theorem applyCopyPerm_isEulerTrail {G : EulerGraph k} (σ : CopyPerm G) {s t : Fin k}
    {f : Fin (totalEdgeTokens G) → edgeTok G} (hf : IsEulerTrail G s t f) :
    IsEulerTrail G s t (applyCopyPerm (k := k) σ f) := by
  refine ⟨applyCopyPerm_bijective σ hf.bijective, ?_, ?_, ?_, ?_⟩
  · exact hf.empty_eq
  · intro h; simp [applyCopyPerm, applyPerm]; exact hf.start_eq h
  · intro i hi; simp [applyCopyPerm, applyPerm]; exact hf.chain i hi
  · intro h; simp [applyCopyPerm, applyPerm]; exact hf.end_eq h

/-! ## Block C: Same vertex sequence ↔ differ by CopyPerm -/

/-- Two Euler trails with the same vertex sequence have the same src/tgt at each position. -/
lemma same_vertexSeq_src_eq {G : EulerGraph k} {s t : Fin k}
    {f g : Fin (totalEdgeTokens G) → edgeTok G}
    (hf : IsEulerTrail G s t f) (hg : IsEulerTrail G s t g)
    (hvs : trailVertexSeq G s f = trailVertexSeq G s g)
    (i : Fin (totalEdgeTokens G)) :
    edgeSrc (f i) = edgeSrc (g i) := by
  rw [edgeSrc_eq_trailVertexSeq_castSucc G s t f hf i,
      hvs,
      ← edgeSrc_eq_trailVertexSeq_castSucc G s t g hg i]

lemma same_vertexSeq_tgt_eq {G : EulerGraph k} {s t : Fin k}
    {f g : Fin (totalEdgeTokens G) → edgeTok G}
    (hf : IsEulerTrail G s t f) (hg : IsEulerTrail G s t g)
    (hvs : trailVertexSeq G s f = trailVertexSeq G s g)
    (i : Fin (totalEdgeTokens G)) :
    edgeTgt (f i) = edgeTgt (g i) := by
  rw [edgeTgt_eq_trailVertexSeq_succ G s t f hf i,
      hvs,
      ← edgeTgt_eq_trailVertexSeq_succ G s t g hg i]

/-! ## Block D: Cardinality of CopyPerm -/

instance instFintypeCopyPerm (G : EulerGraph k) : Fintype (CopyPerm (k := k) G) := by
  unfold CopyPerm
  infer_instance

/-- The cardinality of `CopyPerm G` is `∏ a, ∏ b, (G a b)!`. -/
theorem card_copyPerm (G : EulerGraph k) :
    Fintype.card (CopyPerm (k := k) G) =
      ∏ a : Fin k, ∏ b : Fin k, (G a b).factorial := by
  unfold CopyPerm
  simp [Fintype.card_pi, Fintype.card_perm, Fintype.card_fin]

/-! ## Block E: Fiber cardinality via Equiv

We construct `eulerTrailFinset(G, s.start, s.last) ≃ fiber(N, s) × CopyPerm(G)`.

The Fin cast `totalEdgeTokens(graphOfState s) = N` is handled by `Fin.cast`. -/

open MarkovExchangeability
open UniversalPrediction.FiniteAlphabet
open UniversalPrediction.MarkovExchangeabilityBridge
open MarkovDeFinettiHard

/-- Cast a vertex sequence from `Fin (totalEdgeTokens G + 1)` to `Fin (N + 1)`. -/
def castTraj {N : ℕ} {G : EulerGraph k}
    (hN : totalEdgeTokens (k := k) G = N)
    (xs : Fin (totalEdgeTokens G + 1) → Fin k) : Fin (N + 1) → Fin k :=
  xs ∘ Fin.cast (by omega)

/-- Cast in the other direction: `Fin (N + 1) → Fin k` to `Fin (totalEdgeTokens G + 1) → Fin k`. -/
def uncastTraj {N : ℕ} {G : EulerGraph k}
    (hN : totalEdgeTokens (k := k) G = N)
    (xs : Fin (N + 1) → Fin k) : Fin (totalEdgeTokens G + 1) → Fin k :=
  xs ∘ Fin.cast (by omega)

@[simp] lemma castTraj_uncastTraj {N : ℕ} {G : EulerGraph k}
    (hN : totalEdgeTokens (k := k) G = N) (xs : Fin (N + 1) → Fin k) :
    castTraj hN (uncastTraj hN xs) = xs := by
  ext i; simp [castTraj, uncastTraj, Fin.cast]

@[simp] lemma uncastTraj_castTraj {N : ℕ} {G : EulerGraph k}
    (hN : totalEdgeTokens (k := k) G = N) (xs : Fin (totalEdgeTokens G + 1) → Fin k) :
    uncastTraj hN (castTraj hN xs) = xs := by
  ext i; simp [castTraj, uncastTraj, Fin.cast]

/-- `stateOfTraj` of a cast vertex sequence equals `stateOfTraj` of the original. -/
lemma stateOfTraj_castTraj {N : ℕ} {G : EulerGraph k}
    (hN : totalEdgeTokens (k := k) G = N)
    (xs : Fin (totalEdgeTokens G + 1) → Fin k) :
    stateOfTraj (k := k) (castTraj hN xs) = stateOfTraj (k := k) xs := by
  subst hN; rfl

/-- The cast vertex sequence of an Euler trail on `graphOfState s` belongs to `fiber k N s`. -/
lemma castTraj_trailVertexSeq_mem_fiber {N : ℕ} {s : MarkovState k}
    (hs : s ∈ stateFinset k N)
    {f : Fin (totalEdgeTokens (graphOfState s)) → edgeTok (graphOfState s)}
    (hf : IsEulerTrail (graphOfState s) s.start s.last f) :
    castTraj (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
      (trailVertexSeq (graphOfState s) s.start f) ∈ fiber k N s := by
  rw [fiber, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [stateOfTraj_castTraj]; exact stateOfTraj_trailVertexSeq s f hf⟩

/-! ## Fiber cardinality formula

The main result: `|eulerTrailFinset| = |fiber| × ∏ (G a b)!`.

Strategy: We work entirely in the `totalEdgeTokens G` world via `subst`.
The map `applyCopyPerm σ (trajToEdgeTokN xs)` from `fiber × CopyPerm` to
`eulerTrailFinset` is injective, and cardinality matching gives bijectivity. -/

/-- Applying a copy perm to the canonical labeling of a trajectory gives an Euler trail
with the same vertex sequence. -/
lemma applyCopyPerm_trajToEdgeTokN_mem_eulerTrailFinset {M : ℕ}
    (xs : Fin (M + 1) → Fin k) (σ : CopyPerm (graphOfState (stateOfTraj (k := k) xs))) :
    applyCopyPerm σ (trajToEdgeTokN (k := k) xs) ∈
      eulerTrailFinset (graphOfState (stateOfTraj (k := k) xs)) (xs 0) (xs (Fin.last M)) := by
  rw [mem_eulerTrailFinset]
  exact applyCopyPerm_isEulerTrail σ (trajToEdgeTokN_isEulerTrail xs)

/-- If `applyPerm σ₁ = applyPerm σ₂` on all edge tokens, then `σ₁ = σ₂`. -/
lemma applyPerm_eq_imp_eq {G : EulerGraph k}
    (σ₁ σ₂ : CopyPerm G)
    (h : ∀ e : edgeTok G, applyPerm σ₁ e = applyPerm σ₂ e) :
    σ₁ = σ₂ := by
  funext a b
  ext c
  have heq := h ⟨a, b, c⟩
  -- heq : ⟨a, ⟨b, σ₁ a b c⟩⟩ = ⟨a, ⟨b, σ₂ a b c⟩⟩
  -- Use applyPerm_injective to show the pre-images are equal, then extract copy
  have : applyPerm σ₁ ⟨a, b, c⟩ = applyPerm σ₂ ⟨a, b, c⟩ := heq
  -- Both have same src=a, tgt=b, so the Fin values must agree
  have hinj₁ := applyPerm_injective σ₁
  have hinj₂ := applyPerm_injective σ₂
  -- applyPerm σ ⟨a,b,c⟩ = ⟨a, b, σ a b c⟩, so σ₁ a b c = σ₂ a b c as Fin elements
  show (σ₁ a b c).val = (σ₂ a b c).val
  have h1 : (applyPerm σ₁ ⟨a, b, c⟩).2.2.val = (σ₁ a b c).val := rfl
  have h2 : (applyPerm σ₂ ⟨a, b, c⟩).2.2.val = (σ₂ a b c).val := rfl
  rw [← h1, ← h2, this]

/-- Two `CopyPerm`s applied to the same canonical labeling give the same trail → equal. -/
lemma applyCopyPerm_trajToEdgeTokN_injective {M : ℕ}
    (xs : Fin (M + 1) → Fin k)
    (σ₁ σ₂ : CopyPerm (graphOfState (stateOfTraj (k := k) xs)))
    (h : applyCopyPerm σ₁ (trajToEdgeTokN (k := k) xs) =
         applyCopyPerm σ₂ (trajToEdgeTokN (k := k) xs)) :
    σ₁ = σ₂ := by
  apply applyPerm_eq_imp_eq
  intro e
  obtain ⟨i, hi⟩ := (trajToEdgeTokN_bijective (k := k) xs).2 e
  have := congr_fun h i
  simp only [applyCopyPerm] at this
  rw [hi] at this
  exact this

/-! ## Fiber cardinality formula

We prove `|eulerTrailFinset| = |fiber| × ∏ (G a b)!` via injection counting.

After `subst` (using `totalEdgeTokens (graphOfState s) = N`), trajectories and
trail vertex sequences share the same Fin type, avoiding casts. -/

/-- The map `σ ↦ applyCopyPerm σ f` from `CopyPerm G` to `eulerTrailFinset` is injective
for any Euler trail `f`. -/
lemma applyCopyPerm_injective_of_isEulerTrail {G : EulerGraph k} {s t : Fin k}
    {f : Fin (totalEdgeTokens G) → edgeTok G} (hf : IsEulerTrail G s t f)
    {σ₁ σ₂ : CopyPerm G}
    (h : applyCopyPerm σ₁ f = applyCopyPerm σ₂ f) : σ₁ = σ₂ := by
  apply applyPerm_eq_imp_eq
  intro e
  obtain ⟨i, hi⟩ := hf.surjective e
  have := congr_fun h i
  simp only [applyCopyPerm] at this
  rw [hi] at this
  exact this

/-- Given two Euler trails `f, g` with the same vertex sequence, there exists a `CopyPerm σ`
such that `g = applyCopyPerm σ f`. -/
theorem exists_copyPerm_of_same_vertexSeq {G : EulerGraph k} {s t : Fin k}
    {f g : Fin (totalEdgeTokens G) → edgeTok G}
    (hf : IsEulerTrail G s t f) (hg : IsEulerTrail G s t g)
    (hvs : trailVertexSeq G s f = trailVertexSeq G s g) :
    ∃ σ : CopyPerm G, g = applyCopyPerm σ f := by
  -- f and g have same src/tgt at every position
  have hsrc : ∀ i, edgeSrc (f i) = edgeSrc (g i) :=
    same_vertexSeq_src_eq hf hg hvs
  have htgt : ∀ i, edgeTgt (f i) = edgeTgt (g i) :=
    same_vertexSeq_tgt_eq hf hg hvs
  -- gMap = g ∘ f⁻¹ preserves src/tgt
  let fEquiv := Equiv.ofBijective f hf.bijective
  have hfEquiv_apply : ∀ i, fEquiv i = f i := fun _ => rfl
  have hfEquiv_symm : ∀ e, f (fEquiv.symm e) = e := fEquiv.apply_symm_apply
  have gMap_src : ∀ e, edgeSrc (g (fEquiv.symm e)) = edgeSrc e := by
    intro e
    rw [← hsrc (fEquiv.symm e), hfEquiv_symm]
  have gMap_tgt : ∀ e, edgeTgt (g (fEquiv.symm e)) = edgeTgt e := by
    intro e
    rw [← htgt (fEquiv.symm e), hfEquiv_symm]
  -- Build the CopyPerm: for each (a,b,c), extract copy index of g(f⁻¹(⟨a,b,c⟩))
  -- Key helper: gMap ⟨a,b,c⟩ has the form ⟨a, b, d⟩, so we can extract d
  have gMap_eq : ∀ a b (c : Fin (G a b)),
      ∃ d : Fin (G a b), g (fEquiv.symm ⟨a, b, c⟩) = ⟨a, b, d⟩ := by
    intro a b c
    rcases hv : g (fEquiv.symm ⟨a, b, c⟩) with ⟨a', b', d⟩
    have h1 : a' = a := by
      have := gMap_src ⟨a, b, c⟩; rw [hv] at this; simpa [edgeSrc] using this
    have h2 : b' = b := by
      have := gMap_tgt ⟨a, b, c⟩; rw [hv] at this; simpa [edgeTgt] using this
    subst h1; subst h2
    exact ⟨d, rfl⟩
  -- Define φ(a,b)(c) = the d such that gMap ⟨a,b,c⟩ = ⟨a,b,d⟩
  let φ : ∀ a b : Fin k, Fin (G a b) → Fin (G a b) :=
    fun a b c => (gMap_eq a b c).choose
  have hφ_spec : ∀ a b c, g (fEquiv.symm ⟨a, b, c⟩) = ⟨a, b, φ a b c⟩ :=
    fun a b c => (gMap_eq a b c).choose_spec
  -- φ is injective (since g ∘ fEquiv.symm is)
  have φ_inj : ∀ a b, Function.Injective (φ a b) := by
    intro a b c₁ c₂ heq
    have ginj : Function.Injective (g ∘ fEquiv.symm) :=
      hg.injective.comp fEquiv.symm.injective
    have : g (fEquiv.symm ⟨a, b, c₁⟩) = g (fEquiv.symm ⟨a, b, c₂⟩) := by
      rw [hφ_spec a b c₁, hφ_spec a b c₂, heq]
    have h := ginj this
    -- h : (⟨a, b, c₁⟩ : edgeTok G) = ⟨a, b, c₂⟩
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  -- Build the Equiv
  refine ⟨fun a b => Equiv.ofBijective (φ a b)
    ((Fintype.bijective_iff_injective_and_card (φ a b)).mpr ⟨φ_inj a b, by simp⟩), ?_⟩
  · -- applyCopyPerm σ f = g
    funext i
    simp only [applyCopyPerm, applyPerm, Equiv.ofBijective_apply]
    -- f i = ⟨a, b, c⟩, and we need ⟨a, b, φ a b c⟩ = g i
    -- By construction: g(fEquiv.symm(f i)) = ⟨(f i).1, (f i).2.1, φ (f i).1 (f i).2.1 (f i).2.2⟩
    -- And fEquiv.symm(f i) = i, so g(fEquiv.symm(f i)) = g i
    have := hφ_spec (f i).1 (f i).2.1 (f i).2.2
    simp only [show (⟨(f i).1, (f i).2.1, (f i).2.2⟩ : edgeTok G) = f i from rfl] at this
    -- this : g (fEquiv.symm (f i)) = ⟨...⟩, need g i = ⟨...⟩
    have hkey : fEquiv.symm (f i) = i := by
      show fEquiv.symm (fEquiv i) = i
      exact fEquiv.symm_apply_apply i
    rw [hkey] at this
    exact this

/-! ## Canonical labeling with state cast -/

/-- `trajToEdgeTokN` cast from `graphOfState (stateOfTraj xs)` to `graphOfState s`
when `stateOfTraj xs = s`. -/
def canonicalOnGraph {M : ℕ} (xs : Fin (M + 1) → Fin k)
    {s : MarkovState k} (h : stateOfTraj (k := k) xs = s) :
    Fin (totalEdgeTokens (graphOfState s)) → edgeTok (graphOfState s) :=
  h ▸ trajToEdgeTokN (k := k) xs

lemma canonicalOnGraph_isEulerTrail {M : ℕ} (xs : Fin (M + 1) → Fin k)
    {s : MarkovState k} (h : stateOfTraj (k := k) xs = s) :
    IsEulerTrail (graphOfState s) s.start s.last (canonicalOnGraph xs h) := by
  subst h; exact trajToEdgeTokN_isEulerTrail xs

/-- The vertex sequence of `canonicalOnGraph` recovers the original trajectory
(after appropriate Fin cast). -/
lemma trailVertexSeq_canonicalOnGraph {M : ℕ} (xs : Fin (M + 1) → Fin k)
    {s : MarkovState k} (h : stateOfTraj (k := k) xs = s)
    (i : Fin (totalEdgeTokens (graphOfState s) + 1)) :
    trailVertexSeq (graphOfState s) s.start (canonicalOnGraph xs h) i =
      xs ⟨i.1, by
        have := totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k)
          (h ▸ stateOfTraj_mem_stateFinset (k := k) xs); omega⟩ := by
  subst h; exact trailVertexSeq_trajToEdgeTokN xs i

/-- After `subst`, `trailVertexSeq` of the canonical labeling recovers the original trajectory. -/
lemma trailVertexSeq_canonicalOnGraph_eq
    (xs : Fin (totalEdgeTokens (graphOfState (k := k) s) + 1) → Fin k)
    (h : stateOfTraj (k := k) xs = s) :
    trailVertexSeq (graphOfState s) s.start (canonicalOnGraph xs h) = xs := by
  funext i; exact trailVertexSeq_canonicalOnGraph xs h i

/-- The vertex sequence of an Euler trail on `graphOfState s` belongs to `fiber`. -/
lemma trailVertexSeq_mem_fiber
    {f : Fin (totalEdgeTokens (graphOfState (k := k) s)) → edgeTok (graphOfState s)}
    (hf : IsEulerTrail (graphOfState s) s.start s.last f) :
    trailVertexSeq (graphOfState s) s.start f ∈
      fiber k (totalEdgeTokens (graphOfState (k := k) s)) s := by
  rw [fiber, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, stateOfTraj_trailVertexSeq s f hf⟩

/-! ## Main cardinality formula -/

/-- **Fiber cardinality formula**: the number of Euler trails equals the fiber size times the
product of factorials of edge multiplicities. -/
theorem eulerTrailFinset_card_eq {N : ℕ} (s : MarkovState k) (hs : s ∈ stateFinset k N) :
    (eulerTrailFinset (graphOfState s) s.start s.last).card =
      (fiber k N s).card * ∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial := by
  have hN := totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs
  subst hN
  rw [← card_copyPerm (graphOfState (k := k) s),
      ← Finset.card_univ (α := CopyPerm (graphOfState (k := k) s)),
      ← Finset.card_product]
  -- Goal: |eulerTrailFinset| = |fiber ×ˢ Finset.univ|
  symm
  apply Finset.card_bij
    -- Map: (xs, σ) ↦ applyCopyPerm σ (canonicalOnGraph xs hstate)
    (fun p hp =>
      applyCopyPerm p.2 (canonicalOnGraph p.1
        ((Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2)))
    -- hi: maps into eulerTrailFinset
    (fun p hp => by
      rw [mem_eulerTrailFinset]
      exact applyCopyPerm_isEulerTrail p.2
        (canonicalOnGraph_isEulerTrail p.1 _))
    -- i_inj: injective
    (fun ⟨xs₁, σ₁⟩ hp₁ ⟨xs₂, σ₂⟩ hp₂ heq => by
      dsimp only at heq
      have h₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hp₁).1).2
      have h₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hp₂).1).2
      -- Step 1: vertex sequences agree, hence xs₁ = xs₂
      have hvs : xs₁ = xs₂ := by
        have := congr_arg (trailVertexSeq (graphOfState s) s.start) heq
        rw [trailVertexSeq_applyCopyPerm, trailVertexSeq_applyCopyPerm,
            trailVertexSeq_canonicalOnGraph_eq, trailVertexSeq_canonicalOnGraph_eq] at this
        exact this
      subst hvs
      -- Step 2: same canonical labeling, so σ₁ = σ₂
      have hσ : σ₁ = σ₂ :=
        applyCopyPerm_injective_of_isEulerTrail (canonicalOnGraph_isEulerTrail xs₁ h₁) heq
      exact Prod.ext rfl hσ)
    -- i_surj: surjective
    (fun f hf => by
      rw [mem_eulerTrailFinset] at hf
      -- The vertex sequence lands in fiber
      let xs := trailVertexSeq (graphOfState s) s.start f
      have hxs_fiber := trailVertexSeq_mem_fiber hf
      have hxs_state : stateOfTraj (k := k) xs = s :=
        stateOfTraj_trailVertexSeq s f hf
      -- The canonical labeling and f have the same vertex sequence
      have hvs : trailVertexSeq _ s.start (canonicalOnGraph xs hxs_state) =
                 trailVertexSeq _ s.start f := by
        rw [trailVertexSeq_canonicalOnGraph_eq]
      -- exists_copyPerm gives σ with f = applyCopyPerm σ (canonical xs)
      obtain ⟨σ, hσ⟩ := exists_copyPerm_of_same_vertexSeq
        (canonicalOnGraph_isEulerTrail xs hxs_state) hf hvs
      exact ⟨(xs, σ), Finset.mem_product.mpr ⟨hxs_fiber, Finset.mem_univ _⟩, hσ.symm⟩)

/-- Subset version of `eulerTrailFinset_card_eq`:
for any trajectory subset `A` inside the fiber, the number of Euler trails whose
vertex sequence lands in `A` is `|A| * |CopyPerm|`. -/
theorem eulerTrailFinset_card_filter_trajSubset
    (s : MarkovState k)
    (A : Finset (Traj k (totalEdgeTokens (graphOfState (k := k) s))))
    (hA : A ⊆ fiber k (totalEdgeTokens (graphOfState (k := k) s)) s) :
    ((eulerTrailFinset (graphOfState s) s.start s.last).filter
      (fun f => trailVertexSeq (graphOfState s) s.start f ∈ A)).card =
      A.card * ∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial := by
  rw [← card_copyPerm (graphOfState (k := k) s),
      ← Finset.card_univ (α := CopyPerm (graphOfState (k := k) s)),
      ← Finset.card_product]
  -- count `A × CopyPerm` by a bijection into filtered Euler trails
  symm
  apply Finset.card_bij
    (fun p hp =>
      applyCopyPerm p.2 (canonicalOnGraph p.1
        ((Finset.mem_filter.mp (hA (Finset.mem_product.mp hp).1)).2)))
    (fun p hp => by
      rw [Finset.mem_filter]
      constructor
      · rw [mem_eulerTrailFinset]
        exact applyCopyPerm_isEulerTrail p.2
          (canonicalOnGraph_isEulerTrail p.1
            ((Finset.mem_filter.mp (hA (Finset.mem_product.mp hp).1)).2))
      · -- vertex sequence of the mapped trail is exactly `p.1`
        have hstate : stateOfTraj (k := k) p.1 = s :=
          (Finset.mem_filter.mp (hA (Finset.mem_product.mp hp).1)).2
        have hvs :
            trailVertexSeq (graphOfState s) s.start
              (applyCopyPerm p.2 (canonicalOnGraph p.1 hstate)) =
              trailVertexSeq (graphOfState s) s.start (canonicalOnGraph p.1 hstate) := by
          simpa using trailVertexSeq_applyCopyPerm p.2 s.start (canonicalOnGraph p.1 hstate)
        rw [hvs, trailVertexSeq_canonicalOnGraph_eq]
        exact (Finset.mem_product.mp hp).1)
    (fun p hp₁ q hp₂ heq => by
      rcases p with ⟨xs₁, σ₁⟩
      rcases q with ⟨xs₂, σ₂⟩
      dsimp only at heq
      have h₁ := (Finset.mem_filter.mp (hA (Finset.mem_product.mp hp₁).1)).2
      have h₂ := (Finset.mem_filter.mp (hA (Finset.mem_product.mp hp₂).1)).2
      have hvs : xs₁ = xs₂ := by
        have := congr_arg (trailVertexSeq (graphOfState s) s.start) heq
        rw [trailVertexSeq_applyCopyPerm, trailVertexSeq_applyCopyPerm,
            trailVertexSeq_canonicalOnGraph_eq, trailVertexSeq_canonicalOnGraph_eq] at this
        exact this
      subst hvs
      have hσ : σ₁ = σ₂ :=
        applyCopyPerm_injective_of_isEulerTrail (canonicalOnGraph_isEulerTrail xs₁ h₁) heq
      exact Prod.ext rfl hσ)
    (fun f hf => by
      have hfTrail : IsEulerTrail (graphOfState s) s.start s.last f := by
        rw [Finset.mem_filter] at hf
        rw [mem_eulerTrailFinset] at hf
        exact hf.1
      have hxsA : trailVertexSeq (graphOfState s) s.start f ∈ A := by
        rw [Finset.mem_filter] at hf
        exact hf.2
      let xs := trailVertexSeq (graphOfState s) s.start f
      have hxsState : stateOfTraj (k := k) xs = s :=
        (Finset.mem_filter.mp (hA hxsA)).2
      have hvs : trailVertexSeq (graphOfState s) s.start (canonicalOnGraph xs hxsState) =
                 trailVertexSeq (graphOfState s) s.start f := by
        rw [trailVertexSeq_canonicalOnGraph_eq]
      obtain ⟨σ, hσ⟩ := exists_copyPerm_of_same_vertexSeq
        (canonicalOnGraph_isEulerTrail xs hxsState) hfTrail hvs
      refine ⟨(xs, σ), ?_, hσ.symm⟩
      exact Finset.mem_product.mpr ⟨hxsA, Finset.mem_univ _⟩)

end MarkovDeFinettiHardCopyPerm

end Mettapedia.Logic
