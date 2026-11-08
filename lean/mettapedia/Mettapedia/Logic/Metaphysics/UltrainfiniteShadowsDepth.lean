import Mettapedia.Logic.Metaphysics.UltrainfiniteShadows
import Mettapedia.Logic.Metaphysics.UltrainfiniteShadowsCantor

/-!
# The depth shadows of the Cantor clopen algebra

The two sides of a finite shadow meet here. On the algebra side, the **depth-`n` shadow**
`depthShadow n` is the finite Boolean subalgebra of clopens decided by the first `n` bits. On the
space side, `depth n` is the quotient map onto `n`-bit answer patterns.

* **Its pieces are the depth classes.** The shadow atoms of `depthShadow n` are exactly the
  cylinders `cylinder p = depth n ⁻¹' {p}` (`mem_shadowAtoms_depthShadow_iff`), and no cylinder is
  an atom of the clopen algebra (`cylinder_not_isAtom`): each is a piece only at resolution `n`.
* **The depth shadows exhaust the whole.** They increase with `n` (`depthShadow_mono`), every
  clopen lies in one of them (`exists_mem_depthShadow`, from `continuous_iff_exists_depth_factor`),
  and every shadow lies inside one of them (`exists_le_depthShadow`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Set Function TopologicalSpace BooleanSubalgebra Mettapedia.Foundations.Gunk

/-- Pull a set of depth-`n` answer patterns back to a clopen of Cantor space. -/
def pullDepth (n : ℕ) : BoundedLatticeHom (Set (Fin n → Bool)) (Clopens (ℕ → Bool)) where
  toFun s := ⟨depth n ⁻¹' s, (isClopen_discrete s).preimage (continuous_depth n)⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

@[simp] theorem coe_pullDepth (n : ℕ) (s : Set (Fin n → Bool)) :
    (pullDepth n s : Set (ℕ → Bool)) = depth n ⁻¹' s := rfl

theorem pullDepth_le_iff {n : ℕ} {s t : Set (Fin n → Bool)} :
    pullDepth n s ≤ pullDepth n t ↔ s ⊆ t :=
  (depth_surjective n).preimage_subset_preimage_iff

/-- The **depth-`n` shadow** of the clopen algebra: the clopens decided by the first `n` bits. -/
def depthShadow (n : ℕ) : BooleanSubalgebra (Clopens (ℕ → Bool)) :=
  (⊤ : BooleanSubalgebra (Set (Fin n → Bool))).map (pullDepth n)

theorem mem_depthShadow {n : ℕ} {C : Clopens (ℕ → Bool)} :
    C ∈ depthShadow n ↔ ∃ s, pullDepth n s = C :=
  ⟨fun ⟨s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, mem_top, h⟩⟩

instance finite_depthShadow (n : ℕ) : Finite (depthShadow n) :=
  ((Set.finite_range (pullDepth n)).subset fun _ hC =>
    mem_depthShadow.1 hC : (depthShadow n : Set (Clopens (ℕ → Bool))).Finite)

/-- The clopen cylinder of a depth-`n` answer pattern: one class of the depth-`n` quotient. -/
def cylinder {n : ℕ} (p : Fin n → Bool) : Clopens (ℕ → Bool) := pullDepth n {p}

theorem cylinder_ne_bot {n : ℕ} (p : Fin n → Bool) : cylinder p ≠ ⊥ := by
  intro e
  have hmem : splice p (fun _ => false) ∈ (cylinder p : Set (ℕ → Bool)) :=
    depth_splice p _
  rw [e, Clopens.coe_bot] at hmem
  exact (Set.mem_empty_iff_false _).1 hmem

/-- Every cylinder of depth `n` is a piece of the depth-`n` shadow. -/
theorem cylinder_mem_shadowAtoms {n : ℕ} (p : Fin n → Bool) :
    cylinder p ∈ shadowAtoms (depthShadow n) := by
  refine ⟨mem_depthShadow.2 ⟨{p}, rfl⟩, fun e => cylinder_ne_bot p (congrArg Subtype.val e),
    fun D hD => ?_⟩
  obtain ⟨s, hs⟩ := mem_depthShadow.1 D.2
  have hle : pullDepth n s ≤ cylinder p := by
    rw [hs]
    exact hD.le
  rcases Set.subset_singleton_iff_eq.1 (pullDepth_le_iff.1 hle) with h | h
  · apply Subtype.ext
    show (D : Clopens (ℕ → Bool)) = ⊥
    rw [← hs, h]
    rfl
  · exfalso
    apply hD.ne
    apply Subtype.ext
    show (D : Clopens (ℕ → Bool)) = cylinder p
    rw [← hs, h]
    rfl

/-- **The pieces of the depth-`n` shadow are exactly the depth-`n` classes.** -/
theorem mem_shadowAtoms_depthShadow_iff {n : ℕ} {C : Clopens (ℕ → Bool)} :
    C ∈ shadowAtoms (depthShadow n) ↔ ∃ p : Fin n → Bool, C = cylinder p := by
  refine ⟨fun ⟨hC, hat⟩ => ?_, fun ⟨p, hp⟩ => by rw [hp]; exact cylinder_mem_shadowAtoms p⟩
  obtain ⟨s, hs⟩ := mem_depthShadow.1 hC
  obtain ⟨p, hp⟩ : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hat.1 (Subtype.ext hs.symm)
  have hle : (⟨cylinder p, mem_depthShadow.2 ⟨{p}, rfl⟩⟩ : depthShadow n) ≤ ⟨C, hC⟩ := by
    show pullDepth n {p} ≤ C
    rw [← hs]
    exact pullDepth_le_iff.2 (Set.singleton_subset_iff.2 hp)
  rcases hat.le_iff.1 hle with h | h
  · exact absurd (congrArg Subtype.val h) (cylinder_ne_bot p)
  · exact ⟨p, (congrArg Subtype.val h).symm⟩

/-- **Gunky control.** No cylinder is an atom of the clopen algebra: a depth class is a piece
only at its depth. -/
theorem cylinder_not_isAtom {n : ℕ} (p : Fin n → Bool) : ¬ IsAtom (cylinder p) :=
  isGunky_iff_no_isAtom.1 isGunky_clopens_cantor _

/-- The depth shadows increase with depth. -/
theorem depthShadow_mono {m n : ℕ} (h : m ≤ n) : depthShadow m ≤ depthShadow n := by
  intro C hC
  obtain ⟨s, rfl⟩ := mem_depthShadow.1 hC
  exact mem_depthShadow.2 ⟨truncate h ⁻¹' s, rfl⟩

/-- **Every clopen is decided at some finite depth.** -/
theorem exists_mem_depthShadow (C : Clopens (ℕ → Bool)) : ∃ n, C ∈ depthShadow n := by
  have hc : Continuous (C : Set (ℕ → Bool)).boolIndicator :=
    (continuous_boolIndicator_iff_isClopen _).2 C.isClopen
  obtain ⟨n, G, hG⟩ := continuous_iff_exists_depth_factor.1 hc
  refine ⟨n, mem_depthShadow.2 ⟨G ⁻¹' {true}, Clopens.ext ?_⟩⟩
  ext f
  show G (depth n f) = true ↔ f ∈ (C : Set (ℕ → Bool))
  rw [Set.mem_iff_boolIndicator, congrFun hG f, Function.comp_apply]

/-- **The depth shadows are cofinal**: every shadow of the clopen algebra lies in one of them. -/
theorem exists_le_depthShadow (L : BooleanSubalgebra (Clopens (ℕ → Bool))) [Finite L] :
    ∃ n, L ≤ depthShadow n := by
  choose N hN using exists_mem_depthShadow
  obtain ⟨n, hn⟩ := ((Set.toFinite (L : Set (Clopens (ℕ → Bool)))).image N).bddAbove
  exact ⟨n, fun C hC => depthShadow_mono (hn ⟨C, hC, rfl⟩) (hN C)⟩

theorem iUnion_depthShadow_eq_univ :
    ⋃ n, (depthShadow n : Set (Clopens (ℕ → Bool))) = Set.univ :=
  Set.eq_univ_of_forall fun C => Set.mem_iUnion.2 (exists_mem_depthShadow C)

end Mettapedia.Logic.Metaphysics.Ultrainfinite
