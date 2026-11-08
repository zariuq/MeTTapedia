import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.SupClosed
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Lattice
import Mettapedia.Logic.GunkyMereology

/-!
# Finite shadows of a Boolean algebra

A **shadow** of a Boolean algebra `B` is a finite Boolean subalgebra `L`: what finitely many
distinctions can tell apart. Its atoms, the **shadow atoms** (`shadowAtoms L`), are the pieces into
which those distinctions cut the whole.

* **Local finiteness** (`closure_finite`): finitely many elements generate a finite subalgebra.
* **Shadow atoms partition the whole**: they are nonzero, pairwise disjoint and finitely many,
  their join in `B` is `⊤` (`isLUB_shadowAtoms`), and every element of the shadow is the join of
  the shadow atoms below it (`isLUB_shadowAtoms_le`). A nontrivial algebra has a shadow atom in
  every shadow (`shadowAtoms_nonempty`).
* **The whole is the directed union of its shadows** (`directedOn_shadows`,
  `iUnion_shadows_eq_univ`).
* **Gunk: shadow atoms are never atoms.** `B` is gunky exactly when no shadow atom of any shadow
  is an atom of `B` (`isGunky_iff_forall_shadowAtoms_not_isAtom`), and exactly when every shadow
  atom is cut by a finer shadow (`isGunky_iff_forall_shadowAtoms_split`); the cut produces two
  distinct finer shadow atoms (`exists_finer_shadow_split`).
* **Finiteness: a finest shadow.** `B` is finite exactly when some shadow has only genuine atoms
  (`finite_iff_exists_shadow_forall_isAtom`).

Controls: Cantor clopens, where the cylinder `{f | f 0 = true}` is a shadow atom and not an atom
(`cantorCylinder_mem_shadowAtoms`, `cantorCylinder_not_isAtom`); `Set (Fin n)`, where the atoms of
the top shadow are exactly the singletons, all genuine (`shadowAtoms_top_set`,
`set_fin_exists_shadow_forall_isAtom`); and `Set ℕ`, an infinite atomic algebra, where one shadow
atom is genuine and another is not (`set_nat_singleton_zero_mem_shadowAtoms`,
`set_nat_compl_singleton_zero_not_isAtom`), and no shadow is finest
(`set_nat_not_exists_shadow_forall_isAtom`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Mettapedia.Foundations.Gunk BooleanSubalgebra

universe u

variable {B : Type u} [BooleanAlgebra B]

/-! ## Local finiteness -/

/-- **Finitely many distinctions generate finitely many regions.** -/
theorem closure_finite {s : Set B} (hs : s.Finite) : (closure s : Set B).Finite := by
  classical
  set t : Set B := latticeClosure (insert ⊥ (insert ⊤ s)) with ht_def
  have ht : t.Finite := ((hs.insert ⊤).insert ⊥).latticeClosure
  have hbot : (⊥ : B) ∈ t := subset_latticeClosure (Set.mem_insert _ _)
  have htop : (⊤ : B) ∈ t :=
    subset_latticeClosure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hct : closure t = closure s := by
    rw [ht_def, closure_latticeClosure]
    refine le_antisymm (closure_le.2 ?_) (closure_mono fun x hx => Or.inr (Or.inr hx))
    rintro x (rfl | rfl | hx)
    · exact bot_mem
    · exact top_mem
    · exact subset_closure hx
  have : Fintype t := ht.fintype
  refine (Set.finite_range fun w : Finset (t × t) => w.sup fun x => x.1.1 \ x.2.1).subset ?_
  intro a ha
  rw [SetLike.mem_coe, ← hct] at ha
  obtain ⟨w, rfl⟩ := (mem_closure_iff_sup_sdiff isSublattice_latticeClosure hbot htop).1 ha
  exact ⟨w, rfl⟩

theorem finite_closure {s : Set B} (hs : s.Finite) : Finite (closure s) :=
  closure_finite hs

/-- Any finitely many distinctions live together in one shadow. -/
theorem exists_shadow_superset {s : Set B} (hs : s.Finite) :
    ∃ L : BooleanSubalgebra B, Finite L ∧ s ⊆ L :=
  ⟨closure s, finite_closure hs, subset_closure⟩

/-! ## The whole is the directed union of its shadows -/

/-- The shadows are directed: two shadows have a common refinement. -/
theorem directedOn_shadows : DirectedOn (· ≤ ·) {L : BooleanSubalgebra B | Finite L} := by
  intro L hL M hM
  have : Finite L := hL
  have : Finite M := hM
  refine ⟨closure ((L : Set B) ∪ M),
    finite_closure ((Set.toFinite (L : Set B)).union (Set.toFinite (M : Set B))), ?_, ?_⟩
  · exact fun x hx => subset_closure (Or.inl hx)
  · exact fun x hx => subset_closure (Or.inr hx)

/-- Every element lies in some shadow. -/
theorem iUnion_shadows_eq_univ :
    ⋃ L ∈ {L : BooleanSubalgebra B | Finite L}, (L : Set B) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, SetLike.mem_coe]
  exact ⟨closure {x}, finite_closure (Set.finite_singleton x),
    subset_closure (Set.mem_singleton _)⟩

/-! ## Shadow atoms -/

/-- The **shadow atoms** of a subalgebra `L`: the elements of `B` that are atoms of `L`. -/
def shadowAtoms (L : BooleanSubalgebra B) : Set B :=
  {a | ∃ h : a ∈ L, IsAtom (⟨a, h⟩ : L)}

theorem mem_shadowAtoms {L : BooleanSubalgebra B} {a : B} :
    a ∈ shadowAtoms L ↔ ∃ h : a ∈ L, IsAtom (⟨a, h⟩ : L) :=
  Iff.rfl

theorem shadowAtoms_subset (L : BooleanSubalgebra B) : shadowAtoms L ⊆ L :=
  fun _ ha => ha.1

theorem ne_bot_of_mem_shadowAtoms {L : BooleanSubalgebra B} {a : B} (ha : a ∈ shadowAtoms L) :
    a ≠ ⊥ := by
  obtain ⟨h, hat⟩ := ha
  exact fun e => hat.1 (Subtype.ext e)

theorem shadowAtoms_finite (L : BooleanSubalgebra B) [Finite L] : (shadowAtoms L).Finite :=
  (Set.toFinite (L : Set B)).subset (shadowAtoms_subset L)

/-- Distinct shadow atoms are disjoint in `B`. -/
theorem shadowAtoms_pairwiseDisjoint (L : BooleanSubalgebra B) :
    (shadowAtoms L).PairwiseDisjoint id := by
  rintro a ⟨ha, hat⟩ b ⟨hb, hbt⟩ hab
  have hd := hat.disjoint_of_ne hbt (fun e => hab (congrArg Subtype.val e))
  rw [disjoint_iff] at hd
  show Disjoint a b
  rw [disjoint_iff]
  exact congrArg Subtype.val hd

/-- An atom of `B` that lies in a subalgebra is an atom of it. -/
theorem mem_shadowAtoms_of_isAtom {L : BooleanSubalgebra B} {a : B} (ha : IsAtom a)
    (haL : a ∈ L) : a ∈ shadowAtoms L :=
  ⟨haL, fun e => ha.1 (congrArg Subtype.val e), fun b hb => Subtype.ext (ha.2 b hb)⟩

/-- **A shadow sees each of its elements as the join of its pieces.** Every element of a finite
subalgebra is, in `B`, the least upper bound of the shadow atoms below it. -/
theorem isLUB_shadowAtoms_le (L : BooleanSubalgebra B) [Finite L] {x : B} (hx : x ∈ L) :
    IsLUB {a | a ∈ shadowAtoms L ∧ a ≤ x} x := by
  classical
  refine ⟨fun a ha => ha.2, fun y hy => ?_⟩
  have : Fintype L := Fintype.ofFinite L
  set T : Finset L := Finset.univ.filter (fun a => IsAtom a ∧ a ≤ ⟨x, hx⟩) with hT
  have hxT : (⟨x, hx⟩ : L) ≤ T.sup id := BooleanAlgebra.le_iff_atom_le_imp.2 fun a ha hax =>
    Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha, hax⟩)
  have hmap : ((T.sup id : L) : B) = T.sup (fun a => (a : B)) := map_finset_sup L.subtype T id
  calc x = ((⟨x, hx⟩ : L) : B) := rfl
    _ ≤ ((T.sup id : L) : B) := hxT
    _ = T.sup (fun a => (a : B)) := hmap
    _ ≤ y := Finset.sup_le fun a ha =>
      hy ⟨⟨a.2, (Finset.mem_filter.1 ha).2.1⟩, (Finset.mem_filter.1 ha).2.2⟩

/-- **The shadow atoms cover the whole**: their least upper bound in `B` is `⊤`. -/
theorem isLUB_shadowAtoms (L : BooleanSubalgebra B) [Finite L] : IsLUB (shadowAtoms L) ⊤ := by
  have h := isLUB_shadowAtoms_le L (top_mem (L := L))
  simpa only [le_top, and_true, Set.ofPred_mem_eq] using h

theorem sup_shadowAtoms (L : BooleanSubalgebra B) [Finite L] :
    (shadowAtoms_finite L).toFinset.sup id = ⊤ :=
  le_antisymm le_top ((isLUB_shadowAtoms L).2 fun _ ha =>
    Finset.le_sup (f := id) ((shadowAtoms_finite L).mem_toFinset.2 ha))

/-- **Every shadow of a nontrivial algebra has pieces.** -/
theorem shadowAtoms_nonempty [Nontrivial B] (L : BooleanSubalgebra B) [Finite L] :
    (shadowAtoms L).Nonempty := by
  have hne : (⊤ : L) ≠ ⊥ := fun e => top_ne_bot (congrArg Subtype.val e)
  obtain ⟨a, ha, -⟩ := (eq_bot_or_exists_atom_le (⊤ : L)).resolve_left hne
  exact ⟨a, a.2, ha⟩

/-! ## Gunk: no shadow atom is an atom -/

/-- **Gunk is exactly: no finite piece is a piece of the whole.** -/
theorem isGunky_iff_forall_shadowAtoms_not_isAtom :
    IsGunky B ↔
      ∀ L : BooleanSubalgebra B, Finite L → ∀ a ∈ shadowAtoms L, ¬ IsAtom a := by
  rw [isGunky_iff_no_isAtom]
  exact ⟨fun h _ _ a _ => h a, fun h a ha => h (closure {a})
    (finite_closure (Set.finite_singleton a)) a
    (mem_shadowAtoms_of_isAtom ha (subset_closure (Set.mem_singleton _))) ha⟩

/-- **You can always look deeper.** In a gunky algebra every shadow atom `a` is cut by a finer
shadow `M ≥ L`: `a` lies in `M` but is not an atom of it, and two distinct shadow atoms of `M` lie
below `a`. -/
theorem exists_finer_shadow_split (hg : IsGunky B) {L : BooleanSubalgebra B} [Finite L] {a : B}
    (ha : a ∈ shadowAtoms L) :
    ∃ M : BooleanSubalgebra B, Finite M ∧ L ≤ M ∧ a ∈ M ∧ a ∉ shadowAtoms M ∧
      ∃ b ∈ shadowAtoms M, ∃ c ∈ shadowAtoms M, b ≠ c ∧ b ≤ a ∧ c ≤ a := by
  obtain ⟨b, hb0, hba⟩ := hg a (ne_bot_of_mem_shadowAtoms ha)
  set M : BooleanSubalgebra B := closure ((L : Set B) ∪ {b}) with hM
  have hMfin : Finite M :=
    finite_closure ((Set.toFinite (L : Set B)).union (Set.finite_singleton b))
  have hLM : L ≤ M := fun x hx => subset_closure (Or.inl hx)
  have haM : a ∈ M := hLM ha.1
  have hbM : b ∈ M := subset_closure (Or.inr (Set.mem_singleton b))
  have hdM : a \ b ∈ M := sdiff_mem haM hbM
  have hd0 : a \ b ≠ ⊥ := fun e => hba.ne (le_antisymm hba.le (sdiff_eq_bot_iff.1 e))
  have := hMfin
  obtain ⟨b', hb', hb'b⟩ := (eq_bot_or_exists_atom_le (⟨b, hbM⟩ : M)).resolve_left
    (fun e => hb0 (congrArg Subtype.val e))
  obtain ⟨c', hc', hc'd⟩ := (eq_bot_or_exists_atom_le (⟨a \ b, hdM⟩ : M)).resolve_left
    (fun e => hd0 (congrArg Subtype.val e))
  have hb'B : (b' : B) ≤ b := hb'b
  have hc'B : (c' : B) ≤ a \ b := hc'd
  refine ⟨M, hMfin, hLM, haM, ?_, (b' : B), ⟨b'.2, hb'⟩, (c' : B), ⟨c'.2, hc'⟩, ?_,
    hb'B.trans hba.le, hc'B.trans sdiff_le⟩
  · rintro ⟨_, hat⟩
    exact hb0 (congrArg Subtype.val (hat.2 ⟨b, hbM⟩ hba))
  · intro e
    have h1 : (b' : B) ≤ b ⊓ (a \ b) := le_inf hb'B (by rw [e]; exact hc'B)
    rw [inf_sdiff_self_right] at h1
    exact hb'.1 (Subtype.ext (le_bot_iff.1 h1))

/-- **Gunk is exactly: every finite piece is cut by a finer resolution.** -/
theorem isGunky_iff_forall_shadowAtoms_split :
    IsGunky B ↔ ∀ L : BooleanSubalgebra B, Finite L → ∀ a ∈ shadowAtoms L,
      ∃ M : BooleanSubalgebra B, Finite M ∧ L ≤ M ∧ a ∉ shadowAtoms M := by
  refine ⟨fun hg L hL a ha => ?_, fun h => ?_⟩
  · have := hL
    obtain ⟨M, hM, hLM, -, haM, -⟩ := exists_finer_shadow_split hg ha
    exact ⟨M, hM, hLM, haM⟩
  · rw [isGunky_iff_no_isAtom]
    intro a ha
    obtain ⟨M, -, hLM, haM⟩ := h (closure {a}) (finite_closure (Set.finite_singleton a)) a
      (mem_shadowAtoms_of_isAtom ha (subset_closure (Set.mem_singleton _)))
    exact haM (mem_shadowAtoms_of_isAtom ha (hLM (subset_closure (Set.mem_singleton _))))

/-! ## Finiteness: a finest shadow -/

theorem shadowAtoms_top : shadowAtoms (⊤ : BooleanSubalgebra B) = {a | IsAtom a} := by
  ext a
  refine ⟨fun ⟨_, hat⟩ => ⟨fun e => hat.1 (Subtype.ext e), fun b hb =>
    congrArg Subtype.val (hat.2 ⟨b, mem_top⟩ hb)⟩,
    fun ha => mem_shadowAtoms_of_isAtom ha mem_top⟩

/-- In a Boolean algebra covered by finitely many atoms, every element is the join of the atoms
below it. -/
theorem eq_sup_filter_le_of_isAtom [DecidableRel ((· ≤ ·) : B → B → Prop)] {T : Finset B}
    (hT : ∀ a ∈ T, IsAtom a) (htop : T.sup id = ⊤) (x : B) :
    x = (T.filter (· ≤ x)).sup id := by
  refine le_antisymm ?_ (Finset.sup_le fun a ha => (Finset.mem_filter.1 ha).2)
  calc x = x ⊓ T.sup id := by rw [htop, inf_top_eq]
    _ = T.sup (fun a => x ⊓ id a) := Finset.sup_inf_distrib_left T id x
    _ ≤ _ := Finset.sup_le fun a ha => by
      by_cases hax : a ≤ x
      · exact inf_le_right.trans (Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨ha, hax⟩))
      · have hxa : x ⊓ a = ⊥ := by
          rcases (hT a ha).le_iff.1 (inf_le_right : x ⊓ a ≤ a) with h | h
          · exact h
          · exact absurd (by rw [← h]; exact inf_le_left) hax
        simp only [id, hxa, bot_le]

/-- **A finest shadow exists exactly for a finite whole.** `B` is finite iff some shadow has only
genuine atoms. -/
theorem finite_iff_exists_shadow_forall_isAtom :
    Finite B ↔ ∃ L : BooleanSubalgebra B, Finite L ∧ ∀ a ∈ shadowAtoms L, IsAtom a := by
  classical
  refine ⟨fun _ => ⟨⊤, inferInstance, fun a ha => by rwa [shadowAtoms_top] at ha⟩,
    fun ⟨L, hL, hat⟩ => ?_⟩
  have := hL
  set T := (shadowAtoms_finite L).toFinset
  have hT : ∀ a ∈ T, IsAtom a := fun a ha => hat a ((shadowAtoms_finite L).mem_toFinset.1 ha)
  have hdec := eq_sup_filter_le_of_isAtom hT (sup_shadowAtoms L)
  refine Finite.of_injective (fun x : B => (⟨T.filter (· ≤ x),
    Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩ : T.powerset)) fun x y hxy => ?_
  have h : T.filter (· ≤ x) = T.filter (· ≤ y) := congrArg Subtype.val hxy
  calc x = (T.filter (· ≤ x)).sup id := hdec x
    _ = (T.filter (· ≤ y)).sup id := congrArg (fun S => S.sup id) h
    _ = y := (hdec y).symm

/-! ## The shadow of one distinction -/

theorem mem_closure_singleton {a x : B} :
    x ∈ closure ({a} : Set B) ↔ x = ⊥ ∨ x = a ∨ x = aᶜ ∨ x = ⊤ := by
  refine ⟨fun hx => ?_, ?_⟩
  · induction hx using closure_bot_sup_induction with
    | mem x hx => exact Or.inr (Or.inl hx)
    | bot => exact Or.inl rfl
    | sup x _ y _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> simp
    | compl x _ hx => rcases hx with rfl | rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact bot_mem
    · exact subset_closure (Set.mem_singleton _)
    · exact compl_mem (subset_closure (Set.mem_singleton _))
    · exact top_mem

/-- **One distinction, one piece.** A nonzero element is an atom of the shadow it generates,
`{⊥, a, aᶜ, ⊤}`. -/
theorem mem_shadowAtoms_closure_singleton {a : B} (ha : a ≠ ⊥) :
    a ∈ shadowAtoms (closure ({a} : Set B)) := by
  refine ⟨subset_closure (Set.mem_singleton _), fun e => ha (congrArg Subtype.val e),
    fun b hb => ?_⟩
  have hbB : (b : B) < a := hb
  apply Subtype.ext
  show (b : B) = ⊥
  rcases mem_closure_singleton.1 b.2 with h | h | h | h
  · exact h
  · rw [h] at hbB
    exact absurd hbB (lt_irrefl a)
  · rw [h] at hbB
    have hc : aᶜ ⊓ a = aᶜ := inf_eq_left.2 hbB.le
    rw [compl_inf_self] at hc
    rw [h, ← hc]
  · rw [h] at hbB
    exact absurd hbB not_top_lt

/-! ## Controls -/

section Controls

open TopologicalSpace

/-- The cylinder of the one-bit prefix `true`, a clopen of Cantor space. -/
def cantorCylinder : Clopens (ℕ → Bool) :=
  ⟨{f | f 0 = true}, by
    have he : {f : ℕ → Bool | f 0 = true} = (fun f : ℕ → Bool => f 0) ⁻¹' {true} :=
      Set.ext fun _ => Iff.rfl
    rw [he]
    exact (isClopen_discrete _).preimage (continuous_apply 0)⟩

theorem cantorCylinder_ne_bot : cantorCylinder ≠ ⊥ := by
  intro e
  have hmem : (fun _ => true) ∈ (cantorCylinder : Set (ℕ → Bool)) := rfl
  rw [e, Clopens.coe_bot] at hmem
  exact (Set.mem_empty_iff_false _).1 hmem

/-- **Gunky control.** The cylinder is a piece of the shadow of its own distinction. -/
theorem cantorCylinder_mem_shadowAtoms :
    cantorCylinder ∈ shadowAtoms (closure ({cantorCylinder} : Set (Clopens (ℕ → Bool)))) :=
  mem_shadowAtoms_closure_singleton cantorCylinder_ne_bot

/-- **Gunky control.** The cylinder is not an atom of the clopen algebra. -/
theorem cantorCylinder_not_isAtom : ¬ IsAtom cantorCylinder :=
  isGunky_iff_no_isAtom.1 isGunky_clopens_cantor _

/-- **Finite control.** The pieces of the top shadow of `Set (Fin n)` are exactly the
singletons. -/
theorem shadowAtoms_top_set (n : ℕ) :
    shadowAtoms (⊤ : BooleanSubalgebra (Set (Fin n))) = {s | ∃ i, s = {i}} := by
  rw [shadowAtoms_top]
  ext s
  exact Set.isAtom_iff

/-- **Finite control.** `Set (Fin n)` has a finest shadow: all its pieces are genuine atoms. -/
theorem set_fin_exists_shadow_forall_isAtom (n : ℕ) :
    ∃ L : BooleanSubalgebra (Set (Fin n)), Finite L ∧ ∀ a ∈ shadowAtoms L, IsAtom a :=
  finite_iff_exists_shadow_forall_isAtom.1 inferInstance

/-- **Mixed control.** In `Set ℕ`, the shadow of the distinction `{0}` has a genuine atom. -/
theorem set_nat_singleton_zero_mem_shadowAtoms :
    ({0} : Set ℕ) ∈ shadowAtoms (closure ({({0} : Set ℕ)} : Set (Set ℕ))) ∧
      IsAtom ({0} : Set ℕ) :=
  ⟨mem_shadowAtoms_closure_singleton (Set.singleton_ne_empty 0), Set.isAtom_singleton 0⟩

/-- **Mixed control.** The other piece of that shadow, `{0}ᶜ`, is not an atom. -/
theorem set_nat_compl_singleton_zero_not_isAtom :
    ({0}ᶜ : Set ℕ) ∈ shadowAtoms (closure ({({0} : Set ℕ)} : Set (Set ℕ))) ∧
      ¬ IsAtom ({0}ᶜ : Set ℕ) := by
  refine ⟨?_, fun h => ?_⟩
  · have hc : ({0}ᶜ : Set ℕ) ∈ closure ({({0} : Set ℕ)} : Set (Set ℕ)) :=
      compl_mem (subset_closure (Set.mem_singleton _))
    have hc0 : ({0}ᶜ : Set ℕ) ≠ ⊥ := Set.nonempty_iff_ne_empty.1 ⟨1, by simp⟩
    refine ⟨hc, fun e => hc0 (congrArg Subtype.val e), fun b hb => ?_⟩
    have hbB : (b : Set ℕ) < {0}ᶜ := hb
    apply Subtype.ext
    rcases mem_closure_singleton.1 b.2 with h | h | h | h
    · exact h
    · exfalso
      have h0 : (0 : ℕ) ∈ (b : Set ℕ) := by rw [h]; exact Set.mem_singleton 0
      exact (hbB.le h0) (Set.mem_singleton 0)
    · rw [h] at hbB
      exact absurd hbB (lt_irrefl _)
    · rw [h] at hbB
      exact absurd hbB not_top_lt
  · obtain ⟨i, hi⟩ := Set.isAtom_iff.1 h
    have h1 : (1 : ℕ) ∈ ({0}ᶜ : Set ℕ) := by simp
    have h2 : (2 : ℕ) ∈ ({0}ᶜ : Set ℕ) := by simp
    rw [hi] at h1 h2
    exact absurd ((Set.mem_singleton_iff.1 h1).trans (Set.mem_singleton_iff.1 h2).symm)
      (by decide)

/-- **Mixed control.** `Set ℕ` is atomic but has no finest shadow. -/
theorem set_nat_not_exists_shadow_forall_isAtom :
    ¬ ∃ L : BooleanSubalgebra (Set ℕ), Finite L ∧ ∀ a ∈ shadowAtoms L, IsAtom a := by
  rw [← finite_iff_exists_shadow_forall_isAtom]
  intro h
  have : Finite ℕ := Finite.of_injective (fun n : ℕ => ({n} : Set ℕ)) Set.singleton_injective
  exact Infinite.false (inferInstance : Infinite ℕ)

end Controls

end Mettapedia.Logic.Metaphysics.Ultrainfinite
