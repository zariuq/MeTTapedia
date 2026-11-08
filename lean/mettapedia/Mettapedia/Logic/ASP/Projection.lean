import Mettapedia.Logic.ASP.Counting

/-!
# Projected model counting, with its side conditions

A projected count counts the assignments of the visible variables `X` that extend
to a model by some assignment of the auxiliary variables `E` (`Formula.projModels`,
`Formula.projCount`). Each law below states the side condition it needs; the
controls show each law failing without it.

* With no auxiliary variables the projected count is the count
  (`projCount_empty_aux`).
* **Shannon split on a visible variable** (`projCount_insert`): for `x` neither
  visible yet nor auxiliary, the count over `X ∪ {x}` is the sum of the counts of
  `F[x := 0]` and `F[x := 1]`.
* **Splitting on an auxiliary variable is a union, not a sum**
  (`projModels_insert_aux`): the projected models of `F` with `y` auxiliary are those
  of `F[y := 0]` together with those of `F[y := 1]`. The count is at most the sum
  (`projCount_insert_aux_le`), and equal to it exactly when no visible assignment
  extends both ways (`projCount_insert_aux_eq_iff`).
* **Component decomposition** (`projCount_append`): formulas whose visible and
  auxiliary variables are all disjoint count independently. A shared auxiliary
  variable breaks it.
* **Auxiliary-variable elimination by definition** (`count_define`,
  `projCount_define`): adding a variable `y` outside `S` together with clauses that
  determine its value uniquely from every assignment of `S` (`Defines`), as Tseitin
  encodings do, keeps the count over `S` and the count projected onto `S`. Without
  uniqueness the count changes.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CNF

open Finset

universe u

variable {V : Type u} [DecidableEq V]

namespace Formula

/-- The visible assignment `T` extends to a model of `F` by an assignment of the auxiliary
variables `E`. -/
def Extends (E : Finset V) (F : Formula V) (T : Finset V) : Prop :=
  ∃ U ∈ E.powerset, F.eval (assignmentOf (T ∪ U)) = true

instance (E : Finset V) (F : Formula V) (T : Finset V) : Decidable (F.Extends E T) := by
  unfold Extends
  infer_instance

/-- **The projected models**: the assignments of `X` that extend to a model by an assignment
of `E`. -/
def projModels (X E : Finset V) (F : Formula V) : Finset (Finset V) := X.powerset.filter (F.Extends E)

/-- **The projected model count.** -/
def projCount (X E : Finset V) (F : Formula V) : ℕ := (F.projModels X E).card

theorem projCount_eq_sum (X E : Finset V) (F : Formula V) :
    F.projCount X E = ∑ T ∈ X.powerset, if F.Extends E T then 1 else 0 := by
  rw [projCount, projModels, card_filter]

/-- **With no auxiliary variables the projected count is the count.** -/
theorem projCount_empty_aux (X : Finset V) (F : Formula V) : F.projCount X ∅ = F.count X := by
  unfold projCount projModels count Extends
  congr 1
  apply filter_congr
  intro T _
  simp

theorem extends_condition_false {E : Finset V} {F : Formula V} {T : Finset V} {x : V} (hT : x ∉ T) (hE : x ∉ E) :
    (F.condition x false).Extends E T ↔ F.Extends E T := by
  unfold Extends
  refine exists_congr fun U => and_congr_right fun hU => ?_
  have hx : x ∉ T ∪ U := by
    rw [mem_union, not_or]
    exact ⟨hT, fun h => hE (mem_powerset.mp hU h)⟩
  rw [eval_condition, update_assignmentOf_false hx]

theorem extends_condition_true {E : Finset V} {F : Formula V} {T : Finset V} {x : V} :
    (F.condition x true).Extends E T ↔ F.Extends E (insert x T) := by
  unfold Extends
  refine exists_congr fun U => and_congr_right fun _ => ?_
  rw [eval_condition, update_assignmentOf_true, insert_union]

/-- **The projected Shannon split on a visible variable.** -/
theorem projCount_insert {X E : Finset V} {x : V} (hX : x ∉ X) (hE : x ∉ E) (F : Formula V) :
    F.projCount (insert x X) E = (F.condition x false).projCount X E + (F.condition x true).projCount X E := by
  rw [projCount_eq_sum, sum_powerset_insert hX, projCount_eq_sum, projCount_eq_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have hT' : x ∉ T := fun h => hX (mem_powerset.mp hT h)
    simp only [extends_condition_false hT' hE]
  · refine sum_congr rfl fun T _ => ?_
    simp only [extends_condition_true]

/-- **Splitting on an auxiliary variable is a union.** -/
theorem projModels_insert_aux {X E : Finset V} {y : V} (hX : y ∉ X) (hE : y ∉ E) (F : Formula V) :
    F.projModels X (insert y E) = (F.condition y false).projModels X E ∪ (F.condition y true).projModels X E := by
  ext T
  simp only [projModels, mem_filter, mem_union]
  constructor
  · rintro ⟨hT, U, hU, model⟩
    have hTy : y ∉ T := fun h => hX (mem_powerset.mp hT h)
    rw [mem_powerset] at hU
    by_cases hy : y ∈ U
    · right
      refine ⟨hT, U.erase y, mem_powerset.mpr fun z hz => ?_, ?_⟩
      · have := hU (mem_of_mem_erase hz)
        rcases mem_insert.mp this with rfl | h
        · exact absurd hz (notMem_erase _ _)
        · exact h
      · rw [eval_condition, update_assignmentOf_true, ← union_insert, insert_erase hy]
        exact model
    · left
      refine ⟨hT, U, mem_powerset.mpr fun z hz => ?_, ?_⟩
      · rcases mem_insert.mp (hU hz) with rfl | h
        · exact absurd hz hy
        · exact h
      · rw [eval_condition, update_assignmentOf_false (by simp [hTy, hy])]
        exact model
  · rintro (⟨hT, U, hU, model⟩ | ⟨hT, U, hU, model⟩)
    · refine ⟨hT, U, mem_powerset.mpr ((mem_powerset.mp hU).trans (subset_insert _ _)), ?_⟩
      have hTy : y ∉ T := fun h => hX (mem_powerset.mp hT h)
      have hUy : y ∉ U := fun h => hE (mem_powerset.mp hU h)
      rw [eval_condition, update_assignmentOf_false (by simp [hTy, hUy])] at model
      exact model
    · refine ⟨hT, insert y U, mem_powerset.mpr (insert_subset_insert _ (mem_powerset.mp hU)), ?_⟩
      rw [eval_condition, update_assignmentOf_true] at model
      rw [union_insert]
      exact model

/-- The projected count with an auxiliary variable is at most the sum of the two branches. -/
theorem projCount_insert_aux_le {X E : Finset V} {y : V} (hX : y ∉ X) (hE : y ∉ E) (F : Formula V) :
    F.projCount X (insert y E) ≤ (F.condition y false).projCount X E + (F.condition y true).projCount X E := by
  unfold projCount
  rw [projModels_insert_aux hX hE]
  exact card_union_le _ _

/-- **Equality holds exactly when no visible assignment extends both ways.** -/
theorem projCount_insert_aux_eq_iff {X E : Finset V} {y : V} (hX : y ∉ X) (hE : y ∉ E) (F : Formula V) :
    F.projCount X (insert y E) = (F.condition y false).projCount X E + (F.condition y true).projCount X E ↔
      Disjoint ((F.condition y false).projModels X E) ((F.condition y true).projModels X E) := by
  unfold projCount
  rw [projModels_insert_aux hX hE, ← card_union_add_card_inter]
  constructor
  · intro h
    rw [disjoint_iff_inter_eq_empty, ← card_eq_zero]
    omega
  · intro h
    rw [disjoint_iff_inter_eq_empty.mp h, card_empty, add_zero]

/-! ## Component decomposition -/

omit [DecidableEq V] in
theorem eval_congr_on {F : Formula V} {S : Set V} (h : F.VarsIn S) {σ τ : V → Bool} (same : ∀ x ∈ S, σ x = τ x) :
    F.eval σ = F.eval τ :=
  eval_congr fun c hc l hl => same _ (h c hc l hl)

theorem assignmentOf_eq_on {A B : Finset V} {S : Set V} (same : ∀ x ∈ S, (x ∈ A ↔ x ∈ B)) :
    ∀ x ∈ S, assignmentOf A x = assignmentOf B x := by
  intro x hx
  simp only [assignmentOf]
  exact decide_eq_decide.mpr (same x hx)

/-- **Projected component decomposition**: if the variables of `F` (visible and auxiliary) and
those of `G` are disjoint and each formula uses only its own, the projected count of `F ∧ G` is
the product. -/
theorem projCount_append {X₁ E₁ X₂ E₂ : Finset V} (apart : Disjoint (X₁ ∪ E₁) (X₂ ∪ E₂)) {F G : Formula V} (hF : F.VarsIn ↑(X₁ ∪ E₁))
    (hG : G.VarsIn ↑(X₂ ∪ E₂)) :
    (F ++ G).projCount (X₁ ∪ X₂) (E₁ ∪ E₂) = F.projCount X₁ E₁ * G.projCount X₂ E₂ := by
  unfold projCount
  rw [← card_product]
  -- disjointness facts
  have d : ∀ x, x ∈ X₁ ∪ E₁ → x ∉ X₂ ∪ E₂ := fun x h1 h2 => disjoint_left.mp apart h1 h2
  apply card_nbij' (fun T => (T ∩ X₁, T ∩ X₂)) (fun p => p.1 ∪ p.2)
  · intro T hT
    simp only [projModels, coe_filter, Set.mem_ofPred_eq, mem_powerset, Extends] at hT
    obtain ⟨sub, U, hU, model⟩ := hT
    rw [eval_append, Bool.and_eq_true] at model
    simp only [coe_product, Set.mem_prod, projModels, coe_filter, Set.mem_ofPred_eq, mem_powerset, Extends]
    refine ⟨⟨inter_subset_right, U ∩ E₁, inter_subset_right, ?_⟩,
      ⟨inter_subset_right, U ∩ E₂, inter_subset_right, ?_⟩⟩
    · rw [← model.1]
      refine eval_congr_on hF (assignmentOf_eq_on fun x hx => ?_)
      have hx' : x ∈ X₁ ∪ E₁ := by simpa using hx
      have out := d x hx'
      simp only [mem_union, mem_inter, not_or] at out hx' ⊢
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · rcases mem_union.mp (sub h) with h' | h'
          · exact Or.inl ⟨h, h'⟩
          · exact absurd h' out.1
        · rcases mem_union.mp (hU h) with h' | h'
          · exact Or.inr ⟨h, h'⟩
          · exact absurd h' out.2
    · rw [← model.2]
      refine eval_congr_on hG (assignmentOf_eq_on fun x hx => ?_)
      have hx' : x ∈ X₂ ∪ E₂ := by simpa using hx
      have out : x ∉ X₁ ∪ E₁ := fun h => d x h hx'
      simp only [mem_union, mem_inter, not_or] at out hx' ⊢
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · rcases mem_union.mp (sub h) with h' | h'
          · exact absurd h' out.1
          · exact Or.inl ⟨h, h'⟩
        · rcases mem_union.mp (hU h) with h' | h'
          · exact absurd h' out.2
          · exact Or.inr ⟨h, h'⟩
  · rintro ⟨T₁, T₂⟩ hp
    simp only [coe_product, Set.mem_prod, projModels, coe_filter, Set.mem_ofPred_eq, mem_powerset, Extends] at hp
    obtain ⟨⟨sub₁, U₁, hU₁, model₁⟩, ⟨sub₂, U₂, hU₂, model₂⟩⟩ := hp
    simp only [projModels, coe_filter, Set.mem_ofPred_eq, mem_powerset, Extends]
    refine ⟨union_subset_union sub₁ sub₂, U₁ ∪ U₂, union_subset_union hU₁ hU₂, ?_⟩
    rw [eval_append, Bool.and_eq_true]
    constructor
    · rw [← model₁]
      refine eval_congr_on hF (assignmentOf_eq_on fun x hx => ?_)
      have hx' : x ∈ X₁ ∪ E₁ := by simpa using hx
      have out := d x hx'
      simp only [mem_union, not_or] at out hx' ⊢
      constructor
      · rintro ((h | h) | (h | h))
        · exact Or.inl h
        · exact absurd (sub₂ h) out.1
        · exact Or.inr h
        · exact absurd (hU₂ h) out.2
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
    · rw [← model₂]
      refine eval_congr_on hG (assignmentOf_eq_on fun x hx => ?_)
      have hx' : x ∈ X₂ ∪ E₂ := by simpa using hx
      have out : x ∉ X₁ ∪ E₁ := fun h => d x h hx'
      simp only [mem_union, not_or] at out hx' ⊢
      constructor
      · rintro ((h | h) | (h | h))
        · exact absurd (sub₁ h) out.1
        · exact Or.inl h
        · exact absurd (hU₁ h) out.2
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
  · intro T hT
    simp only [projModels, coe_filter, Set.mem_ofPred_eq, mem_powerset] at hT
    simp only
    rw [← inter_union_distrib_left, inter_eq_left.mpr hT.1]
  · rintro ⟨T₁, T₂⟩ hp
    simp only [coe_product, Set.mem_prod, projModels, coe_filter, Set.mem_ofPred_eq, mem_powerset] at hp
    have dx : Disjoint X₁ X₂ := disjoint_of_subset_left subset_union_left (disjoint_of_subset_right subset_union_left apart)
    simp only [Prod.mk.injEq]
    constructor
    · rw [union_inter_distrib_right, inter_eq_left.mpr hp.1.1,
        disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hp.2.1 dx.symm), union_empty]
    · rw [union_inter_distrib_right, inter_eq_left.mpr hp.2.1,
        disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_left hp.1.1 dx), empty_union]

/-! ## Auxiliary variables by definition -/

/-- The clauses `D` determine `y` uniquely from every assignment of `S`. -/
def Defines (S : Finset V) (y : V) (D : Formula V) : Prop :=
  ∀ T ⊆ S, ∃! b : Bool, D.eval (Function.update (assignmentOf T) y b) = true

theorem existsUnique_bool {p : Bool → Prop} [DecidablePred p] : (∃! b, p b) ↔ (p false ↔ ¬ p true) := by
  constructor
  · rintro ⟨b, hb, unique⟩
    cases b
    · exact ⟨fun _ h => absurd (unique true h) (by simp), fun _ => hb⟩
    · exact ⟨fun h => absurd (unique false h) (by simp), fun h => absurd hb h⟩
  · intro h
    by_cases h1 : p true
    · exact ⟨true, h1, fun b hb => by cases b; exact absurd h1 (h.mp hb); rfl⟩
    · exact ⟨false, h.mpr h1, fun b hb => by cases b; rfl; exact absurd hb h1⟩

/-- A decidable form of `Defines`. -/
theorem defines_iff (S : Finset V) (y : V) (D : Formula V) :
    Defines S y D ↔ ∀ T ∈ S.powerset, (D.eval (Function.update (assignmentOf T) y false) = true ↔
      ¬ D.eval (Function.update (assignmentOf T) y true) = true) := by
  unfold Defines
  simp only [mem_powerset, existsUnique_bool]

theorem ite_add_ite_unique {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] (h : r → (p ∨ q) ∧ ¬ (p ∧ q))
    (hp : p → r) (hq : q → r) :
    ((if p then 1 else 0) + (if q then 1 else 0) : ℕ) = if r then 1 else 0 := by
  by_cases hr : r
  · obtain ⟨one, notBoth⟩ := h hr
    rw [if_pos hr]
    rcases one with hp' | hq'
    · rw [if_pos hp', if_neg fun hq' => notBoth ⟨hp', hq'⟩]
    · rw [if_neg fun hp' => notBoth ⟨hp', hq'⟩, if_pos hq']
  · rw [if_neg hr, if_neg fun h => hr (hp h), if_neg fun h => hr (hq h)]

/-- **Adding a defined variable keeps the count.** If `y ∉ S`, `F` uses only `S`, and `D`
determines `y` from every assignment of `S`, then `F ∧ D` has as many models over `S ∪ {y}` as `F`
over `S`. -/
theorem count_define {S : Finset V} {y : V} (hy : y ∉ S) {F D : Formula V} (hF : F.VarsIn ↑S)
    (defines : Defines S y D) : (F ++ D).count (insert y S) = F.count S := by
  rw [count_insert hy, count, count, count, card_filter, card_filter, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun T hT => ?_
  have hT' : T ⊆ S := mem_powerset.mp hT
  have fixed : ∀ b, F.eval (Function.update (assignmentOf T) y b) = F.eval (assignmentOf T) := fun b =>
    eval_congr_on hF fun x hx => by
      have : x ≠ y := fun same => hy (same ▸ hx)
      rw [Function.update_of_ne this]
  simp only [condition_append, eval_append, eval_condition, fixed, Bool.and_eq_true]
  obtain ⟨b, hb, unique⟩ := defines T hT'
  apply ite_add_ite_unique
  · rintro hFT
    refine ⟨?_, ?_⟩
    · cases b
      · exact Or.inl ⟨hFT, hb⟩
      · exact Or.inr ⟨hFT, hb⟩
    · rintro ⟨⟨-, h0⟩, -, h1⟩
      have := (unique false h0).trans (unique true h1).symm
      cases this
  · exact fun h => h.1
  · exact fun h => h.1

/-- **Projecting away a defined variable keeps the count.** -/
theorem projCount_define {S : Finset V} {y : V} (hy : y ∉ S) {F D : Formula V} (hF : F.VarsIn ↑S)
    (defines : Defines S y D) : (F ++ D).projCount S {y} = F.count S := by
  unfold projCount projModels count
  congr 1
  apply filter_congr
  intro T hT
  have hT' : T ⊆ S := mem_powerset.mp hT
  have fixed : ∀ b, F.eval (Function.update (assignmentOf T) y b) = F.eval (assignmentOf T) := fun b =>
    eval_congr_on hF fun x hx => by
      have : x ≠ y := fun same => hy (same ▸ hx)
      rw [Function.update_of_ne this]
  have hyT : y ∉ T := fun h => hy (hT' h)
  have single : T ∪ {y} = insert y T := by rw [union_comm, ← insert_eq]
  obtain ⟨b, hb, -⟩ := defines T hT'
  unfold Extends
  constructor
  · rintro ⟨U, hU, model⟩
    rw [eval_append, Bool.and_eq_true] at model
    rcases subset_singleton_iff.mp (mem_powerset.mp hU) with rfl | rfl
    · rw [union_empty] at model
      exact model.1
    · rw [single, ← update_assignmentOf_true, fixed] at model
      exact model.1
  · intro hFT
    cases b
    · refine ⟨∅, mem_powerset.mpr (empty_subset _), ?_⟩
      rw [union_empty, eval_append, hFT, ← update_assignmentOf_false hyT, hb]
      rfl
    · refine ⟨{y}, mem_powerset.mpr (Subset.refl _), ?_⟩
      rw [eval_append, single, ← update_assignmentOf_true, fixed, hFT, hb]
      rfl

end Formula

end Mettapedia.Logic.ASP.CNF
