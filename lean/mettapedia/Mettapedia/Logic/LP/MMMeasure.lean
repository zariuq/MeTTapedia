import Mettapedia.Logic.LP.Unification
import Mathlib.Algebra.BigOperators.Fin

/-!
# Logic Programming Kernel: Martelli-Montanari Measures

Global syntactic measures and one-step decrease lemmas used for completeness
arguments:
- variable-cardinality measure (`mmVarCount`)
- structural size measure (`mmSize`)
- rule-wise decrease bounds for delete/decompose/eliminate forms.
-/

namespace Mettapedia.Logic.LP

/-- Variables appearing in an equation list. -/
def eqVars {σ : LPSignature} [DecidableEq σ.vars] :
    List (Term σ × Term σ) → Finset σ.vars
  | [] => ∅
  | (s, t) :: rest => s.freeVars ∪ t.freeVars ∪ eqVars rest

/-- Total variable-cardinality measure. -/
def mmVarCount {σ : LPSignature} [DecidableEq σ.vars]
    (eqs : List (Term σ × Term σ)) : ℕ :=
  (eqVars eqs).card

/-- Structural equation-size measure. -/
def mmSize {σ : LPSignature} : List (Term σ × Term σ) → ℕ
  | [] => 0
  | (s, t) :: rest => s.size + t.size + mmSize rest

/-- Combined MM measure (lexicographic: vars first, then size). -/
def mmMeasure {σ : LPSignature} [DecidableEq σ.vars]
    (eqs : List (Term σ × Term σ)) : ℕ × ℕ :=
  (mmVarCount eqs, mmSize eqs)

private theorem not_mem_freeVars_of_occursIn_false {σ : LPSignature}
    [DecidableEq σ.vars] {v : σ.vars} :
    ∀ t : Term σ, t.occursIn v = false → v ∉ t.freeVars
  | .var w, h => by
      simp [Term.occursIn] at h
      simp [Term.freeVars, h]
  | .const c, _ => by
      simp [Term.freeVars]
  | .app f ts, h => by
      simp [Term.occursIn] at h
      intro hv
      simp [Term.freeVars] at hv
      rcases hv with ⟨i, hi⟩
      exact not_mem_freeVars_of_occursIn_false (ts i) (h i) hi

private theorem freeVars_applyTerm_single_subset {σ : LPSignature}
    [DecidableEq σ.vars] (v : σ.vars) (t : Term σ) :
    ∀ s : Term σ,
      ((Subst.single v t).applyTerm s).freeVars ⊆ s.freeVars ∪ t.freeVars
  | .var w => by
      by_cases h : w = v
      · subst h
        simp [Subst.applyTerm, Subst.single]
      · simp [Subst.applyTerm, Subst.single, h]
  | .const c => by
      simp [Subst.applyTerm, Term.freeVars]
  | .app f ts => by
      intro x hx
      simp [Subst.applyTerm, Term.freeVars] at hx ⊢
      rcases hx with ⟨i, hi⟩
      have hi' := freeVars_applyTerm_single_subset v t (ts i) hi
      rcases Finset.mem_union.mp hi' with hiL | hiR
      · exact Or.inl ⟨i, hiL⟩
      · exact Or.inr hiR

private theorem not_mem_freeVars_applyTerm_single {σ : LPSignature}
    [DecidableEq σ.vars] (v : σ.vars) (t : Term σ)
    (ht : t.occursIn v = false) :
    ∀ s : Term σ, v ∉ ((Subst.single v t).applyTerm s).freeVars
  | .var w => by
      by_cases h : w = v
      · have hvnot : v ∉ t.freeVars :=
          not_mem_freeVars_of_occursIn_false (v := v) t ht
        simpa [Subst.applyTerm, Subst.single, h] using hvnot
      · have hvw : v ≠ w := by
          intro hEq
          exact h hEq.symm
        simpa [Subst.applyTerm, Subst.single, h, Term.freeVars, Finset.mem_singleton] using hvw
  | .const c => by
      simp [Subst.applyTerm, Term.freeVars]
  | .app f ts => by
      intro hv
      simp [Subst.applyTerm, Term.freeVars] at hv
      rcases hv with ⟨i, hi⟩
      exact not_mem_freeVars_applyTerm_single v t ht (ts i) hi

private theorem eqVars_applyEqs_single_subset {σ : LPSignature}
    [DecidableEq σ.vars] (v : σ.vars) (t : Term σ)
    (rest : List (Term σ × Term σ)) :
    eqVars ((Subst.single v t).applyEqs rest) ⊆ eqVars rest ∪ t.freeVars := by
  induction rest with
  | nil =>
      simp [Subst.applyEqs, eqVars]
  | cons p rs ih =>
      rcases p with ⟨s, u⟩
      intro x hx
      simp [Subst.applyEqs, eqVars] at hx ⊢
      rcases hx with hs | hu | htail
      · have hs' : x ∈ s.freeVars ∪ t.freeVars :=
          freeVars_applyTerm_single_subset v t s hs
        rcases Finset.mem_union.mp hs' with hsL | hsT
        · exact Or.inl hsL
        · exact Or.inr <| Or.inr <| Or.inr hsT
      · have hu' : x ∈ u.freeVars ∪ t.freeVars :=
          freeVars_applyTerm_single_subset v t u hu
        rcases Finset.mem_union.mp hu' with huL | huT
        · exact Or.inr <| Or.inl huL
        · exact Or.inr <| Or.inr <| Or.inr huT
      · have htail' : x ∈ eqVars rs ∪ t.freeVars := ih htail
        rcases Finset.mem_union.mp htail' with hEq | hT
        · exact Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr hT

private theorem not_mem_eqVars_applyEqs_single {σ : LPSignature}
    [DecidableEq σ.vars] (v : σ.vars) (t : Term σ)
    (ht : t.occursIn v = false) :
    ∀ rest : List (Term σ × Term σ), v ∉ eqVars ((Subst.single v t).applyEqs rest)
  | [] => by
      simp [Subst.applyEqs, eqVars]
  | (s, u) :: rs => by
      intro hv
      simp [Subst.applyEqs, eqVars] at hv
      rcases hv with hs | hu | htail
      · exact not_mem_freeVars_applyTerm_single v t ht s hs
      · exact not_mem_freeVars_applyTerm_single v t ht u hu
      · exact not_mem_eqVars_applyEqs_single v t ht rs htail

/-- Elimination strictly decreases variable-cardinality measure. -/
theorem mmVarCount_eliminate_lt {σ : LPSignature}
    [DecidableEq σ.vars] (v : σ.vars) (t : Term σ)
    (rest : List (Term σ × Term σ))
    (ht : t.occursIn v = false) :
    mmVarCount ((Subst.single v t).applyEqs rest) <
      mmVarCount ((.var v, t) :: rest) := by
  let newEqs := ((Subst.single v t).applyEqs rest)
  let oldEqs := ((.var v, t) :: rest)
  have hsubsetNewOld :
      eqVars newEqs ⊆ eqVars oldEqs := by
    intro x hx
    have hx' :
        x ∈ eqVars rest ∪ t.freeVars :=
      eqVars_applyEqs_single_subset v t rest hx
    simp [oldEqs, eqVars, Finset.mem_union] at hx' ⊢
    rcases hx' with hEq | hT
    · exact Or.inr (Or.inr hEq)
    · exact Or.inr (Or.inl hT)
  have hvOld : v ∈ eqVars oldEqs := by
    change v ∈ (Term.var v).freeVars ∪ t.freeVars ∪ eqVars rest
    exact Finset.mem_union.mpr <| Or.inl <| by simp [Term.freeVars]
  have hvNotNew : v ∉ eqVars newEqs := by
    simpa [newEqs] using not_mem_eqVars_applyEqs_single v t ht rest
  have hssub : eqVars newEqs ⊂ eqVars oldEqs := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubsetNewOld, ?_⟩
    intro hEq
    have : v ∈ eqVars newEqs := by simpa [hEq] using hvOld
    exact hvNotNew this
  exact Finset.card_lt_card hssub

/-- Deletion (`var = var`) strictly decreases size measure. -/
theorem mmSize_var_eq_lt {σ : LPSignature}
    (v : σ.vars) (rest : List (Term σ × Term σ)) :
    mmSize rest < mmSize ((.var v, .var v) :: rest) := by
  simp [mmSize, Term.size]

/-- Deletion (`const = const`) strictly decreases size measure. -/
theorem mmSize_const_eq_lt {σ : LPSignature}
    (c : σ.constants) (rest : List (Term σ × Term σ)) :
    mmSize rest < mmSize ((.const c, .const c) :: rest) := by
  simp [mmSize, Term.size]

/-- Decompose rule, pointwise form: each generated pair is strictly smaller
than the original app/app equation in total term size. -/
theorem eqPairSize_decompose_component_lt {σ : LPSignature}
    (f : σ.functionSymbols) (ts us : Fin (σ.functionArity f) → Term σ)
    (i : Fin (σ.functionArity f)) :
    (ts i).size + (us i).size <
      (Term.app f ts).size + (Term.app f us).size := by
  have hti : (ts i).size < (Term.app f ts).size := Term.size_subterm i
  have hui : (us i).size < (Term.app f us).size := Term.size_subterm i
  omega

private theorem eqVars_append_eq_union {σ : LPSignature}
    [DecidableEq σ.vars] (xs ys : List (Term σ × Term σ)) :
    eqVars (xs ++ ys) = eqVars xs ∪ eqVars ys := by
  induction xs with
  | nil =>
      simp [eqVars]
  | cons p xs ih =>
      rcases p with ⟨s, t⟩
      simp [eqVars, ih, Finset.union_assoc, Finset.union_comm]

private theorem eqVars_finPairs_subset_app_union {σ : LPSignature}
    [DecidableEq σ.vars] (f : σ.functionSymbols)
    (ts us : Fin (σ.functionArity f) → Term σ) :
    eqVars (finPairsToList ts us) ⊆
      (Term.app f ts).freeVars ∪ (Term.app f us).freeVars := by
  let idxs : List (Fin (σ.functionArity f)) := List.finRange (σ.functionArity f)
  have hMap :
      ∀ L : List (Fin (σ.functionArity f)),
        eqVars (L.map (fun i => (ts i, us i))) ⊆
          (Term.app f ts).freeVars ∪ (Term.app f us).freeVars := by
    intro L
    induction L with
    | nil =>
        simp [eqVars]
    | cons i L ih =>
        intro x hx
        have hx' : x ∈ (ts i).freeVars ∪ (us i).freeVars ∪ eqVars (L.map (fun j => (ts j, us j))) := by
          simpa [eqVars] using hx
        rcases Finset.mem_union.mp hx' with hpair | htail
        · rcases Finset.mem_union.mp hpair with hts | hus
          · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_biUnion.mpr ⟨i, by simp, hts⟩
          · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_biUnion.mpr ⟨i, by simp, hus⟩
        · exact ih htail
  simpa [idxs, finPairsToList] using hMap idxs

/-- Decompose does not increase variable-cardinality measure. -/
theorem mmVarCount_app_eq_decompose_le {σ : LPSignature}
    [DecidableEq σ.vars]
    (f : σ.functionSymbols) (ts us : Fin (σ.functionArity f) → Term σ)
    (rest : List (Term σ × Term σ)) :
    mmVarCount (finPairsToList ts us ++ rest) ≤
      mmVarCount ((.app f ts, .app f us) :: rest) := by
  apply Finset.card_le_card
  intro x hx
  have hUnion :
      x ∈ eqVars (finPairsToList ts us) ∪ eqVars rest :=
    by
      simpa [eqVars_append_eq_union (finPairsToList ts us) rest] using hx
  rcases Finset.mem_union.mp hUnion with hpairs | hrest
  · have happ :
      x ∈ (Term.app f ts).freeVars ∪ (Term.app f us).freeVars :=
      eqVars_finPairs_subset_app_union f ts us hpairs
    have hhead : x ∈ (Term.app f ts).freeVars ∪ (Term.app f us).freeVars ∪ eqVars rest := by
      exact Finset.mem_union.mpr <| Or.inl happ
    simpa [eqVars, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hhead
  · have hhead : x ∈ (Term.app f ts).freeVars ∪ (Term.app f us).freeVars ∪ eqVars rest := by
      exact Finset.mem_union.mpr <| Or.inr hrest
    simpa [eqVars, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hhead

/-- Adding a head equation cannot decrease variable-cardinality measure. -/
theorem mmVarCount_cons_ge {σ : LPSignature}
    [DecidableEq σ.vars] (s t : Term σ) (rest : List (Term σ × Term σ)) :
    mmVarCount rest ≤ mmVarCount ((s, t) :: rest) := by
  apply Finset.card_le_card
  intro x hx
  have hhead : x ∈ (s.freeVars ∪ t.freeVars) ∪ eqVars rest := by
    exact Finset.mem_union.mpr <| Or.inr hx
  simpa [eqVars, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hhead

private theorem mmSize_append {σ : LPSignature}
    (xs ys : List (Term σ × Term σ)) :
    mmSize (xs ++ ys) = mmSize xs + mmSize ys := by
  induction xs with
  | nil =>
      simp [mmSize]
  | cons p xs ih =>
      rcases p with ⟨s, t⟩
      simp [mmSize, ih, Nat.add_assoc, Nat.add_comm]

private theorem list_sum_map_add {α : Type*} (L : List α) (f g : α → ℕ) :
    (L.map (fun x => f x + g x)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc, Nat.add_left_comm]

private theorem mmSize_map_pairs_eq_listSum {σ : LPSignature} {n : ℕ}
    (ts us : Fin n → Term σ) :
    ∀ L : List (Fin n),
      mmSize (L.map (fun i => (ts i, us i))) =
        (L.map (fun i => (ts i).size + (us i).size)).sum
  | [] => by simp [mmSize]
  | i :: L => by
      simp [mmSize, mmSize_map_pairs_eq_listSum ts us L, Nat.add_assoc]

private theorem mmSize_finPairsToList {σ : LPSignature} {n : ℕ}
    (ts us : Fin n → Term σ) :
    mmSize (finPairsToList ts us) =
      ∑ i : Fin n, ((ts i).size + (us i).size) := by
  let idxs : List (Fin n) := List.finRange n
  have hList :
      mmSize (idxs.map (fun i => (ts i, us i))) =
        (idxs.map (fun i => (ts i).size + (us i).size)).sum :=
    mmSize_map_pairs_eq_listSum ts us idxs
  have hFin :
      (idxs.map (fun i => (ts i).size + (us i).size)).sum =
        ∑ i : Fin n, ((ts i).size + (us i).size) := by
    have hAdd :
        (idxs.map (fun i => (ts i).size + (us i).size)).sum =
          (idxs.map (fun i => (ts i).size)).sum + (idxs.map (fun i => (us i).size)).sum :=
      list_sum_map_add idxs (fun i => (ts i).size) (fun i => (us i).size)
    have hs1 : (idxs.map (fun i => (ts i).size)).sum = ∑ i : Fin n, (ts i).size := by
      simpa [idxs] using (Fin.sum_univ_def (fun i : Fin n => (ts i).size)).symm
    have hs2 : (idxs.map (fun i => (us i).size)).sum = ∑ i : Fin n, (us i).size := by
      simpa [idxs] using (Fin.sum_univ_def (fun i : Fin n => (us i).size)).symm
    calc
      (idxs.map (fun i => (ts i).size + (us i).size)).sum
          = (idxs.map (fun i => (ts i).size)).sum + (idxs.map (fun i => (us i).size)).sum := hAdd
      _ = (∑ i : Fin n, (ts i).size) + (∑ i : Fin n, (us i).size) := by
            simp [hs1, hs2]
      _ = ∑ i : Fin n, ((ts i).size + (us i).size) := by
            simpa using
              (Finset.sum_add_distrib :
                (∑ i : Fin n, ((ts i).size + (us i).size)) =
                  (∑ i : Fin n, (ts i).size) + (∑ i : Fin n, (us i).size)).symm
  have hList' :
      mmSize (finPairsToList ts us) =
        (idxs.map (fun i => (ts i).size + (us i).size)).sum := by
    simpa [finPairsToList, idxs] using hList
  exact hList'.trans hFin

/-- Decompose strictly decreases structural size measure. -/
theorem mmSize_app_eq_decompose_lt {σ : LPSignature}
    (f : σ.functionSymbols) (ts us : Fin (σ.functionArity f) → Term σ)
    (rest : List (Term σ × Term σ)) :
    mmSize (finPairsToList ts us ++ rest) <
      mmSize ((.app f ts, .app f us) :: rest) := by
  have hPairs :
      mmSize (finPairsToList ts us) =
        ∑ i : Fin (σ.functionArity f), ((ts i).size + (us i).size) :=
    mmSize_finPairsToList ts us
  have hsum :
      (∑ i : Fin (σ.functionArity f), ((ts i).size + (us i).size)) =
        (∑ i : Fin (σ.functionArity f), (ts i).size) +
        (∑ i : Fin (σ.functionArity f), (us i).size) := by
    simpa using
      (Finset.sum_add_distrib :
        (∑ i : Fin (σ.functionArity f), ((ts i).size + (us i).size)) =
          (∑ i : Fin (σ.functionArity f), (ts i).size) +
            (∑ i : Fin (σ.functionArity f), (us i).size))
  rw [mmSize_append, hPairs]
  rw [hsum]
  simp [mmSize, Term.size]
  omega

end Mettapedia.Logic.LP
