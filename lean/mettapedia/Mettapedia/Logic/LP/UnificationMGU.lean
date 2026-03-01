import Mettapedia.Logic.LP.Unification

/-!
# Logic Programming Kernel: Most General Unifier Property

The main result: `unifyFuel` returns the most general unifier (MGU).

## Design

The MGU property states that if `unifyFuel` returns `θ`, then any other
unifier `δ` of the same equations factors through `θ`: `∃ ρ, δ = ρ ∘ₛ θ`.

The proof follows the same fuel-induction and 9-way case split as
`unifyFuel_sound`. The key new ingredient is the **absorption lemma**:
if `δ v = δ.applyTerm t`, then `δ ∘ₛ single v t = δ`.

## References

- Martelli & Montanari, "An Efficient Unification Algorithm", 1982
- Ribeiro et al., "A Mechanized Textbook Proof of a Unification Algorithm" (SBMF 2015)
- Lloyd, *Foundations of Logic Programming*, Theorem 2.1
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Absorption lemmas -/

/-- If `δ v = δ.applyTerm t`, then `single v t` is absorbed by `δ`:
    composing with it is the identity. -/
theorem Subst.absorb_single {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (t : Term σ) (δ : Subst σ) (h : δ v = δ.applyTerm t) :
    δ ∘ₛ Subst.single v t = δ := by
  funext w
  simp only [Subst.comp, Subst.single]
  split
  · rename_i heq; subst heq; exact h.symm
  · simp [Subst.applyTerm]

/-- Corollary: absorption at the term level. -/
theorem Subst.absorb_single_applyTerm {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (t : Term σ) (δ : Subst σ) (h : δ v = δ.applyTerm t)
    (s : Term σ) :
    δ.applyTerm ((Subst.single v t).applyTerm s) = δ.applyTerm s := by
  rw [← Subst.applyTerm_comp, absorb_single v t δ h]

/-! ## Section 2: Transfer unification through elimination -/

/-- If δ unifies `(var v, t) :: rest` and v ∉ FV(t), then δ unifies
    `(single v t).applyEqs rest`. -/
private theorem unifies_applyEqs_of_eliminate {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (t : Term σ) (rest : List (Term σ × Term σ)) (δ : Subst σ)
    (hv : δ v = δ.applyTerm t) (hrest : Unifies δ rest) :
    Unifies δ ((Subst.single v t).applyEqs rest) := by
  intro p hp
  simp only [Subst.applyEqs, List.mem_map] at hp
  obtain ⟨⟨s₁, s₂⟩, hq, rfl⟩ := hp
  show δ.applyTerm ((Subst.single v t).applyTerm s₁) =
       δ.applyTerm ((Subst.single v t).applyTerm s₂)
  simp only [Subst.absorb_single_applyTerm v t δ hv]
  exact hrest (s₁, s₂) hq

/-- Symmetric version: if δ unifies `(t, var v) :: rest` and v ∉ FV(t). -/
private theorem unifies_applyEqs_of_eliminate_sym {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (t : Term σ) (rest : List (Term σ × Term σ)) (δ : Subst σ)
    (hv : δ.applyTerm t = δ v) (hrest : Unifies δ rest) :
    Unifies δ ((Subst.single v t).applyEqs rest) :=
  unifies_applyEqs_of_eliminate v t rest δ hv.symm hrest

/-! ## Section 3: MGU transfer through elimination -/

/-- If `θ'.moreGeneral δ` and `δ v = δ.applyTerm t`, then
    `(θ' ∘ₛ single v t).moreGeneral δ`. -/
private theorem mgu_transfer_eliminate {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (t : Term σ) (θ' δ : Subst σ)
    (hv : δ v = δ.applyTerm t) (hmgu : θ'.moreGeneral δ) :
    (θ' ∘ₛ Subst.single v t).moreGeneral δ := by
  obtain ⟨ρ, hρ⟩ := hmgu
  have hδ_eq : ρ ∘ₛ θ' = δ := funext fun u => (hρ u).symm
  refine ⟨ρ, fun w => ?_⟩
  show δ w = ρ.applyTerm ((θ' ∘ₛ Subst.single v t) w)
  simp only [Subst.comp]
  rw [← Subst.applyTerm_comp ρ θ', hδ_eq]
  exact (congr_fun (Subst.absorb_single v t δ hv) w).symm

/-! ## Section 4: Decompose helper -/

/-- If δ.applyTerm (app f ts) = δ.applyTerm (app f us), then δ unifies
    each pair (ts i, us i). -/
private theorem unifies_of_app_eq {σ : LPSignature}
    {f : σ.functionSymbols} {ts us : Fin (σ.functionArity f) → Term σ}
    {δ : Subst σ}
    (h : δ.applyTerm (.app f ts) = δ.applyTerm (.app f us)) :
    ∀ i, δ.applyTerm (ts i) = δ.applyTerm (us i) := by
  simp [Subst.applyTerm] at h
  exact fun i => congr_fun h i

/-- δ unifies finPairsToList when it unifies each pair pointwise. -/
private theorem unifies_finPairsToList {σ : LPSignature} {n : ℕ}
    {ts us : Fin n → Term σ} {δ : Subst σ}
    (h : ∀ i, δ.applyTerm (ts i) = δ.applyTerm (us i)) :
    Unifies δ (finPairsToList ts us) := by
  intro p hp
  simp [finPairsToList, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact h i

/-- δ unifying a list and additional rest means it unifies the appended list. -/
private theorem unifies_append {σ : LPSignature} {δ : Subst σ}
    {eqs₁ eqs₂ : List (Term σ × Term σ)}
    (h₁ : Unifies δ eqs₁) (h₂ : Unifies δ eqs₂) :
    Unifies δ (eqs₁ ++ eqs₂) := by
  intro p hp
  simp [List.mem_append] at hp
  rcases hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

/-! ## Section 5: Main MGU theorem -/

/-- **MGU property**: if `unifyFuel` returns `θ`, then `θ` is a most general
    unifier — every other unifier factors through it.

    Formally: if `Unifies δ eqs`, then `θ.moreGeneral δ`. -/
theorem unifyFuel_mgu {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (fuel : ℕ) (eqs : List (Term σ × Term σ)) (θ : Subst σ)
    (h : unifyFuel fuel eqs = some θ)
    (δ : Subst σ) (hδ : Unifies δ eqs) :
    θ.moreGeneral δ := by
  induction fuel generalizing eqs θ with
  | zero => simp [unifyFuel] at h
  | succ n ih =>
    match eqs with
    | [] =>
      simp [unifyFuel] at h; subst h
      exact Subst.id_moreGeneral δ
    | (s, t) :: rest =>
      have hδ_pair : δ.applyTerm s = δ.applyTerm t :=
        hδ (s, t) (List.mem_cons_self ..)
      have hδ_rest : Unifies δ rest :=
        fun p hp => hδ p (List.mem_cons.mpr (Or.inr hp))
      rcases s with v | c | ⟨f, ts⟩ <;> rcases t with w | c' | ⟨g, us⟩ <;>
        simp only [unifyFuel] at h
      -- var v = var w
      · split at h
        · rename_i hvw; subst hvw
          exact ih rest θ h hδ_rest
        · rename_i hvw
          split at h <;> [simp at h; skip]
          rename_i θ' hθ'; simp at h; subst h
          have hv : δ v = δ.applyTerm (.var w) := hδ_pair
          simp [Subst.applyTerm] at hv
          exact mgu_transfer_eliminate v (.var w) θ' δ
            (by simp [Subst.applyTerm]; exact hv)
            (ih _ θ' hθ' (unifies_applyEqs_of_eliminate v (.var w) rest δ
              (by simp [Subst.applyTerm]; exact hv) hδ_rest))
      -- var v = const c'
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        exact mgu_transfer_eliminate v (.const c') θ' δ hδ_pair
          (ih _ θ' hθ' (unifies_applyEqs_of_eliminate v (.const c') rest δ hδ_pair hδ_rest))
      -- var v = app g us
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        exact mgu_transfer_eliminate v (.app g us) θ' δ hδ_pair
          (ih _ θ' hθ' (unifies_applyEqs_of_eliminate v (.app g us) rest δ hδ_pair hδ_rest))
      -- const c = var w
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        exact mgu_transfer_eliminate w (.const c) θ' δ hδ_pair.symm
          (ih _ θ' hθ' (unifies_applyEqs_of_eliminate w (.const c) rest δ hδ_pair.symm hδ_rest))
      -- const c = const c'
      · split at h
        · rename_i hcc; subst hcc
          exact ih rest θ h hδ_rest
        · simp at h
      -- const c = app g us: impossible
      · simp at h
      -- app f ts = var w
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        exact mgu_transfer_eliminate w (.app f ts) θ' δ hδ_pair.symm
          (ih _ θ' hθ' (unifies_applyEqs_of_eliminate w (.app f ts) rest δ hδ_pair.symm hδ_rest))
      -- app f ts = const c': impossible
      · simp at h
      -- app f ts = app g us: decompose
      · split at h
        · rename_i hfg; subst hfg
          exact ih _ θ h (unifies_append
            (unifies_finPairsToList (unifies_of_app_eq hδ_pair))
            hδ_rest)
        · simp at h

/-! ## Section 6: Derived properties -/

/-- MGU for term unification. -/
theorem unifyTerms_mgu {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (s t : Term σ) (fuel : ℕ) (θ : Subst σ) (h : unifyTerms s t fuel = some θ)
    (δ : Subst σ) (hδ : δ.applyTerm s = δ.applyTerm t) :
    θ.moreGeneral δ := by
  apply unifyFuel_mgu fuel [(s, t)] θ h δ
  intro p hp; simp at hp; subst hp; exact hδ

/-- MGU for atom unification. -/
theorem unifyAtoms_mgu {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (a b : Atom σ) (fuel : ℕ) (θ : Subst σ)
    (h : unifyAtoms a b fuel = some θ)
    (δ : Subst σ) (hδ : δ.applyAtom a = δ.applyAtom b) :
    θ.moreGeneral δ := by
  obtain ⟨sa, argsa⟩ := a; obtain ⟨sb, argsb⟩ := b
  unfold unifyAtoms at h
  split at h
  · rename_i hsym; dsimp only at hsym h; subst hsym
    apply unifyFuel_mgu fuel _ θ h δ
    apply unifies_finPairsToList
    intro i
    have hargs : ∀ j, δ.applyTerm (argsa j) = δ.applyTerm (argsb j) := by
      have h1 := hδ; simp [Subst.applyAtom] at h1
      exact fun j => congr_fun h1 j
    exact hargs i
  · simp at h

end Mettapedia.Logic.LP
