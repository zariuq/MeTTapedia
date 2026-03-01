import Mettapedia.Logic.LP.Substitution

/-!
# Logic Programming Kernel: Unification (Martelli-Montanari)

First-order unification over LP signatures with function symbols.

## Design

- `Term.occursIn` — decidable occurs check.
- `unifyFuel` — fuel-bounded unification via Martelli-Montanari rules:
  delete, decompose, orient, eliminate, conflict, occurs-check failure.
- `unifyFuel_sound` — if unification succeeds, the returned substitution unifies.
- `Subst.single_applyTerm_not_occursIn` — key lemma: `single v s` is the identity on
  terms not containing `v`.

## References

- Martelli & Montanari, "An Efficient Unification Algorithm", 1982
- Lloyd, *Foundations of Logic Programming*, Ch. 1
- Ribeiro et al., "A Mechanized Textbook Proof of a Unification Algorithm" (SBMF 2015)
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Occurs check -/

/-- Check if a variable occurs in a term. -/
def Term.occursIn [DecidableEq σ.vars] (v : σ.vars) : Term σ → Bool
  | .var w => v == w
  | .const _ => false
  | .app f ts => (List.finRange (σ.functionArity f)).any (fun i => occursIn v (ts i))

/-! ## Section 2: Equation helpers -/

/-- Apply a substitution to a list of equations. -/
def Subst.applyEqs {σ : LPSignature} (θ : Subst σ) :
    List (Term σ × Term σ) → List (Term σ × Term σ) :=
  List.map (fun (s, t) => (θ.applyTerm s, θ.applyTerm t))

/-- Convert Fin-indexed pairs to a list of equations. -/
def finPairsToList {σ : LPSignature} {n : ℕ}
    (ts us : Fin n → Term σ) : List (Term σ × Term σ) :=
  (List.finRange n).map (fun i => (ts i, us i))

/-! ## Section 3: Substitution lemma for occurs check -/

/-- A single-variable substitution is the identity on terms not containing that variable. -/
theorem Subst.single_applyTerm_not_occursIn {σ : LPSignature} [DecidableEq σ.vars]
    (v : σ.vars) (s t : Term σ) (h : t.occursIn v = false) :
    (Subst.single v s).applyTerm t = t := by
  induction t with
  | var w =>
    simp [Term.occursIn] at h
    simp [Subst.applyTerm, Subst.single, Ne.symm h]
  | const _ => rfl
  | app f ts ih =>
    simp [Subst.applyTerm]; funext i; apply ih i
    simp [Term.occursIn] at h; have := h i; simpa using this

/-! ## Section 4: Unification algorithm -/

/-- Unification via Martelli-Montanari with explicit fuel.
    Returns `none` on failure or fuel exhaustion; `some θ` on success.

    Rules applied:
    - **Delete**: `var v = var v` — skip, unify rest.
    - **Eliminate**: `var v = t` (v ∉ FV(t)) — substitute `v ↦ t` in rest, compose.
    - **Orient**: `t = var v` — handled symmetrically to eliminate.
    - **Decompose**: `app f ts = app f us` — unify arguments pointwise.
    - **Conflict**: mismatched constructors — fail.
    - **Occurs check**: `var v = t` with v ∈ FV(t) — fail (prevents infinite terms). -/
def unifyFuel {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] :
    ℕ → List (Term σ × Term σ) → Option (Subst σ)
  | 0, _ => none
  | _, [] => some (Subst.id σ)
  | fuel + 1, (s, t) :: rest =>
    match s with
    | .var v =>
      match t with
      | .var w =>
        if v = w then unifyFuel fuel rest
        else match unifyFuel fuel ((Subst.single v (.var w)).applyEqs rest) with
          | none => none
          | some θ' => some (θ' ∘ₛ Subst.single v (.var w))
      | t =>
        if t.occursIn v then none
        else match unifyFuel fuel ((Subst.single v t).applyEqs rest) with
          | none => none
          | some θ' => some (θ' ∘ₛ Subst.single v t)
    | .const c =>
      match t with
      | .var v =>
        if (Term.const c).occursIn v then none
        else match unifyFuel fuel ((Subst.single v (.const c)).applyEqs rest) with
          | none => none
          | some θ' => some (θ' ∘ₛ Subst.single v (.const c))
      | .const c' => if c = c' then unifyFuel fuel rest else none
      | .app _ _ => none
    | .app f ts =>
      match t with
      | .var v =>
        if (Term.app f ts).occursIn v then none
        else match unifyFuel fuel ((Subst.single v (.app f ts)).applyEqs rest) with
          | none => none
          | some θ' => some (θ' ∘ₛ Subst.single v (.app f ts))
      | .const _ => none
      | .app g us =>
        if h : f = g then unifyFuel fuel (finPairsToList ts (h ▸ us) ++ rest)
        else none

/-- Convenience wrapper: unify two terms with default fuel. -/
def unifyTerms {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (s t : Term σ) (fuel : ℕ := 1000) :
    Option (Subst σ) :=
  unifyFuel fuel [(s, t)]

/-- Unify two atoms (same symbol required). -/
def unifyAtoms {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (a b : Atom σ) (fuel : ℕ := 1000) : Option (Subst σ) :=
  if h : a.symbol = b.symbol then
    unifyFuel fuel (finPairsToList a.args (h ▸ b.args))
  else none

/-! ## Section 5: Soundness -/

/-- A substitution unifies an equation list if it makes both sides equal. -/
def Unifies {σ : LPSignature} (θ : Subst σ) (eqs : List (Term σ × Term σ)) : Prop :=
  ∀ p ∈ eqs, θ.applyTerm p.1 = θ.applyTerm p.2

/-- Soundness helper: elimination unifies the eliminated pair `(var v, t)`. -/
private theorem elim_pair {σ : LPSignature} [DecidableEq σ.vars]
    (θ' : Subst σ) (v : σ.vars) (t : Term σ) (hocc : t.occursIn v = false) :
    (θ' ∘ₛ Subst.single v t).applyTerm (.var v) =
    (θ' ∘ₛ Subst.single v t).applyTerm t := by
  simp [Subst.comp, Subst.applyTerm, Subst.single, Subst.applyTerm_comp,
        Subst.single_applyTerm_not_occursIn v t t hocc]

/-- Soundness helper: composition transfers unification through `applyEqs`. -/
private theorem elim_rest {σ : LPSignature}
    (θ' θ : Subst σ) (rest : List (Term σ × Term σ))
    (h : Unifies θ' (θ.applyEqs rest)) :
    Unifies (θ' ∘ₛ θ) rest := by
  intro p hp
  have hmem : (θ.applyTerm p.1, θ.applyTerm p.2) ∈ θ.applyEqs rest :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have := h _ hmem
  simp [Subst.applyTerm_comp] at this ⊢; exact this

/-- Helper to convert `¬ (b = true)` to `b = false`. -/
private theorem Bool.not_eq_true_to_eq_false {b : Bool} (h : ¬ (b = true)) : b = false := by
  cases b <;> simp_all

/-- **Soundness**: if `unifyFuel` returns `some θ`, then `θ` unifies the equation list. -/
theorem unifyFuel_sound {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (fuel : ℕ) (eqs : List (Term σ × Term σ)) (θ : Subst σ)
    (h : unifyFuel fuel eqs = some θ) : Unifies θ eqs := by
  induction fuel generalizing eqs θ with
  | zero => simp [unifyFuel] at h
  | succ n ih =>
    match eqs with
    | [] => simp [unifyFuel] at h; subst h; intro p hp; simp at hp
    | (s, t) :: rest =>
      intro p hp; simp only [List.mem_cons] at hp
      rcases s with v | c | ⟨f, ts⟩ <;> rcases t with w | c' | ⟨g, us⟩ <;>
        simp only [unifyFuel] at h
      -- var v = var w
      · split at h
        · rename_i hvw; subst hvw
          rcases hp with rfl | hp <;> [rfl; exact ih rest θ h p hp]
        · rename_i hvw
          split at h <;> [simp at h; skip]
          rename_i θ' hθ'; simp at h; subst h
          rcases hp with rfl | hp
          · exact elim_pair θ' v (.var w) (by simp [Term.occursIn, hvw])
          · exact elim_rest θ' _ rest (ih _ θ' hθ') p hp
      -- var v = const c'
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        rcases hp with rfl | hp
        · exact elim_pair θ' v (.const c') rfl
        · exact elim_rest θ' _ rest (ih _ θ' hθ') p hp
      -- var v = app g us
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        rcases hp with rfl | hp
        · exact elim_pair θ' v (.app g us) (Bool.not_eq_true_to_eq_false hocc)
        · exact elim_rest θ' _ rest (ih _ θ' hθ') p hp
      -- const c = var w
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        rcases hp with rfl | hp
        · exact (elim_pair θ' w (.const c) rfl).symm
        · exact elim_rest θ' _ rest (ih _ θ' hθ') p hp
      -- const c = const c'
      · split at h
        · rename_i hcc; subst hcc
          rcases hp with rfl | hp <;> [rfl; exact ih rest θ h p hp]
        · simp at h
      -- const c = app g us: impossible
      · simp at h
      -- app f ts = var w
      · split at h <;> [simp at h; skip]
        split at h <;> [simp at h; skip]
        rename_i hocc _ θ' hθ'; simp at h; subst h
        rcases hp with rfl | hp
        · exact (elim_pair θ' w (.app f ts)
            (Bool.not_eq_true_to_eq_false hocc)).symm
        · exact elim_rest θ' _ rest (ih _ θ' hθ') p hp
      -- app f ts = const c': impossible
      · simp at h
      -- app f ts = app g us: decompose
      · split at h
        · rename_i hfg; subst hfg
          have hunif := ih _ θ h
          rcases hp with rfl | hp
          · simp only [Subst.applyTerm_app, Term.app.injEq, heq_eq_eq, true_and]
            funext i
            exact hunif (ts i, us i) (by
              simp only [List.mem_append, finPairsToList, List.mem_map,
                         List.mem_finRange, true_and]
              exact Or.inl ⟨i, rfl⟩)
          · exact hunif p (List.mem_append_right _ hp)
        · simp at h

/-! ## Section 6: Derived properties -/

/-- If unifying two terms succeeds, the substitution makes them equal. -/
theorem unifyTerms_sound {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (s t : Term σ) (fuel : ℕ) (θ : Subst σ) (h : unifyTerms s t fuel = some θ) :
    θ.applyTerm s = θ.applyTerm t := by
  have := unifyFuel_sound fuel [(s, t)] θ h
  exact this (s, t) (by simp)

/-- If unifying two atoms succeeds, the substitution makes them equal. -/
theorem unifyAtoms_sound {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (a b : Atom σ) (fuel : ℕ) (θ : Subst σ) (h : unifyAtoms a b fuel = some θ) :
    θ.applyAtom a = θ.applyAtom b := by
  obtain ⟨sa, argsa⟩ := a; obtain ⟨sb, argsb⟩ := b
  unfold unifyAtoms at h
  split at h
  · rename_i hsym; dsimp only at hsym h; subst hsym
    simp [Subst.applyAtom]
    funext i
    have hunif := unifyFuel_sound fuel (finPairsToList argsa argsb) θ h
    exact hunif (argsa i, argsb i) (by
      simp [finPairsToList, List.mem_map, List.mem_finRange]
      exact ⟨i, by simp, rfl⟩)
  · simp at h

end Mettapedia.Logic.LP
