import Mettapedia.Logic.LP.UnificationMGU
import Mettapedia.Logic.LP.MMMeasure
import Mathlib.Data.Prod.Lex

/-!
# Logic Programming Kernel: Unification Fuel Completeness

Completeness bridge for the fuel-bounded Martelli-Montanari implementation:
we factor successful unification through a fuel-free derivation relation and
prove that every derivation admits a concrete fuel budget for `unifyFuel`.

This module complements:
- `Unification.lean` (`unifyFuel_sound`)
- `UnificationMGU.lean` (most-general-unifier property when success occurs)
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Fuel-free successful derivations -/

/-- A fuel-free successful derivation for Martelli-Montanari rules.

`UnifyDerives eqs` means the equation list `eqs` can be reduced to success by
the same rule choices implemented in `unifyFuel`, but without any fuel budget.
-/
inductive UnifyDerives {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    List (Term σ × Term σ) → Prop where
  | nil :
      UnifyDerives []
  | var_eq (v : σ.vars) (rest : List (Term σ × Term σ)) :
      UnifyDerives rest →
      UnifyDerives ((.var v, .var v) :: rest)
  | var_subst (v : σ.vars) (t : Term σ) (rest : List (Term σ × Term σ))
      (hocc : t.occursIn v = false) :
      UnifyDerives ((Subst.single v t).applyEqs rest) →
      UnifyDerives ((.var v, t) :: rest)
  | const_eq (c : σ.constants) (rest : List (Term σ × Term σ)) :
      UnifyDerives rest →
      UnifyDerives ((.const c, .const c) :: rest)
  | const_var (c : σ.constants) (v : σ.vars) (rest : List (Term σ × Term σ)) :
      UnifyDerives ((Subst.single v (.const c)).applyEqs rest) →
      UnifyDerives ((.const c, .var v) :: rest)
  | app_var (f : σ.functionSymbols) (ts : Fin (σ.functionArity f) → Term σ)
      (v : σ.vars) (rest : List (Term σ × Term σ))
      (hocc : (Term.app f ts).occursIn v = false) :
      UnifyDerives ((Subst.single v (.app f ts)).applyEqs rest) →
      UnifyDerives ((.app f ts, .var v) :: rest)
  | app_eq (f : σ.functionSymbols) (ts us : Fin (σ.functionArity f) → Term σ)
      (rest : List (Term σ × Term σ)) :
      UnifyDerives (finPairsToList ts us ++ rest) →
      UnifyDerives ((.app f ts, .app f us) :: rest)

/-! ## Section 2: Derivation completeness for `unifyFuel` -/

/-- Fuel existence: every fuel-free successful derivation can be executed by
`unifyFuel` using some finite fuel budget. -/
theorem unifyFuel_exists_of_derives {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {eqs : List (Term σ × Term σ)} :
    UnifyDerives eqs → ∃ fuel : ℕ, ∃ θ : Subst σ, unifyFuel fuel eqs = some θ := by
  intro h
  induction h with
  | nil =>
      exact ⟨1, Subst.id σ, by simp [unifyFuel]⟩
  | var_eq v rest hrest ih =>
      rcases ih with ⟨fuel, θ, hθ⟩
      exact ⟨fuel + 1, θ, by simpa [unifyFuel] using hθ⟩
  | var_subst v t rest hocc hrest ih =>
      rcases ih with ⟨fuel, θ', hθ'⟩
      refine ⟨fuel + 1, θ' ∘ₛ Subst.single v t, ?_⟩
      cases t with
      | var w =>
          have hvw : v ≠ w := by
            intro hvw
            subst hvw
            simp [Term.occursIn] at hocc
          simp [unifyFuel, hvw, hθ']
      | const c =>
          simp [unifyFuel, hocc, hθ']
      | app f ts =>
          simp [unifyFuel, hocc, hθ']
  | const_eq c rest hrest ih =>
      rcases ih with ⟨fuel, θ, hθ⟩
      exact ⟨fuel + 1, θ, by simpa [unifyFuel] using hθ⟩
  | const_var c v rest hrest ih =>
      rcases ih with ⟨fuel, θ', hθ'⟩
      refine ⟨fuel + 1, θ' ∘ₛ Subst.single v (.const c), ?_⟩
      simp [unifyFuel, Term.occursIn, hθ']
  | app_var f ts v rest hocc hrest ih =>
      rcases ih with ⟨fuel, θ', hθ'⟩
      refine ⟨fuel + 1, θ' ∘ₛ Subst.single v (.app f ts), ?_⟩
      simp [unifyFuel, hocc, hθ']
  | app_eq f ts us rest hrest ih =>
      rcases ih with ⟨fuel, θ, hθ⟩
      exact ⟨fuel + 1, θ, by simpa [unifyFuel] using hθ⟩

/-- Corollary: fuel-free successful derivations are semantically unifiable. -/
theorem unifiable_of_derives {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {eqs : List (Term σ × Term σ)} :
    UnifyDerives eqs → ∃ θ : Subst σ, Unifies θ eqs := by
  intro h
  rcases unifyFuel_exists_of_derives (eqs := eqs) h with ⟨fuel, θ, hθ⟩
  exact ⟨θ, unifyFuel_sound fuel eqs θ hθ⟩

/-- Semantic-form completeness, parameterized by a bridge from semantic
unifiability to fuel-free successful derivations. -/
theorem unifyFuel_exists_of_unifies_bridge {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (hBridge : (∃ δ : Subst σ, Unifies δ eqs) → UnifyDerives eqs)
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, unifyFuel fuel eqs = some θ :=
  unifyFuel_exists_of_derives (eqs := eqs) (hBridge hunif)

/-! ## Section 3: Internalized bridges from semantic unifiability -/

private theorem unifies_tail_of_cons {σ : LPSignature}
    {δ : Subst σ} {s t : Term σ} {rest : List (Term σ × Term σ)}
    (h : Unifies δ ((s, t) :: rest)) :
    Unifies δ rest := by
  intro p hp
  exact h p (List.mem_cons_of_mem _ hp)

/-- Semantic lifting for elimination:
if `δ` satisfies `δ v = δ t` and unifies `rest`, then `δ` unifies
the rewritten-rest equation list `single v t` applied to `rest`. -/
theorem unifies_applyEqs_of_eliminate {σ : LPSignature}
    [DecidableEq σ.vars]
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

/-- Constructor-level elimination lifting:
if the rewritten-rest equations derive, the original eliminate step derives. -/
theorem derives_eliminate_of_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (v : σ.vars) (t : Term σ)
    (rest : List (Term σ × Term σ)) (hocc : t.occursIn v = false)
    (hDer : UnifyDerives ((Subst.single v t).applyEqs rest)) :
    UnifyDerives ((.var v, t) :: rest) :=
  UnifyDerives.var_subst v t rest hocc hDer

/-- Semantic lifting for decompose:
if `δ` unifies `app f ts = app f us` and unifies `rest`, then `δ` unifies
the decomposed argument equations appended to `rest`. -/
theorem unifies_decompose_append_of_app_eq {σ : LPSignature}
    (f : σ.functionSymbols) (ts us : Fin (σ.functionArity f) → Term σ)
    (rest : List (Term σ × Term σ)) (δ : Subst σ)
    (happ : δ.applyTerm (.app f ts) = δ.applyTerm (.app f us))
    (hrest : Unifies δ rest) :
    Unifies δ (finPairsToList ts us ++ rest) := by
  have hfun :
      (fun i => δ.applyTerm (ts i)) = (fun i => δ.applyTerm (us i)) := by
    simpa [Subst.applyTerm] using happ
  have hargs : ∀ i, δ.applyTerm (ts i) = δ.applyTerm (us i) := by
    intro i
    exact congrArg (fun g => g i) hfun
  intro p hp
  rcases List.mem_append.mp hp with hpairs | htail
  · simp [finPairsToList, List.mem_map] at hpairs
    rcases hpairs with ⟨i, _, rfl⟩
    exact hargs i
  · exact hrest p htail

/-- Constructor-level decompose lifting:
if decomposed equations derive, the original app/app equation derives. -/
theorem derives_decompose_of_lift {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (f : σ.functionSymbols) (ts us : Fin (σ.functionArity f) → Term σ)
    (rest : List (Term σ × Term σ))
    (hDer : UnifyDerives (finPairsToList ts us ++ rest)) :
    UnifyDerives ((.app f ts, .app f us) :: rest) :=
  UnifyDerives.app_eq f ts us rest hDer

private theorem size_le_applyTerm_of_occursIn_true {σ : LPSignature}
    [DecidableEq σ.vars] (δ : Subst σ) (v : σ.vars) :
    ∀ t : Term σ, t.occursIn v = true → (δ v).size ≤ (δ.applyTerm t).size
  | .var w, h => by
      simp [Term.occursIn] at h
      subst h
      simp [Subst.applyTerm]
  | .const c, h => by
      simp [Term.occursIn] at h
  | .app f ts, h => by
      have hAny :
          (List.finRange (σ.functionArity f)).any (fun i => (ts i).occursIn v) = true := by
        simpa [Term.occursIn] using h
      rcases List.any_eq_true.mp hAny with ⟨i, _, hi⟩
      have hsub : (δ v).size ≤ (δ.applyTerm (ts i)).size :=
        size_le_applyTerm_of_occursIn_true δ v (ts i) hi
      have hsubterm : (δ.applyTerm (ts i)).size <
          (δ.applyTerm (.app f ts)).size := by
        simpa [Subst.applyTerm] using
          (Term.size_subterm (f := f) (ts := fun j => δ.applyTerm (ts j)) i)
      exact le_trans hsub (Nat.le_of_lt hsubterm)

private theorem size_lt_applyTerm_app_of_occursIn_true {σ : LPSignature}
    [DecidableEq σ.vars] (δ : Subst σ) (v : σ.vars)
    (f : σ.functionSymbols) (ts : Fin (σ.functionArity f) → Term σ)
    (hocc : (Term.app f ts).occursIn v = true) :
    (δ v).size < (δ.applyTerm (.app f ts)).size := by
  have hAny :
      (List.finRange (σ.functionArity f)).any (fun i => (ts i).occursIn v) = true := by
    simpa [Term.occursIn] using hocc
  rcases List.any_eq_true.mp hAny with ⟨i, _, hi⟩
  have hsub : (δ v).size ≤ (δ.applyTerm (ts i)).size :=
    size_le_applyTerm_of_occursIn_true δ v (ts i) hi
  have hsubterm : (δ.applyTerm (ts i)).size <
      (δ.applyTerm (.app f ts)).size := by
    simpa [Subst.applyTerm] using
      (Term.size_subterm (f := f) (ts := fun j => δ.applyTerm (ts j)) i)
  exact lt_of_le_of_lt hsub hsubterm

private theorem occursIn_false_of_unifies_var_app {σ : LPSignature}
    [DecidableEq σ.vars] (δ : Subst σ) (v : σ.vars)
    (f : σ.functionSymbols) (ts : Fin (σ.functionArity f) → Term σ)
    (hpair : δ.applyTerm (.var v) = δ.applyTerm (.app f ts)) :
    (Term.app f ts).occursIn v = false := by
  by_cases hocc : (Term.app f ts).occursIn v = true
  · have hlt : (δ v).size < (δ.applyTerm (.app f ts)).size :=
      size_lt_applyTerm_app_of_occursIn_true δ v f ts hocc
    have hsize : (δ v).size = (δ.applyTerm (.app f ts)).size := by
      simpa [Subst.applyTerm] using congrArg Term.size hpair
    exact (Nat.ne_of_lt hlt) hsize |> False.elim
  · cases hval : (Term.app f ts).occursIn v with
    | false =>
        simp
    | true =>
        exact (hocc hval).elim

private def MMRel {σ : LPSignature} [DecidableEq σ.vars] :
    List (Term σ × Term σ) → List (Term σ × Term σ) → Prop :=
  InvImage (Prod.Lex (· < ·) (· < ·)) (fun eqs => mmMeasure eqs)

private theorem mmRel_wf {σ : LPSignature} [DecidableEq σ.vars] :
    WellFounded (MMRel (σ := σ)) := by
  exact InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

private theorem mmRel_of_var_lt {σ : LPSignature} [DecidableEq σ.vars]
    {eqs' eqs : List (Term σ × Term σ)}
    (h : mmVarCount eqs' < mmVarCount eqs) :
    MMRel eqs' eqs := by
  dsimp [MMRel, InvImage]
  exact (Prod.lex_iff).2 (Or.inl h)

private theorem mmRel_of_var_le_size_lt {σ : LPSignature} [DecidableEq σ.vars]
    {eqs' eqs : List (Term σ × Term σ)}
    (hVarLe : mmVarCount eqs' ≤ mmVarCount eqs)
    (hSizeLt : mmSize eqs' < mmSize eqs) :
    MMRel eqs' eqs := by
  dsimp [MMRel, InvImage]
  by_cases hVarLt : mmVarCount eqs' < mmVarCount eqs
  · exact (Prod.lex_iff).2 (Or.inl hVarLt)
  · have hVarEq : mmVarCount eqs' = mmVarCount eqs :=
      (Nat.lt_or_eq_of_le hVarLe).resolve_left hVarLt
    exact (Prod.lex_iff).2 (Or.inr ⟨hVarEq, hSizeLt⟩)

/-- Assumption-free semantic-to-derivation bridge for full first-order
equation systems. -/
theorem unifies_to_derives {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    UnifyDerives eqs := by
  have hAll :
      ∀ eqs : List (Term σ × Term σ),
        (∃ δ : Subst σ, Unifies δ eqs) → UnifyDerives eqs := by
    intro eqs
    refine (mmRel_wf (σ := σ)).induction
      (C := fun eqs => (∃ δ : Subst σ, Unifies δ eqs) → UnifyDerives eqs) eqs ?_
    intro eqs ih hunif'
    cases eqs with
  | nil =>
      exact UnifyDerives.nil
  | cons p rest =>
      rcases p with ⟨s, t⟩
      rcases hunif' with ⟨δ, hδ⟩
      have hpair : δ.applyTerm s = δ.applyTerm t :=
        hδ (s, t) (List.mem_cons_self ..)
      have hrest : Unifies δ rest :=
        unifies_tail_of_cons hδ
      cases s with
      | var v =>
          cases t with
          | var w =>
              by_cases hEq : v = w
              · subst hEq
                have hRel : MMRel rest ((.var v, .var v) :: rest) :=
                  mmRel_of_var_le_size_lt
                    (mmVarCount_cons_ge (.var v) (.var v) rest)
                    (mmSize_var_eq_lt v rest)
                exact UnifyDerives.var_eq v rest (ih rest hRel ⟨δ, hrest⟩)
              · have hocc : (Term.var w).occursIn v = false := by
                  simp [Term.occursIn, hEq]
                let eqs' : List (Term σ × Term σ) :=
                  (Subst.single v (.var w)).applyEqs rest
                have hv : δ v = δ.applyTerm (.var w) := by
                  simpa [Subst.applyTerm] using hpair
                have hSub : Unifies δ eqs' := by
                  simpa [eqs'] using
                    unifies_applyEqs_of_eliminate v (.var w) rest δ hv hrest
                have hRel : MMRel eqs' ((.var v, .var w) :: rest) :=
                  mmRel_of_var_lt (mmVarCount_eliminate_lt v (.var w) rest hocc)
                exact derives_eliminate_of_lift v (.var w) rest hocc (ih eqs' hRel ⟨δ, hSub⟩)
          | const c =>
              have hocc : (Term.const c).occursIn v = false := by
                simp [Term.occursIn]
              let eqs' : List (Term σ × Term σ) :=
                (Subst.single v (.const c)).applyEqs rest
              have hv : δ v = δ.applyTerm (.const c) := by
                simpa [Subst.applyTerm] using hpair
              have hSub : Unifies δ eqs' := by
                simpa [eqs'] using
                  unifies_applyEqs_of_eliminate v (.const c) rest δ hv hrest
              have hRel : MMRel eqs' ((.var v, .const c) :: rest) :=
                mmRel_of_var_lt (mmVarCount_eliminate_lt v (.const c) rest hocc)
              exact derives_eliminate_of_lift v (.const c) rest hocc (ih eqs' hRel ⟨δ, hSub⟩)
          | app f ts =>
              have hocc : (Term.app f ts).occursIn v = false :=
                occursIn_false_of_unifies_var_app δ v f ts hpair
              let eqs' : List (Term σ × Term σ) :=
                (Subst.single v (.app f ts)).applyEqs rest
              have hv : δ v = δ.applyTerm (.app f ts) := by
                simpa [Subst.applyTerm] using hpair
              have hSub : Unifies δ eqs' := by
                simpa [eqs'] using
                  unifies_applyEqs_of_eliminate v (.app f ts) rest δ hv hrest
              have hRel : MMRel eqs' ((.var v, .app f ts) :: rest) :=
                mmRel_of_var_lt (mmVarCount_eliminate_lt v (.app f ts) rest hocc)
              exact derives_eliminate_of_lift v (.app f ts) rest hocc (ih eqs' hRel ⟨δ, hSub⟩)
      | const c =>
          cases t with
          | var v =>
              let eqs' : List (Term σ × Term σ) :=
                (Subst.single v (.const c)).applyEqs rest
              have hv : δ v = δ.applyTerm (.const c) := by
                simpa [Subst.applyTerm] using hpair.symm
              have hSub : Unifies δ eqs' := by
                simpa [eqs'] using
                  unifies_applyEqs_of_eliminate v (.const c) rest δ hv hrest
              have hRel : MMRel eqs' ((.const c, .var v) :: rest) := by
                have hocc : (Term.const c).occursIn v = false := by simp [Term.occursIn]
                exact mmRel_of_var_lt (mmVarCount_eliminate_lt v (.const c) rest hocc)
              exact UnifyDerives.const_var c v rest (ih eqs' hRel ⟨δ, hSub⟩)
          | const c' =>
              by_cases hcc : c = c'
              · subst hcc
                have hRel : MMRel rest ((.const c, .const c) :: rest) :=
                  mmRel_of_var_le_size_lt
                    (mmVarCount_cons_ge (.const c) (.const c) rest)
                    (mmSize_const_eq_lt c rest)
                exact UnifyDerives.const_eq c rest (ih rest hRel ⟨δ, hrest⟩)
              · exfalso
                have : c = c' := by
                  simpa [Subst.applyTerm] using hpair
                exact hcc this
          | app g us =>
              exfalso
              simp [Subst.applyTerm] at hpair
      | app f ts =>
          cases t with
          | var v =>
              have hocc : (Term.app f ts).occursIn v = false :=
                occursIn_false_of_unifies_var_app δ v f ts hpair.symm
              let eqs' : List (Term σ × Term σ) :=
                (Subst.single v (.app f ts)).applyEqs rest
              have hv : δ v = δ.applyTerm (.app f ts) := by
                simpa [Subst.applyTerm] using hpair.symm
              have hSub : Unifies δ eqs' := by
                simpa [eqs'] using
                  unifies_applyEqs_of_eliminate v (.app f ts) rest δ hv hrest
              have hVarLt :
                  mmVarCount eqs' < mmVarCount ((.app f ts, .var v) :: rest) := by
                simpa [eqs', mmVarCount, eqVars, Finset.union_assoc, Finset.union_comm,
                  Finset.union_left_comm] using
                  (mmVarCount_eliminate_lt v (.app f ts) rest hocc)
              have hRel : MMRel eqs' ((.app f ts, .var v) :: rest) :=
                mmRel_of_var_lt hVarLt
              exact UnifyDerives.app_var f ts v rest hocc (ih eqs' hRel ⟨δ, hSub⟩)
          | const c =>
              exfalso
              simp [Subst.applyTerm] at hpair
          | app g us =>
              by_cases hfg : f = g
              · subst hfg
                let eqs' : List (Term σ × Term σ) := finPairsToList ts us ++ rest
                have hSub : Unifies δ eqs' := by
                  simpa [eqs'] using
                    unifies_decompose_append_of_app_eq f ts us rest δ hpair hrest
                have hRel : MMRel eqs' ((.app f ts, .app f us) :: rest) :=
                  mmRel_of_var_le_size_lt
                    (mmVarCount_app_eq_decompose_le f ts us rest)
                    (mmSize_app_eq_decompose_lt f ts us rest)
                exact derives_decompose_of_lift f ts us rest (ih eqs' hRel ⟨δ, hSub⟩)
              · exfalso
                simp [Subst.applyTerm, hfg] at hpair
  exact hAll eqs hunif

/-- Assumption-free semantic completeness theorem (full first-order):
if an equation system is unifiable, `unifyFuel` succeeds for some finite fuel. -/
theorem unifyFuel_exists_of_unifies {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, unifyFuel fuel eqs = some θ := by
  exact unifyFuel_exists_of_derives (eqs := eqs) (unifies_to_derives (eqs := eqs) hunif)

/-- Internalized semantic-to-derivation bridge for the function-free fragment.

No external bridge hypothesis is needed: in the absence of function symbols,
every semantically unifiable equation list admits a finite `UnifyDerives` proof.
-/
theorem unifies_to_derives_functionFree {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [IsEmpty σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    UnifyDerives eqs := by
  exact unifies_to_derives (eqs := eqs) hunif

/-- Assumption-free semantic completeness theorem for the function-free
fragment: semantically unifiable equations succeed for some finite fuel. -/
theorem unifyFuel_exists_of_unifies_functionFree {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [IsEmpty σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, unifyFuel fuel eqs = some θ := by
  exact unifyFuel_exists_of_unifies (eqs := eqs) hunif

/-! ## Section 4: Ground-equation corollaries -/

/-- Ground equations predicate. -/
def GroundEqs {σ : LPSignature} (eqs : List (Term σ × Term σ)) : Prop :=
  ∀ p ∈ eqs, p.1.isGround ∧ p.2.isGround

private theorem subst_applyTerm_eq_self_of_isGround {σ : LPSignature}
    (θ : Subst σ) {t : Term σ} (ht : t.isGround) :
    θ.applyTerm t = t := by
  induction t with
  | var v =>
      cases ht
  | const c =>
      simp [Subst.applyTerm]
  | app f ts ih =>
      simp [Subst.applyTerm]
      funext i
      exact ih i (ht i)

/-- Ground semantic bridge (no function-free restriction):
if all equations are ground and semantically unifiable, they admit a finite
`UnifyDerives` proof. -/
theorem unifies_to_derives_ground {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (_hGround : GroundEqs eqs)
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    UnifyDerives eqs := by
  exact unifies_to_derives (eqs := eqs) hunif

/-- Assumption-free semantic completeness for ground equations:
if a ground equation system is unifiable, `unifyFuel` succeeds for some fuel. -/
theorem unifyFuel_exists_of_unifies_ground {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (_hGround : GroundEqs eqs)
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, unifyFuel fuel eqs = some θ := by
  exact unifyFuel_exists_of_unifies (eqs := eqs) hunif

private theorem term_eq_const_of_isGround_functionFree {σ : LPSignature}
    [IsEmpty σ.functionSymbols] {t : Term σ} (ht : t.isGround) :
    ∃ c : σ.constants, t = .const c := by
  cases t with
  | var v =>
      simp [Term.isGround] at ht
  | const c =>
      exact ⟨c, rfl⟩
  | app f ts =>
      exfalso
      exact (IsEmpty.false f)

/-- Internalized semantic-to-derivation bridge for function-free ground equations. -/
theorem unifies_to_derives_functionFree_ground {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [IsEmpty σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (_hGround : GroundEqs eqs)
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    UnifyDerives eqs := by
  exact unifies_to_derives (eqs := eqs) hunif

/-- Assumption-free semantic completeness theorem for function-free ground equations:
if an equation system is unifiable, `unifyFuel` succeeds for some fuel. -/
theorem unifyFuel_exists_of_unifies_functionFree_ground {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [IsEmpty σ.functionSymbols]
    {eqs : List (Term σ × Term σ)}
    (hGround : GroundEqs eqs)
    (hunif : ∃ δ : Subst σ, Unifies δ eqs) :
    ∃ fuel : ℕ, ∃ θ : Subst σ, unifyFuel fuel eqs = some θ := by
  exact unifyFuel_exists_of_unifies_ground (eqs := eqs) hGround hunif

end Mettapedia.Logic.LP
