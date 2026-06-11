import Mettapedia.Logic.HOL.CanonicalQuantifierBridges
import Mathlib.Tactic.Set
import Mathlib.Data.Set.Insert

/-!
# Henkin witnessing: conservativity of a single witness axiom

The canonical term model needs the *existence property*: every provable
existential has a closed-term witness in the world.  The standard Henkin route
adds, for each existential body `φ`, a fresh parameter constant `c` together with
the **witness axiom**

  `(∃x. φ) → φ[c]`.

The mathematical heart — proven here — is that adding one such axiom over a fresh
parameter **preserves consistency** (`consistent_addWitness`).  The argument is
fully intuitionistic and rests on the fresh-constant generalization
`provable_all_intro_fresh` (and its derivation-level core `allI_fresh`) built in
`CanonicalQuantifierBridges`.

This file provides:

* `instantiate_vz_rename_lift_weaken` — the pure renaming identity behind
  `∀`-elimination under a binder (the same identity that powers `allI_fresh`);
* three intuitionistic natural-deduction helpers (`notB_of_not_imp`,
  `notnotA_of_not_imp`, `notEx_of_allNot`);
* the consistency theorem `consistent_addWitness`.
-/

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## The renaming identity behind `∀`-elimination under a binder -/

/-- Instantiating the freshly-bound variable of a once-weakened body is the
identity: `(rename (lift weaken) φ)[vz] = φ`.  This is the reverse of `weaken`
under one binder. -/
theorem instantiate_vz_rename_lift_weaken
    {Γ : Ctx Base} {σ τ : Ty Base} (φ : Term Const (σ :: Γ) τ) :
    instantiate (Base := Base) (.var .vz)
        (rename (Rename.lift (Base := Base) (σ := σ)
          (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ) = φ := by
  unfold instantiate
  rw [subst_rename]
  refine Eq.trans (subst_ext ?_ φ) (subst_id φ)
  intro τ' v
  cases v with
  | vz => rfl
  | vs w => rfl

/-! ## Intuitionistic natural-deduction helpers -/

/-- `¬(A → B) ⊢ ¬B`. -/
theorem notB_of_not_imp
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {A B : Formula Const Γ}
    (h : ExtDerivation Const Δ (.not (.imp A B))) :
    ExtDerivation Const Δ (.not B) := by
  apply ExtDerivation.notI
  refine ExtDerivation.notE (φ := .imp A B) ?_ ?_
  · exact ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) h
  · apply ExtDerivation.impI
    exact ExtDerivation.hyp (by simp)

/-- `¬(A → B) ⊢ ¬¬A`. -/
theorem notnotA_of_not_imp
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {A B : Formula Const Γ}
    (h : ExtDerivation Const Δ (.not (.imp A B))) :
    ExtDerivation Const Δ (.not (.not A)) := by
  apply ExtDerivation.notI
  refine ExtDerivation.notE (φ := .imp A B) ?_ ?_
  · exact ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) h
  · apply ExtDerivation.impI
    apply ExtDerivation.botE
    refine ExtDerivation.notE (φ := A) ?_ ?_
    · exact ExtDerivation.hyp (by simp)
    · exact ExtDerivation.hyp (by simp)

/-- `∀x. ¬φ ⊢ ¬∃x. φ`. -/
theorem notEx_of_allNot
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
    {φ : Formula Const (σ :: Γ)}
    (h : ExtDerivation Const Δ (.all (.not φ))) :
    ExtDerivation Const Δ (.not (.ex φ)) := by
  apply ExtDerivation.notI
  refine ExtDerivation.exE (φ := φ) (ψ := .bot) ?_ ?_
  · exact ExtDerivation.hyp (by simp)
  · -- body context: `φ :: weakenHyps (.ex φ :: Δ)`, goal `weaken .bot = .bot`
    have hbase : ExtDerivation Const (weakenHyps (σ := σ) Δ)
        (.all (.not (rename (Rename.lift (Base := Base) (σ := σ)
          (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ))) :=
      ExtDerivation.rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) h
    have hW : ExtDerivation Const (φ :: weakenHyps (σ := σ) (.ex φ :: Δ))
        (.all (.not (rename (Rename.lift (Base := Base) (σ := σ)
          (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ))) := by
      refine ExtDerivation.mono ?_ hbase
      intro ξ hξ
      simp only [weakenHyps, List.map] at hξ ⊢
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hξ)
    have hNotφ : ExtDerivation Const (φ :: weakenHyps (σ := σ) (.ex φ :: Δ))
        (.not φ) := by
      have h1 : ExtDerivation Const (φ :: weakenHyps (σ := σ) (.ex φ :: Δ))
          (.not (instantiate (Base := Base) (.var .vz)
            (rename (Rename.lift (Base := Base) (σ := σ)
              (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ))) :=
        ExtDerivation.allE (Base := Base) (.var .vz) hW
      rwa [instantiate_vz_rename_lift_weaken] at h1
    exact ExtDerivation.notE hNotφ (ExtDerivation.hyp (by simp))

/-- `¬∃x. φ ⊢ ∀x. ¬φ` (the converse direction of `notEx_of_allNot`). -/
theorem allNot_of_notEx
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
    {φ : Formula Const (σ :: Γ)}
    (h : ExtDerivation Const Δ (.not (.ex φ))) :
    ExtDerivation Const Δ (.all (.not φ)) := by
  apply ExtDerivation.allI
  apply ExtDerivation.notI
  -- context: `φ :: weakenHyps Δ`, goal `.bot`
  have hbase : ExtDerivation Const (weakenHyps (σ := σ) Δ)
      (.not (.ex (rename (Rename.lift (Base := Base) (σ := σ)
        (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ))) :=
    ExtDerivation.rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) h
  have hW : ExtDerivation Const (φ :: weakenHyps (σ := σ) Δ)
      (.not (.ex (rename (Rename.lift (Base := Base) (σ := σ)
        (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ))) :=
    ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) hbase
  have hex : ExtDerivation Const (φ :: weakenHyps (σ := σ) Δ)
      (.ex (rename (Rename.lift (Base := Base) (σ := σ)
        (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ)) := by
    have h1 : ExtDerivation Const (φ :: weakenHyps (σ := σ) Δ)
        (instantiate (Base := Base) (.var .vz)
          (rename (Rename.lift (Base := Base) (σ := σ)
            (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))) φ)) := by
      rw [instantiate_vz_rename_lift_weaken]
      exact ExtDerivation.hyp List.mem_cons_self
    exact ExtDerivation.exI (Base := Base) (.var .vz) h1
  exact ExtDerivation.notE hW hex

/-- `(X → ⊥) ⊢ ¬X`: the implication-to-falsity form of negation. -/
theorem not_of_imp_bot
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {X : Formula Const Γ}
    (h : ExtDerivation Const Δ (.imp X .bot)) :
    ExtDerivation Const Δ (.not X) := by
  apply ExtDerivation.notI
  exact ExtDerivation.impE
    (ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) h)
    (ExtDerivation.hyp (by simp))

/-! ## Deduction theorem (`insert` form) -/

open scoped Classical in
/-- **Deduction theorem.**  If `ψ` is provable from `T` together with an extra
hypothesis `χ`, then `χ → ψ` is provable from `T` alone. -/
theorem provable_imp_of_insert {T : ClosedTheorySet Const} {χ ψ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) (insert χ T) ψ) :
    ClosedTheorySet.Provable (Const := Const) T (Term.imp χ ψ) := by
  classical
  rcases h with ⟨Γ, hΓ, d⟩
  set ΓT : ClosedTheory Const := Γ.filter (fun ξ => decide (ξ ≠ χ)) with hΓT
  have hΓT_subT : ∀ ξ, ξ ∈ ΓT → ξ ∈ T := by
    intro ξ hξ
    rw [hΓT, List.mem_filter] at hξ
    obtain ⟨hξΓ, hξne⟩ := hξ
    have hne : ξ ≠ χ := by simpa using hξne
    rcases Set.mem_insert_iff.mp (hΓ ξ hξΓ) with he | hmem
    · exact absurd he hne
    · exact hmem
  have d' : ExtDerivation Const (χ :: ΓT) ψ := by
    refine ExtDerivation.mono ?_ d
    intro ξ hξ
    by_cases he : ξ = χ
    · subst he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hξ, by simp [he]⟩)
  exact ⟨ΓT, fun ξ hξ => hΓT_subT ξ hξ, ExtDerivation.impI d'⟩

/-- The Henkin witness axiom for body `φ` at witness constant `c`:
`(∃x. φ) → φ[c]`. -/
@[reducible] def witnessAxiom {σ : Ty Base} (c : Const σ) (φ : Formula Const [σ]) :
    ClosedFormula Const :=
  Term.imp (.ex φ) (instantiate (Base := Base) (.const c) φ)

/-! ## Consistency of adding one Henkin witness axiom -/

open scoped Classical in
/-- **Henkin witness conservativity (single step).**  For a parameter constant
`c : Const σ` that is fresh for the theory `T` and the body `φ`, adjoining the
witness axiom `(∃x. φ) → φ[c]` to `T` preserves consistency.  The argument is
intuitionistic: a derivation of `⊥` from the witness axiom yields `⊢ ¬φ[c]`,
hence (by freshness) `⊢ ∀x. ¬φ`, hence `⊢ ¬∃x. φ`, contradicting the `¬¬∃x. φ`
that the same refutation provides. -/
theorem consistent_addWitness {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (c : Const σ)
    (hCons : ClosedTheorySet.Consistent (Const := Const) T)
    (hT : ∀ ψ ∈ T, NoConstOccurrence c ψ)
    (hφ : NoConstOccurrence c φ) :
    ClosedTheorySet.Consistent (Const := Const)
      (insert (witnessAxiom c φ) T) := by
  classical
  set hax : ClosedFormula Const := witnessAxiom c φ with hhax
  intro hbot
  rcases hbot with ⟨Γ, hΓ, d⟩
  -- The finite subtheory of genuine `T`-hypotheses (the witness axiom removed).
  set ΓT : ClosedTheory Const := Γ.filter (fun ψ => decide (ψ ≠ hax)) with hΓT
  have hΓT_subT : ∀ ψ, ψ ∈ ΓT → ψ ∈ T := by
    intro ψ hψ
    rw [hΓT, List.mem_filter] at hψ
    obtain ⟨hψΓ, hψne⟩ := hψ
    have hne : ψ ≠ hax := by simpa using hψne
    rcases Set.mem_insert_iff.mp (hΓ ψ hψΓ) with he | hmem
    · exact absurd he hne
    · exact hmem
  -- The original `⊥`-derivation, re-based onto `hax :: ΓT`.
  have d' : ExtDerivation Const (hax :: ΓT) .bot := by
    refine ExtDerivation.mono ?_ d
    intro ψ hψ
    by_cases he : ψ = hax
    · subst he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hψ, by simp [he]⟩)
  -- Discharge the witness axiom into a negation, then run the Henkin argument.
  have dnothax : ExtDerivation Const ΓT (.not hax) :=
    not_of_imp_bot (ExtDerivation.impI d')
  have hΓTfresh : ∀ ψ ∈ ΓT, NoConstOccurrence c ψ :=
    fun ψ hψ => hT ψ (hΓT_subT ψ hψ)
  have dnotB : ExtDerivation Const ΓT (.not (instantiate (Base := Base) (.const c) φ)) :=
    notB_of_not_imp dnothax
  have dall : ExtDerivation Const ΓT (.all (.not φ)) :=
    ExtDerivation.allI_fresh c hΓTfresh (NoConstOccurrence.not hφ) dnotB
  have dnotEx : ExtDerivation Const ΓT (.not (.ex φ)) := notEx_of_allNot dall
  have dnotnotEx : ExtDerivation Const ΓT (.not (.not (.ex φ))) :=
    notnotA_of_not_imp dnothax
  have dbot : ExtDerivation Const ΓT .bot := ExtDerivation.notE dnotnotEx dnotEx
  exact hCons (ClosedTheorySet.provable_of_closedTheory
    (fun {ψ} hψ => hΓT_subT ψ hψ) dbot)

end Mettapedia.Logic.HOL
