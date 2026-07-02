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

/-- Converse direction of the theory-level deduction theorem. -/
theorem provable_insert_of_imp {T : ClosedTheorySet Const} {χ ψ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T (Term.imp χ ψ)) :
    ClosedTheorySet.Provable (Const := Const) (insert χ T) ψ := by
  exact ClosedTheorySet.provable_mp
    (ClosedTheorySet.provable_mono (Const := Const)
      (T := T) (U := insert χ T)
      (by intro ξ hξ; exact Set.mem_insert_of_mem χ hξ)
      h)
    (ClosedTheorySet.provable_of_mem (Const := Const) (Set.mem_insert χ T))

/-- Theory-level deduction theorem for a single inserted hypothesis. -/
theorem provable_insert_iff_imp {T : ClosedTheorySet Const} {χ ψ : ClosedFormula Const} :
    ClosedTheorySet.Provable (Const := Const) (insert χ T) ψ ↔
      ClosedTheorySet.Provable (Const := Const) T (Term.imp χ ψ) :=
  ⟨provable_imp_of_insert, provable_insert_of_imp⟩

/-- Disjunction elimination packaged for closed theory sets. -/
theorem provable_or_elim {T : ClosedTheorySet Const}
    {φ ψ θ : ClosedFormula Const}
    (hOr : ClosedTheorySet.Provable (Const := Const) T (.or φ ψ))
    (hφ : ClosedTheorySet.Provable (Const := Const) (insert φ T) θ)
    (hψ : ClosedTheorySet.Provable (Const := Const) (insert ψ T) θ) :
    ClosedTheorySet.Provable (Const := Const) T θ := by
  rcases hOr with ⟨ΓOr, hΓOr, dOr⟩
  have hφImp : ClosedTheorySet.Provable (Const := Const) T (.imp φ θ) :=
    provable_imp_of_insert (Const := Const) hφ
  have hψImp : ClosedTheorySet.Provable (Const := Const) T (.imp ψ θ) :=
    provable_imp_of_insert (Const := Const) hψ
  rcases hφImp with ⟨Γφ, hΓφ, dφ⟩
  rcases hψImp with ⟨Γψ, hΓψ, dψ⟩
  refine ⟨ΓOr ++ Γφ ++ Γψ, ?_, ?_⟩
  · intro ξ hξ
    simp only [List.mem_append] at hξ
    rcases hξ with (hξOr | hξφ) | hξψ
    · exact hΓOr ξ hξOr
    · exact hΓφ ξ hξφ
    · exact hΓψ ξ hξψ
  · refine ExtDerivation.orE (φ := φ) (ψ := ψ) (χ := θ) ?_ ?_ ?_
    · exact ExtDerivation.mono
        (by intro ξ hξ; simp [hξ]) dOr
    · exact ExtDerivation.impE
        (ExtDerivation.mono
          (by
            intro ξ hξ
            exact List.mem_cons_of_mem _ (by simp [hξ]))
          dφ)
        (ExtDerivation.hyp List.mem_cons_self)
    · exact ExtDerivation.impE
        (ExtDerivation.mono
          (by
            intro ξ hξ
            exact List.mem_cons_of_mem _ (by simp [hξ]))
          dψ)
        (ExtDerivation.hyp List.mem_cons_self)

/-- If `T ⊬ θ` but `T ⊢ φ ∨ ψ`, then at least one disjunct can be added while
still omitting `θ`. -/
theorem exists_or_branch_omitting
    {T : ClosedTheorySet Const} {φ ψ θ : ClosedFormula Const}
    (hNot : ¬ ClosedTheorySet.Provable (Const := Const) T θ)
    (hOr : ClosedTheorySet.Provable (Const := Const) T (.or φ ψ)) :
    (¬ ClosedTheorySet.Provable (Const := Const) (insert φ T) θ) ∨
      (¬ ClosedTheorySet.Provable (Const := Const) (insert ψ T) θ) := by
  classical
  by_cases hφ : ClosedTheorySet.Provable (Const := Const) (insert φ T) θ
  · right
    intro hψ
    exact hNot (provable_or_elim (Const := Const) hOr hφ hψ)
  · exact Or.inl hφ

/-- Existential elimination packaged for a closed theory: from `∃x. φ` and
`∀x. (φ → θ)`, derive the closed conclusion `θ`. -/
theorem provable_of_ex_and_all_imp {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {θ : ClosedFormula Const}
    (hEx : ClosedTheorySet.Provable (Const := Const) T (.ex φ))
    (hAll : ClosedTheorySet.Provable (Const := Const) T (.all (.imp φ (weaken θ)))) :
    ClosedTheorySet.Provable (Const := Const) T θ := by
  rcases hEx with ⟨ΓEx, hΓEx, dEx⟩
  rcases hAll with ⟨ΓAll, hΓAll, dAll⟩
  refine ⟨ΓEx ++ ΓAll, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with hξEx | hξAll
    · exact hΓEx ξ hξEx
    · exact hΓAll ξ hξAll
  · refine ExtDerivation.exE (φ := φ) (ψ := θ) ?_ ?_
    · exact ExtDerivation.mono
        (by intro ξ hξ; exact List.mem_append_left ΓAll hξ) dEx
    · have hAllBody : ExtDerivation Const
          (φ :: weakenHyps (Base := Base) (σ := σ) (ΓEx ++ ΓAll))
          (.all (rename (Rename.lift (Base := Base) (σ := σ)
            (Rename.weaken (Base := Base) (Γ := []) (σ := σ)))
              (.imp φ (weaken (Base := Base) (σ := σ) θ)))) := by
        have hRenamed : ExtDerivation Const
            (weakenHyps (Base := Base) (σ := σ) ΓAll)
            (.all (rename (Rename.lift (Base := Base) (σ := σ)
              (Rename.weaken (Base := Base) (Γ := []) (σ := σ)))
                (.imp φ (weaken (Base := Base) (σ := σ) θ)))) := by
          have hRaw :=
            (ExtDerivation.rename
              (Rename.weaken (Base := Base) (Γ := []) (σ := σ)) dAll)
          have hCtx :
              ΓAll.map (rename (Rename.weaken (Base := Base) (Γ := []) (σ := σ))) =
                weakenHyps (Base := Base) (σ := σ) ΓAll := by
            simp [weakenHyps, weaken]
          simpa [hCtx, weaken, rename] using hRaw
        refine ExtDerivation.mono ?_ hRenamed
        intro ξ hξ
        simp only [weakenHyps, List.map_append] at hξ ⊢
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hξ)
      have hImp : ExtDerivation Const
          (φ :: weakenHyps (Base := Base) (σ := σ) (ΓEx ++ ΓAll))
          (.imp φ (weaken (Base := Base) (σ := σ) θ)) := by
        have hInst := ExtDerivation.allE (Base := Base) (.var .vz) hAllBody
        simpa [instantiate_vz_rename_lift_weaken] using hInst
      exact ExtDerivation.impE hImp (ExtDerivation.hyp List.mem_cons_self)

/-- The Henkin witness axiom for body `φ` at witness constant `c`:
`(∃x. φ) → φ[c]`. -/
@[reducible] def witnessAxiom {σ : Ty Base} (c : Const σ) (φ : Formula Const [σ]) :
    ClosedFormula Const :=
  Term.imp (.ex φ) (instantiate (Base := Base) (.const c) φ)

/-- If `∃x. φ` is already derivable on the left, adding a fresh instance `φ[c]`
preserves omission of a fresh closed formula `θ`.  This is the one-step
intuitionistic Henkin-pair move used for separating extensions. -/
theorem not_provable_insert_fresh_instance_of_ex_provable
    {T : ClosedTheorySet Const} {σ : Ty Base} {φ : Formula Const [σ]}
    {θ : ClosedFormula Const} (c : Const σ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := Const) T θ)
    (hEx : ClosedTheorySet.Provable (Const := Const) T (.ex φ))
    (hT : ∀ ψ ∈ T, NoConstOccurrence c ψ)
    (hφ : NoConstOccurrence c φ)
    (hθ : NoConstOccurrence c θ) :
    ¬ ClosedTheorySet.Provable (Const := Const)
      (insert (instantiate (Base := Base) (.const c) φ) T) θ := by
  intro hInst
  have hImp : ClosedTheorySet.Provable (Const := Const) T
      (.imp (instantiate (Base := Base) (.const c) φ) θ) :=
    provable_imp_of_insert (Const := Const) hInst
  have hBodyFresh : NoConstOccurrence c (.imp φ (weaken (Base := Base) (σ := σ) θ)) :=
    NoConstOccurrence.imp hφ
      (noConstOccurrence_rename Rename.weaken _ hθ)
  have hAll : ClosedTheorySet.Provable (Const := Const) T (.all (.imp φ (weaken θ))) := by
    refine ClosedTheorySet.provable_all_intro_fresh
      (Const := Const) (T := T) (c := c) hT hBodyFresh ?_
    convert hImp using 1
    change Term.imp (instantiate (Base := Base) (.const c) φ)
      (instantiate (Base := Base) (.const c) (weaken (Base := Base) (σ := σ) θ)) =
        (instantiate (Base := Base) (.const c) φ).imp θ
    rw [instantiate_weaken]
  exact hNot
    (provable_of_ex_and_all_imp
      (Const := Const)
      hEx
      hAll)

/-- Membership form of `not_provable_insert_fresh_instance_of_ex_provable`. -/
theorem not_provable_insert_fresh_instance_of_ex_mem
    {T : ClosedTheorySet Const} {σ : Ty Base} {φ : Formula Const [σ]}
    {θ : ClosedFormula Const} (c : Const σ)
    (hNot : ¬ ClosedTheorySet.Provable (Const := Const) T θ)
    (hEx : (.ex φ : ClosedFormula Const) ∈ T)
    (hT : ∀ ψ ∈ T, NoConstOccurrence c ψ)
    (hφ : NoConstOccurrence c φ)
    (hθ : NoConstOccurrence c θ) :
    ¬ ClosedTheorySet.Provable (Const := Const)
      (insert (instantiate (Base := Base) (.const c) φ) T) θ := by
  exact not_provable_insert_fresh_instance_of_ex_provable
    (Const := Const) c hNot
    (ClosedTheorySet.provable_of_mem (Const := Const) hEx)
    hT hφ hθ

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
