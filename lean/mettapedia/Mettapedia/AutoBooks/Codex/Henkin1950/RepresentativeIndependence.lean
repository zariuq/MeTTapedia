import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalTruth
import Mettapedia.AutoBooks.Codex.Henkin1950.DerivedResults

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Representative-independence helpers for Henkin pp. 86-88.

The canonical truth relation currently closes open syntax by choosing concrete
closed representatives for quotient classes. To show that this is well-defined,
we need a bridge from provable equality of closed terms and formulas to
closed-theory membership. This file packages the first reusable lemmas in that
direction, together with representative-assignment versions of the closed-term
quantifier clauses.
-/

/-- Extensional provable equality of closed propositions yields closed-theory
provable equivalence. -/
theorem provablyEquivalent_of_termEquivalent_prop
    {T : ClosedTheorySet} {φ ψ : Sentence}
    (hEq : TermEquivalent T φ ψ) :
    Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
      (Const := Primitive) T φ ψ := by
  rcases hEq with ⟨Γ, hΓ, hEq⟩
  constructor
  · exact ⟨Γ, hΓ, ExtDerivation.eqPropEL hEq⟩
  · exact ⟨Γ, hΓ, ExtDerivation.eqPropER hEq⟩

/-- Closed-theory provable equivalence of propositions yields extensional
provable proposition equality. -/
theorem termEquivalent_of_provablyEquivalent_prop
    {T : ClosedTheorySet} {φ ψ : Sentence}
    (hEqv : Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
      (Const := Primitive) T φ ψ) :
    TermEquivalent T φ ψ := by
  rcases hEqv with ⟨hφψ, hψφ⟩
  rcases hφψ with ⟨Γ₁, hΓ₁, hφψ⟩
  rcases hψφ with ⟨Γ₂, hΓ₂, hψφ⟩
  refine extSetProvable_of_closedTheory (T := T) (Δ := Γ₁ ++ Γ₂) ?_ ?_
  · intro ξ hξ
    rcases List.mem_append.mp hξ with hξ | hξ
    · exact hΓ₁ ξ hξ
    · exact hΓ₂ ξ hξ
  · exact
      ExtDerivation.eqPropI
        (ExtDerivation.mono
          (Δ := Γ₁) (Δ' := Γ₁ ++ Γ₂) (φ := imp φ ψ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inl hξ))
          hφψ)
        (ExtDerivation.mono
          (Δ := Γ₂) (Δ' := Γ₁ ++ Γ₂) (φ := imp ψ φ)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inr hξ))
          hψφ)

/-- Membership of closed propositions is invariant under closed-theory provable
equivalence. -/
theorem mem_iff_of_provablyEquivalent_prop
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    {φ ψ : Sentence}
    (hEqv : Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
      (Const := Primitive) T φ ψ) :
    φ ∈ T ↔ ψ ∈ T := by
  constructor
  · intro hφ
    exact hT.closed <|
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
        (T := T)
        (φ := φ)
        (ψ := ψ)
        (hImp := hEqv.1)
        (hφ := Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive) hφ)
  · intro hψ
    exact hT.closed <|
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_mp
        (T := T)
        (φ := ψ)
        (ψ := φ)
        (hImp := hEqv.2)
        (hφ := Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive) hψ)

/-- In a complete consistent theory, two closed propositions with the same
membership status are propositionally equal in the extensional quotient. -/
theorem termEquivalent_of_membership_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    {φ ψ : Sentence}
    (hiff : φ ∈ T ↔ ψ ∈ T) :
    TermEquivalent T φ ψ := by
  by_cases hφ : φ ∈ T
  · have hψ : ψ ∈ T := hiff.mp hφ
    exact
      extSetProvable_imp_mp
        (extSetProvable_imp_mp
          (extSetProvable_of_theorem
            (T := T)
            (hφ := derived19 φ ψ))
          (extSetProvable_of_mem (T := T) hφ))
        (extSetProvable_of_mem (T := T) hψ)
  · have hψ : ψ ∉ T := by
      intro hψ
      exact hφ (hiff.mpr hψ)
    have hNotφ : not φ ∈ T :=
      CompleteConsistentTheory.neg_mem_of_not_mem hT hφ
    have hNotψ : not ψ ∈ T :=
      CompleteConsistentTheory.neg_mem_of_not_mem hT hψ
    exact
      extSetProvable_imp_mp
        (extSetProvable_imp_mp
          (extSetProvable_of_theorem
            (T := T)
            (hφ := derived20 φ ψ))
        (extSetProvable_of_mem (T := T) hNotφ))
        (extSetProvable_of_mem (T := T) hNotψ)

/-- Equality formulas are invariant under extensional provable equality of
their term arguments. -/
theorem provablyEquivalent_eq_of_termEquivalent
    {T : ClosedTheorySet} {α : HTy}
    {t t' u u' : ClosedTerm α}
    (htt' : TermEquivalent T t t')
    (huu' : TermEquivalent T u u') :
    Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
      (Const := Primitive) T (eq t u) (eq t' u') := by
  rcases htt' with ⟨Γ₁, hΓ₁, htt'⟩
  rcases huu' with ⟨Γ₂, hΓ₂, huu'⟩
  constructor
  · refine
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
        (Const := Primitive)
        (T := T)
        (Δ := Γ₁ ++ Γ₂)
        ?_
        ?_
    · intro ξ hξ
      rcases List.mem_append.mp hξ with hξ | hξ
      · exact hΓ₁ ξ hξ
      · exact hΓ₂ ξ hξ
    · refine .impI ?_
      have htt'_ctx :
          ExtDerivation Primitive (eq t u :: (Γ₁ ++ Γ₂)) (eq t t') :=
        ExtDerivation.mono
          (Δ := Γ₁)
          (Δ' := eq t u :: (Γ₁ ++ Γ₂))
          (φ := eq t t')
          (by
            intro ξ hξ
            show ξ ∈ eq t u :: (Γ₁ ++ Γ₂)
            simp [hξ])
          htt'
      have huu'_ctx :
          ExtDerivation Primitive (eq t u :: (Γ₁ ++ Γ₂)) (eq u u') :=
        ExtDerivation.mono
          (Δ := Γ₂)
          (Δ' := eq t u :: (Γ₁ ++ Γ₂))
          (φ := eq u u')
          (by
            intro ξ hξ
            show ξ ∈ eq t u :: (Γ₁ ++ Γ₂)
            simp [hξ])
          huu'
      have hEqtu :
          ExtDerivation Primitive (eq t u :: (Γ₁ ++ Γ₂)) (eq t u) :=
        .hyp (by simp)
      have ht't :
          ExtDerivation Primitive (eq t u :: (Γ₁ ++ Γ₂)) (eq t' t) :=
        .eqSymm htt'_ctx
      have ht'u :
          ExtDerivation Primitive (eq t u :: (Γ₁ ++ Γ₂)) (eq t' u) :=
        .eqTrans ht't hEqtu
      exact .eqTrans ht'u huu'_ctx
  · refine
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
        (Const := Primitive)
        (T := T)
        (Δ := Γ₁ ++ Γ₂)
        ?_
        ?_
    · intro ξ hξ
      rcases List.mem_append.mp hξ with hξ | hξ
      · exact hΓ₁ ξ hξ
      · exact hΓ₂ ξ hξ
    · refine .impI ?_
      have htt'_ctx :
          ExtDerivation Primitive (eq t' u' :: (Γ₁ ++ Γ₂)) (eq t t') :=
        ExtDerivation.mono
          (Δ := Γ₁)
          (Δ' := eq t' u' :: (Γ₁ ++ Γ₂))
          (φ := eq t t')
          (by
            intro ξ hξ
            show ξ ∈ eq t' u' :: (Γ₁ ++ Γ₂)
            simp [hξ])
          htt'
      have huu'_ctx :
          ExtDerivation Primitive (eq t' u' :: (Γ₁ ++ Γ₂)) (eq u u') :=
        ExtDerivation.mono
          (Δ := Γ₂)
          (Δ' := eq t' u' :: (Γ₁ ++ Γ₂))
          (φ := eq u u')
          (by
            intro ξ hξ
            show ξ ∈ eq t' u' :: (Γ₁ ++ Γ₂)
            simp [hξ])
          huu'
      have hEqt'u' :
          ExtDerivation Primitive (eq t' u' :: (Γ₁ ++ Γ₂)) (eq t' u') :=
        .hyp (by simp)
      have htu' :
          ExtDerivation Primitive (eq t' u' :: (Γ₁ ++ Γ₂)) (eq t u') :=
        .eqTrans htt'_ctx hEqt'u'
      have hu'u :
          ExtDerivation Primitive (eq t' u' :: (Γ₁ ++ Γ₂)) (eq u' u) :=
        .eqSymm huu'_ctx
      exact .eqTrans htu' hu'u

namespace RepresentativeAssignment

/-- If two representative assignments realize the same quotient-valued class
assignment, then they assign provably equivalent closed representatives to each
variable. -/
theorem termEquivalent_of_realizes
    {T : ClosedTheorySet}
    {ν : ClassAssignment T Γ}
    {ρ σ : RepresentativeAssignment Γ}
    (hρ : Realizes T ρ ν)
    (hσ : Realizes T σ ν)
    {τ : HTy} (v : Var Γ τ) :
    TermEquivalent T (ρ v) (σ v) := by
  exact
    (classOf_eq_iff (T := T)).1 <|
      by rw [hρ v, hσ v]

end RepresentativeAssignment

/-- Representative-assignment version of the universal closed-instance clause:
closing `∀x.φ` using `ρ` is membership-equivalent to membership of all closed
instances of the closed body. -/
theorem closeFormula_all_iff_forall_closed_instances
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hAll : UniversalCounterexampleClosed T)
    (ρ : RepresentativeAssignment Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    closeFormula ρ (.all φ) ∈ T ↔
      ∀ t : ClosedTerm σ, closeTerm (RepresentativeAssignment.extend ρ t) φ ∈ T := by
  constructor
  · intro hForall t
    have hAllMem : (.all (subst
        (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ) : Sentence) ∈ T := by
      simpa [closeFormula, closeTerm, subst] using hForall
    have hInst :
        instantiate t
          (subst
            (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ) ∈ T :=
      hT.closed <|
        provable_specialize_closed
          (T := T)
          (φ := subst
            (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ)
          (t := t)
          (Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
            (Const := Primitive) hAllMem)
    simpa [instantiate_subst_lift] using hInst
  · intro hInstances
    by_contra hNotAll
    have hNotAll' :
        (.all (subst
          (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ) : Sentence) ∉ T := by
      simpa [closeFormula, closeTerm, subst] using hNotAll
    rcases hAll (φ := subst
      (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ) hNotAll' with ⟨t, ht⟩
    exact ht <| by simpa [instantiate_subst_lift] using hInstances t

/-- Representative-assignment version of Henkin's witness clause: closing
`∃x.φ` using `ρ` is membership-equivalent to existence of a closed witness for
the closed body. -/
theorem closeFormula_ex_iff_exists_closed_witness
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (ρ : RepresentativeAssignment Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    closeFormula ρ (.ex φ) ∈ T ↔
      ∃ t : ClosedTerm σ, closeTerm (RepresentativeAssignment.extend ρ t) φ ∈ T := by
  constructor
  · intro hExMem
    have hExMem' :
        (.ex (subst
          (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ) : Sentence) ∈ T := by
      simpa [closeFormula, closeTerm, subst] using hExMem
    rcases hEx
      (φ := subst
        (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ)
      hExMem' with ⟨t, ht⟩
    exact ⟨t, by simpa [instantiate_subst_lift] using ht⟩
  · rintro ⟨t, ht⟩
    have hProv :
        SetProvable T
          (.ex (subst
            (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ) : Sentence) :=
      provable_exists_closed
        (T := T)
        (φ := subst
          (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ)
        (t := t)
        (Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive) (by simpa [instantiate_subst_lift] using ht))
    have hMem :
        (.ex (subst
          (Subst.lift (Base := Atom) (Const := Primitive) ρ) φ) : Sentence) ∈ T :=
      hT.closed hProv
    simpa [closeFormula, closeTerm, subst] using hMem

namespace RepresentativeAssignment

/-- Pointwise extensional equivalence of representative assignments is preserved
when both sides are extended by the same closed witness. -/
theorem extend_termEquivalent_of_pointwise
    {T : ClosedTheorySet}
    {ρ σ : RepresentativeAssignment Γ}
    (hρσ : ∀ {τ}, (v : Var Γ τ) → TermEquivalent T (ρ v) (σ v))
    (t : ClosedTerm α) :
    ∀ {τ}, (v : Var (α :: Γ) τ) →
      TermEquivalent T
        (RepresentativeAssignment.extend ρ t v)
        (RepresentativeAssignment.extend σ t v) := by
  intro τ v
  cases v with
  | vz =>
      simpa [RepresentativeAssignment.extend] using termEquivalent_refl T t
  | vs v =>
      simpa [RepresentativeAssignment.extend] using hρσ v

end RepresentativeAssignment

/-- Closing a term is invariant under pointwise extensional equivalence of the
chosen representatives. -/
theorem closeTerm_termEquivalent_of_pointwise
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    {ρ σ : RepresentativeAssignment Γ}
    (hρσ : ∀ {τ}, (v : Var Γ τ) → TermEquivalent T (ρ v) (σ v))
    {τ : HTy} (t : Term Γ τ) :
    TermEquivalent T (closeTerm ρ t) (closeTerm σ t) := by
  induction t with
  | var v =>
      simpa [closeTerm, subst] using hρσ v
  | const c =>
      simpa [closeTerm, subst] using
        (termEquivalent_refl T (.const c : ClosedTerm _))
  | app f u ihf ihu =>
      simpa [closeTerm, subst] using
        (termEquivalent_app
          (ihf hρσ)
          (ihu hρσ))
  | lam body ih =>
      let f : ClosedTerm _ := closeTerm ρ (.lam body)
      let g : ClosedTerm _ := closeTerm σ (.lam body)
      let ε : RepresentativeAssignment ([] : Ctx Atom) := fun {_} v => nomatch v
      have hInstances :
          ∀ t : ClosedTerm _, closeTerm (RepresentativeAssignment.extend ε t)
            (pointwiseEq f g) ∈ T := by
        intro t
        have hBody :
            TermEquivalent T
              (closeTerm (RepresentativeAssignment.extend ρ t) body)
              (closeTerm (RepresentativeAssignment.extend σ t) body) :=
          by
            apply ih
            intro τ v
            exact
              RepresentativeAssignment.extend_termEquivalent_of_pointwise
                (T := T) (ρ := ρ) (σ := σ) hρσ t v
        have hBetaLeft :
            TermEquivalent T
              (.app f t)
              (closeTerm (RepresentativeAssignment.extend ρ t) body) := by
          exact
            extSetProvable_of_theorem (T := T) <|
              by
                simpa [f, closeTerm, instantiate_subst_lift, subst, eq] using
                  (ExtDerivation.beta t
                    (subst
                      (Subst.lift (Base := Atom) (Const := Primitive) ρ)
                      body))
        have hBetaRight :
            TermEquivalent T
              (.app g t)
              (closeTerm (RepresentativeAssignment.extend σ t) body) := by
          exact
            extSetProvable_of_theorem (T := T) <|
              by
                simpa [g, closeTerm, instantiate_subst_lift, subst, eq] using
                  (ExtDerivation.beta t
                    (subst
                      (Subst.lift (Base := Atom) (Const := Primitive) σ)
                      body))
        have hApp :
            TermEquivalent T (.app f t) (.app g t) :=
          termEquivalent_trans
            (termEquivalent_trans hBetaLeft hBody)
            (termEquivalent_symm hBetaRight)
        have hWeakenF :
            subst (RepresentativeAssignment.extend ε t)
              (weaken (Base := Atom) (Const := Primitive) f) = f := by
          simpa [weakenCtx] using
            (RepresentativeAssignment.close_weakenCtx
              (ρ := RepresentativeAssignment.extend ε t)
              (Γ := [_])
              (t := f))
        have hWeakenG :
            subst (RepresentativeAssignment.extend ε t)
              (weaken (Base := Atom) (Const := Primitive) g) = g := by
          simpa [weakenCtx] using
            (RepresentativeAssignment.close_weakenCtx
              (ρ := RepresentativeAssignment.extend ε t)
              (Γ := [_])
              (t := g))
        have hAppMem : eq (.app f t) (.app g t) ∈ T :=
          hT.closed hApp
        have hPointwiseClose :
            closeTerm (RepresentativeAssignment.extend ε t) (pointwiseEq f g) =
              eq (.app f t) (.app g t) := by
          change
            eq
              (subst (RepresentativeAssignment.extend ε t)
                (.app (weaken f) (.var .vz)))
              (subst (RepresentativeAssignment.extend ε t)
                (.app (weaken g) (.var .vz))) =
              eq (.app f t) (.app g t)
          change
            eq
              (.app
                (subst (RepresentativeAssignment.extend ε t) (weaken f))
                (subst (RepresentativeAssignment.extend ε t) (.var .vz)))
              (.app
                (subst (RepresentativeAssignment.extend ε t) (weaken g))
                (subst (RepresentativeAssignment.extend ε t) (.var .vz))) =
              eq (.app f t) (.app g t)
          simp [RepresentativeAssignment.extend, hWeakenF, hWeakenG]
        exact hPointwiseClose ▸ hAppMem
      have hForallMem : (.all (pointwiseEq f g) : Sentence) ∈ T := by
        have hAllIff :=
          closeFormula_all_iff_forall_closed_instances
            (T := T) hT hAll ε (pointwiseEq f g)
        simpa [closeFormula] using hAllIff.mpr hInstances
      have hEq : TermEquivalent T f g :=
        extSetProvable_imp_mp
          (extSetProvable_of_theorem (T := T) (hφ := eq_of_pointwiseEq f g))
          (extSetProvable_of_mem (T := T) hForallMem)
      simpa [f, g] using hEq
  | top =>
      simpa [closeTerm, subst] using
        (termEquivalent_refl T (.top : Sentence))
  | bot =>
      simpa [closeTerm, subst] using
        (termEquivalent_refl T (.bot : Sentence))
  | and φ ψ ihφ ihψ =>
      simpa [closeTerm, subst] using
        (termEquivalent_of_provablyEquivalent_prop
          (Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.and_congr
            (provablyEquivalent_of_termEquivalent_prop (ihφ hρσ))
            (provablyEquivalent_of_termEquivalent_prop (ihψ hρσ))))
  | or φ ψ ihφ ihψ =>
      simpa [closeTerm, subst] using
        (termEquivalent_of_provablyEquivalent_prop
          (Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.or_congr
            (provablyEquivalent_of_termEquivalent_prop (ihφ hρσ))
            (provablyEquivalent_of_termEquivalent_prop (ihψ hρσ))))
  | imp φ ψ ihφ ihψ =>
      simpa [closeTerm, subst] using
        (termEquivalent_of_provablyEquivalent_prop
          (Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent.imp_congr
            (provablyEquivalent_of_termEquivalent_prop (ihφ hρσ))
            (provablyEquivalent_of_termEquivalent_prop (ihψ hρσ))))
  | not φ ihφ =>
      have hEqv :
          Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
            (Const := Primitive) T
            (closeFormula ρ φ) (closeFormula σ φ) :=
        provablyEquivalent_of_termEquivalent_prop (ihφ hρσ)
      have hNotEqv :
          Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
            (Const := Primitive) T
            (.not (closeFormula ρ φ))
            (.not (closeFormula σ φ)) := by
        exact
          ⟨Mettapedia.Logic.HOL.ClosedTheorySet.Provable.not_congr hEqv.2,
            Mettapedia.Logic.HOL.ClosedTheorySet.Provable.not_congr hEqv.1⟩
      simpa [closeTerm, closeFormula, subst] using
        (termEquivalent_of_provablyEquivalent_prop hNotEqv)
  | eq t u iht ihu =>
      simpa [closeTerm, subst, eq] using
        (termEquivalent_of_provablyEquivalent_prop
          (provablyEquivalent_eq_of_termEquivalent
            (iht hρσ) (ihu hρσ)))
  | all φ ih =>
      have hAllMem :
          closeFormula ρ (.all φ) ∈ T ↔
            closeFormula σ (.all φ) ∈ T := by
        rw [closeFormula_all_iff_forall_closed_instances hT hAll ρ φ,
          closeFormula_all_iff_forall_closed_instances hT hAll σ φ]
        constructor
        · intro hInstances t
          have hEq :
              TermEquivalent T
                (closeTerm (RepresentativeAssignment.extend ρ t) φ)
                (closeTerm (RepresentativeAssignment.extend σ t) φ) :=
            ih <|
              RepresentativeAssignment.extend_termEquivalent_of_pointwise
                (T := T) (ρ := ρ) (σ := σ) hρσ t
          exact
            (mem_iff_of_provablyEquivalent_prop hT
              (provablyEquivalent_of_termEquivalent_prop hEq)).mp
              (hInstances t)
        · intro hInstances t
          have hEq :
              TermEquivalent T
                (closeTerm (RepresentativeAssignment.extend ρ t) φ)
                (closeTerm (RepresentativeAssignment.extend σ t) φ) :=
            ih <|
              RepresentativeAssignment.extend_termEquivalent_of_pointwise
                (T := T) (ρ := ρ) (σ := σ) hρσ t
          exact
            (mem_iff_of_provablyEquivalent_prop hT
              (provablyEquivalent_of_termEquivalent_prop hEq)).mpr
              (hInstances t)
      simpa [closeFormula] using termEquivalent_of_membership_iff hT hAllMem
  | ex φ ih =>
      have hExMem :
          closeFormula ρ (.ex φ) ∈ T ↔
            closeFormula σ (.ex φ) ∈ T := by
        rw [closeFormula_ex_iff_exists_closed_witness hT hEx ρ φ,
          closeFormula_ex_iff_exists_closed_witness hT hEx σ φ]
        constructor
        · rintro ⟨t, ht⟩
          refine ⟨t, ?_⟩
          have hEq :
              TermEquivalent T
                (closeTerm (RepresentativeAssignment.extend ρ t) φ)
                (closeTerm (RepresentativeAssignment.extend σ t) φ) :=
            ih <|
              RepresentativeAssignment.extend_termEquivalent_of_pointwise
                (T := T) (ρ := ρ) (σ := σ) hρσ t
          exact
            (mem_iff_of_provablyEquivalent_prop hT
              (provablyEquivalent_of_termEquivalent_prop hEq)).mp ht
        · rintro ⟨t, ht⟩
          refine ⟨t, ?_⟩
          have hEq :
              TermEquivalent T
                (closeTerm (RepresentativeAssignment.extend ρ t) φ)
                (closeTerm (RepresentativeAssignment.extend σ t) φ) :=
            ih <|
              RepresentativeAssignment.extend_termEquivalent_of_pointwise
                (T := T) (ρ := ρ) (σ := σ) hρσ t
          exact
            (mem_iff_of_provablyEquivalent_prop hT
              (provablyEquivalent_of_termEquivalent_prop hEq)).mpr ht
      simpa [closeFormula] using termEquivalent_of_membership_iff hT hExMem

/-- Closed-theory membership of a closed representative-substitution is
invariant under pointwise extensional equivalence of the representatives. -/
theorem closeFormula_mem_iff_of_pointwise
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    {ρ σ : RepresentativeAssignment Γ}
    (hρσ : ∀ {τ}, (v : Var Γ τ) → TermEquivalent T (ρ v) (σ v))
    (φ : Formula Γ) :
    closeFormula ρ φ ∈ T ↔ closeFormula σ φ ∈ T := by
  exact
    mem_iff_of_provablyEquivalent_prop hT
      (provablyEquivalent_of_termEquivalent_prop
        (closeTerm_termEquivalent_of_pointwise
          hT hEx hAll hρσ φ))

/-- Canonical truth is independent of the chosen realizing representative
assignment. -/
theorem holds_iff_closeFormula_of_realizes
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    {ν : ClassAssignment T Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes T ρ ν)
    (φ : Formula Γ) :
    Holds T ν φ ↔ closeFormula ρ φ ∈ T := by
  unfold Holds ClassAssignment.closeFormula ClassAssignment.closeTerm
  exact
    closeFormula_mem_iff_of_pointwise
      hT hEx hAll
      (fun v =>
        RepresentativeAssignment.termEquivalent_of_realizes
          (hρ := ClassAssignment.chooseRepresentatives_realizes ν)
          (hσ := hρ)
          v)
      φ

end Mettapedia.AutoBooks.Codex.Henkin1950
