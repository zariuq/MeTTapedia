import Mettapedia.AutoBooks.Codex.Henkin1950.AxiomSchemes
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalTruth

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Transport open derivations to closed theorems by representative substitution.

Henkin's canonical truth relation closes an open formula by replacing each free
variable with a chosen closed representative. To reuse theorem schemata inside
that canonical layer, we need the corresponding proof-theoretic substitution
principle: an open derivation remains a derivation after substituting closed
terms for its free variables.
-/

/-- Substituting into weakened hypotheses is the same as weakening substituted
hypotheses. -/
@[simp] theorem derivation_subst_weakenHyps
    (σs : Subst Primitive Γ Δ)
    (Θ : List (Formula Γ)) :
    weakenHyps
        (Base := Atom)
        (Const := Primitive)
        (σ := σ)
        (Θ.map (subst σs)) =
      (weakenHyps
          (Base := Atom)
          (Const := Primitive)
          (σ := σ)
          Θ).map
        (subst (Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs)) := by
  simp [weakenHyps, List.map_map, Function.comp, subst_weaken]

/-- Substitution commutes with one-step instantiation. -/
@[simp] theorem derivation_subst_instantiate
    (σs : Subst Primitive Γ Δ)
    (t : Term Γ σ)
    (u : Term (σ :: Γ) τ) :
    subst σs (instantiate (Base := Atom) t u) =
      instantiate
        (Base := Atom)
        (subst σs t)
        (subst (Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs) u) := by
  have hcomp :
      (Subst.comp
        σs
        (Subst.single (Base := Atom) (Const := Primitive) t) :
          Subst Primitive (σ :: Γ) Δ) =
      (Subst.comp
        (Subst.single (Base := Atom) (Const := Primitive) (subst σs t))
        (Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs) :
          Subst Primitive (σ :: Γ) Δ) := by
    funext α v
    cases v with
    | vz =>
        rfl
    | vs v =>
        simpa [Subst.comp, Subst.lift, Subst.single, instantiate, weaken] using
          (instantiate_weaken
            (Base := Atom)
            (Const := Primitive)
            (t := subst σs t)
            (u := σs v)).symm
  unfold instantiate
  calc
    subst σs
        (subst
          (Subst.single (Base := Atom) (Const := Primitive) t)
          u) =
      subst
        (Subst.comp
          σs
          (Subst.single (Base := Atom) (Const := Primitive) t))
        u := by
          exact
            (subst_comp
              (Base := Atom)
              (Const := Primitive)
              (τs := σs)
              (σs := Subst.single (Base := Atom) (Const := Primitive) t)
              (t := u))
    _ =
      subst
        (Subst.comp
          (Subst.single (Base := Atom) (Const := Primitive) (subst σs t))
          (Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs))
        u := by
          rw [hcomp]
    _ =
      subst
        (Subst.single (Base := Atom) (Const := Primitive) (subst σs t))
        (subst
          (Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs)
          u) := by
            exact
              (subst_comp
                (Base := Atom)
                (Const := Primitive)
                (τs := Subst.single (Base := Atom) (Const := Primitive) (subst σs t))
                (σs := Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs)
                (t := u)).symm

/-- Variable substitution is admissible for the trusted HOL derivation core. -/
theorem derivation_subst
    (σs : Subst Primitive Γ Δ) :
    Derivation Primitive Θ φ →
      Derivation Primitive
        (Θ.map (subst σs))
        (subst σs φ) := by
  intro d
  induction d generalizing Δ with
  | hyp hmem =>
      exact .hyp (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  | topI =>
      exact .topI
  | botE h ih =>
      exact .botE (ih σs)
  | andI hφ hψ ihφ ihψ =>
      exact .andI (ihφ σs) (ihψ σs)
  | andEL h ih =>
      exact .andEL (ih σs)
  | andER h ih =>
      exact .andER (ih σs)
  | orIL h ih =>
      exact .orIL (ih σs)
  | orIR h ih =>
      exact .orIR (ih σs)
  | orE hor hφ hψ ihor ihφ ihψ =>
      exact .orE (ihor σs) (ihφ σs) (ihψ σs)
  | impI h ih =>
      exact .impI (ih σs)
  | impE hφψ hφ ihφψ ihφ =>
      exact .impE (ihφψ σs) (ihφ σs)
  | notI h ih =>
      exact .notI (ih σs)
  | notE hnot hφ ihnot ihφ =>
      exact .notE (ihnot σs) (ihφ σs)
  | allI h ih =>
      exact .allI (by
        simpa [derivation_subst_weakenHyps] using
          ih (Subst.lift (Base := Atom) (Const := Primitive) (σ := _) σs))
  | allE t h ih =>
      simpa [derivation_subst_instantiate] using
        (.allE (subst σs t) (ih σs))
  | exI t h ih =>
      rename_i Γ' Θ' σ body
      have ih' :
          Derivation Primitive
            (Θ'.map (subst σs))
            (instantiate
              (subst σs t)
              (subst
                (Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs)
                body)) := by
        simpa [derivation_subst_instantiate] using (ih σs)
      exact .exI (subst σs t) ih'
  | exE hex hbody ihex ihbody =>
      rename_i Γ' Θ' σ body ψ
      refine .exE (ihex σs) ?_
      simpa [List.map, derivation_subst_weakenHyps, subst_weaken] using
        ihbody (Subst.lift (Base := Atom) (Const := Primitive) (σ := σ) σs)
  | eqRefl t =>
      exact .eqRefl (subst σs t)
  | eqSymm h ih =>
      exact .eqSymm (ih σs)
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans (ihtu σs) (ihuv σs)
  | eqApp t h ih =>
      exact .eqApp (subst σs t) (ih σs)
  | eqLam h ih =>
      exact .eqLam (by
        simp only [derivation_subst_weakenHyps]
        exact ih (Subst.lift (Base := Atom) (Const := Primitive) (σ := _) σs))
  | funExt h ih =>
      exact .funExt (by
        simpa [subst, subst_weaken, Subst.lift] using ih σs)
  | beta t u =>
      simpa [subst, derivation_subst_instantiate] using
        (.beta
          (subst σs t)
          (subst (Subst.lift (Base := Atom) (Const := Primitive) (σ := _) σs) u))
  | eta f =>
      simpa [subst, subst_weaken] using
        (.eta (subst σs f))

/-- Closing an open theorem in context by representative substitution yields a
closed theorem. -/
theorem closeTheoremInContext
    (ρ : RepresentativeAssignment Γ)
    {φ : Formula Γ} :
    TheoremInContext φ →
      Theorem (closeFormula ρ φ) := by
  intro hφ
  simp only [Theorem, closeFormula]
  exact
    (derivation_subst (Γ := Γ) (Θ := ([] : List (Formula Γ)))
      (φ := φ) ρ hφ)

/-- Every open theorem in context holds in the canonical truth relation of a
complete consistent theory after closing by any quotient-valued assignment. -/
theorem holds_of_theoremInContext
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : ClassAssignment T Γ)
    {φ : Formula Γ} :
    TheoremInContext φ →
      Holds T ν φ := by
  intro hφ
  have hClosed :
      Theorem (ClassAssignment.closeFormula ν φ) :=
    closeTheoremInContext (ρ := ClassAssignment.chooseRepresentatives ν) hφ
  have hClosedExt :
      ExtDerivation.Theorem Primitive (ClassAssignment.closeFormula ν φ) :=
    ExtDerivation.ofBase hClosed
  exact hT.closed <|
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_closedTheory
      (Const := Primitive)
      (T := T)
      (Δ := [])
      (hΔ := by intro ψ hψ; cases hψ)
      hClosedExt

/-- Positive canary: Henkin axiom 5 holds in every complete consistent
canonical theory. -/
theorem holds_axiom5
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : ClassAssignment T [α, Pred α]) :
    Holds T ν (axiom5 (α := α)) :=
  holds_of_theoremInContext (T := T) hT ν axiom5_theorem

/-- Positive canary: Henkin axiom 10 holds in every complete consistent
canonical theory. -/
theorem holds_axiom10
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : ClassAssignment T [σ ⇒ τ, σ ⇒ τ]) :
    Holds T ν (axiom10 (σ := σ) (τ := τ)) :=
  holds_of_theoremInContext (T := T) hT ν axiom10_theorem

end Mettapedia.AutoBooks.Codex.Henkin1950
