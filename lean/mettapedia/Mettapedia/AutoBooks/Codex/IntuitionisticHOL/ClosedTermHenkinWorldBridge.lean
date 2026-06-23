import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModelCountermodel

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Ordinary term substitution commutes with one-step instantiation. This is the
term-substitution analogue of `rename_instantiate` and is needed to substitute a
fresh eigenconstant back into an abstracted derivation. -/
theorem subst_instantiate
    {Γ Γ' : Ctx Base} {σ τ : Ty Base}
    (σs : Subst Const Γ Γ') (t : Term Const Γ σ)
    (u : Term Const (σ :: Γ) τ) :
    subst σs (instantiate (Base := Base) t u) =
      instantiate (Base := Base)
        (subst σs t)
        (subst (Subst.lift (Base := Base) (σ := σ) σs) u) := by
  unfold instantiate
  calc
    subst σs (subst (Subst.single (Base := Base) (Const := Const) t) u) =
        subst
          (Subst.comp σs
            (Subst.single (Base := Base) (Const := Const) t)) u := by
          exact subst_comp (Base := Base) (Const := Const)
            (τs := σs)
            (σs := Subst.single (Base := Base) (Const := Const) t)
            (t := u)
    _ =
        subst
          (Subst.comp
            (Subst.single (Base := Base) (Const := Const) (subst σs t))
            (Subst.lift (Base := Base) (Const := Const) (σ := σ) σs)) u := by
          apply subst_ext
          intro ρ v
          cases v with
          | vz =>
              rfl
          | vs v =>
              change σs v =
                subst (Subst.single (Base := Base) (Const := Const) (subst σs t))
                  (rename
                    (Rename.weaken (Base := Base) (Γ := Γ') (σ := σ)) (σs v))
              exact
                (instantiate_weaken
                  (Base := Base) (Const := Const)
                  (σ := σ) (t := subst σs t) (u := σs v)).symm
    _ =
        subst (Subst.single (Base := Base) (Const := Const) (subst σs t))
          (subst (Subst.lift (Base := Base) (Const := Const) (σ := σ) σs) u) := by
          symm
          exact subst_comp (Base := Base) (Const := Const)
            (τs := Subst.single (Base := Base) (Const := Const) (subst σs t))
            (σs := Subst.lift (Base := Base) (Const := Const) (σ := σ) σs)
            (t := u)

@[simp] theorem weakenHyps_append
    {Γ : Ctx Base} {σ : Ty Base}
    (Δ Ε : List (Formula Const Γ)) :
    weakenHyps (Base := Base) (Const := Const) (σ := σ) (Δ ++ Ε) =
      weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ ++
        weakenHyps (Base := Base) (Const := Const) (σ := σ) Ε := by
  simp [weakenHyps]

/-- A closed formula viewed in an arbitrary variable context by iterated
weakening. This is the open-context image of a closed antecedent in the
cut-free Henkin-elimination induction. -/
abbrev weakenClosedFormulaToCtx (Γ : Ctx Base) (φ : ClosedFormula Const) :
    Formula Const Γ :=
  weakenCtx Γ φ

@[simp] theorem weakenClosedFormulaToCtx_nil (φ : ClosedFormula Const) :
    weakenClosedFormulaToCtx (Base := Base) (Const := Const) [] φ = φ := by
  rfl

@[simp] theorem weakenClosedFormulaToCtx_cons
    (Γ : Ctx Base) (φ : ClosedFormula Const) :
    weakenClosedFormulaToCtx (Base := Base) (Const := Const) (σ :: Γ) φ =
      weaken (Base := Base) (Const := Const) (σ := σ)
        (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ φ) := by
  rfl

/-- A finite closed theory viewed in an arbitrary variable context. -/
def weakenClosedTheoryToCtx (Γ : Ctx Base) (Δ : ClosedTheory Const) :
    List (Formula Const Γ) :=
  Δ.map (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ)

@[simp] theorem weakenClosedTheoryToCtx_nil (Γ : Ctx Base) :
    weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ
      ([] : ClosedTheory Const) = [] := by
  rfl

@[simp] theorem weakenClosedTheoryToCtx_empty (Δ : ClosedTheory Const) :
    weakenClosedTheoryToCtx (Base := Base) (Const := Const) [] Δ = Δ := by
  induction Δ with
  | nil =>
      rfl
  | cons φ Δ ih =>
      simp only [weakenClosedTheoryToCtx, List.map_cons, weakenClosedFormulaToCtx_nil]
      exact congrArg (fun tail => φ :: tail) ih

@[simp] theorem weakenClosedTheoryToCtx_cons
    (Γ : Ctx Base) (φ : ClosedFormula Const) (Δ : ClosedTheory Const) :
    weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ (φ :: Δ) =
      weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ φ ::
        weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ Δ := by
  rfl

@[simp] theorem weakenClosedTheoryToCtx_append
    (Γ : Ctx Base) (Δ E : ClosedTheory Const) :
    weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ (Δ ++ E) =
      weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ Δ ++
        weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ E := by
  simp [weakenClosedTheoryToCtx]

@[simp] theorem weakenClosedTheoryToCtx_ctx_cons
    {σ : Ty Base} (Γ : Ctx Base) (Δ : ClosedTheory Const) :
    weakenClosedTheoryToCtx (Base := Base) (Const := Const) (σ :: Γ) Δ =
      weakenHyps (Base := Base) (Const := Const) (σ := σ)
        (weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ Δ) := by
  induction Δ with
  | nil =>
      rfl
  | cons φ Δ ih =>
      simp [weakenClosedTheoryToCtx, weakenHyps]

theorem weakenAntecedents_eq_weakenHyps
    {Γ : Ctx Base} {σ : Ty Base} (Δ : List (Formula Const Γ)) :
    Mettapedia.AutoBooks.Codex.IntuitionisticHOL.weakenAntecedents σ Δ =
      weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ := by
  rfl

theorem noConstOccurrence_weakenCtx
    {σ τ : Ty Base} (c : Const σ) (Γ : Ctx Base)
    {t : ClosedTerm Const τ}
    (ht : NoConstOccurrence c t) :
    NoConstOccurrence c (weakenCtx Γ t) := by
  induction Γ with
  | nil =>
      simpa using ht
  | cons ρ Γ ih =>
      change NoConstOccurrence c
        (rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := ρ)) (weakenCtx Γ t))
      exact
        noConstOccurrence_rename
          (Base := Base) (Const := Const)
          (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := ρ))
          (weakenCtx Γ t) ih

theorem noConstOccurrence_weakenClosedFormulaToCtx
    {σ : Ty Base} (c : Const σ) (Γ : Ctx Base)
    {φ : ClosedFormula Const}
    (hφ : NoConstOccurrence c φ) :
    NoConstOccurrence c
      (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ φ) :=
  noConstOccurrence_weakenCtx (Base := Base) (Const := Const) c Γ hφ

@[simp] theorem weakenClosedFormulaToCtx_imp
    (Γ : Ctx Base) (φ ψ : ClosedFormula Const) :
    weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ (.imp φ ψ) =
      .imp
        (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ φ)
        (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ ψ) := by
  induction Γ with
  | nil =>
      rfl
  | cons σ Γ ih =>
      simp [weakenClosedFormulaToCtx, weakenCtx, weaken, rename, ih]

theorem extDerivation_weakenClosedTheoryToCtx
    (Γ : Ctx Base) {Δ : ClosedTheory Const} {θ : ClosedFormula Const}
    (hDer : ClosedTheory.Provable (Const := Const) Δ θ) :
    ExtDerivation Const
      (weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ Δ)
      (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ θ) := by
  induction Γ with
  | nil =>
      rw [weakenClosedTheoryToCtx_empty, weakenClosedFormulaToCtx_nil]
      exact hDer
  | cons σ Γ ih =>
      rw [weakenClosedTheoryToCtx_ctx_cons, weakenClosedFormulaToCtx_cons]
      exact
        (ExtDerivation.rename
          (Base := Base) (Const := Const)
          (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
          ih)

namespace ExtDerivation

@[simp] theorem subst_weakenHyps
    {Γ Γ' : Ctx Base} {σ : Ty Base}
    (σs : Subst Const Γ Γ') (Δ : List (Formula Const Γ)) :
    weakenHyps
        (Base := Base)
        (Const := Const)
        (σ := σ)
        (Δ.map (Mettapedia.Logic.HOL.subst σs)) =
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ).map
        (Mettapedia.Logic.HOL.subst
          (Subst.lift (Base := Base) (Const := Const) (σ := σ) σs)) := by
  simp [weakenHyps, List.map_map, Function.comp, Mettapedia.Logic.HOL.subst_weaken]

/-- Ordinary term-substitution preserves extended HOL derivability. This local
Codex bridge mirrors the trusted renaming and constant-substitution preservation
lemmas from the HOL core without changing that core. -/
theorem subst_derivation
    {Γ Γ' : Ctx Base}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (σs : Subst Const Γ Γ') :
    ExtDerivation Const Δ φ →
      ExtDerivation Const
        (Δ.map (Mettapedia.Logic.HOL.subst σs))
        (Mettapedia.Logic.HOL.subst σs φ) := by
  intro d
  induction d generalizing Γ' with
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
      refine .orE (ihor σs) ?_ ?_
      · simpa [List.map] using ihφ σs
      · simpa [List.map] using ihψ σs
  | impI h ih =>
      exact .impI (by
        simpa [List.map] using ih σs)
  | impE hφψ hφ ihφψ ihφ =>
      exact .impE (ihφψ σs) (ihφ σs)
  | notI h ih =>
      exact .notI (by
        simpa [List.map, Mettapedia.Logic.HOL.subst] using ih σs)
  | notE hnot hφ ihnot ihφ =>
      exact .notE (ihnot σs) (ihφ σs)
  | allI h ih =>
      rename_i Γ₀ Δ₀ ρ body
      exact .allI (by
        simpa [subst_weakenHyps] using
          ih (Subst.lift (Base := Base) (Const := Const) (σ := ρ) σs))
  | allE t h ih =>
      simpa [Mettapedia.Logic.HOL.subst_instantiate] using
        (.allE (Mettapedia.Logic.HOL.subst σs t) (ih σs))
  | exI t h ih =>
      rename_i Γ₀ Δ₀ ρ body
      have ih' :
          ExtDerivation Const
            (Δ₀.map (Mettapedia.Logic.HOL.subst σs))
            (instantiate (Base := Base)
              (Mettapedia.Logic.HOL.subst σs t)
              (Mettapedia.Logic.HOL.subst
                (Subst.lift (Base := Base) (Const := Const) (σ := ρ) σs) body)) := by
        simpa [Mettapedia.Logic.HOL.subst_instantiate
          (Base := Base) (Const := Const) (σs := σs) (t := t) (u := body)] using
          ih σs
      exact .exI (Mettapedia.Logic.HOL.subst σs t) ih'
  | exE hex hbody ihex ihbody =>
      rename_i Γ₀ Δ₀ ρ body ψ
      refine .exE (ihex σs) ?_
      simpa [List.map, subst_weakenHyps, Mettapedia.Logic.HOL.subst_weaken,
        Mettapedia.Logic.HOL.subst] using
        ihbody (Subst.lift (Base := Base) (Const := Const) (σ := ρ) σs)
  | eqRefl t =>
      exact .eqRefl (Mettapedia.Logic.HOL.subst σs t)
  | eqSymm h ih =>
      exact .eqSymm (ih σs)
  | eqTrans htu huv ihtu ihuv =>
      exact .eqTrans (ihtu σs) (ihuv σs)
  | eqPropI hpq hqp ihpq ihqp =>
      exact .eqPropI (ihpq σs) (ihqp σs)
  | eqPropEL hpq ihpq =>
      exact .eqPropEL (ihpq σs)
  | eqPropER hpq ihpq =>
      exact .eqPropER (ihpq σs)
  | eqApp t h ih =>
      exact .eqApp (Mettapedia.Logic.HOL.subst σs t) (ih σs)
  | eqAppArg f h ih =>
      exact .eqAppArg (Mettapedia.Logic.HOL.subst σs f) (ih σs)
  | eqLam h ih =>
      rename_i Γ₀ Δ₀ ρ τ t u
      exact .eqLam (by
        simpa [subst_weakenHyps, Mettapedia.Logic.HOL.subst] using
          ih (Subst.lift (Base := Base) (Const := Const) (σ := ρ) σs))
  | funExt h ih =>
      rename_i Γ₀ Δ₀ ρ τ f g
      exact .funExt (by
        simpa [Mettapedia.Logic.HOL.subst, Mettapedia.Logic.HOL.subst_weaken,
          Subst.lift] using ih σs)
  | beta t u =>
      rename_i Γ₀ Δ₀ ρ τ
      simpa [Mettapedia.Logic.HOL.subst, Mettapedia.Logic.HOL.subst_instantiate] using
        (.beta (Mettapedia.Logic.HOL.subst σs t)
          (Mettapedia.Logic.HOL.subst
            (Subst.lift (Base := Base) (Const := Const) (σ := ρ) σs) u))
  | eta f =>
      rename_i Γ₀ Δ₀ ρ τ
      simpa [Mettapedia.Logic.HOL.subst, Mettapedia.Logic.HOL.subst_weaken] using
        (.eta (Mettapedia.Logic.HOL.subst σs f))

/-- Move one distinguished assumption from the middle of an append-context to
the head. Since extended derivations use membership hypotheses, this is just
antecedent monotonicity specialized to the exchange shape needed by local cut
arguments. -/
theorem cons_append_of_append_cons
    {Γ : Ctx Base}
    {ΓHead ΓTail : List (Formula Const Γ)}
    {χ θ : Formula Const Γ}
    (hDer : ExtDerivation Const (ΓHead ++ χ :: ΓTail) θ) :
    ExtDerivation Const (χ :: ΓHead ++ ΓTail) θ :=
  ExtDerivation.mono
    (Const := Const)
    (Δ := ΓHead ++ χ :: ΓTail)
    (Δ' := χ :: ΓHead ++ ΓTail)
    (φ := θ)
    (by
      intro ξ hξ
      simp [List.mem_append, List.mem_cons] at hξ ⊢
      tauto)
    hDer

/-- Move one distinguished assumption from the head back into the middle of an
append-context. This inverse transport keeps split-context principal cut
lemmas usable inside larger finite derivations. -/
theorem append_cons_of_cons_append
    {Γ : Ctx Base}
    {ΓHead ΓTail : List (Formula Const Γ)}
    {χ θ : Formula Const Γ}
    (hDer : ExtDerivation Const (χ :: ΓHead ++ ΓTail) θ) :
    ExtDerivation Const (ΓHead ++ χ :: ΓTail) θ :=
  ExtDerivation.mono
    (Const := Const)
    (Δ := χ :: ΓHead ++ ΓTail)
    (Δ' := ΓHead ++ χ :: ΓTail)
    (φ := θ)
    (by
      intro ξ hξ
      simp [List.mem_append, List.mem_cons] at hξ ⊢
      tauto)
    hDer

end ExtDerivation

/-- Abstracting a fresh constant out of its own closed instance recovers the
generic one-variable body. This is the reusable syntactic core behind the
fresh-constant universal generalization step. -/
theorem abstractConstAt_instantiate_const_self
    {σ : Ty Base} (c : Const σ) (φ : Formula Const [σ])
    (hφno : NoConstOccurrence c φ) :
    abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c []
      (instantiate (Base := Base) (.const c) φ) = φ := by
  have hInsertCancel :
      ∀ {τ : Ty Base} (t : Term Const [σ] τ),
        instantiate (Base := Base) (.var (.vz : Var [σ] σ))
          (rename
            (fun {τ : Ty Base} (v : Var [σ] τ) =>
              insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v) t) = t := by
    intro τ t
    unfold instantiate
    calc
      subst
          (Subst.single (Base := Base) (Const := Const)
            (.var (.vz : Var [σ] σ)))
          (rename
            (fun {τ : Ty Base} (v : Var [σ] τ) =>
              insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v) t)
          =
        subst
          (fun {τ : Ty Base} (v : Var [σ] τ) =>
            (Subst.single (Base := Base) (Const := Const)
              (.var (.vz : Var [σ] σ)))
              (insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)) t := by
            simpa using
              (subst_rename (Base := Base) (Const := Const)
                (σs := Subst.single (Base := Base) (Const := Const)
                  (.var (.vz : Var [σ] σ)))
                (ρ := fun {τ : Ty Base} (v : Var [σ] τ) =>
                  insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)
                t)
        _ = subst (Subst.id (Base := Base) (Const := Const) (Γ := [σ])) t := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = t := subst_id (Base := Base) (Const := Const) t
  have hConstSelf :
      abstractConstAt (Base := Base) (Γ := []) c [] (.const c) =
        (.var (.vz : Var [σ] σ)) := by
    simp only [abstractConstAt, varAtDepth]
    split
    · rfl
    · contradiction
  calc
    abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c []
        (instantiate (Base := Base) (.const c) φ)
        =
          instantiate (Base := Base)
            (abstractConstAt (Base := Base) (Γ := []) c [] (.const c))
            (abstractConstAt (Base := Base) (Γ := []) c [σ] φ) := by
            exact
              (abstractConstAt_instantiate (Base := Base) (Γ := []) (c := c) []
                (.const c) φ)
    _ = instantiate (Base := Base) (.var (.vz : Var [σ] σ))
          (rename
            (fun {τ : Ty Base} (v : Var [σ] τ) =>
              insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v) φ) := by
          rw [hConstSelf]
          rw [abstractConstAt_noOccurrence
            (Base := Base) (Γ := []) (c := c) [σ] φ hφno]
          rfl
    _ = φ := hInsertCancel φ

theorem abstractConstAt_closed_imp
    {σ : Ty Base} (c : Const σ) (φ ψ : ClosedFormula Const) :
    abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] (.imp φ ψ) =
      .imp
        (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] φ)
        (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) := by
  simp only [abstractConstAt]

theorem abstractConstAt_closed_ex
    {σ ρ : Ty Base} (c : Const σ) (φ : Formula Const [ρ]) :
    abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] (.ex φ) =
      .ex (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [ρ] φ) := by
  simp only [abstractConstAt]

theorem abstractConstAt_closed_all
    {σ ρ : Ty Base} (c : Const σ) (φ : Formula Const [ρ]) :
    abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] (.all φ) =
      .all (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [ρ] φ) := by
  simp only [abstractConstAt]

namespace ClosedTheorySet

/-- Henkin witness data for a closed theory-set: existential formulas have
closed-term witnesses, and failed universal formulas have closed-term
counterexamples. This is precisely the remaining data needed to upgrade a prime
separating closed theory-set into a canonical closed world. -/
structure HenkinWitnessData (U : ClosedTheorySet Const) : Prop where
  exists_witness :
    ∀ {σ : Ty Base} {φ : Formula Const [σ]},
      (.ex φ : ClosedFormula Const) ∈ U →
        ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∈ U
  all_counterexample :
    ∀ {σ : Ty Base} {φ : Formula Const [σ]},
      (.all φ : ClosedFormula Const) ∉ U →
        ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∉ U

/-- Constant Henkin witness data is the sharper invariant produced by the usual
fresh-constant construction: every existential trigger and failed universal
trigger is handled by a closed constant instance. -/
structure ConstantHenkinWitnessData (U : ClosedTheorySet Const) : Prop where
  exists_const_witness :
    ∀ {σ : Ty Base} {φ : Formula Const [σ]},
      (.ex φ : ClosedFormula Const) ∈ U →
        ∃ c : Const σ, instantiate (Base := Base) (.const c) φ ∈ U
  all_const_counterexample :
    ∀ {σ : Ty Base} {φ : Formula Const [σ]},
      (.all φ : ClosedFormula Const) ∉ U →
        ∃ c : Const σ, instantiate (Base := Base) (.const c) φ ∉ U

/-- Fresh-constant implication data is the local proof obligation generated by
the Henkin construction. If these implications lie in a deductively closed
closed theory-set, then existential triggers have constant witnesses and failed
universal triggers have constant counterexamples. -/
structure ConstantHenkinImplicationData (U : ClosedTheorySet Const) : Type (max u v) where
  exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ
  allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ
  ex_imp :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]),
      (.imp (.ex φ : ClosedFormula Const)
        (instantiate (Base := Base) (.const (exConst φ)) φ) :
          ClosedFormula Const) ∈ U
  all_imp :
    ∀ {σ : Ty Base} (φ : Formula Const [σ]),
      (.imp (instantiate (Base := Base) (.const (allConst φ)) φ)
        (.all φ : ClosedFormula Const) : ClosedFormula Const) ∈ U

/-- The existential Henkin implication generated by a chosen witness constant. -/
def constantHenkinExImplication
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ]) : ClosedFormula Const :=
  .imp (.ex φ : ClosedFormula Const)
    (instantiate (Base := Base) (.const (exConst φ)) φ)

/-- The universal Henkin implication generated by a chosen counterexample constant. -/
def constantHenkinAllImplication
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ]) : ClosedFormula Const :=
  .imp (instantiate (Base := Base) (.const (allConst φ)) φ)
    (.all φ : ClosedFormula Const)

@[simp] theorem weakenClosedFormulaToCtx_constantHenkinExImplication
    (Γ : Ctx Base)
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ]) :
    weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ
        (constantHenkinExImplication (Base := Base) (Const := Const) exConst φ) =
      .imp
        (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ
          (.ex φ : ClosedFormula Const))
        (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ
          (instantiate (Base := Base) (.const (exConst φ)) φ)) := by
  simp [constantHenkinExImplication]

@[simp] theorem weakenClosedFormulaToCtx_constantHenkinAllImplication
    (Γ : Ctx Base)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ]) :
    weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ
        (constantHenkinAllImplication (Base := Base) (Const := Const) allConst φ) =
      .imp
        (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ
          (instantiate (Base := Base) (.const (allConst φ)) φ))
        (weakenClosedFormulaToCtx (Base := Base) (Const := Const) Γ
          (.all φ : ClosedFormula Const)) := by
  simp [constantHenkinAllImplication]

/-- The one-binder body obtained after abstracting the chosen eigenconstant
under a quantifier whose original body was `φ`. The original bound variable is
kept at the head of the context; the newly abstracted eigenvariable sits behind
it. -/
def constantHenkinAbstractedBody
    {σ : Ty Base} (φ : Formula Const [σ]) : Formula Const (σ :: [σ]) :=
  rename
    (fun {τ : Ty Base} (v : Var [σ] τ) =>
      insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)
    φ

theorem abstractConstAt_constantHenkinExImplication
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ])
    (hφno : NoConstOccurrence (exConst φ) φ) :
    abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (exConst φ) []
        (constantHenkinExImplication (Base := Base) (Const := Const) exConst φ) =
      .imp (.ex (constantHenkinAbstractedBody (Base := Base) (Const := Const) φ))
        φ := by
  unfold constantHenkinExImplication constantHenkinAbstractedBody
  change abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (exConst φ) []
      (.imp (.ex φ : ClosedFormula Const)
        (instantiate (Base := Base) (.const (exConst φ)) φ)) =
    .imp (.ex
        (rename
          (fun {τ : Ty Base} (v : Var [σ] τ) =>
            insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)
          φ))
      φ
  rw [abstractConstAt_closed_imp]
  have hEx :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (exConst φ) []
        (.ex φ : ClosedFormula Const) =
      .ex
        (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (exConst φ) [σ] φ) :=
    abstractConstAt_closed_ex (Base := Base) (Const := Const) (c := exConst φ) φ
  have hNo :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (exConst φ) [σ] φ =
        rename
          (fun {τ : Ty Base} (v : Var [σ] τ) =>
            insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)
          φ := by
    exact abstractConstAt_noOccurrence
      (Base := Base) (Γ := []) (c := exConst φ) [σ] φ hφno
  have hInst :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (exConst φ) []
        (instantiate (Base := Base) (.const (exConst φ)) φ) = φ :=
    abstractConstAt_instantiate_const_self
      (Base := Base) (Const := Const) (exConst φ) φ hφno
  rw [hEx, hNo, hInst]
  rfl

theorem abstractConstAt_constantHenkinAllImplication
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ])
    (hφno : NoConstOccurrence (allConst φ) φ) :
    abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (allConst φ) []
        (constantHenkinAllImplication (Base := Base) (Const := Const) allConst φ) =
      .imp φ (.all (constantHenkinAbstractedBody (Base := Base) (Const := Const) φ)) := by
  unfold constantHenkinAllImplication constantHenkinAbstractedBody
  change abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (allConst φ) []
      (.imp (instantiate (Base := Base) (.const (allConst φ)) φ)
        (.all φ : ClosedFormula Const)) =
    .imp φ
      (.all
        (rename
          (fun {τ : Ty Base} (v : Var [σ] τ) =>
            insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)
          φ))
  rw [abstractConstAt_closed_imp]
  have hInst :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (allConst φ) []
        (instantiate (Base := Base) (.const (allConst φ)) φ) = φ :=
    abstractConstAt_instantiate_const_self
      (Base := Base) (Const := Const) (allConst φ) φ hφno
  have hAll :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (allConst φ) []
        (.all φ : ClosedFormula Const) =
      .all
        (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (allConst φ) [σ] φ) :=
    abstractConstAt_closed_all (Base := Base) (Const := Const) (c := allConst φ) φ
  have hNo :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) (allConst φ) [σ] φ =
        rename
          (fun {τ : Ty Base} (v : Var [σ] τ) =>
            insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)
          φ := by
    exact abstractConstAt_noOccurrence
      (Base := Base) (Γ := []) (c := allConst φ) [σ] φ hφno
  rw [hInst, hAll, hNo]
  rfl

/-- The closed theory-set freely generated by the fresh-constant Henkin
implication scheme. The canonical construction should prime-extend a theory
containing this set, after which `constantHenkinImplicationDataOfContainsTheorySet`
extracts the implication data consumed by the world construction. -/
def constantHenkinImplicationTheorySet
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) :
    ClosedTheorySet Const :=
  fun θ =>
    (∃ (σ : Ty Base) (φ : Formula Const [σ]),
      θ = constantHenkinExImplication (Base := Base) (Const := Const) exConst φ) ∨
    (∃ (σ : Ty Base) (φ : Formula Const [σ]),
      θ = constantHenkinAllImplication (Base := Base) (Const := Const) allConst φ)

/-- Adjoin the generated fresh-constant Henkin implication scheme to a closed
theory-set. This is the theory that should be prime-extended in the canonical
Henkin construction. -/
def withConstantHenkinImplications
    (T : ClosedTheorySet Const)
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) :
    ClosedTheorySet Const :=
  fun θ =>
    θ ∈ T ∨
      θ ∈ constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst

theorem mem_withConstantHenkinImplications_of_base
    {T : ClosedTheorySet Const}
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {θ : ClosedFormula Const}
    (hθ : θ ∈ T) :
    θ ∈ withConstantHenkinImplications
      (Base := Base) (Const := Const) T exConst allConst :=
  Or.inl hθ

theorem mem_withConstantHenkinImplications_of_implication
    {T : ClosedTheorySet Const}
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {θ : ClosedFormula Const}
    (hθ :
      θ ∈ constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst) :
    θ ∈ withConstantHenkinImplications
      (Base := Base) (Const := Const) T exConst allConst :=
  Or.inr hθ

theorem contains_constantHenkinImplicationTheorySet_of_withConstantHenkinImplications
    {T U : ClosedTheorySet Const}
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hExt :
      ∀ {θ : ClosedFormula Const},
        θ ∈ withConstantHenkinImplications
          (Base := Base) (Const := Const) T exConst allConst →
          θ ∈ U) :
    ∀ {θ : ClosedFormula Const},
      θ ∈ constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst →
        θ ∈ U := by
  intro θ hθ
  exact hExt
    (mem_withConstantHenkinImplications_of_implication
      (Base := Base) (Const := Const) (T := T) exConst allConst hθ)

/-- Eliminate a finite iterated implication inside a closed theory-set once all
of the finite antecedents are themselves theory-set provable. This is the
closed-theory-set analogue of repeatedly applying modus ponens to a deduction
theorem. -/
theorem provable_of_iterImp_provable
    {T : ClosedTheorySet Const}
    {Γ : ClosedTheory Const} {θ : ClosedFormula Const}
    (hImp :
      Provable (Const := Const) T
        (ClosedTheory.iterImp (Const := Const) Γ θ))
    (hΓ : ∀ ψ, ψ ∈ Γ → Provable (Const := Const) T ψ) :
    Provable (Const := Const) T θ := by
  induction Γ generalizing θ with
  | nil =>
      simpa [ClosedTheory.iterImp] using hImp
  | cons ψ Γ ih =>
      have hImpStep :
          Provable (Const := Const) T (.imp ψ θ) :=
        ih hImp (by
          intro ξ hξ
          exact hΓ ξ (by simp [hξ]))
      exact provable_mp
        (T := T)
        (φ := ψ)
        (ψ := θ)
        hImpStep
        (hΓ ψ (by simp))

/-- Replay a finite closed derivation over an ambient closed theory-set when
every finite hypothesis has already been proved from that theory-set. -/
theorem provable_of_closedTheoryProvable_of_provable_hyps
    {T : ClosedTheorySet Const}
    {Γ : ClosedTheory Const} {θ : ClosedFormula Const}
    (hΓ : ∀ ψ, ψ ∈ Γ → Provable (Const := Const) T ψ)
    (hDer : ClosedTheory.Provable (Const := Const) Γ θ) :
    Provable (Const := Const) T θ := by
  have hIterDer :
      ClosedTheory.Provable (Const := Const) []
        (ClosedTheory.iterImp (Const := Const) Γ θ) :=
    ClosedTheory.provable_iterImp (Const := Const) hDer
  have hIterSet :
      Provable (Const := Const) T
        (ClosedTheory.iterImp (Const := Const) Γ θ) :=
    provable_of_closedTheory
      (Const := Const) (T := T) (Δ := [])
      (hΔ := by intro ξ hξ; cases hξ)
      hIterDer
  exact provable_of_iterImp_provable
    (Const := Const) (T := T) hIterSet hΓ

theorem split_withConstantHenkinImplications_support
    {T : ClosedTheorySet Const}
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {Γ : ClosedTheory Const}
    (hΓ :
      ∀ ψ, ψ ∈ Γ →
        ψ ∈ withConstantHenkinImplications
          (Base := Base) (Const := Const) T exConst allConst) :
    ∃ ΓBase ΓHenkin : ClosedTheory Const,
      (∀ ψ, ψ ∈ ΓBase → ψ ∈ T) ∧
      (∀ ψ, ψ ∈ ΓHenkin →
        ψ ∈ constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst) ∧
      (∀ {ψ : ClosedFormula Const}, ψ ∈ Γ → ψ ∈ ΓBase ++ ΓHenkin) := by
  induction Γ with
  | nil =>
      refine ⟨[], [], ?_, ?_, ?_⟩
      · intro ψ hψ
        cases hψ
      · intro ψ hψ
        cases hψ
      · intro ψ hψ
        cases hψ
  | cons γ Γ ih =>
      have hTail :
          ∀ ψ, ψ ∈ Γ →
            ψ ∈ withConstantHenkinImplications
              (Base := Base) (Const := Const) T exConst allConst := by
        intro ψ hψ
        exact hΓ ψ (by simp [hψ])
      rcases ih hTail with ⟨ΓBase, ΓHenkin, hBase, hHenkin, hSub⟩
      have hHead :
          γ ∈ withConstantHenkinImplications
            (Base := Base) (Const := Const) T exConst allConst :=
        hΓ γ (by simp)
      rcases hHead with hγBase | hγHenkin
      · refine ⟨γ :: ΓBase, ΓHenkin, ?_, hHenkin, ?_⟩
        · intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact hγBase
          · exact hBase ψ hψ
        · intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_append.mpr (Or.inl (by simp))
          · rcases List.mem_append.mp (hSub hψ) with hψBase | hψHenkin
            · exact List.mem_append.mpr (Or.inl (by simp [hψBase]))
            · exact List.mem_append.mpr (Or.inr hψHenkin)
      · refine ⟨ΓBase, γ :: ΓHenkin, hBase, ?_, ?_⟩
        · intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact hγHenkin
          · exact hHenkin ψ hψ
        · intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_append.mpr (Or.inr (by simp))
          · rcases List.mem_append.mp (hSub hψ) with hψBase | hψHenkin
            · exact List.mem_append.mpr (Or.inl hψBase)
            · exact List.mem_append.mpr (Or.inr (by simp [hψHenkin]))

theorem provable_withConstantHenkinImplications_iff_exists_split
    {T : ClosedTheorySet Const}
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {θ : ClosedFormula Const} :
    Provable (Const := Const)
        (withConstantHenkinImplications
          (Base := Base) (Const := Const) T exConst allConst)
        θ ↔
      ∃ ΓBase ΓHenkin : ClosedTheory Const,
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ T) ∧
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) ∧
        ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ := by
  constructor
  · rintro ⟨Γ, hΓ, hDer⟩
    rcases split_withConstantHenkinImplications_support
        (Base := Base) (Const := Const) (T := T) exConst allConst hΓ with
      ⟨ΓBase, ΓHenkin, hBase, hHenkin, hSub⟩
    exact ⟨ΓBase, ΓHenkin, hBase, hHenkin,
      ClosedTheory.Provable.mono
        (Const := Const) (Δ := Γ) (Δ' := ΓBase ++ ΓHenkin)
        hSub hDer⟩
  · rintro ⟨ΓBase, ΓHenkin, hBase, hHenkin, hDer⟩
    refine ⟨ΓBase ++ ΓHenkin, ?_, hDer⟩
    intro ψ hψ
    rcases List.mem_append.mp hψ with hψBase | hψHenkin
    · exact Or.inl (hBase ψ hψBase)
    · exact Or.inr (hHenkin ψ hψHenkin)

/-- A constant does not occur in any member of a finite closed theory. This is
the finite-context freshness invariant needed by eigenconstant elimination. -/
def NoConstOccurrenceInClosedTheory
    {σ : Ty Base} (c : Const σ) (Γ : ClosedTheory Const) : Prop :=
  ∀ {θ : ClosedFormula Const}, θ ∈ Γ → NoConstOccurrence c θ

/-- A constant does not occur in any member of a closed theory-set. -/
def NoConstOccurrenceInClosedTheorySet
    {σ : Ty Base} (c : Const σ) (T : ClosedTheorySet Const) : Prop :=
  ∀ {θ : ClosedFormula Const}, θ ∈ T → NoConstOccurrence c θ

/-- A sigma-packaged constant does not occur in a term. This lets freshness
statements quantify over the eigenconstant selected by a generated implication
without exposing its type at every call site. -/
def NoSigmaConstOccurrence
    (c : Sigma Const) {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) : Prop :=
  match c with
  | ⟨_, c⟩ => NoConstOccurrence c t

/-- Sigma-packaged no-occurrence over a finite closed theory. -/
def NoSigmaConstOccurrenceInClosedTheory
    (c : Sigma Const) (Γ : ClosedTheory Const) : Prop :=
  ∀ {θ : ClosedFormula Const}, θ ∈ Γ → NoSigmaConstOccurrence c θ

/-- Sigma-packaged no-occurrence over a closed theory-set. -/
def NoSigmaConstOccurrenceInClosedTheorySet
    (c : Sigma Const) (T : ClosedTheorySet Const) : Prop :=
  ∀ {θ : ClosedFormula Const}, θ ∈ T → NoSigmaConstOccurrence c θ

theorem noConstOccurrenceInClosedTheory_nil
    {σ : Ty Base} (c : Const σ) :
    NoConstOccurrenceInClosedTheory (Const := Const) c [] := by
  intro θ hθ
  cases hθ

theorem noConstOccurrenceInClosedTheory_cons_iff
    {σ : Ty Base} (c : Const σ)
    (θ : ClosedFormula Const) (Γ : ClosedTheory Const) :
    NoConstOccurrenceInClosedTheory (Const := Const) c (θ :: Γ) ↔
      NoConstOccurrence c θ ∧
        NoConstOccurrenceInClosedTheory (Const := Const) c Γ := by
  constructor
  · intro h
    refine ⟨h (by simp), ?_⟩
    intro ψ hψ
    exact h (by simp [hψ])
  · rintro ⟨hθ, hΓ⟩ ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hθ
    · exact hΓ hψ

theorem noConstOccurrenceInClosedTheory_append_iff
    {σ : Ty Base} (c : Const σ)
    (Γ Δ : ClosedTheory Const) :
    NoConstOccurrenceInClosedTheory (Const := Const) c (Γ ++ Δ) ↔
      NoConstOccurrenceInClosedTheory (Const := Const) c Γ ∧
        NoConstOccurrenceInClosedTheory (Const := Const) c Δ := by
  constructor
  · intro h
    constructor
    · intro θ hθ
      exact h (List.mem_append.mpr (Or.inl hθ))
    · intro θ hθ
      exact h (List.mem_append.mpr (Or.inr hθ))
  · rintro ⟨hΓ, hΔ⟩ θ hθ
    rcases List.mem_append.mp hθ with hθ | hθ
    · exact hΓ hθ
    · exact hΔ hθ

theorem noConstOccurrenceIn_weakenClosedTheoryToCtx
    {σ : Ty Base} (c : Const σ) (Γ : Ctx Base)
    {Δ : ClosedTheory Const}
    (hΔ : NoConstOccurrenceInClosedTheory (Const := Const) c Δ) :
    ∀ {φ : Formula Const Γ},
      φ ∈ weakenClosedTheoryToCtx (Base := Base) (Const := Const) Γ Δ →
        NoConstOccurrence c φ := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨ψ, hψ, rfl⟩
  exact noConstOccurrence_weakenClosedFormulaToCtx
    (Base := Base) (Const := Const) c Γ (hΔ hψ)

theorem noConstOccurrenceInClosedTheory_of_subset
    {σ : Ty Base} {c : Const σ}
    {Γ Δ : ClosedTheory Const}
    (hΔ : NoConstOccurrenceInClosedTheory (Const := Const) c Δ)
    (hSub : ∀ {θ : ClosedFormula Const}, θ ∈ Γ → θ ∈ Δ) :
    NoConstOccurrenceInClosedTheory (Const := Const) c Γ := by
  intro θ hθ
  exact hΔ (hSub hθ)

theorem noConstOccurrenceInClosedTheory_of_mem_set
    {σ : Ty Base} {c : Const σ}
    {T : ClosedTheorySet Const} {Γ : ClosedTheory Const}
    (hT : NoConstOccurrenceInClosedTheorySet (Const := Const) c T)
    (hΓ : ∀ {θ : ClosedFormula Const}, θ ∈ Γ → θ ∈ T) :
    NoConstOccurrenceInClosedTheory (Const := Const) c Γ := by
  intro θ hθ
  exact hT (hΓ hθ)

theorem noSigmaConstOccurrence_mk_iff
    {σ : Ty Base} (c : Const σ)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    NoSigmaConstOccurrence (Const := Const) ⟨σ, c⟩ t ↔
      NoConstOccurrence c t :=
  Iff.rfl

theorem noSigmaConstOccurrenceInClosedTheory_mk_iff
    {σ : Ty Base} (c : Const σ) (Γ : ClosedTheory Const) :
    NoSigmaConstOccurrenceInClosedTheory (Const := Const) ⟨σ, c⟩ Γ ↔
      NoConstOccurrenceInClosedTheory (Const := Const) c Γ :=
  Iff.rfl

theorem noSigmaConstOccurrenceInClosedTheorySet_mk_iff
    {σ : Ty Base} (c : Const σ) (T : ClosedTheorySet Const) :
    NoSigmaConstOccurrenceInClosedTheorySet (Const := Const) ⟨σ, c⟩ T ↔
      NoConstOccurrenceInClosedTheorySet (Const := Const) c T :=
  Iff.rfl

theorem noSigmaConstOccurrenceInClosedTheory_append_iff
    (c : Sigma Const) (Γ Δ : ClosedTheory Const) :
    NoSigmaConstOccurrenceInClosedTheory (Const := Const) c (Γ ++ Δ) ↔
      NoSigmaConstOccurrenceInClosedTheory (Const := Const) c Γ ∧
        NoSigmaConstOccurrenceInClosedTheory (Const := Const) c Δ := by
  rcases c with ⟨σ, c⟩
  exact noConstOccurrenceInClosedTheory_append_iff
    (Const := Const) c Γ Δ

theorem extDerivation_weaken_closedTheory
    {Γ : ClosedTheory Const} {θ : ClosedFormula Const}
    {σ : Ty Base}
    (hDer : ClosedTheory.Provable (Const := Const) Γ θ) :
  ExtDerivation Const
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ)
      (weaken (Base := Base) (Const := Const) (σ := σ) θ) := by
  change ExtDerivation Const
    (List.map
      (fun θ : ClosedFormula Const =>
        rename (Rename.weaken (Base := Base) (Γ := []) (σ := σ)) θ) Γ)
    (rename (Rename.weaken (Base := Base) (Γ := []) (σ := σ)) θ)
  exact
    ExtDerivation.rename
      (Base := Base) (Const := Const)
      (ρ := Rename.weaken (Base := Base) (Γ := []) (σ := σ))
      hDer

theorem extDerivation_abstractConstAt_closedTheory
    {Γ : ClosedTheory Const} {θ : ClosedFormula Const}
    {σ : Ty Base} (c : Const σ)
    (hDer : ClosedTheory.Provable (Const := Const) Γ θ) :
    ExtDerivation Const
      (Γ.map (fun ψ =>
        abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ))
      (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] θ) :=
  ExtDerivation.abstractConstAt_deriv
    (Base := Base) (Const := Const) (Γ := []) (Ξ := []) c hDer

theorem abstractConstAt_closedTheory_eq_weakenHyps
    {σ : Ty Base} (c : Const σ)
    {Γ : ClosedTheory Const}
    (hΓno : NoConstOccurrenceInClosedTheory (Const := Const) c Γ) :
    Γ.map (fun ψ =>
        abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
      weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ := by
  induction Γ with
  | nil =>
      simp [weakenHyps]
  | cons ψ Γ ih =>
      have hψ : NoConstOccurrence c ψ := hΓno (by simp)
      have hΓ : NoConstOccurrenceInClosedTheory (Const := Const) c Γ := by
        intro χ hχ
        exact hΓno (by simp [hχ])
      have hHead :
          abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ =
            weaken (Base := Base) (Const := Const) (σ := σ) ψ := by
        simpa [insertRen, weaken] using
          abstractConstAt_noOccurrence
            (Base := Base) (Γ := []) (c := c) [] ψ hψ
      have hTail :
          Γ.map (fun ψ =>
              abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
            weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ :=
        ih hΓ
      change
        abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ ::
            Γ.map (fun ψ =>
              abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
          weaken (Base := Base) (Const := Const) (σ := σ) ψ ::
            weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ
      rw [hHead, hTail]
      rfl

theorem extDerivation_abstractConstAt_weaken_of_noOccurrence
    {Γ : ClosedTheory Const} {θ : ClosedFormula Const}
    {σ : Ty Base} {c : Const σ}
    (hΓno : NoConstOccurrenceInClosedTheory (Const := Const) c Γ)
    (hθno : NoConstOccurrence c θ)
    (hDer : ClosedTheory.Provable (Const := Const) Γ θ) :
    ExtDerivation Const
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ)
      (weaken (Base := Base) (Const := Const) (σ := σ) θ) := by
  have hAbs :
      ExtDerivation Const
        (Γ.map (fun ψ =>
          abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ))
        (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] θ) :=
    extDerivation_abstractConstAt_closedTheory
      (Base := Base) (Const := Const) c hDer
  have hΓeq :
      Γ.map (fun ψ =>
          abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
        weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ :=
    abstractConstAt_closedTheory_eq_weakenHyps
      (Base := Base) (Const := Const) c hΓno
  have hθeq :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] θ =
        weaken (Base := Base) (Const := Const) (σ := σ) θ := by
    simpa [insertRen, weaken] using
      abstractConstAt_noOccurrence
        (Base := Base) (Γ := []) (c := c) [] θ hθno
  rw [hΓeq] at hAbs
  simpa [hθeq] using hAbs

theorem closedTheoryProvable_all_of_const_instance_append
    {ΓBase ΓTail : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    (hBaseNo :
      NoConstOccurrenceInClosedTheory (Const := Const) c ΓBase)
    (hTailNo :
      NoConstOccurrenceInClosedTheory (Const := Const) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail)
      (instantiate (Base := Base) (.const c) φ)) :
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail) (.all φ) :=
  Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTheory.Provable.all_of_const_instance
    (Base := Base) (Const := Const)
    (Δ := ΓBase ++ ΓTail)
    (c := c)
    (hΔno := by
      intro ψ hψ
      exact
        ((noConstOccurrenceInClosedTheory_append_iff
          (Const := Const) c ΓBase ΓTail).2 ⟨hBaseNo, hTailNo⟩) hψ)
    hφno hInst

theorem closedTheoryProvable_all_of_freshHenkinAllAntecedent
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {ΓBase ΓTail : ClosedTheory Const}
    {σ : Ty Base} (φ : Formula Const [σ])
    (hBaseNo :
      NoConstOccurrenceInClosedTheory (Const := Const) (allConst φ) ΓBase)
    (hTailNo :
      NoConstOccurrenceInClosedTheory (Const := Const) (allConst φ) ΓTail)
    (hφno : NoConstOccurrence (allConst φ) φ)
    (hInst : ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail)
      (instantiate (Base := Base) (.const (allConst φ)) φ)) :
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail) (.all φ) :=
  closedTheoryProvable_all_of_const_instance_append
    (Base := Base) (Const := Const)
    (ΓBase := ΓBase) (ΓTail := ΓTail)
    hBaseNo hTailNo hφno hInst

/-- Degenerate existential Henkin implications are theorematic when the chosen
fresh instance is itself fresh-constant-free. In that case the body could not
have used its bound variable except as a weakening of the closed instance, so
ordinary existential elimination derives the instance. -/
theorem closedTheoryProvable_exImplication_of_instance_noConstOccurrence
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    (hInstNo :
      NoConstOccurrence c (instantiate (Base := Base) (.const c) φ)) :
    ClosedTheory.Provable (Const := Const) []
      (.imp (.ex φ : ClosedFormula Const)
        (instantiate (Base := Base) (.const c) φ)) := by
  let θ : ClosedFormula Const := instantiate (Base := Base) (.const c) φ
  have hφeq :
      φ = weaken (Base := Base) (Const := Const) (σ := σ) θ :=
    weaken_of_instantiate_const_noOccurrence
      (Base := Base) (Const := Const) c φ θ rfl hInstNo
  apply ExtDerivation.impI
  exact ExtDerivation.exE
    (φ := φ) (ψ := θ)
    (.hyp (by simp))
    (by
      have hHyp :
          ExtDerivation Const
            (φ ::
              weakenHyps (Base := Base) (Const := Const) (σ := σ)
                [(.ex φ : ClosedFormula Const)])
            φ :=
        ExtDerivation.hyp
          (Const := Const)
          (Δ := φ ::
            weakenHyps (Base := Base) (Const := Const) (σ := σ)
              [(.ex φ : ClosedFormula Const)])
          (φ := φ)
          (by simp)
      exact
        Eq.ndrec
          (motive := fun η =>
            ExtDerivation Const
              (φ ::
                weakenHyps (Base := Base) (Const := Const) (σ := σ)
                  [(.ex φ : ClosedFormula Const)])
              η)
          hHyp hφeq)

/-- Degenerate universal Henkin implications are theorematic when the fresh
instance is fresh-constant-free. The same weakening identity lets universal
introduction rebuild the quantified formula from the closed instance. -/
theorem closedTheoryProvable_allImplication_of_instance_noConstOccurrence
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    (hInstNo :
      NoConstOccurrence c (instantiate (Base := Base) (.const c) φ)) :
    ClosedTheory.Provable (Const := Const) []
      (.imp (instantiate (Base := Base) (.const c) φ)
        (.all φ : ClosedFormula Const)) := by
  let θ : ClosedFormula Const := instantiate (Base := Base) (.const c) φ
  have hφeq :
      φ = weaken (Base := Base) (Const := Const) (σ := σ) θ :=
    weaken_of_instantiate_const_noOccurrence
      (Base := Base) (Const := Const) c φ θ rfl hInstNo
  apply ExtDerivation.impI
  apply ExtDerivation.allI
  change
    ExtDerivation Const
      (weakenHyps (Base := Base) (Const := Const) (σ := σ) [θ]) φ
  have hHyp :
      ExtDerivation Const
        (weakenHyps (Base := Base) (Const := Const) (σ := σ) [θ])
        (weaken (Base := Base) (Const := Const) (σ := σ) θ) :=
    ExtDerivation.hyp
      (Const := Const)
      (Δ := weakenHyps (Base := Base) (Const := Const) (σ := σ) [θ])
      (φ := weaken (Base := Base) (Const := Const) (σ := σ) θ)
      (by simp [weakenHyps])
  exact
    Eq.ndrec
      (motive := fun η =>
        ExtDerivation Const
          (weakenHyps (Base := Base) (Const := Const) (σ := σ) [θ]) η)
      hHyp hφeq.symm

theorem closedTheoryProvable_constantHenkinExImplication_of_instance_noConstOccurrence
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ])
    (hInstNo :
      NoConstOccurrence (exConst φ)
        (instantiate (Base := Base) (.const (exConst φ)) φ)) :
    ClosedTheory.Provable (Const := Const) []
      (constantHenkinExImplication (Base := Base) (Const := Const) exConst φ) := by
  simpa [constantHenkinExImplication] using
    closedTheoryProvable_exImplication_of_instance_noConstOccurrence
      (Base := Base) (Const := Const) (φ := φ) (c := exConst φ) hInstNo

theorem closedTheoryProvable_constantHenkinAllImplication_of_instance_noConstOccurrence
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ])
    (hInstNo :
      NoConstOccurrence (allConst φ)
        (instantiate (Base := Base) (.const (allConst φ)) φ)) :
    ClosedTheory.Provable (Const := Const) []
      (constantHenkinAllImplication (Base := Base) (Const := Const) allConst φ) := by
  simpa [constantHenkinAllImplication] using
    closedTheoryProvable_allImplication_of_instance_noConstOccurrence
      (Base := Base) (Const := Const) (φ := φ) (c := allConst φ) hInstNo

/-- Move one distinguished finite closed assumption from the middle of an
append-context to the head. `ExtDerivation` hypotheses are membership-based, so
this is ordinary antecedent monotonicity rather than an added exchange rule. -/
theorem closedTheoryProvable_cons_append_of_append_cons
    {ΓHead ΓTail : ClosedTheory Const}
    {χ θ : ClosedFormula Const}
    (hDer : ClosedTheory.Provable (Const := Const) (ΓHead ++ χ :: ΓTail) θ) :
    ClosedTheory.Provable (Const := Const) (χ :: ΓHead ++ ΓTail) θ :=
  ExtDerivation.cons_append_of_append_cons
    (Base := Base) (Const := Const) hDer

/-- Move one distinguished finite closed assumption from the head back into the
middle of an append-context. This is the inverse transport needed when a local
principal-cut lemma is applied inside a split finite proof state. -/
theorem closedTheoryProvable_append_cons_of_cons_append
    {ΓHead ΓTail : ClosedTheory Const}
    {χ θ : ClosedFormula Const}
    (hDer : ClosedTheory.Provable (Const := Const) (χ :: ΓHead ++ ΓTail) θ) :
    ClosedTheory.Provable (Const := Const) (ΓHead ++ χ :: ΓTail) θ :=
  ExtDerivation.append_cons_of_cons_append
    (Base := Base) (Const := Const) hDer

/-- Replace a fresh closed instance assumption by the corresponding existential
assumption. This is the proof-theoretic kernel of the existential Henkin
principal case: after abstracting the fresh eigenconstant, existential
elimination supplies exactly the missing instance assumption. -/
theorem closedTheoryProvable_of_exists_of_fresh_instance_assumption
    {Γ : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    {θ : ClosedFormula Const}
    (hΓno : NoConstOccurrenceInClosedTheory (Const := Const) c Γ)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hDer : ClosedTheory.Provable (Const := Const)
      (instantiate (Base := Base) (.const c) φ :: Γ) θ) :
    ClosedTheory.Provable (Const := Const) ((.ex φ : ClosedFormula Const) :: Γ) θ := by
  have hAbs :
      ExtDerivation Const
        ((instantiate (Base := Base) (.const c) φ :: Γ).map
          (fun ψ =>
            abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ))
        (abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] θ) :=
    extDerivation_abstractConstAt_closedTheory
      (Base := Base) (Const := Const) c hDer
  have hCtx :
      (instantiate (Base := Base) (.const c) φ :: Γ).map
          (fun ψ =>
            abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
        φ :: weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ := by
    change
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c []
          (instantiate (Base := Base) (.const c) φ) ::
        Γ.map
          (fun ψ =>
            abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
      φ :: weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ
    rw [abstractConstAt_instantiate_const_self
      (Base := Base) (Const := Const) c φ hφno]
    rw [abstractConstAt_closedTheory_eq_weakenHyps
      (Base := Base) (Const := Const) c hΓno]
    rfl
  have hθeq :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] θ =
        weaken (Base := Base) (Const := Const) (σ := σ) θ := by
    simpa [insertRen, weaken] using
      abstractConstAt_noOccurrence
        (Base := Base) (Γ := []) (c := c) [] θ hθno
  rw [hCtx] at hAbs
  have hBodyBase :
      ExtDerivation Const
        (φ :: weakenHyps (Base := Base) (Const := Const) (σ := σ) Γ)
        (weaken (Base := Base) (Const := Const) (σ := σ) θ) := by
    simpa [hθeq] using hAbs
  have hBody :
      ExtDerivation Const
        (φ ::
          weakenHyps (Base := Base) (Const := Const) (σ := σ)
            ((.ex φ : ClosedFormula Const) :: Γ))
        (weaken (Base := Base) (Const := Const) (σ := σ) θ) := by
    refine ExtDerivation.mono (Const := Const) ?_ hBodyBase
    intro ξ hξ
    rw [List.mem_cons] at hξ ⊢
    rcases hξ with rfl | hξ
    · exact Or.inl rfl
    · exact Or.inr (by
        simp [weakenHyps] at hξ ⊢
        exact Or.inr hξ)
  exact ExtDerivation.exE
    (φ := φ) (ψ := θ)
    (.hyp (show (.ex φ : ClosedFormula Const) ∈ (.ex φ :: Γ) from by simp))
    hBody

/-- Principal existential Henkin cut. If a fresh instance would prove the target
and the existential antecedent is already derivable, then the target is
derivable without the generated existential Henkin implication. -/
theorem closedTheoryProvable_of_fresh_ex_principal_cut
    {Γ : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    {θ : ClosedFormula Const}
    (hΓno : NoConstOccurrenceInClosedTheory (Const := Const) c Γ)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hEx : ClosedTheory.Provable (Const := Const) Γ (.ex φ : ClosedFormula Const))
    (hUse : ClosedTheory.Provable (Const := Const)
      (instantiate (Base := Base) (.const c) φ :: Γ) θ) :
    ClosedTheory.Provable (Const := Const) Γ θ := by
  have hExToTheta :
      ClosedTheory.Provable (Const := Const) ((.ex φ : ClosedFormula Const) :: Γ) θ :=
    closedTheoryProvable_of_exists_of_fresh_instance_assumption
      (Base := Base) (Const := Const) hΓno hφno hθno hUse
  exact
    Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable.ext_hypSubst
      (Const := Const)
      (Δ := (.ex φ : ClosedFormula Const) :: Γ)
      (Δ' := Γ)
      (φ := θ)
      (by
        intro ξ hξ
        rw [List.mem_cons] at hξ
        rcases hξ with rfl | hξ
        · exact hEx
        · exact .hyp hξ)
      hExToTheta

/-- Append-context form of `closedTheoryProvable_of_fresh_ex_principal_cut`.
This matches the split finite Henkin proof state where the principal generated
implication occurs between original antecedents and the remaining Henkin tail. -/
theorem closedTheoryProvable_of_fresh_ex_principal_cut_append
    {ΓBase ΓTail : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    {θ : ClosedFormula Const}
    (hBaseNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓBase)
    (hTailNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hEx : ClosedTheory.Provable (Const := Const)
      (ΓBase ++ ΓTail) (.ex φ : ClosedFormula Const))
    (hUse : ClosedTheory.Provable (Const := Const)
      (ΓBase ++ instantiate (Base := Base) (.const c) φ :: ΓTail) θ) :
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail) θ :=
  closedTheoryProvable_of_fresh_ex_principal_cut
    (Base := Base) (Const := Const)
    ((noConstOccurrenceInClosedTheory_append_iff
      (Const := Const) c ΓBase ΓTail).2 ⟨hBaseNo, hTailNo⟩)
    hφno hθno hEx
    (closedTheoryProvable_cons_append_of_append_cons
      (Base := Base) (Const := Const)
      (ΓHead := ΓBase) (ΓTail := ΓTail)
      (χ := instantiate (Base := Base) (.const c) φ)
      (θ := θ) hUse)

/-- Cut-free principal existential branch packaged for the sequent calculus.
When a head `impL` on the generated existential Henkin implication exposes a
derivation of the existential antecedent and a continuation from the fresh
instance, the extended principal-cut lemma removes the fresh instance from the
closed split context. -/
theorem closedTheoryProvable_of_fresh_ex_principal_cut_derivable_append
    {ΓBase ΓTail : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    {θ : ClosedFormula Const}
    (hBaseNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓBase)
    (hTailNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hθno : NoConstOccurrence c θ)
    (hEx :
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable
        (Base := Base) (Const := Const)
        (ΓBase ++ ΓTail) (.ex φ : ClosedFormula Const))
    (hUse :
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable
        (Base := Base) (Const := Const)
        (ΓBase ++ instantiate (Base := Base) (.const c) φ :: ΓTail) θ) :
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail) θ :=
  closedTheoryProvable_of_fresh_ex_principal_cut_append
    (Base := Base) (Const := Const)
    hBaseNo hTailNo hφno hθno
    (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable.toExtDerivation hEx)
    (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable.toExtDerivation hUse)

/-- Principal universal Henkin cut. If the fresh instance is derivable, the
fresh-constant universal-introduction lemma derives the universal formula, so a
proof using the universal formula as its principal continuation can discharge
that continuation. -/
theorem closedTheoryProvable_of_fresh_all_principal_cut
    {Γ : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    {θ : ClosedFormula Const}
    (hΓno : NoConstOccurrenceInClosedTheory (Const := Const) c Γ)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := Const) Γ
      (instantiate (Base := Base) (.const c) φ))
    (hUse : ClosedTheory.Provable (Const := Const)
      ((.all φ : ClosedFormula Const) :: Γ) θ) :
    ClosedTheory.Provable (Const := Const) Γ θ := by
  have hAll : ClosedTheory.Provable (Const := Const) Γ (.all φ : ClosedFormula Const) :=
    closedTheoryProvable_all_of_const_instance_append
      (Base := Base) (Const := Const)
      (ΓBase := []) (ΓTail := Γ)
      (noConstOccurrenceInClosedTheory_nil (Base := Base) (Const := Const) c)
      hΓno hφno
      (by simpa using hInst)
  exact
    Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable.ext_hypSubst
      (Const := Const)
      (Δ := (.all φ : ClosedFormula Const) :: Γ)
      (Δ' := Γ)
      (φ := θ)
      (by
        intro ξ hξ
        rw [List.mem_cons] at hξ
        rcases hξ with rfl | hξ
        · exact hAll
        · exact .hyp hξ)
      hUse

/-- Append-context form of `closedTheoryProvable_of_fresh_all_principal_cut`.
This is the universal principal case in the same split finite proof-state shape
used by the Henkin one-step conservativity reducer. -/
theorem closedTheoryProvable_of_fresh_all_principal_cut_append
    {ΓBase ΓTail : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    {θ : ClosedFormula Const}
    (hBaseNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓBase)
    (hTailNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail)
      (instantiate (Base := Base) (.const c) φ))
    (hUse : ClosedTheory.Provable (Const := Const)
      (ΓBase ++ (.all φ : ClosedFormula Const) :: ΓTail) θ) :
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail) θ :=
  closedTheoryProvable_of_fresh_all_principal_cut
    (Base := Base) (Const := Const)
    ((noConstOccurrenceInClosedTheory_append_iff
      (Const := Const) c ΓBase ΓTail).2 ⟨hBaseNo, hTailNo⟩)
    hφno hInst
    (closedTheoryProvable_cons_append_of_append_cons
      (Base := Base) (Const := Const)
      (ΓHead := ΓBase) (ΓTail := ΓTail)
      (χ := (.all φ : ClosedFormula Const))
      (θ := θ) hUse)

/-- Cut-free principal universal branch packaged for the sequent calculus. This
is the `impL` head case for the generated universal Henkin implication: a
derivation of the fresh instance and a continuation from the universal formula
combine to remove the generated implication from the split closed context. -/
theorem closedTheoryProvable_of_fresh_all_principal_cut_derivable_append
    {ΓBase ΓTail : ClosedTheory Const}
    {σ : Ty Base} {φ : Formula Const [σ]} {c : Const σ}
    {θ : ClosedFormula Const}
    (hBaseNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓBase)
    (hTailNo : NoConstOccurrenceInClosedTheory (Const := Const) c ΓTail)
    (hφno : NoConstOccurrence c φ)
    (hInst :
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable
        (Base := Base) (Const := Const)
        (ΓBase ++ ΓTail) (instantiate (Base := Base) (.const c) φ))
    (hUse :
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable
        (Base := Base) (Const := Const)
        (ΓBase ++ (.all φ : ClosedFormula Const) :: ΓTail) θ) :
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓTail) θ :=
  closedTheoryProvable_of_fresh_all_principal_cut_append
    (Base := Base) (Const := Const)
    hBaseNo hTailNo hφno
    (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable.toExtDerivation hInst)
    (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Derivable.toExtDerivation hUse)

theorem constantHenkinExImplication_mem_theorySet
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ]) :
    constantHenkinExImplication (Base := Base) (Const := Const) exConst φ ∈
      constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst :=
  Or.inl ⟨σ, φ, rfl⟩

theorem constantHenkinAllImplication_mem_theorySet
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {σ : Ty Base} (φ : Formula Const [σ]) :
    constantHenkinAllImplication (Base := Base) (Const := Const) allConst φ ∈
    constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst :=
  Or.inr ⟨σ, φ, rfl⟩

/-- Typed shape witness for a generated Henkin implication. The set membership
predicate is propositional; this witness keeps the branch, source formula, and
chosen eigenconstant recoverable for subsequent freshness proofs. -/
inductive ConstantHenkinImplicationShape
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) :
    ClosedFormula Const → Type (max u v) where
  | exImp {σ : Ty Base} (φ : Formula Const [σ]) :
      ConstantHenkinImplicationShape exConst allConst
        (constantHenkinExImplication
          (Base := Base) (Const := Const) exConst φ)
  | allImp {σ : Ty Base} (φ : Formula Const [σ]) :
      ConstantHenkinImplicationShape exConst allConst
        (constantHenkinAllImplication
          (Base := Base) (Const := Const) allConst φ)

namespace ConstantHenkinImplicationShape

/-- The eigenconstant selected by a generated Henkin implication shape. -/
def selected
    {exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {θ : ClosedFormula Const}
    (hθ : ConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ) :
    Sigma Const :=
  match hθ with
  | exImp (σ := σ) φ => ⟨σ, exConst φ⟩
  | allImp (σ := σ) φ => ⟨σ, allConst φ⟩

theorem toMem
    {exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {θ : ClosedFormula Const}
    (hθ : ConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ) :
    θ ∈ constantHenkinImplicationTheorySet
      (Base := Base) (Const := Const) exConst allConst := by
  cases hθ with
  | exImp φ =>
      exact constantHenkinExImplication_mem_theorySet
        (Base := Base) (Const := Const) exConst allConst φ
  | allImp φ =>
      exact constantHenkinAllImplication_mem_theorySet
        (Base := Base) (Const := Const) exConst allConst φ

end ConstantHenkinImplicationShape

theorem constantHenkinImplication_mem_of_shape
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {θ : ClosedFormula Const}
    (hθ : ConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ) :
    θ ∈ constantHenkinImplicationTheorySet
      (Base := Base) (Const := Const) exConst allConst :=
  hθ.toMem

/-- A generated Henkin implication whose selected eigenconstant is fresh for
the source formula being instantiated. Context/conclusion freshness is tracked
separately, since it depends on the finite derivation where the implication is
used. -/
inductive FreshConstantHenkinImplicationShape
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) :
    ClosedFormula Const → Type (max u v) where
  | exImp {σ : Ty Base} (φ : Formula Const [σ])
      (hφ : NoConstOccurrence (exConst φ) φ) :
      FreshConstantHenkinImplicationShape exConst allConst
        (constantHenkinExImplication
          (Base := Base) (Const := Const) exConst φ)
  | allImp {σ : Ty Base} (φ : Formula Const [σ])
      (hφ : NoConstOccurrence (allConst φ) φ) :
      FreshConstantHenkinImplicationShape exConst allConst
        (constantHenkinAllImplication
          (Base := Base) (Const := Const) allConst φ)

namespace FreshConstantHenkinImplicationShape

/-- Forget freshness, retaining only the generated-implication shape. -/
def toShape
    {exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {θ : ClosedFormula Const}
    (hθ : FreshConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ) :
    ConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ :=
  match hθ with
  | exImp φ _ => .exImp φ
  | allImp φ _ => .allImp φ

/-- The eigenconstant selected by a fresh generated implication. -/
def selected
    {exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {θ : ClosedFormula Const}
    (hθ : FreshConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ) :
    Sigma Const :=
  hθ.toShape.selected

theorem toMem
    {exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {θ : ClosedFormula Const}
    (hθ : FreshConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ) :
    θ ∈ constantHenkinImplicationTheorySet
      (Base := Base) (Const := Const) exConst allConst :=
  hθ.toShape.toMem

theorem sourceNoOccurrence
    {exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ}
    {θ : ClosedFormula Const}
    (hθ : FreshConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst θ) :
    (∃ (σ : Ty Base) (φ : Formula Const [σ]),
      θ = constantHenkinExImplication
          (Base := Base) (Const := Const) exConst φ ∧
      hθ.selected = ⟨σ, exConst φ⟩ ∧
      NoConstOccurrence (exConst φ) φ) ∨
    (∃ (σ : Ty Base) (φ : Formula Const [σ]),
      θ = constantHenkinAllImplication
          (Base := Base) (Const := Const) allConst φ ∧
      hθ.selected = ⟨σ, allConst φ⟩ ∧
      NoConstOccurrence (allConst φ) φ) := by
  cases hθ with
  | exImp φ hφ =>
      exact Or.inl ⟨_, φ, rfl, rfl, hφ⟩
  | allImp φ hφ =>
      exact Or.inr ⟨_, φ, rfl, rfl, hφ⟩

end FreshConstantHenkinImplicationShape

/-- A finite list of generated Henkin implications is fresh for a one-step
elimination sweep when each head eigenconstant is fresh for the fixed base
context, the remaining Henkin tail, and the final conclusion. -/
def FreshConstantHenkinImplicationListFor
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (ΓBase : ClosedTheory Const) :
    ClosedTheory Const → ClosedFormula Const → Prop
  | [], _ => True
  | γ :: ΓTail, θ =>
      ∃ hγ : FreshConstantHenkinImplicationShape
          (Base := Base) (Const := Const) exConst allConst γ,
        NoSigmaConstOccurrenceInClosedTheory
          (Const := Const) hγ.selected ΓBase ∧
        NoSigmaConstOccurrenceInClosedTheory
          (Const := Const) hγ.selected ΓTail ∧
        NoSigmaConstOccurrence (Const := Const) hγ.selected θ ∧
        FreshConstantHenkinImplicationListFor exConst allConst ΓBase ΓTail θ

/-- Any closed theory-set containing the generated Henkin implication scheme
has the implication data needed by the prime-Henkin world bridge. -/
def constantHenkinImplicationDataOfContainsTheorySet
    {U : ClosedTheorySet Const}
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hContains :
      ∀ {θ : ClosedFormula Const},
        θ ∈ constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst →
          θ ∈ U) :
    ConstantHenkinImplicationData (Const := Const) U where
  exConst := exConst
  allConst := allConst
  ex_imp := by
    intro σ φ
    exact hContains
      (constantHenkinExImplication_mem_theorySet
        (Base := Base) (Const := Const) exConst allConst φ)
  all_imp := by
    intro σ φ
    exact hContains
      (constantHenkinAllImplication_mem_theorySet
        (Base := Base) (Const := Const) exConst allConst φ)

namespace HenkinWitnessData

/-- Any canonical closed world carries its Henkin witness data. -/
theorem of_world (W : ClosedTheorySet.World Const) :
    HenkinWitnessData (Const := Const) W.carrier where
  exists_witness := W.exists_witness
  all_counterexample := W.all_counterexample

end HenkinWitnessData

namespace ConstantHenkinWitnessData

/-- Constant witnesses are closed-term witnesses, by viewing each fresh
constant as a closed term. -/
theorem toHenkinWitnessData
    {U : ClosedTheorySet Const}
    (hConst : ConstantHenkinWitnessData (Const := Const) U) :
    HenkinWitnessData (Const := Const) U where
  exists_witness := by
    intro σ φ hEx
    rcases hConst.exists_const_witness hEx with ⟨c, hc⟩
    exact ⟨.const c, hc⟩
  all_counterexample := by
    intro σ φ hAll
    rcases hConst.all_const_counterexample hAll with ⟨c, hc⟩
    exact ⟨.const c, hc⟩

end ConstantHenkinWitnessData

namespace ConstantHenkinImplicationData

/-- In a deductively closed theory-set, the fresh-constant implication scheme
extracts constant Henkin witness data by one modus-ponens step for existentials
and one contradiction-by-membership step for failed universals. -/
theorem toConstantHenkinWitnessData
    {U : ClosedTheorySet Const}
    (hImp : ConstantHenkinImplicationData (Const := Const) U)
    (hClosed : DeductivelyClosed (Const := Const) U) :
    ConstantHenkinWitnessData (Const := Const) U where
  exists_const_witness := by
    intro σ φ hEx
    let c := hImp.exConst (σ := σ) φ
    refine ⟨c, ?_⟩
    exact hClosed <|
      ClosedTheorySet.provable_mp
        (T := U)
        (φ := (.ex φ : ClosedFormula Const))
        (ψ := instantiate (Base := Base) (.const c) φ)
        (ClosedTheorySet.provable_of_mem
          (Const := Const) (T := U) (φ := .imp (.ex φ) (instantiate (Base := Base) (.const c) φ))
          (by
            dsimp [c]
            exact hImp.ex_imp φ))
        (ClosedTheorySet.provable_of_mem
          (Const := Const) (T := U) (φ := (.ex φ : ClosedFormula Const)) hEx)
  all_const_counterexample := by
    intro σ φ hAllNot
    let c := hImp.allConst (σ := σ) φ
    refine ⟨c, ?_⟩
    intro hInst
    apply hAllNot
    exact hClosed <|
      ClosedTheorySet.provable_mp
        (T := U)
        (φ := instantiate (Base := Base) (.const c) φ)
        (ψ := (.all φ : ClosedFormula Const))
        (ClosedTheorySet.provable_of_mem
          (Const := Const) (T := U)
          (φ := .imp (instantiate (Base := Base) (.const c) φ) (.all φ))
          (by
            dsimp [c]
            exact hImp.all_imp φ))
        (ClosedTheorySet.provable_of_mem
          (Const := Const) (T := U)
          (φ := instantiate (Base := Base) (.const c) φ) hInst)

end ConstantHenkinImplicationData

/-- Non-namespace alias for the implication-to-witness extraction theorem. -/
theorem constantHenkinWitnessDataOfImplications
    {U : ClosedTheorySet Const}
    (hClosed : DeductivelyClosed (Const := Const) U)
    (hImp : ConstantHenkinImplicationData (Const := Const) U) :
    ConstantHenkinWitnessData (Const := Const) U :=
  hImp.toConstantHenkinWitnessData hClosed

end ClosedTheorySet

end Mettapedia.Logic.HOL

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open ClosedTermCanonicalWorldModel
open scoped ENNReal

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace CompletenessFrontier

/-- The antecedent theory-set of a closed frontier after adjoining the generated
fresh-constant Henkin implication scheme. -/
def henkinizedAntecedentTheorySet
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) :
    ClosedTheorySet Const :=
  ClosedTheorySet.withConstantHenkinImplications
    (Base := Base) (Const := Const)
    F.antecedentTheorySet exConst allConst

theorem antecedent_mem_henkinizedAntecedentTheorySet
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {θ : ClosedFormula Const}
    (hθ : θ ∈ F.antecedents) :
    θ ∈ F.henkinizedAntecedentTheorySet
      (Base := Base) (Const := Const) exConst allConst :=
  ClosedTheorySet.mem_withConstantHenkinImplications_of_base
    (Base := Base) (Const := Const)
    (T := F.antecedentTheorySet) exConst allConst hθ

theorem henkinImplication_mem_henkinizedAntecedentTheorySet
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {θ : ClosedFormula Const}
    (hθ :
      θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst) :
    θ ∈ F.henkinizedAntecedentTheorySet
      (Base := Base) (Const := Const) exConst allConst :=
  ClosedTheorySet.mem_withConstantHenkinImplications_of_implication
    (Base := Base) (Const := Const)
    (T := F.antecedentTheorySet) exConst allConst hθ

/-- Ordinary antecedent-theory provability is monotone into the Henkinized
antecedent theory. -/
theorem henkinizedProvable_of_antecedentTheorySetProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    {θ : ClosedFormula Const}
    (hθ : ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet θ) :
    ClosedTheorySet.Provable (Const := Const)
      (F.henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst)
      θ :=
  ClosedTheorySet.provable_mono
    (Const := Const)
    (T := F.antecedentTheorySet)
    (U := F.henkinizedAntecedentTheorySet
      (Base := Base) (Const := Const) exConst allConst)
    (hTU := by
      intro θ hθ
      exact F.antecedent_mem_henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst hθ)
    hθ

/-- Conservativity of the chosen Henkin implication scheme over the original
antecedent theory. Proving this for a fresh-constant construction is the
remaining proof-theoretic obligation needed to turn ordinary non-provability
into the Henkinized countermodel theorem below. -/
def HenkinImplicationConservative
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) : Prop :=
  ∀ {θ : ClosedFormula Const},
    ClosedTheorySet.Provable (Const := Const)
      (F.henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst)
      θ →
    ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet θ

/-- Finite-context form of Henkin implication conservativity. Since
closed-theory-set provability is finite, this is equivalent to the global
set-based conservativity obligation but exposes the exact finite proof spine:
original antecedents plus finitely many generated Henkin implications. -/
def FiniteHenkinImplicationConservative
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) : Prop :=
  ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
    (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
    (∀ ψ, ψ ∈ ΓHenkin →
      ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst) →
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ →
    ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet θ

/-- One-step finite Henkin implication elimination. This is the precise local
freshness target needed by the canonical construction: remove a single generated
Henkin implication from a finite derivation, assuming all remaining finite
Henkin assumptions are still generated by the same scheme. -/
def OneStepHenkinImplicationConservative
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) : Prop :=
  ∀ {θ γ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
    (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
    (∀ ψ, ψ ∈ ΓHenkin →
      ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst) →
    γ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
      (Base := Base) (Const := Const) exConst allConst →
    ClosedTheory.Provable (Const := Const) (ΓBase ++ γ :: ΓHenkin) θ →
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ

/-- Fresh one-step Henkin implication elimination. This is the eigenconstant
form of the local proof obligation: the generated implication is supplied with
typed shape/fresh-source data, and its selected constant is fresh for the base
context, remaining Henkin tail, and target conclusion. -/
def FreshOneStepHenkinImplicationConservative
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) : Prop :=
  ∀ {θ γ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
    (hγ : ClosedTheorySet.FreshConstantHenkinImplicationShape
      (Base := Base) (Const := Const) exConst allConst γ) →
    ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
      (Const := Const) hγ.selected ΓBase →
    ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
      (Const := Const) hγ.selected ΓHenkin →
    ClosedTheorySet.NoSigmaConstOccurrence
      (Const := Const) hγ.selected θ →
    (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
    (∀ ψ, ψ ∈ ΓHenkin →
      ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst) →
    ClosedTheory.Provable (Const := Const) (ΓBase ++ γ :: ΓHenkin) θ →
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ

theorem freshOneStepHenkinImplicationConservative_of_branch_cases
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hEx :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
        {σ : Ty Base} (φ : Formula Const [σ]),
        NoConstOccurrence (exConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (exConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (exConst φ) ΓHenkin →
        NoConstOccurrence (exConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheory.Provable (Const := Const)
          (ΓBase ++
            ClosedTheorySet.constantHenkinExImplication
              (Base := Base) (Const := Const) exConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ)
    (hAll :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
        {σ : Ty Base} (φ : Formula Const [σ]),
        NoConstOccurrence (allConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (allConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (allConst φ) ΓHenkin →
        NoConstOccurrence (allConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheory.Provable (Const := Const)
          (ΓBase ++
            ClosedTheorySet.constantHenkinAllImplication
              (Base := Base) (Const := Const) allConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ) :
    F.FreshOneStepHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  intro θ γ ΓBase ΓHenkin hγ hBaseFresh hTailFresh hθFresh hBase hHenkin hDer
  cases hγ with
  | exImp φ hφno =>
      change ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := Const) (exConst φ) ΓBase at hBaseFresh
      change ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := Const) (exConst φ) ΓHenkin at hTailFresh
      change NoConstOccurrence (exConst φ) θ at hθFresh
      exact hEx φ hφno hBaseFresh hTailFresh hθFresh hBase hHenkin hDer
  | allImp φ hφno =>
      change ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := Const) (allConst φ) ΓBase at hBaseFresh
      change ClosedTheorySet.NoConstOccurrenceInClosedTheory
        (Const := Const) (allConst φ) ΓHenkin at hTailFresh
      change NoConstOccurrence (allConst φ) θ at hθFresh
      exact hAll φ hφno hBaseFresh hTailFresh hθFresh hBase hHenkin hDer

/-- Finite-context Henkin conservativity under explicit freshness data for the
finite Henkin tail. This is weaker than global conservativity but exactly
matches the finite proof state exposed by the split lemma. -/
def FreshFiniteHenkinImplicationConservative
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) : Prop :=
  ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
    (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
    (∀ ψ, ψ ∈ ΓHenkin →
      ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst) →
    ClosedTheorySet.FreshConstantHenkinImplicationListFor
      (Base := Base) (Const := Const) exConst allConst ΓBase ΓHenkin θ →
    ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ →
    ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet θ

/-- Proof-state freshness for converting the freshness-aware one-step
eliminator into the ordinary one-step conservativity interface. It says that
whenever a generated Henkin implication is about to be eliminated from a finite
proof state, it can be presented with a source-fresh shape whose selected
eigenconstant is fresh for the base context, the remaining Henkin tail, and the
conclusion. -/
def HenkinImplicationOneStepFreshness
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) : Prop :=
  ∀ {θ γ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
    (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
    (∀ ψ, ψ ∈ ΓHenkin →
      ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst) →
    γ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
      (Base := Base) (Const := Const) exConst allConst →
    ∃ hγ : ClosedTheorySet.FreshConstantHenkinImplicationShape
        (Base := Base) (Const := Const) exConst allConst γ,
      ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
        (Const := Const) hγ.selected ΓBase ∧
      ClosedTheorySet.NoSigmaConstOccurrenceInClosedTheory
        (Const := Const) hγ.selected ΓHenkin ∧
      ClosedTheorySet.NoSigmaConstOccurrence
        (Const := Const) hγ.selected θ

theorem closedTheoryProvable_withoutHenkin_of_oneStepHenkinImplicationConservative
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
    (hBase : ∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents)
    (hHenkin :
      ∀ ψ, ψ ∈ ΓHenkin →
        ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst)
    (hDer : ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ) :
    ClosedTheory.Provable (Const := Const) ΓBase θ := by
  induction ΓHenkin generalizing θ with
  | nil =>
      simpa using hDer
  | cons γ ΓHenkin ih =>
      have hTail :
          ∀ ψ, ψ ∈ ΓHenkin →
            ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
              (Base := Base) (Const := Const) exConst allConst := by
        intro ψ hψ
        exact hHenkin ψ (by simp [hψ])
      have hγ :
          γ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst :=
        hHenkin γ (by simp)
      have hReducedTail :
          ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ :=
        hStep hBase hTail hγ hDer
      exact ih hTail hReducedTail

theorem closedTheoryProvable_withoutFreshHenkin_of_freshOneStepHenkinImplicationConservative
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
    (hBase : ∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents)
    (hHenkin :
      ∀ ψ, ψ ∈ ΓHenkin →
        ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst)
    (hFresh :
      ClosedTheorySet.FreshConstantHenkinImplicationListFor
        (Base := Base) (Const := Const) exConst allConst ΓBase ΓHenkin θ)
    (hDer : ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ) :
    ClosedTheory.Provable (Const := Const) ΓBase θ := by
  induction ΓHenkin generalizing θ with
  | nil =>
      simpa using hDer
  | cons γ ΓHenkin ih =>
      rcases hFresh with
        ⟨hγFresh, hBaseFresh, hTailFresh, hθFresh, hFreshTail⟩
      have hTail :
          ∀ ψ, ψ ∈ ΓHenkin →
            ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
              (Base := Base) (Const := Const) exConst allConst := by
        intro ψ hψ
        exact hHenkin ψ (by simp [hψ])
      have hReducedTail :
          ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ :=
        hStep hγFresh hBaseFresh hTailFresh hθFresh hBase hTail hDer
      exact ih hTail hFreshTail hReducedTail

theorem finiteHenkinImplicationConservative_of_oneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst) :
    F.FiniteHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  intro θ ΓBase ΓHenkin hBase hHenkin hDer
  have hClosedDer :
      ClosedTheory.Provable (Const := Const) ΓBase θ :=
    F.closedTheoryProvable_withoutHenkin_of_oneStepHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst hStep hBase hHenkin hDer
  exact ClosedTheorySet.provable_of_closedTheory
    (Const := Const) (T := F.antecedentTheorySet)
    (Δ := ΓBase)
    (hΔ := by
      intro ψ hψ
      exact hBase ψ hψ)
    hClosedDer

theorem freshFiniteHenkinImplicationConservative_of_freshOneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst) :
    F.FreshFiniteHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  intro θ ΓBase ΓHenkin hBase hHenkin hFresh hDer
  have hClosedDer :
      ClosedTheory.Provable (Const := Const) ΓBase θ :=
    F.closedTheoryProvable_withoutFreshHenkin_of_freshOneStepHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst
      hStep hBase hHenkin hFresh hDer
  exact ClosedTheorySet.provable_of_closedTheory
    (Const := Const) (T := F.antecedentTheorySet)
    (Δ := ΓBase)
    (hΔ := by
      intro ψ hψ
      exact hBase ψ hψ)
    hClosedDer

theorem oneStepHenkinImplicationConservative_of_freshOneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hFresh :
      F.HenkinImplicationOneStepFreshness
        (Base := Base) (Const := Const) exConst allConst) :
    F.OneStepHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  intro θ γ ΓBase ΓHenkin hBase hHenkin hγ hDer
  rcases hFresh hBase hHenkin hγ with
    ⟨hγFresh, hBaseFresh, hTailFresh, hθFresh⟩
  exact hStep hγFresh hBaseFresh hTailFresh hθFresh hBase hHenkin hDer

/-- A freshness witness for every finite Henkin tail specializes to the
one-step freshness interface by looking at the head of the list. This cleanly
separates the structural eliminator from the problem of manufacturing fresh
eigenconstants for a given finite proof state. -/
theorem henkinImplicationOneStepFreshness_of_listFreshness
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hFreshList :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := Base) (Const := Const) exConst allConst ΓBase ΓHenkin θ) :
    F.HenkinImplicationOneStepFreshness
      (Base := Base) (Const := Const) exConst allConst := by
  intro θ γ ΓBase ΓHenkin hBase hHenkin hγ
  have hFresh :
      ClosedTheorySet.FreshConstantHenkinImplicationListFor
        (Base := Base) (Const := Const) exConst allConst ΓBase (γ :: ΓHenkin) θ :=
    hFreshList hBase (by
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψTail
      · exact hγ
      · exact hHenkin ψ hψTail)
  rcases hFresh with ⟨hγFresh, hBaseFresh, hTailFresh, hθFresh, _hFreshTail⟩
  exact ⟨hγFresh, hBaseFresh, hTailFresh, hθFresh⟩

/-- Fresh one-step elimination plus a finite-list freshness supplier already
gives the ordinary finite Henkin conservativity interface. -/
theorem finiteHenkinImplicationConservative_of_freshOneStep_listFreshness
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hFreshList :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := Base) (Const := Const) exConst allConst ΓBase ΓHenkin θ) :
    F.FiniteHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  intro θ ΓBase ΓHenkin hBase hHenkin hDer
  exact
    F.freshFiniteHenkinImplicationConservative_of_freshOneStep
      (Base := Base) (Const := Const) exConst allConst hStep
      hBase hHenkin (hFreshList hBase hHenkin) hDer

/-- Fresh one-step elimination therefore yields full Henkin conservativity as
soon as every finite split admits a freshness witness list. -/
theorem henkinImplicationConservative_of_freshOneStep_listFreshness
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hFreshList :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := Base) (Const := Const) exConst allConst ΓBase ΓHenkin θ) :
    F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  intro θ hProv
  rcases (ClosedTheorySet.provable_withConstantHenkinImplications_iff_exists_split
      (Base := Base) (Const := Const)
      (T := F.antecedentTheorySet) exConst allConst).1 hProv with
    ⟨ΓBase, ΓHenkin, hBase, hHenkin, hDer⟩
  exact F.finiteHenkinImplicationConservative_of_freshOneStep_listFreshness
    (Base := Base) (Const := Const) exConst allConst hStep hFreshList
    hBase hHenkin hDer

/-- Branch-specific fresh one-step eliminators plus a finite-list freshness
supplier already yield the ordinary finite Henkin conservativity interface. -/
theorem finiteHenkinImplicationConservative_of_branch_cases_and_listFreshness
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hEx :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
        {σ : Ty Base} (φ : Formula Const [σ]),
        NoConstOccurrence (exConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (exConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (exConst φ) ΓHenkin →
        NoConstOccurrence (exConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheory.Provable (Const := Const)
          (ΓBase ++
            ClosedTheorySet.constantHenkinExImplication
              (Base := Base) (Const := Const) exConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ)
    (hAll :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
        {σ : Ty Base} (φ : Formula Const [σ]),
        NoConstOccurrence (allConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (allConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (allConst φ) ΓHenkin →
        NoConstOccurrence (allConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheory.Provable (Const := Const)
          (ΓBase ++
            ClosedTheorySet.constantHenkinAllImplication
              (Base := Base) (Const := Const) allConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ)
    (hFreshList :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := Base) (Const := Const) exConst allConst ΓBase ΓHenkin θ) :
    F.FiniteHenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst :=
  F.finiteHenkinImplicationConservative_of_freshOneStep_listFreshness
    (Base := Base) (Const := Const) exConst allConst
    (F.freshOneStepHenkinImplicationConservative_of_branch_cases
      (Base := Base) (Const := Const) exConst allConst hEx hAll)
    hFreshList

/-- The global Henkin conservativity theorem follows from branch-specific fresh
one-step elimination together with a finite-list freshness supplier. -/
theorem henkinImplicationConservative_of_branch_cases_and_listFreshness
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hEx :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
        {σ : Ty Base} (φ : Formula Const [σ]),
        NoConstOccurrence (exConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (exConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (exConst φ) ΓHenkin →
        NoConstOccurrence (exConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheory.Provable (Const := Const)
          (ΓBase ++
            ClosedTheorySet.constantHenkinExImplication
              (Base := Base) (Const := Const) exConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ)
    (hAll :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const}
        {σ : Ty Base} (φ : Formula Const [σ]),
        NoConstOccurrence (allConst φ) φ →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (allConst φ) ΓBase →
        ClosedTheorySet.NoConstOccurrenceInClosedTheory
          (Const := Const) (allConst φ) ΓHenkin →
        NoConstOccurrence (allConst φ) θ →
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheory.Provable (Const := Const)
          (ΓBase ++
            ClosedTheorySet.constantHenkinAllImplication
              (Base := Base) (Const := Const) allConst φ :: ΓHenkin) θ →
        ClosedTheory.Provable (Const := Const) (ΓBase ++ ΓHenkin) θ)
    (hFreshList :
      ∀ {θ : ClosedFormula Const} {ΓBase ΓHenkin : ClosedTheory Const},
        (∀ ψ, ψ ∈ ΓBase → ψ ∈ F.antecedents) →
        (∀ ψ, ψ ∈ ΓHenkin →
          ψ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
            (Base := Base) (Const := Const) exConst allConst) →
        ClosedTheorySet.FreshConstantHenkinImplicationListFor
          (Base := Base) (Const := Const) exConst allConst ΓBase ΓHenkin θ) :
    F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  exact F.henkinImplicationConservative_of_freshOneStep_listFreshness
    (Base := Base) (Const := Const) exConst allConst
    (F.freshOneStepHenkinImplicationConservative_of_branch_cases
      (Base := Base) (Const := Const) exConst allConst hEx hAll)
    hFreshList

theorem henkinImplicationConservative_iff_finite
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ) :
    F.HenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst ↔
      F.FiniteHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst := by
  constructor
  · intro hCons θ ΓBase ΓHenkin hBase hHenkin hDer
    apply hCons
    refine ⟨ΓBase ++ ΓHenkin, ?_, hDer⟩
    intro ψ hψ
    rcases List.mem_append.mp hψ with hψBase | hψHenkin
    · exact F.antecedent_mem_henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst (hBase ψ hψBase)
    · exact F.henkinImplication_mem_henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst (hHenkin ψ hψHenkin)
  · intro hFinite θ hProv
    rcases (ClosedTheorySet.provable_withConstantHenkinImplications_iff_exists_split
        (Base := Base) (Const := Const)
        (T := F.antecedentTheorySet) exConst allConst).1 hProv with
      ⟨ΓBase, ΓHenkin, hBase, hHenkin, hDer⟩
    exact hFinite hBase hHenkin hDer

theorem henkinImplicationConservative_of_finite
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst) :
    F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst :=
  (F.henkinImplicationConservative_iff_finite
    (Base := Base) (Const := Const) exConst allConst).2 hFinite

theorem henkinImplicationConservative_of_oneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst) :
    F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst :=
  F.henkinImplicationConservative_of_finite
    (Base := Base) (Const := Const) exConst allConst
    (F.finiteHenkinImplicationConservative_of_oneStep
      (Base := Base) (Const := Const) exConst allConst hStep)

theorem henkinImplicationConservative_of_freshOneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.FreshOneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hFresh :
      F.HenkinImplicationOneStepFreshness
        (Base := Base) (Const := Const) exConst allConst) :
    F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst :=
  F.henkinImplicationConservative_of_oneStep
    (Base := Base) (Const := Const) exConst allConst
    (F.oneStepHenkinImplicationConservative_of_freshOneStep
      (Base := Base) (Const := Const) exConst allConst hStep hFresh)

/-- If every generated Henkin implication is already provable from the original
antecedent theory, then the generated implication scheme is conservative.  This
is mostly a plumbing lemma; the real canonical-construction work is to prove
the analogous hypothesis from freshness rather than assuming the implications
are directly provable. -/
theorem henkinImplicationConservative_of_implicationsProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hImp :
      ∀ {θ : ClosedFormula Const},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst →
        ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet θ) :
    F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst := by
  apply F.henkinImplicationConservative_of_finite
    (Base := Base) (Const := Const) exConst allConst
  intro θ ΓBase ΓHenkin hBase hHenkin hDer
  apply ClosedTheorySet.provable_of_closedTheoryProvable_of_provable_hyps
    (Const := Const)
    (T := F.antecedentTheorySet)
    (Γ := ΓBase ++ ΓHenkin)
    (θ := θ)
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψBase | hψHenkin
    · exact ClosedTheorySet.provable_of_mem
        (Const := Const) (T := F.antecedentTheorySet)
        (hBase ψ hψBase)
    · exact hImp (hHenkin ψ hψHenkin)
  · exact hDer

/-- A conservative Henkin implication scheme converts non-provability from the
original antecedents into non-provability from the Henkinized antecedents. -/
theorem not_henkinizedProvable_of_not_antecedentTheorySetProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hCons : F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ ClosedTheorySet.Provable (Const := Const)
      (F.henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst)
      F.succedent := by
  intro hHenkin
  exact hNot (hCons hHenkin)

end CompletenessFrontier

namespace CompletenessFrontier.PrimeSeparatingExtension

/-- A prime separating extension plus Henkin witness data is a canonical closed
world. This packages the two quantifier obligations as a single reusable target
for the Henkin/Lindenbaum construction. -/
def toWorldOfHenkinWitnessData
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := Const) U) :
    ClosedTheorySet.World Const :=
  hFU.toWorld hWit.exists_witness hWit.all_counterexample

@[simp]
theorem toWorldOfHenkinWitnessData_carrier
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := Const) U) :
    (hFU.toWorldOfHenkinWitnessData hWit).carrier = U :=
  rfl

theorem mem_toWorldOfHenkinWitnessData_of_antecedent
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := Const) U)
    {φ : ClosedFormula Const} (hφ : φ ∈ F.antecedents) :
    φ ∈ (hFU.toWorldOfHenkinWitnessData hWit).carrier := by
  simpa using hFU.contains_antecedents hφ

theorem succedent_not_mem_toWorldOfHenkinWitnessData
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := Const) U) :
    F.succedent ∉ (hFU.toWorldOfHenkinWitnessData hWit).carrier := by
  simpa using hFU.omits_succedent

end CompletenessFrontier.PrimeSeparatingExtension

namespace CompletenessFrontier

/-- Prime separation plus Henkin witness data yields the singleton world-model
counterexample endpoint. -/
def singletonWorldModelCounterexampleOfPrimeSeparatingExtensionHenkin
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := Const) U) :
    SingletonWorldModelCounterexample (Const := Const) F :=
  singletonWorldModelCounterexampleOfWorldCounterexample
    (Base := Base) (Const := Const)
    (W := hFU.toWorldOfHenkinWitnessData hWit)
    (fun _ hφ => hFU.mem_toWorldOfHenkinWitnessData_of_antecedent hWit hφ)
    (hFU.succedent_not_mem_toWorldOfHenkinWitnessData hWit)

theorem not_derivable_of_primeSeparatingExtension_henkin
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := Const) U) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  (singletonWorldModelCounterexampleOfPrimeSeparatingExtensionHenkin
    (Base := Base) (Const := Const) hFU hWit).not_derivable

theorem not_singletonStrengthConsequence_of_primeSeparatingExtension_henkin
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hWit : ClosedTheorySet.HenkinWitnessData (Const := Const) U) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  not_singletonStrengthConsequence_of_counterexample
    (Base := Base) (Const := Const)
    (singletonWorldModelCounterexampleOfPrimeSeparatingExtensionHenkin
      (Base := Base) (Const := Const) hFU hWit)

/-- A prime Henkin separating extension packages the carrier produced by the
Lindenbaum/prime-extension stage together with the Henkin witness data needed
to view it as a canonical world. -/
structure PrimeHenkinSeparatingExtension
    (F : CompletenessFrontier Const []) : Type (max u v) where
  carrier : ClosedTheorySet Const
  extension : PrimeSeparatingExtension (Const := Const) F carrier
  henkin : ClosedTheorySet.HenkinWitnessData (Const := Const) carrier

namespace PrimeHenkinSeparatingExtension

/-- Forget the bundled frontier package down to its canonical closed world. -/
def toWorld {F : CompletenessFrontier Const []}
    (E : PrimeHenkinSeparatingExtension (Const := Const) F) :
    ClosedTheorySet.World Const :=
  E.extension.toWorldOfHenkinWitnessData E.henkin

@[simp]
theorem toWorld_carrier {F : CompletenessFrontier Const []}
    (E : PrimeHenkinSeparatingExtension (Const := Const) F) :
    E.toWorld.carrier = E.carrier :=
  rfl

theorem contains_antecedents {F : CompletenessFrontier Const []}
    (E : PrimeHenkinSeparatingExtension (Const := Const) F)
    {φ : ClosedFormula Const} (hφ : φ ∈ F.antecedents) :
    φ ∈ E.toWorld.carrier := by
  simpa using E.extension.contains_antecedents hφ

theorem omits_succedent {F : CompletenessFrontier Const []}
    (E : PrimeHenkinSeparatingExtension (Const := Const) F) :
    F.succedent ∉ E.toWorld.carrier := by
  simpa using E.extension.omits_succedent

/-- A prime Henkin separating extension is immediately a singleton world-model
counterexample. -/
def toSingletonWorldModelCounterexample {F : CompletenessFrontier Const []}
    (E : PrimeHenkinSeparatingExtension (Const := Const) F) :
    SingletonWorldModelCounterexample (Const := Const) F :=
  singletonWorldModelCounterexampleOfPrimeSeparatingExtensionHenkin
    (Base := Base) (Const := Const) E.extension E.henkin

theorem not_derivable {F : CompletenessFrontier Const []}
    (E : PrimeHenkinSeparatingExtension (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  not_derivable_of_primeSeparatingExtension_henkin
    (Base := Base) (Const := Const) E.extension E.henkin

theorem not_singletonStrengthConsequence {F : CompletenessFrontier Const []}
    (E : PrimeHenkinSeparatingExtension (Const := Const) F) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  not_singletonStrengthConsequence_of_primeSeparatingExtension_henkin
    (Base := Base) (Const := Const) E.extension E.henkin

end PrimeHenkinSeparatingExtension

/-- A prime constant-Henkin separating extension is the sharper production
target for a fresh-constant Henkin construction: the prime separating carrier
comes with constant witnesses, which can then be viewed as closed-term
witnesses. -/
structure PrimeConstantHenkinSeparatingExtension
    (F : CompletenessFrontier Const []) : Type (max u v) where
  carrier : ClosedTheorySet Const
  extension : PrimeSeparatingExtension (Const := Const) F carrier
  const_henkin : ClosedTheorySet.ConstantHenkinWitnessData (Const := Const) carrier

namespace PrimeConstantHenkinSeparatingExtension

/-- Constant-Henkin separating extensions coerce to term-Henkin separating
extensions. -/
def toPrimeHenkinSeparatingExtension {F : CompletenessFrontier Const []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := Const) F) :
    PrimeHenkinSeparatingExtension (Const := Const) F where
  carrier := E.carrier
  extension := E.extension
  henkin := E.const_henkin.toHenkinWitnessData

/-- Forget a prime constant-Henkin separating extension down to its canonical
closed world. -/
def toWorld {F : CompletenessFrontier Const []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := Const) F) :
    ClosedTheorySet.World Const :=
  E.toPrimeHenkinSeparatingExtension.toWorld

@[simp]
theorem toWorld_carrier {F : CompletenessFrontier Const []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := Const) F) :
    E.toWorld.carrier = E.carrier :=
  rfl

/-- A prime constant-Henkin separating extension yields the singleton
world-model counterexample endpoint. -/
def toSingletonWorldModelCounterexample {F : CompletenessFrontier Const []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := Const) F) :
    SingletonWorldModelCounterexample (Const := Const) F :=
  E.toPrimeHenkinSeparatingExtension.toSingletonWorldModelCounterexample

theorem not_derivable {F : CompletenessFrontier Const []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  E.toPrimeHenkinSeparatingExtension.not_derivable

theorem not_singletonStrengthConsequence {F : CompletenessFrontier Const []}
    (E : PrimeConstantHenkinSeparatingExtension (Const := Const) F) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  E.toPrimeHenkinSeparatingExtension.not_singletonStrengthConsequence

end PrimeConstantHenkinSeparatingExtension

namespace PrimeSeparatingExtension

/-- A prime separating extension whose carrier contains the fresh-constant
Henkin implication scheme is already a prime constant-Henkin separating
extension. -/
def toPrimeConstantHenkinSeparatingExtensionOfImplications
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hImp : ClosedTheorySet.ConstantHenkinImplicationData (Const := Const) U) :
    PrimeConstantHenkinSeparatingExtension (Const := Const) F where
  carrier := U
  extension := hFU
  const_henkin := hImp.toConstantHenkinWitnessData hFU.closed

/-- If the prime extension contains the generated Henkin implication theory-set,
then it is already a prime constant-Henkin separating extension. This is the
direct handoff shape for the usual "add Henkin implications, then prime-extend"
construction. -/
def toPrimeConstantHenkinSeparatingExtensionOfContainedImplications
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hContains :
      ∀ {θ : ClosedFormula Const},
        θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
          (Base := Base) (Const := Const) exConst allConst →
          θ ∈ U) :
    PrimeConstantHenkinSeparatingExtension (Const := Const) F :=
  hFU.toPrimeConstantHenkinSeparatingExtensionOfImplications
    (ClosedTheorySet.constantHenkinImplicationDataOfContainsTheorySet
      (Base := Base) (Const := Const) exConst allConst hContains)

end PrimeSeparatingExtension

/-- Prime separation together with explicit containment of the generated
fresh-constant Henkin implication theory-set. This is the natural target for
the canonical construction step "add Henkin implications, then prime-extend";
the ordinary constant-witness and closed-term-witness packages are extracted
from it. -/
structure PrimeHenkinImplicationSeparatingExtension
    (F : CompletenessFrontier Const []) : Type (max u v) where
  carrier : ClosedTheorySet Const
  extension : PrimeSeparatingExtension (Const := Const) F carrier
  exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ
  allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ
  contains_implications :
    ∀ {θ : ClosedFormula Const},
      θ ∈ ClosedTheorySet.constantHenkinImplicationTheorySet
        (Base := Base) (Const := Const) exConst allConst →
        θ ∈ carrier

namespace PrimeHenkinImplicationSeparatingExtension

/-- The contained implication theory-set gives the raw implication data. -/
def implicationData {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    ClosedTheorySet.ConstantHenkinImplicationData (Const := Const) E.carrier :=
  ClosedTheorySet.constantHenkinImplicationDataOfContainsTheorySet
    (Base := Base) (Const := Const) E.exConst E.allConst E.contains_implications

/-- A prime Henkin-implication separating extension is a prime
constant-Henkin separating extension. -/
def toPrimeConstantHenkinSeparatingExtension
    {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    PrimeConstantHenkinSeparatingExtension (Const := Const) F :=
  E.extension.toPrimeConstantHenkinSeparatingExtensionOfContainedImplications
    E.exConst E.allConst E.contains_implications

/-- A prime Henkin-implication separating extension is a prime term-Henkin
separating extension. -/
def toPrimeHenkinSeparatingExtension
    {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    PrimeHenkinSeparatingExtension (Const := Const) F :=
  E.toPrimeConstantHenkinSeparatingExtension.toPrimeHenkinSeparatingExtension

/-- The canonical world extracted from a prime Henkin-implication separating
extension. -/
def toWorld {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    ClosedTheorySet.World Const :=
  E.toPrimeConstantHenkinSeparatingExtension.toWorld

@[simp]
theorem toWorld_carrier {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    E.toWorld.carrier = E.carrier :=
  rfl

/-- The singleton world-model counterexample extracted from a prime
Henkin-implication separating extension. -/
def toSingletonWorldModelCounterexample {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    SingletonWorldModelCounterexample (Const := Const) F :=
  E.toPrimeConstantHenkinSeparatingExtension.toSingletonWorldModelCounterexample

theorem not_derivable {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  E.toPrimeConstantHenkinSeparatingExtension.not_derivable

theorem not_singletonStrengthConsequence {F : CompletenessFrontier Const []}
    (E : PrimeHenkinImplicationSeparatingExtension (Const := Const) F) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  E.toPrimeConstantHenkinSeparatingExtension.not_singletonStrengthConsequence

end PrimeHenkinImplicationSeparatingExtension

/-- If the Henkinized antecedent theory-set does not prove the succedent, the
prime-filter separation theorem produces a prime extension containing both the
original antecedents and the generated Henkin implication scheme. -/
theorem nonempty_primeHenkinImplicationSeparatingExtension_of_not_henkinizedProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        (F.henkinizedAntecedentTheorySet
          (Base := Base) (Const := Const) exConst allConst)
        F.succedent) :
    Nonempty (PrimeHenkinImplicationSeparatingExtension
      (Base := Base) (Const := Const) F) := by
  rcases ClosedTheorySet.exists_prime_extension_separating
      (Const := Const)
      (T := F.henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst)
      (φ := F.succedent)
      hNot with
    ⟨U, hExt, hClosed, hConsistent, hPrime, hOmit⟩
  exact ⟨{
    carrier := U
    extension := {
      contains_antecedents := by
        intro θ hθ
        exact hExt
          (F.antecedent_mem_henkinizedAntecedentTheorySet
            (Base := Base) (Const := Const) exConst allConst hθ)
      closed := hClosed
      consistent := hConsistent
      prime_or := hPrime
      omits_succedent := hOmit }
    exConst := exConst
    allConst := allConst
    contains_implications := by
      intro θ hθ
      exact hExt
        (F.henkinImplication_mem_henkinizedAntecedentTheorySet
          (Base := Base) (Const := Const) exConst allConst hθ) }⟩

/-- Non-provability from the Henkinized antecedent theory-set produces an
explicit singleton world-model counterexample for the original closed
frontier. -/
theorem nonempty_singletonWorldModelCounterexample_of_not_henkinizedProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        (F.henkinizedAntecedentTheorySet
          (Base := Base) (Const := Const) exConst allConst)
        F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := Base) (Const := Const) F) := by
  rcases F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_henkinizedProvable
      (Base := Base) (Const := Const) exConst allConst hNot with
    ⟨E⟩
  exact ⟨E.toSingletonWorldModelCounterexample⟩

/-- Non-provability from the Henkinized antecedent theory-set already refutes
native derivability of the original closed frontier through the packaged
prime-Henkin implication extension. -/
theorem not_derivable_of_not_henkinizedProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        (F.henkinizedAntecedentTheorySet
          (Base := Base) (Const := Const) exConst allConst)
        F.succedent) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  rcases F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_henkinizedProvable
      (Base := Base) (Const := Const) exConst allConst hNot with
    ⟨E⟩
  exact E.not_derivable

/-- Non-provability from the Henkinized antecedent theory-set also refutes
singleton-strength semantic consequence for the original closed frontier. -/
theorem not_singletonStrengthConsequence_of_not_henkinizedProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        (F.henkinizedAntecedentTheorySet
          (Base := Base) (Const := Const) exConst allConst)
        F.succedent) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F := by
  rcases F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_henkinizedProvable
      (Base := Base) (Const := Const) exConst allConst hNot with
    ⟨E⟩
  exact E.not_singletonStrengthConsequence

/-- Under conservativity of the generated Henkin implication scheme, ordinary
closed-theory non-provability produces an explicit singleton world-model
counterexample. -/
theorem nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hCons : F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := Base) (Const := Const) F) :=
  F.nonempty_singletonWorldModelCounterexample_of_not_henkinizedProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.not_henkinizedProvable_of_not_antecedentTheorySetProvable
      (Base := Base) (Const := Const) exConst allConst hCons hNot)

/-- Under conservativity of the generated Henkin implication scheme, ordinary
closed-theory non-provability refutes native derivability of the original
frontier. -/
theorem not_derivable_of_not_antecedentTheorySetProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hCons : F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  F.not_derivable_of_not_henkinizedProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.not_henkinizedProvable_of_not_antecedentTheorySetProvable
      (Base := Base) (Const := Const) exConst allConst hCons hNot)

/-- Under conservativity of the generated Henkin implication scheme, ordinary
closed-theory non-provability refutes singleton-strength semantic consequence. -/
theorem not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hCons : F.HenkinImplicationConservative
      (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  F.not_singletonStrengthConsequence_of_not_henkinizedProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.not_henkinizedProvable_of_not_antecedentTheorySetProvable
      (Base := Base) (Const := Const) exConst allConst hCons hNot)

/-- Finite-context conservativity converts ordinary non-provability into
Henkinized non-provability, exposing the exact handoff into prime separation. -/
theorem not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_finite
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ ClosedTheorySet.Provable (Const := Const)
      (F.henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst)
      F.succedent :=
  F.not_henkinizedProvable_of_not_antecedentTheorySetProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.henkinImplicationConservative_of_finite
      (Base := Base) (Const := Const) exConst allConst hFinite)
    hNot

/-- Finite-context conservativity produces the prime Henkin-implication
separating extension directly from ordinary closed-theory non-provability. -/
theorem nonempty_primeHenkinImplicationSeparatingExtension_of_not_antecedentTheorySetProvable_of_finite
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    Nonempty (PrimeHenkinImplicationSeparatingExtension
      (Base := Base) (Const := Const) F) :=
  F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_henkinizedProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_finite
      (Base := Base) (Const := Const) exConst allConst hFinite hNot)

/-- Finite-context conservativity of the generated Henkin implication scheme is
enough to extract the singleton world-model counterexample from ordinary
closed-theory non-provability. -/
theorem nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_of_finite
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := Base) (Const := Const) F) :=
  F.nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.henkinImplicationConservative_of_finite
      (Base := Base) (Const := Const) exConst allConst hFinite)
    hNot

/-- Finite-context conservativity of the generated Henkin implication scheme
refutes native derivability whenever the original closed antecedent theory-set
does not prove the succedent. -/
theorem not_derivable_of_not_antecedentTheorySetProvable_of_finite
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  F.not_derivable_of_not_antecedentTheorySetProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.henkinImplicationConservative_of_finite
      (Base := Base) (Const := Const) exConst allConst hFinite)
    hNot

/-- Finite-context conservativity of the generated Henkin implication scheme is
also enough to refute singleton-strength semantic consequence. -/
theorem not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_of_finite
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hFinite :
      F.FiniteHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  F.not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable
    (Base := Base) (Const := Const) exConst allConst
    (F.henkinImplicationConservative_of_finite
      (Base := Base) (Const := Const) exConst allConst hFinite)
    hNot

/-- One-step finite Henkin implication elimination is enough to extract the
singleton world-model counterexample from ordinary closed-theory
non-provability. -/
theorem nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_of_oneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    Nonempty (SingletonWorldModelCounterexample (Base := Base) (Const := Const) F) :=
  F.nonempty_singletonWorldModelCounterexample_of_not_antecedentTheorySetProvable_of_finite
    (Base := Base) (Const := Const) exConst allConst
    (F.finiteHenkinImplicationConservative_of_oneStep
      (Base := Base) (Const := Const) exConst allConst hStep)
    hNot

/-- One-step finite Henkin implication elimination converts ordinary
non-provability into Henkinized non-provability. -/
theorem not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_oneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ ClosedTheorySet.Provable (Const := Const)
      (F.henkinizedAntecedentTheorySet
        (Base := Base) (Const := Const) exConst allConst)
      F.succedent :=
  F.not_henkinizedProvable_of_not_antecedentTheorySetProvable_of_finite
    (Base := Base) (Const := Const) exConst allConst
    (F.finiteHenkinImplicationConservative_of_oneStep
      (Base := Base) (Const := Const) exConst allConst hStep)
    hNot

/-- One-step finite Henkin implication elimination produces the prime
Henkin-implication separating extension directly from ordinary closed-theory
non-provability. -/
theorem nonempty_primeHenkinImplicationSeparatingExtension_of_not_antecedentTheorySetProvable_of_oneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    Nonempty (PrimeHenkinImplicationSeparatingExtension
      (Base := Base) (Const := Const) F) :=
  F.nonempty_primeHenkinImplicationSeparatingExtension_of_not_antecedentTheorySetProvable_of_finite
    (Base := Base) (Const := Const) exConst allConst
    (F.finiteHenkinImplicationConservative_of_oneStep
      (Base := Base) (Const := Const) exConst allConst hStep)
    hNot

/-- One-step finite Henkin implication elimination refutes native derivability
whenever the original closed antecedent theory-set does not prove the
succedent. -/
theorem not_derivable_of_not_antecedentTheorySetProvable_of_oneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  F.not_derivable_of_not_antecedentTheorySetProvable_of_finite
    (Base := Base) (Const := Const) exConst allConst
    (F.finiteHenkinImplicationConservative_of_oneStep
      (Base := Base) (Const := Const) exConst allConst hStep)
    hNot

/-- One-step finite Henkin implication elimination is also enough to refute
singleton-strength semantic consequence. -/
theorem not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_of_oneStep
    (F : CompletenessFrontier Const [])
    (exConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (allConst : ∀ {σ : Ty Base}, Formula Const [σ] → Const σ)
    (hStep :
      F.OneStepHenkinImplicationConservative
        (Base := Base) (Const := Const) exConst allConst)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
        F.antecedentTheorySet F.succedent) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  F.not_singletonStrengthConsequence_of_not_antecedentTheorySetProvable_of_finite
    (Base := Base) (Const := Const) exConst allConst
    (F.finiteHenkinImplicationConservative_of_oneStep
      (Base := Base) (Const := Const) exConst allConst hStep)
    hNot

end CompletenessFrontier

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
