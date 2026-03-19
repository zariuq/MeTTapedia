import Mettapedia.Logic.HOL.TruthLemma

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinConstInfinity

/-!
A companion canonical model layer for the cumulative Henkin language.

This file packages the already-built canonical worlds as a typed semantics
whose proposition values are upward-closed truth sets of worlds, while all
other semantic values are represented by closed terms in the cumulative Henkin
signature.

It is intentionally lighter-weight than
`/home/zar/claude/lean-projects/mettapedia/Mettapedia/Logic/HOL/Semantics/HeytingHenkin.lean`:
the current completeness path needs a typed canonical semantics first, and only
later a clean bridge into the total-function `HeytingHenkinModel` interface.
-/
/-- Canonical worlds over the cumulative Henkin signature. -/
abbrev World (Base : Type u) (Const : Ty Base → Type v) :=
  ClosedTheorySet.World (HInf Base Const)

/-- Canonical proposition truth values as upward-closed sets of worlds. -/
abbrev TruthVal (Base : Type u) (Const : Ty Base → Type v) :=
  OrderDual (ClosedTheorySet.World.TruthVal (HInf Base Const))

instance instSetLikeTruthVal :
    SetLike (TruthVal Base Const) (World Base Const) where
  coe s := ((show ClosedTheorySet.World.TruthVal (HInf Base Const) from s) :
    Set (World Base Const))
  coe_injective' := by
    intro s t h
    cases s
    cases t
    cases h
    rfl

/-- Closed substitutions into the cumulative Henkin signature. -/
abbrev ClosedSubst (Base : Type u) (Const : Ty Base → Type v) (Γ : Ctx Base) :=
  Subst (HInf Base Const) Γ []

/-- The unique closed substitution on the empty context. -/
abbrev emptyClosedSubst (Base : Type u) (Const : Ty Base → Type v) :
    ClosedSubst Base Const [] :=
  fun {_τ} v => nomatch v

/-- Extend a closed substitution with one more closed term. -/
def ClosedSubst.extend (σs : ClosedSubst Base Const Γ)
    (t : ClosedTerm (HInf Base Const) σ) :
    ClosedSubst Base Const (σ :: Γ)
  | _, .vz => t
  | _, .vs v => σs v

/--
Canonical semantic values:
- propositions are interpreted as truth values over canonical worlds,
- all other types are represented by closed terms in the cumulative signature.
-/
def Value (Base : Type u) (Const : Ty Base → Type v) :
    Ty Base → Type (max u (v + 1))
  | .prop => TruthVal Base Const
  | .base b => ClosedTerm (HInf Base Const) (.base b)
  | .arr σ τ => ClosedTerm (HInf Base Const) (.arr σ τ)

/-- Interpret a closed cumulative-Henkin term as a canonical semantic value. -/
def denoteClosed :
    {τ : Ty Base} →
      ClosedTerm (HInf Base Const) τ →
        Value Base Const τ
  | .prop, φ => ClosedTheorySet.World.truthSet (Const := HInf Base Const) φ
  | .base _, t => t
  | .arr _ _, t => t

/-- Interpret an open cumulative-Henkin term by first closing it with a substitution. -/
def denote :
    {Γ : Ctx Base} → {τ : Ty Base} →
      Term (HInf Base Const) Γ τ →
        ClosedSubst Base Const Γ →
          Value Base Const τ
  | _, _, t, σs => denoteClosed (Base := Base) (Const := Const) (subst σs t)

/-- Proposition-valued specialization of the canonical denotation. -/
abbrev denoteFormula {Γ : Ctx Base}
    (φ : Formula (HInf Base Const) Γ) (σs : ClosedSubst Base Const Γ) :
    TruthVal Base Const :=
  denote (Base := Base) (Const := Const) φ σs

/-- Canonical context semantics as the meet of the closed instantiated formulas. -/
def contextDenote {Γ : Ctx Base}
    (Δ : List (Formula (HInf Base Const) Γ)) (σs : ClosedSubst Base Const Γ) :
    TruthVal Base Const :=
  Δ.foldr (fun φ acc => denoteFormula (Base := Base) (Const := Const) φ σs ⊓ acc) ⊤

/-- Canonical entailment at a closed substitution. -/
def modelsFrom {Γ : Ctx Base}
    (Δ : List (Formula (HInf Base Const) Γ))
    (φ : Formula (HInf Base Const) Γ) (σs : ClosedSubst Base Const Γ) : Prop :=
  contextDenote (Base := Base) (Const := Const) Δ σs ≤
    denoteFormula (Base := Base) (Const := Const) φ σs

/-- Closed-formula validity in the canonical world semantics. -/
def models (φ : ClosedFormula (HInf Base Const)) : Prop :=
  denoteFormula (Base := Base) (Const := Const) φ (emptyClosedSubst Base Const) = ⊤

@[simp] theorem denoteClosed_prop
    (φ : ClosedFormula (HInf Base Const)) :
    denoteClosed (Base := Base) (Const := Const) (τ := .prop) φ =
      ClosedTheorySet.World.truthSet (Const := HInf Base Const) φ :=
  rfl

@[simp] theorem denoteClosed_base
    {b : Base} (t : ClosedTerm (HInf Base Const) (.base b)) :
    denoteClosed (Base := Base) (Const := Const) (τ := .base b) t = t :=
  rfl

@[simp] theorem denoteClosed_arr
    {σ τ : Ty Base} (t : ClosedTerm (HInf Base Const) (σ ⇒ τ)) :
    denoteClosed (Base := Base) (Const := Const) (τ := σ ⇒ τ) t = t :=
  rfl

@[simp] theorem denote_formula_eq_truthSet_subst
    {Γ : Ctx Base} (φ : Formula (HInf Base Const) Γ)
    (σs : ClosedSubst Base Const Γ) :
    denoteFormula (Base := Base) (Const := Const) φ σs =
      ClosedTheorySet.World.truthSet (Const := HInf Base Const) (subst σs φ) :=
  rfl

@[simp] theorem mem_denoteFormula_iff
    {Γ : Ctx Base} {W : World Base Const}
    {φ : Formula (HInf Base Const) Γ} {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) φ σs ↔
      subst σs φ ∈ W.carrier :=
  Iff.rfl

@[simp] theorem subst_emptyClosedSubst
    (φ : ClosedFormula (HInf Base Const)) :
    subst (emptyClosedSubst Base Const) φ = φ := by
  calc
    subst (emptyClosedSubst Base Const) φ
        =
        subst
          (Subst.id (Base := Base) (Const := HInf Base Const) (Γ := []))
          φ := by
            apply subst_ext
            intro τ v
            cases v
    _ = φ := subst_id (Base := Base) (Const := HInf Base Const) (t := φ)

@[simp] theorem subst_extend_eq_instantiate
    {Γ : Ctx Base} {σ : Ty Base}
    (φ : Formula (HInf Base Const) (σ :: Γ))
    (σs : ClosedSubst Base Const Γ)
    (t : ClosedTerm (HInf Base Const) σ) :
    subst (ClosedSubst.extend (Base := Base) (Const := Const) σs t) φ =
      instantiate (Base := Base) t
        (subst (Subst.lift (Base := Base) (σ := σ) σs) φ) := by
  calc
    subst (ClosedSubst.extend (Base := Base) (Const := Const) σs t) φ
        =
        subst
          (Subst.comp
            (Subst.single (Base := Base) (Const := HInf Base Const) t)
            (Subst.lift (Base := Base) (σ := σ) σs))
          φ := by
            apply subst_ext
            intro τ v
            cases v with
            | vz =>
                rfl
            | vs v =>
                simpa [ClosedSubst.extend, Subst.comp, instantiate, weaken] using
                  (instantiate_weaken
                    (Base := Base)
                    (Const := HInf Base Const)
                    (t := t)
                    (u := σs v)).symm
    _ =
        subst
          (Subst.single (Base := Base) (Const := HInf Base Const) t)
          (subst (Subst.lift (Base := Base) (σ := σ) σs) φ) := by
            symm
            exact subst_comp
              (Base := Base)
              (Const := HInf Base Const)
              (τs := Subst.single (Base := Base) (Const := HInf Base Const) t)
              (σs := Subst.lift (Base := Base) (σ := σ) σs)
              (t := φ)

@[simp] theorem mem_denoteFormula_extend_iff
    {Γ : Ctx Base} {σ : Ty Base} {W : World Base Const}
    {φ : Formula (HInf Base Const) (σ :: Γ)}
    {σs : ClosedSubst Base Const Γ}
    {t : ClosedTerm (HInf Base Const) σ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) φ
        (ClosedSubst.extend (Base := Base) (Const := Const) σs t) ↔
      instantiate (Base := Base) t
          (subst (Subst.lift (Base := Base) (σ := σ) σs) φ) ∈ W.carrier := by
  rw [mem_denoteFormula_iff]
  simp [subst_extend_eq_instantiate]

@[simp] theorem mem_denoteFormula_top_iff
    {Γ : Ctx Base} {W : World Base Const} {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const)
        (.top : Formula (HInf Base Const) Γ) σs := by
  simpa [denoteFormula, denote, subst] using
    (ClosedTheorySet.World.mem_truthSet_top_iff
      (Const := HInf Base Const)
      (W := W))

@[simp] theorem mem_denoteFormula_and_iff
    {Γ : Ctx Base} {W : World Base Const}
    {φ ψ : Formula (HInf Base Const) Γ}
    {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) (.and φ ψ) σs ↔
      W ∈ denoteFormula (Base := Base) (Const := Const) φ σs ∧
        W ∈ denoteFormula (Base := Base) (Const := Const) ψ σs := by
  simpa [denoteFormula, denote, subst, mem_denoteFormula_iff] using
    (ClosedTheorySet.World.mem_truthSet_and_iff
      (Const := HInf Base Const)
      (W := W)
      (φ := subst σs φ)
      (ψ := subst σs ψ))

@[simp] theorem mem_denoteFormula_or_iff
    {Γ : Ctx Base} {W : World Base Const}
    {φ ψ : Formula (HInf Base Const) Γ}
    {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) (.or φ ψ) σs ↔
      W ∈ denoteFormula (Base := Base) (Const := Const) φ σs ∨
        W ∈ denoteFormula (Base := Base) (Const := Const) ψ σs := by
  simpa [denoteFormula, denote, subst, mem_denoteFormula_iff] using
    (ClosedTheorySet.World.mem_truthSet_or_iff
      (Const := HInf Base Const)
      (W := W)
      (φ := subst σs φ)
      (ψ := subst σs ψ))

@[simp] theorem mem_denoteFormula_ex_iff
    {Γ : Ctx Base} {σ : Ty Base} {W : World Base Const}
    {φ : Formula (HInf Base Const) (σ :: Γ)}
    {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) (.ex φ) σs ↔
      ∃ t : ClosedTerm (HInf Base Const) σ,
        W ∈ denoteFormula (Base := Base) (Const := Const) φ
          (ClosedSubst.extend (Base := Base) (Const := Const) σs t) := by
  simpa [denoteFormula, denote, subst, mem_denoteFormula_extend_iff] using
    (ClosedTheorySet.World.mem_truthSet_ex_iff
      (Base := Base)
      (Const := HInf Base Const)
      (W := W)
      (σ := σ)
      (φ := subst (Subst.lift (Base := Base) (σ := σ) σs) φ))

@[simp] theorem mem_denoteFormula_all_iff
    {Γ : Ctx Base} {σ : Ty Base} {W : World Base Const}
    {φ : Formula (HInf Base Const) (σ :: Γ)}
    {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) (.all φ) σs ↔
      ∀ t : ClosedTerm (HInf Base Const) σ,
        W ∈ denoteFormula (Base := Base) (Const := Const) φ
          (ClosedSubst.extend (Base := Base) (Const := Const) σs t) := by
  simpa [denoteFormula, denote, subst, mem_denoteFormula_extend_iff] using
    (ClosedTheorySet.World.mem_truthSet_all_iff
      (Base := Base)
      (Const := HInf Base Const)
      (W := W)
      (σ := σ)
      (φ := subst (Subst.lift (Base := Base) (σ := σ) σs) φ))

theorem mem_denoteFormula_imp_iff
    {Γ : Ctx Base} {W : World Base Const}
    (hHenkin : HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier)
    {φ ψ : Formula (HInf Base Const) Γ}
    {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) (.imp φ ψ) σs ↔
      ∀ ⦃V : World Base Const⦄, W ≤ V →
        V ∈ denoteFormula (Base := Base) (Const := Const) φ σs →
          V ∈ denoteFormula (Base := Base) (Const := Const) ψ σs := by
  constructor
  · intro h V hWV hφV
    have hForces :
        ClosedTheorySet.World.ForcesImp (Const := HInf Base Const)
          W (subst σs φ) (subst σs ψ) := by
      simpa [denoteFormula, denote, subst, mem_denoteFormula_iff] using
        (forcesImp_iff_mem
          (Base := Base)
          (Const := Const)
          (W := W)
          (hHenkin := hHenkin)
          (φ := subst σs φ)
          (ψ := subst σs ψ)).2
          ((mem_denoteFormula_iff
            (Base := Base)
            (Const := Const)
            (W := W)
            (φ := (.imp φ ψ : Formula (HInf Base Const) Γ))
            (σs := σs)).1 h)
    exact (mem_denoteFormula_iff
      (Base := Base)
      (Const := Const)
      (W := V)
      (φ := ψ)
      (σs := σs)).2 <|
      hForces hWV ((mem_denoteFormula_iff
        (Base := Base)
        (Const := Const)
        (W := V)
        (φ := φ)
        (σs := σs)).1 hφV)
  · intro h
    have hForces :
        ClosedTheorySet.World.ForcesImp (Const := HInf Base Const)
          W (subst σs φ) (subst σs ψ) := by
      intro V hWV hφV
      exact (mem_denoteFormula_iff
        (Base := Base)
        (Const := Const)
        (W := V)
        (φ := ψ)
        (σs := σs)).1 <|
        h hWV ((mem_denoteFormula_iff
          (Base := Base)
          (Const := Const)
          (W := V)
          (φ := φ)
          (σs := σs)).2 hφV)
    exact (mem_denoteFormula_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (φ := (.imp φ ψ : Formula (HInf Base Const) Γ))
      (σs := σs)).2 <|
      (forcesImp_iff_mem
        (Base := Base)
        (Const := Const)
        (W := W)
        (hHenkin := hHenkin)
        (φ := subst σs φ)
        (ψ := subst σs ψ)).1 hForces

theorem mem_denoteFormula_not_iff
    {Γ : Ctx Base} {W : World Base Const}
    (hHenkin : HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier)
    {φ : Formula (HInf Base Const) Γ}
    {σs : ClosedSubst Base Const Γ} :
    W ∈ denoteFormula (Base := Base) (Const := Const) (.not φ) σs ↔
      ∀ ⦃V : World Base Const⦄, W ≤ V →
        V ∉ denoteFormula (Base := Base) (Const := Const) φ σs := by
  constructor
  · intro h V hWV hφV
    have hForces :
        ClosedTheorySet.World.ForcesNot (Const := HInf Base Const) W (subst σs φ) := by
      simpa [denoteFormula, denote, subst, mem_denoteFormula_iff] using
        (forcesNot_iff_mem
          (Base := Base)
          (Const := Const)
          (W := W)
          (hHenkin := hHenkin)
          (φ := subst σs φ)).2
          ((mem_denoteFormula_iff
            (Base := Base)
            (Const := Const)
            (W := W)
            (φ := (.not φ : Formula (HInf Base Const) Γ))
            (σs := σs)).1 h)
    exact hForces hWV ((mem_denoteFormula_iff
      (Base := Base)
      (Const := Const)
      (W := V)
      (φ := φ)
      (σs := σs)).1 hφV)
  · intro h
    have hForces :
        ClosedTheorySet.World.ForcesNot (Const := HInf Base Const) W (subst σs φ) := by
      intro V hWV hφV
      exact h hWV ((mem_denoteFormula_iff
        (Base := Base)
        (Const := Const)
        (W := V)
        (φ := φ)
        (σs := σs)).2 hφV)
    exact (mem_denoteFormula_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (φ := (.not φ : Formula (HInf Base Const) Γ))
      (σs := σs)).2 <|
      (forcesNot_iff_mem
        (Base := Base)
        (Const := Const)
        (W := W)
        (hHenkin := hHenkin)
        (φ := subst σs φ)).1 hForces

theorem exists_canonical_counterworld_of_notProvable
    {T : ClosedTheorySet (HInf Base Const)}
    {φ : ClosedFormula (HInf Base Const)}
    (hHenkin : HenkinAxioms (Base := Base) (Const := Const) ⊆ T)
    (hNot : ¬ ClosedTheorySet.Provable (Const := HInf Base Const) T φ) :
    ∃ W : World Base Const,
      (∀ {ψ : ClosedFormula (HInf Base Const)},
          ψ ∈ T →
            W ∈ denoteFormula (Base := Base) (Const := Const) ψ
              (emptyClosedSubst Base Const)) ∧
      HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier ∧
      W ∉ denoteFormula (Base := Base) (Const := Const) φ
        (emptyClosedSubst Base Const) := by
  rcases exists_world_separating_of_notProvable
      (Base := Base)
      (Const := Const)
      (T := T)
      (φ := φ)
      hHenkin
      hNot with
    ⟨W, hExt, hHenkinW, hOmit⟩
  refine ⟨W, ?_, hHenkinW, ?_⟩
  · intro ψ hψ
    exact (mem_denoteFormula_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (φ := ψ)
      (σs := emptyClosedSubst Base Const)).2 <|
      by simpa [subst_emptyClosedSubst] using hExt hψ
  · exact (mem_denoteFormula_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (φ := φ)
      (σs := emptyClosedSubst Base Const)).not.2 <|
      by simpa [subst_emptyClosedSubst] using hOmit

theorem exists_canonical_counterworld_of_list_notProvable
    {Δ : List (ClosedFormula (HInf Base Const))}
    {φ : ClosedFormula (HInf Base Const)}
    (hNot :
      ¬ ClosedTheorySet.Provable
          (Const := HInf Base Const)
          (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
          φ) :
    ∃ W : World Base Const,
      (∀ {ψ : ClosedFormula (HInf Base Const)},
          ψ ∈ Δ →
            W ∈ denoteFormula (Base := Base) (Const := Const) ψ
              (emptyClosedSubst Base Const)) ∧
      HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier ∧
      W ∉ denoteFormula (Base := Base) (Const := Const) φ
        (emptyClosedSubst Base Const) := by
  rcases exists_canonical_counterworld_of_notProvable
      (Base := Base)
      (Const := Const)
      (T := fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
      (φ := φ)
      (hHenkin := by
        intro ψ hψ
        exact Or.inr hψ)
      hNot with
    ⟨W, hΔW, hHenkinW, hNotW⟩
  refine ⟨W, ?_, hHenkinW, hNotW⟩
  intro ψ hψ
  exact hΔW (Or.inl hψ)

@[simp] theorem contextDenote_nil
    {Γ : Ctx Base} (σs : ClosedSubst Base Const Γ) :
    contextDenote (Base := Base) (Const := Const) [] σs = ⊤ :=
  rfl

@[simp] theorem contextDenote_cons
    {Γ : Ctx Base} (φ : Formula (HInf Base Const) Γ)
    (Δ : List (Formula (HInf Base Const) Γ)) (σs : ClosedSubst Base Const Γ) :
    contextDenote (Base := Base) (Const := Const) (φ :: Δ) σs =
      denoteFormula (Base := Base) (Const := Const) φ σs ⊓
        contextDenote (Base := Base) (Const := Const) Δ σs :=
  rfl

theorem contextDenote_le_of_mem
    {Γ : Ctx Base} {Δ : List (Formula (HInf Base Const) Γ)}
    {φ : Formula (HInf Base Const) Γ} (σs : ClosedSubst Base Const Γ)
    (hφ : φ ∈ Δ) :
    contextDenote (Base := Base) (Const := Const) Δ σs ≤
      denoteFormula (Base := Base) (Const := Const) φ σs := by
  induction Δ with
  | nil =>
      cases hφ
  | cons ψ Δ ih =>
      rw [contextDenote_cons]
      rw [List.mem_cons] at hφ
      rcases hφ with rfl | hφ
      · exact inf_le_left
      · exact le_trans inf_le_right (ih hφ)

@[simp] theorem mem_contextDenote_iff
    {Γ : Ctx Base} {W : World Base Const}
    {Δ : List (Formula (HInf Base Const) Γ)} {σs : ClosedSubst Base Const Γ} :
    W ∈ contextDenote (Base := Base) (Const := Const) Δ σs ↔
      ∀ φ : Formula (HInf Base Const) Γ,
        φ ∈ Δ →
          W ∈ denoteFormula (Base := Base) (Const := Const) φ σs := by
  induction Δ with
  | nil =>
      constructor
      · intro _ φ hφ
        cases hφ
      · intro _
        change W ∈ ((⊥ : ClosedTheorySet.World.TruthVal (HInf Base Const)) :
          TruthVal Base Const)
        simp
  | cons ψ Δ ih =>
      constructor
      · intro h φ hφ
        rw [contextDenote_cons] at h
        rw [List.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · simpa using h.1
        · exact (ih.mp h.2) φ hφ
      · intro h
        rw [contextDenote_cons]
        refine ⟨?_, ?_⟩
        · exact h ψ (by simp)
        · apply ih.mpr
          intro φ hφ
          exact h φ (by simp [hφ])

theorem not_modelsFrom_of_mem_contextDenote_of_not_mem
    {Γ : Ctx Base} {W : World Base Const}
    {Δ : List (Formula (HInf Base Const) Γ)}
    {φ : Formula (HInf Base Const) Γ}
    {σs : ClosedSubst Base Const Γ}
    (hΔ : W ∈ contextDenote (Base := Base) (Const := Const) Δ σs)
    (hφ : W ∉ denoteFormula (Base := Base) (Const := Const) φ σs) :
    ¬ modelsFrom (Base := Base) (Const := Const) Δ φ σs := by
  intro hmodels
  exact hφ (hmodels hΔ)

theorem exists_canonical_counterexample_of_list_notProvable
    {Δ : List (ClosedFormula (HInf Base Const))}
    {φ : ClosedFormula (HInf Base Const)}
    (hNot :
      ¬ ClosedTheorySet.Provable
          (Const := HInf Base Const)
          (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
          φ) :
    ∃ W : World Base Const,
      W ∈ contextDenote (Base := Base) (Const := Const) Δ
        (emptyClosedSubst Base Const) ∧
      W ∉ denoteFormula (Base := Base) (Const := Const) φ
        (emptyClosedSubst Base Const) := by
  rcases exists_canonical_counterworld_of_list_notProvable
      (Base := Base)
      (Const := Const)
      (Δ := Δ)
      (φ := φ)
      hNot with
    ⟨W, hΔW, _hHenkinW, hNotW⟩
  refine ⟨W, ?_, hNotW⟩
  apply (mem_contextDenote_iff
    (Base := Base)
    (Const := Const)
    (W := W)
    (Δ := Δ)
    (σs := emptyClosedSubst Base Const)).2
  intro ψ hψ
  exact hΔW hψ

theorem exists_canonical_countermodel_of_list_notProvable
    {Δ : List (ClosedFormula (HInf Base Const))}
    {φ : ClosedFormula (HInf Base Const)}
    (hNot :
      ¬ ClosedTheorySet.Provable
          (Const := HInf Base Const)
          (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
          φ) :
    ∃ W : World Base Const,
      W ∈ contextDenote (Base := Base) (Const := Const) Δ
        (emptyClosedSubst Base Const) ∧
      ¬ modelsFrom (Base := Base) (Const := Const) Δ φ
        (emptyClosedSubst Base Const) := by
  rcases exists_canonical_counterexample_of_list_notProvable
      (Base := Base)
      (Const := Const)
      (Δ := Δ)
      (φ := φ)
      hNot with
    ⟨W, hΔW, hNotW⟩
  refine ⟨W, hΔW, ?_⟩
  exact not_modelsFrom_of_mem_contextDenote_of_not_mem
    (Base := Base)
    (Const := Const)
    (W := W)
    (Δ := Δ)
    (φ := φ)
    (σs := emptyClosedSubst Base Const)
    hΔW
    hNotW

theorem mem_truthSet_of_theorem
    {φ : ClosedFormula (HInf Base Const)}
    (hφ : ExtDerivation.Theorem (HInf Base Const) φ)
    (W : World Base Const) :
    W ∈ ClosedTheorySet.World.truthSet (Const := HInf Base Const) φ := by
  apply W.mem_of_provable
  refine ClosedTheorySet.provable_of_closedTheory
    (Const := HInf Base Const)
    (T := W.carrier)
    (Δ := [])
    ?_ hφ
  intro ψ hψ
  cases hψ

theorem mem_eq_refl
    {τ : Ty Base} (t : ClosedTerm (HInf Base Const) τ) (W : World Base Const) :
    W ∈ ClosedTheorySet.World.truthSet (Const := HInf Base Const) (.eq t t) :=
  mem_truthSet_of_theorem (Base := Base) (Const := Const) (.eqRefl t) W

theorem mem_eq_symm
    {τ : Ty Base} {t u : ClosedTerm (HInf Base Const) τ}
    (h : ExtDerivation.Theorem (HInf Base Const) (.eq t u))
    (W : World Base Const) :
    W ∈ ClosedTheorySet.World.truthSet (Const := HInf Base Const) (.eq u t) :=
  mem_truthSet_of_theorem (Base := Base) (Const := Const) (.eqSymm h) W

theorem mem_eq_trans
    {τ : Ty Base} {t u v : ClosedTerm (HInf Base Const) τ}
    (htu : ExtDerivation.Theorem (HInf Base Const) (.eq t u))
    (huv : ExtDerivation.Theorem (HInf Base Const) (.eq u v))
    (W : World Base Const) :
    W ∈ ClosedTheorySet.World.truthSet (Const := HInf Base Const) (.eq t v) :=
  mem_truthSet_of_theorem (Base := Base) (Const := Const) (.eqTrans htu huv) W

end HenkinConstInfinity

end Mettapedia.Logic.HOL
