import Mettapedia.Logic.HOL.CanonicalTheory

/-!
# Quantifier bridges for `ClosedTheorySet.Provable`

The canonical-model truth lemma needs the quantifier analogues of the existing
propositional `Provable` helpers (`provable_mp`, `provable_and_intro`, …).  This
file adds the two structural quantifier bridges that follow directly from the
`ExtDerivation` rules:

* `provable_all_elim`  — universal instantiation;
* `provable_ex_intro`  — existential introduction at a witness.

The harder fresh-constant generalization (`provable_all_intro_fresh`), which
turns a derivation over a fresh parameter into a universal statement, is built
here on top of the substitution machinery (`abstractConstAt_deriv`,
`abstractConstAt_instantiate`, `abstractConstAt_noOccurrence`).
-/

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Fresh-constant generalization (the syntactic core)

The Henkin / `∀`-introduction step: a derivation that proves `φ[c]` for a
parameter constant `c` that occurs nowhere else can be turned into a derivation
of `∀x. φ`.  Syntactically, `abstractConstAt c []` *abstracts* the constant back
into the freshly bound variable; the two facts below say this abstraction is the
exact inverse of the substitution we performed, leaving everything else fixed. -/

/-- Round-trip: abstracting the constant we just substituted recovers the body,
provided the constant did not already occur in it.  This is the syntactic heart
of fresh-parameter `∀`-introduction. -/
theorem abstractConstAt_nil_instantiate_const
    {Γ : Ctx Base} {σ τ : Ty Base} (c : Const σ)
    (φ : Term Const (σ :: Γ) τ) (hφ : NoConstOccurrence c φ) :
    abstractConstAt (Base := Base) c [] (instantiate (Base := Base) (.const c) φ) = φ := by
  rw [abstractConstAt_instantiate (c := c) (Γ := Γ) [] (.const c) φ,
      abstractConstAt_noOccurrence (c := c) [σ] φ hφ]
  -- `abstractConstAt c [] (.const c)` is exactly the freshly bound variable.
  have hconst : abstractConstAt (Base := Base) c [] (.const c)
      = (Term.var (varAtDepth (Γ := Γ) (σ := σ) []) : Term Const (σ :: Γ) σ) := by
    simp only [abstractConstAt]
    split
    · rfl
    · next heq => exact absurd trivial heq
  rw [hconst]
  -- The remaining goal is the pure renaming identity
  --   `instantiate (.var vz) (rename (insertRen [σ]) φ) = φ`.
  unfold instantiate
  exact (subst_rename _ _ φ).trans
    ((subst_ext (fun v => by cases v <;> rfl) φ).trans (subst_id φ))

/-- Fresh-parameter `∀`-introduction at the derivation level: if `c : Const σ`
occurs in neither the hypotheses `Δ` nor the body `φ`, then a derivation of the
instance `φ[c]` yields a derivation of `∀x. φ`. -/
theorem ExtDerivation.allI_fresh
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
    (c : Const σ) {φ : Formula Const (σ :: Γ)}
    (hΔ : ∀ ψ ∈ Δ, NoConstOccurrence c ψ)
    (hφ : NoConstOccurrence c φ)
    (d : ExtDerivation Const Δ (instantiate (Base := Base) (.const c) φ)) :
    ExtDerivation Const Δ (.all φ) := by
  have key := abstractConstAt_deriv (Γ := Γ) (Ξ := []) c d
  have hmap : Δ.map (abstractConstAt (Base := Base) c []) = weakenHyps (σ := σ) Δ := by
    rw [weakenHyps]
    apply List.map_congr_left
    intro ψ hψ
    exact abstractConstAt_noOccurrence (c := c) [] ψ (hΔ ψ hψ)
  rw [hmap] at key
  exact ExtDerivation.allI (abstractConstAt_nil_instantiate_const c φ hφ ▸ key)

namespace ClosedTheorySet

/-- Universal instantiation at a closed witness: from `∀x.φ` provable over `T`,
`φ[t]` is provable over `T`. -/
theorem provable_all_elim {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : Provable (Const := Const) T (.all φ)) :
    Provable (Const := Const) T (instantiate (Base := Base) t φ) := by
  rcases h with ⟨Γ, hΓ, hd⟩
  exact ⟨Γ, hΓ, ExtDerivation.allE (Base := Base) t hd⟩

/-- Existential introduction at a closed witness: from `φ[t]` provable over `T`,
`∃x.φ` is provable over `T`. -/
theorem provable_ex_intro {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : Provable (Const := Const) T (instantiate (Base := Base) t φ)) :
    Provable (Const := Const) T (.ex φ) := by
  rcases h with ⟨Γ, hΓ, hd⟩
  exact ⟨Γ, hΓ, ExtDerivation.exI (Base := Base) t hd⟩

/-- World-level universal elimination: if `∀x.φ ∈ W` then every instance is in `W`. -/
theorem World.all_elim_mem {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : (.all φ : ClosedFormula Const) ∈ W.carrier) :
    instantiate (Base := Base) t φ ∈ W.carrier := by
  apply World.mem_of_provable (W := W)
  exact provable_all_elim (Const := Const) t (provable_of_mem (Const := Const) h)

/-- World-level existential introduction: if some instance `φ[t] ∈ W` then `∃x.φ ∈ W`. -/
theorem World.ex_intro_mem {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (t : ClosedTerm Const σ)
    (h : instantiate (Base := Base) t φ ∈ W.carrier) :
    (.ex φ : ClosedFormula Const) ∈ W.carrier := by
  apply World.mem_of_provable (W := W)
  exact provable_ex_intro (Const := Const) t (provable_of_mem (Const := Const) h)

/-- Fresh-parameter universal introduction over a theory set: if a parameter
constant `c : Const σ` is fresh for the theory `T` and the body `φ`, then a proof
of the instance `φ[c]` over `T` yields a proof of `∀x. φ` over `T`.  This is the
quantifier analogue of `provable_mp` and the engine behind the canonical-model
`all_counterexample`/existence-property arguments. -/
theorem provable_all_intro_fresh {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (c : Const σ)
    (hT : ∀ ψ ∈ T, NoConstOccurrence c ψ)
    (hφ : NoConstOccurrence c φ)
    (h : Provable (Const := Const) T (instantiate (Base := Base) (.const c) φ)) :
    Provable (Const := Const) T (.all φ) := by
  rcases h with ⟨Γ, hΓ, hd⟩
  exact ⟨Γ, hΓ, ExtDerivation.allI_fresh c (fun ψ hψ => hT ψ (hΓ ψ hψ)) hφ hd⟩

/-! ## Quantifier membership over a world (truth-lemma quantifier core)

These two equivalences are the quantifier heart of the canonical term-model truth
lemma: a universal/existential closed formula is in the world exactly when its
closed-term *instances* are, so the truth lemma's `∀`/`∃` cases reduce to closed
representatives of the term-model domain — never to recursion on instantiated
formulas (which would hit the prop-quantification trap).  They use only the proven
`World` interface: `all_elim_mem` + the `all_counterexample` field for `∀`, and the
`exists_witness` field + `ex_intro_mem` for `∃`. -/

/-- `∀x.φ ∈ W` iff every closed-term instance `φ[t] ∈ W`. -/
theorem World.mem_all_iff {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} :
    (.all φ : ClosedFormula Const) ∈ W.carrier ↔
      ∀ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∈ W.carrier := by
  constructor
  · intro h t
    exact World.all_elim_mem (W := W) t h
  · intro h
    by_contra hnot
    obtain ⟨t, ht⟩ := W.all_counterexample hnot
    exact ht (h t)

/-- `∃x.φ ∈ W` iff some closed-term instance `φ[t] ∈ W`. -/
theorem World.mem_ex_iff {W : ClosedTheorySet.World Const}
    {σ : Ty Base} {φ : Formula Const [σ]} :
    (.ex φ : ClosedFormula Const) ∈ W.carrier ↔
      ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∈ W.carrier := by
  constructor
  · intro h
    exact W.exists_witness h
  · rintro ⟨t, ht⟩
    exact World.ex_intro_mem (W := W) t ht

end ClosedTheorySet
end Mettapedia.Logic.HOL
