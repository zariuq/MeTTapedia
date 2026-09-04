/-!
# The contextual ladder: unityped to simply typed to dependent

This module isolates the common context-and-substitution algebra of unityped,
simply typed, and dependent disciplines.  It gives canonical structure maps
between the three interfaces.  In particular, `Scwf.toCwf` sends a simple
type to a context-constant dependent family, for which substitution casts are
definitionally trivial.

This identifies the shared structural waist; it does not identify the type
fibres or assert that simple and dependent type theory are equivalent.  The
categorical base theorem and a strict non-collapse witness are in
`ContextualLadderBaseCategory`.

Ladder (each arrow preserves contexts, substitutions, terms on the nose):

```
Ucwf ──toScwf──▶ Scwf ──toCwf──▶ Cwf
```

Instances: the set-families models `unitypedFamilies V`, `simpleFamilies`,
`familiesCwf`, with `constantFamily_tm` showing that the simply typed image
inside the dependent model is exactly the constant families.  The syntactic
face of `Scwf.toCwf` is `Logic/HOL/Embedding/SimpleSliceOfDependent`
(HOL as the non-dependent slice of a dependent core).

Terminology follows Castellan–Clairambault–Dybjer (ucwf/scwf/cwf).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

/-! ## Dependent: the substitution/comprehension core of a CwF -/

/-- The substitution/comprehension core of a category with families, stated
concretely: contexts, substitutions, context-indexed types with a
substitution action, typed terms, and context comprehension with its β and η
laws.  The chosen terminal context required by the standard definition is
packaged separately in `ContextualLadderTerminal.CwfWithTerminal`, so the
existing terminal-free interface remains reusable. -/
structure Cwf : Type (max (u + 1) (v + 1) (w + 1) (w' + 1)) where
  Ctx : Type u
  Sub : Ctx → Ctx → Type v
  idS : (Γ : Ctx) → Sub Γ Γ
  compS : {Γ Δ Θ : Ctx} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  id_comp : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS (idS Δ) σ = σ
  comp_id : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS σ (idS Γ) = σ
  comp_assoc : ∀ {Γ Δ Θ Ξ : Ctx} (σ : Sub Θ Ξ) (τ : Sub Δ Θ) (ρ : Sub Γ Δ),
      compS (compS σ τ) ρ = compS σ (compS τ ρ)
  Ty : Ctx → Type w
  tySub : {Γ Δ : Ctx} → Ty Δ → Sub Γ Δ → Ty Γ
  tySub_id : ∀ {Γ : Ctx} (A : Ty Γ), tySub A (idS Γ) = A
  tySub_comp : ∀ {Γ Δ Θ : Ctx} (A : Ty Θ) (σ : Sub Δ Θ) (τ : Sub Γ Δ),
      tySub A (compS σ τ) = tySub (tySub A σ) τ
  Tm : (Γ : Ctx) → Ty Γ → Type w'
  tmSub : {Γ Δ : Ctx} → {A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (tySub A σ)
  tmSub_id : ∀ {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A),
      tmSub t (idS Γ) = cast (by rw [tySub_id]) t
  tmSub_comp : ∀ {Γ Δ Θ : Ctx} {A : Ty Θ} (t : Tm Θ A) (σ : Sub Δ Θ) (τ : Sub Γ Δ),
      tmSub t (compS σ τ) = cast (by rw [tySub_comp]) (tmSub (tmSub t σ) τ)
  ext : (Γ : Ctx) → Ty Γ → Ctx
  wk : ∀ {Γ : Ctx} (A : Ty Γ), Sub (ext Γ A) Γ
  vz : ∀ {Γ : Ctx} (A : Ty Γ), Tm (ext Γ A) (tySub A (wk A))
  pair : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty Δ), Tm Γ (tySub A σ) → Sub Γ (ext Δ A)
  wk_pair : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty Δ) (t : Tm Γ (tySub A σ)),
      compS (wk A) (pair σ A t) = σ
  vz_pair : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty Δ) (t : Tm Γ (tySub A σ)),
      tmSub (vz A) (pair σ A t) =
        cast (by rw [← tySub_comp, wk_pair]) t
  pair_eta : ∀ {Γ Δ : Ctx} (A : Ty Δ) (σ' : Sub Γ (ext Δ A)),
      pair (compS (wk A) σ') A (cast (by rw [← tySub_comp]) (tmSub (vz A) σ')) = σ'

/-! ## Simply typed: types ignore the context -/

/-- The terminal-free core of a simply typed cwf: one fixed set of types, no
substitution action on them, hence no casts anywhere. -/
structure Scwf : Type (max (u + 1) (v + 1) (w + 1) (w' + 1)) where
  Ctx : Type u
  Sub : Ctx → Ctx → Type v
  idS : (Γ : Ctx) → Sub Γ Γ
  compS : {Γ Δ Θ : Ctx} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  id_comp : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS (idS Δ) σ = σ
  comp_id : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS σ (idS Γ) = σ
  comp_assoc : ∀ {Γ Δ Θ Ξ : Ctx} (σ : Sub Θ Ξ) (τ : Sub Δ Θ) (ρ : Sub Γ Δ),
      compS (compS σ τ) ρ = compS σ (compS τ ρ)
  Ty : Type w
  Tm : Ctx → Ty → Type w'
  tmSub : {Γ Δ : Ctx} → {A : Ty} → Tm Δ A → Sub Γ Δ → Tm Γ A
  tmSub_id : ∀ {Γ : Ctx} {A : Ty} (t : Tm Γ A), tmSub t (idS Γ) = t
  tmSub_comp : ∀ {Γ Δ Θ : Ctx} {A : Ty} (t : Tm Θ A) (σ : Sub Δ Θ) (τ : Sub Γ Δ),
      tmSub t (compS σ τ) = tmSub (tmSub t σ) τ
  ext : Ctx → Ty → Ctx
  wk : ∀ {Γ : Ctx} (A : Ty), Sub (ext Γ A) Γ
  vz : ∀ {Γ : Ctx} (A : Ty), Tm (ext Γ A) A
  pair : ∀ {Γ Δ : Ctx} (_σ : Sub Γ Δ) (A : Ty), Tm Γ A → Sub Γ (ext Δ A)
  wk_pair : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty) (t : Tm Γ A),
      compS (wk A) (pair σ A t) = σ
  vz_pair : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty) (t : Tm Γ A),
      tmSub (vz A) (pair σ A t) = t
  pair_eta : ∀ {Γ Δ : Ctx} (A : Ty) (σ' : Sub Γ (ext Δ A)),
      pair (compS (wk A) σ') A (tmSub (vz A) σ') = σ'

/-! ## Unityped: one implicit type -/

/-- The terminal-free core of a unityped cwf: contexts, substitutions, and
raw terms — the rewrite layer's shape. -/
structure Ucwf : Type (max (u + 1) (v + 1) (w' + 1)) where
  Ctx : Type u
  Sub : Ctx → Ctx → Type v
  idS : (Γ : Ctx) → Sub Γ Γ
  compS : {Γ Δ Θ : Ctx} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  id_comp : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS (idS Δ) σ = σ
  comp_id : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS σ (idS Γ) = σ
  comp_assoc : ∀ {Γ Δ Θ Ξ : Ctx} (σ : Sub Θ Ξ) (τ : Sub Δ Θ) (ρ : Sub Γ Δ),
      compS (compS σ τ) ρ = compS σ (compS τ ρ)
  Tm : Ctx → Type w'
  tmSub : {Γ Δ : Ctx} → Tm Δ → Sub Γ Δ → Tm Γ
  tmSub_id : ∀ {Γ : Ctx} (t : Tm Γ), tmSub t (idS Γ) = t
  tmSub_comp : ∀ {Γ Δ Θ : Ctx} (t : Tm Θ) (σ : Sub Δ Θ) (τ : Sub Γ Δ),
      tmSub t (compS σ τ) = tmSub (tmSub t σ) τ
  ext : Ctx → Ctx
  wk : ∀ {Γ : Ctx}, Sub (ext Γ) Γ
  vz : ∀ {Γ : Ctx}, Tm (ext Γ)
  pair : ∀ {Γ Δ : Ctx}, Sub Γ Δ → Tm Γ → Sub Γ (ext Δ)
  wk_pair : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) (t : Tm Γ), compS wk (pair σ t) = σ
  vz_pair : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ) (t : Tm Γ), tmSub vz (pair σ t) = t
  pair_eta : ∀ {Γ Δ : Ctx} (σ' : Sub Γ (ext Δ)),
      pair (compS wk σ') (tmSub vz σ') = σ'

/-! ## The ladder structure maps -/

/-- Every unityped structure is a simply typed one with a single type.
Contexts, substitutions, and terms are unchanged. -/
def Ucwf.toScwf (U : Ucwf.{u, v, w'}) : Scwf.{u, v, w, w'} where
  Ctx := U.Ctx
  Sub := U.Sub
  idS := U.idS
  compS := U.compS
  id_comp := U.id_comp
  comp_id := U.comp_id
  comp_assoc := U.comp_assoc
  Ty := PUnit
  Tm Γ _ := U.Tm Γ
  tmSub := fun t σ => U.tmSub t σ
  tmSub_id := U.tmSub_id
  tmSub_comp := U.tmSub_comp
  ext Γ _ := U.ext Γ
  wk _ := U.wk
  vz _ := U.vz
  pair σ _ t := U.pair σ t
  wk_pair σ _ t := U.wk_pair σ t
  vz_pair σ _ t := U.vz_pair σ t
  pair_eta _ σ' := U.pair_eta σ'

/-- Embed a simply typed structure into the dependent interface using
context-constant, substitution-inert type families.  Every cast demanded by
the dependent interface becomes `cast rfl`.  This is the constant-family
fragment; dependent structures may also contain genuinely varying types. -/
def Scwf.toCwf (S : Scwf.{u, v, w, w'}) : Cwf.{u, v, w, w'} where
  Ctx := S.Ctx
  Sub := S.Sub
  idS := S.idS
  compS := S.compS
  id_comp := S.id_comp
  comp_id := S.comp_id
  comp_assoc := S.comp_assoc
  Ty _ := S.Ty
  tySub A _ := A
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm := S.Tm
  tmSub := S.tmSub
  tmSub_id t := S.tmSub_id t
  tmSub_comp := S.tmSub_comp
  ext := S.ext
  wk := S.wk
  vz := S.vz
  pair := S.pair
  wk_pair := S.wk_pair
  vz_pair := S.vz_pair
  pair_eta := S.pair_eta

/-! ## The families models: all three rungs inhabited by one idea -/

/-- The dependent set-families model: contexts are types, types are families,
terms are sections. -/
def familiesCwf : Cwf.{w + 1, w, w + 1, w} where
  Ctx := Type w
  Sub Γ Δ := Γ → Δ
  idS _ := fun γ => γ
  compS σ τ := fun γ => σ (τ γ)
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty Γ := Γ → Type w
  tySub A σ := fun γ => A (σ γ)
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm Γ A := ∀ γ : Γ, A γ
  tmSub t σ := fun γ => t (σ γ)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext Γ A := Σ γ : Γ, A γ
  wk _ := fun p => p.1
  vz _ := fun p => p.2
  pair σ _ t := fun γ => ⟨σ γ, t γ⟩
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ _ := rfl

/-- The simply typed families model: terms are plain functions. -/
def simpleFamilies : Scwf.{w + 1, w, w + 1, w} where
  Ctx := Type w
  Sub Γ Δ := Γ → Δ
  idS _ := fun γ => γ
  compS σ τ := fun γ => σ (τ γ)
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty := Type w
  Tm Γ A := Γ → A
  tmSub t σ := fun γ => t (σ γ)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext Γ A := Γ × A
  wk _ := fun p => p.1
  vz _ := fun p => p.2
  pair σ _ t := fun γ => (σ γ, t γ)
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ _ := rfl

/-- The unityped families model over a fixed value carrier `V`. -/
def unitypedFamilies (V : Type w) : Ucwf.{w + 1, w, w} where
  Ctx := Type w
  Sub Γ Δ := Γ → Δ
  idS _ := fun γ => γ
  compS σ τ := fun γ => σ (τ γ)
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Tm Γ := Γ → V
  tmSub t σ := fun γ => t (σ γ)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext Γ := Γ × V
  wk := fun p => p.1
  vz := fun p => p.2
  pair σ t := fun γ => (σ γ, t γ)
  wk_pair _ _ := rfl
  vz_pair _ _ := rfl
  pair_eta _ := rfl

/-! ## The simply typed image inside the dependent model -/

/-- A simple type, viewed in the dependent model, is a constant family. -/
def constantFamily {Γ : Type w} (A : Type w) : familiesCwf.Ty Γ :=
  fun _ => A

/-- On constant families, dependent terms are exactly the simply typed ones. -/
theorem constantFamily_tm (Γ A : Type w) :
    familiesCwf.Tm Γ (constantFamily A) = simpleFamilies.Tm Γ A := rfl

/-- Constant families are substitution-inert: the dependent action collapses
to the simply typed (absent) one. -/
theorem constantFamily_sub {Γ Δ : Type w} (A : Type w)
    (σ : familiesCwf.Sub Γ Δ) :
    familiesCwf.tySub (constantFamily A) σ = constantFamily A := rfl

/-- Term substitution agrees on the nose across the inclusion. -/
theorem constantFamily_tmSub {Γ Δ : Type w} (A : Type w)
    (t : familiesCwf.Tm Δ (constantFamily A)) (σ : familiesCwf.Sub Γ Δ) :
    familiesCwf.tmSub (A := constantFamily A) t σ =
      simpleFamilies.tmSub (A := A) t σ := rfl

/-- The ladder composes, and each rung preserves terms definitionally: the
unityped families model, pushed up both inclusions, has exactly its original
terms. -/
theorem ladder_composes (V : Type w) (Γ : Type w) :
    ((unitypedFamilies V).toScwf.toCwf).Tm Γ PUnit.unit = (Γ → V) := rfl

#print axioms Scwf.toCwf
#print axioms Ucwf.toScwf
#print axioms familiesCwf
#print axioms constantFamily_tm
#print axioms ladder_composes

end Mettapedia.GSLT.Core.ContextualLadder
