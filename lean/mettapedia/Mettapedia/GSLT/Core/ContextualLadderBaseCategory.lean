import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mettapedia.GSLT.Core.ContextualLadder

/-!
# The base category of the contextual ladder

`ContextualLadder` constructs unityped, simply typed, and dependent
categories with families.  This file states the exact categorical content of
the word "inclusion" at their common waist:

* every rung has a category of contexts and substitutions;
* `Ucwf.toScwf` and `Scwf.toCwf` preserve that category on the nose;
* the resulting functors are fully faithful and compose on the nose;
* the dependent type fibre is nevertheless strictly larger than the
  constant-family image in the families model.

Thus the ladder identifies the structural base shared by the three typing
disciplines.  It does not identify their type fibres or assert an equivalence
between simple and dependent type theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

/-! ## A category presented by contexts and substitutions -/

/-- The context/substitution part common to `Ucwf`, `Scwf`, and `Cwf`. -/
structure ContextualBase : Type (max (u + 1) (v + 1)) where
  Ctx : Type u
  Sub : Ctx → Ctx → Type v
  idS : (Γ : Ctx) → Sub Γ Γ
  compS : {Γ Δ Θ : Ctx} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
  id_comp : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS (idS Δ) σ = σ
  comp_id : ∀ {Γ Δ : Ctx} (σ : Sub Γ Δ), compS σ (idS Γ) = σ
  comp_assoc : ∀ {Γ Δ Θ Ξ : Ctx} (σ : Sub Θ Ξ) (τ : Sub Δ Θ) (ρ : Sub Γ Δ),
      compS (compS σ τ) ρ = compS σ (compS τ ρ)

/-- Forget a dependent cwf down to its context/substitution base.  The base
is a reducible structural view, while its categorical normal forms are
controlled by the lemmas below. -/
abbrev Cwf.base (C : Cwf.{u, v, w, w'}) : ContextualBase.{u, v} where
  Ctx := C.Ctx
  Sub := C.Sub
  idS := C.idS
  compS := C.compS
  id_comp := C.id_comp
  comp_id := C.comp_id
  comp_assoc := C.comp_assoc

/-- Forget a simply typed cwf down to its context/substitution base. -/
def Scwf.base (S : Scwf.{u, v, w, w'}) : ContextualBase.{u, v} where
  Ctx := S.Ctx
  Sub := S.Sub
  idS := S.idS
  compS := S.compS
  id_comp := S.id_comp
  comp_id := S.comp_id
  comp_assoc := S.comp_assoc

/-- Forget a unityped cwf down to its context/substitution base. -/
def Ucwf.base (U : Ucwf.{u, v, w'}) : ContextualBase.{u, v} where
  Ctx := U.Ctx
  Sub := U.Sub
  idS := U.idS
  compS := U.compS
  id_comp := U.id_comp
  comp_id := U.comp_id
  comp_assoc := U.comp_assoc

namespace ContextualBase

/-- An object of the category presented by a contextual base. -/
@[ext]
structure Context (B : ContextualBase.{u, v}) where
  val : B.Ctx

/-- Contexts are objects and substitutions are arrows. -/
instance (B : ContextualBase.{u, v}) : Category.{v} B.Context where
  Hom Γ Δ := B.Sub Γ.val Δ.val
  id Γ := B.idS Γ.val
  comp σ τ := B.compS τ σ
  id_comp σ := B.comp_id σ
  comp_id σ := B.id_comp σ
  assoc ρ τ σ := (B.comp_assoc σ τ ρ).symm

/-- The categorical identity is the presented identity substitution. -/
theorem id_substitution (B : ContextualBase.{u, v}) (Γ : B.Context) :
    (𝟙 Γ : Γ ⟶ Γ) = B.idS Γ.val := rfl

/-- Categorical composition is the presented substitution composition, with
the categorical diagrammatic order made explicit. -/
theorem comp_substitution (B : ContextualBase.{u, v})
    {Γ Δ Θ : B.Context} (first : Γ ⟶ Δ) (second : Δ ⟶ Θ) :
    first ≫ second = B.compS second first := rfl

/-- Presented identity substitutions normalize to categorical identities. -/
@[simp]
theorem idS_eq_id (B : ContextualBase.{u, v}) (Γ : B.Context) :
    B.idS Γ.val = (𝟙 Γ : Γ ⟶ Γ) := rfl

/-- Presented substitution composition normalizes to categorical
composition. -/
@[simp]
theorem compS_eq_comp (B : ContextualBase.{u, v})
    {Γ Δ Θ : B.Context} (first : Γ ⟶ Δ) (second : Δ ⟶ Θ) :
    B.compS second first = first ≫ second := rfl

end ContextualBase

/-- At a CwF base, categorical identity is the specified identity
substitution.  This specialized bridge preserves the opacity of `Cwf.base`
for unrelated clients. -/
theorem Cwf.base_id_substitution (C : Cwf.{u, v, w, w'})
    (Γ : C.base.Context) :
    (𝟙 Γ : Γ ⟶ Γ) = C.idS Γ.val := rfl

/-- At a CwF base, categorical composition is the specified substitution
composition in diagrammatic order. -/
theorem Cwf.base_comp_substitution (C : Cwf.{u, v, w, w'})
    {Γ Δ Θ : C.base.Context} (first : Γ ⟶ Δ) (second : Δ ⟶ Θ) :
    first ≫ second = C.compS second first := rfl

/-- Specified CwF identities normalize to identities in the structural base
category. -/
@[simp]
theorem Cwf.idS_eq_base_id (C : Cwf.{u, v, w, w'})
    (Γ : C.base.Context) :
    C.idS Γ.val = (𝟙 Γ : Γ ⟶ Γ) := rfl

/-- Specified CwF substitution composition normalizes to composition in the
structural base category. -/
@[simp]
theorem Cwf.compS_eq_base_comp (C : Cwf.{u, v, w, w'})
    {Γ Δ Θ : C.base.Context} (first : Γ ⟶ Δ) (second : Δ ⟶ Θ) :
    C.compS second first = first ≫ second := rfl

/-! ## The common base is preserved fully faithfully -/

@[simp]
theorem Ucwf.toScwf_base (U : Ucwf.{u, v, w'}) :
    U.toScwf.base = U.base := rfl

@[simp]
theorem Scwf.toCwf_base (S : Scwf.{u, v, w, w'}) :
    S.toCwf.base = S.base := rfl

/-- Passing from unityped to simply typed syntax changes no context or
substitution. -/
def Ucwf.baseFunctor (U : Ucwf.{u, v, w'}) :
    U.base.Context ⥤ U.toScwf.base.Context where
  obj Γ := ⟨Γ.val⟩
  map σ := σ

/-- The unityped-to-simple base functor induces an equivalence on every hom
set. -/
def Ucwf.baseFunctorFullyFaithful (U : Ucwf.{u, v, w'}) :
    U.baseFunctor.FullyFaithful where
  preimage σ := σ

/-- Passing from simple to dependent typing changes no context or
substitution. -/
def Scwf.baseFunctor (S : Scwf.{u, v, w, w'}) :
    S.base.Context ⥤ S.toCwf.base.Context where
  obj Γ := ⟨Γ.val⟩
  map σ := σ

/-- The simple-to-dependent base functor induces an equivalence on every hom
set. -/
def Scwf.baseFunctorFullyFaithful (S : Scwf.{u, v, w, w'}) :
    S.baseFunctor.FullyFaithful where
  preimage σ := σ

/-- The direct base functor from a unityped cwf to its dependent image. -/
def Ucwf.baseToCwfFunctor (U : Ucwf.{u, v, w'}) :
    U.base.Context ⥤ U.toScwf.toCwf.base.Context where
  obj Γ := ⟨Γ.val⟩
  map σ := σ

/-- The two base inclusions compose exactly on context objects. -/
@[simp]
theorem Ucwf.baseFunctor_comp_obj (U : Ucwf.{u, v, w'})
    (Γ : U.base.Context) :
    U.toScwf.baseFunctor.obj (U.baseFunctor.obj Γ) =
      U.baseToCwfFunctor.obj Γ := rfl

/-- The two base inclusions compose exactly on substitutions. -/
@[simp]
theorem Ucwf.baseFunctor_comp_map (U : Ucwf.{u, v, w'})
    {Γ Δ : U.base.Context} (σ : Γ ⟶ Δ) :
    U.toScwf.baseFunctor.map (U.baseFunctor.map σ) =
      U.baseToCwfFunctor.map σ := rfl

/-! ## The type fibres do not collapse -/

/-- A family belongs to the simply typed image when it is constant over its
context. -/
def IsConstantFamily {Γ : Type w} (A : familiesCwf.Ty Γ) : Prop :=
  ∃ B : Type w, A = constantFamily B

/-- Constant families give the positive image witness. -/
theorem constantFamily_isConstant {Γ : Type w} (A : Type w) :
    IsConstantFamily (constantFamily (Γ := Γ) A) :=
  ⟨A, rfl⟩

/-- A small dependent family whose fibre genuinely varies with the context. -/
def varyingBoolFamily : familiesCwf.Ty Bool :=
  fun b => if b then PEmpty else PUnit

/-- The varying family cannot come from any simple type.  This is the
non-collapse witness complementing full faithfulness of the shared base. -/
theorem varyingBoolFamily_not_constant :
    ¬ IsConstantFamily varyingBoolFamily := by
  rintro ⟨A, hA⟩
  have hFalse : PUnit = A := by
    have h := congrFun hA false
    change PUnit = A at h
    exact h
  have hTrue : PEmpty = A := by
    have h := congrFun hA true
    change PEmpty = A at h
    exact h
  have hType : PUnit = PEmpty := hFalse.trans hTrue.symm
  have impossible : PEmpty := cast hType PUnit.unit
  exact nomatch impossible

/-- Consequently, constant families form a proper fragment of the dependent
families model. -/
theorem exists_dependent_family_outside_simple_image :
    ∃ A : familiesCwf.Ty Bool, ¬ IsConstantFamily A :=
  ⟨varyingBoolFamily, varyingBoolFamily_not_constant⟩

#print axioms Ucwf.baseFunctorFullyFaithful
#print axioms Scwf.baseFunctorFullyFaithful
#print axioms Ucwf.baseFunctor_comp_obj
#print axioms Ucwf.baseFunctor_comp_map
#print axioms varyingBoolFamily_not_constant
#print axioms exists_dependent_family_outside_simple_image

end Mettapedia.GSLT.Core.ContextualLadder
