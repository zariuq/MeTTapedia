import Mettapedia.OSLF.Syntax.IndexedRuleFiniteContexts
import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-!
# Finite-list presentation of operational contexts

The operational context category permits an arbitrary finite type of typed
variables. A presentation by a finite list of judgment labels gives a
universe-small source category when the judgment and rule signatures are
small. The comparison below keeps the actual free-tree substitution maps.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton

open Mettapedia.TypeTheory
open CategoryTheory
open CategoryTheory.Limits
open Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts

universe uIndex uShape

variable {Judgment : Type uIndex}
variable (P : IndexedPolynomial.{0, uIndex, uShape, 0}
  Unit (fun _ => Judgment))

/-- A finite typed variable context enumerated by a finite ordinal. -/
structure ListContext (P : IndexedPolynomial.{0, uIndex, uShape, 0}
    Unit (fun _ => Judgment)) where
  length : Nat
  label : Fin length → Judgment

/-- The enumerated variables as an operational context. -/
def toContext (Γ : ListContext P) : Context P where
  slots := fun judgment => Σ position : Fin Γ.length, PLift (Γ.label position = judgment)
  finite := by
    exact Finite.intro {
      toFun := fun ⟨_, position, _⟩ => position
      invFun := fun position => ⟨Γ.label position, position, ⟨rfl⟩⟩
      left_inv := by
        intro ⟨judgment, position, ⟨equal⟩⟩
        cases equal
        rfl
      right_inv := by intro position; rfl }

/-- An arrow substitutes a free rule tree for each variable of the target
finite-list context. -/
abbrev Hom (Γ Δ : ListContext P) : Type _ :=
  Substitution P (toContext P Γ) (toContext P Δ)

/-- Composition uses exactly the free-tree substitution of the full
operational context category. -/
noncomputable instance : Category (ListContext P) where
  Hom := Hom P
  id Γ := identity P (toContext P Γ)
  comp f g := compose P f g
  id_comp := by intro Γ Δ f; exact identity_comp P f
  comp_id := by intro Γ Δ f; exact comp_identity P f
  assoc := by intro Γ Δ Θ Ψ f g h; exact compose_assoc P f g h

/-- The finite-list presentation embeds by keeping each typed variable and
each free-tree substitution exactly. -/
noncomputable def inclusion : ListContext P ⥤ Context P where
  obj Γ := toContext P Γ
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (inclusion P).Full where
  map_surjective := fun f => ⟨f, rfl⟩

instance : (inclusion P).Faithful where
  map_injective := fun equal => equal

/-- The list presentation does not quotient or merge distinct firing-tree
arrows. -/
theorem inclusion_map_injective {Γ Δ : ListContext P} (f g : Γ ⟶ Δ)
    (equal : (inclusion P).map f = (inclusion P).map g) : f = g :=
  (inclusion P).map_injective equal

/-- Choose a finite enumeration of the variables of any operational context.
The choice only fixes an order; it does not identify variables. -/
noncomputable def enumerate (Γ : Context P) :
    Σ length : Nat, (Σ judgment, Γ.slots judgment) ≃ Fin length := by
  let h := @Finite.exists_equiv_fin
    (Σ judgment, Γ.slots judgment) Γ.finite
  exact ⟨Classical.choose h, Classical.choice (Classical.choose_spec h)⟩

/-- Present an arbitrary finite operational context by its enumerated
judgment labels. -/
noncomputable def fromContext (Γ : Context P) : ListContext P where
  length := (enumerate P Γ).1
  label position := ((enumerate P Γ).2.symm position).1

/-- Each enumerated typed position corresponds to exactly one variable in
the original context at the same judgment. -/
noncomputable def slotEquiv (Γ : Context P) (judgment : Judgment) :
    Γ.slots judgment ≃ (toContext P (fromContext P Γ)).slots judgment := by
  let e := (enumerate P Γ).2
  let encode : Γ.slots judgment →
      (toContext P (fromContext P Γ)).slots judgment :=
    fun value => ⟨e ⟨judgment, value⟩, ⟨by
      change (e.symm (e ⟨judgment, value⟩)).1 = judgment
      rw [Equiv.symm_apply_apply]⟩⟩
  apply Equiv.ofBijective encode
  constructor
  · intro first second equal
    have positions : e ⟨judgment, first⟩ =
        e ⟨judgment, second⟩ := congrArg Sigma.fst equal
    have elements := e.injective positions
    cases elements
    rfl
  · rintro ⟨position, ⟨equal⟩⟩
    rcases h : e.symm position with ⟨other, value⟩
    have same : other = judgment := by
      simpa only [fromContext, e, h] using equal
    cases same
    refine ⟨value, ?_⟩
    have positionEqual : (encode value).1 = position := by
      change e ⟨judgment, value⟩ = position
      simpa only [h] using e.apply_symm_apply position
    apply Sigma.ext
    · exact positionEqual
    · exact Subsingleton.helim
        (congrArg (fun index =>
          PLift ((fromContext P Γ).label index = judgment)) positionEqual)
        _ _

/-- Reindex variables to obtain an isomorphism of operational contexts,
with no change to the free rule trees except their leaf names. -/
noncomputable def contextIso (Γ : Context P) :
    (inclusion P).obj (fromContext P Γ) ≅ Γ where
  hom := fun judgment slot =>
    IndexedPolynomial.Free.pure P ((slotEquiv P Γ judgment) slot)
  inv := fun judgment slot =>
    IndexedPolynomial.Free.pure P ((slotEquiv P Γ judgment).symm slot)
  hom_inv_id := by
    funext judgment slot
    change (toContext P (fromContext P Γ)).slots judgment at slot
    change IndexedPolynomial.Free.bind P
      (fun _ index seed => IndexedPolynomial.Free.pure P
        ((slotEquiv P Γ index) seed)) PUnit.unit judgment
      (IndexedPolynomial.Free.pure P
        ((slotEquiv P Γ judgment).symm slot)) = _
    rw [IndexedPolynomial.Free.bind_pure]
    simp only [Equiv.apply_symm_apply]
    rfl
  inv_hom_id := by
    funext judgment slot
    change IndexedPolynomial.Free.bind P
      (fun _ index seed => IndexedPolynomial.Free.pure P
        ((slotEquiv P Γ index).symm seed)) PUnit.unit judgment
      (IndexedPolynomial.Free.pure P
        ((slotEquiv P Γ judgment) slot)) = _
    rw [IndexedPolynomial.Free.bind_pure]
    simp only [Equiv.symm_apply_apply]
    rfl

instance : (inclusion P).EssSurj where
  mem_essImage Γ := ⟨fromContext P Γ, ⟨contextIso P Γ⟩⟩

instance : (inclusion P).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Every finite operational context has a finite-list representative,
and the free-tree substitutions agree in both directions. -/
noncomputable def listEquivalence : ListContext P ≌ Context P :=
  (inclusion P).asEquivalence

/-- The small list presentation has all finite products because its
inclusion is an equivalence with the full finite-context category. -/
noncomputable instance : HasFiniteProducts (ListContext P) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence (inclusion P)⟩

/-- The enumeration comparison preserves the product structure used to
interpret simultaneous operational premises. -/
instance : PreservesFiniteProducts (inclusion P) := by
  infer_instance

section SmallPresentations

variable {SmallJudgment : Type}
variable (smallRules : IndexedPolynomial.{0, 0, 0, 0}
  Unit (fun _ => SmallJudgment))

/-- Small authored signatures give an actually small category of enumerated
operational contexts, the size required by the relative lex completion. -/
noncomputable instance : SmallCategory (ListContext smallRules) := inferInstance

/-- The existing relative finite-limit universal property now applies to
the small finite-list operational category. It includes interpretation
morphisms and does not assume that the target is a topos. -/
noncomputable def relativeLexClassification
    (D : Type) [SmallCategory D] [HasFiniteLimits D] :
    Mettapedia.OSLF.CartesianContextModels.LeftExactTargetInterpretations
        (ListContext smallRules) D ≌
      Mettapedia.OSLF.CartesianContextModels.CartesianTargetInterpretations
        (ListContext smallRules) D :=
  Mettapedia.OSLF.CartesianContextModels.cartesianTargetLexEquivalence
    (ListContext smallRules) D

end SmallPresentations

end Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
