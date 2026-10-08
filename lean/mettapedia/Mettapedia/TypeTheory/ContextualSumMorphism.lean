import Mettapedia.TypeTheory.ContextualLogicalMorphism

/-!
# Full-motive sum elimination under contextual morphisms

The two context presentations are compared using actual image context
equalities. Local formation and pairing preservation earn the packing
square. The inverse square and elimination law follow from the proved
packing inverse equations and term substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLogicalMorphism

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u v w w'

variable {C D : CwfWithTerminal.{u, v, w, w'}}

theorem sum_contexts (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    context F (sumContext source A B) = sumContext target A' B' :=
  extension_images F contexts (preserves.formation contexts domains codomains)

/-- Both independently constructed packing maps have the same projection
and newest-variable readings after translation. -/
theorem pack_square (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    F.toFamilyMorphism.base.map (pack source A B) ≫
        eqToHom (ContextualBase.Context.ext (sum_contexts F source target preserves contexts domains codomains)) =
      eqToHom (ContextualBase.Context.ext (tuple_contexts F contexts domains codomains)) ≫
        pack target A' B' := by
  let tupleEq := ContextualBase.Context.ext (tuple_contexts F contexts domains codomains)
  let sumEq := ContextualBase.Context.ext (sum_contexts F source target preserves contexts domains codomains)
  let baseEq := ContextualBase.Context.ext contexts
  let oldPack := F.toFamilyMorphism.base.map (pack source A B)
  let newPack := pack target A' B'
  have formation := preserves.formation contexts domains codomains
  have projectionRead := (projection_heq F Γ (source.operations.sigma A B)).trans
    (wk_heq contexts formation)
  have projection := diagram_of_heq sumEq baseEq
    (F.toFamilyMorphism.base.map (C.toCwf.wk (source.operations.sigma A B)))
    (D.toCwf.wk (target.operations.sigma A' B')) projectionRead
  have bases := diagram_of_heq tupleEq baseEq
    (F.toFamilyMorphism.base.map (C.toCwf.compS (C.toCwf.wk A) (C.toCwf.wk B)))
    (D.toCwf.compS (D.toCwf.wk A') (D.toCwf.wk B'))
    (tuple_base_heq F contexts domains codomains)
  apply TypeOver.substitution_ext
  · change (oldPack ≫ eqToHom sumEq) ≫ D.toCwf.wk (target.operations.sigma A' B') =
      (eqToHom tupleEq ≫ newPack) ≫ D.toCwf.wk (target.operations.sigma A' B')
    calc
      _ = oldPack ≫ (eqToHom sumEq ≫ D.toCwf.wk (target.operations.sigma A' B')) :=
        Category.assoc _ _ _
      _ = oldPack ≫ F.toFamilyMorphism.base.map
          (C.toCwf.wk (source.operations.sigma A B)) ≫ eqToHom baseEq := by rw [← projection]
      _ = F.toFamilyMorphism.base.map
          (C.toCwf.compS (C.toCwf.wk (source.operations.sigma A B)) (pack source A B)) ≫
            eqToHom baseEq := (Category.assoc _ _ _).symm.trans
              (congrArg (fun arrow => arrow ≫ eqToHom baseEq)
                (F.toFamilyMorphism.base.map_comp (pack source A B)
                  (C.toCwf.wk (source.operations.sigma A B))).symm)
      _ = F.toFamilyMorphism.base.map
          (C.toCwf.compS (C.toCwf.wk A) (C.toCwf.wk B)) ≫ eqToHom baseEq := by rw [pack_over]
      _ = eqToHom tupleEq ≫ (D.toCwf.compS (D.toCwf.wk A') (D.toCwf.wk B')) := bases
      _ = (eqToHom tupleEq ≫ newPack) ≫ D.toCwf.wk (target.operations.sigma A' B') := by
        have targetPackOver := pack_over target A' B'
        exact (congrArg (fun arrow : D.toCwf.Sub (tupleContext A' B') Γ' =>
          D.toCwf.compS arrow (eqToHom tupleEq)) targetPackOver.symm).trans
            (D.toCwf.comp_assoc _ _ _)
  · have genericType := substituted_type_heq F
      (sum_contexts F source target preserves contexts domains codomains) contexts formation projectionRead
    have genericValue := (variable_heq F Γ (source.operations.sigma A B)).trans
      (vz_heq contexts formation)
    have mapRead := (F.toFamilyMorphism.mapTerm_substitution
      (C.toCwf.vz (source.operations.sigma A B)) (pack source A B)).trans
      (tmSub_heq rfl (sum_contexts F source target preserves contexts domains codomains)
        genericType genericValue (hom_eqToHom_heq sumEq oldPack).symm)
    have targetRead := (TypeOver.tmSub_comp_heq
      (D.toCwf.vz (target.operations.sigma A' B')) newPack (eqToHom tupleEq)).trans
      (term_eqToHom_heq tupleEq _)
    exact mapRead.symm.trans
      ((packed_variable_heq F source target preserves contexts domains codomains).trans targetRead.symm)

theorem pack_heq (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    HEq (F.toFamilyMorphism.base.map (pack source A B)) (pack target A' B') :=
  heq_of_diagram (ContextualBase.Context.ext (tuple_contexts F contexts domains codomains))
    (ContextualBase.Context.ext (sum_contexts F source target preserves contexts domains codomains)) _ _
    (pack_square F source target preserves contexts domains codomains)

/-- The inverse square is earned by cancellation with the actual packing
inverse equations on both sides. -/
theorem unpack_square (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    F.toFamilyMorphism.base.map (unpack source A B) ≫
        eqToHom (ContextualBase.Context.ext (tuple_contexts F contexts domains codomains)) =
      eqToHom (ContextualBase.Context.ext (sum_contexts F source target preserves contexts domains codomains)) ≫
        unpack target A' B' := by
  let tupleEq := ContextualBase.Context.ext (tuple_contexts F contexts domains codomains)
  let sumEq := ContextualBase.Context.ext (sum_contexts F source target preserves contexts domains codomains)
  let oldPack := F.toFamilyMorphism.base.map (pack source A B)
  let oldUnpack := F.toFamilyMorphism.base.map (unpack source A B)
  let newPack : (⟨tupleContext A' B'⟩ : D.toCwf.base.Context) ⟶ ⟨sumContext target A' B'⟩ :=
    pack target A' B'
  let newUnpack : (⟨sumContext target A' B'⟩ : D.toCwf.base.Context) ⟶ ⟨tupleContext A' B'⟩ :=
    unpack target A' B'
  have packing := pack_square F source target preserves contexts domains codomains
  change oldPack ≫ eqToHom sumEq = eqToHom tupleEq ≫ newPack at packing
  have targetInverse := unpack_pack target A' B'
  change newPack ≫ newUnpack = 𝟙 _ at targetInverse
  have sourceInverse : oldUnpack ≫ oldPack = 𝟙 _ := by
    exact (F.toFamilyMorphism.base.map_comp (unpack source A B) (pack source A B)).symm.trans
      ((congrArg F.toFamilyMorphism.base.map (pack_unpack source A B)).trans
        (F.toFamilyMorphism.base.map_id _))
  change oldUnpack ≫ eqToHom tupleEq = eqToHom sumEq ≫ newUnpack
  calc
    _ = (oldUnpack ≫ eqToHom tupleEq) ≫ (newPack ≫ newUnpack) := by rw [targetInverse, Category.comp_id]
    _ = oldUnpack ≫ (eqToHom tupleEq ≫ newPack) ≫ newUnpack := by simp only [Category.assoc]
    _ = oldUnpack ≫ (oldPack ≫ eqToHom sumEq) ≫ newUnpack := by rw [← packing]
    _ = (oldUnpack ≫ oldPack) ≫ eqToHom sumEq ≫ newUnpack := by simp only [Category.assoc]
    _ = _ := by rw [sourceInverse, Category.id_comp]

theorem unpack_heq (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B') :
    HEq (F.toFamilyMorphism.base.map (unpack source A B)) (unpack target A' B') :=
  heq_of_diagram (ContextualBase.Context.ext (sum_contexts F source target preserves contexts domains codomains))
    (ContextualBase.Context.ext (tuple_contexts F contexts domains codomains)) _ _
    (unpack_square F source target preserves contexts domains codomains)

/-- Full-motive elimination preservation is derived, with the complete sum
variable retained in the motive and both witnesses retained in the branch. -/
theorem elimination_heq (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (M : C.toCwf.Ty (sumContext source A B)) (M' : D.toCwf.Ty (sumContext target A' B'))
    (motives : HEq (F.toFamilyMorphism.mapType M) M')
    (body : C.toCwf.Tm (tupleContext A B) (C.toCwf.tySub M (pack source A B)))
    (body' : D.toCwf.Tm (tupleContext A' B') (D.toCwf.tySub M' (pack target A' B')))
    (bodies : HEq (F.toFamilyMorphism.mapTerm body) body') :
    HEq (F.toFamilyMorphism.mapTerm (eliminate source A B M body))
      (eliminate target A' B' M' body') := by
  have bodyTypes := substituted_type_heq F (tuple_contexts F contexts domains codomains)
    (sum_contexts F source target preserves contexts domains codomains) motives
    (pack_heq F source target preserves contexts domains codomains)
  have substitution := substituted_term_heq F
    (sum_contexts F source target preserves contexts domains codomains)
    (tuple_contexts F contexts domains codomains) bodyTypes bodies
    (unpack_heq F source target preserves contexts domains codomains)
  exact (F.mapTerm_heq (motive_roundtrip source A B M).symm
    (eliminate_heq source A B M body)).trans
      (substitution.trans (eliminate_heq target A' B' M' body').symm)

/-- The generated-language form of the rule also substitutes a supplied
pair into the complete motive. Its preservation follows from the earned
full section law and actual self-extension preservation. -/
theorem elimination_application_heq (F : StrictCwfMorphism C D)
    (source : StableSums C.toCwf) (target : StableSums D.toCwf)
    (preserves : SigmaPreservation F source.operations target.operations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (domains : HEq (F.toFamilyMorphism.mapType A) A')
    {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
    (codomains : HEq (F.toFamilyMorphism.mapType B) B')
    (M : C.toCwf.Ty (sumContext source A B)) (M' : D.toCwf.Ty (sumContext target A' B'))
    (motives : HEq (F.toFamilyMorphism.mapType M) M')
    (body : C.toCwf.Tm (tupleContext A B) (C.toCwf.tySub M (pack source A B)))
    (body' : D.toCwf.Tm (tupleContext A' B') (D.toCwf.tySub M' (pack target A' B')))
    (bodies : HEq (F.toFamilyMorphism.mapTerm body) body')
    (p : C.toCwf.Tm Γ (source.operations.sigma A B))
    (p' : D.toCwf.Tm Γ' (target.operations.sigma A' B'))
    (pairs : HEq (F.toFamilyMorphism.mapTerm p) p') :
    HEq (F.toFamilyMorphism.mapTerm
      (C.toCwf.tmSub (eliminate source A B M body)
        (ContextualProductComparison.selfExtend C.toCwf p)))
      (D.toCwf.tmSub (eliminate target A' B' M' body')
        (ContextualProductComparison.selfExtend D.toCwf p')) :=
  substituted_term_heq F contexts (sum_contexts F source target preserves contexts domains codomains)
    motives (elimination_heq F source target preserves contexts domains codomains M M' motives body body' bodies)
    (self_extension_heq F contexts (preserves.formation contexts domains codomains) p p' pairs)

end Mettapedia.TypeTheory.ContextualLogicalMorphism
