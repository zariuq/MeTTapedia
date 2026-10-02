import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaProgramProducts

/-!
# Mapping ordered parameter products

The product, recursive context, and variable projection laws are proved
before the target category is specialized. Source context and coordinate
objects remain explicit throughout the comparison.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel SecondOrderContext

section ProductComparison

variable {C D : Type*} [Category C] [Category D]
variable [HasBinaryProducts C] [CartesianMonoidalCategory D]
variable (H : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) H]

/-- A functor preserving binary products identifies the image of the chosen
source product with the chosen cartesian tensor in the target. -/
def mappedChosenProductIso (X Y : C) : H.obj (X ⨯ Y) ≅ H.obj X ⊗ H.obj Y := by
  let limiting := mapIsLimitOfPreservesOfIsLimit H prod.fst prod.snd (prodIsProd X Y)
  refine { hom := lift (H.map prod.fst) (H.map prod.snd)
           inv := BinaryFan.IsLimit.lift limiting (fst _ _) (snd _ _)
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · apply BinaryFan.IsLimit.hom_ext limiting
    · simp only [Category.assoc, BinaryFan.IsLimit.lift_fst, Category.id_comp]
      exact CartesianMonoidalCategory.lift_fst _ _
    · simp only [Category.assoc, BinaryFan.IsLimit.lift_snd, Category.id_comp]
      exact CartesianMonoidalCategory.lift_snd _ _
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, Category.id_comp]
      exact BinaryFan.IsLimit.lift_fst limiting _ _
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd, Category.id_comp]
      exact BinaryFan.IsLimit.lift_snd limiting _ _

@[reassoc]
theorem mappedChosenProductIso_fst (X Y : C) :
    (mappedChosenProductIso H X Y).hom ≫ fst _ _ = H.map prod.fst :=
  lift_fst _ _

@[reassoc]
theorem mappedChosenProductIso_snd (X Y : C) :
    (mappedChosenProductIso H X Y).hom ≫ snd _ _ = H.map prod.snd :=
  lift_snd _ _

end ProductComparison

section GenericProjection

variable {S : Signature}
variable {D : Type*} [Category D] [CartesianMonoidalCategory D]
variable (sort : S.Srt → D) (objects : Ctx S → D)
variable (comparison : ∀ Γ, objects Γ ⟶ contextOf sort Γ)
variable (coordinates : ∀ {Γ : Ctx S} {s : S.Srt}, Var Γ s → (objects Γ ⟶ sort s))
variable (tail : ∀ (a : S.Srt) (Γ : Ctx S), objects (a :: Γ) ⟶ objects Γ)

/-- A comparison preserving the head and tail projections preserves every
variable coordinate. This holds in any cartesian target. -/
theorem contextProjection_of_head_tail
    (head_law : ∀ (a : S.Srt) (Γ : Ctx S),
      comparison (a :: Γ) ≫ fst _ _ = coordinates (Var.zero : Var (a :: Γ) a))
    (tail_law : ∀ (a : S.Srt) (Γ : Ctx S),
      comparison (a :: Γ) ≫ snd _ _ = tail a Γ ≫ comparison Γ)
    (coordinate_succ : ∀ (a : S.Srt) {Γ : Ctx S} {s : S.Srt} (v : Var Γ s),
      coordinates (Var.succ v : Var (a :: Γ) s) = tail a Γ ≫ coordinates v) :
    ∀ {Γ : Ctx S} {s : S.Srt} (v : Var Γ s),
      comparison Γ ≫ projectVar sort v = coordinates v
  | _, _, @Var.zero _ Γ a => head_law a Γ
  | _, _, @Var.succ _ Γ s a v => by
      change comparison (a :: Γ) ≫ (snd _ _ ≫ projectVar sort v) = _
      rw [← Category.assoc, tail_law, Category.assoc,
        contextProjection_of_head_tail head_law tail_law coordinate_succ v, ← coordinate_succ a v]

end GenericProjection

namespace ParameterImage
variable {S : Signature}
variable {C D : Type*} [Category C] [Category D]
variable [HasBinaryProducts C] [CartesianMonoidalCategory D]
variable (H : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) H]
variable (objects : Ctx S → C) (sources : S.Srt → C) (sorts : S.Srt → D)
variable (empty : IsTerminal (objects []))
variable (pairs : ∀ Γ s, objects (s :: Γ) ≅ objects Γ ⨯ sources s)
variable (sourceHead : ∀ Γ s, objects (s :: Γ) ⟶ sources s)
variable (sourceTail : ∀ Γ s, objects (s :: Γ) ⟶ objects Γ)
variable (pairHead : ∀ Γ s, (pairs Γ s).hom ≫ prod.snd = sourceHead Γ s)
variable (pairTail : ∀ Γ s, (pairs Γ s).hom ≫ prod.fst = sourceTail Γ s)
variable (sortIso : ∀ s, H.obj (sources s) ≅ sorts s)

def imagePair (Γ : Ctx S) (s : S.Srt) :
    H.obj (objects (s :: Γ)) ≅ H.obj (objects Γ) ⊗ sorts s :=
  H.mapIso (pairs Γ s) ≪≫ mappedChosenProductIso H (objects Γ) (sources s) ≪≫
    whiskerLeftIso (H.obj (objects Γ)) (sortIso s)

include pairHead in
theorem imagePair_head (Γ : Ctx S) (s : S.Srt) :
    (imagePair H objects sources sorts pairs sortIso Γ s).hom ≫ snd _ _ =
      H.map (sourceHead Γ s) ≫ (sortIso s).hom := by
  simp only [imagePair, Iso.trans_hom, Functor.mapIso_hom, whiskerLeftIso_hom,
    Category.assoc, whiskerLeft_snd]
  have middle := congrArg (fun f => H.map (pairs Γ s).hom ≫ f ≫ (sortIso s).hom)
    (mappedChosenProductIso_snd H (objects Γ) (sources s))
  have mapped := congrArg (fun f => f ≫ (sortIso s).hom)
    ((H.map_comp (pairs Γ s).hom prod.snd).symm.trans (congrArg H.map (pairHead Γ s)))
  calc
    _ = H.map (pairs Γ s).hom ≫ H.map prod.snd ≫ (sortIso s).hom := by
      simpa only [Category.assoc] using middle
    _ = H.map (sourceHead Γ s) ≫ (sortIso s).hom := by
      simpa only [Category.assoc] using mapped

include pairTail in
theorem imagePair_tail (Γ : Ctx S) (s : S.Srt) :
    (imagePair H objects sources sorts pairs sortIso Γ s).hom ≫ fst _ _ =
      H.map (sourceTail Γ s) := by
  simp only [imagePair, Iso.trans_hom, Functor.mapIso_hom, whiskerLeftIso_hom,
    Category.assoc, whiskerLeft_fst]
  rw [mappedChosenProductIso_fst, ← H.map_comp, pairTail]

variable [PreservesLimit (Functor.empty.{0} C) H] [BraidedCategory D]

def contextIso : ∀ Γ : Ctx S, H.obj (objects Γ) ≅ contextOf sorts Γ
  | [] => empty.isTerminalObj H |>.uniqueUpToIso isTerminalTensorUnit
  | s :: Γ => imagePair H objects sources sorts pairs sortIso Γ s ≪≫
      whiskerRightIso (contextIso Γ) (sorts s) ≪≫ (β_ (contextOf sorts Γ) (sorts s))

include pairHead in
theorem contextIso_head (Γ : Ctx S) (s : S.Srt) :
    (contextIso H objects sources sorts empty pairs sortIso (s :: Γ)).hom ≫ fst _ _ =
      H.map (sourceHead Γ s) ≫ (sortIso s).hom := by
  simp only [contextIso, Iso.trans_hom, whiskerRightIso_hom,
    Category.assoc, braiding_hom_fst, whiskerRight_snd,
    imagePair_head H objects sources sorts pairs sourceHead pairHead sortIso]

include pairTail in
theorem contextIso_tail (Γ : Ctx S) (s : S.Srt) :
    (contextIso H objects sources sorts empty pairs sortIso (s :: Γ)).hom ≫ snd _ _ =
      H.map (sourceTail Γ s) ≫ (contextIso H objects sources sorts empty pairs sortIso Γ).hom := by
  simp only [contextIso, Iso.trans_hom, whiskerRightIso_hom,
    Category.assoc, braiding_hom_snd, whiskerRight_fst]
  rw [← Category.assoc, imagePair_tail H objects sources sorts pairs sourceTail pairTail sortIso]

variable (coordinates : ∀ {Γ : Ctx S} {s : S.Srt}, Var Γ s → (objects Γ ⟶ sources s))
variable (coordinateHead : ∀ Γ s, sourceHead Γ s = coordinates (Var.zero : Var (s :: Γ) s))
variable (coordinateSucc : ∀ s {Γ : Ctx S} {r : S.Srt} (v : Var Γ r),
  coordinates (Var.succ v : Var (s :: Γ) r) = sourceTail Γ s ≫ coordinates v)

include pairHead pairTail coordinateHead coordinateSucc in
theorem contextIso_variable : ∀ {Γ : Ctx S} {s : S.Srt} (v : Var Γ s),
    (contextIso H objects sources sorts empty pairs sortIso Γ).hom ≫ projectVar sorts v =
      H.map (coordinates v) ≫ (sortIso s).hom := by
  apply contextProjection_of_head_tail sorts (fun Γ => H.obj (objects Γ))
    (fun Γ => (contextIso H objects sources sorts empty pairs sortIso Γ).hom)
    (fun {Γ s} v => H.map (coordinates v) ≫ (sortIso s).hom)
    (fun s Γ => H.map (sourceTail Γ s))
  · intro s Γ
    exact (contextIso_head H objects sources sorts empty pairs sourceHead pairHead sortIso Γ s).trans
      (congrArg (fun f => H.map f ≫ (sortIso s).hom) (coordinateHead Γ s))
  · intro s Γ
    exact contextIso_tail H objects sources sorts empty pairs sourceTail pairTail sortIso Γ s
  · intro s Γ r v
    rw [coordinateSucc, H.map_comp, Category.assoc]

end ParameterImage

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
