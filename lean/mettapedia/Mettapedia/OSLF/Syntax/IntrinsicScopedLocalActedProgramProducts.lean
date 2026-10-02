import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafSetting
import Mettapedia.OSLF.Syntax.SecondOrderEquationProducts

/-!
# Products with a program context in the operational classifier

An arbitrary classifier stage can carry event variables. Pairing that stage
with a program context reindexes its event variables along the first
projection of the product in the equation-context base. The cartesian lift
proves the product universal property, including uniqueness of its event
component. Thus subsequent binder comparisons apply at event-bearing stages.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Functor
open _root_.CategoryTheory.Pseudofunctor
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

private theorem base_isHomLift {a b : Classifier R equations} (f : a ⟶ b) :
    IsHomLift (CoGrothendieck.forget (fibres R equations)) f.base f :=
  IsHomLift.map (CoGrothendieck.forget (fibres R equations)) f

/-- Pair a stage with a program context by a cartesian lift in the classifier. -/
abbrev productWithProgram (a : Classifier R equations) (X : Base equations) :
    Classifier R equations :=
  CoGrothendieck.domainCartesianLift a.fiber (prod.fst : a.base ⨯ X ⟶ a.base)

/-- The first projection retains the stage's event variables. -/
abbrev programProductFst (a : Classifier R equations) (X : Base equations) :
    productWithProgram R equations a X ⟶ a :=
  CoGrothendieck.cartesianLift a.fiber (prod.fst : a.base ⨯ X ⟶ a.base)

/-- The second projection is the ordinary program-context projection. -/
def programProductSnd (a : Classifier R equations) (X : Base equations) :
    productWithProgram R equations a X ⟶ (programSection R equations).obj X :=
  (programHomEquiv R equations _ X).symm prod.snd

/-- The projection retaining events is strongly cartesian. -/
theorem programProductFst_cartesian (a : Classifier R equations) (X : Base equations) :
    IsStronglyCartesian (CoGrothendieck.forget (fibres R equations))
      (prod.fst : a.base ⨯ X ⟶ a.base) (programProductFst R equations a X) :=
  CoGrothendieck.isStronglyCartesian_homCartesianLift a.fiber prod.fst

/-- A cone into the two factors lifts uniquely over its paired base map. -/
def programProductLift {a c : Classifier R equations} {X : Base equations}
    (f : c ⟶ a) (g : c ⟶ (programSection R equations).obj X) :
    c ⟶ productWithProgram R equations a X := by
  let := programProductFst_cartesian R equations a X
  let := base_isHomLift R equations f
  exact IsStronglyCartesian.map (CoGrothendieck.forget (fibres R equations))
    (prod.fst : a.base ⨯ X ⟶ a.base) (programProductFst R equations a X)
    (prod.lift_fst f.base (g.base : c.base ⟶ X)).symm f

/-- The paired map has exactly the paired assignment as its program part. -/
theorem programProductLift_base {a c : Classifier R equations} {X : Base equations}
    (f : c ⟶ a) (g : c ⟶ (programSection R equations).obj X) :
    (programProductLift R equations f g).base = prod.lift f.base g.base := by
  let := programProductFst_cartesian R equations a X
  let := base_isHomLift R equations f
  have lifted : IsHomLift (CoGrothendieck.forget (fibres R equations))
      (prod.lift f.base (g.base : c.base ⟶ X)) (programProductLift R equations f g) := by
    unfold programProductLift
    infer_instance
  change (CoGrothendieck.forget (fibres R equations)).map
    (programProductLift R equations f g) = prod.lift f.base (g.base : c.base ⟶ X)
  exact (@IsHomLift.eq_of_isHomLift _ _ _ _
    (CoGrothendieck.forget (fibres R equations)) c (productWithProgram R equations a X)
    (prod.lift f.base (g.base : c.base ⟶ X)) (programProductLift R equations f g) lifted).symm

/-- The first product equation follows from the cartesian lift. -/
theorem programProductLift_fst {a c : Classifier R equations} {X : Base equations}
    (f : c ⟶ a) (g : c ⟶ (programSection R equations).obj X) :
    programProductLift R equations f g ≫ programProductFst R equations a X = f := by
  let := programProductFst_cartesian R equations a X
  let := base_isHomLift R equations f
  exact IsStronglyCartesian.fac (CoGrothendieck.forget (fibres R equations))
    (prod.fst : a.base ⨯ X ⟶ a.base) (programProductFst R equations a X)
    (prod.lift_fst f.base (g.base : c.base ⟶ X)).symm f

/-- The second product equation is determined by the program assignment. -/
theorem programProductLift_snd {a c : Classifier R equations} {X : Base equations}
    (f : c ⟶ a) (g : c ⟶ (programSection R equations).obj X) :
    programProductLift R equations f g ≫ programProductSnd R equations a X = g := by
  apply (programHomEquiv R equations c X).injective
  change (programProductLift R equations f g).base ≫ prod.snd = g.base
  rw [programProductLift_base]
  exact prod.lift_snd _ _

/-- The two projections determine the complete arrow, including its firing trees. -/
theorem programProductLift_unique {a c : Classifier R equations} {X : Base equations}
    (f : c ⟶ a) (g : c ⟶ (programSection R equations).obj X)
    (candidate : c ⟶ productWithProgram R equations a X)
    (hf : candidate ≫ programProductFst R equations a X = f)
    (hg : candidate ≫ programProductSnd R equations a X = g) :
    candidate = programProductLift R equations f g := by
  let := programProductFst_cartesian R equations a X
  let := base_isHomLift R equations f
  have first : candidate.base ≫ prod.fst = f.base :=
    congrArg (fun u : c ⟶ a => u.base) hf
  have second : candidate.base ≫ prod.snd = (g.base : c.base ⟶ X) :=
    congrArg (fun u : c ⟶ (programSection R equations).obj X => u.base) hg
  have paired : candidate.base = prod.lift f.base (g.base : c.base ⟶ X) := by
    apply prod.hom_ext
    · exact first.trans (prod.lift_fst _ _).symm
    · exact second.trans (prod.lift_snd _ _).symm
  have : IsHomLift (CoGrothendieck.forget (fibres R equations))
      (prod.lift f.base (g.base : c.base ⟶ X)) candidate :=
    paired ▸ base_isHomLift R equations candidate
  exact IsStronglyCartesian.map_uniq (CoGrothendieck.forget (fibres R equations))
    (prod.fst : a.base ⨯ X ⟶ a.base) (programProductFst R equations a X)
    (prod.lift_fst f.base (g.base : c.base ⟶ X)).symm f candidate hf

/-- Products with program contexts exist at every operational classifier stage. -/
def programProductIsLimit (a : Classifier R equations) (X : Base equations) :
    IsLimit (BinaryFan.mk (programProductFst R equations a X)
      (programProductSnd R equations a X)) :=
  BinaryFan.isLimitMk
    (fun cone => programProductLift R equations cone.fst cone.snd)
    (fun cone => programProductLift_fst R equations cone.fst cone.snd)
    (fun cone => programProductLift_snd R equations cone.fst cone.snd)
    (fun cone candidate hf hg =>
      programProductLift_unique R equations cone.fst cone.snd candidate hf hg)

/-- The product universal property as an equivalence of actual assignment arrows. -/
def programProductHomEquiv (c a : Classifier R equations) (X : Base equations) :
    (c ⟶ productWithProgram R equations a X) ≃
      (c ⟶ a) × (c ⟶ (programSection R equations).obj X) where
  toFun f := (f ≫ programProductFst R equations a X,
    f ≫ programProductSnd R equations a X)
  invFun pair := programProductLift R equations pair.1 pair.2
  left_inv f := (programProductLift_unique R equations _ _ f rfl rfl).symm
  right_inv pair := Prod.ext
    (programProductLift_fst R equations pair.1 pair.2)
    (programProductLift_snd R equations pair.1 pair.2)

/-- The product correspondence commutes with every change of classifier stage. -/
theorem programProductHomEquiv_precompose {c b a : Classifier R equations}
    (f : c ⟶ b) (X : Base equations)
    (g : b ⟶ productWithProgram R equations a X) :
    programProductHomEquiv R equations c a X (f ≫ g) =
      (f ≫ (programProductHomEquiv R equations b a X g).1,
        f ≫ (programProductHomEquiv R equations b a X g).2) :=
  Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The product with a program context is the actual product of representables,
at all stages and at the declared presheaf universe. -/
def programProductRepresentableIso.{w} (a : Classifier R equations) (X : Base equations) :
    (embedding.{w} R equations).obj (productWithProgram R equations a X) ≅
      (embedding.{w} R equations).obj a ⊗
        (embedding.{w} R equations).obj ((programSection R equations).obj X) :=
  NatIso.ofComponents
    (fun c => ({
      toFun := fun f =>
        (ULift.up (f.down ≫ programProductFst R equations a X),
          ULift.up (f.down ≫ programProductSnd R equations a X))
      invFun := fun pair => ULift.up (programProductLift R equations pair.1.down pair.2.down)
      left_inv := fun f => congrArg ULift.up
        (programProductLift_unique R equations _ _ f.down rfl rfl).symm
      right_inv := fun pair => Prod.ext
        (congrArg ULift.up (programProductLift_fst R equations pair.1.down pair.2.down))
        (congrArg ULift.up (programProductLift_snd R equations pair.1.down pair.2.down))
      } : _ ≃ _).toIso)
    (by
      intro c b f
      ext g
      apply Prod.ext
      · exact congrArg ULift.up (Category.assoc _ _ _)
      · exact congrArg ULift.up (Category.assoc _ _ _))

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
