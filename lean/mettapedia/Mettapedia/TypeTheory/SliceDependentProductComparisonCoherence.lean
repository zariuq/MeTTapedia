import Mettapedia.TypeTheory.SliceDependentProductComparison
import Mettapedia.CategoryTheory.SliceFunctorPullbackCoherence
import Mettapedia.TypeTheory.CodomainDependentProductReadouts

/-!
# Coherent dependent-product mates at actual slices

Complete pullback comparisons compose by their universal properties.
Their dependent-product mates therefore compose through the actual
adjunctions, retaining full evaluation, abstraction and argument bodies.
Route pasting uses the compound chosen adjunctions; product preservation
or invertibility of a geometric comparison is not an extra hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Mettapedia.TypeTheory.SliceDependentProductComparisonCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open Mettapedia.CategoryTheory
open scoped TwoSquare

attribute [local instance] comp_preservesFiniteLimits

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C] [HasFiniteLimits C]
variable {D : Type u₂} [Category.{v₂} D] [HasFiniteLimits D]
variable {E : Type u₃} [Category.{v₃} E] [HasFiniteLimits E]
variable (source : CodomainClosedComprehension C)
variable (middle : CodomainClosedComprehension D)
variable (target : CodomainClosedComprehension E)
variable (F : C ⥤ D) [PreservesFiniteLimits F]
variable (G : D ⥤ E) [PreservesFiniteLimits G]
variable {X Y : C} (route : X ⟶ Y)

section AdjunctionChoice

universe u₄ v₄
variable {P : Type u₁} [Category.{v₁} P] {Q : Type u₂} [Category.{v₂} Q]
variable {R : Type u₃} [Category.{v₃} R] {S : Type u₄} [Category.{v₄} S]

/-- Transporting a left adjoint and then comparing its right adjoint is
the actual conjugate of the inverse left comparison. -/
theorem transported_rightComparison
    {L L' : P ⥤ Q} {A A' : Q ⥤ P}
    (earlier : L ⊣ A) (later : L' ⊣ A') (choice : L ≅ L') :
    (Adjunction.rightAdjointUniq (earlier.ofNatIsoLeft choice) later).hom =
      conjugateEquiv earlier later choice.inv := by
  apply NatTrans.ext
  funext result
  apply (later.homEquiv _ result).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have transported := Adjunction.rightAdjointUniq_hom_app_counit
    (earlier.ofNatIsoLeft choice) later result
  change L'.map ((Adjunction.rightAdjointUniq (earlier.ofNatIsoLeft choice) later).hom.app result) ≫
      later.counit.app result = choice.inv.app (A.obj result) ≫ earlier.counit.app result
    at transported
  exact transported.trans (conjugateEquiv_counit earlier later choice.inv result).symm

/-- Mates respect independently chosen source and target adjoints. The
square is transported only by the supplied actual left isomorphisms. -/
theorem mate_choice_comparison
    {L L' : P ⥤ Q} {A A' : Q ⥤ P}
    {M M' : R ⥤ S} {B B' : S ⥤ R}
    (sourceAdj : L ⊣ A) (sourceOther : L' ⊣ A')
    (targetAdj : M ⊣ B) (targetOther : M' ⊣ B')
    (sourceChoice : L ≅ L') (targetChoice : M ≅ M')
    {top : P ⥤ R} {bottom : Q ⥤ S} (square : TwoSquare top L M bottom) :
    whiskerRight (Adjunction.rightAdjointUniq
        (sourceAdj.ofNatIsoLeft sourceChoice) sourceOther).hom top ≫
      (mateEquiv sourceOther targetOther
        (TwoSquare.mk _ _ _ _
          (whiskerLeft top targetChoice.inv ≫ square.natTrans ≫
            whiskerRight sourceChoice.hom bottom))).natTrans =
    (mateEquiv sourceAdj targetAdj square).natTrans ≫
      whiskerLeft bottom (Adjunction.rightAdjointUniq
        (targetAdj.ofNatIsoLeft targetChoice) targetOther).hom := by
  rw [transported_rightComparison, transported_rightComparison]
  let changed : TwoSquare top L' M' bottom := TwoSquare.mk _ _ _ _
    (whiskerLeft top targetChoice.inv ≫ square.natTrans ≫
      whiskerRight sourceChoice.hom bottom)
  have sourceChange := conjugateEquiv_mateEquiv_vcomp sourceAdj sourceOther targetOther
    sourceChoice.inv changed
  have targetChange := mateEquiv_conjugateEquiv_vcomp sourceAdj targetAdj targetOther
    square targetChoice.inv
  have same : changed.whiskerLeft sourceChoice.inv =
      square.whiskerRight targetChoice.inv := by
    apply TwoSquare.ext
    intro argument
    simp only [changed, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    rw [← bottom.map_comp, Iso.hom_inv_id_app, bottom.map_id]
    exact congrArg (fun arrow => targetChoice.inv.app (top.obj argument) ≫ arrow)
      (Category.comp_id (square.natTrans.app argument))
  exact congrArg (fun result => result.natTrans)
    (sourceChange.symm.trans
      ((congrArg (fun input => mateEquiv sourceAdj targetOther input) same).trans targetChange))

end AdjunctionChoice

/-- The actual identity comparison retains the identity post-functor
isomorphisms on both slice endpoints. -/
def identityComparison : source.dependentProduct route ⋙ Over.post (𝟭 C) ⟶
    Over.post (𝟭 C) ⋙ source.dependentProduct route :=
  (isoWhiskerLeft (source.dependentProduct route)
      (SliceFunctorPullbackCoherence.postIdentity Y) ≪≫
    Functor.rightUnitor (source.dependentProduct route) ≪≫
    (Functor.leftUnitor (source.dependentProduct route)).symm ≪≫
    isoWhiskerRight (SliceFunctorPullbackCoherence.postIdentity X).symm
      (source.dependentProduct route)).hom

theorem identityComparison_app (result : Over X) :
    (identityComparison source route).app result =
      (SliceFunctorPullbackCoherence.postIdentity Y).hom.app
          ((source.dependentProduct route).obj result) ≫
        (source.dependentProduct route).map
          ((SliceFunctorPullbackCoherence.postIdentity X).inv.app result) := by
  simp [identityComparison]

/-- The identity mate is the actual chosen slice identity comparison. -/
theorem comparison_identity :
    SliceDependentProductComparison.comparison source source (𝟭 C) route =
      identityComparison source route := by
  symm
  apply SliceDependentProductComparison.unique
  intro result
  rw [identityComparison_app, Functor.map_comp, Category.assoc]
  have evaluationNatural := (source.dependentAdjunction route).counit.naturality
    ((SliceFunctorPullbackCoherence.postIdentity X).inv.app result)
  change (Over.pullback route).map
      ((source.dependentProduct route).map
        ((SliceFunctorPullbackCoherence.postIdentity X).inv.app result)) ≫
      source.evaluation route ((Over.post (𝟭 C)).obj result) =
    source.evaluation route result ≫
      (SliceFunctorPullbackCoherence.postIdentity X).inv.app result at evaluationNatural
  change (Over.pullback route).map
      ((SliceFunctorPullbackCoherence.postIdentity Y).hom.app
        ((source.dependentProduct route).obj result)) ≫
      ((Over.pullback route).map
        ((source.dependentProduct route).map
          ((SliceFunctorPullbackCoherence.postIdentity X).inv.app result)) ≫
        source.evaluation route ((Over.post (𝟭 C)).obj result)) = _
  rw [evaluationNatural, SliceFunctorPullbackCoherence.comparison_identity]
  simp only [SliceFunctorPullbackCoherence.identityComparison, Iso.trans_inv,
    NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Iso.symm_inv,
    Category.comp_id]
  have remove :
      (Over.pullback route).map
          ((SliceFunctorPullbackCoherence.postIdentity Y).hom.app
            ((source.dependentProduct route).obj result)) ≫
        𝟙 ((Over.pullback route).obj ((source.dependentProduct route).obj result)) =
      (Over.pullback route).map
        ((SliceFunctorPullbackCoherence.postIdentity Y).hom.app
          ((source.dependentProduct route).obj result)) := Category.comp_id _
  rw [remove]
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun arrow => (Over.pullback route).map
      ((SliceFunctorPullbackCoherence.postIdentity Y).hom.app
        ((source.dependentProduct route).obj result)) ≫ arrow)
      ((SliceFunctorPullbackCoherence.postIdentity X).inv.naturality
        (source.evaluation route result)).symm)).symm

theorem pullbackSquare_composition :
    SliceDependentProductComparison.pullbackSquare (F ⋙ G) route =
      (SliceDependentProductComparison.pullbackSquare F route) ≫ₕ
        (SliceDependentProductComparison.pullbackSquare G (F.map route)) := by
  apply TwoSquare.ext
  intro argument
  simpa [SliceDependentProductComparison.pullbackSquare, TwoSquare.hComp] using
    SliceFunctorPullbackCoherence.comparison_composition_inverse F G route argument

/-- Both stages act on the whole dependent function, at the actual slices. -/
def stagedComparison : source.dependentProduct route ⋙ Over.post (F ⋙ G) ⟶
    Over.post (F ⋙ G) ⋙ target.dependentProduct ((F ⋙ G).map route) :=
  whiskerRight (SliceDependentProductComparison.comparison source middle F route) (Over.post G) ≫
    whiskerLeft (Over.post F)
      (SliceDependentProductComparison.comparison middle target G (F.map route))

theorem comparison_composition :
    SliceDependentProductComparison.comparison source target (F ⋙ G) route =
      stagedComparison source middle target F G route := by
  have pasting := mateEquiv_vcomp (source.dependentAdjunction route)
    (middle.dependentAdjunction (F.map route))
    (target.dependentAdjunction ((F ⋙ G).map route))
    (SliceDependentProductComparison.pullbackSquare F route)
    (SliceDependentProductComparison.pullbackSquare G (F.map route))
  rw [← pullbackSquare_composition F G route] at pasting
  apply NatTrans.ext
  funext result
  have reading := congrArg (fun square => square.natTrans.app result) pasting
  simpa [SliceDependentProductComparison.comparison, stagedComparison, TwoSquare.vComp] using
    reading

theorem composition_evaluation (result : Over X) :
    (Over.pullback ((F ⋙ G).map route)).map
        ((stagedComparison source middle target F G route).app result) ≫
      target.evaluation ((F ⋙ G).map route) ((Over.post (F ⋙ G)).obj result) =
    (SliceFunctorPullbackComparison.comparison G (F.map route)).inv.app
        ((Over.post F).obj ((source.dependentProduct route).obj result)) ≫
      (Over.post G).map
        ((SliceFunctorPullbackComparison.comparison F route).inv.app
            ((source.dependentProduct route).obj result) ≫
          (Over.post F).map (source.evaluation route result)) := by
  rw [← comparison_composition, SliceDependentProductComparison.evaluation,
    SliceFunctorPullbackCoherence.comparison_composition_inverse]
  change ((SliceFunctorPullbackComparison.comparison G (F.map route)).inv.app
      ((Over.post F).obj ((source.dependentProduct route).obj result)) ≫
      (Over.post G).map ((SliceFunctorPullbackComparison.comparison F route).inv.app
        ((source.dependentProduct route).obj result))) ≫
      (Over.post G).map ((Over.post F).map (source.evaluation route result)) = _
  rw [Category.assoc, Functor.map_comp]

theorem composition_abstraction {argument : Over Y} {result : Over X}
    (body : (Over.pullback route).obj argument ⟶ result) :
    (Over.post G).map ((Over.post F).map (source.abstraction route body)) ≫
        (stagedComparison source middle target F G route).app result =
    target.abstraction (G.map (F.map route))
      ((SliceFunctorPullbackComparison.comparison G (F.map route)).inv.app
          ((Over.post F).obj argument) ≫
        (Over.post G).map
          ((SliceFunctorPullbackComparison.comparison F route).inv.app argument ≫
            (Over.post F).map body)) := by
  change (Over.post G).map ((Over.post F).map (source.abstraction route body)) ≫
      (Over.post G).map ((SliceDependentProductComparison.comparison source middle F route).app result) ≫
      (SliceDependentProductComparison.comparison middle target G (F.map route)).app
        ((Over.post F).obj result) = _
  calc
    _ = (Over.post G).map
        ((Over.post F).map (source.abstraction route body) ≫
          (SliceDependentProductComparison.comparison source middle F route).app result) ≫
        (SliceDependentProductComparison.comparison middle target G (F.map route)).app
          ((Over.post F).obj result) := by
      rw [Functor.map_comp, Category.assoc]
    _ = (Over.post G).map
        (middle.abstraction (F.map route)
          ((SliceFunctorPullbackComparison.comparison F route).inv.app argument ≫
            (Over.post F).map body)) ≫
        (SliceDependentProductComparison.comparison middle target G (F.map route)).app
          ((Over.post F).obj result) :=
      congrArg (fun function => (Over.post G).map function ≫
        (SliceDependentProductComparison.comparison middle target G (F.map route)).app
          ((Over.post F).obj result))
        (SliceDependentProductComparison.abstraction source middle F route body)
    _ = _ := SliceDependentProductComparison.abstraction middle target G (F.map route) _

section RouteIdentity

variable (base : C)

def mappedPullbackIdentity : Over.pullback (F.map (𝟙 base)) ≅ 𝟭 (Over (F.obj base)) :=
  CanonicalSlicePullback.transport (F.map_id base) ≪≫
    CanonicalSlicePullback.identity (F.obj base)

def mappedProductIdentity : middle.dependentProduct (F.map (𝟙 base)) ≅
    𝟭 (Over (F.obj base)) :=
  Adjunction.rightAdjointUniq
    ((middle.dependentAdjunction (F.map (𝟙 base))).ofNatIsoLeft
      (mappedPullbackIdentity F base))
    (Adjunction.id (C := Over (F.obj base)))

def routeIdentitySquare : TwoSquare (Over.post (X := base) F)
    (𝟭 (Over base)) (𝟭 (Over (F.obj base))) (Over.post (X := base) F) :=
  TwoSquare.mk _ _ _ _ ((Functor.rightUnitor (Over.post F)).hom ≫
    (Functor.leftUnitor (Over.post F)).inv)

theorem routeIdentitySquare_transported : routeIdentitySquare F base =
    TwoSquare.mk _ _ _ _
      (whiskerLeft (Over.post F) (mappedPullbackIdentity F base).inv ≫
        (SliceDependentProductComparison.pullbackSquare F (𝟙 base)).natTrans ≫
        whiskerRight (CanonicalSlicePullback.identity base).hom (Over.post F)) := by
  apply TwoSquare.ext
  intro argument
  have forward : (Over.post F).map ((CanonicalSlicePullback.identity base).hom.app argument) =
      (SliceFunctorPullbackComparison.comparison F (𝟙 base)).hom.app argument ≫
        (mappedPullbackIdentity F base).hom.app ((Over.post F).obj argument) := by
    simpa only [mappedPullbackIdentity, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc] using SliceFunctorPullbackCoherence.route_identity F argument
  simp only [routeIdentitySquare, TwoSquare.mk, NatTrans.comp_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    SliceDependentProductComparison.pullbackSquare]
  change (𝟙 ((Over.post F).obj argument) ≫ 𝟙 ((Over.post F).obj argument)) =
    (mappedPullbackIdentity F base).inv.app ((Over.post F).obj argument) ≫
      (SliceFunctorPullbackComparison.comparison F (𝟙 base)).inv.app argument ≫
        (Over.post F).map ((CanonicalSlicePullback.identity base).hom.app argument)
  have remove : 𝟙 ((Over.post F).obj argument) ≫ 𝟙 ((Over.post F).obj argument) =
      𝟙 ((Over.post F).obj argument) := Category.id_comp _
  rw [remove]
  rw [forward, ← Category.assoc
    ((SliceFunctorPullbackComparison.comparison F (𝟙 base)).inv.app argument),
    Iso.inv_hom_id_app, Category.id_comp, Iso.inv_hom_id_app]
  rfl

omit [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits F] in
theorem routeIdentitySquare_mate :
    (mateEquiv (Adjunction.id (C := Over base))
      (Adjunction.id (C := Over (F.obj base))) (routeIdentitySquare F base)).natTrans =
      𝟙 (Over.post (X := base) F) := by
  apply NatTrans.ext
  funext argument
  simp [routeIdentitySquare, mateEquiv, Adjunction.id]

/-- The direct identity-route mate commutes with the actual chosen
right-adjoint identity isomorphisms. -/
theorem chosen_route_identity (result : Over base) :
    (Over.post F).map ((source.productIdentity base).hom.app result) =
      (SliceDependentProductComparison.comparison source middle F (𝟙 base)).app result ≫
        (mappedProductIdentity middle F base).hom.app ((Over.post F).obj result) := by
  have chosen := mate_choice_comparison
    (source.dependentAdjunction (𝟙 base)) (Adjunction.id (C := Over base))
    (middle.dependentAdjunction (F.map (𝟙 base)))
    (Adjunction.id (C := Over (F.obj base)))
    (CanonicalSlicePullback.identity base) (mappedPullbackIdentity F base)
    (SliceDependentProductComparison.pullbackSquare F (𝟙 base))
  rw [← routeIdentitySquare_transported F base, routeIdentitySquare_mate F base] at chosen
  have reading := congr_app chosen result
  change (Over.post F).map ((source.productIdentity base).hom.app result) ≫
      𝟙 ((Over.post F).obj result) =
    (SliceDependentProductComparison.comparison source middle F (𝟙 base)).app result ≫
      (mappedProductIdentity middle F base).hom.app ((Over.post F).obj result) at reading
  exact (Category.comp_id _).symm.trans reading

end RouteIdentity

section RoutePasting

variable {Z : C} (next : Y ⟶ Z)

def mappedPullbackComposition :
    Over.pullback (F.map (route ≫ next)) ≅
      Over.pullback (F.map next) ⋙ Over.pullback (F.map route) :=
  CanonicalSlicePullback.transport (F.map_comp route next) ≪≫
    CanonicalSlicePullback.composition (F.map route) (F.map next)

omit [HasFiniteLimits C] [PreservesFiniteLimits F] in
theorem mappedPullbackComposition_inverse (argument : Over (F.obj Z)) :
    (mappedPullbackComposition F route next).inv.app argument =
      (CanonicalSlicePullback.compositionInverse (F.map route) (F.map next)).hom.app argument ≫
        (CanonicalSlicePullback.transport (F.map_comp route next).symm).hom.app argument := by
  simp only [mappedPullbackComposition, Iso.trans_inv, NatTrans.comp_app,
    CanonicalSlicePullback.composition, Iso.symm_inv,
    SliceFunctorPullbackCoherence.transport_inverse]

def mappedProductComposition : middle.dependentProduct (F.map (route ≫ next)) ≅
    middle.dependentProduct (F.map route) ⋙ middle.dependentProduct (F.map next) :=
  Adjunction.rightAdjointUniq
    ((middle.dependentAdjunction (F.map (route ≫ next))).ofNatIsoLeft
      (mappedPullbackComposition F route next))
    ((middle.dependentAdjunction (F.map next)).comp (middle.dependentAdjunction (F.map route)))

theorem transported_productComposition {whole : X ⟶ Z} (same : whole = route ≫ next) :
    Adjunction.rightAdjointUniq
      ((source.dependentAdjunction whole).ofNatIsoLeft
        (CanonicalSlicePullback.transport same ≪≫
          CanonicalSlicePullback.composition route next))
      ((source.dependentAdjunction next).comp (source.dependentAdjunction route)) =
    eqToIso (congrArg (fun arrow => source.dependentProduct arrow) same) ≪≫
      source.productComposition route next := by
  cases same
  simp only [CanonicalSlicePullback.transport, eqToIso_refl, Iso.refl_trans]
  rfl

omit [HasFiniteLimits C] [PreservesFiniteLimits F] in
theorem mappedProductComposition_eq_canonical : mappedProductComposition middle F route next =
    eqToIso (congrArg (fun arrow => middle.dependentProduct arrow) (F.map_comp route next)) ≪≫
      middle.productComposition (F.map route) (F.map next) :=
  transported_productComposition middle (F.map route) (F.map next) (F.map_comp route next)

def routePastingSquare : TwoSquare (Over.post (X := Z) F)
    (Over.pullback next ⋙ Over.pullback route)
    (Over.pullback (F.map next) ⋙ Over.pullback (F.map route))
    (Over.post (X := X) F) :=
  (SliceDependentProductComparison.pullbackSquare F next) ≫ᵥ
    (SliceDependentProductComparison.pullbackSquare F route)

theorem routePastingSquare_app (argument : Over Z) :
    (routePastingSquare F route next).app argument =
      (Over.pullback (F.map route)).map
          ((SliceFunctorPullbackComparison.comparison F next).inv.app argument) ≫
        (SliceFunctorPullbackComparison.comparison F route).inv.app
          ((Over.pullback next).obj argument) := by
  simp [routePastingSquare, TwoSquare.vComp,
    SliceDependentProductComparison.pullbackSquare]

def routePastingComparison :
    (source.dependentProduct route ⋙ source.dependentProduct next) ⋙ Over.post F ⟶
      Over.post F ⋙ (middle.dependentProduct (F.map route) ⋙
        middle.dependentProduct (F.map next)) :=
  (mateEquiv ((source.dependentAdjunction next).comp (source.dependentAdjunction route))
    ((middle.dependentAdjunction (F.map next)).comp
      (middle.dependentAdjunction (F.map route)))
    (routePastingSquare F route next)).natTrans

theorem route_pasting : routePastingComparison source middle F route next =
    whiskerLeft (source.dependentProduct route)
        (SliceDependentProductComparison.comparison source middle F next) ≫
      whiskerRight (SliceDependentProductComparison.comparison source middle F route)
        (middle.dependentProduct (F.map next)) := by
  have pasting := mateEquiv_hcomp (source.dependentAdjunction next)
    (middle.dependentAdjunction (F.map next)) (source.dependentAdjunction route)
    (middle.dependentAdjunction (F.map route))
    (SliceDependentProductComparison.pullbackSquare F next)
    (SliceDependentProductComparison.pullbackSquare F route)
  apply NatTrans.ext
  funext result
  have reading := congrArg (fun square => square.natTrans.app result) pasting
  simpa [routePastingComparison, routePastingSquare,
    SliceDependentProductComparison.comparison, TwoSquare.hComp] using reading

theorem route_pasting_evaluation (result : Over X) :
    (Over.pullback (F.map next) ⋙ Over.pullback (F.map route)).map
        ((routePastingComparison source middle F route next).app result) ≫
      ((middle.dependentAdjunction (F.map next)).comp
        (middle.dependentAdjunction (F.map route))).counit.app ((Over.post F).obj result) =
    (routePastingSquare F route next).app
        ((source.dependentProduct route ⋙ source.dependentProduct next).obj result) ≫
      (Over.post F).map
        (((source.dependentAdjunction next).comp (source.dependentAdjunction route)).counit.app result) :=
  mateEquiv_counit _ _ (routePastingSquare F route next) result

theorem routePastingSquare_transported : routePastingSquare F route next =
    TwoSquare.mk _ _ _ _
      (whiskerLeft (Over.post F) (mappedPullbackComposition F route next).inv ≫
        (SliceDependentProductComparison.pullbackSquare F (route ≫ next)).natTrans ≫
        whiskerRight (CanonicalSlicePullback.composition route next).hom (Over.post F)) := by
  apply TwoSquare.ext
  intro argument
  let staged := (SliceFunctorPullbackComparison.comparison F route).hom.app
      ((Over.pullback next).obj argument) ≫
    (Over.pullback (F.map route)).map
      ((SliceFunctorPullbackComparison.comparison F next).hom.app argument)
  have stagedInverse : (routePastingSquare F route next).app argument ≫ staged = 𝟙 _ := by
    rw [routePastingSquare_app]
    dsimp only [staged]
    rw [Category.assoc, ← Category.assoc
      ((SliceFunctorPullbackComparison.comparison F route).inv.app _),
      Iso.inv_hom_id_app, Category.id_comp, ← Functor.map_comp,
      Iso.inv_hom_id_app, _root_.CategoryTheory.Functor.map_id]
    rfl
  have originalMapped :
      (Over.post F).map ((CanonicalSlicePullback.compositionInverse route next).hom.app argument) ≫
        (SliceFunctorPullbackComparison.comparison F (route ≫ next)).hom.app argument =
      staged ≫ (mappedPullbackComposition F route next).inv.app ((Over.post F).obj argument) := by
    rw [mappedPullbackComposition_inverse]
    simpa only [staged, Category.assoc] using
      SliceFunctorPullbackCoherence.route_composition F route next argument
  have forward : (Over.post F).map ((CanonicalSlicePullback.composition route next).hom.app argument) ≫
      staged =
    (SliceFunctorPullbackComparison.comparison F (route ≫ next)).hom.app argument ≫
      (mappedPullbackComposition F route next).hom.app ((Over.post F).obj argument) := by
    apply (cancel_epi ((Over.post F).map
      ((CanonicalSlicePullback.compositionInverse route next).hom.app argument))).mp
    rw [← Category.assoc, ← Functor.map_comp]
    change (Over.post F).map
      (((CanonicalSlicePullback.compositionInverse route next).hom.app argument) ≫
        ((CanonicalSlicePullback.compositionInverse route next).inv.app argument)) ≫ staged = _
    rw [Iso.hom_inv_id_app, _root_.CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc, originalMapped, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id staged).symm
  apply (cancel_mono staged).mp
  rw [stagedInverse]
  simp only [TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, SliceDependentProductComparison.pullbackSquare]
  symm
  calc
    _ = (mappedPullbackComposition F route next).inv.app ((Over.post F).obj argument) ≫
        (SliceFunctorPullbackComparison.comparison F (route ≫ next)).inv.app argument ≫
          ((Over.post F).map ((CanonicalSlicePullback.composition route next).hom.app argument) ≫
            staged) := by simp only [Category.assoc]
    _ = (mappedPullbackComposition F route next).inv.app ((Over.post F).obj argument) ≫
        (SliceFunctorPullbackComparison.comparison F (route ≫ next)).inv.app argument ≫
          ((SliceFunctorPullbackComparison.comparison F (route ≫ next)).hom.app argument ≫
            (mappedPullbackComposition F route next).hom.app ((Over.post F).obj argument)) :=
      congrArg (fun arrow => (mappedPullbackComposition F route next).inv.app
        ((Over.post F).obj argument) ≫
        (SliceFunctorPullbackComparison.comparison F (route ≫ next)).inv.app argument ≫ arrow)
        forward
    _ = _ := by
      rw [← Category.assoc ((SliceFunctorPullbackComparison.comparison F (route ≫ next)).inv.app argument),
        Iso.inv_hom_id_app, Category.id_comp, Iso.inv_hom_id_app]
      rfl

/-- The compound mate and the direct-route mate commute with both chosen
product-composition isomorphisms. -/
theorem chosen_route_pasting (result : Over X) :
    (Over.post F).map ((source.productComposition route next).hom.app result) ≫
        (routePastingComparison source middle F route next).app result =
    (SliceDependentProductComparison.comparison source middle F (route ≫ next)).app result ≫
      (mappedProductComposition middle F route next).hom.app ((Over.post F).obj result) := by
  have chosen := mate_choice_comparison
    (source.dependentAdjunction (route ≫ next))
    ((source.dependentAdjunction next).comp (source.dependentAdjunction route))
    (middle.dependentAdjunction (F.map (route ≫ next)))
    ((middle.dependentAdjunction (F.map next)).comp (middle.dependentAdjunction (F.map route)))
    (CanonicalSlicePullback.composition route next) (mappedPullbackComposition F route next)
    (SliceDependentProductComparison.pullbackSquare F (route ≫ next))
  rw [← routePastingSquare_transported F route next] at chosen
  exact congr_app chosen result

end RoutePasting

end Mettapedia.TypeTheory.SliceDependentProductComparisonCoherence
