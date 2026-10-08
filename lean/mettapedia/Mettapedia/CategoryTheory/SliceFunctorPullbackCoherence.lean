import Mettapedia.CategoryTheory.SliceFunctorPullbackComparison
import Mettapedia.CategoryTheory.CanonicalSlicePullback
import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Coherent complete pullback comparisons

The comparison of a finite-limit functor with chosen slice pullbacks is
fixed by both projections. The resulting equations compare actual functor
composition, identity, and pasting of base routes, retaining the complete
display map. No chosen pullback objects are identified by assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Mettapedia.CategoryTheory.SliceFunctorPullbackCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits
open SliceFunctorPullbackComparison

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
variable {D : Type u₂} [Category.{v₂} D] [HasPullbacks D]
variable {E : Type u₃} [Category.{v₃} E] [HasPullbacks E]
variable (F : C ⥤ D) [PreservesFiniteLimits F]
variable (G : D ⥤ E) [PreservesFiniteLimits G]
variable {X Y : C} (route : X ⟶ Y)

/-- Both complete projections determine the selected comparison. -/
theorem component_unique (display : Over Y)
    (candidate : (Over.pullback route ⋙ Over.post F).obj display ⟶
      (Over.post F ⋙ Over.pullback (F.map route)).obj display)
    (first : candidate.left ≫ pullback.fst (F.map display.hom) (F.map route) =
      F.map (pullback.fst display.hom route))
    (second : candidate.left ≫ pullback.snd (F.map display.hom) (F.map route) =
      F.map (pullback.snd display.hom route)) :
    candidate = (component F route display).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact first.trans (component_first F route display).symm
  · exact second.trans (component_second F route display).symm

@[reassoc (attr := simp)] theorem component_inverse_first (display : Over Y) :
    (component F route display).inv.left ≫ F.map (pullback.fst display.hom route) =
      pullback.fst (F.map display.hom) (F.map route) := by
  rw [← component_first F route display, ← Category.assoc]
  have cancel := congrArg (fun arrow => arrow.left) (component F route display).inv_hom_id
  change (component F route display).inv.left ≫ (component F route display).hom.left =
    𝟙 _ at cancel
  rw [cancel, Category.id_comp]

@[reassoc (attr := simp)] theorem component_inverse_second (display : Over Y) :
    (component F route display).inv.left ≫ F.map (pullback.snd display.hom route) =
      pullback.snd (F.map display.hom) (F.map route) := by
  rw [← component_second F route display, ← Category.assoc]
  have cancel := congrArg (fun arrow => arrow.left) (component F route display).inv_hom_id
  change (component F route display).inv.left ≫ (component F route display).hom.left =
    𝟙 _ at cancel
  rw [cancel, Category.id_comp]

def postIdentity (base : C) : Over.post (X := base) (𝟭 C) ≅ 𝟭 (Over base) :=
  NatIso.ofComponents (fun display => Over.isoMk (Iso.refl display.left) (by
    change 𝟙 display.left ≫ display.hom = display.hom
    exact Category.id_comp _)) (by
    intro first second square
    apply Over.OverMorphism.ext
    change square.left ≫ 𝟙 _ = 𝟙 _ ≫ square.left
    rw [Category.comp_id, Category.id_comp])

def identityComparison : Over.pullback route ⋙ Over.post (𝟭 C) ≅
    Over.post (𝟭 C) ⋙ Over.pullback route :=
  isoWhiskerLeft (Over.pullback route) (postIdentity X) ≪≫
    Functor.rightUnitor (Over.pullback route) ≪≫
    (Functor.leftUnitor (Over.pullback route)).symm ≪≫
    isoWhiskerRight (postIdentity Y).symm (Over.pullback route)

theorem comparison_identity : comparison (𝟭 C) route = identityComparison route := by
  apply Iso.ext
  apply NatTrans.ext
  funext display
  apply Over.OverMorphism.ext
  change (component (𝟭 C) route display).hom.left =
    (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
      ((Over.pullback route).map ((postIdentity Y).inv.app display)).left)
  simp only [Category.id_comp]
  apply pullback.hom_ext
  · change (component (𝟭 C) route display).hom.left ≫ pullback.fst display.hom route =
      ((Over.pullback route).map ((postIdentity Y).inv.app display)).left ≫
        pullback.fst display.hom route
    calc
      _ = pullback.fst display.hom route := component_first (𝟭 C) route display
      _ = _ := by
        have readout := pullback_first_readout route ((postIdentity Y).inv.app display)
        change ((Over.pullback route).map ((postIdentity Y).inv.app display)).left ≫
          pullback.fst display.hom route = pullback.fst display.hom route ≫ 𝟙 _ at readout
        simpa only [Category.comp_id] using readout.symm
  · change (component (𝟭 C) route display).hom.left ≫ pullback.snd display.hom route =
      ((Over.pullback route).map ((postIdentity Y).inv.app display)).left ≫
        pullback.snd display.hom route
    exact (component_second (𝟭 C) route display).trans
      (pullback_second_readout route ((postIdentity Y).inv.app display)).symm

/-- Compose the two independently constructed complete comparison maps. -/
def compositionComparison : Over.pullback route ⋙ Over.post (F ⋙ G) ≅
    Over.post (F ⋙ G) ⋙ Over.pullback ((F ⋙ G).map route) :=
  isoWhiskerLeft (Over.pullback route) (Over.postComp F G) ≪≫
    (Functor.associator (Over.pullback route) (Over.post F) (Over.post G)).symm ≪≫
    isoWhiskerRight (comparison F route) (Over.post G) ≪≫
    Functor.associator (Over.post F) (Over.pullback (F.map route)) (Over.post G) ≪≫
    isoWhiskerLeft (Over.post F) (comparison G (F.map route)) ≪≫
    (Functor.associator (Over.post F) (Over.post G)
      (Over.pullback ((F ⋙ G).map route))).symm ≪≫
    isoWhiskerRight (Over.postComp F G).symm (Over.pullback ((F ⋙ G).map route))

theorem component_composition (display : Over Y) :
    (component (F ⋙ G) route display).hom =
      (Over.post G).map (component F route display).hom ≫
        (component G (F.map route) ((Over.post F).obj display)).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (component (F ⋙ G) route display).hom.left ≫
        pullback.fst (G.map (F.map display.hom)) (G.map (F.map route)) =
      (G.map (component F route display).hom.left ≫
        (component G (F.map route) ((Over.post F).obj display)).hom.left) ≫
        pullback.fst (G.map (F.map display.hom)) (G.map (F.map route))
    calc
      _ = G.map (F.map (pullback.fst display.hom route)) :=
        component_first (F ⋙ G) route display
      _ = G.map ((component F route display).hom.left ≫
          pullback.fst (F.map display.hom) (F.map route)) :=
        congrArg (fun arrow => G.map arrow) (component_first F route display).symm
      _ = G.map (component F route display).hom.left ≫
          G.map (pullback.fst (F.map display.hom) (F.map route)) := G.map_comp _ _
      _ = G.map (component F route display).hom.left ≫
          (component G (F.map route) ((Over.post F).obj display)).hom.left ≫
            pullback.fst (G.map (F.map display.hom)) (G.map (F.map route)) :=
        congrArg (fun arrow => G.map (component F route display).hom.left ≫ arrow)
          (component_first G (F.map route) ((Over.post F).obj display)).symm
      _ = _ := (Category.assoc _ _ _).symm
  · change (component (F ⋙ G) route display).hom.left ≫
        pullback.snd (G.map (F.map display.hom)) (G.map (F.map route)) =
      (G.map (component F route display).hom.left ≫
        (component G (F.map route) ((Over.post F).obj display)).hom.left) ≫
        pullback.snd (G.map (F.map display.hom)) (G.map (F.map route))
    calc
      _ = G.map (F.map (pullback.snd display.hom route)) :=
        component_second (F ⋙ G) route display
      _ = G.map ((component F route display).hom.left ≫
          pullback.snd (F.map display.hom) (F.map route)) :=
        congrArg (fun arrow => G.map arrow) (component_second F route display).symm
      _ = G.map (component F route display).hom.left ≫
          G.map (pullback.snd (F.map display.hom) (F.map route)) := G.map_comp _ _
      _ = G.map (component F route display).hom.left ≫
          (component G (F.map route) ((Over.post F).obj display)).hom.left ≫
            pullback.snd (G.map (F.map display.hom)) (G.map (F.map route)) :=
        congrArg (fun arrow => G.map (component F route display).hom.left ≫ arrow)
          (component_second G (F.map route) ((Over.post F).obj display)).symm
      _ = _ := (Category.assoc _ _ _).symm

theorem comparison_composition : comparison (F ⋙ G) route =
    compositionComparison F G route := by
  apply Iso.ext
  apply NatTrans.ext
  funext display
  change (component (F ⋙ G) route display).hom = _
  simpa [compositionComparison, Over.postComp, comparison] using
    component_composition F G route display

theorem comparison_composition_inverse (display : Over Y) :
    (comparison (F ⋙ G) route).inv.app display =
      (comparison G (F.map route)).inv.app ((Over.post F).obj display) ≫
        (Over.post G).map ((comparison F route).inv.app display) := by
  rw [comparison_composition]
  simp [compositionComparison, Over.postComp]

theorem route_identity (display : Over Y) :
    (Over.post F).map ((CanonicalSlicePullback.identity Y).hom.app display) =
      (comparison F (𝟙 Y)).hom.app display ≫
        (CanonicalSlicePullback.transport (F.map_id Y)).hom.app ((Over.post F).obj display) ≫
        (CanonicalSlicePullback.identity (F.obj Y)).hom.app ((Over.post F).obj display) := by
  apply Over.OverMorphism.ext
  change F.map ((CanonicalSlicePullback.identity Y).hom.app display).left = _
  simp only [CanonicalSlicePullback.identity, NatIso.ofComponents_hom_app,
    CanonicalSlicePullback.identityComponent_left, Over.comp_left,
    CanonicalSlicePullback.transport_fst, comparison]
  exact (component_first F (𝟙 Y) display).symm

theorem route_composition {Z : C} (next : Y ⟶ Z) (display : Over Z) :
    (Over.post F).map
        ((CanonicalSlicePullback.compositionInverse route next).hom.app display) ≫
      (comparison F (route ≫ next)).hom.app display =
    (comparison F route).hom.app ((Over.pullback next).obj display) ≫
      (Over.pullback (F.map route)).map ((comparison F next).hom.app display) ≫
      (CanonicalSlicePullback.compositionInverse (F.map route) (F.map next)).hom.app
        ((Over.post F).obj display) ≫
      (CanonicalSlicePullback.transport (F.map_comp route next).symm).hom.app
        ((Over.post F).obj display) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (F.map ((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫
        (component F (route ≫ next) display).hom.left) ≫
        pullback.fst (F.map display.hom) (F.map (route ≫ next)) = _
    calc
      _ = F.map ((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫
          F.map (pullback.fst display.hom (route ≫ next)) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun arrow =>
            F.map ((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫ arrow)
            (component_first F (route ≫ next) display))
      _ = F.map (((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫
          pullback.fst display.hom (route ≫ next)) := (F.map_comp _ _).symm
      _ = F.map (pullback.fst (pullback.snd display.hom next) route ≫
          pullback.fst display.hom next) :=
        congrArg (fun arrow => F.map arrow)
          (CanonicalSlicePullback.compositionInverseComponent_fst route next display)
      _ = _ := by
        symm
        simp only [Over.comp_left, Category.assoc, CanonicalSlicePullback.transport_fst,
          CanonicalSlicePullback.compositionInverse, NatIso.ofComponents_hom_app,
          CanonicalSlicePullback.compositionInverseComponent_fst]
        change (component F route ((Over.pullback next).obj display)).hom.left ≫
            ((Over.pullback (F.map route)).map (component F next display).hom).left ≫
            pullback.fst (pullback.snd (F.map display.hom) (F.map next)) (F.map route) ≫
            pullback.fst (F.map display.hom) (F.map next) = _
        calc
          _ = (component F route ((Over.pullback next).obj display)).hom.left ≫
              (((Over.pullback (F.map route)).map (component F next display).hom).left ≫
                pullback.fst (pullback.snd (F.map display.hom) (F.map next)) (F.map route)) ≫
              pullback.fst (F.map display.hom) (F.map next) := by
            simp only [Category.assoc]
          _ = (component F route ((Over.pullback next).obj display)).hom.left ≫
              (pullback.fst (F.map (pullback.snd display.hom next)) (F.map route) ≫
                (component F next display).hom.left) ≫
              pullback.fst (F.map display.hom) (F.map next) :=
            congrArg (fun arrow =>
              (component F route ((Over.pullback next).obj display)).hom.left ≫ arrow ≫
                pullback.fst (F.map display.hom) (F.map next))
              (pullback_first_readout (F.map route) (component F next display).hom)
          _ = ((component F route ((Over.pullback next).obj display)).hom.left ≫
              pullback.fst (F.map (pullback.snd display.hom next)) (F.map route)) ≫
              ((component F next display).hom.left ≫
                pullback.fst (F.map display.hom) (F.map next)) := by
            simp only [Category.assoc]
          _ = F.map (pullback.fst (pullback.snd display.hom next) route) ≫
              F.map (pullback.fst display.hom next) :=
            congrArg₂ (fun earlier later => earlier ≫ later)
              (component_first F route ((Over.pullback next).obj display))
              (component_first F next display)
          _ = _ := (F.map_comp _ _).symm
  · change (F.map ((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫
        (component F (route ≫ next) display).hom.left) ≫
        pullback.snd (F.map display.hom) (F.map (route ≫ next)) = _
    calc
      _ = F.map ((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫
          F.map (pullback.snd display.hom (route ≫ next)) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun arrow =>
            F.map ((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫ arrow)
            (component_second F (route ≫ next) display))
      _ = F.map (((CanonicalSlicePullback.compositionInverse route next).hom.app display).left ≫
          pullback.snd display.hom (route ≫ next)) := (F.map_comp _ _).symm
      _ = F.map (pullback.snd (pullback.snd display.hom next) route) :=
        congrArg (fun arrow => F.map arrow)
          (CanonicalSlicePullback.compositionInverseComponent_snd route next display)
      _ = _ := by
        symm
        simp only [Over.comp_left, Category.assoc, CanonicalSlicePullback.transport_snd,
          CanonicalSlicePullback.compositionInverse, NatIso.ofComponents_hom_app,
          CanonicalSlicePullback.compositionInverseComponent_snd]
        change (component F route ((Over.pullback next).obj display)).hom.left ≫
            ((Over.pullback (F.map route)).map (component F next display).hom).left ≫
            pullback.snd (pullback.snd (F.map display.hom) (F.map next)) (F.map route) = _
        calc
          _ = (component F route ((Over.pullback next).obj display)).hom.left ≫
              pullback.snd (F.map (pullback.snd display.hom next)) (F.map route) :=
            congrArg (fun arrow =>
              (component F route ((Over.pullback next).obj display)).hom.left ≫ arrow)
              (pullback_second_readout (F.map route) (component F next display).hom)
          _ = _ := component_second F route ((Over.pullback next).obj display)

theorem transport_inverse {first second : C} {earlier later : first ⟶ second}
    (same : earlier = later) :
    (CanonicalSlicePullback.transport same).inv =
      (CanonicalSlicePullback.transport same.symm).hom := by
  cases same
  rfl

section OrdinaryCells

variable {H : C ⥤ D} (cell : F ⟶ H)

/-- An ordinary theory cell gives a lax pullback comparison. The complete
input stays unchanged; its base map is the supplied cell component. -/
def ordinaryUnderlying (display : Over (F.obj Y)) :
    pullback display.hom (F.map route) ⟶
      pullback (display.hom ≫ cell.app Y) (H.map route) :=
  pullback.lift (pullback.fst display.hom (F.map route))
    (pullback.snd display.hom (F.map route) ≫ cell.app X) (by
      rw [← Category.assoc, pullback.condition, Category.assoc, cell.naturality,
        ← Category.assoc])

omit [HasPullbacks C] [PreservesFiniteLimits F] in
@[reassoc (attr := simp)] theorem ordinaryUnderlying_first (display : Over (F.obj Y)) :
    ordinaryUnderlying F route cell display ≫
        pullback.fst (display.hom ≫ cell.app Y) (H.map route) =
      pullback.fst display.hom (F.map route) :=
  pullback.lift_fst _ _ _

omit [HasPullbacks C] [PreservesFiniteLimits F] in
@[reassoc (attr := simp)] theorem ordinaryUnderlying_second (display : Over (F.obj Y)) :
    ordinaryUnderlying F route cell display ≫
        pullback.snd (display.hom ≫ cell.app Y) (H.map route) =
      pullback.snd display.hom (F.map route) ≫ cell.app X :=
  pullback.lift_snd _ _ _

def ordinaryComparison :
    Over.pullback (F.map route) ⋙ Over.map (cell.app X) ⟶
      Over.map (cell.app Y) ⋙ Over.pullback (H.map route) where
  app display := Over.homMk (ordinaryUnderlying F route cell display)
    (ordinaryUnderlying_second F route cell display)
  naturality := by
    intro first second square
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (((Over.pullback (F.map route)).map square).left ≫
          ordinaryUnderlying F route cell second) ≫
          pullback.fst (second.hom ≫ cell.app Y) (H.map route) =
        (ordinaryUnderlying F route cell first ≫
          ((Over.pullback (H.map route)).map ((Over.map (cell.app Y)).map square)).left) ≫
          pullback.fst (second.hom ≫ cell.app Y) (H.map route)
      rw [Category.assoc, ordinaryUnderlying_first, pullback_first_readout]
      have targetRead := pullback_first_readout (H.map route) ((Over.map (cell.app Y)).map square)
      change ((Over.pullback (H.map route)).map ((Over.map (cell.app Y)).map square)).left ≫
        pullback.fst (second.hom ≫ cell.app Y) (H.map route) =
        pullback.fst (first.hom ≫ cell.app Y) (H.map route) ≫ square.left at targetRead
      rw [Category.assoc, targetRead, ← Category.assoc, ordinaryUnderlying_first]
    · change (((Over.pullback (F.map route)).map square).left ≫
          ordinaryUnderlying F route cell second) ≫
          pullback.snd (second.hom ≫ cell.app Y) (H.map route) =
        (ordinaryUnderlying F route cell first ≫
          ((Over.pullback (H.map route)).map ((Over.map (cell.app Y)).map square)).left) ≫
          pullback.snd (second.hom ≫ cell.app Y) (H.map route)
      rw [Category.assoc, ordinaryUnderlying_second, ← Category.assoc,
        pullback_second_readout]
      have targetRead := pullback_second_readout (H.map route) ((Over.map (cell.app Y)).map square)
      change ((Over.pullback (H.map route)).map ((Over.map (cell.app Y)).map square)).left ≫
        pullback.snd (second.hom ≫ cell.app Y) (H.map route) =
        pullback.snd (first.hom ≫ cell.app Y) (H.map route) at targetRead
      rw [Category.assoc, targetRead, ordinaryUnderlying_second]

/-- The ordinary cell and both independently chosen complete pullback
comparisons form an actual commuting square. No inverse to the ordinary
cell or its lax comparison is required. -/
theorem ordinary_comparison_square [PreservesFiniteLimits H] (display : Over Y) :
    (Over.map (cell.app X)).map ((comparison F route).hom.app display) ≫
        (ordinaryComparison F route cell).app ((Over.post F).obj display) ≫
        (Over.pullback (H.map route)).map ((Over.postMap cell).app display) =
      (Over.postMap cell).app ((Over.pullback route).obj display) ≫
        (comparison H route).hom.app display := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((component F route display).hom.left ≫
          (ordinaryUnderlying F route cell ((Over.post F).obj display) ≫
            ((Over.pullback (H.map route)).map ((Over.postMap cell).app display)).left)) ≫
          pullback.fst (H.map display.hom) (H.map route) =
        (cell.app (pullback display.hom route) ≫ (component H route display).hom.left) ≫
          pullback.fst (H.map display.hom) (H.map route)
    have transported := pullback_first_readout (H.map route) ((Over.postMap cell).app display)
    change ((Over.pullback (H.map route)).map ((Over.postMap cell).app display)).left ≫
        pullback.fst (H.map display.hom) (H.map route) =
      pullback.fst (F.map display.hom ≫ cell.app Y) (H.map route) ≫
        cell.app display.left at transported
    have ordinary := ordinaryUnderlying_first F route cell ((Over.post F).obj display)
    change ordinaryUnderlying F route cell ((Over.post F).obj display) ≫
        pullback.fst (F.map display.hom ≫ cell.app Y) (H.map route) =
      pullback.fst (F.map display.hom) (F.map route) at ordinary
    calc
      _ = (component F route display).hom.left ≫
          ordinaryUnderlying F route cell ((Over.post F).obj display) ≫
          (pullback.fst (F.map display.hom ≫ cell.app Y) (H.map route) ≫
            cell.app display.left) := by rw [Category.assoc, Category.assoc, transported]
      _ = (component F route display).hom.left ≫
          (pullback.fst (F.map display.hom) (F.map route) ≫ cell.app display.left) :=
        (congrArg (fun arrow => (component F route display).hom.left ≫ arrow)
          (Category.assoc (ordinaryUnderlying F route cell ((Over.post F).obj display))
            (pullback.fst (F.map display.hom ≫ cell.app Y) (H.map route))
            (cell.app display.left)).symm).trans
          (congrArg (fun arrow => (component F route display).hom.left ≫
            (arrow ≫ cell.app display.left)) ordinary)
      _ = F.map (pullback.fst display.hom route) ≫ cell.app display.left :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun arrow => arrow ≫ cell.app display.left) (component_first F route display))
      _ = cell.app (pullback display.hom route) ≫ H.map (pullback.fst display.hom route) :=
        cell.naturality _
      _ = _ := (congrArg (fun arrow => cell.app (pullback display.hom route) ≫ arrow)
        (component_first H route display).symm).trans (Category.assoc _ _ _).symm
  · change ((component F route display).hom.left ≫
          (ordinaryUnderlying F route cell ((Over.post F).obj display) ≫
            ((Over.pullback (H.map route)).map ((Over.postMap cell).app display)).left)) ≫
          pullback.snd (H.map display.hom) (H.map route) =
        (cell.app (pullback display.hom route) ≫ (component H route display).hom.left) ≫
          pullback.snd (H.map display.hom) (H.map route)
    have transported := pullback_second_readout (H.map route) ((Over.postMap cell).app display)
    change ((Over.pullback (H.map route)).map ((Over.postMap cell).app display)).left ≫
        pullback.snd (H.map display.hom) (H.map route) =
      pullback.snd (F.map display.hom ≫ cell.app Y) (H.map route) at transported
    calc
      _ = (component F route display).hom.left ≫
          (ordinaryUnderlying F route cell ((Over.post F).obj display) ≫
            pullback.snd (F.map display.hom ≫ cell.app Y) (H.map route)) := by
        rw [Category.assoc, Category.assoc, transported]
      _ = (component F route display).hom.left ≫
          (pullback.snd (F.map display.hom) (F.map route) ≫ cell.app X) :=
        congrArg (fun arrow => (component F route display).hom.left ≫ arrow)
          (ordinaryUnderlying_second F route cell ((Over.post F).obj display))
      _ = F.map (pullback.snd display.hom route) ≫ cell.app X :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun arrow => arrow ≫ cell.app X) (component_second F route display))
      _ = cell.app (pullback display.hom route) ≫ H.map (pullback.snd display.hom route) :=
        cell.naturality _
      _ = _ := (congrArg (fun arrow => cell.app (pullback display.hom route) ≫ arrow)
        (component_second H route display).symm).trans (Category.assoc _ _ _).symm

end OrdinaryCells

end Mettapedia.CategoryTheory.SliceFunctorPullbackCoherence
