import Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContextsInterpretation

/-!
# Structural substitution and the dependent pair context

The independently generated frame maps are interpreted by actual context
maps. Their object projection equations are derived from the constructor
operations. Packing and unpacking use the existing native dependent-sum
comprehension isomorphism and retain both supplied witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open Mettapedia.TypeTheory.DisplayedPresheafSliceSigma

universe u w
variable {C : Type u} [Category.{u} C] {Constant Predicate : Type u}
variable (D : Cᵒᵖ ⥤ Type u) (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u,u,u,u} D)
variable {Declaration : (n : Nat) → Formula Constant Predicate n → Type w}
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (PresheafInterpretation.family D constants predicates formula).sections)

/-- Context lifting over an explicitly proved family comparison. -/
noncomputable def liftAlong {P Q : Cᵒᵖ ⥤ Type u} (change : P ⟶ Q)
    (A : DisplayedFamily.{u,u,u,u} P) (B : DisplayedFamily.{u,u,u,u} Q)
    (same : A = reindexDisplayed change B) : totalSpace A ⟶ totalSpace B :=
  (eqToIso (congrArg totalSpace same)).hom ≫ totalReindexMap change B

theorem liftAlong_square {P Q : Cᵒᵖ ⥤ Type u} (change : P ⟶ Q)
    (A : DisplayedFamily.{u,u,u,u} P) (B : DisplayedFamily.{u,u,u,u} Q)
    (same : A = reindexDisplayed change B) :
    liftAlong change A B same ≫ totalProjection B = totalProjection A ≫ change := by
  subst A
  simpa only [liftAlong, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
    totalReindexMap_square change B

theorem liftAlong_first {P Q : Cᵒᵖ ⥤ Type u} (change : P ⟶ Q)
    (A : DisplayedFamily.{u,u,u,u} P) (B : DisplayedFamily.{u,u,u,u} Q)
    (same : A = reindexDisplayed change B) (point : P.Elements)
    (witness : A.obj point) :
    ((liftAlong change A B same).app point.1 ⟨point.2, witness⟩).1 = change.app point.1 point.2 := by
  subst A
  rfl

theorem liftAlong_witness {P Q : Cᵒᵖ ⥤ Type u} (change : P ⟶ Q)
    (A : DisplayedFamily.{u,u,u,u} P) (B : DisplayedFamily.{u,u,u,u} Q)
    (same : A = reindexDisplayed change B) (point : P.Elements)
    (witness : A.obj point) :
    HEq ((liftAlong change A B same).app point.1 ⟨point.2, witness⟩).2 witness := by
  subst A
  rfl

theorem liftAlong_apply {P Q : Cᵒᵖ ⥤ Type u} (change : P ⟶ Q)
    (A : DisplayedFamily.{u,u,u,u} P) (B : DisplayedFamily.{u,u,u,u} Q)
    (same : A = reindexDisplayed change B) (point : P.Elements)
    (witness : A.obj point) :
    (liftAlong change A B same).app point.1 ⟨point.2, witness⟩ =
      ⟨change.app point.1 point.2,
        cast (congrArg (fun family => family.obj point) same) witness⟩ := by
  subst A
  rfl

/-- These equations are outputs of the recursively constructed frame
interpreter, rather than laws supplied for every proof by a model record. -/
structure FrameMap {n : Nat} (source target : Scope Constant Predicate n) where
  map : context D constants predicates source ⟶ context D constants predicates target
  tuple_eq : map ≫ tuple D constants predicates target = tuple D constants predicates source

theorem legacy_frame {n : Nat} {source target : Scope Constant Predicate n}
    (change : FrameMap D constants predicates source target) (formula : Formula Constant Predicate n) :
    legacyFamily D constants predicates source formula =
      reindexDisplayed change.map (legacyFamily D constants predicates target formula) := by
  change reindexDisplayed (tuple D constants predicates source) _ =
    reindexDisplayed (change.map ≫ tuple D constants predicates target) _
  rw [change.tuple_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Interpret each structural substitution with its genuine context map. -/
noncomputable def frame : {n : Nat} → {source target : Scope Constant Predicate n} →
    FrameSubstitution Declaration source target → FrameMap D constants predicates source target
  | _, _, _, .identity _ => ⟨𝟙 _, Category.id_comp _⟩
  | _, _, _, .compose earlier later =>
      let first := frame earlier
      let second := frame later
      ⟨first.map ≫ second.map, by rw [Category.assoc, second.tuple_eq, first.tuple_eq]⟩
  | _, _, _, .dropProof scope formula =>
      ⟨totalProjection (legacyFamily D constants predicates scope formula), rfl⟩
  | _, _, _, .supplyProof term =>
      ⟨sectionLift (legacyFamily D constants predicates _ _) (evidence D constants predicates declarations term),
        by
          change (_ ≫ (totalProjection _ ≫ _)) = _
          rw [← Category.assoc, sectionLift_projection, Category.id_comp]
          rfl⟩
  | _, _, _, .objectLift change =>
      let old := frame change
      ⟨totalReindexMap old.map (ObjectInterpretation.objectFamily D (context D constants predicates _)), by
        ext point value
        apply Sigma.ext
        · exact congrArg (fun map => map.app point value.1) old.tuple_eq
        · rfl⟩
  | _, _, _, .proofLift change formula =>
      let old := frame change
      ⟨liftAlong old.map (legacyFamily D constants predicates _ formula)
        (legacyFamily D constants predicates _ formula) (legacy_frame D constants predicates old formula), by
        have square := liftAlong_square old.map
          (legacyFamily D constants predicates _ formula)
          (legacyFamily D constants predicates _ formula)
          (legacy_frame D constants predicates old formula)
        change _ ≫ (totalProjection (legacyFamily D constants predicates _ formula) ≫
          tuple D constants predicates _) = totalProjection (legacyFamily D constants predicates _ formula) ≫
          tuple D constants predicates _
        calc
          _ = (_ ≫ totalProjection (legacyFamily D constants predicates _ formula)) ≫
              tuple D constants predicates _ := (Category.assoc _ _ _).symm
          _ = (totalProjection (legacyFamily D constants predicates _ formula) ≫ old.map) ≫
              tuple D constants predicates _ := congrArg (fun map => map ≫ tuple D constants predicates _) square
          _ = totalProjection (legacyFamily D constants predicates _ formula) ≫
              (old.map ≫ tuple D constants predicates _) := Category.assoc _ _ _
          _ = _ := congrArg (fun map => totalProjection (legacyFamily D constants predicates _ formula) ≫ map)
              old.tuple_eq⟩

/-- The native sum reassociation compares the raw one-assumption context
with the raw object-and-proof context. -/
noncomputable def pairIso {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) :
    context D constants predicates (scope.sum body) ≅ context D constants predicates (scope.pair body) := by
  change totalSpace (legacyFamily D constants predicates scope (.sigma body)) ≅
    totalSpace (legacyFamily D constants predicates (.object scope) body)
  exact eqToIso (congrArg totalSpace (legacy_sigma D constants predicates scope body)) ≪≫
    sigmaTotalIso (ObjectInterpretation.objectFamily D (context D constants predicates scope))
      (legacyFamily D constants predicates (.object scope) body)

private theorem totalCast_first {P : Cᵒᵖ ⥤ Type u}
    (A B : DisplayedFamily.{u,u,u,u} P) (same : A = B) (point : P.Elements) (witness : A.obj point) :
    ((eqToIso (congrArg totalSpace same)).hom.app point.1 ⟨point.2, witness⟩).1 = point.2 := by
  subst B
  rfl

private theorem totalCast_witness {P : Cᵒᵖ ⥤ Type u}
    (A B : DisplayedFamily.{u,u,u,u} P) (same : A = B) (point : P.Elements) (witness : A.obj point) :
    HEq ((eqToIso (congrArg totalSpace same)).hom.app point.1 ⟨point.2, witness⟩).2 witness := by
  subst B
  rfl

theorem totalCast_value {P : Cᵒᵖ ⥤ Type u}
    (A B : DisplayedFamily.{u,u,u,u} P) (same : A = B) (world : Cᵒᵖ)
    (value : (totalSpace A).obj world) :
    HEq ((eqToIso (congrArg totalSpace same)).hom.app world value) value := by
  subst B
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pack_value {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (point : (context D constants predicates (scope.pair body)).Elements) :
    (pairIso D constants predicates scope body).inv.app point.1 point.2 =
      ⟨point.2.1.1, ⟨point.2.1.2, point.2.2⟩⟩ := by
  exact eq_of_heq (totalCast_value _ _ (legacy_sigma D constants predicates scope body).symm
    point.1 ⟨point.2.1.1, ⟨point.2.1.2, point.2.2⟩⟩)

set_option backward.isDefEq.respectTransparency false in
theorem pack_first {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (point : (context D constants predicates (scope.pair body)).Elements) :
    ((pairIso D constants predicates scope body).inv.app point.1 point.2).1 = point.2.1.1 := by
  exact totalCast_first _ _ (legacy_sigma D constants predicates scope body).symm
    ⟨point.1, point.2.1.1⟩ ⟨point.2.1.2, point.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem pack_pair {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (point : (context D constants predicates (scope.pair body)).Elements) :
    HEq ((pairIso D constants predicates scope body).inv.app point.1 point.2).2
      (⟨point.2.1.2, point.2.2⟩ :
        (sigmaDisplayed (ObjectInterpretation.objectFamily D (context D constants predicates scope))
          (legacyFamily D constants predicates (.object scope) body)).obj ⟨point.1, point.2.1.1⟩) := by
  exact totalCast_witness _ _ (legacy_sigma D constants predicates scope body).symm
    ⟨point.1, point.2.1.1⟩ ⟨point.2.1.2, point.2.2⟩

noncomputable def substitution : {n m : Nat} → {source : Scope Constant Predicate n} →
    {target : Scope Constant Predicate m} → ContextSubstitution Declaration source target →
      (context D constants predicates source ⟶ context D constants predicates target)
  | _, _, _, _, .frame change => (frame D constants predicates declarations change).map
  | _, _, _, _, .compose earlier later => substitution earlier ≫ substitution later
  | _, _, _, _, .pack scope body => (pairIso D constants predicates scope body).inv
  | _, _, _, _, .unpack scope body => (pairIso D constants predicates scope body).hom

@[simp] theorem pack_unpack {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) :
    substitution D constants predicates declarations (ContextSubstitution.pack scope body) ≫
        substitution D constants predicates declarations (ContextSubstitution.unpack scope body) =
      𝟙 (context D constants predicates (scope.pair body)) :=
  (pairIso D constants predicates scope body).inv_hom_id

@[simp] theorem unpack_pack {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1)) :
    substitution D constants predicates declarations (ContextSubstitution.unpack scope body) ≫
        substitution D constants predicates declarations (ContextSubstitution.pack scope body) =
      𝟙 (context D constants predicates (scope.sum body)) :=
  (pairIso D constants predicates scope body).hom_inv_id

end Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation
