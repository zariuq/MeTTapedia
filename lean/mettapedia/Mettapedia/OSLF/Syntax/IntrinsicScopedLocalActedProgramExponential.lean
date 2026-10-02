import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramProducts
import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionEquations

/-!
# Selected program powers from actual contextual assignments

Fresh nullary declarations encode ordinary parameters in the authored
quotient. The comparison uses the actual chosen products, with their order
made explicit, rather than presuming that a representable is an exponential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open SecondOrderContext SecondOrderVariableAbstraction
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier

variable {S : Signature} {K : List (MetaArity S)} (equations : List (EqAxiom S K))

/-- Adjoining fresh ordinary parameters retains equation-related assignments. -/
theorem liftAssignment_related (Γ : Ctx S) {X Y : Object S} {f g : X ⟶ Y}
    (related : (authoredEquationPresentation S equations).homRel f g) :
    (authoredEquationPresentation S equations).homRel
      (X := ⟨extendedMetas Γ X.arities⟩) (Y := ⟨extendedMetas Γ Y.arities⟩)
      (liftAssignment Γ f) (liftAssignment Γ g) := by
  induction Γ generalizing X Y with
  | nil => exact related
  | cons a Γ ih =>
      apply ih (X := ⟨headMetas a X.arities⟩) (Y := ⟨headMetas a Y.arities⟩)
      intro i
      rcases i with ⟨n, bound⟩
      cases n with
      | zero => exact .refl _
      | succ n =>
          change EqClosure ((authoredEquationPresentation S equations).axioms
            (⟨headMetas a X.arities⟩ : Object S))
            (shift a (f ⟨n, Nat.lt_of_succ_lt_succ bound⟩))
            (shift a (g ⟨n, Nat.lt_of_succ_lt_succ bound⟩))
          exact instInto_eqClosure_generators
            ((authoredEquationPresentation S equations).axioms ⟨headMetas a X.arities⟩)
            (shiftAssignment a)
            ((authoredEquationPresentation S equations).generator_substitute (shiftAssignment a))
            (related ⟨n, Nat.lt_of_succ_lt_succ bound⟩)

/-- Fresh-parameter extension is a functor on the actual quotient context category. -/
def parameterExtension (Γ : Ctx S) : Base equations ⥤ Base equations where
  obj X := (authoredEquationPresentation S equations).quotientFunctor.obj
    ⟨extendedMetas Γ X.as.arities⟩
  map f := Quot.liftOn f
    (fun raw => (authoredEquationPresentation S equations).quotientFunctor.map
      (X := ⟨extendedMetas Γ _⟩) (Y := ⟨extendedMetas Γ _⟩) (liftAssignment Γ raw))
    (by
      intro f g related
      apply _root_.CategoryTheory.Quotient.sound
      apply liftAssignment_related equations Γ
      simpa only [HomRel.compClosure_eq_self] using related)
  map_id X := by
    change Quot.mk _ (liftAssignment Γ (𝟙 X.as)) = Quot.mk _ _
    exact congrArg (Quot.mk _) (liftAssignment_id Γ)
  map_comp f g := by
    induction f using Quot.ind with
    | _ f =>
      induction g using Quot.ind with
      | _ g =>
        change Quot.mk _ (liftAssignment Γ (f ≫ g)) =
          Quot.mk _ (fun i => instInto (liftAssignment Γ f) (liftAssignment Γ g i))
        exact congrArg (Quot.mk _) (liftAssignment_comp Γ g f)

/-- The functor computes on genuine assignment representatives. -/
theorem parameterExtension_map_mk (Γ : Ctx S) {X Y : Object S} (f : X ⟶ Y) :
    (parameterExtension equations Γ).map
        ((authoredEquationPresentation S equations).quotientFunctor.map f) =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (X := ⟨extendedMetas Γ X.arities⟩) (Y := ⟨extendedMetas Γ Y.arities⟩)
        (liftAssignment Γ f) := rfl

/-- Extending by one nullary declaration is the raw product assignment. -/
theorem headAssignment_pair (a : S.Srt) (X Y : Object S) (f : X ⟶ Y) :
    pair S (productObject S (single S [] a) X) (single S [] a) Y
      (firstProjection S (single S [] a) X)
      (secondProjection S (single S [] a) X ≫ f) = liftHeadAssignment a f := by
  funext i
  rcases i with ⟨n, bound⟩
  cases n with
  | zero => rfl
  | succ n =>
      change instInto (shiftAssignment a) (f ⟨n, Nat.lt_of_succ_lt_succ bound⟩) = _
      rfl

/-- A one-parameter extension is the product with that parameter, using the
actual product cone of the equation context category. -/
def headParameterIso (a : S.Srt) (X : Base equations) :
    (parameterExtension equations [a]).obj X ≅
      (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] a) ⨯ X :=
  (quotientProductIsLimit (authoredEquationPresentation S equations)
    (single S [] a) X.as).conePointUniqueUpToIso (limit.isLimit _)


/-- The product comparison retains the fresh parameter projection. -/
theorem headParameterIso_fst (a : S.Srt) (X : Base equations) :
    (headParameterIso equations a X).hom ≫ prod.fst =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (firstProjection S (single S [] a) X.as) := by
  exact (quotientProductIsLimit (authoredEquationPresentation S equations)
    (single S [] a) X.as).conePointUniqueUpToIso_hom_comp (limit.isLimit _)
      ⟨WalkingPair.left⟩

/-- The product comparison retains every old metavariable projection. -/
theorem headParameterIso_snd (a : S.Srt) (X : Base equations) :
    (headParameterIso equations a X).hom ≫ prod.snd =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (secondProjection S (single S [] a) X.as) := by
  exact (quotientProductIsLimit (authoredEquationPresentation S equations)
    (single S [] a) X.as).conePointUniqueUpToIso_hom_comp (limit.isLimit _)
      ⟨WalkingPair.right⟩

/-- The one-parameter product comparison is natural on all equation-class maps. -/
theorem headParameterIso_natural (a : S.Srt) {X Y : Base equations} (f : X ⟶ Y) :
    (parameterExtension equations [a]).map f ≫ (headParameterIso equations a Y).hom =
      (headParameterIso equations a X).hom ≫ prod.map (𝟙 _) f := by
  apply prod.hom_ext
  · rw [Category.assoc, headParameterIso_fst, Category.assoc, prod.map_fst,
      ← Category.assoc, headParameterIso_fst, Category.comp_id]
    induction f using Quot.ind with
    | _ f =>
      change (authoredEquationPresentation S equations).quotientFunctor.map
          (liftHeadAssignment a f ≫ firstProjection S (single S [] a) Y.as) =
        (authoredEquationPresentation S equations).quotientFunctor.map
          (firstProjection S (single S [] a) X.as)
      apply congrArg (authoredEquationPresentation S equations).quotientFunctor.map
      exact (congrArg (fun h : productObject S (single S [] a) X.as ⟶
          productObject S (single S [] a) Y.as => h ≫ firstProjection S (single S [] a) Y.as)
          (headAssignment_pair a X.as Y.as f).symm).trans
        (pair_first S _ _ _ _ _)
  · rw [Category.assoc, headParameterIso_snd, Category.assoc, prod.map_snd,
      ← Category.assoc, headParameterIso_snd]
    induction f using Quot.ind with
    | _ f =>
      change (authoredEquationPresentation S equations).quotientFunctor.map
          (liftHeadAssignment a f ≫ secondProjection S (single S [] a) Y.as) =
        (authoredEquationPresentation S equations).quotientFunctor.map
          (secondProjection S (single S [] a) X.as ≫ f)
      apply congrArg (authoredEquationPresentation S equations).quotientFunctor.map
      exact (congrArg (fun h : productObject S (single S [] a) X.as ⟶
          productObject S (single S [] a) Y.as => h ≫ secondProjection S (single S [] a) Y.as)
          (headAssignment_pair a X.as Y.as f).symm).trans
        (pair_second S _ _ _ _ _)

/-- One fresh-parameter extension is naturally the ordinary product functor. -/
def headParameterNatIso (a : S.Srt) :
    parameterExtension equations [a] ≅
      prod.functor.obj ((authoredEquationPresentation S equations).quotientFunctor.obj
        (single S [] a)) :=
  NatIso.ofComponents (headParameterIso equations a) (fun f => headParameterIso_natural equations a f)

/-- Parameter products follow the reverse declaration order of full abstraction. -/
def parameterContext : Ctx S → Base equations
  | [] => ⊤_ (Base equations)
  | a :: Γ => parameterContext Γ ⨯
      (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] a)

/-- Recursive abstraction is recursive functor composition on actual quotient maps. -/
def parameterExtensionConsIso (a : S.Srt) (Γ : Ctx S) :
    parameterExtension equations (a :: Γ) ≅
      parameterExtension equations [a] ⋙ parameterExtension equations Γ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    induction f using Quot.ind with
    | _ f =>
      change (parameterExtension equations (a :: Γ)).map
          ((authoredEquationPresentation S equations).quotientFunctor.map f) ≫ 𝟙 _ =
        𝟙 _ ≫ (parameterExtension equations Γ).map
          ((parameterExtension equations [a]).map
            ((authoredEquationPresentation S equations).quotientFunctor.map f))
      rw [Category.comp_id, Category.id_comp]
      rfl)


/-- The empty parameter extension acts identically on every quotient map. -/
theorem parameterExtension_nil_map {X Y : Base equations} (f : X ⟶ Y) :
    (parameterExtension equations []).map f = f := by
  induction f using Quot.ind with
  | _ f => rfl

/-- All fresh parameters form an actual product factor, naturally on every
quotient assignment. The recursive order agrees with full abstraction. -/
def parameterProductNatIso : (Γ : Ctx S) →
    parameterExtension equations Γ ≅ prod.functor.obj (parameterContext equations Γ)
  | [] => NatIso.ofComponents (fun X => (prod.leftUnitor X).symm) (by
      intro X Y f
      change (parameterExtension equations []).map f ≫ (prod.leftUnitor Y).inv =
        (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f
      rw [parameterExtension_nil_map]
      exact (prod.leftUnitor_inv_naturality f).symm)
  | a :: Γ =>
      parameterExtensionConsIso equations a Γ ≪≫
        isoWhiskerLeft (parameterExtension equations [a]) (parameterProductNatIso Γ) ≪≫
        isoWhiskerRight (headParameterNatIso equations a)
          (prod.functor.obj (parameterContext equations Γ)) ≪≫
        (prod.functorLeftComp (parameterContext equations Γ)
          ((authoredEquationPresentation S equations).quotientFunctor.obj (single S [] a))).symm

/-- The explicit order adapter places the stage before the fresh parameter
factor, while retaining the reverse fresh-declaration order. -/
def extensionProductIso (Γ : Ctx S) (X : Base equations) :
    (parameterExtension equations Γ).obj X ≅ X ⨯ parameterContext equations Γ :=
  (parameterProductNatIso equations Γ).app X ≪≫ prod.braiding _ _

/-- The order adapter respects arbitrary, possibly noninjective assignments. -/
theorem extensionProductIso_natural (Γ : Ctx S) {X Y : Base equations} (f : X ⟶ Y) :
    (parameterExtension equations Γ).map f ≫ (extensionProductIso equations Γ Y).hom =
      (extensionProductIso equations Γ X).hom ≫ prod.map f (𝟙 _) := by
  change (parameterExtension equations Γ).map f ≫
      (parameterProductNatIso equations Γ).hom.app Y ≫ (prod.braiding _ _).hom =
    ((parameterProductNatIso equations Γ).hom.app X ≫ (prod.braiding _ _).hom) ≫ _
  rw [← Category.assoc, (parameterProductNatIso equations Γ).hom.naturality]
  change ((parameterProductNatIso equations Γ).hom.app X ≫ prod.map (𝟙 _) f) ≫
      (prod.braiding _ _).hom =
    ((parameterProductNatIso equations Γ).hom.app X ≫ (prod.braiding _ _).hom) ≫ _
  rw [Category.assoc, braid_natural, ← Category.assoc]

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
