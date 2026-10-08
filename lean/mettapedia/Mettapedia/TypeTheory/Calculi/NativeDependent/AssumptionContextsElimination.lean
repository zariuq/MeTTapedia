import Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContextsBinderCoherence

/-!
# Full-motive dependent pair interpretation

Primitive motive symbols denote arbitrary displayed families over their
independently authored proof contexts. The dependent pair eliminator uses
the native section equivalence for the complete pair context, transported
along the proved context comparison. Its beta and eta equations preserve
the exact two-variable branch and its evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open Mettapedia.TypeTheory.DisplayedPresheafSliceSigma

universe u w z
variable {C : Type u} [Category.{u} C] {Constant Predicate : Type u}
variable (D : Cᵒᵖ ⥤ Type u) (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u,u,u,u} D)
variable {Declaration : (n : Nat) → Formula Constant Predicate n → Type w}
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (PresheafInterpretation.family D constants predicates formula).sections)
variable {Motive : {n : Nat} → Scope Constant Predicate n → Type z}
variable (motives : ∀ {n : Nat} {scope : Scope Constant Predicate n},
  Motive scope → DisplayedFamily.{u,u,u,u} (context D constants predicates scope))

/-- Family interpretation follows only the generated formation rules;
motive meanings are supplied one primitive symbol at a time. -/
noncomputable def family : {n : Nat} → {scope : Scope Constant Predicate n} →
    Family Declaration Motive scope → DisplayedFamily.{u,u,u,u} (context D constants predicates scope)
  | _, _, .legacy scope formula => legacyFamily D constants predicates scope formula
  | _, _, .atom symbol => motives symbol
  | _, _, .reindex body change => reindexDisplayed (substitution D constants predicates declarations change)
      (family body)

/-- The native section equivalence is moved along the actual sum-context
comparison. Its computation laws do not depend on a chosen description of
the motive's evidence. -/
noncomputable def sumSectionEquiv {P : Cᵒᵖ ⥤ Type u} (A : DisplayedFamily.{u,u,u,u} P)
    (B : DisplayedFamily.{u,u,u,u} (totalSpace A)) (R : Cᵒᵖ ⥤ Type u)
    (same : R = totalSpace (sigmaDisplayed A B)) (motive : DisplayedFamily.{u,u,u,u} R) :
    (reindexDisplayed ((eqToIso same) ≪≫ sigmaTotalIso A B).inv motive).sections ≃ motive.sections := by
  subst R
  exact DisplayedPresheafSigmaElimination.sectionEquiv A B motive

theorem sumSectionEquiv_inverse {P : Cᵒᵖ ⥤ Type u} (A : DisplayedFamily.{u,u,u,u} P)
    (B : DisplayedFamily.{u,u,u,u} (totalSpace A)) (R : Cᵒᵖ ⥤ Type u)
    (same : R = totalSpace (sigmaDisplayed A B)) (motive : DisplayedFamily.{u,u,u,u} R)
    (term : motive.sections) :
    (sumSectionEquiv A B R same motive).symm term =
      reindexDisplayedSection ((eqToIso same) ≪≫ sigmaTotalIso A B).inv motive term := by
  subst R
  rfl

noncomputable def sigmaSectionEquiv {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (motive : DisplayedFamily.{u,u,u,u} (context D constants predicates (scope.sum body))) :
    (reindexDisplayed (pairIso D constants predicates scope body).inv motive).sections ≃ motive.sections :=
  sumSectionEquiv (ObjectInterpretation.objectFamily D (context D constants predicates scope))
    (legacyFamily D constants predicates (.object scope) body)
    (context D constants predicates (scope.sum body))
    (congrArg totalSpace (legacy_sigma D constants predicates scope body)) motive

theorem sigmaSectionEquiv_inverse {n : Nat} (scope : Scope Constant Predicate n)
    (body : Formula Constant Predicate (n + 1))
    (motive : DisplayedFamily.{u,u,u,u} (context D constants predicates (scope.sum body)))
    (term : motive.sections) :
    (sigmaSectionEquiv D constants predicates scope body motive).symm term =
      reindexDisplayedSection (pairIso D constants predicates scope body).inv motive term :=
  sumSectionEquiv_inverse _ _ _ _ motive term

theorem reindexSection_equal_maps {P Q : Cᵒᵖ ⥤ Type u}
    (first second : P ⟶ Q) (same : first = second) (motive : DisplayedFamily.{u,u,u,u} Q)
    (sectionValue : motive.sections) :
    (Functor.sectionsFunctor P.Elements).map
        (eqToIso (congrArg (fun map => reindexDisplayed map motive) same)).hom
        (reindexDisplayedSection first motive sectionValue) =
      reindexDisplayedSection second motive sectionValue := by
  subst second
  rfl

/-- Canonical comparison for dependent motives along an actual commuting
square of base-presheaf maps. -/
noncomputable def reindexSquareComparison {P Q R S : Cᵒᵖ ⥤ Type u}
    (first : P ⟶ Q) (top : Q ⟶ S) (left : P ⟶ R) (second : R ⟶ S)
    (square : first ≫ top = left ≫ second) (motive : DisplayedFamily.{u,u,u,u} S) :
    reindexDisplayed first (reindexDisplayed top motive) ≅
      reindexDisplayed left (reindexDisplayed second motive) :=
  eqToIso (congrArg (fun change : P ⟶ S => reindexDisplayed change motive) square)

theorem reindexSquareComparison_section {P Q R S : Cᵒᵖ ⥤ Type u}
    (first : P ⟶ Q) (top : Q ⟶ S) (left : P ⟶ R) (second : R ⟶ S)
    (square : first ≫ top = left ≫ second) (motive : DisplayedFamily.{u,u,u,u} S)
    (sectionValue : motive.sections) :
    (Functor.sectionsFunctor P.Elements).map
        (reindexSquareComparison first top left second square motive).hom
        (reindexDisplayedSection first (reindexDisplayed top motive)
          (reindexDisplayedSection top motive sectionValue)) =
      reindexDisplayedSection left (reindexDisplayed second motive)
        (reindexDisplayedSection second motive sectionValue) := by
  exact reindexSection_equal_maps (first ≫ top) (left ≫ second) square motive sectionValue

set_option backward.isDefEq.respectTransparency false in
/-- A commuting packing square determines how the actual section
equivalences transport dependent elimination. The inverse computations are
supplied by those equivalences, not an elimination-substitution axiom. -/
theorem sectionEquiv_square {P Q R S : Cᵒᵖ ⥤ Type u}
    (first : P ⟶ Q) (top : Q ⟶ S) (left : P ⟶ R) (second : R ⟶ S)
    (square : first ≫ top = left ≫ second) (motive : DisplayedFamily.{u,u,u,u} S)
    (sourceEquiv : (reindexDisplayed left (reindexDisplayed second motive)).sections ≃
      (reindexDisplayed second motive).sections)
    (targetEquiv : (reindexDisplayed top motive).sections ≃ motive.sections)
    (sourceInverse : ∀ sectionValue, sourceEquiv.symm sectionValue =
      reindexDisplayedSection left (reindexDisplayed second motive) sectionValue)
    (targetInverse : ∀ sectionValue, targetEquiv.symm sectionValue =
      reindexDisplayedSection top motive sectionValue)
    (branch : (reindexDisplayed top motive).sections) :
    sourceEquiv ((Functor.sectionsFunctor P.Elements).map
      (reindexSquareComparison first top left second square motive).hom
      (reindexDisplayedSection first (reindexDisplayed top motive) branch)) =
      reindexDisplayedSection second motive (targetEquiv branch) := by
  apply sourceEquiv.symm.injective
  rw [Equiv.symm_apply_apply, sourceInverse]
  have targetBeta : reindexDisplayedSection top motive (targetEquiv branch) = branch := by
    rw [← targetInverse]
    exact targetEquiv.symm_apply_apply branch
  conv_lhs => rw [← targetBeta]
  exact reindexSquareComparison_section first top left second square motive (targetEquiv branch)

set_option backward.isDefEq.respectTransparency false in
/-- The two lifted substitutions have the same dependent motive family
after the actual packing square, not merely pointwise inhabited fibres. -/
noncomputable def frameMotiveComparison {n : Nat} {source target : Scope Constant Predicate n}
    (change : FrameSubstitution Declaration source target) (body : Formula Constant Predicate (n + 1))
    (motive : DisplayedFamily.{u,u,u,u} (context D constants predicates (target.sum body))) :
    reindexDisplayed (frame D constants predicates declarations (.proofLift (.objectLift change) body)).map
        (reindexDisplayed (pairIso D constants predicates target body).inv motive) ≅
      reindexDisplayed (pairIso D constants predicates source body).inv
        (reindexDisplayed (frame D constants predicates declarations (.proofLift change (.sigma body))).map motive) :=
  reindexSquareComparison
    (frame D constants predicates declarations (.proofLift (.objectLift change) body)).map
    (pairIso D constants predicates target body).inv
    (pairIso D constants predicates source body).inv
    (frame D constants predicates declarations (.proofLift change (.sigma body))).map
    (pack_frame_square D constants predicates declarations change body).symm motive

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the complete two-variable branch along both independently
generated frame lifts and the canonical motive comparison. -/
noncomputable def frameBranch {n : Nat} {source target : Scope Constant Predicate n}
    (change : FrameSubstitution Declaration source target) (body : Formula Constant Predicate (n + 1))
    (motive : DisplayedFamily.{u,u,u,u} (context D constants predicates (target.sum body)))
    (branch : (reindexDisplayed (pairIso D constants predicates target body).inv motive).sections) :
    (reindexDisplayed (pairIso D constants predicates source body).inv
      (reindexDisplayed (frame D constants predicates declarations (.proofLift change (.sigma body))).map
        motive)).sections :=
  (Functor.sectionsFunctor (context D constants predicates (source.pair body)).Elements).map
    (frameMotiveComparison D constants predicates declarations change body motive).hom
    (reindexDisplayedSection
      (frame D constants predicates declarations (.proofLift (.objectLift change) body)).map
      (reindexDisplayed (pairIso D constants predicates target body).inv motive) branch)

section FrameElimination

attribute [local irreducible] tuple

set_option backward.isDefEq.respectTransparency false in
/-- Full dependent elimination commutes with the independently interpreted
frame substitution and both binder lifts. The motive comparison is explicit. -/
theorem sigmaElimination_frame {n : Nat} {source target : Scope Constant Predicate n}
    (change : FrameSubstitution Declaration source target) (body : Formula Constant Predicate (n + 1))
    (motive : DisplayedFamily.{u,u,u,u} (context D constants predicates (target.sum body)))
    (branch : (reindexDisplayed (pairIso D constants predicates target body).inv motive).sections) :
    sigmaSectionEquiv D constants predicates source body
        (reindexDisplayed (frame D constants predicates declarations (.proofLift change (.sigma body))).map motive)
        (frameBranch D constants predicates declarations change body motive branch) =
      reindexDisplayedSection (frame D constants predicates declarations (.proofLift change (.sigma body))).map
        motive (sigmaSectionEquiv D constants predicates target body motive branch) := by
  let pairMap : context D constants predicates (source.pair body) ⟶
      context D constants predicates (target.pair body) :=
    (frame D constants predicates declarations (.proofLift (.objectLift change) body)).map
  let sumMap : context D constants predicates (source.sum body) ⟶
      context D constants predicates (target.sum body) :=
    (frame D constants predicates declarations (.proofLift change (.sigma body))).map
  let oldPack : context D constants predicates (target.pair body) ⟶
      context D constants predicates (target.sum body) := (pairIso D constants predicates target body).inv
  let newPack : context D constants predicates (source.pair body) ⟶
      context D constants predicates (source.sum body) := (pairIso D constants predicates source body).inv
  have square : pairMap ≫ oldPack = newPack ≫ sumMap :=
    (pack_frame_square D constants predicates declarations change body).symm
  have sourceInverse : ∀ sectionValue,
      (sigmaSectionEquiv D constants predicates source body (reindexDisplayed sumMap motive)).symm sectionValue =
        reindexDisplayedSection newPack (reindexDisplayed sumMap motive) sectionValue :=
    sigmaSectionEquiv_inverse D constants predicates source body (reindexDisplayed sumMap motive)
  have targetInverse : ∀ sectionValue,
      (sigmaSectionEquiv D constants predicates target body motive).symm sectionValue =
        reindexDisplayedSection oldPack motive sectionValue :=
    sigmaSectionEquiv_inverse D constants predicates target body motive
  have comparison := sectionEquiv_square pairMap oldPack newPack sumMap square motive
    (sigmaSectionEquiv D constants predicates source body (reindexDisplayed sumMap motive))
    (sigmaSectionEquiv D constants predicates target body motive)
    sourceInverse targetInverse branch
  unfold frameBranch frameMotiveComparison
  exact comparison

end FrameElimination

variable {Primitive : {n : Nat} → (scope : Scope Constant Predicate n) →
  Family Declaration Motive scope → Type z}
variable (primitives : ∀ {n : Nat} {scope : Scope Constant Predicate n}
  {body : Family Declaration Motive scope}, Primitive scope body →
    (family D constants predicates declarations motives body).sections)

/-- Sound interpretation of the generated proof terms is constructed by
recursion. In particular, the dependent eliminator is not a model field. -/
noncomputable def term : {n : Nat} → {scope : Scope Constant Predicate n} →
    {body : Family Declaration Motive scope} → Term Declaration Motive Primitive n scope body →
      (family D constants predicates declarations motives body).sections
  | _, _, _, .primitive symbol => primitives symbol
  | _, _, _, .evidence proof => evidence D constants predicates declarations proof
  | _, _, _, .reindex proof change => reindexDisplayedSection
      (substitution D constants predicates declarations change) _ (term proof)
  | _, _, _, .sigmaElim scope body motive branch =>
      sigmaSectionEquiv D constants predicates scope body
        (family D constants predicates declarations motives motive) (term branch)

/-- Unpacking an eliminated term recovers the exact supplied dependent
branch, including its proof-variable witnesses. -/
theorem beta {n : Nat} (scope : Scope Constant Predicate n) (body : Formula Constant Predicate (n + 1))
    (motive : Family Declaration Motive (scope.sum body))
    (branch : Term Declaration Motive Primitive (n + 1) (scope.pair body)
      (.reindex motive (.pack scope body))) :
    term D constants predicates declarations motives primitives
        (.reindex (.sigmaElim scope body motive branch) (.pack scope body)) =
      term D constants predicates declarations motives primitives branch := by
  change reindexDisplayedSection (pairIso D constants predicates scope body).inv _
    (sigmaSectionEquiv D constants predicates scope body _ _) = _
  rw [← sigmaSectionEquiv_inverse]
  exact Equiv.symm_apply_apply _ _

theorem eta {n : Nat} (scope : Scope Constant Predicate n) (body : Formula Constant Predicate (n + 1))
    (motive : Family Declaration Motive (scope.sum body))
    (proof : Term Declaration Motive Primitive n (scope.sum body) motive) :
    term D constants predicates declarations motives primitives
        (.sigmaElim scope body motive (.reindex proof (.pack scope body))) =
      term D constants predicates declarations motives primitives proof := by
  change sigmaSectionEquiv D constants predicates scope body _
    (reindexDisplayedSection (pairIso D constants predicates scope body).inv _ _) = _
  rw [← sigmaSectionEquiv_inverse]
  exact Equiv.apply_symm_apply _ _

/-- All authored beta/eta/congruence equations are valid in the native
interpretation, for arbitrary primitive motive families. -/
theorem equation_sound {n : Nat} {scope : Scope Constant Predicate n} {body : Family Declaration Motive scope}
    {first second : Term Declaration Motive Primitive n scope body} (equation : TermEquation first second) :
    term D constants predicates declarations motives primitives first =
      term D constants predicates declarations motives primitives second := by
  induction equation with
  | refl _ => rfl
  | evidence equation => exact evidence_equation_sound D constants predicates declarations equation
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | reindex _ change ih => exact congrArg (reindexDisplayedSection _ _) ih
  | sigmaElim scope body motive _ ih => exact congrArg (sigmaSectionEquiv D constants predicates scope body _) ih
  | beta scope body motive branch => exact beta D constants predicates declarations motives primitives scope body motive branch
  | eta scope body motive proof => exact eta D constants predicates declarations motives primitives scope body motive proof

end Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation
