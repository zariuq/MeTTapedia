import Mettapedia.TypeTheory.NativeLocalTypeFormers

/-!
# Term operations for native local dependent formers

The native product decoding isomorphism transports the complete abstraction
equivalence. Application substitutes the supplied argument into its full
evaluation body. Sum terms are transported across the earned decoding
equality, retaining both supplied components. Beta and eta compare the
actual terms of the local-presentation CwF.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalTypeOperations

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafPi DisplayedPresheafSigma
open DisplayedPresheafPiSubstitution NativeLocalFunctionParameters
open ContextualLocalUniverses NativeLocalTypeFormers ContextualTypeOperations
open ContextualProductComparison (selfExtend)

universe u
variable {C : Type u} [Category.{u} C]
variable {X Y : Face.{u, u, u} C}

abbrev localModel (C : Type u) [Category.{u} C] := localCwf (presheafCwf C)

private theorem sectionTypeCast_value_heq
    {P : Face.{u, u, u} C} {A B : DisplayedFamily.{u, u, u, u} P}
    (same : A = B) (body : A.sections) (point : P.Elements) :
    HEq ((cast (congrArg (fun family : DisplayedFamily.{u, u, u, u} P =>
      (family.sections : Type u)) same) body).val point) (body.val point) := by
  cases same
  rfl

private theorem sections_heq_of_pointwise
    {P : Face.{u, u, u} C} {A B : DisplayedFamily.{u, u, u, u} P}
    (same : A = B) (first : A.sections) (second : B.sections)
    (values : ∀ point : P.Elements, HEq (first.val point) (second.val point)) :
    HEq first second := by
  cases same
  apply heq_of_eq
  apply (Functor.sections_ext_iff).2
  intro point
  exact eq_of_heq (values point)

private theorem sectionValue_heq_of_heq
    {P : Face.{u, u, u} C} {A B : DisplayedFamily.{u, u, u, u} P}
    (same : A = B) {first : A.sections} {second : B.sections}
    (terms : HEq first second) (point : P.Elements) :
    HEq (first.val point) (second.val point) := by
  cases same
  cases terms
  rfl

private theorem naturalEvaluation_heq
    {P : Face.{u, u, u} C} {A B : DisplayedFamily.{u, u, u, u} P}
    (map : A ⟶ B) {first second : P.Elements} (points : first = second)
    {left : A.obj first} {right : A.obj second} (values : HEq left right) :
    HEq (map.app first left) (map.app second right) := by
  cases points
  cases values
  rfl

private theorem sectionPoint_heq
    {P : Face.{u, u, u} C} {A : DisplayedFamily.{u, u, u, u} P}
    (body : A.sections) {first second : P.Elements} (points : first = second) :
    HEq (body.val first) (body.val second) := by
  cases points
  rfl

theorem substituteTerm_value (A : NativeType X) (body : A.decoded.sections)
    (s : Y ⟶ X) (point : Y.Elements) :
    HEq ((substituteTerm (type := A) body s).val point)
      (body.val (s.mapElements.obj point)) :=
  sectionTypeCast_value_heq (A.decoded_reindex s).symm
    (reindexDisplayedSection s A.decoded body) point

noncomputable def functionEquiv (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) :
    B.decoded.sections ≃ (pi A B).decoded.sections :=
  (Equiv.cast (congrArg (fun family : DisplayedFamily.{u, u, u, u}
    (totalSpace A.decoded) => (family.sections : Type u))
      (parameterBody_decode A B).symm)).trans
    ((piSectionEquiv A.decoded
      (reindexDisplayed (totalReindexMap (formerName A B) (parameterDomain A B))
        (parameterBody A B))).trans
      (((Functor.sectionsFunctor X.Elements).mapIso
        (piSubstitutionIso (formerName A B) (parameterDomain A B)
          (parameterBody A B))).toEquiv))

set_option backward.isDefEq.respectTransparency false in
/-- The complete evaluation body uses the original parameter-space
counit. Only the earned codomain equality transports its evidence. -/
theorem functionEquiv_inverse_value (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (function : (pi A B).decoded.sections) (point : (totalSpace A.decoded).Elements) :
    HEq (((functionEquiv A B).symm function).val point)
      (((DisplayedPresheafSlicePi.displayedProductAdjunction (parameterDomain A B)).counit.app
        (parameterBody A B)).app
        ((totalReindexMap (formerName A B) (parameterDomain A B)).mapElements.obj point)
        (function.val ((totalProjection A.decoded).mapElements.obj point))) := by
  let codomain := reindexDisplayed
    (totalReindexMap (formerName A B) (parameterDomain A B)) (parameterBody A B)
  let comparison := piSubstitutionIso (formerName A B) (parameterDomain A B) (parameterBody A B)
  let nativeFunction : (piDisplayed A.decoded codomain).sections :=
    (Functor.sectionsFunctor X.Elements).map comparison.inv function
  let body := (piSectionEquiv A.decoded codomain).symm nativeFunction
  have transported := sectionTypeCast_value_heq (parameterBody_decode A B) body point
  have evaluated := piSectionEquiv_inverse_value A.decoded codomain nativeFunction point
  have changed := evaluation_baseChange (formerName A B) (parameterDomain A B)
    (parameterBody A B) point
    (nativeFunction.val ((totalProjection A.decoded).mapElements.obj point))
  have cancelled := ConcreteCategory.congr_hom
    (comparison.inv_hom_id_app ((totalProjection A.decoded).mapElements.obj point))
    (function.val ((totalProjection A.decoded).mapElements.obj point))
  simp only [types_comp_apply, types_id_apply] at cancelled
  change HEq ((cast (congrArg
      (fun family : DisplayedFamily.{u, u, u, u} (totalSpace A.decoded) =>
        (family.sections : Type u)) (parameterBody_decode A B)) body).val point) _
  exact transported.trans ((heq_of_eq evaluated).trans ((heq_of_eq changed.symm).trans
    (heq_of_eq (congrArg
      (((DisplayedPresheafSlicePi.displayedProductAdjunction (parameterDomain A B)).counit.app
        (parameterBody A B)).app
        ((totalReindexMap (formerName A B) (parameterDomain A B)).mapElements.obj point))
      cancelled))))

noncomputable def lam {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (body : B.decoded.sections) : (pi A B).decoded.sections := functionEquiv A B body

noncomputable def app {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (function : (pi A B).decoded.sections) (argument : A.decoded.sections) :
    (reindexDisplayed (sectionLift A.decoded argument) B.decoded).sections :=
  reindexDisplayedSection (sectionLift A.decoded argument) B.decoded
    ((functionEquiv A B).symm function)

theorem beta {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (body : B.decoded.sections) (argument : A.decoded.sections) :
    app (lam body) argument =
      reindexDisplayedSection (sectionLift A.decoded argument) B.decoded body := by
  unfold app lam
  rw [Equiv.symm_apply_apply]

theorem eta {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (function : (pi A B).decoded.sections) :
    lam ((functionEquiv A B).symm function) = function :=
  (functionEquiv A B).apply_symm_apply function

theorem local_selfExtend (A : NativeType X) (argument : A.decoded.sections) :
    selfExtend (localModel C) (type := A) argument = sectionLift A.decoded argument := by
  rfl

theorem local_extensionSubstitution (s : Y ⟶ X) (A : NativeType X) :
    TypeOver.extensionSubstitution (C := localModel C) s A =
      totalReindexMap s A.decoded := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem functionEquiv_inverse_substitution (s : Y ⟶ X) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded))
    (function : (pi A B).decoded.sections)
    (reindexedFunction : (pi (A.reindex s)
      (B.reindex (totalReindexMap s A.decoded))).decoded.sections)
    (related : HEq (substituteTerm (type := pi A B) function s) reindexedFunction) :
    HEq ((functionEquiv (A.reindex s)
      (B.reindex (totalReindexMap s A.decoded))).symm reindexedFunction)
      (substituteTerm (type := B) ((functionEquiv A B).symm function)
        (totalReindexMap s A.decoded)) := by
  let A' := A.reindex s
  let B' := B.reindex (totalReindexMap s A.decoded)
  let lifted := totalReindexMap s A.decoded
  have typeEquality := (B.decoded_reindex lifted).symm
  apply sections_heq_of_pointwise typeEquality
  intro point
  have leftValue := functionEquiv_inverse_value A' B' reindexedFunction point
  have rightValue := functionEquiv_inverse_value A B function (lifted.mapElements.obj point)
  have originalValue := substituteTerm_value B ((functionEquiv A B).symm function) lifted point
  have functionValues := sectionValue_heq_of_heq
    (congrArg (fun type : NativeType Y => type.decoded) (pi_reindex s A B)) related
    ((totalProjection A'.decoded).mapElements.obj point)
  have substitutionValue := substituteTerm_value (pi A B) function s
    ((totalProjection A'.decoded).mapElements.obj point)
  have sameName : formerName A' B' = s ≫ formerName A B :=
    NativeLocalFunctionParameters.name_substitution s A.name A.family B.parameters B.name
  have arguments :
      (totalReindexMap (formerName A' B') (parameterDomain A B)).mapElements.obj point =
        (totalReindexMap (formerName A B) (parameterDomain A B)).mapElements.obj
          (lifted.mapElements.obj point) := by
    rcases point with ⟨world, base, argument⟩
    apply congrArg (fun receipt : (totalSpace (parameterDomain A B)).obj world =>
      (⟨world, receipt⟩ : (totalSpace (parameterDomain A B)).Elements))
    apply Sigma.ext
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app sameName world) base
    · rfl
  have values : HEq
      (reindexedFunction.val ((totalProjection A'.decoded).mapElements.obj point))
      (function.val ((totalProjection A.decoded).mapElements.obj
        (lifted.mapElements.obj point))) :=
    functionValues.symm.trans substitutionValue
  have evaluations : HEq
      (((DisplayedPresheafSlicePi.displayedProductAdjunction (parameterDomain A B)).counit.app
        (parameterBody A B)).app
        ((totalReindexMap (formerName A' B') (parameterDomain A B)).mapElements.obj point)
        (reindexedFunction.val ((totalProjection A'.decoded).mapElements.obj point)))
      (((DisplayedPresheafSlicePi.displayedProductAdjunction (parameterDomain A B)).counit.app
        (parameterBody A B)).app
        ((totalReindexMap (formerName A B) (parameterDomain A B)).mapElements.obj
          (lifted.mapElements.obj point))
        (function.val ((totalProjection A.decoded).mapElements.obj
          (lifted.mapElements.obj point)))) :=
    naturalEvaluation_heq
      ((DisplayedPresheafSlicePi.displayedProductAdjunction (parameterDomain A B)).counit.app
        (parameterBody A B)) arguments values
  exact leftValue.trans (evaluations.trans (rightValue.symm.trans originalValue.symm))

noncomputable def products (C : Type u) [Category.{u} C] : PiOperations (localModel C) where
  pi := NativeLocalTypeFormers.pi
  lam := lam
  app := app

theorem products_beta (C : Type u) [Category.{u} C] : PiBeta (products C) := by
  intro X A B body argument
  exact beta body argument

theorem products_formation_substitution (C : Type u) [Category.{u} C] :
    StrictPiFormationSubstitution (products C) := by
  intro X Y s A B
  exact pi_reindex s A B

set_option backward.isDefEq.respectTransparency false in
theorem lam_reindex (s : Y ⟶ X) {A : NativeType X}
    {B : NativeType (totalSpace A.decoded)} (body : B.decoded.sections) :
    HEq (substituteTerm (type := pi A B) (lam (A := A) (B := B) body) s)
      (lam (A := A.reindex s) (B := B.reindex (totalReindexMap s A.decoded))
        (substituteTerm (type := B) body (totalReindexMap s A.decoded))) := by
  let function := reindexFunction (products C) (products_formation_substitution C)
    s (lam (A := A) (B := B) body)
  have related : HEq (substituteTerm (type := pi A B) (lam (A := A) (B := B) body) s) function :=
    (reindexFunction_heq (products C) (products_formation_substitution C)
      s (lam (A := A) (B := B) body)).symm
  have bodyEquality := functionEquiv_inverse_substitution s A B
    (lam (A := A) (B := B) body) function related
  simp only [lam, Equiv.symm_apply_apply] at bodyEquality
  have recovered := congrArg (functionEquiv (A.reindex s)
    (B.reindex (totalReindexMap s A.decoded))) (eq_of_heq bodyEquality)
  simp only [Equiv.apply_symm_apply] at recovered
  exact related.trans (heq_of_eq recovered)

set_option backward.isDefEq.respectTransparency false in
theorem app_reindex (s : Y ⟶ X) {A : NativeType X}
    {B : NativeType (totalSpace A.decoded)}
    (function : (pi A B).decoded.sections) (argument : A.decoded.sections)
    (reindexedFunction : (pi (A.reindex s)
      (B.reindex (totalReindexMap s A.decoded))).decoded.sections)
    (related : HEq (substituteTerm (type := pi A B) function s) reindexedFunction) :
    HEq (substituteTerm (type := B.reindex (sectionLift A.decoded argument))
      (app function argument) s)
      (app reindexedFunction (substituteTerm (type := A) argument s)) := by
  let lifted := totalReindexMap s A.decoded
  let argument' := substituteTerm (type := A) argument s
  have square : sectionLift (A.reindex s).decoded argument' ≫ lifted =
      s ≫ sectionLift A.decoded argument :=
    selfExtend_substitution (C := localModel C) s argument
  have typeEquality :
      ((B.reindex (sectionLift A.decoded argument)).reindex s).decoded =
        ((B.reindex lifted).reindex
          (sectionLift (A.reindex s).decoded argument')).decoded := by
    exact congrArg (fun type : NativeType Y => type.decoded)
      (congrArg (fun arrow => B.reindex arrow) square.symm)
  apply sections_heq_of_pointwise typeEquality
  intro point
  have leftValue := substituteTerm_value
    (B.reindex (sectionLift A.decoded argument)) (app function argument) s point
  have bodies := functionEquiv_inverse_substitution s A B function reindexedFunction related
  have bodyValues := sectionValue_heq_of_heq
    (B.decoded_reindex lifted).symm bodies
    ((sectionLift (A.reindex s).decoded argument').mapElements.obj point)
  have rightValue := substituteTerm_value B ((functionEquiv A B).symm function) lifted
    ((sectionLift (A.reindex s).decoded argument').mapElements.obj point)
  have samePoints :
      lifted.mapElements.obj ((sectionLift (A.reindex s).decoded argument').mapElements.obj point) =
        (sectionLift A.decoded argument).mapElements.obj (s.mapElements.obj point) :=
    congrArg (fun map => map.mapElements.obj point) square
  have sameValues := sectionPoint_heq ((functionEquiv A B).symm function) samePoints
  exact leftValue.trans (sameValues.symm.trans
    (rightValue.symm.trans bodyValues.symm))

theorem products_substitution (C : Type u) [Category.{u} C] :
    StrictPiSubstitution (products C) := by
  refine ⟨products_formation_substitution C, ?_, ?_⟩
  · intro X Y s A B body
    exact lam_reindex (A := A) (B := B) s body
  · intro X Y s A B function argument reindexedFunction related
    exact app_reindex (A := A) (B := B) s function argument reindexedFunction related

def sumTermEquiv (A : NativeType X) (B : NativeType (totalSpace A.decoded)) :
    (sigma A B).decoded.sections ≃ (sigmaDisplayed A.decoded B.decoded).sections :=
  Equiv.cast (congrArg (fun family : DisplayedFamily.{u, u, u, u} X =>
    (family.sections : Type u))
    (sigmaDecode A B))

theorem sumTermEquiv_heq (A : NativeType X) (B : NativeType (totalSpace A.decoded))
    (value : (sigma A B).decoded.sections) : HEq (sumTermEquiv A B value) value :=
  cast_heq _ _

def pair {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (first : A.decoded.sections)
    (second : (reindexDisplayed (sectionLift A.decoded first) B.decoded).sections) :
    (sigma A B).decoded.sections :=
  (sumTermEquiv A B).symm (sigmaDisplayedPair A.decoded B.decoded first second)

theorem pair_heq {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (first : A.decoded.sections)
    (second : (reindexDisplayed (sectionLift A.decoded first) B.decoded).sections) :
    HEq (pair (A := A) (B := B) first second)
      (sigmaDisplayedPair A.decoded B.decoded first second) := cast_heq _ _

def fst {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (value : (sigma A B).decoded.sections) : A.decoded.sections :=
  sigmaDisplayedFst (sumTermEquiv A B value)

def snd {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (value : (sigma A B).decoded.sections) :
    (reindexDisplayed (sectionLift A.decoded (fst value)) B.decoded).sections :=
  sigmaDisplayedSnd (sumTermEquiv A B value)

theorem fst_pair {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (first : A.decoded.sections)
    (second : (reindexDisplayed (sectionLift A.decoded first) B.decoded).sections) :
    fst (pair first second) = first := by
  unfold fst pair
  rw [Equiv.apply_symm_apply]
  exact sigmaDisplayedFst_pair _ _ _ _

theorem snd_pair {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (first : A.decoded.sections)
    (second : (reindexDisplayed (sectionLift A.decoded first) B.decoded).sections) :
    HEq (snd (pair first second)) second := by
  unfold snd pair fst
  rw [Equiv.apply_symm_apply]
  exact sigmaDisplayedSnd_pair_heq _ _ _ _

theorem sum_eta {A : NativeType X} {B : NativeType (totalSpace A.decoded)}
    (value : (sigma A B).decoded.sections) : pair (fst value) (snd value) = value := by
  apply (sumTermEquiv A B).injective
  unfold pair fst snd
  rw [Equiv.apply_symm_apply]
  exact sigmaDisplayed_eta _ _ _

noncomputable def sums (C : Type u) [Category.{u} C] : SigmaOperations (localModel C) where
  sigma := NativeLocalTypeFormers.sigma
  pair := pair
  fst := fst
  snd := snd

theorem sums_beta (C : Type u) [Category.{u} C] : SigmaBeta (sums C) :=
  ⟨fst_pair, snd_pair⟩

theorem sums_formation_substitution (C : Type u) [Category.{u} C] :
    StrictSigmaFormationSubstitution (sums C) := by
  intro X Y s A B
  exact sigma_reindex s A B

private theorem nativePair_term_heq
    {P : Face.{u, u, u} C} {A : DisplayedFamily.{u, u, u, u} P}
    {B : DisplayedFamily.{u, u, u, u} (totalSpace A)}
    {first otherFirst : A.sections} (firsts : first = otherFirst)
    {second : (reindexDisplayed (sectionLift A first) B).sections}
    {otherSecond : (reindexDisplayed (sectionLift A otherFirst) B).sections}
    (seconds : HEq second otherSecond) :
    HEq (sigmaDisplayedPair A B first second)
      (sigmaDisplayedPair A B otherFirst otherSecond) := by
  cases firsts
  cases seconds
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pair_reindex (s : Y ⟶ X) {A : NativeType X}
    {B : NativeType (totalSpace A.decoded)} (first : A.decoded.sections)
    (second : (reindexDisplayed (sectionLift A.decoded first) B.decoded).sections)
    (reindexedSecond : (reindexDisplayed
      (sectionLift (A.reindex s).decoded (substituteTerm (type := A) first s))
      (B.reindex (totalReindexMap s A.decoded)).decoded).sections)
    (related : HEq (substituteTerm
      (type := B.reindex (sectionLift A.decoded first)) second s) reindexedSecond) :
    HEq (substituteTerm (type := sigma A B) (pair (A := A) (B := B) first second) s)
      (pair (A := A.reindex s) (B := B.reindex (totalReindexMap s A.decoded))
        (substituteTerm (type := A) first s) reindexedSecond) := by
  have substituted := substituteTerm_heq (C := presheafCwf C) (type := sigma A B)
    (pair (A := A) (B := B) first second) s
  have decoded := TypeOver.tmSub_heq (C := presheafCwf C) (sigmaDecode A B)
    (pair_heq (A := A) (B := B) first second) s
  have native := sigmaDisplayedPair_reindex_heq s A.decoded B.decoded first second
  have firsts : reindexDisplayedSection s A.decoded first = substituteTerm (type := A) first s :=
    eq_of_heq (substituteTerm_heq (C := presheafCwf C) (type := A) first s).symm
  have seconds : HEq (reindexDependentSection s A.decoded B.decoded first second) reindexedSecond :=
    (reindexDependentSection_heq s A.decoded B.decoded first second).symm.trans
      ((substituteTerm_heq (C := presheafCwf C)
        (type := B.reindex (sectionLift A.decoded first)) second s).symm.trans related)
  have pairs := nativePair_term_heq firsts seconds
  have target := pair_heq (A := A.reindex s) (B := B.reindex (totalReindexMap s A.decoded))
    (substituteTerm (type := A) first s) reindexedSecond
  exact substituted.trans (decoded.trans (native.trans (pairs.trans target.symm)))

set_option backward.isDefEq.respectTransparency false in
theorem sumTermEquiv_reindex (s : Y ⟶ X) (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) (value : (sigma A B).decoded.sections)
    (reindexedValue : (sigma (A.reindex s)
      (B.reindex (totalReindexMap s A.decoded))).decoded.sections)
    (related : HEq (substituteTerm (type := sigma A B) value s) reindexedValue) :
    HEq (sumTermEquiv (A.reindex s) (B.reindex (totalReindexMap s A.decoded)) reindexedValue)
      (reindexDisplayedSection s (sigmaDisplayed A.decoded B.decoded)
        (sumTermEquiv A B value)) := by
  have normalized := sumTermEquiv_heq (A.reindex s)
    (B.reindex (totalReindexMap s A.decoded)) reindexedValue
  have substituted := substituteTerm_heq (C := presheafCwf C)
    (type := sigma A B) value s
  have decoded := TypeOver.tmSub_heq (C := presheafCwf C) (sigmaDecode A B)
    (sumTermEquiv_heq A B value).symm s
  exact normalized.trans (related.symm.trans (substituted.trans decoded))

set_option backward.isDefEq.respectTransparency false in
theorem projections_reindex (s : Y ⟶ X) {A : NativeType X}
    {B : NativeType (totalSpace A.decoded)} (value : (sigma A B).decoded.sections)
    (reindexedValue : (sigma (A.reindex s)
      (B.reindex (totalReindexMap s A.decoded))).decoded.sections)
    (related : HEq (substituteTerm (type := sigma A B) value s) reindexedValue) :
    HEq (substituteTerm (type := A) (fst (A := A) (B := B) value) s)
      (fst (A := A.reindex s) (B := B.reindex (totalReindexMap s A.decoded)) reindexedValue) ∧
    HEq (substituteTerm (type := B.reindex (sectionLift A.decoded (fst (A := A) (B := B) value)))
        (snd (A := A) (B := B) value) s)
      (snd (A := A.reindex s) (B := B.reindex (totalReindexMap s A.decoded)) reindexedValue) := by
  have normalized := sumTermEquiv_reindex s A B value reindexedValue related
  have comparisons := (presheafDependentSums_strictSubstitution C).2.2 s
    (sumTermEquiv A B value)
    (sumTermEquiv (A.reindex s) (B.reindex (totalReindexMap s A.decoded)) reindexedValue)
    normalized.symm
  exact ⟨(substituteTerm_heq (C := presheafCwf C) (type := A)
      (fst (A := A) (B := B) value) s).trans comparisons.1,
    (substituteTerm_heq (C := presheafCwf C)
      (type := B.reindex (sectionLift A.decoded (fst (A := A) (B := B) value)))
      (snd (A := A) (B := B) value) s).trans comparisons.2⟩

private theorem projections_codomain_heq {A : NativeType X}
    {B otherB : NativeType (totalSpace A.decoded)} (codomains : B = otherB)
    {value : (sigma A B).decoded.sections} {otherValue : (sigma A otherB).decoded.sections}
    (values : HEq value otherValue) :
    HEq (fst (A := A) (B := B) value) (fst (A := A) (B := otherB) otherValue) ∧
      HEq (snd (A := A) (B := B) value) (snd (A := A) (B := otherB) otherValue) := by
  cases codomains
  cases values
  exact ⟨HEq.rfl, HEq.rfl⟩

attribute [local irreducible] NativeLocalFunctionParameters.name fst snd sumTermEquiv

set_option backward.isDefEq.respectTransparency true in
private theorem sums_first_substitution (C : Type u) [Category.{u} C]
    {X Y : (localModel C).Ctx} (s : (localModel C).Sub Y X)
    {A : (localModel C).Ty X} {B : (localModel C).Ty ((localModel C).ext X A)}
    (value : (localModel C).Tm X ((sums C).sigma A B))
    (reindexedValue : (localModel C).Tm Y ((sums C).sigma ((localModel C).tySub A s)
      ((localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A))))
    (related : HEq ((localModel C).tmSub value s) reindexedValue) :
    HEq ((localModel C).tmSub ((sums C).fst (domain := A) (codomain := B) value) s)
      ((sums C).fst (domain := (localModel C).tySub A s)
        (codomain := (localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A)) reindexedValue) := by
  change Face.{u, u, u} C at X
  change Face.{u, u, u} C at Y
  change NativeType X at A
  change NativeType (totalSpace A.decoded) at B
  let originalCodomain := (localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A)
  let nativeCodomain := B.reindex (totalReindexMap s A.decoded)
  have codomains : originalCodomain = nativeCodomain :=
    congrArg (fun arrow => B.reindex arrow) (local_extensionSubstitution s A)
  let nativeValue : (sigma (A.reindex s) nativeCodomain).decoded.sections :=
    cast (congrArg (fun body : NativeType (totalSpace (A.reindex s).decoded) =>
      ((sigma (A.reindex s) body).decoded.sections : Type u)) codomains) reindexedValue
  have values : HEq reindexedValue nativeValue := (cast_heq _ reindexedValue).symm
  have projections := projections_reindex (C := C) (A := A) (B := B)
    s value nativeValue (related.trans values)
  have converted := projections_codomain_heq (A := A.reindex s)
    (B := originalCodomain) (otherB := nativeCodomain) codomains values
  exact projections.1.trans converted.1.symm

set_option backward.isDefEq.respectTransparency true in
private theorem sums_second_substitution (C : Type u) [Category.{u} C]
    {X Y : (localModel C).Ctx} (s : (localModel C).Sub Y X)
    {A : (localModel C).Ty X} {B : (localModel C).Ty ((localModel C).ext X A)}
    (value : (localModel C).Tm X ((sums C).sigma A B))
    (reindexedValue : (localModel C).Tm Y ((sums C).sigma ((localModel C).tySub A s)
      ((localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A))))
    (related : HEq ((localModel C).tmSub value s) reindexedValue) :
    HEq ((localModel C).tmSub ((sums C).snd (domain := A) (codomain := B) value) s)
        ((sums C).snd (domain := (localModel C).tySub A s)
          (codomain := (localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A)) reindexedValue) := by
  change Face.{u, u, u} C at X
  change Face.{u, u, u} C at Y
  change NativeType X at A
  change NativeType (totalSpace A.decoded) at B
  let originalCodomain := (localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A)
  let nativeCodomain := B.reindex (totalReindexMap s A.decoded)
  have codomains : originalCodomain = nativeCodomain :=
    congrArg (fun arrow => B.reindex arrow) (local_extensionSubstitution s A)
  let nativeValue : (sigma (A.reindex s) nativeCodomain).decoded.sections :=
    cast (congrArg (fun body : NativeType (totalSpace (A.reindex s).decoded) =>
      ((sigma (A.reindex s) body).decoded.sections : Type u)) codomains) reindexedValue
  have values : HEq reindexedValue nativeValue := (cast_heq _ reindexedValue).symm
  have projections := projections_reindex (C := C) (A := A) (B := B)
    s value nativeValue (related.trans values)
  have converted := projections_codomain_heq (A := A.reindex s)
    (B := originalCodomain) (otherB := nativeCodomain) codomains values
  let sourceType : (localModel C).Ty X := (localModel C).tySub B
    (selfExtend (localModel C) ((sums C).fst (domain := A) (codomain := B) value))
  let nativeSourceType : NativeType X := B.reindex
    (sectionLift A.decoded (fst (A := A) (B := B) value))
  have sourceTypes : sourceType = nativeSourceType :=
    congrArg (fun arrow : X ⟶ totalSpace A.decoded => B.reindex arrow)
      (local_selfExtend (C := C) A ((sums C).fst (domain := A) (codomain := B) value))
  have sourceTerms : HEq ((sums C).snd (domain := A) (codomain := B) value)
      (snd (A := A) (B := B) value) := HEq.rfl
  have sourceSubstitution : HEq
      ((localModel C).tmSub ((sums C).snd (domain := A) (codomain := B) value) s)
      (substituteTerm (type := nativeSourceType) (snd (A := A) (B := B) value) s) :=
    TypeOver.tmSub_heq (C := localModel C) (A := sourceType) (B := nativeSourceType)
      sourceTypes sourceTerms s
  exact sourceSubstitution.trans (projections.2.trans converted.2.symm)

theorem sums_projections_substitution (C : Type u) [Category.{u} C]
    {X Y : (localModel C).Ctx} (s : (localModel C).Sub Y X)
    {A : (localModel C).Ty X} {B : (localModel C).Ty ((localModel C).ext X A)}
    (value : (localModel C).Tm X ((sums C).sigma A B))
    (reindexedValue : (localModel C).Tm Y ((sums C).sigma ((localModel C).tySub A s)
      ((localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A))))
    (related : HEq ((localModel C).tmSub value s) reindexedValue) :
    HEq ((localModel C).tmSub ((sums C).fst (domain := A) (codomain := B) value) s)
      ((sums C).fst (domain := (localModel C).tySub A s)
        (codomain := (localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A)) reindexedValue) ∧
      HEq ((localModel C).tmSub ((sums C).snd (domain := A) (codomain := B) value) s)
        ((sums C).snd (domain := (localModel C).tySub A s)
          (codomain := (localModel C).tySub B (TypeOver.extensionSubstitution (C := localModel C) s A)) reindexedValue) := by
  exact ⟨sums_first_substitution C s value reindexedValue related,
    sums_second_substitution C s value reindexedValue related⟩

theorem sums_substitution (C : Type u) [Category.{u} C] :
    StrictSigmaSubstitution (sums C) := by
  refine ⟨sums_formation_substitution C, ?_, ?_⟩
  · intro X Y s A B first second reindexedSecond related
    exact pair_reindex (A := A) (B := B) s first second reindexedSecond related
  · exact sums_projections_substitution C

end Mettapedia.TypeTheory.NativeLocalTypeOperations
