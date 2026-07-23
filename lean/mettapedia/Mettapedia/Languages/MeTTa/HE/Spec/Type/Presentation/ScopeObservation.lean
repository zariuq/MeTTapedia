import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance

/-!
# Scoped observation of finite type presentations

Branch-local type freshening changes private variable spellings.  Exact
runtime simulation must therefore retain the branch-local presentation, while
the static specification presentation is compared with it only on the finite
scope visible to the evaluator.

This boundary does not quotient scan structure: candidate order,
multiplicity, success positions, and diagnostic ledgers remain exact in their
respective relations.  Only valuation observations of the two finite binding
theories are scoped here.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.ApplicationEquivariance
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.PrincipalAlpha
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.ExactNormal
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaTypeConformance
open LeaTTaTypePresentationFoldConformance

/-! ## Structural renaming helpers -/

mutual

/-- Whole-type renaming depends only on the names occurring in the atom. -/
theorem renameTypeVars_congr_on_typeVars
    {left right : String → String} (atom : Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVars atom →
      left name = right name) :
    renameTypeVars left atom = renameTypeVars right atom := by
  cases atom with
  | symbol name => simp [renameTypeVars]
  | var name =>
      simp only [renameTypeVars, Atom.var.injEq]
      exact agrees name (by simp [TypeSubst.typeVars])
  | grounded value => simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, Atom.expression.injEq]
      apply renameTypeVarsList_congr_on_typeVars
      intro name member
      exact agrees name (by simpa [TypeSubst.typeVars] using member)

/-- List companion of `renameTypeVars_congr_on_typeVars`. -/
theorem renameTypeVarsList_congr_on_typeVars
    {left right : String → String} (atoms : List Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVarsList atoms →
      left name = right name) :
    atoms.map (renameTypeVars left) =
      atoms.map (renameTypeVars right) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply renameTypeVars_congr_on_typeVars atom
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply renameTypeVarsList_congr_on_typeVars atoms
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

end

mutual

/-- Successive whole-type renamings compose. -/
theorem renameTypeVars_comp
    (outer inner : String → String) (atom : Atom) :
    renameTypeVars outer (renameTypeVars inner atom) =
      renameTypeVars (outer ∘ inner) atom := by
  cases atom with
  | symbol name => simp [renameTypeVars]
  | var name => simp [renameTypeVars, Function.comp_apply]
  | grounded value => simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, Atom.expression.injEq]
      exact renameTypeVarsList_comp outer inner atoms

/-- List companion of `renameTypeVars_comp`. -/
theorem renameTypeVarsList_comp
    (outer inner : String → String) (atoms : List Atom) :
    (atoms.map (renameTypeVars inner)).map
        (renameTypeVars outer) =
      atoms.map (renameTypeVars (outer ∘ inner)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨renameTypeVars_comp outer inner atom,
        renameTypeVarsList_comp outer inner atoms⟩

end

/-- Renaming every type variable by the identity function is inert. -/
theorem renameTypeVars_id (atom : Atom) :
    renameTypeVars id atom = atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
    atoms.map (renameTypeVars id) = atoms) with
  | symbol name => simp [renameTypeVars]
  | var name => simp [renameTypeVars]
  | grounded value => simp [renameTypeVars]
  | expression atoms ih => simp [renameTypeVars, ih]
  | nil => rfl
  | cons atom atoms ihAtom ihAtoms => simp [ihAtom, ihAtoms]

mutual

/-- If a structural type renaming leaves an atom literally unchanged, it
fixes every variable name occurring in that atom. -/
theorem renameTypeVars_eq_self_fixed_on_typeVars
    (rename : String → String) (atom : Atom)
    (equation : renameTypeVars rename atom = atom) :
    ∀ name, name ∈ TypeSubst.typeVars atom → rename name = name := by
  cases atom with
  | symbol symbol => simp [TypeSubst.typeVars]
  | var variableName =>
      intro name member
      have nameEquation : name = variableName := by
        simpa [TypeSubst.typeVars] using member
      subst name
      simpa [renameTypeVars] using equation
  | grounded value => simp [TypeSubst.typeVars]
  | expression atoms =>
      have listEquation :
          atoms.map (renameTypeVars rename) = atoms := by
        simpa [renameTypeVars] using equation
      exact renameTypeVarsList_eq_self_fixed_on_typeVars
        rename atoms listEquation

/-- List companion of
`renameTypeVars_eq_self_fixed_on_typeVars`. -/
theorem renameTypeVarsList_eq_self_fixed_on_typeVars
    (rename : String → String) (atoms : List Atom)
    (equation : atoms.map (renameTypeVars rename) = atoms) :
    ∀ name,
      name ∈ TypeSubst.typeVarsList atoms → rename name = name := by
  cases atoms with
  | nil => simp [TypeSubst.typeVarsList]
  | cons atom atoms =>
      have parts := List.cons.inj equation
      intro name member
      rw [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact renameTypeVars_eq_self_fixed_on_typeVars
          rename atom parts.1 name headMember
      · exact renameTypeVarsList_eq_self_fixed_on_typeVars
          rename atoms parts.2 name tailMember

end

mutual

/-- Whole-type renaming maps the finite variable support pointwise. -/
theorem typeVars_renameTypeVars
    (rename : String → String) (atom : Atom) :
    TypeSubst.typeVars (renameTypeVars rename atom) =
      (TypeSubst.typeVars atom).map rename := by
  cases atom with
  | symbol name => simp [renameTypeVars, TypeSubst.typeVars]
  | var name => simp [renameTypeVars, TypeSubst.typeVars]
  | grounded value => simp [renameTypeVars, TypeSubst.typeVars]
  | expression atoms =>
      simpa [renameTypeVars, TypeSubst.typeVars] using
        typeVarsList_renameTypeVars rename atoms

/-- List companion of `typeVars_renameTypeVars`. -/
theorem typeVarsList_renameTypeVars
    (rename : String → String) (atoms : List Atom) :
    TypeSubst.typeVarsList
        (atoms.map (renameTypeVars rename)) =
      (TypeSubst.typeVarsList atoms).map rename := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, TypeSubst.typeVarsList,
        List.map_append]
      exact congrArg₂ List.append
        (typeVars_renameTypeVars rename atom)
        (typeVarsList_renameTypeVars rename atoms)

end

/-- Satisfaction of a finite presentation depends only on the names that its
assignment theory mentions. -/
theorem typeSubstSatisfied_congr_of_presentationVars
    {left right : String → Atom} {presentation : TypeSubst}
    (agrees : ValuationsAgreeOn
      (specBindingVars ⟨presentation, []⟩) left right) :
    TypeSubstSatisfied left presentation ↔
      TypeSubstSatisfied right presentation := by
  have bindingEquiv := specTypeBindingSatisfied_congr_of_bindingVars
    (bindings := (⟨presentation, []⟩ : Bindings)) agrees
  simpa [TypeBindingSatisfied, TypeSubstSatisfied] using bindingEquiv

mutual

/-- Recursive reduced-type consistency depends only on the valuation at
variables occurring in its two input atoms. -/
theorem reducedTypeConsistent_congr_of_typeVars
    {leftModel rightModel : String → Atom} (left right : Atom)
    (agrees : ∀ name,
      name ∈ TypeSubst.typeVars left ++ TypeSubst.typeVars right →
        leftModel name = rightModel name) :
    ReducedTypeConsistent leftModel left right ↔
      ReducedTypeConsistent rightModel left right := by
  cases left <;> cases right
  case var.var left right =>
    unfold ReducedTypeConsistent
    rw [agrees left (by simp [TypeSubst.typeVars]),
      agrees right (by simp [TypeSubst.typeVars])]
  case var.expression left right =>
    unfold ReducedTypeConsistent
    have valueAgreement := agrees left (by simp [TypeSubst.typeVars])
    have applicationAgreement :=
      applyTypeValuation_congr_of_typeVars
        (left := leftModel) (right := rightModel)
        (.expression right) (by
          intro name member
          exact agrees name (by
            simp only [TypeSubst.typeVars, List.mem_append]
            exact Or.inr member))
    rw [valueAgreement, applicationAgreement]
  case expression.var left right =>
    unfold ReducedTypeConsistent
    have valueAgreement := agrees right (by simp [TypeSubst.typeVars])
    have applicationAgreement :=
      applyTypeValuation_congr_of_typeVars
        (left := leftModel) (right := rightModel)
        (.expression left) (by
          intro name member
          exact agrees name (by
            simp only [TypeSubst.typeVars, List.mem_append]
            exact Or.inl member))
    rw [valueAgreement, applicationAgreement]
  case expression.expression left right =>
    unfold ReducedTypeConsistent
    apply reducedTypeListConsistent_congr_of_typeVars
    intro name member
    exact agrees name (by
      simpa [TypeSubst.typeVars] using member)
  all_goals
    unfold ReducedTypeConsistent
  all_goals
    (try split) <;>
      simp_all [applyTypeValuation, TypeSubst.typeVars]

/-- List companion of `reducedTypeConsistent_congr_of_typeVars`. -/
theorem reducedTypeListConsistent_congr_of_typeVars
    {leftModel rightModel : String → Atom}
    (left right : List Atom)
    (agrees : ∀ name,
      name ∈ TypeSubst.typeVarsList left ++
          TypeSubst.typeVarsList right →
        leftModel name = rightModel name) :
    ReducedTypeListConsistent leftModel left right ↔
      ReducedTypeListConsistent rightModel left right := by
  cases left with
  | nil => cases right <;> simp [ReducedTypeListConsistent]
  | cons left lefts =>
      cases right with
      | nil => simp [ReducedTypeListConsistent]
      | cons right rights =>
          simp only [ReducedTypeListConsistent]
          apply and_congr
          · apply reducedTypeConsistent_congr_of_typeVars
            intro name member
            apply agrees name
            apply List.mem_append.mpr
            rcases List.mem_append.mp member with member | member
            · left
              simp only [TypeSubst.typeVarsList]
              exact List.mem_append.mpr (Or.inl member)
            · right
              simp only [TypeSubst.typeVarsList]
              exact List.mem_append.mpr (Or.inl member)
          · apply reducedTypeListConsistent_congr_of_typeVars
            intro name member
            apply agrees name
            apply List.mem_append.mpr
            rcases List.mem_append.mp member with member | member
            · left
              simp only [TypeSubst.typeVarsList]
              exact List.mem_append.mpr (Or.inr member)
            · right
              simp only [TypeSubst.typeVarsList]
              exact List.mem_append.mpr (Or.inr member)

end

/-- Published-top plus R2 consistency has the same finite valuation support
as its two input atoms. -/
theorem corePlusR2TypeConsistent_congr_of_typeVars
    {leftModel rightModel : String → Atom} (left right : Atom)
    (agrees : ∀ name,
      name ∈ TypeSubst.typeVars left ++ TypeSubst.typeVars right →
        leftModel name = rightModel name) :
    CorePlusR2TypeConsistent leftModel left right ↔
      CorePlusR2TypeConsistent rightModel left right := by
  simp only [CorePlusR2TypeConsistent]
  rw [reducedTypeConsistent_congr_of_typeVars left right agrees]


/-! ## Public-fixed permutations for one private candidate -/

/-- Two candidate presentations are private alpha siblings relative to the
same finite protected scope. -/
def PrivateCandidateAlphaRel
    (fixedScope : List String) (left right : Atom) : Prop :=
  ∃ source,
    TypeCandidateAlphaVariantRel fixedScope source left ∧
      TypeCandidateAlphaVariantRel fixedScope source right

/-- Two lawful private presentations of one candidate admit a global
permutation that fixes every protected name and maps the left presentation to
the right one. -/
theorem PrivateCandidateAlphaRel.exists_public_fixed_permutation
    {fixedScope : List String} {left right : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope left right) :
    ∃ permutation : Equiv.Perm String,
      (∀ name, name ∈ fixedScope → permutation name = name) ∧
        right = renameTypeVars permutation left := by
  rcases alpha with
    ⟨source,
      ⟨leftRename, leftInjective, leftEquation, leftFresh⟩,
      ⟨rightRename, rightInjective, rightEquation, rightFresh⟩⟩
  let PublicVariable := {name : String // name ∈ fixedScope}
  let PrivateVariable :=
    {name : String // name ∈ TypeSubst.typeVars source}
  let ScopedVariable := Sum PublicVariable PrivateVariable
  let leftImage : ScopedVariable → String
    | .inl name => name.1
    | .inr name => leftRename name.1
  let rightImage : ScopedVariable → String
    | .inl name => name.1
    | .inr name => rightRename name.1
  have leftImageInjective : Function.Injective leftImage := by
    intro first second equal
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            congr 1
            exact Subtype.ext equal
        | inr second =>
            exfalso
            exact leftFresh second.1 second.2 (by
              change first.1 = leftRename second.1 at equal
              rw [← equal]
              exact first.2)
    | inr first =>
        cases second with
        | inl second =>
            exfalso
            exact leftFresh first.1 first.2 (by
              change leftRename first.1 = second.1 at equal
              rw [equal]
              exact second.2)
        | inr second =>
            congr 1
            apply Subtype.ext
            exact leftInjective equal
  have rightImageInjective : Function.Injective rightImage := by
    intro first second equal
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            congr 1
            exact Subtype.ext equal
        | inr second =>
            exfalso
            exact rightFresh second.1 second.2 (by
              change first.1 = rightRename second.1 at equal
              rw [← equal]
              exact first.2)
    | inr first =>
        cases second with
        | inl second =>
            exfalso
            exact rightFresh first.1 first.2 (by
              change rightRename first.1 = second.1 at equal
              rw [equal]
              exact second.2)
        | inr second =>
            congr 1
            apply Subtype.ext
            exact rightInjective equal
  obtain ⟨permutation, extensionLaw⟩ :=
    Equiv.Perm.exists_extending_pair
      leftImage rightImage leftImageInjective rightImageInjective
  refine ⟨permutation, ?_, ?_⟩
  · intro name member
    exact extensionLaw
      (Sum.inl (β := PrivateVariable)
        (⟨name, member⟩ : PublicVariable))
  · rw [leftEquation, rightEquation,
      renameTypeVars_comp]
    apply renameTypeVars_congr_on_typeVars source
    intro name member
    exact (extensionLaw
      (Sum.inr (α := PublicVariable)
        (⟨name, member⟩ : PrivateVariable))).symm

/-- Every variable in either private candidate presentation lies outside the
protected public scope. -/
theorem PrivateCandidateAlphaRel.vars_avoid_fixedScope
    {fixedScope : List String} {left right : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope left right) :
    (∀ name, name ∈ TypeSubst.typeVars left → name ∉ fixedScope) ∧
      ∀ name, name ∈ TypeSubst.typeVars right → name ∉ fixedScope := by
  rcases alpha with
    ⟨source,
      ⟨leftRename, _, leftEquation, leftFresh⟩,
      ⟨rightRename, _, rightEquation, rightFresh⟩⟩
  constructor
  · intro name member scopeMember
    rw [leftEquation, typeVars_renameTypeVars] at member
    obtain ⟨sourceName, sourceMember, nameEquation⟩ :=
      List.mem_map.mp member
    subst name
    exact leftFresh sourceName sourceMember scopeMember
  · intro name member scopeMember
    rw [rightEquation, typeVars_renameTypeVars] at member
    obtain ⟨sourceName, sourceMember, nameEquation⟩ :=
      List.mem_map.mp member
    subst name
    exact rightFresh sourceName sourceMember scopeMember

/-- A model of one private-alpha candidate constraint transports to the
sibling candidate while preserving the complete protected scope. -/
theorem PrivateCandidateAlphaRel.transport_model
    {fixedScope observationScope : List String}
    {incoming : TypeSubst} {expected leftActual rightActual : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (incomingCovered : ∀ name,
      name ∈ specBindingVars ⟨incoming, []⟩ → name ∈ fixedScope)
    (expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ fixedScope)
    (observationCovered : ∀ name,
      name ∈ observationScope → name ∈ fixedScope)
    (leftModel : String → Atom)
    (leftSatisfied : TypeSubstSatisfied leftModel incoming)
    (leftConsistent : CorePlusR2TypeConsistent
      leftModel expected leftActual) :
    ∃ rightModel,
      TypeSubstSatisfied rightModel incoming ∧
        CorePlusR2TypeConsistent rightModel expected rightActual ∧
        ValuationsAgreeOn observationScope leftModel rightModel := by
  obtain ⟨permutation, fixed, candidateEquation⟩ :=
    alpha.exists_public_fixed_permutation
  let rightModel : String → Atom := leftModel ∘ permutation.symm
  have inverseFixed : ∀ name, name ∈ fixedScope →
      permutation.symm name = name := by
    intro name member
    apply permutation.injective
    simp [fixed name member]
  have agreesFixed : ValuationsAgreeOn fixedScope leftModel rightModel := by
    intro name member
    simp [rightModel, Function.comp_apply, inverseFixed name member]
  have rightSatisfied : TypeSubstSatisfied rightModel incoming :=
    (typeSubstSatisfied_congr_of_presentationVars
      (fun name member => agreesFixed name (incomingCovered name member))).mp
        leftSatisfied
  have expectedFixed :
      renameTypeVars permutation expected = expected := by
    calc
      renameTypeVars permutation expected =
          renameTypeVars id expected := by
        apply renameTypeVars_congr_on_typeVars expected
        intro name member
        exact fixed name (expectedCovered name member)
      _ = expected := renameTypeVars_id expected
  have renamedConsistent : CorePlusR2TypeConsistent rightModel
      (renameTypeVars permutation expected)
      (renameTypeVars permutation leftActual) := by
    apply (corePlusR2TypeConsistent_rename_iff
      rightModel permutation expected leftActual).mpr
    simpa [rightModel, Function.comp_def] using leftConsistent
  refine ⟨rightModel, rightSatisfied, ?_, ?_⟩
  · simpa [expectedFixed, candidateEquation] using renamedConsistent
  · intro name member
    exact agreesFixed name (observationCovered name member)

/-- Two finite type presentations have the same model observations on a
finite name scope.  Models may choose different values for private names
outside that scope. -/
structure TypePresentationTheoryEquivAt
    (scope : List String) (left right : TypeSubst) : Prop where
  leftToRight : ∀ leftModel,
    TypeSubstSatisfied leftModel left →
      ∃ rightModel,
        TypeSubstSatisfied rightModel right ∧
          ValuationsAgreeOn scope leftModel rightModel
  rightToLeft : ∀ rightModel,
    TypeSubstSatisfied rightModel right →
      ∃ leftModel,
        TypeSubstSatisfied leftModel left ∧
          ValuationsAgreeOn scope leftModel rightModel

namespace TypePresentationTheoryEquivAt

/-- Scoped presentation observation is reflexive. -/
@[refl] theorem refl (scope : List String) (presentation : TypeSubst) :
    TypePresentationTheoryEquivAt scope presentation presentation := by
  constructor <;> intro model satisfied <;>
    exact ⟨model, satisfied, fun _ _ => rfl⟩

/-- Scoped presentation observation is symmetric. -/
theorem symm {scope : List String} {left right : TypeSubst}
    (equiv : TypePresentationTheoryEquivAt scope left right) :
    TypePresentationTheoryEquivAt scope right left := by
  constructor
  · intro rightModel rightSatisfied
    obtain ⟨leftModel, leftSatisfied, agrees⟩ :=
      equiv.rightToLeft rightModel rightSatisfied
    exact ⟨leftModel, leftSatisfied,
      fun name member => (agrees name member).symm⟩
  · intro leftModel leftSatisfied
    obtain ⟨rightModel, rightSatisfied, agrees⟩ :=
      equiv.leftToRight leftModel leftSatisfied
    exact ⟨rightModel, rightSatisfied,
      fun name member => (agrees name member).symm⟩

/-- Scoped presentation observation composes. -/
theorem trans {scope : List String} {left middle right : TypeSubst}
    (leftMiddle : TypePresentationTheoryEquivAt scope left middle)
    (middleRight : TypePresentationTheoryEquivAt scope middle right) :
    TypePresentationTheoryEquivAt scope left right := by
  constructor
  · intro leftModel leftSatisfied
    obtain ⟨middleModel, middleSatisfied, leftAgrees⟩ :=
      leftMiddle.leftToRight leftModel leftSatisfied
    obtain ⟨rightModel, rightSatisfied, rightAgrees⟩ :=
      middleRight.leftToRight middleModel middleSatisfied
    exact ⟨rightModel, rightSatisfied, fun name member =>
      (leftAgrees name member).trans (rightAgrees name member)⟩
  · intro rightModel rightSatisfied
    obtain ⟨middleModel, middleSatisfied, rightAgrees⟩ :=
      middleRight.rightToLeft rightModel rightSatisfied
    obtain ⟨leftModel, leftSatisfied, leftAgrees⟩ :=
      leftMiddle.rightToLeft middleModel middleSatisfied
    exact ⟨leftModel, leftSatisfied, fun name member =>
      (leftAgrees name member).trans (rightAgrees name member)⟩

/-- Agreement on a larger finite scope entails agreement on any smaller
scope. -/
theorem mono {large small : List String} {left right : TypeSubst}
    (equiv : TypePresentationTheoryEquivAt large left right)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    TypePresentationTheoryEquivAt small left right := by
  constructor
  · intro leftModel leftSatisfied
    obtain ⟨rightModel, rightSatisfied, agrees⟩ :=
      equiv.leftToRight leftModel leftSatisfied
    exact ⟨rightModel, rightSatisfied,
      fun name member => agrees name (subset name member)⟩
  · intro rightModel rightSatisfied
    obtain ⟨leftModel, leftSatisfied, agrees⟩ :=
      equiv.rightToLeft rightModel rightSatisfied
    exact ⟨leftModel, leftSatisfied,
      fun name member => agrees name (subset name member)⟩

/-- Normal scoped-equivalent presentations observe any atom whose variables
are wholly inside the scope up to private alpha-renaming. -/
theorem observedTypeAlpha
    {scope : List String} {left right : TypeSubst}
    (equiv : TypePresentationTheoryEquivAt scope left right)
    (leftNormal : left.Normal) (rightNormal : right.Normal)
    (atom : Atom)
    (atomCovered : ∀ name,
      name ∈ TypeSubst.typeVars atom → name ∈ scope) :
    ObservedTypeAlphaRel (left.apply atom) (right.apply atom) := by
  let rightCanonical := presentedValuation right
  have rightSatisfied : TypeSubstSatisfied rightCanonical right :=
    normal_presentedValuation_satisfied rightNormal
  obtain ⟨leftModel, leftSatisfied, agrees⟩ :=
    equiv.rightToLeft rightCanonical rightSatisfied
  have rightInstance : ∃ forward : String → Atom,
      applyTypeValuation forward (left.apply atom) = right.apply atom := by
    refine ⟨leftModel, ?_⟩
    calc
      applyTypeValuation leftModel (left.apply atom) =
          applyTypeValuation leftModel atom :=
        by simpa [applyTypeValuation_presented_eq_apply] using
          typeSubst_factorization leftSatisfied atom
      _ = applyTypeValuation rightCanonical atom :=
        applyTypeValuation_congr_of_typeVars atom
          (fun name member => agrees name (atomCovered name member))
      _ = right.apply atom := by
        simp [rightCanonical, applyTypeValuation_presented_eq_apply]
  let leftCanonical := presentedValuation left
  have leftSatisfiedCanonical : TypeSubstSatisfied leftCanonical left :=
    normal_presentedValuation_satisfied leftNormal
  obtain ⟨rightModel, rightModelSatisfied, reverseAgrees⟩ :=
    equiv.leftToRight leftCanonical leftSatisfiedCanonical
  have leftInstance : ∃ backward : String → Atom,
      applyTypeValuation backward (right.apply atom) = left.apply atom := by
    refine ⟨rightModel, ?_⟩
    calc
      applyTypeValuation rightModel (right.apply atom) =
          applyTypeValuation rightModel atom :=
        by simpa [applyTypeValuation_presented_eq_apply] using
          typeSubst_factorization rightModelSatisfied atom
      _ = applyTypeValuation leftCanonical atom := by
        symm
        exact applyTypeValuation_congr_of_typeVars atom
          (fun name member => reverseAgrees name (atomCovered name member))
      _ = left.apply atom := by
        simp [leftCanonical, applyTypeValuation_presented_eq_apply]
  exact observedTypeAlpha_of_mutual_instances rightInstance leftInstance

end TypePresentationTheoryEquivAt

/-- One alpha observation is represented by a single global permutation on
the finite variables of the observed atom. -/
theorem ObservedTypeAlphaRel.exists_permutation
    {left right : Atom} (alpha : ObservedTypeAlphaRel left right) :
    ∃ permutation : Equiv.Perm String,
      right = renameTypeVars permutation left := by
  have singletonAlpha : ScopedObservedTypeListAlphaRel [left] [right] :=
    .cons alpha (by simp [AtomVarsFreshFromAtoms, TypeSubst.typeVarsList])
      (by simp [AtomVarsFreshFromAtoms, TypeSubst.typeVarsList]) .nil
  obtain ⟨permutation, equation⟩ :=
    singletonAlpha.exists_permutation
  have headEquation := List.cons.inj equation
  exact ⟨permutation, headEquation.1⟩

/-- Alpha observation composes without choosing a canonical private
spelling. -/
theorem ObservedTypeAlphaRel.trans
    {left middle right : Atom}
    (leftMiddle : ObservedTypeAlphaRel left middle)
    (middleRight : ObservedTypeAlphaRel middle right) :
    ObservedTypeAlphaRel left right := by
  obtain ⟨first, firstEquation⟩ :=
    ObservedTypeAlphaRel.exists_permutation leftMiddle
  obtain ⟨second, secondEquation⟩ :=
    ObservedTypeAlphaRel.exists_permutation middleRight
  refine ⟨left, TypeVariableRenamingOf.refl left,
    ⟨second ∘ first,
      Function.Injective.comp second.injective first.injective, ?_⟩⟩
  rw [secondEquation, firstEquation, renameTypeVars_comp]

/-- Transport one private-alpha consistency constraint across two incoming
presentations that already agree on the protected public scope.  The target
model is patched only on the fresh candidate family; incoming satisfaction
and all public observations therefore remain those of the model supplied by
the incoming-theory correspondence. -/
theorem PrivateCandidateAlphaRel.transport_model_across_presentations
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {expected leftActual rightActual : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (rightIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨rightIncoming, []⟩ → name ∈ fixedScope)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope)
    (leftModel : String → Atom)
    (leftSatisfied : TypeSubstSatisfied leftModel leftIncoming)
    (leftConsistent : CorePlusR2TypeConsistent
      leftModel expected leftActual) :
    ∃ rightModel,
      TypeSubstSatisfied rightModel rightIncoming ∧
        CorePlusR2TypeConsistent rightModel expected rightActual ∧
        ValuationsAgreeOn observationScope leftModel rightModel := by
  obtain ⟨permutation, fixed, candidateEquation⟩ :=
    alpha.exists_public_fixed_permutation
  obtain ⟨rightBase, rightBaseSatisfied, baseAgrees⟩ :=
    incomingEquiv.leftToRight leftModel leftSatisfied
  let transported : String → Atom := leftModel ∘ permutation.symm
  let rightModel : String → Atom := fun name =>
    if name ∈ TypeSubst.typeVars rightActual then
      transported name
    else
      rightBase name
  have inverseFixed : ∀ name, name ∈ fixedScope →
      permutation.symm name = name := by
    intro name member
    apply permutation.injective
    simp [fixed name member]
  have rightActualAvoids : ∀ name,
      name ∈ TypeSubst.typeVars rightActual → name ∉ fixedScope :=
    alpha.vars_avoid_fixedScope.2
  have rightModelAgreesBaseOnFixed :
      ValuationsAgreeOn fixedScope rightBase rightModel := by
    intro name member
    have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
      intro candidateMember
      exact rightActualAvoids name candidateMember member
    simp [rightModel, notCandidate]
  have rightSatisfied : TypeSubstSatisfied rightModel rightIncoming :=
    (typeSubstSatisfied_congr_of_presentationVars
      (left := rightBase) (right := rightModel)
      (fun name member => rightModelAgreesBaseOnFixed name
        (rightIncomingCovered name member))).mp rightBaseSatisfied
  have expectedFixed :
      renameTypeVars permutation expected = expected := by
    calc
      renameTypeVars permutation expected =
          renameTypeVars id expected := by
        apply renameTypeVars_congr_on_typeVars expected
        intro name member
        exact fixed name (theoryCovered name (expectedObserved name member))
      _ = expected := renameTypeVars_id expected
  have transportedConsistent : CorePlusR2TypeConsistent transported
      expected rightActual := by
    have renamedConsistent : CorePlusR2TypeConsistent transported
        (renameTypeVars permutation expected)
        (renameTypeVars permutation leftActual) := by
      apply (corePlusR2TypeConsistent_rename_iff
        transported permutation expected leftActual).mpr
      simpa [transported, Function.comp_def] using leftConsistent
    simpa [expectedFixed, candidateEquation] using renamedConsistent
  have constraintAgreement : ∀ name,
      name ∈ TypeSubst.typeVars expected ++
          TypeSubst.typeVars rightActual →
        transported name = rightModel name := by
    intro name member
    rcases List.mem_append.mp member with expectedMember | actualMember
    · have theoryMember := expectedObserved name expectedMember
      have fixedMember := theoryCovered name theoryMember
      have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
        intro candidateMember
        exact rightActualAvoids name candidateMember fixedMember
      simp [rightModel, notCandidate, transported, Function.comp_apply,
        inverseFixed name fixedMember, baseAgrees name theoryMember]
    · simp [rightModel, actualMember]
  have rightConsistent : CorePlusR2TypeConsistent rightModel
      expected rightActual :=
    (corePlusR2TypeConsistent_congr_of_typeVars
      expected rightActual constraintAgreement).mp transportedConsistent
  refine ⟨rightModel, rightSatisfied, rightConsistent, ?_⟩
  intro name member
  have theoryMember := observationObserved name member
  have fixedMember := theoryCovered name theoryMember
  have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
    intro candidateMember
    exact rightActualAvoids name candidateMember fixedMember
  simpa [rightModel, notCandidate] using baseAgrees name theoryMember

/-- Transport one private-alpha constraint when each target is fresh from
its own incoming presentation.

The common alpha scope protects only the theory that must be observed on
both sides.  It need not contain both presentation supports: the target
model is patched only at the right candidate variables, and the separate
freshness premise is exactly what makes that patch inert for the right
incoming theory.  The symmetric constraint theorem below supplies the
corresponding left-side premise for the reverse direction. -/
theorem PrivateCandidateAlphaRel.transport_model_across_presentations_of_target_fresh
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {expected leftActual rightActual : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (rightTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars rightActual →
        name ∉ specBindingVars ⟨rightIncoming, []⟩)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope)
    (leftModel : String → Atom)
    (leftSatisfied : TypeSubstSatisfied leftModel leftIncoming)
    (leftConsistent : CorePlusR2TypeConsistent
      leftModel expected leftActual) :
    ∃ rightModel,
      TypeSubstSatisfied rightModel rightIncoming ∧
        CorePlusR2TypeConsistent rightModel expected rightActual ∧
        ValuationsAgreeOn observationScope leftModel rightModel := by
  obtain ⟨permutation, fixed, candidateEquation⟩ :=
    alpha.exists_public_fixed_permutation
  obtain ⟨rightBase, rightBaseSatisfied, baseAgrees⟩ :=
    incomingEquiv.leftToRight leftModel leftSatisfied
  let transported : String → Atom := leftModel ∘ permutation.symm
  let rightModel : String → Atom := fun name =>
    if name ∈ TypeSubst.typeVars rightActual then
      transported name
    else
      rightBase name
  have inverseFixed : ∀ name, name ∈ fixedScope →
      permutation.symm name = name := by
    intro name member
    apply permutation.injective
    simp [fixed name member]
  have rightModelAgreesBaseOnIncoming :
      ValuationsAgreeOn
        (specBindingVars ⟨rightIncoming, []⟩) rightBase rightModel := by
    intro name member
    have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
      intro candidateMember
      exact rightTargetFresh name candidateMember member
    simp [rightModel, notCandidate]
  have rightSatisfied : TypeSubstSatisfied rightModel rightIncoming :=
    (typeSubstSatisfied_congr_of_presentationVars
      (left := rightBase) (right := rightModel)
      rightModelAgreesBaseOnIncoming).mp rightBaseSatisfied
  have rightActualAvoids : ∀ name,
      name ∈ TypeSubst.typeVars rightActual → name ∉ fixedScope :=
    alpha.vars_avoid_fixedScope.2
  have expectedFixed :
      renameTypeVars permutation expected = expected := by
    calc
      renameTypeVars permutation expected =
          renameTypeVars id expected := by
        apply renameTypeVars_congr_on_typeVars expected
        intro name member
        exact fixed name (theoryCovered name (expectedObserved name member))
      _ = expected := renameTypeVars_id expected
  have transportedConsistent : CorePlusR2TypeConsistent transported
      expected rightActual := by
    have renamedConsistent : CorePlusR2TypeConsistent transported
        (renameTypeVars permutation expected)
        (renameTypeVars permutation leftActual) := by
      apply (corePlusR2TypeConsistent_rename_iff
        transported permutation expected leftActual).mpr
      simpa [transported, Function.comp_def] using leftConsistent
    simpa [expectedFixed, candidateEquation] using renamedConsistent
  have constraintAgreement : ∀ name,
      name ∈ TypeSubst.typeVars expected ++
          TypeSubst.typeVars rightActual →
        transported name = rightModel name := by
    intro name member
    rcases List.mem_append.mp member with expectedMember | actualMember
    · have theoryMember := expectedObserved name expectedMember
      have fixedMember := theoryCovered name theoryMember
      have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
        intro candidateMember
        exact rightActualAvoids name candidateMember fixedMember
      simp [rightModel, notCandidate, transported, Function.comp_apply,
        inverseFixed name fixedMember, baseAgrees name theoryMember]
    · simp [rightModel, actualMember]
  have rightConsistent : CorePlusR2TypeConsistent rightModel
      expected rightActual :=
    (corePlusR2TypeConsistent_congr_of_typeVars
      expected rightActual constraintAgreement).mp transportedConsistent
  refine ⟨rightModel, rightSatisfied, rightConsistent, ?_⟩
  intro name member
  have theoryMember := observationObserved name member
  have fixedMember := theoryCovered name theoryMember
  have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
    intro candidateMember
    exact rightActualAvoids name candidateMember fixedMember
  simpa [rightModel, notCandidate] using baseAgrees name theoryMember

/-- Runtime-support variant of
`transport_model_across_presentations_of_target_fresh`.

The exact right presentation may use an independent private spelling, so
syntactic support inclusion is neither required nor generally true.
`TypePresentationSimulationState` proves that its complete solution theory
depends only on the variables occurring in the runtime binding list; the
runtime candidate is fresh from exactly that support. -/
theorem PrivateCandidateAlphaRel.transport_model_across_presentations_of_runtime_target_fresh
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {rightSpec : Bindings} {runtimeBindings : Metta.Bindings}
    {expected leftActual rightActual : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (rightState : TypePresentationSimulationState
      rightIncoming rightSpec runtimeBindings)
    (rightTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars rightActual →
        name ∉ runtimeBindings.vars)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope)
    (leftModel : String → Atom)
    (leftSatisfied : TypeSubstSatisfied leftModel leftIncoming)
    (leftConsistent : CorePlusR2TypeConsistent
      leftModel expected leftActual) :
    ∃ rightModel,
      TypeSubstSatisfied rightModel rightIncoming ∧
        CorePlusR2TypeConsistent rightModel expected rightActual ∧
        ValuationsAgreeOn observationScope leftModel rightModel := by
  obtain ⟨permutation, fixed, candidateEquation⟩ :=
    alpha.exists_public_fixed_permutation
  obtain ⟨rightBase, rightBaseSatisfied, baseAgrees⟩ :=
    incomingEquiv.leftToRight leftModel leftSatisfied
  let transported : String → Atom := leftModel ∘ permutation.symm
  let rightModel : String → Atom := fun name =>
    if name ∈ TypeSubst.typeVars rightActual then
      transported name
    else
      rightBase name
  have inverseFixed : ∀ name, name ∈ fixedScope →
      permutation.symm name = name := by
    intro name member
    apply permutation.injective
    simp [fixed name member]
  have rightModelAgreesBaseOnRuntime :
      ValuationsAgreeOn runtimeBindings.vars rightBase rightModel := by
    intro name member
    have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
      intro candidateMember
      exact rightTargetFresh name candidateMember member
    simp [rightModel, notCandidate]
  have rightSatisfied : TypeSubstSatisfied rightModel rightIncoming :=
    (rightState.satisfied_congr_on_runtimeVars
      rightModelAgreesBaseOnRuntime).mp rightBaseSatisfied
  have rightActualAvoids : ∀ name,
      name ∈ TypeSubst.typeVars rightActual → name ∉ fixedScope :=
    alpha.vars_avoid_fixedScope.2
  have expectedFixed :
      renameTypeVars permutation expected = expected := by
    calc
      renameTypeVars permutation expected =
          renameTypeVars id expected := by
        apply renameTypeVars_congr_on_typeVars expected
        intro name member
        exact fixed name (theoryCovered name (expectedObserved name member))
      _ = expected := renameTypeVars_id expected
  have transportedConsistent : CorePlusR2TypeConsistent transported
      expected rightActual := by
    have renamedConsistent : CorePlusR2TypeConsistent transported
        (renameTypeVars permutation expected)
        (renameTypeVars permutation leftActual) := by
      apply (corePlusR2TypeConsistent_rename_iff
        transported permutation expected leftActual).mpr
      simpa [transported, Function.comp_def] using leftConsistent
    simpa [expectedFixed, candidateEquation] using renamedConsistent
  have constraintAgreement : ∀ name,
      name ∈ TypeSubst.typeVars expected ++
          TypeSubst.typeVars rightActual →
        transported name = rightModel name := by
    intro name member
    rcases List.mem_append.mp member with expectedMember | actualMember
    · have theoryMember := expectedObserved name expectedMember
      have fixedMember := theoryCovered name theoryMember
      have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
        intro candidateMember
        exact rightActualAvoids name candidateMember fixedMember
      simp [rightModel, notCandidate, transported, Function.comp_apply,
        inverseFixed name fixedMember, baseAgrees name theoryMember]
    · simp [rightModel, actualMember]
  have rightConsistent : CorePlusR2TypeConsistent rightModel
      expected rightActual :=
    (corePlusR2TypeConsistent_congr_of_typeVars
      expected rightActual constraintAgreement).mp transportedConsistent
  refine ⟨rightModel, rightSatisfied, rightConsistent, ?_⟩
  intro name member
  have theoryMember := observationObserved name member
  have fixedMember := theoryCovered name theoryMember
  have notCandidate : name ∉ TypeSubst.typeVars rightActual := by
    intro candidateMember
    exact rightActualAvoids name candidateMember fixedMember
  simpa [rightModel, notCandidate] using baseAgrees name theoryMember

/-! ## One matched constraint under scoped observation -/

/-- Two incoming finite theories extended by one type-consistency constraint
have the same observations on `scope`.  This is the semantic interface needed
by private-alpha candidate transport: no spelling map or canonical finite
substitution is chosen. -/
structure TypeConstraintTheoryEquivAt
    (scope : List String)
    (leftIncoming : TypeSubst) (leftExpected leftActual : Atom)
    (rightIncoming : TypeSubst) (rightExpected rightActual : Atom) : Prop where
  leftToRight : ∀ leftModel,
    TypeSubstSatisfied leftModel leftIncoming →
      CorePlusR2TypeConsistent leftModel leftExpected leftActual →
        ∃ rightModel,
          TypeSubstSatisfied rightModel rightIncoming ∧
            CorePlusR2TypeConsistent
              rightModel rightExpected rightActual ∧
            ValuationsAgreeOn scope leftModel rightModel
  rightToLeft : ∀ rightModel,
    TypeSubstSatisfied rightModel rightIncoming →
      CorePlusR2TypeConsistent rightModel rightExpected rightActual →
        ∃ leftModel,
          TypeSubstSatisfied leftModel leftIncoming ∧
            CorePlusR2TypeConsistent
              leftModel leftExpected leftActual ∧
            ValuationsAgreeOn scope leftModel rightModel

namespace TypeConstraintTheoryEquivAt

/-- Identical incoming theories and constraints are reflexively equivalent at
every observation scope. -/
theorem refl (scope : List String) (incoming : TypeSubst)
    (expected actual : Atom) :
    TypeConstraintTheoryEquivAt scope incoming expected actual
      incoming expected actual := by
  constructor <;> intro model satisfied consistent <;>
    exact ⟨model, satisfied, consistent, fun _ _ => rfl⟩

/-- Constraint-theory equivalence is symmetric. -/
theorem symm {scope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {leftExpected leftActual rightExpected rightActual : Atom}
    (equiv : TypeConstraintTheoryEquivAt scope
      leftIncoming leftExpected leftActual
      rightIncoming rightExpected rightActual) :
    TypeConstraintTheoryEquivAt scope
      rightIncoming rightExpected rightActual
      leftIncoming leftExpected leftActual := by
  constructor
  · intro rightModel rightSatisfied rightConsistent
    obtain ⟨leftModel, leftSatisfied, leftConsistent, agrees⟩ :=
      equiv.rightToLeft rightModel rightSatisfied rightConsistent
    exact ⟨leftModel, leftSatisfied, leftConsistent,
      fun name member => (agrees name member).symm⟩
  · intro leftModel leftSatisfied leftConsistent
    obtain ⟨rightModel, rightSatisfied, rightConsistent, agrees⟩ :=
      equiv.leftToRight leftModel leftSatisfied leftConsistent
    exact ⟨rightModel, rightSatisfied, rightConsistent,
      fun name member => (agrees name member).symm⟩

end TypeConstraintTheoryEquivAt

/-- Scoped-equivalent incoming presentations remain equivalent after adding
the same public type-consistency constraint on both sides. -/
theorem TypeConstraintTheoryEquivAt.of_scopedIncoming_sameConstraint
    {theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {expected actual : Atom}
    (incomingEquiv : TypePresentationTheoryEquivAt theoryScope
      leftIncoming rightIncoming)
    (constraintObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected ++ TypeSubst.typeVars actual →
        name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope) :
    TypeConstraintTheoryEquivAt observationScope
      leftIncoming expected actual rightIncoming expected actual := by
  constructor
  · intro leftModel leftSatisfied leftConsistent
    obtain ⟨rightModel, rightSatisfied, agrees⟩ :=
      incomingEquiv.leftToRight leftModel leftSatisfied
    have constraintAgreement : ∀ name,
        name ∈ TypeSubst.typeVars expected ++ TypeSubst.typeVars actual →
          leftModel name = rightModel name := by
      intro name member
      exact agrees name (constraintObserved name member)
    exact ⟨rightModel, rightSatisfied,
      (corePlusR2TypeConsistent_congr_of_typeVars expected actual
        constraintAgreement).mp leftConsistent,
      fun name member => agrees name (observationObserved name member)⟩
  · intro rightModel rightSatisfied rightConsistent
    obtain ⟨leftModel, leftSatisfied, agrees⟩ :=
      incomingEquiv.rightToLeft rightModel rightSatisfied
    have constraintAgreement : ∀ name,
        name ∈ TypeSubst.typeVars expected ++ TypeSubst.typeVars actual →
          leftModel name = rightModel name := by
      intro name member
      exact agrees name (constraintObserved name member)
    exact ⟨leftModel, leftSatisfied,
      (corePlusR2TypeConsistent_congr_of_typeVars expected actual
        constraintAgreement).mpr rightConsistent,
      fun name member => agrees name (observationObserved name member)⟩

/-- Under a scope containing the incoming presentation, the raw formal, and
the observation boundary, private-alpha sibling candidates induce equivalent
one-step constraint theories. -/
theorem TypeConstraintTheoryEquivAt.of_privateCandidateAlpha
    {fixedScope observationScope : List String}
    {incoming : TypeSubst} {expected leftActual rightActual : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (incomingCovered : ∀ name,
      name ∈ specBindingVars ⟨incoming, []⟩ → name ∈ fixedScope)
    (expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ fixedScope)
    (observationCovered : ∀ name,
      name ∈ observationScope → name ∈ fixedScope) :
    TypeConstraintTheoryEquivAt observationScope
      incoming expected leftActual incoming expected rightActual := by
  have reverseAlpha :
      PrivateCandidateAlphaRel fixedScope rightActual leftActual := by
    rcases alpha with ⟨source, leftVariant, rightVariant⟩
    exact ⟨source, rightVariant, leftVariant⟩
  constructor
  · exact alpha.transport_model incomingCovered expectedCovered
      observationCovered
  · intro rightModel rightSatisfied rightConsistent
    obtain ⟨leftModel, leftSatisfied, leftConsistent, agrees⟩ :=
      reverseAlpha.transport_model incomingCovered expectedCovered
        observationCovered rightModel rightSatisfied rightConsistent
    exact ⟨leftModel, leftSatisfied, leftConsistent,
      fun name member => (agrees name member).symm⟩

/-- Scoped-equivalent incoming presentations remain scoped-equivalent after
matching private-alpha sibling candidates against the same public formal. -/
theorem TypeConstraintTheoryEquivAt.of_scopedIncoming_privateCandidateAlpha
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {expected leftActual rightActual : Atom}
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (leftIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨leftIncoming, []⟩ → name ∈ fixedScope)
    (rightIncomingCovered : ∀ name,
      name ∈ specBindingVars ⟨rightIncoming, []⟩ → name ∈ fixedScope)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope) :
    TypeConstraintTheoryEquivAt observationScope
      leftIncoming expected leftActual
      rightIncoming expected rightActual := by
  have reverseAlpha :
      PrivateCandidateAlphaRel fixedScope rightActual leftActual := by
    rcases alpha with ⟨source, leftVariant, rightVariant⟩
    exact ⟨source, rightVariant, leftVariant⟩
  constructor
  · exact alpha.transport_model_across_presentations incomingEquiv
      rightIncomingCovered theoryCovered expectedObserved
      observationObserved
  · intro rightModel rightSatisfied rightConsistent
    obtain ⟨leftModel, leftSatisfied, leftConsistent, agrees⟩ :=
      reverseAlpha.transport_model_across_presentations incomingEquiv.symm
        leftIncomingCovered theoryCovered expectedObserved
        observationObserved
        rightModel rightSatisfied rightConsistent
    exact ⟨leftModel, leftSatisfied, leftConsistent,
      fun name member => (agrees name member).symm⟩

/-- Scoped-equivalent incoming presentations remain equivalent after
matching sibling private candidates that are fresh from their respective
incoming theories.

Unlike `of_scopedIncoming_privateCandidateAlpha`, this theorem does not
force both finite presentations into one common syntactic avoid set.  The
shared set protects only the observed theory; each direction uses the
freshness of the target candidate against the presentation being patched. -/
theorem TypeConstraintTheoryEquivAt.of_scopedIncoming_privateCandidateAlpha_separateSupport
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {expected leftActual rightActual : Atom}
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (leftTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars leftActual →
        name ∉ specBindingVars ⟨leftIncoming, []⟩)
    (rightTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars rightActual →
        name ∉ specBindingVars ⟨rightIncoming, []⟩)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope) :
    TypeConstraintTheoryEquivAt observationScope
      leftIncoming expected leftActual
      rightIncoming expected rightActual := by
  have reverseAlpha :
      PrivateCandidateAlphaRel fixedScope rightActual leftActual := by
    rcases alpha with ⟨source, leftVariant, rightVariant⟩
    exact ⟨source, rightVariant, leftVariant⟩
  constructor
  · exact alpha.transport_model_across_presentations_of_target_fresh
      incomingEquiv rightTargetFresh theoryCovered expectedObserved
        observationObserved
  · intro rightModel rightSatisfied rightConsistent
    obtain ⟨leftModel, leftSatisfied, leftConsistent, agrees⟩ :=
      reverseAlpha.transport_model_across_presentations_of_target_fresh
        incomingEquiv.symm leftTargetFresh theoryCovered expectedObserved
          observationObserved rightModel rightSatisfied rightConsistent
    exact ⟨leftModel, leftSatisfied, leftConsistent,
      fun name member => (agrees name member).symm⟩

/-- Cross a scoped specification/runtime boundary without identifying the
runtime presentation's private syntactic support.  The left candidate is
fresh from the finite specification presentation; the right candidate is
fresh from the runtime binding list that semantically supports its exact
branch presentation. -/
theorem TypeConstraintTheoryEquivAt.of_scopedIncoming_privateCandidateAlpha_runtimeSupport
    {fixedScope theoryScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {rightSpec : Bindings} {runtimeBindings : Metta.Bindings}
    {expected leftActual rightActual : Atom}
    (incomingEquiv : TypePresentationTheoryEquivAt
      theoryScope leftIncoming rightIncoming)
    (rightState : TypePresentationSimulationState
      rightIncoming rightSpec runtimeBindings)
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (leftTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars leftActual →
        name ∉ specBindingVars ⟨leftIncoming, []⟩)
    (rightTargetFresh : ∀ name,
      name ∈ TypeSubst.typeVars rightActual →
        name ∉ runtimeBindings.vars)
    (theoryCovered : ∀ name, name ∈ theoryScope → name ∈ fixedScope)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ theoryScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ theoryScope) :
    TypeConstraintTheoryEquivAt observationScope
      leftIncoming expected leftActual
      rightIncoming expected rightActual := by
  have reverseAlpha :
      PrivateCandidateAlphaRel fixedScope rightActual leftActual := by
    rcases alpha with ⟨source, leftVariant, rightVariant⟩
    exact ⟨source, rightVariant, leftVariant⟩
  constructor
  · exact alpha.transport_model_across_presentations_of_runtime_target_fresh
      incomingEquiv rightState rightTargetFresh theoryCovered
        expectedObserved observationObserved
  · intro rightModel rightSatisfied rightConsistent
    obtain ⟨leftModel, leftSatisfied, leftConsistent, agrees⟩ :=
      reverseAlpha.transport_model_across_presentations_of_target_fresh
        incomingEquiv.symm leftTargetFresh theoryCovered expectedObserved
          observationObserved rightModel rightSatisfied rightConsistent
    exact ⟨leftModel, leftSatisfied, leftConsistent,
      fun name member => (agrees name member).symm⟩

/-- Finite presentation derivations expose exactly their incoming theory
conjoined with one consistency constraint.  Therefore a scoped equivalence of
those conjunctions transports directly to the two output presentations. -/
theorem CorePlusR2TypePresentationMatchRel.outputTheoryEquivAt
    {scope : List String}
    {leftIncoming leftOutput rightIncoming rightOutput : TypeSubst}
    {leftExpected leftActual rightExpected rightActual : Atom}
    (leftNormal : leftIncoming.Normal)
    (rightNormal : rightIncoming.Normal)
    (leftDerivation : CorePlusR2TypePresentationMatchRel
      leftIncoming leftExpected leftActual leftOutput)
    (rightDerivation : CorePlusR2TypePresentationMatchRel
      rightIncoming rightExpected rightActual rightOutput)
    (constraints : TypeConstraintTheoryEquivAt scope
      leftIncoming leftExpected leftActual
      rightIncoming rightExpected rightActual) :
    TypePresentationTheoryEquivAt scope leftOutput rightOutput := by
  constructor
  · intro leftModel leftSatisfied
    obtain ⟨leftIncomingSatisfied, leftConsistent⟩ :=
      (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        leftDerivation leftNormal leftModel).mp leftSatisfied
    obtain ⟨rightModel, rightIncomingSatisfied, rightConsistent, agrees⟩ :=
      constraints.leftToRight leftModel leftIncomingSatisfied leftConsistent
    exact ⟨rightModel,
      (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        rightDerivation rightNormal rightModel).mpr
        ⟨rightIncomingSatisfied, rightConsistent⟩,
      agrees⟩
  · intro rightModel rightSatisfied
    obtain ⟨rightIncomingSatisfied, rightConsistent⟩ :=
      (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        rightDerivation rightNormal rightModel).mp rightSatisfied
    obtain ⟨leftModel, leftIncomingSatisfied, leftConsistent, agrees⟩ :=
      constraints.rightToLeft rightModel rightIncomingSatisfied
        rightConsistent
    exact ⟨leftModel,
      (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        leftDerivation leftNormal leftModel).mpr
        ⟨leftIncomingSatisfied, leftConsistent⟩,
      agrees⟩

/-- A static specification presentation and one runtime binding state agree
through an exact branch-local presentation, with only the comparison between
the two finite presentations restricted to the declared public scope. -/
def ScopedTypePresentationSimulationState
    (scope : List String) (specPresentation : TypeSubst)
    (runtimeBindings : Metta.Bindings) : Prop :=
  specPresentation.Normal ∧
    ∃ branchPresentation specBindings,
      TypePresentationSimulationState
          branchPresentation specBindings runtimeBindings ∧
        TypePresentationTheoryEquivAt
          scope specPresentation branchPresentation

/-- Exact same-spelling simulation is the reflexive case of scoped
simulation. -/
theorem ScopedTypePresentationSimulationState.ofExact
    {scope : List String} {presentation : TypeSubst}
    {spec : Bindings} {runtime : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec runtime) :
    ScopedTypePresentationSimulationState scope presentation runtime :=
  ⟨state.normal, presentation, spec, state,
    TypePresentationTheoryEquivAt.refl scope presentation⟩

/-- Scoped simulation is contravariant in its observation scope: agreement
at a larger finite scope immediately gives agreement at every smaller scope.
This is the boundary used after a private signature scan, where the recursive
matcher may temporarily observe signature variables that the evaluator seal
does not expose. -/
theorem ScopedTypePresentationSimulationState.mono
    {large small : List String} {presentation : TypeSubst}
    {runtime : Metta.Bindings}
    (state : ScopedTypePresentationSimulationState
      large presentation runtime)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ScopedTypePresentationSimulationState small presentation runtime := by
  rcases state with
    ⟨normal, branchPresentation, specBindings,
      branchState, theory⟩
  exact ⟨normal, branchPresentation, specBindings, branchState,
    theory.mono subset⟩

/-- A scoped presentation state observes any declared type whose variables
lie in the public scope exactly as the repaired runtime does, up to private
alpha-renaming.  This is the diagnostic/policy projection of the semantic
state; it does not identify the private finite presentations syntactically. -/
theorem ScopedTypePresentationSimulationState.returnAlpha
    {scope : List String} {presentation : TypeSubst}
    {runtime : Metta.Bindings}
    (state : ScopedTypePresentationSimulationState
      scope presentation runtime)
    (declared : Atom)
    (declaredCovered : ∀ name,
      name ∈ TypeSubst.typeVars declared → name ∈ scope) :
    ObservedTypeAlphaRel
      (presentation.apply declared)
      (fromLeaTTaAtom
        (Metta.instantiate runtime (toLeaTTaAtom declared))) := by
  rcases state with
    ⟨presentationNormal, branchPresentation, specBindings,
      branchState, presentationEquiv⟩
  exact ObservedTypeAlphaRel.trans
    (presentationEquiv.observedTypeAlpha presentationNormal
      branchState.normal declared declaredCovered)
    (branchState.returnAlpha declared)

/-- Pointwise scoped simulation for an ordered branch list. -/
def ScopedTypePresentationSimulationStates
    (scope : List String) (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (ScopedTypePresentationSimulationState scope)
    presentations runtimeBindings

/-- Pointwise scope weakening for an ordered branch list. -/
theorem scopedTypePresentationSimulationStates_mono
    {large small : List String} {presentations : List TypeSubst}
    {runtimeBindings : List Metta.Bindings}
    (states : ScopedTypePresentationSimulationStates
      large presentations runtimeBindings)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ScopedTypePresentationSimulationStates
      small presentations runtimeBindings := by
  exact states.imp fun _ _ state => state.mono subset

/-! ## Boundary canaries -/

private def privateA : TypeSubst := [("t", .var "uA")]
private def privateB : TypeSubst := [("t", .var "uB")]

/-- With no observed names, two satisfiable private spellings have the same
empty-scope observations. -/
theorem private_spellings_empty_scope_equivalent :
    TypePresentationTheoryEquivAt [] privateA privateB := by
  have normalA : privateA.Normal := by
    simp [privateA, TypeSubst.Normal, TypeSubst.keys,
      TypeSubst.typeVars]
  have normalB : privateB.Normal := by
    simp [privateB, TypeSubst.Normal, TypeSubst.keys,
      TypeSubst.typeVars]
  constructor
  · intro _ _
    exact ⟨presentedValuation privateB,
      normal_presentedValuation_satisfied normalB, by simp [ValuationsAgreeOn]⟩
  · intro _ _
    exact ⟨presentedValuation privateA,
      normal_presentedValuation_satisfied normalA, by simp [ValuationsAgreeOn]⟩

private def spellingDiscriminator : String → Atom :=
  fun name => if name = "uB" then .symbol "B" else .symbol "A"

/-- Observing the public endpoint and both private spellings distinguishes the
two theories.  The scope restriction is therefore substantive, not a global
solution-theory equality disguised by a new carrier. -/
theorem private_spellings_not_globally_equivalent :
    ¬TypePresentationTheoryEquivAt ["t", "uA", "uB"] privateA privateB := by
  intro equiv
  have leftSatisfied : TypeSubstSatisfied spellingDiscriminator privateA := by
    simp [TypeSubstSatisfied, spellingDiscriminator, privateA,
      applyTypeValuation]
  obtain ⟨rightModel, rightSatisfied, agrees⟩ :=
    equiv.leftToRight spellingDiscriminator leftSatisfied
  have agreeT := agrees "t" (by simp)
  have agreeUA := agrees "uA" (by simp)
  have agreeUB := agrees "uB" (by simp)
  have rightEquation := rightSatisfied "t" (.var "uB") (by simp [privateB])
  simp [applyTypeValuation] at rightEquation
  simp [spellingDiscriminator] at agreeT agreeUA agreeUB
  rw [← agreeT, ← agreeUB] at rightEquation
  have namesEqual : "A" = "B" := Atom.symbol.inj rightEquation
  simp at namesEqual

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
