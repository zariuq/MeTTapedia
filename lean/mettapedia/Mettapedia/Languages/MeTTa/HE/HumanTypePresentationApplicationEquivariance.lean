import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationPrincipalAlpha
import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationCompleteness
import Mettapedia.Languages.MeTTa.HE.HumanTypePresentationExactNormal

/-!
# Alpha equivariance of finite application presentations

Application-type inference consumes independently freshened operator and
argument scopes.  This module isolates the semantic invariant used to compare
two lawful fresh presentations: renaming conjugates valuations, preserves the
complete consistency theory, and therefore preserves both success and
failure.  Successful outputs are compared through normal-presentation
principality rather than by identifying finite substitution records.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanTypePresentationApplicationEquivariance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentation
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationTheory
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationCompleteness
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationExact
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationExactNormal
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationAlpha
open Mettapedia.Languages.MeTTa.HE.HumanTypePresentationPrincipalAlpha
open Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement

mutual

/-- Valuation after whole-type renaming is valuation conjugation on variable
names. -/
theorem applyTypeValuation_renameHumanTypeVars
    (valuation : String → Atom) (rename : String → String) (atom : Atom) :
    applyTypeValuation valuation (renameHumanTypeVars rename atom) =
      applyTypeValuation (valuation ∘ rename) atom := by
  cases atom with
  | symbol name => simp [renameHumanTypeVars, applyTypeValuation]
  | var name => simp [renameHumanTypeVars, applyTypeValuation]
  | grounded value => simp [renameHumanTypeVars, applyTypeValuation]
  | expression atoms =>
      simp only [renameHumanTypeVars, applyTypeValuation,
        Atom.expression.injEq]
      exact applyTypeValuationList_renameHumanTypeVars
        valuation rename atoms

/-- List companion of `applyTypeValuation_renameHumanTypeVars`. -/
theorem applyTypeValuationList_renameHumanTypeVars
    (valuation : String → Atom) (rename : String → String)
    (atoms : List Atom) :
    (atoms.map (renameHumanTypeVars rename)).map
        (applyTypeValuation valuation) =
      atoms.map (applyTypeValuation (valuation ∘ rename)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨applyTypeValuation_renameHumanTypeVars
          valuation rename atom,
        applyTypeValuationList_renameHumanTypeVars
          valuation rename atoms⟩

end

mutual

/-- Recursive R2 consistency is invariant under simultaneous renaming of
both inputs and conjugation of the valuation. -/
theorem reducedTypeConsistent_rename_iff
    (valuation : String → Atom) (rename : String → String) :
    ∀ left right,
      ReducedTypeConsistent valuation
          (renameHumanTypeVars rename left)
          (renameHumanTypeVars rename right) ↔
        ReducedTypeConsistent (valuation ∘ rename) left right := by
  intro left right
  cases left <;> cases right <;>
    simp only [renameHumanTypeVars]
  case var.expression left right =>
    unfold ReducedTypeConsistent
    simp only [applyTypeValuation, Function.comp_apply]
    have listConjugation := applyTypeValuationList_renameHumanTypeVars
      valuation rename right
    simpa [List.map_map, Function.comp_def] using
      congrArg (fun values => valuation (rename left) = .expression values)
        listConjugation
  case expression.var left right =>
    unfold ReducedTypeConsistent
    simp only [applyTypeValuation, Function.comp_apply]
    have listConjugation := applyTypeValuationList_renameHumanTypeVars
      valuation rename left
    simpa [List.map_map, Function.comp_def] using
      congrArg (fun values => .expression values = valuation (rename right))
        listConjugation
  case expression.expression left right =>
    unfold ReducedTypeConsistent
    exact reducedTypeListConsistent_rename_iff
      valuation rename left right
  all_goals
    unfold ReducedTypeConsistent
  all_goals
    (try split) <;>
      simp_all [applyTypeValuation, Function.comp_apply]

/-- List companion of `reducedTypeConsistent_rename_iff`. -/
theorem reducedTypeListConsistent_rename_iff
    (valuation : String → Atom) (rename : String → String) :
    ∀ left right,
      ReducedTypeListConsistent valuation
          (left.map (renameHumanTypeVars rename))
          (right.map (renameHumanTypeVars rename)) ↔
        ReducedTypeListConsistent (valuation ∘ rename) left right := by
  intro left right
  cases left with
  | nil => cases right <;> simp [ReducedTypeListConsistent]
  | cons left lefts =>
      cases right with
      | nil => simp [ReducedTypeListConsistent]
      | cons right rights =>
          simp only [List.map_cons, ReducedTypeListConsistent]
          exact and_congr
            (reducedTypeConsistent_rename_iff
              valuation rename left right)
            (reducedTypeListConsistent_rename_iff
              valuation rename lefts rights)

end

/-- Published-top plus R2 consistency has the same simultaneous-renaming
invariance as its reduced structural core. -/
theorem corePlusR2TypeConsistent_rename_iff
    (valuation : String → Atom) (rename : String → String)
    (left right : Atom) :
    CorePlusR2TypeConsistent valuation
        (renameHumanTypeVars rename left)
        (renameHumanTypeVars rename right) ↔
      CorePlusR2TypeConsistent (valuation ∘ rename) left right := by
  simp only [CorePlusR2TypeConsistent]
  have undefinedPreserved (atom : Atom) :
      renameHumanTypeVars rename atom = Atom.undefinedType ↔
        atom = Atom.undefinedType := by
    cases atom <;> simp [renameHumanTypeVars, Atom.undefinedType]
  have atomPreserved (candidate : Atom) :
      renameHumanTypeVars rename candidate = Atom.atomType ↔
        candidate = Atom.atomType := by
    cases candidate <;> simp [renameHumanTypeVars, Atom.atomType]
  rw [undefinedPreserved left, undefinedPreserved right,
    atomPreserved left, atomPreserved right,
    reducedTypeConsistent_rename_iff]

/-! ## One global permutation for independent finite scopes -/

mutual

private theorem typeVars_rename
    (rename : String → String) (atom : Atom) :
    TypeSubst.typeVars (renameHumanTypeVars rename atom) =
      (TypeSubst.typeVars atom).map rename := by
  cases atom with
  | symbol name => simp [renameHumanTypeVars, TypeSubst.typeVars]
  | var name => simp [renameHumanTypeVars, TypeSubst.typeVars]
  | grounded value => simp [renameHumanTypeVars, TypeSubst.typeVars]
  | expression atoms =>
      simpa [renameHumanTypeVars, TypeSubst.typeVars] using
        typeVarsList_rename rename atoms

private theorem typeVarsList_rename
    (rename : String → String) (atoms : List Atom) :
    TypeSubst.typeVarsList
        (atoms.map (renameHumanTypeVars rename)) =
      (TypeSubst.typeVarsList atoms).map rename := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, TypeSubst.typeVarsList,
        List.map_append]
      exact congrArg₂ List.append
        (typeVars_rename rename atom)
        (typeVarsList_rename rename atoms)

end

mutual

private theorem rename_congr_on_typeVars
    {left right : String → String} (atom : Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVars atom →
      left name = right name) :
    renameHumanTypeVars left atom = renameHumanTypeVars right atom := by
  cases atom with
  | symbol name => simp [renameHumanTypeVars]
  | var name =>
      simp only [renameHumanTypeVars, Atom.var.injEq]
      exact agrees name (by simp [TypeSubst.typeVars])
  | grounded value => simp [renameHumanTypeVars]
  | expression atoms =>
      simp only [renameHumanTypeVars, Atom.expression.injEq]
      apply renameList_congr_on_typeVars
      intro name member
      exact agrees name (by simpa [TypeSubst.typeVars] using member)

private theorem renameList_congr_on_typeVars
    {left right : String → String} (atoms : List Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVarsList atoms →
      left name = right name) :
    atoms.map (renameHumanTypeVars left) =
      atoms.map (renameHumanTypeVars right) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply rename_congr_on_typeVars atom
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply renameList_congr_on_typeVars atoms
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

end

mutual

private theorem rename_comp
    (outer inner : String → String) (atom : Atom) :
    renameHumanTypeVars outer (renameHumanTypeVars inner atom) =
      renameHumanTypeVars (outer ∘ inner) atom := by
  cases atom with
  | symbol name => simp [renameHumanTypeVars]
  | var name => simp [renameHumanTypeVars, Function.comp_apply]
  | grounded value => simp [renameHumanTypeVars]
  | expression atoms =>
      simp only [renameHumanTypeVars, Atom.expression.injEq]
      exact renameList_comp outer inner atoms

private theorem renameList_comp
    (outer inner : String → String) (atoms : List Atom) :
    (atoms.map (renameHumanTypeVars inner)).map
        (renameHumanTypeVars outer) =
      atoms.map (renameHumanTypeVars (outer ∘ inner)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rename_comp outer inner atom,
        renameList_comp outer inner atoms⟩

end


/-- The variables of one scoped atom do not occur in any later scope. -/
def AtomVarsFreshFromAtoms (atom : Atom) (atoms : List Atom) : Prop :=
  ∀ name, name ∈ TypeSubst.typeVars atom →
    name ∉ TypeSubst.typeVarsList atoms

/-- Pointwise alpha evidence together with the pairwise-disjoint scope law
needed to combine all local renamings into one finite permutation. -/
inductive ScopedObservedTypeListAlphaRel :
    List Atom → List Atom → Prop where
  | nil : ScopedObservedTypeListAlphaRel [] []
  | cons {left right : Atom} {lefts rights : List Atom} :
      ObservedTypeAlphaRel left right →
      AtomVarsFreshFromAtoms left lefts →
      AtomVarsFreshFromAtoms right rights →
      ScopedObservedTypeListAlphaRel lefts rights →
      ScopedObservedTypeListAlphaRel
        (left :: lefts) (right :: rights)

/-- Pairwise-disjoint local alpha scopes combine into one global finite
permutation.  The construction tags every local source scope before invoking
finite permutation extension, so equal private spellings in different scopes
remain independent. -/
theorem ScopedObservedTypeListAlphaRel.exists_permutation
    {left right : List Atom}
    (alpha : ScopedObservedTypeListAlphaRel left right) :
    ∃ permutation : Equiv.Perm String,
      right = left.map (renameHumanTypeVars permutation) := by
  induction alpha with
  | nil => exact ⟨Equiv.refl String, rfl⟩
  | @cons leftHead rightHead leftTail rightTail
      headAlpha leftFresh rightFresh tailAlpha ih =>
      obtain ⟨tailPermutation, tailEquation⟩ := ih
      rcases headAlpha with
        ⟨source,
          ⟨leftRename, leftInjective, leftEquation⟩,
          ⟨rightRename, rightInjective, rightEquation⟩⟩
      let HeadVariable :=
        {name : String // name ∈ TypeSubst.typeVars source}
      let TailVariable :=
        {name : String // name ∈ TypeSubst.typeVarsList leftTail}
      let ScopedVariable := Sum HeadVariable TailVariable
      let leftImage : ScopedVariable → String
        | .inl name => leftRename name.1
        | .inr name => name.1
      let rightImage : ScopedVariable → String
        | .inl name => rightRename name.1
        | .inr name => tailPermutation name.1
      have leftHeadMember (name : HeadVariable) :
          leftRename name.1 ∈ TypeSubst.typeVars leftHead := by
        rw [leftEquation, typeVars_rename]
        exact List.mem_map.mpr ⟨name.1, name.2, rfl⟩
      have rightHeadMember (name : HeadVariable) :
          rightRename name.1 ∈ TypeSubst.typeVars rightHead := by
        rw [rightEquation, typeVars_rename]
        exact List.mem_map.mpr ⟨name.1, name.2, rfl⟩
      have rightTailMember (name : TailVariable) :
          tailPermutation name.1 ∈
            TypeSubst.typeVarsList rightTail := by
        rw [tailEquation, typeVarsList_rename]
        exact List.mem_map.mpr ⟨name.1, name.2, rfl⟩
      have leftImageInjective : Function.Injective leftImage := by
        intro first second equal
        cases first with
        | inl first =>
            cases second with
            | inl second =>
                congr 1
                apply Subtype.ext
                exact leftInjective equal
            | inr second =>
                exfalso
                exact leftFresh _ (leftHeadMember first) (by
                  change leftRename first.1 = second.1 at equal
                  rw [equal]
                  exact second.2)
        | inr first =>
            cases second with
            | inl second =>
                exfalso
                exact leftFresh _ (leftHeadMember second) (by
                  change first.1 = leftRename second.1 at equal
                  rw [← equal]
                  exact first.2)
            | inr second =>
                congr 1
                exact Subtype.ext equal
      have rightImageInjective : Function.Injective rightImage := by
        intro first second equal
        cases first with
        | inl first =>
            cases second with
            | inl second =>
                congr 1
                apply Subtype.ext
                exact rightInjective equal
            | inr second =>
                exfalso
                exact rightFresh _ (rightHeadMember first) (by
                  change rightRename first.1 =
                    tailPermutation second.1 at equal
                  rw [equal]
                  exact rightTailMember second)
        | inr first =>
            cases second with
            | inl second =>
                exfalso
                exact rightFresh _ (rightHeadMember second) (by
                  change tailPermutation first.1 =
                    rightRename second.1 at equal
                  rw [← equal]
                  exact rightTailMember first)
            | inr second =>
                congr 1
                apply Subtype.ext
                exact tailPermutation.injective equal
      obtain ⟨permutation, extensionLaw⟩ :=
        Equiv.Perm.exists_extending_pair
          leftImage rightImage leftImageInjective rightImageInjective
      have headEquation :
          rightHead = renameHumanTypeVars permutation leftHead := by
        rw [leftEquation, rightEquation, rename_comp]
        apply rename_congr_on_typeVars source
        intro name member
        exact (extensionLaw (Sum.inl (β := TailVariable)
          (⟨name, member⟩ : HeadVariable))).symm
      have globalTailEquation :
          rightTail =
            leftTail.map (renameHumanTypeVars permutation) := by
        rw [tailEquation]
        apply renameList_congr_on_typeVars leftTail
        intro name member
        exact (extensionLaw (Sum.inr (α := HeadVariable)
          (⟨name, member⟩ : TailVariable))).symm
      exact ⟨permutation,
        congrArg₂ List.cons headEquation globalTailEquation⟩

/-! ## Complete argument-fold theory -/

/-- The complete solution theory of the ordered presentation fold, stated in
the human lane so equivariance does not depend on a runtime bridge module. -/
theorem presentationArgumentList_solutions
    {expected actual : List Atom} {incoming output : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual incoming output)
    (normal : incoming.Normal) (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation incoming ∧
        List.Forall₂
          (CorePlusR2TypeConsistent valuation) expected actual := by
  induction derivation with
  | nil substitution => simp
  | @cons expected actual expecteds actuals incoming next output head tail ih =>
      have nextNormal := head.output_normal normal
      rw [ih nextNormal,
        HumanTypePresentationMatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
          head normal valuation]
      constructor
      · rintro ⟨⟨incomingSatisfied, headConsistent⟩, tailConsistent⟩
        exact ⟨incomingSatisfied,
          List.Forall₂.cons headConsistent tailConsistent⟩
      · rintro ⟨incomingSatisfied, allConsistent⟩
        cases allConsistent with
        | cons headConsistent tailConsistent =>
            exact ⟨⟨incomingSatisfied, headConsistent⟩,
              tailConsistent⟩

/-- Pointwise application constraints conjugate under one simultaneous
renaming of both sides. -/
theorem argumentConsistency_rename_iff
    (valuation : String → Atom) (rename : String → String) :
    ∀ expected actual,
      List.Forall₂ (CorePlusR2TypeConsistent valuation)
          (expected.map (renameHumanTypeVars rename))
          (actual.map (renameHumanTypeVars rename)) ↔
        List.Forall₂
          (CorePlusR2TypeConsistent (valuation ∘ rename))
          expected actual := by
  intro expected
  induction expected with
  | nil =>
      intro actual
      cases actual <;> simp
  | cons expected expecteds ih =>
      intro actual
      cases actual with
      | nil => simp
      | cons actual actuals =>
          constructor
          · intro consistent
            cases consistent with
            | cons head tail =>
                exact List.Forall₂.cons
                  ((corePlusR2TypeConsistent_rename_iff
                    valuation rename expected actual).mp head)
                  ((ih actuals).mp tail)
          · intro consistent
            cases consistent with
            | cons head tail =>
                exact List.Forall₂.cons
                  ((corePlusR2TypeConsistent_rename_iff
                    valuation rename expected actual).mpr head)
                  ((ih actuals).mpr tail)

/-- A valuation satisfying the incoming normal presentation and every
ordered argument constraint reconstructs a normal, satisfied finite output
presentation. -/
theorem PresentationArgumentListMatchRel.exists_of_satisfied
    {valuation : String → Atom} {incoming : TypeSubst}
    (normal : incoming.Normal)
    (satisfied : TypeSubstSatisfied valuation incoming) :
    ∀ {expected actual},
      List.Forall₂ (CorePlusR2TypeConsistent valuation)
        expected actual →
      ∃ output,
        PresentationArgumentListMatchRel
            expected actual incoming output ∧
          output.Normal ∧ TypeSubstSatisfied valuation output := by
  intro expected actual consistent
  induction consistent generalizing incoming with
  | nil =>
      exact ⟨incoming,
        PresentationArgumentListMatchRel.nil incoming,
        normal, satisfied⟩
  | @cons expected actual expecteds actuals head tail ih =>
      obtain ⟨next, headMatch, nextNormal, nextSatisfied⟩ :=
        CorePlusR2TypePresentationMatchRel.exists_of_satisfied
          normal satisfied expected actual head
      obtain ⟨output, tailMatch, outputNormal, outputSatisfied⟩ :=
        ih nextNormal nextSatisfied
      exact ⟨output,
        PresentationArgumentListMatchRel.cons headMatch tailMatch,
        outputNormal, outputSatisfied⟩

/-- An application argument presentation exists exactly when the complete
ordered consistency system has a model. -/
theorem presentationArgumentList_exists_iff
    (expected actual : List Atom) :
    (∃ output,
      PresentationArgumentListMatchRel expected actual [] output) ↔
      ∃ valuation,
        List.Forall₂ (CorePlusR2TypeConsistent valuation)
          expected actual := by
  constructor
  · rintro ⟨output, derivation⟩
    have outputNormal :=
      HumanTypePresentationExactNormal.PresentationArgumentListMatchRel.output_normal
        derivation TypeSubst.normal_empty
    let valuation := presentedValuation output
    have outputSatisfied : TypeSubstSatisfied valuation output :=
      normal_presentedValuation_satisfied outputNormal
    have theory := presentationArgumentList_solutions
      derivation TypeSubst.normal_empty valuation
    exact ⟨valuation, (theory.mp outputSatisfied).2⟩
  · rintro ⟨valuation, consistent⟩
    obtain ⟨output, derivation, _normal, _satisfied⟩ :=
      PresentationArgumentListMatchRel.exists_of_satisfied
        TypeSubst.normal_empty
        (by simp [TypeSubstSatisfied]) consistent
    exact ⟨output, derivation⟩

/-- Simultaneous permutation of all variables preserves and reflects
application-fold success.  The inverse permutation supplies the reverse
valuation without any choice of private spelling. -/
theorem presentationArgumentList_success_perm_iff
    (permutation : Equiv.Perm String)
    (expected actual : List Atom) :
    (∃ output,
      PresentationArgumentListMatchRel
        (expected.map (renameHumanTypeVars permutation))
        (actual.map (renameHumanTypeVars permutation)) [] output) ↔
      ∃ output,
        PresentationArgumentListMatchRel expected actual [] output := by
  rw [presentationArgumentList_exists_iff,
    presentationArgumentList_exists_iff]
  constructor
  · rintro ⟨valuation, consistent⟩
    exact ⟨valuation ∘ permutation,
      (argumentConsistency_rename_iff
        valuation permutation expected actual).mp consistent⟩
  · rintro ⟨valuation, consistent⟩
    let renamedValuation : String → Atom :=
      valuation ∘ permutation.symm
    refine ⟨renamedValuation,
      (argumentConsistency_rename_iff
        renamedValuation permutation expected actual).mpr ?_⟩
    simpa [renamedValuation, Function.comp_def] using consistent

/-! ## Principal output comparison -/

/-- Two successful folds for permutation-related problems emit alpha-exact
presentations of corresponding return atoms. -/
theorem PresentationArgumentListMatchRel.output_alpha_of_perm
    {expected actual : List Atom} {leftOutput rightOutput : TypeSubst}
    (permutation : Equiv.Perm String)
    (leftDerivation : PresentationArgumentListMatchRel
      expected actual [] leftOutput)
    (rightDerivation : PresentationArgumentListMatchRel
      (expected.map (renameHumanTypeVars permutation))
      (actual.map (renameHumanTypeVars permutation)) [] rightOutput)
    (returnType : Atom) :
    ObservedTypeAlphaRel
      (leftOutput.apply returnType)
      (rightOutput.apply (renameHumanTypeVars permutation returnType)) := by
  let leftModel := presentedValuation leftOutput
  let rightModel := presentedValuation rightOutput
  let transportedLeftModel : String → Atom :=
    leftModel ∘ permutation.symm
  have leftNormal :=
    HumanTypePresentationExactNormal.PresentationArgumentListMatchRel.output_normal
      leftDerivation TypeSubst.normal_empty
  have rightNormal :=
    HumanTypePresentationExactNormal.PresentationArgumentListMatchRel.output_normal
      rightDerivation TypeSubst.normal_empty
  have leftModelSatisfied : TypeSubstSatisfied leftModel leftOutput :=
    normal_presentedValuation_satisfied leftNormal
  have leftConsistent :
      List.Forall₂ (CorePlusR2TypeConsistent leftModel)
        expected actual :=
    ((presentationArgumentList_solutions leftDerivation
      TypeSubst.normal_empty leftModel).mp leftModelSatisfied).2
  have transportedConsistent :
      List.Forall₂
        (CorePlusR2TypeConsistent transportedLeftModel)
        (expected.map (renameHumanTypeVars permutation))
        (actual.map (renameHumanTypeVars permutation)) := by
    apply (argumentConsistency_rename_iff
      transportedLeftModel permutation expected actual).mpr
    simpa [transportedLeftModel, Function.comp_def] using leftConsistent
  have transportedSatisfied :
      TypeSubstSatisfied transportedLeftModel rightOutput :=
    (presentationArgumentList_solutions rightDerivation
      TypeSubst.normal_empty transportedLeftModel).mpr
        ⟨by simp [TypeSubstSatisfied], transportedConsistent⟩
  have rightModelSatisfied : TypeSubstSatisfied rightModel rightOutput :=
    normal_presentedValuation_satisfied rightNormal
  have rightConsistent :
      List.Forall₂ (CorePlusR2TypeConsistent rightModel)
        (expected.map (renameHumanTypeVars permutation))
        (actual.map (renameHumanTypeVars permutation)) :=
    ((presentationArgumentList_solutions rightDerivation
      TypeSubst.normal_empty rightModel).mp rightModelSatisfied).2
  have pulledRightConsistent :
      List.Forall₂
        (CorePlusR2TypeConsistent (rightModel ∘ permutation))
        expected actual :=
    (argumentConsistency_rename_iff
      rightModel permutation expected actual).mp rightConsistent
  have pulledRightSatisfied :
      TypeSubstSatisfied (rightModel ∘ permutation) leftOutput :=
    (presentationArgumentList_solutions leftDerivation
      TypeSubst.normal_empty (rightModel ∘ permutation)).mpr
        ⟨by simp [TypeSubstSatisfied], pulledRightConsistent⟩
  have rightFactorsThroughTransportedLeft :
      ∃ post : String → Atom, ∀ name,
        presentedValuation rightOutput name =
          applyTypeValuation post (transportedLeftModel name) := by
    refine ⟨rightModel ∘ permutation, ?_⟩
    intro name
    have factor := typeSubst_factorization
      pulledRightSatisfied (.var (permutation.symm name))
    simpa [leftModel, rightModel, transportedLeftModel,
      applyTypeValuation, Function.comp_def] using factor.symm
  have alpha := observedTypeAlpha_of_mutuallyPrincipal
    rightNormal transportedSatisfied
      rightFactorsThroughTransportedLeft
      (renameHumanTypeVars permutation returnType)
  have transportedObservation :
      applyTypeValuation transportedLeftModel
          (renameHumanTypeVars permutation returnType) =
        leftOutput.apply returnType := by
    rw [applyTypeValuation_renameHumanTypeVars]
    simp [transportedLeftModel, leftModel, Function.comp_def,
      applyTypeValuation_presented_eq_apply]
  rw [transportedObservation] at alpha
  exact alpha.symm

/-! ## Boundary examples -/

/-- Positive: a nontrivial swap of private type-variable spellings preserves
an empty argument fold and transports its observed return. -/
theorem empty_fold_return_alpha_swap :
    ObservedTypeAlphaRel (.var "t") (.var "u") := by
  have alpha := PresentationArgumentListMatchRel.output_alpha_of_perm
    (permutation := Equiv.swap "t" "u")
    (leftDerivation := PresentationArgumentListMatchRel.nil [])
    (rightDerivation := PresentationArgumentListMatchRel.nil [])
    (returnType := .var "t")
  simpa [TypeSubst.apply, renameHumanTypeVars] using alpha

/-- Negative: alpha permutation cannot manufacture consistency between two
distinct closed type symbols. -/
theorem distinct_concrete_arguments_remain_inconsistent :
    ¬∃ output,
      PresentationArgumentListMatchRel
        [.symbol "A"] [.symbol "B"] [] output := by
  rw [presentationArgumentList_exists_iff]
  simp [CorePlusR2TypeConsistent, ReducedTypeConsistent,
    Atom.undefinedType, Atom.atomType]

end Mettapedia.Languages.MeTTa.HE.HumanTypePresentationApplicationEquivariance
