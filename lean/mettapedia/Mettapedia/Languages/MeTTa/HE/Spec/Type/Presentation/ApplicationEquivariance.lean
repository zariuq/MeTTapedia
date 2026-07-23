import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrincipalAlpha
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal

/-!
# Alpha equivariance of finite application presentations

Application-type inference consumes independently freshened operator and
argument scopes.  This module isolates the semantic invariant used to compare
two lawful fresh presentations: renaming conjugates valuations, preserves the
complete consistency theory, and therefore preserves both success and
failure.  Successful outputs are compared through normal-presentation
principality rather than by identifying finite substitution records.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Alpha
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrincipalAlpha
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

mutual

/-- Valuation after whole-type renaming is valuation conjugation on variable
names. -/
theorem applyTypeValuation_renameTypeVars
    (valuation : String → Atom) (rename : String → String) (atom : Atom) :
    applyTypeValuation valuation (renameTypeVars rename atom) =
      applyTypeValuation (valuation ∘ rename) atom := by
  cases atom with
  | symbol name => simp [renameTypeVars, applyTypeValuation]
  | var name => simp [renameTypeVars, applyTypeValuation]
  | grounded value => simp [renameTypeVars, applyTypeValuation]
  | expression atoms =>
      simp only [renameTypeVars, applyTypeValuation,
        Atom.expression.injEq]
      exact applyTypeValuationList_renameTypeVars
        valuation rename atoms

/-- List companion of `applyTypeValuation_renameTypeVars`. -/
theorem applyTypeValuationList_renameTypeVars
    (valuation : String → Atom) (rename : String → String)
    (atoms : List Atom) :
    (atoms.map (renameTypeVars rename)).map
        (applyTypeValuation valuation) =
      atoms.map (applyTypeValuation (valuation ∘ rename)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨applyTypeValuation_renameTypeVars
          valuation rename atom,
        applyTypeValuationList_renameTypeVars
          valuation rename atoms⟩

end

mutual

/-- Recursive R2 consistency is invariant under simultaneous renaming of
both inputs and conjugation of the valuation. -/
theorem reducedTypeConsistent_rename_iff
    (valuation : String → Atom) (rename : String → String) :
    ∀ left right,
      ReducedTypeConsistent valuation
          (renameTypeVars rename left)
          (renameTypeVars rename right) ↔
        ReducedTypeConsistent (valuation ∘ rename) left right := by
  intro left right
  cases left <;> cases right <;>
    simp only [renameTypeVars]
  case var.expression left right =>
    unfold ReducedTypeConsistent
    simp only [applyTypeValuation, Function.comp_apply]
    have listConjugation := applyTypeValuationList_renameTypeVars
      valuation rename right
    simpa [List.map_map, Function.comp_def] using
      congrArg (fun values => valuation (rename left) = .expression values)
        listConjugation
  case expression.var left right =>
    unfold ReducedTypeConsistent
    simp only [applyTypeValuation, Function.comp_apply]
    have listConjugation := applyTypeValuationList_renameTypeVars
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
          (left.map (renameTypeVars rename))
          (right.map (renameTypeVars rename)) ↔
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
        (renameTypeVars rename left)
        (renameTypeVars rename right) ↔
      CorePlusR2TypeConsistent (valuation ∘ rename) left right := by
  simp only [CorePlusR2TypeConsistent]
  have undefinedPreserved (atom : Atom) :
      renameTypeVars rename atom = Atom.undefinedType ↔
        atom = Atom.undefinedType := by
    cases atom <;> simp [renameTypeVars, Atom.undefinedType]
  have atomPreserved (candidate : Atom) :
      renameTypeVars rename candidate = Atom.atomType ↔
        candidate = Atom.atomType := by
    cases candidate <;> simp [renameTypeVars, Atom.atomType]
  rw [undefinedPreserved left, undefinedPreserved right,
    atomPreserved left, atomPreserved right,
    reducedTypeConsistent_rename_iff]

/-! ## Consistency of two alpha presentations -/

mutual

/-- Two renamings of the same type are recursively consistent whenever the
valuation identifies corresponding source variables.  Unlike simultaneous
renaming invariance, this theorem compares independently chosen private
spellings. -/
theorem reducedTypeConsistent_two_renames
    (valuation : String → Atom) (left right : String → String) :
    ∀ source,
      (∀ name, name ∈ TypeSubst.typeVars source →
        valuation (left name) = valuation (right name)) →
      ReducedTypeConsistent valuation
        (renameTypeVars left source) (renameTypeVars right source) := by
  intro source agrees
  cases source with
  | symbol name =>
      by_cases undefined : name = "%Undefined%"
      · subst name
        simp [renameTypeVars, ReducedTypeConsistent]
      · simp [renameTypeVars, ReducedTypeConsistent]
  | var name =>
      simpa [renameTypeVars, ReducedTypeConsistent] using
        agrees name (by simp [TypeSubst.typeVars])
  | grounded value =>
      simp [renameTypeVars, ReducedTypeConsistent]
  | expression atoms =>
      simpa [renameTypeVars, ReducedTypeConsistent,
        TypeSubst.typeVars] using
        reducedTypeListConsistent_two_renames valuation left right atoms
          agrees

/-- List companion of `reducedTypeConsistent_two_renames`. -/
theorem reducedTypeListConsistent_two_renames
    (valuation : String → Atom) (left right : String → String) :
    ∀ sources,
      (∀ name, name ∈ TypeSubst.typeVarsList sources →
        valuation (left name) = valuation (right name)) →
      ReducedTypeListConsistent valuation
        (sources.map (renameTypeVars left))
        (sources.map (renameTypeVars right)) := by
  intro sources agrees
  cases sources with
  | nil => simp [ReducedTypeListConsistent]
  | cons source sources =>
      simp only [List.map_cons, ReducedTypeListConsistent]
      constructor
      · apply reducedTypeConsistent_two_renames valuation left right source
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply reducedTypeListConsistent_two_renames valuation left right
          sources
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

end


/-- The complete top-level type consistency relation inherits independent
alpha-presentation consistency. -/
theorem corePlusR2TypeConsistent_two_renames
    (valuation : String → Atom) (left right : String → String)
    (source : Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVars source →
      valuation (left name) = valuation (right name)) :
    CorePlusR2TypeConsistent valuation
      (renameTypeVars left source) (renameTypeVars right source) := by
  exact Or.inr (Or.inr (Or.inr (Or.inr
    (reducedTypeConsistent_two_renames valuation left right source agrees))))

/-! ## One global permutation for independent finite scopes -/

mutual

private theorem typeVars_rename
    (rename : String → String) (atom : Atom) :
    TypeSubst.typeVars (renameTypeVars rename atom) =
      (TypeSubst.typeVars atom).map rename := by
  cases atom with
  | symbol name => simp [renameTypeVars, TypeSubst.typeVars]
  | var name => simp [renameTypeVars, TypeSubst.typeVars]
  | grounded value => simp [renameTypeVars, TypeSubst.typeVars]
  | expression atoms =>
      simpa [renameTypeVars, TypeSubst.typeVars] using
        typeVarsList_rename rename atoms

private theorem typeVarsList_rename
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
        (typeVars_rename rename atom)
        (typeVarsList_rename rename atoms)

end

mutual

private theorem rename_congr_on_typeVars
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
      apply renameList_congr_on_typeVars
      intro name member
      exact agrees name (by simpa [TypeSubst.typeVars] using member)

private theorem renameList_congr_on_typeVars
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
    renameTypeVars outer (renameTypeVars inner atom) =
      renameTypeVars (outer ∘ inner) atom := by
  cases atom with
  | symbol name => simp [renameTypeVars]
  | var name => simp [renameTypeVars, Function.comp_apply]
  | grounded value => simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, Atom.expression.injEq]
      exact renameList_comp outer inner atoms

private theorem renameList_comp
    (outer inner : String → String) (atoms : List Atom) :
    (atoms.map (renameTypeVars inner)).map
        (renameTypeVars outer) =
      atoms.map (renameTypeVars (outer ∘ inner)) := by
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
      right = left.map (renameTypeVars permutation) := by
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
          rightHead = renameTypeVars permutation leftHead := by
        rw [leftEquation, rightEquation, rename_comp]
        apply rename_congr_on_typeVars source
        intro name member
        exact (extensionLaw (Sum.inl (β := TailVariable)
          (⟨name, member⟩ : HeadVariable))).symm
      have globalTailEquation :
          rightTail =
            leftTail.map (renameTypeVars permutation) := by
        rw [tailEquation]
        apply renameList_congr_on_typeVars leftTail
        intro name member
        exact (extensionLaw (Sum.inr (α := HeadVariable)
          (⟨name, member⟩ : TailVariable))).symm
      exact ⟨permutation,
        congrArg₂ List.cons headEquation globalTailEquation⟩

/-! ## Complete argument-fold theory -/

/-- The complete solution theory of the ordered presentation fold, stated in
the spec lane so equivariance does not depend on a runtime bridge module. -/
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
        Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
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
          (expected.map (renameTypeVars rename))
          (actual.map (renameTypeVars rename)) ↔
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
      Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
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
        (expected.map (renameTypeVars permutation))
        (actual.map (renameTypeVars permutation)) [] output) ↔
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
      (expected.map (renameTypeVars permutation))
      (actual.map (renameTypeVars permutation)) [] rightOutput)
    (returnType : Atom) :
    ObservedTypeAlphaRel
      (leftOutput.apply returnType)
      (rightOutput.apply (renameTypeVars permutation returnType)) := by
  let leftModel := presentedValuation leftOutput
  let rightModel := presentedValuation rightOutput
  let transportedLeftModel : String → Atom :=
    leftModel ∘ permutation.symm
  have leftNormal :=
    Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      leftDerivation TypeSubst.normal_empty
  have rightNormal :=
    Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
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
        (expected.map (renameTypeVars permutation))
        (actual.map (renameTypeVars permutation)) := by
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
        (expected.map (renameTypeVars permutation))
        (actual.map (renameTypeVars permutation)) :=
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
      (renameTypeVars permutation returnType)
  have transportedObservation :
      applyTypeValuation transportedLeftModel
          (renameTypeVars permutation returnType) =
        leftOutput.apply returnType := by
    rw [applyTypeValuation_renameTypeVars]
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
  simpa [TypeSubst.apply, renameTypeVars] using alpha

/-- Negative: alpha permutation cannot manufacture consistency between two
distinct closed type symbols. -/
theorem distinct_concrete_arguments_remain_inconsistent :
    ¬∃ output,
      PresentationArgumentListMatchRel
        [.symbol "A"] [.symbol "B"] [] output := by
  rw [presentationArgumentList_exists_iff]
  simp [CorePlusR2TypeConsistent, ReducedTypeConsistent,
    Atom.undefinedType, Atom.atomType]

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
