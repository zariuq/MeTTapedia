import Mettapedia.Languages.Agda.Structural.SpineAdmission
import Mettapedia.Languages.Agda.Structural.SpineStaticControls
import Mettapedia.Languages.Agda.Structural.StaticAdmissionControls

/-!
# Controls for admission by combined static trees

Weakening shifts the free function variable without capturing it. A typed
substitution replaces that variable with its administrative elimination,
reindexing a two-argument derivation from the combined family. A dependent
substitution changes a type annotation and supplies an administrative term
as its newest image. The admitted syntax keeps those actual terms, while
companion receipts still distinguish different conversion histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics.AdmissionControls

open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawSub RawContext)

noncomputable def functionContextFormed : CoreDerivation (Statics.context Controls.functionContext) :=
  includeCanonical Controls.functionContextFormed

def weakenedContext : RawContext 2 := Controls.functionContext.snoc Controls.domain.code

noncomputable def weakenedContextFormed : CoreDerivation (Statics.context weakenedContext) :=
  includeCanonical (Statics.Derivation.extend Controls.functionContextFormed
    (Controls.domainFormed Controls.functionContextFormed))

/-- The reindexed result has the older function variable, with both arguments retained. -/
noncomputable def weakenedTwoArgumentTyping :
    CoreDerivation (Statics.typed weakenedContext
      (eliminate (.var (.succ .zero))
        (cons (apply (Statics.universeTerm 0))
          (cons (apply (eliminate (Statics.universeTerm 0) nil)) nil))) Controls.domain.code) :=
  CoreDerivation.renaming Controls.twoArgumentTyping weakenedContext
    (Telescope.RawRen.projection (S := sig) .term 1)
    (Telescope.RawRen.respects_projection Controls.functionContext Controls.domain.code)
    weakenedContextFormed

theorem weakened_head_is_not_captured :
    (Term.var (.succ .zero) : RawTm 2) ≠ .var .zero := by
  intro same
  cases same

def administrativeFunction : RawTm 1 := eliminate (.var .zero) nil

noncomputable def administrativeFunctionTyped :
    CoreDerivation (Statics.typed Controls.functionContext administrativeFunction Controls.doubleArrow.code) :=
  Derivation.elimination Controls.functionTyped
    (Derivation.nil Controls.functionContext Controls.doubleArrow.code)

def administrativeSub : RawSub 1 1 :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 1) administrativeFunction

noncomputable def administrativeSubTyped :
    TypedSubstitution Controls.functionContext Controls.functionContext administrativeSub :=
  Statics.TypedSubstitution.pair coreAlgebra
    (Statics.TypedSubstitution.empty coreAlgebra functionContextFormed)
    (includeCanonical (Controls.doubleArrowFormed Statics.Derivation.empty))
    administrativeFunctionTyped

theorem administrative_substitution_is_not_a_renaming (ρ : Statics.RawRen 1 1) :
    administrativeSub ≠ ρ.asSub := by
  intro same
  have atVariable := congrFun (congrFun same .term) .zero
  cases atVariable

/-- Both application premises are recursively substituted in the combined tree. -/
noncomputable def substitutedTwoArgumentTyping :
    CoreDerivation (Statics.typed Controls.functionContext
      (eliminate administrativeFunction Controls.twoArguments) Controls.domain.code) :=
  CoreDerivation.substitution Controls.twoArgumentTyping Controls.functionContext
    administrativeSub administrativeSubTyped

theorem substituted_conversion_histories_differ :
    Action.substitution Controls.inputConvertedNil Controls.functionContext administrativeSub administrativeSubTyped ≠
      Action.substitution Controls.outputConvertedNil Controls.functionContext administrativeSub administrativeSubTyped := by
  rw [Controls.inputConvertedNil, Controls.outputConvertedNil,
    substitution_inputConversion, substitution_outputConversion]
  intro same
  have shape := (IndexedPolynomial.Fix.roll.inj same).1
  cases shape

noncomputable def functionContext : spineAdmission.Context :=
  ⟨⟨1, Controls.functionContext⟩, ⟨functionContextFormed⟩⟩

noncomputable def functionDomain : spineAdmission.TypeOver functionContext :=
  ⟨Controls.domain.code, ⟨includeCanonical (Controls.domainFormed Controls.functionContextFormed)⟩⟩

noncomputable def administrativeTerm : spineAdmission.Term functionContext functionDomain :=
  ⟨⟨Controls.secondArgument⟩, ⟨Controls.directElimination⟩⟩

theorem admitted_administrative_term_keeps_raw_syntax :
    administrativeTerm.val.code = eliminate (Statics.universeTerm 0) nil := rfl

theorem retained_administrative_histories_differ :
    spineAdmission.retainTerm (Γ := functionContext) (A := functionDomain) Controls.directElimination ≠
      spineAdmission.retainTerm (Γ := functionContext) (A := functionDomain) Controls.convertedElimination := by
  intro same
  exact Controls.elimination_history_retained (spineAdmission.retainTerm_injective same)

theorem supported_administrative_terms_agree :
    (spineAdmission.retainTerm (Γ := functionContext) (A := functionDomain) Controls.directElimination).1 =
      (spineAdmission.retainTerm (Γ := functionContext) (A := functionDomain) Controls.convertedElimination).1 := rfl

namespace Dependent

open Statics.AdmissionControls (sourceOne sourceTwo target dependentType typesSub
  sourceOneFormed sourceTwoFormed targetFormed dependentFormed universeFormed)

noncomputable def typesSubTyped : TypedSubstitution sourceOne target typesSub :=
  Statics.TypedSubstitution.pair coreAlgebra
    (Statics.TypedSubstitution.empty coreAlgebra (includeCanonical targetFormed))
    (includeCanonical (universeFormed Statics.Derivation.empty 1))
    (includeCanonical (Statics.Derivation.sort 0 targetFormed))

def administrativeElement : RawTm 1 := eliminate (.var .zero) nil

noncomputable def administrativeElementTyped :
    CoreDerivation (Statics.typed target administrativeElement (Statics.universeType 1 0).code) :=
  Derivation.elimination
    (includeCanonical (Statics.Derivation.variableTerm (Γ := target) .zero targetFormed))
    (Derivation.nil target (Statics.universeType 1 0).code)

def elementsSub : RawSub 2 1 := Telescope.pair typesSub administrativeElement

noncomputable def elementsSubTyped : TypedSubstitution sourceTwo target elementsSub :=
  Statics.TypedSubstitution.pair coreAlgebra typesSubTyped
    (includeCanonical dependentFormed) administrativeElementTyped

theorem dependent_type_changes : bind typesSub dependentType = (Statics.universeType 1 0).code := rfl

theorem dependent_type_does_not_stay_variable : bind typesSub dependentType ≠ dependentType := by
  intro same
  cases same

theorem type_component : elementsSub .term (.succ .zero) = Statics.universeTerm 0 := rfl
theorem element_component : elementsSub .term .zero = administrativeElement := rfl

noncomputable def transportedElement :
    CoreDerivation (Statics.typed target administrativeElement (Statics.universeType 1 0).code) :=
  CoreDerivation.substitution
    (includeCanonical (Statics.Derivation.variableTerm (Γ := sourceTwo) .zero sourceTwoFormed))
    target elementsSub elementsSubTyped

noncomputable def sourceContext : spineAdmission.Context :=
  ⟨⟨2, sourceTwo⟩, ⟨includeCanonical sourceTwoFormed⟩⟩
noncomputable def targetContext : spineAdmission.Context :=
  ⟨⟨1, target⟩, ⟨includeCanonical targetFormed⟩⟩

noncomputable def admittedSub : spineAdmission.Substitution targetContext sourceContext :=
  ⟨elementsSub, ⟨elementsSubTyped⟩⟩

theorem admitted_substitution_keeps_dependent_components : admittedSub.val = elementsSub := rfl

end Dependent

private def isLiteral {n : Nat} (term : RawTm n) : Bool :=
  match term with
  | .op (.natLiteral _) _ => true
  | _ => false

private def excludesLiterals : CombinedJudgment → Prop
  | .core (.term _ _ term) => isLiteral term.code = false
  | _ => True

private theorem literal_invariant (j : CombinedJudgment) (tree : Derivation j) : excludesLiterals j := by
  apply least excludesLiterals (fun _ _ shape ih => ?_) j tree
  cases shape with
  | core shape =>
      cases shape with
      | empty | extend | formation | typeEquality | reflexivity | symmetry | transitivity
        | equalityConversion | piCongruence | applicationCongruence | beta | eta => trivial
      | sort | «variable» | application => rfl
      | pi Γ A B => cases B <;> rfl
      | lambda Γ A B body => cases body <;> rfl
      | conversion Γ t A B => exact ih ⟨0, by change 0 < 2; decide⟩
  | nil | cons | append | inputConversion | outputConversion => trivial
  | elimination => rfl

/-- Even the combined admission requires a typing tree for every raw image. -/
theorem literal_image_not_admitted :
    ¬ Nonempty (TypedSubstitution Statics.AdmissionControls.sourceOne
      Statics.AdmissionControls.target Statics.AdmissionControls.wrongImage) := by
  rintro ⟨evidence⟩
  have impossible := literal_invariant _ (evidence.image .zero)
  cases impossible

end Mettapedia.Languages.Agda.Structural.SpineStatics.AdmissionControls
