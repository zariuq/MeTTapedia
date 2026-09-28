import Mettapedia.Languages.Agda.Structural.AdministrativeFunctionality
import Mettapedia.Languages.Agda.Structural.AdministrativeInclusion
import Mettapedia.Languages.Agda.Structural.SpineStaticControls

/-!
# Controls for recursive administrative equality

The examples retain real ordered histories and use actual typed substitutions.
A variable argument changes to distinct beta-equal terms; a dependent result
code changes with it. Conditional equality at an unsupported annotation does
not mint a formation or context derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)

abbrev empty := (Telescope.RawContext.nil : RawContext 0)
abbrev domain := Statics.Boundary.domain
abbrev extended := Statics.Boundary.oneContext
abbrev expanded := Statics.app Statics.Boundary.identityTerm (Statics.universeTerm 0)
abbrev contracted := Statics.universeTerm (n := 0) 0

noncomputable def domainFormed : CoreDerivation (Statics.formed empty domain.code) :=
  includeCanonical (Statics.Boundary.universeFormed Statics.Derivation.empty 1)
noncomputable def expandedTyped : CoreDerivation (Statics.typed empty expanded domain.code) :=
  includeCanonical Statics.Boundary.redexTyped
noncomputable def contractedTyped : CoreDerivation (Statics.typed empty contracted domain.code) :=
  includeCanonical (Statics.Derivation.sort 0 Statics.Derivation.empty)

noncomputable def betaEqual : CoreDerivation (Statics.termEqual empty expanded contracted domain.code) :=
  includeCanonical (Statics.Derivation.beta (A := domain) (B := .noBind domain)
    (body := .bind (.var .zero))
    (Statics.Boundary.universeFormed Statics.Derivation.empty 1)
    (Statics.Boundary.universeFormed Statics.Boundary.oneContextFormed 1)
    (Statics.Derivation.variableTerm (Γ := extended) .zero Statics.Boundary.oneContextFormed)
    (Statics.Derivation.sort 0 Statics.Derivation.empty))

noncomputable def argumentImages : Statics.EqualSubstitution CoreDerivation extended empty
    (Statics.single expanded) (Statics.single contracted) :=
  Statics.EqualSubstitution.single administrativeOperations domainFormed expandedTyped contractedTyped betaEqual

noncomputable def newestTyped : CoreDerivation
    (Statics.typed extended (.var .zero) (Statics.universeType 1 1).code) :=
  includeCanonical (Statics.Derivation.variableTerm (Γ := extended) .zero Statics.Boundary.oneContextFormed)

def dependentBody : TypeBody 1 := .bind ⟨1, .var .zero⟩
def variableSpine : Spine (scope 1) := cons (apply (.var .zero)) nil

noncomputable def variableAction : Action extended (Statics.piType (Statics.universeType 1 1) dependentBody).code
    variableSpine (dependentBody.instantiate (.var .zero)).code :=
  Derivation.cons (A := Statics.universeType 1 1) (B := dependentBody) newestTyped
    (Derivation.nil extended (dependentBody.instantiate (.var .zero)).code)

/-- Both spines and the dependent output are computed by the actual fold. -/
noncomputable def changedArgumentSpines := Action.functionality variableAction argumentImages

theorem substituted_arguments_differ :
    bind (Statics.single expanded) variableSpine ≠ bind (Statics.single contracted) variableSpine := by
  intro same
  cases same

theorem dependent_output_codes_differ :
    bind (Statics.single expanded) (dependentBody.instantiate (.var .zero)).code ≠
      bind (Statics.single contracted) (dependentBody.instantiate (.var .zero)).code := by
  intro same
  cases same

noncomputable def administrativeVariable : CoreDerivation
    (Statics.typed extended (eliminate (.var .zero) nil) (Statics.universeType 1 1).code) :=
  Derivation.elimination newestTyped (Derivation.nil extended _)

noncomputable def changedAdministrativeHeads : CoreDerivation (Statics.termEqual empty
    (eliminate expanded nil) (eliminate contracted nil) domain.code) :=
  CoreDerivation.typingFunctionality administrativeVariable argumentImages

noncomputable def administrativeFormation : CoreDerivation
    (Statics.formed extended (el (set (levelClosed 1)) (eliminate (.var .zero) nil))) :=
  Derivation.core (.formation extended 1 (eliminate (.var .zero) nil))
    (consEvidence CoreDerivation administrativeVariable (noEvidence CoreDerivation))

noncomputable def changedAdministrativeType :=
  CoreDerivation.formationFunctionality administrativeFormation argumentImages

noncomputable def emptyAdministrativeEquality : CoreDerivation
    (Statics.termEqual empty (eliminate contracted nil) contracted domain.code) :=
  Derivation.emptyElimination contractedTyped

/-- An inherited rule recursively consumes a new administrative equality. -/
noncomputable def administrativeTypeEquality : CoreDerivation (Statics.typeEqual empty
    (el (set (levelClosed 1)) (eliminate contracted nil)) (el (set (levelClosed 1)) contracted)) :=
  Derivation.core (.typeEquality empty 1 (eliminate contracted nil) contracted)
    (consEvidence CoreDerivation emptyAdministrativeEquality (noEvidence CoreDerivation))

noncomputable def inputConverted : Action empty (el (set (levelClosed 1)) (eliminate contracted nil))
    nil (el (set (levelClosed 1)) contracted) :=
  Derivation.inputConversion administrativeTypeEquality (Derivation.nil empty _)

noncomputable def outputConverted : Action empty (el (set (levelClosed 1)) (eliminate contracted nil))
    nil (el (set (levelClosed 1)) contracted) :=
  Derivation.outputConversion (Derivation.nil empty _) administrativeTypeEquality

theorem conversion_changes_raw_codes :
    el (set (levelClosed 1)) (eliminate contracted nil) ≠ el (set (levelClosed 1)) contracted := by
  intro same
  cases same

theorem conversion_positions_remain_distinct : inputConverted ≠ outputConverted := by
  intro same
  have shapes := (IndexedPolynomial.Fix.roll.inj same).1
  cases shapes

noncomputable def firstAction := includePrior SpineStatics.Controls.firstAction
noncomputable def secondAction := includePrior SpineStatics.Controls.secondAction
noncomputable def functionTyped := includePrior SpineStatics.Controls.functionTyped

noncomputable def orderedNestedEquality := Derivation.nestedElimination functionTyped firstAction secondAction

noncomputable def consPrefixEquality := Derivation.appendCons
  (Derivation.append firstAction secondAction)

noncomputable def emptyPrefixEquality := Derivation.appendEmpty
  (Derivation.append (Derivation.nil SpineStatics.Controls.functionContext _) firstAction)

noncomputable def bothConversionEquality := Derivation.spineInputConversion
  (includePrior SpineStatics.Controls.domainEquality)
  (Derivation.spineOutputConversion (Derivation.spineRefl (Derivation.nil SpineStatics.Controls.functionContext _))
    (includePrior SpineStatics.Controls.domainEquality))

def nilAction : Action empty domain.code nil domain.code := Derivation.nil empty domain.code
def directEquality : SpineEq empty domain.code nil nil domain.code := Derivation.spineRefl nilAction
def symmetricEquality : SpineEq empty domain.code nil nil domain.code := Derivation.spineSymm directEquality

theorem reflexivity_and_symmetry_histories_differ : directEquality ≠ symmetricEquality := by
  intro same
  have shapes := (IndexedPolynomial.Fix.roll.inj same).1
  cases shapes

def firstThenSecond := Derivation.spineTrans directEquality symmetricEquality
def secondThenFirst := Derivation.spineTrans symmetricEquality directEquality

theorem repeated_premise_positions_remain_ordered : firstThenSecond ≠ secondThenFirst := by
  intro same
  have children := eq_of_heq (IndexedPolynomial.Fix.roll.inj same).2
  exact reflexivity_and_symmetry_histories_differ (congrFun children 0)

noncomputable def leftSubstitutedEquality := SpineEq.substitution directEquality empty
  (Telescope.identity (S := sig) .term 0)
  (Statics.TypedSubstitution.identity coreAlgebra (includeCanonical Statics.Derivation.empty))

noncomputable def renamedEquality := SpineEq.renaming directEquality extended
  (Telescope.RawRen.projection (S := sig) .term 0)
  (Telescope.RawRen.respects_projection empty domain.code)
  (includeCanonical Statics.Boundary.oneContextFormed)

theorem prior_distinct_histories_remain_distinct :
    includePrior SpineStatics.Controls.directNil ≠ includePrior SpineStatics.Controls.inputConvertedNil := by
  intro same
  exact SpineStatics.Controls.input_conversion_history_distinct (includePrior_injective same)

def unsupportedType : RawTy 0 := el (prop (levelClosed 1)) contracted

def unsupportedEquality : SpineEq empty unsupportedType nil nil unsupportedType :=
  Derivation.spineRefl (Derivation.nil empty unsupportedType)

theorem unsupported_type_unformed : ¬ Nonempty (CoreDerivation (Statics.formed empty unsupportedType)) := by
  rintro ⟨tree⟩
  have boundary := tree.formationView.boundary
  cases boundary

def malformedContext : RawContext 1 := empty.snoc unsupportedType

def malformedContextEquality : SpineEq malformedContext (Statics.universeType 1 0).code nil nil
    (Statics.universeType 1 0).code := Derivation.spineRefl (Derivation.nil malformedContext _)

theorem malformed_context_unformed : ¬ Nonempty (CoreDerivation (Statics.context malformedContext)) := by
  rintro ⟨tree⟩
  have formed := tree.lookupFormation .zero
  have boundary := formed.formationView.boundary
  cases boundary

theorem conditional_equality_does_not_supply_formation :
    Nonempty (SpineEq empty unsupportedType nil nil unsupportedType) ∧
      ¬ Nonempty (CoreDerivation (Statics.formed empty unsupportedType)) :=
  ⟨⟨unsupportedEquality⟩, unsupported_type_unformed⟩

theorem finite_annotation_mismatch_rejected
    (tree : CoreDerivation (Statics.typeEqual empty (Statics.universeType 0 0).code (Statics.universeType 0 1).code)) :
    False := by
  have levels := tree.typeEquality_levels
  cases levels

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Controls
