import Mettapedia.Languages.Agda.Structural.StaticAdmission

/-!
# Dependent controls for admission by structural typing derivations

The source telescope is `X : Set 1, x : X`. The target is `z : Set 0`.
An actual typed substitution sends `X` to `Set 0` and `x` to `z`, changing
the dependent type code. The negative controls reject an unsupported literal
image and retain different typing histories for the same admitted term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics.AdmissionControls

open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory

def empty : RawContext 0 := .nil
def sourceOne : RawContext 1 := empty.snoc (universeType 0 1).code
def target : RawContext 1 := empty.snoc (universeType 0 0).code
def dependentType : RawTy 1 := (TypeParameter.mk (n := 1) 1 (.var .zero)).code
def sourceTwo : RawContext 2 := sourceOne.snoc dependentType

def universeFormed {n : Nat} {Γ : RawContext n} (d : Derivation (context Γ)) (k : Nat) :
    Derivation (formed Γ (universeType n k).code) := Derivation.formation (Derivation.sort k d)

def sourceOneFormed : Derivation (context sourceOne) :=
  Derivation.extend Derivation.empty (universeFormed Derivation.empty 1)
def targetFormed : Derivation (context target) :=
  Derivation.extend Derivation.empty (universeFormed Derivation.empty 0)
def dependentFormed : Derivation (formed sourceOne dependentType) :=
  Derivation.formation (Derivation.variableTerm (Γ := sourceOne) .zero sourceOneFormed)
def sourceTwoFormed : Derivation (context sourceTwo) :=
  Derivation.extend sourceOneFormed dependentFormed

def typesSub : RawSub 1 1 :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 1) (universeTerm 0)

def elementsSub : RawSub 2 1 := Telescope.pair typesSub (.var .zero)

noncomputable def typesSubTyped : TypedSubstitution Derivation sourceOne target typesSub :=
  TypedSubstitution.pair (IndexedPolynomial.Algebra.initial presentation.polynomial)
    (TypedSubstitution.empty (IndexedPolynomial.Algebra.initial presentation.polynomial) targetFormed)
    (universeFormed Derivation.empty 1) (Derivation.sort 0 targetFormed)

noncomputable def elementsSubTyped : TypedSubstitution Derivation sourceTwo target elementsSub :=
  TypedSubstitution.pair (IndexedPolynomial.Algebra.initial presentation.polynomial) typesSubTyped
    dependentFormed (Derivation.variableTerm (Γ := target) .zero targetFormed)

theorem dependent_type_changes : bind typesSub dependentType = (universeType 1 0).code := rfl

theorem dependent_type_does_not_stay_variable : bind typesSub dependentType ≠ dependentType := by
  intro equality
  cases equality

theorem type_component : elementsSub .term (.succ .zero) = universeTerm 0 := rfl
theorem element_component : elementsSub .term .zero = .var .zero := rfl
theorem components_differ : elementsSub .term (.succ .zero) ≠ elementsSub .term .zero := by
  intro equality
  cases equality

noncomputable def transportedDependentType : Derivation (formed target (universeType 1 0).code) :=
  Derivation.substitution dependentFormed target typesSub typesSubTyped

noncomputable def transportedElement : Derivation (typed target (.var .zero) (universeType 1 0).code) :=
  Derivation.substitution (Derivation.variableTerm (Γ := sourceTwo) .zero sourceTwoFormed) target elementsSub elementsSubTyped

noncomputable def sourceContext : canonicalAdmission.Context := ⟨⟨2, sourceTwo⟩, ⟨sourceTwoFormed⟩⟩
noncomputable def targetContext : canonicalAdmission.Context := ⟨⟨1, target⟩, ⟨targetFormed⟩⟩
noncomputable def admittedSub : canonicalAdmission.Substitution targetContext sourceContext :=
  ⟨elementsSub, ⟨elementsSubTyped⟩⟩

theorem admitted_substitution_keeps_raw_components : admittedSub.val = elementsSub := rfl

noncomputable def targetType : canonicalAdmission.TypeOver targetContext :=
  ⟨(universeType 1 0).code, ⟨universeFormed targetFormed 0⟩⟩

def variableTyping : Derivation (typed target (.var .zero) (universeType 1 0).code) :=
  Derivation.variableTerm (Γ := target) .zero targetFormed

def variableTypingWithConversion : Derivation (typed target (.var .zero) (universeType 1 0).code) :=
  Derivation.conversion variableTyping
    (Derivation.typeEquality (Derivation.reflexivity (Derivation.sort 0 targetFormed)))

theorem different_typing_histories : variableTyping ≠ variableTypingWithConversion := by
  intro same
  unfold variableTypingWithConversion variableTyping Derivation.variableTerm Derivation.conversion at same
  have root := (IndexedPolynomial.Fix.roll.inj same).1
  cases root

theorem retained_histories_differ :
    canonicalAdmission.retainTerm (Γ := targetContext) (A := targetType) variableTyping ≠
      canonicalAdmission.retainTerm (Γ := targetContext) (A := targetType) variableTypingWithConversion := by
  intro same
  exact different_typing_histories (canonicalAdmission.retainTerm_injective same)

theorem supported_terms_agree :
    (canonicalAdmission.retainTerm (Γ := targetContext) (A := targetType) variableTyping).1 =
      (canonicalAdmission.retainTerm (Γ := targetContext) (A := targetType) variableTypingWithConversion).1 := rfl

private def isLiteral {n : Nat} (term : RawTm n) : Bool :=
  match term with
  | .op (.natLiteral _) _ => true
  | _ => false

private def excludesLiterals : Judgment → Prop
  | .term _ _ term => isLiteral term.code = false
  | _ => True

private theorem literal_invariant (j : Judgment) (tree : Derivation j) : excludesLiterals j := by
  apply least excludesLiterals (fun _ _ shape ih => ?_) j tree
  cases shape with
  | empty | extend | formation | typeEquality | reflexivity | symmetry | transitivity
    | equalityConversion | piCongruence | applicationCongruence | beta | eta => trivial
  | sort | «variable» | application => rfl
  | pi Γ A B => cases B <;> rfl
  | lambda Γ A B body => cases body <;> rfl
  | conversion Γ t A B => exact ih ⟨0, by change 0 < 2; decide⟩

def wrongImage : RawSub 1 1 :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 1) (natLiteral 0)

/-- A raw substitution cannot enter the admitted category merely by being scoped. -/
theorem wrong_image_not_admitted : ¬ Nonempty (TypedSubstitution Derivation sourceOne target wrongImage) := by
  rintro ⟨evidence⟩
  have impossible := literal_invariant _ (evidence.image .zero)
  cases impossible

end Mettapedia.Languages.Agda.Structural.Statics.AdmissionControls
