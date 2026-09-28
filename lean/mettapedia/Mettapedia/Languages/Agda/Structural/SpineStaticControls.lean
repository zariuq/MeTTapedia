import Mettapedia.Languages.Agda.Structural.SpineStatics
import Mettapedia.Languages.Agda.Structural.StaticBoundary

/-!
# Controls for the explicit-spine static extension

The canonical beta counterexample's administrative target acquires a typing
derivation through typed-head elimination. Ordered append and multiple
arguments retain actual intermediate types and recursive histories. Canonical
rules can consume new derivations from the same combined fixed point.

These controls do not prove general subject reduction. In particular, typed
equalities for administrative nodes and dependent endpoint conversion remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.SpineStatics.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)

noncomputable def universeTyped :
    CoreDerivation (Statics.typed (.nil : RawContext 0) (Statics.universeTerm 0)
      (Statics.universeType 0 1).code) :=
  includeCanonical (Statics.Derivation.sort 0 Statics.Derivation.empty)

/-- The exact target of the permanent canonical beta counterexample. -/
noncomputable def betaTargetTyped :
    CoreDerivation (Statics.typed (.nil : RawContext 0) (eliminate (Statics.universeTerm 0) nil)
      (Statics.universeType 0 1).code) :=
  Derivation.elimination universeTyped (Derivation.nil .nil _)

/-- Both typing histories and the actual structural beta step remain available. -/
noncomputable def repairedBetaExample :
    CoreDerivation (Statics.typed (.nil : RawContext 0)
      (Statics.app Statics.Boundary.identityTerm (Statics.universeTerm 0)) (Statics.universeType 0 1).code) ×
    Step (Statics.app Statics.Boundary.identityTerm (Statics.universeTerm 0))
      (eliminate (Statics.universeTerm 0) nil) ×
    CoreDerivation (Statics.typed (.nil : RawContext 0) (eliminate (Statics.universeTerm 0) nil)
      (Statics.universeType 0 1).code) :=
  ⟨includeCanonical Statics.Boundary.redexTyped, Statics.Boundary.betaStep, betaTargetTyped⟩

/-- The old absence theorem still holds for its original eighteen-rule family. -/
theorem canonical_boundary_preserved :
    ¬ Nonempty (Statics.Derivation (Statics.typed (.nil : RawContext 0)
      (eliminate (Statics.universeTerm 0) nil) (Statics.universeType 0 1).code)) :=
  Statics.Boundary.beta_intermediate_untypable

/-- A canonical rule consumes an extension-generated premise, without leaving the combined tree. -/
noncomputable def administrativeReflexivity :
    CoreDerivation (Statics.termEqual (.nil : RawContext 0)
      (eliminate (Statics.universeTerm 0) nil) (eliminate (Statics.universeTerm 0) nil)
      (Statics.universeType 0 1).code) :=
  Derivation.core (.reflexivity .nil _ _) (consEvidence CoreDerivation betaTargetTyped (noEvidence CoreDerivation))

def domain {n : Nat} : TypeParameter n := Statics.universeType n 1
def arrow {n : Nat} : TypeParameter n := Statics.piType domain (.noBind domain)
def doubleArrow {n : Nat} : TypeParameter n := Statics.piType domain (.noBind arrow)

def domainFormed {n : Nat} {Γ : RawContext n} (context : Statics.Derivation (Statics.context Γ)) :
    Statics.Derivation (Statics.formed Γ (domain (n := n)).code) :=
  Statics.Boundary.universeFormed context 1

def arrowFormed {n : Nat} {Γ : RawContext n} (context : Statics.Derivation (Statics.context Γ)) :
    Statics.Derivation (Statics.formed Γ (arrow (n := n)).code) :=
  Statics.Derivation.formation (Statics.Derivation.pi (A := domain) (B := .noBind domain)
    (domainFormed context) (domainFormed (Statics.Derivation.extend context (domainFormed context))))

def doubleArrowFormed {n : Nat} {Γ : RawContext n} (context : Statics.Derivation (Statics.context Γ)) :
    Statics.Derivation (Statics.formed Γ (doubleArrow (n := n)).code) :=
  Statics.Derivation.formation (Statics.Derivation.pi (A := domain) (B := .noBind arrow)
    (domainFormed context) (arrowFormed (Statics.Derivation.extend context (domainFormed context))))

def functionContext : RawContext 1 := .snoc .nil (doubleArrow (n := 0)).code
def functionContextFormed : Statics.Derivation (Statics.context functionContext) :=
  Statics.Derivation.extend Statics.Derivation.empty (doubleArrowFormed Statics.Derivation.empty)

noncomputable def functionTyped :
    CoreDerivation (Statics.typed functionContext (.var .zero) (doubleArrow (n := 1)).code) :=
  includeCanonical (Statics.Derivation.variableTerm (Γ := functionContext) .zero functionContextFormed)

def firstArgument : RawTm 1 := Statics.universeTerm 0
def secondArgument : RawTm 1 := eliminate firstArgument nil

noncomputable def firstArgumentTyped : CoreDerivation (Statics.typed functionContext firstArgument domain.code) :=
  includeCanonical (Statics.Derivation.sort 0 functionContextFormed)

noncomputable def secondArgumentTyped : CoreDerivation (Statics.typed functionContext secondArgument domain.code) :=
  Derivation.elimination firstArgumentTyped (Derivation.nil functionContext domain.code)

def firstSpine : Spine (scope 1) := cons (apply firstArgument) nil
def secondSpine : Spine (scope 1) := cons (apply secondArgument) nil
def twoArguments : Spine (scope 1) := cons (apply firstArgument) secondSpine

noncomputable def firstAction : Action functionContext doubleArrow.code firstSpine arrow.code :=
  Derivation.cons (A := domain) (B := .noBind arrow) firstArgumentTyped
    (Derivation.nil functionContext arrow.code)

noncomputable def secondAction : Action functionContext arrow.code secondSpine domain.code :=
  Derivation.cons (A := domain) (B := .noBind domain) secondArgumentTyped
    (Derivation.nil functionContext domain.code)

noncomputable def twoArgumentAction : Action functionContext doubleArrow.code twoArguments domain.code :=
  Derivation.cons (A := domain) (B := .noBind arrow) firstArgumentTyped secondAction

noncomputable def twoArgumentTyping :
    CoreDerivation (Statics.typed functionContext (eliminate (.var .zero) twoArguments) domain.code) :=
  Derivation.elimination functionTyped twoArgumentAction

/-- The first action's output is the actual input of the second action. -/
noncomputable def appendedAction :
    Action functionContext doubleArrow.code (append firstSpine secondSpine) domain.code :=
  Derivation.append firstAction secondAction

noncomputable def appendedTyping :
    CoreDerivation (Statics.typed functionContext (eliminate (.var .zero) (append firstSpine secondSpine)) domain.code) :=
  Derivation.elimination functionTyped appendedAction

noncomputable def nestedEliminationTyping :
    CoreDerivation (Statics.typed functionContext
      (eliminate (eliminate (.var .zero) firstSpine) secondSpine) domain.code) :=
  Derivation.elimination (Derivation.elimination functionTyped firstAction) secondAction

def appendStep : Step
    (eliminate (eliminate (.var .zero) firstSpine) secondSpine)
    (eliminate (.var .zero) (append firstSpine secondSpine)) :=
  .root (.eliminateAppend (.var .zero) firstSpine secondSpine)

theorem two_argument_order_visible :
    twoArguments ≠ cons (apply secondArgument) (cons (apply firstArgument) nil) := by
  intro same
  cases same

noncomputable def domainEquality : CoreDerivation (Statics.typeEqual functionContext domain.code domain.code) :=
  includeCanonical (Statics.Derivation.typeEquality (k := 2)
    (Statics.Derivation.reflexivity (Statics.Derivation.sort 1 functionContextFormed)))

def directNil : Action functionContext domain.code nil domain.code := Derivation.nil functionContext domain.code
noncomputable def inputConvertedNil : Action functionContext domain.code nil domain.code :=
  Derivation.inputConversion domainEquality directNil
noncomputable def outputConvertedNil : Action functionContext domain.code nil domain.code :=
  Derivation.outputConversion directNil domainEquality
noncomputable def bothConversions : Action functionContext domain.code nil domain.code :=
  Derivation.outputConversion inputConvertedNil domainEquality

theorem input_conversion_history_distinct : directNil ≠ inputConvertedNil := by
  intro same
  have shape := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll.inj same).1
  cases shape

theorem input_output_history_distinct : inputConvertedNil ≠ outputConvertedNil := by
  intro same
  have shape := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll.inj same).1
  cases shape

def convertibleInput : TypeParameter 0 :=
  ⟨1, Statics.app Statics.Boundary.identityTerm (Statics.universeTerm 0)⟩
def convertibleOutput : TypeParameter 0 := Statics.universeType 0 0

/-- A beta-derived type equality changes the actual code, rather than only its evidence. -/
noncomputable def nontrivialTypeEquality :
    CoreDerivation (Statics.typeEqual (.nil : RawContext 0) convertibleInput.code convertibleOutput.code) :=
  includeCanonical (Statics.Derivation.typeEquality (k := 1)
    (Statics.Derivation.beta (A := Statics.Boundary.domain) (B := .noBind Statics.Boundary.domain)
      (body := .bind (.var .zero))
      (Statics.Boundary.universeFormed Statics.Derivation.empty 1)
      (Statics.Boundary.universeFormed Statics.Boundary.oneContextFormed 1)
      (Statics.Derivation.variableTerm (Γ := Statics.Boundary.oneContext) .zero Statics.Boundary.oneContextFormed)
      (Statics.Derivation.sort 0 Statics.Derivation.empty)))

noncomputable def changedInputAction :
    Action (.nil : RawContext 0) convertibleInput.code nil convertibleOutput.code :=
  Derivation.inputConversion nontrivialTypeEquality (Derivation.nil .nil convertibleOutput.code)

noncomputable def changedOutputAction :
    Action (.nil : RawContext 0) convertibleInput.code nil convertibleOutput.code :=
  Derivation.outputConversion (Derivation.nil .nil convertibleInput.code) nontrivialTypeEquality

theorem conversion_changes_code : convertibleInput.code ≠ convertibleOutput.code := by
  intro same
  cases same

theorem changed_conversion_histories_distinct : changedInputAction ≠ changedOutputAction := by
  intro same
  have shape := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll.inj same).1
  cases shape

noncomputable def appendDirectConverted : Action functionContext domain.code (append nil nil) domain.code :=
  Derivation.append directNil inputConvertedNil
noncomputable def appendConvertedDirect : Action functionContext domain.code (append nil nil) domain.code :=
  Derivation.append inputConvertedNil directNil

/-- Even repeated equal judgments retain the two different child addresses. -/
theorem append_child_order_retained : appendDirectConverted ≠ appendConvertedDirect := by
  intro same
  exact input_conversion_history_distinct (append_injective same).1

noncomputable def directElimination :
    CoreDerivation (Statics.typed functionContext secondArgument domain.code) :=
  Derivation.elimination firstArgumentTyped directNil
noncomputable def convertedElimination :
    CoreDerivation (Statics.typed functionContext secondArgument domain.code) :=
  Derivation.elimination firstArgumentTyped bothConversions

theorem elimination_history_retained : directElimination ≠ convertedElimination := by
  intro same
  have action := (elimination_injective same).2
  have shape := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll.inj action).1
  cases shape

/-- Elimination requires two ordered children; the nil action cannot delete the head. -/
theorem elimination_premises_exact {n : Nat} (Γ : RawContext n) (head : RawTm n)
    (A : RawTy n) (spine : Spine (scope n)) (B : RawTy n) :
    premises (.elimination Γ head A spine B) =
      [.core (Statics.typed Γ head A), .spineAction Γ A spine B] := rfl

theorem elimination_children_recover {n : Nat} (Γ : RawContext n) (head : RawTm n)
    (A : RawTy n) (spine : Spine (scope n)) (B : RawTy n)
    (children : Evidence Derivation (premises (.elimination Γ head A spine B))) :
    (eliminationEvidenceEquiv Γ head A spine B).symm
      (eliminationEvidenceEquiv Γ head A spine B children) = children :=
  (eliminationEvidenceEquiv Γ head A spine B).left_inv children

theorem nil_action_has_no_canonical_origin {n : Nat} (Γ : RawContext n) (A : RawTy n) :
    usesCanonical (Derivation.nil Γ A) = false := usesCanonical_nil Γ A

/-- Every actual typing tree needs more than conditional spine rules alone. -/
theorem no_typing_from_spine_only {n : Nat} {Γ : RawContext n} {term : RawTm n} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ term A)) : usesCanonical tree ≠ false := by
  intro absent
  have present := usesCanonical_of_typing tree rfl
  rw [present] at absent
  cases absent

end Mettapedia.Languages.Agda.Structural.SpineStatics.Controls
