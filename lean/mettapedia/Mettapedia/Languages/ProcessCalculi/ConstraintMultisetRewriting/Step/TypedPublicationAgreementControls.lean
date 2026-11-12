import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SyntacticShadow
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongReflection

/-!
# Raw output typing can distinguish agreeing typed substitutions

At Ground -> Ground, identity agrees with an expansion which evaluates
`g x` and discards the result. Identity can also be checked at U0 -> U0.
The expansion cannot: its additional call applies g to a universe-valued
argument. Both substitutions are typed at their declared source context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationAgreementControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentEtaLong
open DependentFull.Controls (setting ground arrow ground_typed arrow_typed smallUniverse)

abbrev levels : LevelModel Tower.rules Nat := setting.levels

def arrowType (Γ : Context Tower.rules) : TypeOver Γ :=
  ⟨arrow, .sort Tower.zero, .sort _, arrow_typed _⟩

abbrev scope := extend (empty Tower.rules) (arrowType (empty Tower.rules))
abbrev wideContext := extend scope (smallUniverse scope)

def univ {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)
def wide {n : Nat} : Tower.Tm n := .pi univ univ

theorem wide_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ wide (.head (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

def wideType (Γ : Context Tower.rules) : TypeOver Γ :=
  ⟨wide, .sort (.max (.succ Tower.zero) (.succ Tower.zero)), .sort _, wide_typed _⟩

def identityCode : Tower.Tm 1 := .lam (.var 0)
def expandedCode : Tower.Tm 1 :=
  .lam (.app (.lam (.var 1)) (.app (.var 1) (.var 0)))

theorem identity_typed : Typed Tower.rules scope.raw identityCode arrow :=
  .lamIntro (arrow_typed _) (.sort _) (Derivable.var 0)

theorem extra_call_typed :
    Typed Tower.rules (.snoc scope.raw ground) (.app (.var 1) (.var 0)) ground :=
  Derivable.appElim (A := ground) (B := ground) (Derivable.var 1) (Derivable.var 0)

theorem expanded_typed : Typed Tower.rules scope.raw expandedCode arrow := by
  apply Derivable.lamIntro (arrow_typed _) (.sort _)
  exact .appElim (.lamIntro (arrow_typed _) (.sort _) (Derivable.var 1))
    extra_call_typed

theorem expanded_equals_identity : Equal Tower.rules scope.raw expandedCode identityCode arrow := by
  apply Derivable.lamCong (arrow_typed _) (.sort _)
  exact .betaPi (arrow_typed _) (.sort _) (Derivable.var 1)
    extra_call_typed

def identityReading : scope ⟶ scope :=
  pair (toEmpty scope) ⟨identityCode, identity_typed⟩

def expandedReading : scope ⟶ scope :=
  pair (toEmpty scope) ⟨expandedCode, expanded_typed⟩

theorem readings_agree : UnificationWithLevels.Agree (frames levels) identityReading expandedReading := by
  have pointwise : SubstEq Tower.rules scope.raw scope.raw
      identityReading.substitution expandedReading.substitution := by
    refine ⟨identityReading.typed, ?_⟩
    intro index
    fin_cases index
    exact expanded_equals_identity.symm
  exact act_equal_of_substEq (S := setting) pointwise

theorem universe_not_below_ground {n : Nat} {Γ : Tower.Ctx n}
    (formed : CtxFormed Tower.rules Γ) : ¬ TypeLe Tower.rules Γ univ ground := by
  intro below
  have typeGround : IsType Tower.rules Γ ground := ⟨.sort Tower.zero, .sort _, ground_typed _⟩
  have typeUniverse : IsType Tower.rules Γ univ :=
    ⟨.sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩
  obtain ⟨head, isUniverse, equal, _⟩ := Below.universe_source (S := setting) TowerModel.facts
    (TypeLe.toBelow below typeGround) formed (.sort Tower.zero) typeUniverse.refl
  cases head with
  | legacyGround => cases isUniverse
  | sort level =>
      have same := TypeEq.head_injective TowerModel.facts equal formed
      change (LevelTower.Head.legacyGround : Tower.Head) = .sort level ∨ False at same
      rcases same with impossible | impossible
      · cases impossible
      · exact impossible

theorem extra_call_not_typable {result : Tower.Tm 2} :
    ¬ Typed Tower.rules wideContext.raw (.app (.var 1) (.var 0)) result := by
  intro typed
  obtain ⟨domain, codomain, functionTyped, argumentTyped, _⟩ := typed.generation
  have functionLe := functionTyped.generation
  change TypeLe Tower.rules wideContext.raw arrow (.pi domain codomain) at functionLe
  have domains := (TypeLe.pi_parts (S := setting) TowerModel.facts functionLe
    (Typed.isType functionTyped wideContext.formed) wideContext.formed).1
  have argumentGround := Typed.convType argumentTyped domains.symm
  have below := argumentGround.generation
  change TypeLe Tower.rules wideContext.raw univ ground at below
  exact universe_not_below_ground wideContext.formed below

def requestedRow : DependentFull.Make scope := ⟨wideType scope, .var 0⟩

theorem identity_reading_types_requested_row : (requestedRow.reindex identityReading).WellTyped :=
  .lamIntro (wide_typed _) (.sort _) (Derivable.var 0)

theorem expanded_reading_does_not_type_requested_row :
    ¬ (requestedRow.reindex expandedReading).WellTyped := by
  intro typed
  change Typed Tower.rules scope.raw expandedCode wide at typed
  have body := Typed.lam_inv (S := setting) TowerModel.facts typed scope.formed
  obtain ⟨domain, codomain, _, argumentTyped, _⟩ := body.generation
  exact extra_call_not_typable argumentTyped

/-- Both substitutions solve the same empty information and agree on all
judged terms, while the raw output-typing request separates them. -/
theorem typing_not_closed_under_agreement :
    ¬ NativeTypesOnTheStep.ClosedUnderAgreement levels [] requestedRow := by
  intro closed
  exact expanded_reading_does_not_type_requested_row
    (closed scope expandedReading identityReading (Frames.models_nil _)
      readings_agree.symm identity_reading_types_requested_row)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationAgreementControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationAgreementControls.readings_agree
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationAgreementControls.expanded_reading_does_not_type_requested_row
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublicationAgreementControls.typing_not_closed_under_agreement
