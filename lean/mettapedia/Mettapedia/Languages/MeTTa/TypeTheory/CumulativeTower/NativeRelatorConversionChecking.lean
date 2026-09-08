import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorRootConversionCode
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeConversionChecking

/-!
# Checked conversion for the unchanged native List/identity/relator package

All five authored roots use the existing structural finite-code checker,
including beta, head conversion, scoped congruence, symmetry and composition.
Every raw open conversion has a code and every accepted code denotes that
conversion. This checks a supplied finite code; it does not find one.

Logical use retains independent source admission and target formation via
`Judgment.convertChecked`. Neither root exactness nor conversion checking
establishes preservation of the eliminators' typing rules. No declaration or
computation package is changed or combined with MIL here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionChecking

open Presentation StructuralConversionCode NativeIndexedFamilies

variable {n : Nat}

abbrev Code (n : Nat) :=
  StructuralConversionCode.Code Tower.Head NativeRelatorRootConversionCode.Code n

abbrev StepCode (n : Nat) :=
  StructuralConversionCode.StepCode Tower.Head NativeRelatorRootConversionCode.Code n

def check (code : Code n) (left right : Tower.Tm n) : Bool :=
  code.check Tower.HeadEq NativeRelatorRootConversionCode.decode left right

def checkStep (code : StepCode n) (left right : Tower.Tm n) : Bool :=
  code.check Tower.HeadEq NativeRelatorRootConversionCode.decode left right

theorem check_sound {code : Code n} {left right : Tower.Tm n}
    (checked : check code left right = true) :
    Conv IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation :=
  StructuralConversionCode.Code.check_sound (headEq := Tower.HeadEq)
    NativeRelatorRootConversionCode.rootDecoder checked

theorem conversion_iff_checked {left right : Tower.Tm n} :
    Conv IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation ↔
      ∃ code : Code n, check code left right = true :=
  StructuralConversionCode.Code.conversion_iff_checked (headEq := Tower.HeadEq)
    NativeRelatorRootConversionCode.rootDecoder

theorem step_iff_checked {left right : Tower.Tm n} :
    StepCore IntrinsicRelator.rules.computation IntrinsicRelator.rules.headEq left right ↔
      ∃ code : StepCode n, checkStep code left right = true :=
  StructuralConversionCode.StepCode.step_iff_checked (headEq := Tower.HeadEq)
    NativeRelatorRootConversionCode.rootDecoder

/-- Source admission and target formation are separate proof inputs, never
fields of the executable raw conversion code. -/
theorem convertChecked {context : Tower.Ctx n} {term sourceType targetType : Tower.Tm n}
    {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicRelator.rules context term sourceType)
    (targetFormed : FormationSensitive.Typing IntrinsicRelator.rules context targetType (.head sortHead))
    (isUniverse : IntrinsicRelator.rules.isUniverse sortHead)
    {code : Code n} (checked : check code sourceType targetType = true) :
    FormationSensitive.Judgment IntrinsicRelator.rules context term targetType := by
  letI : DecidableRel IntrinsicRelator.rules.headEq := Tower.instDecidableHeadEq
  exact source.convertChecked NativeRelatorRootConversionCode.rootDecoder
    targetFormed isUniverse checked

namespace Examples

def relConsStep : StepCode 12 := .root NativeRelatorRootConversionCode.Examples.relConsCode

theorem relator_step_checked :
    checkStep relConsStep IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaRight = true := by decide

/-- The outer code has eleven variables and the retained root beneath its
lambda has twelve. The original open cons schema is checked literally. -/
theorem relational_root_beneath_binder_checked :
    check (.single (.congLam relConsStep))
      (.lam IntrinsicRelator.consIotaLeft) (.lam IntrinsicRelator.consIotaRight) = true := by decide

theorem symmetric_relator_conversion_checked :
    check (.symm (.single relConsStep)) IntrinsicRelator.consIotaRight
      IntrinsicRelator.consIotaLeft = true := by decide

def beneathBinder : StepCode 1 := .congLam (.betaPi (.var 2) (.var 0))

def beneathBinderSource : Tower.Tm 1 := .lam (.app (.lam (.var 2)) (.var 0))

theorem beta_beneath_binder_checked :
    check (.single beneathBinder) beneathBinderSource (.lam (.var 1)) = true := by decide

theorem variable_capture_rejected :
    check (.single beneathBinder) beneathBinderSource (.lam (.var 0)) = false := by decide

def firstHead : Tower.Head := .sort (.max (.param 0) (.const 0))
def secondHead : Tower.Head := .sort (.param 0)

def brokenJoin : Code 0 := .trans (.refl (.head firstHead)) (.refl (.head secondHead))

def repairedJoin : Code 0 :=
  .trans (.refl (.head firstHead))
    (.trans (.single (.head firstHead secondHead)) (.refl (.head secondHead)))

/-- Refusing a malformed path does not refute conversion of its endpoints. -/
theorem explicit_bridge_repairs_join :
    check brokenJoin (.head firstHead) (.head secondHead) = false ∧
    check repairedJoin (.head firstHead) (.head secondHead) = true := by decide

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def betaArgument {n : Nat} (argument : Tower.Tm n) : Tower.Tm n :=
  .app (.lam (.var 0)) argument

theorem ground_formed {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing IntrinsicRelator.rules context ground (sortTm Tower.zero) :=
  .headType .legacyGround

theorem betaArgument_typed {n : Nat} {context : Tower.Ctx n} {argument : Tower.Tm n}
    (typed : FormationSensitive.Typing IntrinsicRelator.rules context argument ground) :
    FormationSensitive.Typing IntrinsicRelator.rules context (betaArgument argument) ground := by
  have functionTyped : FormationSensitive.Typing IntrinsicRelator.rules context
      (.lam (.var 0)) (.pi ground ground) :=
    .lamIntro (.piForm (ground_formed _) (.sort _) (ground_formed _) (.sort _) (.sorts _ _))
      (.sort _) (.var 0)
  simpa only [betaArgument, ground, inst0, subst] using
    FormationSensitive.Typing.appElim functionTyped typed

def identityExpansionCode {n : Nat} (argument : Tower.Tm n) : Code n :=
  .symm (.trans
    (.single (.congIdLeft ground (.betaPi (.var 0) argument) (betaArgument argument)))
    (.single (.congIdRight ground argument (.betaPi (.var 0) argument))))

theorem identity_expansion_checked {n : Nat} (argument : Tower.Tm n) :
    check (identityExpansionCode argument) (.id ground argument argument)
      (.id ground (betaArgument argument) (betaArgument argument)) = true := by
  simp [check, identityExpansionCode, StructuralConversionCode.Code.check,
    StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode,
    mapEndpoints, reverseEndpoints, joinEndpoints, betaArgument, inst0, subst]

/-- A checked nontrivial change of a dependent displayed type retains an
independently admitted term and independently formed endpoint expressions. -/
theorem checked_dependent_identity_admission {n : Nat} {context : Tower.Ctx n}
    {argument : Tower.Tm n}
    (source : FormationSensitive.Judgment IntrinsicRelator.rules context argument ground) :
    FormationSensitive.Judgment IntrinsicRelator.rules context (.refl argument)
      (.id ground (betaArgument argument) (betaArgument argument)) := by
  exact convertChecked ⟨source.context, .reflIntro source.typing⟩
    (.idForm (ground_formed _) (.sort _) (betaArgument_typed source.typing)
      (betaArgument_typed source.typing)) (.sort _) (identity_expansion_checked argument)

def missingName : DeclName := `Prime.List.mapRel.missingConversionEvidence

theorem conversion_does_not_supply_formation :
    check (.refl (.const missingName) : Code 0) (.const missingName) (.const missingName) = true ∧
    ¬ ∃ type : Tower.Tm 0,
      FormationSensitive.Judgment IntrinsicRelator.rules .nil (.const missingName) type := by
  constructor
  · decide
  · rintro ⟨type, judgment⟩
    obtain ⟨declaredType, sortHead, known, _, _⟩ := judgment.typing.constFormation
    have absent : IntrinsicRelator.rules.constantType missingName = none := by decide
    rw [absent] at known
    cases known

end Examples

#print axioms check_sound
#print axioms conversion_iff_checked
#print axioms step_iff_checked
#print axioms convertChecked
#print axioms Examples.relator_step_checked
#print axioms Examples.relational_root_beneath_binder_checked
#print axioms Examples.symmetric_relator_conversion_checked
#print axioms Examples.beta_beneath_binder_checked
#print axioms Examples.variable_capture_rejected
#print axioms Examples.explicit_bridge_repairs_join
#print axioms Examples.betaArgument_typed
#print axioms Examples.identity_expansion_checked
#print axioms Examples.checked_dependent_identity_admission
#print axioms Examples.conversion_does_not_supply_formation

end NativeRelatorConversionChecking
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
