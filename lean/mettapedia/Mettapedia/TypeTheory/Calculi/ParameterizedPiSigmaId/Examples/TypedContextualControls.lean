import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualCwf
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversionSkeleton

/-!
# Typed contextual comprehension with eta-sensitive annotations

The context contains a function and a type family on functions. Applying
that family to the function or its eta expansion produces different type
codes with a typed equality. A supplied variable can be retyped across those
annotations and enters the selected quotient comprehension. Eta-equal supplied
functions also give equal quotient arrows, while original syntax cannot be
recovered uniformly from their quotient classes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedContextualControls

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization TypedContextual

abbrev levels : LevelModel Tower.rules Nat := TowerModel.levels (fun _ => (0 : Nat))
abbrev sort0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)
abbrev functionCode {n : Nat} : Tower.Tm n := .pi sort0 sort0
abbrev high := LevelTower.Head.sort (.max (.succ Tower.zero) (.succ Tower.zero))

theorem function_formed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ functionCode (.head high) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

abbrev closed : Context Tower.rules := empty Tower.rules

def functionType : TypeOver closed := ⟨functionCode, high, .sort _, function_formed .nil⟩
abbrev functionContext := extend closed functionType

def familyType : TypeOver functionContext where
  code := .pi functionCode sort0
  level := .sort (.max (.max (.succ Tower.zero) (.succ Tower.zero)) (.succ Tower.zero))
  universeWitness := .sort _
  formed := .piForm (function_formed _) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

abbrev familyContext := extend functionContext familyType

/-- The older variable is a function; the newest variable is a type family
whose arguments are functions of that genuinely formed type. -/
def suppliedFunction : Term familyContext
    (functionType.reindex (projectionHom functionContext familyType ≫ projectionHom closed functionType)) :=
  ⟨.var 1, .var 1⟩

def etaFunction : Term familyContext
    (functionType.reindex (projectionHom functionContext familyType ≫ projectionHom closed functionType)) := by
  refine ⟨.lam (.app (.var 2) (.var 0)), ?_⟩
  change Typed Tower.rules familyContext.raw (.lam (.app (.var 2) (.var 0))) functionCode
  apply Derivable.lamIntro (function_formed _) (.sort _)
  change Typed Tower.rules (.snoc familyContext.raw sort0) (.app (.var 2) (.var 0)) sort0
  exact .appElim (A := sort0) (B := sort0) (.var 2) (.var 0)

theorem function_eta : Equal Tower.rules familyContext.raw suppliedFunction.code etaFunction.code functionCode := by
  apply Derivable.etaPi suppliedFunction.typed etaFunction.typed
  change Equal Tower.rules (.snoc familyContext.raw sort0)
    (.app (.var 2) (.var 0))
    (.app (.lam (.app (.var 3) (.var 0))) (.var 0)) sort0
  exact .symm (.betaPi (function_formed _) (.sort _)
    (.appElim (A := sort0) (B := sort0) (.var 3) (.var 0)) (.var 0))

def firstAnnotation : TypeOver familyContext :=
  ⟨.app (.var 0) suppliedFunction.code, .sort Tower.zero, .sort _, .appElim (.var 0) suppliedFunction.typed⟩

def secondAnnotation : TypeOver familyContext :=
  ⟨.app (.var 0) etaFunction.code, .sort Tower.zero, .sort _, .appElim (.var 0) etaFunction.typed⟩

theorem annotations_equal : TypeEq Tower.rules familyContext.raw firstAnnotation.code secondAnnotation.code :=
  ⟨.sort Tower.zero, .sort _, .appCong (A := functionCode) (B := sort0) (.refl (.var 0)) function_eta⟩

theorem annotations_different_codes : firstAnnotation.code ≠ secondAnnotation.code := by
  intro same
  cases same

theorem annotations_not_raw_converted :
    ¬ Conv Tower.rules.headEq firstAnnotation.code secondAnnotation.code Tower.rules.computation := by
  apply TowerConversionSkeleton.not_conv_of_normal_erase_ne
  · intro target step
    cases step with
    | congAppFun earlier => cases earlier
    | congAppArg earlier => cases earlier
  · intro target step
    cases step with
    | congAppFun earlier => cases earlier
    | congAppArg earlier =>
        cases earlier with
        | congLam inside =>
            cases inside with
            | congAppFun prior => cases prior
            | congAppArg prior => cases prior
  · intro same
    cases same

theorem annotation_classes_agree : QType.mk levels firstAnnotation = QType.mk levels secondAnnotation :=
  (QType.mk_eq_iff levels _ _).mpr annotations_equal

abbrev suppliedContext := extend familyContext firstAnnotation

def suppliedVariable : Term suppliedContext (firstAnnotation.reindex (projectionHom familyContext firstAnnotation)) :=
  newest familyContext firstAnnotation

def convertedVariable : Term suppliedContext (secondAnnotation.reindex (projectionHom familyContext firstAnnotation)) :=
  suppliedVariable.convertType _ (reindex_typeEquality annotations_equal (projectionHom familyContext firstAnnotation))

theorem variable_survives_retyping : convertedVariable.code = .var 0 := rfl

theorem variable_classes_agree : QTerm.mk levels convertedVariable = QTerm.mk levels suppliedVariable :=
  QTerm.mk_convertType suppliedVariable _ _

/-- Both different raw annotations represent the same family class; the
selected comprehension receives the actual supplied variable class. -/
noncomputable def suppliedNativeVariable :
    QuotientCwf.Tm levels ((quotientProjection Tower.rules).obj suppliedContext)
      (QuotientCwf.tySub (QType.mk levels secondAnnotation)
        (QuotientCwf.project (projectionHom familyContext firstAnnotation))) :=
  ⟨QTerm.mk levels convertedVariable, rfl⟩

noncomputable def nativePair :
    (quotientProjection Tower.rules).obj suppliedContext ⟶
      QuotientCwf.ext ((quotientProjection Tower.rules).obj familyContext) (QType.mk levels secondAnnotation) :=
  QuotientCwf.pair (QuotientCwf.project (projectionHom familyContext firstAnnotation))
    (QType.mk levels secondAnnotation) suppliedNativeVariable

theorem native_pair_preserves_base :
    nativePair ≫ QuotientCwf.wk (QType.mk levels secondAnnotation) =
      QuotientCwf.project (projectionHom familyContext firstAnnotation) :=
  QuotientCwf.wk_pair _ _ _

theorem native_pair_preserves_variable :
    (QuotientCwf.tmSub (QuotientCwf.vz (QType.mk levels secondAnnotation)) nativePair).val =
      QTerm.mk levels suppliedVariable :=
  (QuotientCwf.vz_pair_value _ _ _).trans variable_classes_agree

theorem function_classes_agree : QTerm.mk levels suppliedFunction = QTerm.mk levels etaFunction := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  exact ⟨(functionType.reindex
    (projectionHom functionContext familyType ≫ projectionHom closed functionType)).isType.refl, function_eta⟩

def functionArrow : familyContext ⟶ functionContext :=
  TypedContextual.pair (toEmpty familyContext) suppliedFunction

def etaArrow : familyContext ⟶ functionContext :=
  TypedContextual.pair (toEmpty familyContext) etaFunction

theorem eta_arrow_classes_agree :
    (quotientProjection Tower.rules).map functionArrow = (quotientProjection Tower.rules).map etaArrow :=
  quotientProjection_pair_eq (homTypedEquality_refl _) function_eta

theorem eta_arrows_different : functionArrow ≠ etaArrow :=
  pair_distinguishes_codes _ (by intro same; cases same)

theorem function_not_raw_converted :
    ¬ Conv Tower.rules.headEq suppliedFunction.code etaFunction.code Tower.rules.computation := by
  apply TowerConversionSkeleton.not_conv_of_normal_erase_ne
    (TowerConversionSkeleton.erase_var_normal 1)
  · intro target step
    cases step with
    | congLam inner =>
        cases inner with
        | congAppFun earlier => cases earlier
        | congAppArg earlier => cases earlier
  · intro same
    cases same

/-- A typed class cannot promise the exact code of every supplied term. -/
theorem no_uniform_original_code :
    ¬ ∃ decode : QTerm levels familyContext → Tower.Tm familyContext.arity,
      ∀ (type : TypeOver familyContext) (term : Term familyContext type),
        decode (QTerm.mk levels term) = term.code := by
  rintro ⟨decode, recovers⟩
  have same := congrArg decode function_classes_agree
  rw [recovers _ suppliedFunction, recovers _ etaFunction] at same
  cases same

end Examples.TypedContextualControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
