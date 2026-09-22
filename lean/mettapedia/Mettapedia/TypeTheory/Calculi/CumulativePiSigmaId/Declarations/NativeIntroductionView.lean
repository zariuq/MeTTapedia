import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayConversionView
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCertificate
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorQualification

/-!
# Computed native introduction evidence through conversion wrappers

The source's existing principal view supplies its original introduction code.
The result tail supplies a composed finite conversion, with cumulative steps
excluded by the native Pi/head and Sigma/head separation theorems. Both
extractors succeed on every accepted introduction subject, at any displayed
type; neither searches for a derivation or reconstructs a convenient witness.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay

open Presentation StructuralTypingReplay NativeIndexedFamilies

structure LambdaView (n : Nat) where
  domain : Tower.Tm n
  codomain : Tower.Tm (n + 1)
  level : Tower.Head
  formation : Code n
  body : Code (n + 1)
  conversion : NativeRelatorConversionChecking.Code n

structure PairView (n : Nat) where
  domain : Tower.Tm n
  codomain : Tower.Tm (n + 1)
  level : Tower.Head
  formation : Code n
  first : Code n
  second : Code n
  conversion : NativeRelatorConversionChecking.Code n

def lambdaView {n : Nat} (displayed : Tower.Tm n) (code : Code n) : Option (LambdaView n) := do
  let view ← code.principalView displayed
  let conversion ← view.tail.conversion? (.refl) (.trans) view.type
  match view.type, view.code with
  | .pi domain codomain, .lamIntro level formation body =>
      return ⟨domain, codomain, level, formation, body, conversion⟩
  | _, _ => none

def pairView {n : Nat} (displayed : Tower.Tm n) (code : Code n) : Option (PairView n) := do
  let view ← code.principalView displayed
  let conversion ← view.tail.conversion? (.refl) (.trans) view.type
  match view.type, view.code with
  | .sigma domain codomain, .pairIntro level formation first second =>
      return ⟨domain, codomain, level, formation, first, second, conversion⟩
  | _, _ => none

private theorem conversion_from_view {n : Nat} {context : Tower.Ctx n}
    {subject displayed : Tower.Tm n} {code : Code n}
    {view : PrincipalView Tower.Head NativeRelatorConversionChecking.Code n}
    (accepted : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context subject displayed code = true)
    (computed : code.principalView displayed = some view)
    (separated : ∀ head conversion,
      NativeRelatorConversionChecking.check conversion view.type (.head head) = false) :
    ∃ conversion, view.tail.conversion? (.refl) (.trans) view.type = some conversion ∧
      NativeRelatorConversionChecking.check conversion view.type displayed = true :=
  Code.principal_conversion_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check
    (.refl) (.trans)
    (StructuralConversionCode.Code.check_refl Tower.HeadEq NativeRelatorRootConversionCode.decode)
    (StructuralConversionCode.Code.check_trans Tower.HeadEq NativeRelatorRootConversionCode.decode)
    code accepted computed separated

theorem lambdaView_checked {n : Nat} {context : Tower.Ctx n}
    {body : Tower.Tm (n + 1)} {displayed : Tower.Tm n} {code : Code n}
    (accepted : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context (.lam body) displayed code = true) :
    ∃ view, lambdaView displayed code = some view ∧
      IntrinsicRelator.rules.isUniverse view.level ∧
      StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        context (.pi view.domain view.codomain) (.head view.level) view.formation = true ∧
      StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        (.snoc context view.domain) body view.codomain view.body = true ∧
      NativeRelatorConversionChecking.check view.conversion
        (.pi view.domain view.codomain) displayed = true := by
  obtain ⟨view, computed, checked, _⟩ :=
    Code.principalView_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check code accepted
  have principal := (Code.principalView_reconstruct code computed).2
  obtain ⟨A, B, level, formation, bodyCode, typeEq, codeEq, isU, formed, bodyChecked⟩ :=
    Code.principal_lambda IntrinsicRelator.rules NativeRelatorConversionChecking.check
      view.code principal checked
  obtain ⟨conversion, conversionComputed, conversionChecked⟩ := conversion_from_view accepted computed
    (fun head conversion => by
      rw [typeEq]
      exact FormationSensitiveNativeRelatorQualification.check_pi_head_rejected conversion A B head)
  refine ⟨⟨A, B, level, formation, bodyCode, conversion⟩, ?_, isU, formed, bodyChecked, ?_⟩
  · rw [typeEq] at conversionComputed
    simp [lambdaView, computed, typeEq, codeEq, conversionComputed]
  · simpa only [typeEq] using conversionChecked

theorem pairView_checked {n : Nat} {context : Tower.Ctx n}
    {first second displayed : Tower.Tm n} {code : Code n}
    (accepted : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context (.pair first second) displayed code = true) :
    ∃ view, pairView displayed code = some view ∧
      IntrinsicRelator.rules.isUniverse view.level ∧
      StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        context (.sigma view.domain view.codomain) (.head view.level) view.formation = true ∧
      StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        context first view.domain view.first = true ∧
      StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        context second (inst0 first view.codomain) view.second = true ∧
      NativeRelatorConversionChecking.check view.conversion
        (.sigma view.domain view.codomain) displayed = true := by
  obtain ⟨view, computed, checked, _⟩ :=
    Code.principalView_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check code accepted
  have principal := (Code.principalView_reconstruct code computed).2
  obtain ⟨A, B, level, formation, firstCode, secondCode, typeEq, codeEq,
      isU, formed, firstChecked, secondChecked⟩ :=
    Code.principal_pair IntrinsicRelator.rules NativeRelatorConversionChecking.check
      view.code principal checked
  obtain ⟨conversion, conversionComputed, conversionChecked⟩ := conversion_from_view accepted computed
    (fun head conversion => by
      rw [typeEq]
      exact FormationSensitiveNativeRelatorQualification.check_sigma_head_rejected conversion A B head)
  refine ⟨⟨A, B, level, formation, firstCode, secondCode, conversion⟩,
    ?_, isU, formed, firstChecked, secondChecked, ?_⟩
  · rw [typeEq] at conversionComputed
    simp [pairView, computed, typeEq, codeEq, conversionComputed]
  · simpa only [typeEq] using conversionChecked

#print axioms lambdaView_checked
#print axioms pairView_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
