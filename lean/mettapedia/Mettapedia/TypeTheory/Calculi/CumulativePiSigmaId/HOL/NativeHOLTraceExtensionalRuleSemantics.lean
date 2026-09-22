import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceLeibnizProofSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofCoverage

/-!
# Extensional HOL rules in the Aczel trace model

The native Leibniz compiler deliberately omits the extensional HOL rules.  This
module constructs their exact semantic witnesses in the already established
Aczel trace model.  It does not add a native constant or a compiler case.

At propositions, mutual implication determines the literal two-valued trace
code.  At arrows, equality at every trace argument determines the literal
function trace.  These equalities inhabit the same separated Leibniz proof
family used by compiled native proofs.  The controls show why both implication
directions and all function arguments are essential.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceExtensionalRuleSemantics

open Presentation Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (Section)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetTraceProofDecoding
open NativeHOLTraceLeibnizProofSemantics

universe u

/-- Mutual truth preservation identifies proposition trace values literally. -/
theorem proposition_extensional {a : ZFSet.{u}}
    (left right : Value a .prop)
    (forward : ZFSetHOLTypeInterpretation.holds left →
      ZFSetHOLTypeInterpretation.holds right)
    (backward : ZFSetHOLTypeInterpretation.holds right →
      ZFSetHOLTypeInterpretation.holds left) :
    left = right := by
  calc
    left = ZFSetHOLTypeInterpretation.truth
        (ZFSetHOLTypeInterpretation.holds left) :=
      (ZFSetHOLTypeInterpretation.truth_holds left).symm
    _ = ZFSetHOLTypeInterpretation.truth
        (ZFSetHOLTypeInterpretation.holds right) :=
      congrArg ZFSetHOLTypeInterpretation.truth (propext ⟨forward, backward⟩)
    _ = right := ZFSetHOLTypeInterpretation.truth_holds right

/-- Pointwise equality at every trace argument identifies Aczel traces
literally, not merely their decoded functions. -/
theorem function_extensional {a : ZFSet.{u}} {domain codomain : HOL.Ty BaseSort}
    (left right : Value a (.arr domain codomain))
    (pointwise : ∀ argument : Value a domain,
      app left argument = app right argument) :
    left = right := by
  calc
    left = lam (fun argument => app left argument) := (lam_eta left).symm
    _ = lam (fun argument => app right argument) :=
      congrArg lam (funext pointwise)
    _ = right := lam_eta right

/-- Equality of lambda bodies gives literal equality of their trace lambdas. -/
theorem lambda_extensional {a : ZFSet.{u}} {domain codomain : HOL.Ty BaseSort}
    (left right : Value a domain → Value a codomain)
    (pointwise : ∀ argument, left argument = right argument) :
    lam left = lam right :=
  congrArg lam (funext pointwise)

/-- A true proposition has a canonical inhabitant in the separated proof
code.  This is semantic evidence; it is not presented as native syntax. -/
noncomputable def truthSection {Gamma : Type (u + 1)} {proposition : Gamma → Prop}
    (valid : ∀ environment, proposition environment) :
    Section (truthFamily proposition) :=
  fun environment =>
    ⟨∅, (mem_truthCode (proposition environment) ∅).mpr
      ⟨rfl, valid environment⟩⟩

/-- Pointwise literal equality supplies the exact separated proof section used
by the native Leibniz equality decoder. -/
noncomputable def equalitySection {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    {type : HOL.Ty BaseSort} (left right : Gamma → Value a type)
    (equal : ∀ environment, left environment = right environment) :
    Section (truthFamily (equalityProposition left right)) :=
  truthSection equal

/-- Semantic realization of the HOL propositional-extensionality rule in the
same equality proof family used by compiled native proofs. -/
noncomputable def propositionExtensionalitySection {a : ZFSet.{u}}
    {Gamma : Type (u + 1)} (left right : Gamma → Value a .prop)
    (forward : ∀ environment, ZFSetHOLTypeInterpretation.holds (left environment) →
      ZFSetHOLTypeInterpretation.holds (right environment))
    (backward : ∀ environment, ZFSetHOLTypeInterpretation.holds (right environment) →
      ZFSetHOLTypeInterpretation.holds (left environment)) :
    Section (truthFamily (equalityProposition left right)) :=
  equalitySection left right
    (fun environment => proposition_extensional _ _
      (forward environment) (backward environment))

/-- Semantic realization of HOL function extensionality.  Quantification is
over every element of the actual trace domain. -/
noncomputable def functionExtensionalitySection {a : ZFSet.{u}}
    {Gamma : Type (u + 1)} {domain codomain : HOL.Ty BaseSort}
    (left right : Gamma → Value a (.arr domain codomain))
    (pointwise : ∀ environment (argument : Value a domain),
      app (left environment) argument = app (right environment) argument) :
    Section (truthFamily (equalityProposition left right)) :=
  equalitySection left right
    (fun environment => function_extensional _ _ (pointwise environment))

/-- The lambda-congruence rule is realized by the actual trace constructor. -/
noncomputable def lambdaCongruenceSection {a : ZFSet.{u}}
    {Gamma : Type (u + 1)} {domain codomain : HOL.Ty BaseSort}
    (left right : Gamma → Value a domain → Value a codomain)
    (pointwise : ∀ environment argument,
      left environment argument = right environment argument) :
    Section (truthFamily (equalityProposition
      (fun environment => lam (left environment))
      (fun environment => lam (right environment)))) :=
  equalitySection _ _
    (fun environment => lambda_extensional _ _ (pointwise environment))

/-- Eta is literal equality of the trace re-encoding with the original trace. -/
noncomputable def etaSection {a : ZFSet.{u}} {Gamma : Type (u + 1)}
    {domain codomain : HOL.Ty BaseSort}
    (function : Gamma → Value a (.arr domain codomain)) :
    Section (truthFamily (equalityProposition
      (fun environment => lam (fun argument => app (function environment) argument))
      function)) :=
  equalitySection _ _ (fun environment => lam_eta (function environment))

namespace Controls

/-- One implication direction is not propositional extensionality. -/
theorem forward_only_not_enough {a : ZFSet.{u}} :
    (ZFSetHOLTypeInterpretation.holds
        (ZFSetHOLTypeInterpretation.truth False : Value a .prop) →
      ZFSetHOLTypeInterpretation.holds
        (ZFSetHOLTypeInterpretation.truth True : Value a .prop)) ∧
    (ZFSetHOLTypeInterpretation.truth False : Value a .prop) ≠
      ZFSetHOLTypeInterpretation.truth True := by
  constructor
  · intro impossible
    exact False.elim ((ZFSetHOLTypeInterpretation.holds_truth False).mp impossible)
  · intro equal
    have trueAtLeft : ZFSetHOLTypeInterpretation.holds
        (ZFSetHOLTypeInterpretation.truth False) := by
      rw [equal]
      exact (ZFSetHOLTypeInterpretation.holds_truth True).mpr trivial
    exact (ZFSetHOLTypeInterpretation.holds_truth False).mp trueAtLeft

noncomputable def propositionIdentity {a : ZFSet.{u}} :
    Value a (.arr .prop .prop) :=
  lam (fun proposition => proposition)

noncomputable def propositionConstantTrue {a : ZFSet.{u}} :
    Value a (.arr .prop .prop) :=
  lam (fun _ => ZFSetHOLTypeInterpretation.truth True)

/-- Agreement at one test point is not function extensionality. -/
theorem one_argument_not_enough {a : ZFSet.{u}} :
    app (propositionIdentity (a := a)) (ZFSetHOLTypeInterpretation.truth True) =
        app (propositionConstantTrue (a := a))
          (ZFSetHOLTypeInterpretation.truth True) ∧
      propositionIdentity (a := a) ≠ propositionConstantTrue (a := a) := by
  constructor
  · simp [propositionIdentity, propositionConstantTrue]
  · intro equal
    have atFalse := congrArg
      (fun function : Value a (.arr .prop .prop) =>
        app function (ZFSetHOLTypeInterpretation.truth False)) equal
    have valuesEqual :
        (ZFSetHOLTypeInterpretation.truth False : Value a .prop) =
          ZFSetHOLTypeInterpretation.truth True := by
      simpa only [propositionIdentity, propositionConstantTrue, app_lam] using atFalse
    exact forward_only_not_enough (a := a) |>.2 valuesEqual

end Controls

#print axioms proposition_extensional
#print axioms function_extensional
#print axioms lambda_extensional
#print axioms equalitySection
#print axioms propositionExtensionalitySection
#print axioms functionExtensionalitySection
#print axioms lambdaCongruenceSection
#print axioms etaSection
#print axioms Controls.forward_only_not_enough
#print axioms Controls.one_argument_not_enough

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLTraceExtensionalRuleSemantics
