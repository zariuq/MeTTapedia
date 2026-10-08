import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWeakHead

/-!
# Constructed weak-head checking over the cumulative natural-number model

The recursor's authored equations inspect its fourth argument. The other
three arguments are parameters or methods and remain unevaluated until used.
This plan is derived from the existing role of `num-rec`, not supplied as an
execution witness. Both checking and conversion use the constructed shared-
budget weak-head reducer. The model's declaration, preservation and formation
proofs discharge the checking soundness obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableTowerNumbersWeakHead

open UniverseLevel
open TowerNumbersModel

variable (level : LevelExpr Nat)

def plan : ExecutableWeakHead.Plan Tower.Head := fun {_} term => match term with
  | .app (.app (.app (.app (.const name) _) _) _) _ =>
      if name = numRec then [.argument .here] else []
  | _ => []

theorem plan_recursor {n : Nat} (motive base step argument : Tm Tower.Head n) :
    plan (recApp numRec [motive, base, step] argument) = [.argument .here] := by
  simp [plan, recApp, appSpine]

theorem declared_inspection :
    roles numRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := roles_numRec

def reducer : ExecutableReduction.Reducer (rules level) := fun budget {_} term => do
  let result ← ExecutableWeakHead.run (rules level) (ExecutableTowerNumbers.root level)
    plan budget term
  return ⟨result.value, result.reduction⟩

def accepts {n : Nat} (budget : Nat) (context : Ctx Tower.Head n) (term type : Tm Tower.Head n) :
    Bool := ExecutableChecking.accepts (rules level) (ExecutableTowerNumbers.choices level)
      (reducer level) budget context term type

theorem accepts_sound {n budget : Nat} {context : Ctx Tower.Head n} {term type : Tm Tower.Head n}
    (accepted : accepts level budget context term type = true) : Typed (rules level) context term type :=
  ExecutableChecking.accepts_sound (S := setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) accepted

def acceptsSource {n : Nat} (budget : Nat)
    (context : ExecutableWrittenChecking.SourceContext Tower.Head n)
    (term type : ATm Tower.Head n) : Bool :=
  ExecutableWrittenChecking.acceptsSource (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) budget context term type

theorem acceptsSource_sound {n budget : Nat}
    {context : ExecutableWrittenChecking.SourceContext Tower.Head n} {term type : ATm Tower.Head n}
    (accepted : acceptsSource level budget context term type = true) :
    ATyped (rules level) context.erase term type.erase :=
  ExecutableWrittenChecking.acceptsSource_sound (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) accepted

/-- A dependent consumer also receives formation of every written context
entry and of the written expected type, not just typing after erasure. -/
theorem acceptsSource_formation {n budget : Nat}
    {context : ExecutableWrittenChecking.SourceContext Tower.Head n} {term type : ATm Tower.Head n}
    (accepted : acceptsSource level budget context term type = true) :
    ExecutableWrittenChecking.SourceContext.Formed (rules level) context ∧
      ∃ head, (rules level).isUniverse head ∧ ATyped (rules level) context.erase type (.head head) :=
  ExecutableWrittenChecking.acceptsSource_formation (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) accepted

def inferSource {n : Nat} (budget : Nat)
    (context : ExecutableWrittenChecking.SourceContext Tower.Head n)
    (term : ATm Tower.Head n) : Option (Tm Tower.Head n) :=
  ExecutableWrittenChecking.inferSource (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) budget context term

theorem inferSource_sound {n budget : Nat}
    {context : ExecutableWrittenChecking.SourceContext Tower.Head n}
    {term : ATm Tower.Head n} {type : Tm Tower.Head n}
    (computed : inferSource level budget context term = some type) :
    ExecutableWrittenChecking.SourceContext.Formed (rules level) context ∧
      ATyped (rules level) context.erase term type :=
  ExecutableWrittenChecking.inferSource_sound (setting level (fun _ => 0))
    (facts level) (roots level) (heads level) (algebra level)
    (ExecutableTowerNumbers.declaredTypesFormed level) (ExecutableTowerNumbers.choices level)
    (reducer level) computed

end TypedEquality.Normalization.ExecutableTowerNumbersWeakHead
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
