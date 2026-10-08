import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.IotaComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws

/-!
# Head substitution preserves constructor recursor equations

Closed field types change with their heads; recursive field positions and
constructor occurrences stay in their original order. Both sides of every
recursor equation are transported, including all recursive calls.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization

variable {H K : Type}

def Field.mapHead (map : H → K) : Field H → Field K
  | .recursive => .recursive
  | .closed type => .closed (type.mapHead map)

def mapConstructors (map : H → K) (constructors : List (DeclName × List (Field H))) :
    List (DeclName × List (Field K)) :=
  constructors.map (fun constructor => (constructor.1, constructor.2.map (Field.mapHead map)))

@[simp] theorem mapHead_appSpine {n : Nat} (map : H → K) (function : Tm H n)
    (arguments : List (Tm H n)) :
    (appSpine function arguments).mapHead map =
      appSpine (function.mapHead map) (arguments.map (Tm.mapHead map)) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons first rest ih =>
      simpa only [appSpine, List.foldl, List.map_cons, Tm.mapHead] using (ih (.app function first))

@[simp] theorem mapHead_recApp {n : Nat} (map : H → K) (name : DeclName)
    (before : List (Tm H n)) (argument : Tm H n) :
    (recApp name before argument).mapHead map =
      recApp name (before.map (Tm.mapHead map)) (argument.mapHead map) := by
  simp [recApp, Tm.mapHead]

@[simp] theorem mapHead_recArgs {n : Nat} (map : H → K) :
    ∀ (fields : List (Field H)) (arguments : List (Tm H n)),
      (recArgs fields arguments).map (Tm.mapHead map) =
        recArgs (fields.map (Field.mapHead map)) (arguments.map (Tm.mapHead map))
  | .recursive :: fields, argument :: arguments => by
      simp [recArgs, Field.mapHead, mapHead_recArgs map fields arguments]
  | .closed _ :: fields, _ :: arguments => by
      simp [recArgs, Field.mapHead, mapHead_recArgs map fields arguments]
  | [], _ => by simp [recArgs]
  | .recursive :: _, [] => by simp [recArgs, Field.mapHead]
  | .closed _ :: _, [] => by simp [recArgs, Field.mapHead]

theorem IotaStep.mapHead {n : Nat} {name : DeclName}
    {constructors : List (DeclName × List (Field H))} {left right : Tm H n}
    (map : H → K) (step : IotaStep name constructors left right) :
    IotaStep name (mapConstructors map constructors) (left.mapHead map) (right.mapHead map) := by
  obtain ⟨motive, methods, index, constructor, fields, arguments, method,
    methodsLength, found, argumentsLength, methodFound, rfl, rfl⟩ := step
  refine ⟨motive.mapHead map, methods.map (Tm.mapHead map), index, constructor,
    fields.map (Field.mapHead map), arguments.map (Tm.mapHead map), method.mapHead map,
    by simp [mapConstructors, methodsLength], ?_, by simp [argumentsLength],
    by simp [methodFound], ?_, ?_⟩
  · simp [mapConstructors, found]
  · simp only [mapHead_recApp, mapHead_appSpine, Tm.mapHead, List.map_cons]
  · rw [mapHead_appSpine, List.map_append, ← mapHead_recArgs]
    simp only [List.map_map, Function.comp_def, mapHead_recApp, List.map_cons]

end TypedEquality.Normalization
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
