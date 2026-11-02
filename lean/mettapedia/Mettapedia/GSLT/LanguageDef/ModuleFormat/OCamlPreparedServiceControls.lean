import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedPrimitivePath
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedFailurePaths

/-! Source values and faults exercise the composed query paths. Negative
controls exclude an invented primitive answer and entering a failed body.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ServiceControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def number (value : Int) : OCaml.Value := .literal (.integer value)
def primitiveProgram : OCaml.Program where
  code := #[.literal (.integer 40), .literal (.integer 2), .primitive .add [0, 1]]
  entry := 2
def lambdaProgram : OCaml.Program where
  code := #[.literal (.integer 42), .literal (.integer 0), .lambda (.literal (.integer 0)) 1, .apply 2 0]
  entry := 3
def letProgram : OCaml.Program where
  code := #[.literal (.integer 42), .literal (.integer 0), .letValue (.literal (.integer 0)) 0 1]
  entry := 2
def rest : OCaml.Continuation := [.consHead (.literal .nil)]
def encodedRest : Pattern := node "MlKConsHead" [value (.literal .nil), node "MlKDone"]
def addition : GeneralPremise.ProviderSnapshot := GeneralPremise.ProviderAppend.appendRows provider
  [primitiveRow .add [number 40, number 2] (.ok (number 42))]
def division : GeneralPremise.ProviderSnapshot := GeneralPremise.ProviderAppend.appendRows provider
  [primitiveRow .divide [number 42, number 0] (.error .divisionByZero)]
def failure : GeneralPremise.ProviderSnapshot := GeneralPremise.ProviderAppend.appendRows provider [failureRow 0 (number 42)]

#guard primitiveProgram.checkScope
#guard (prepare primitiveProgram).toOption.isSome
#guard OCaml.run primitiveProgram 100 (OCaml.begin primitiveProgram) == .complete (.ok (number 42))
#guard lambdaProgram.checkScope
#guard (prepare lambdaProgram).toOption.isSome
#guard OCaml.run lambdaProgram 100 (OCaml.begin lambdaProgram) == .complete (.error .matchFailure)
#guard !(OCaml.run lambdaProgram 100 (OCaml.begin lambdaProgram) == .complete (.ok (number 0)))
#guard letProgram.checkScope
#guard (prepare letProgram).toOption.isSome
#guard OCaml.run letProgram 100 (OCaml.begin letProgram) == .complete (.error .matchFailure)
#guard !(OCaml.run letProgram 100 (OCaml.begin letProgram) == .complete (.ok (number 0)))

theorem addition_retains_outer_continuation (prepared : Prepared) (built : prepare primitiveProgram = .ok prepared) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared addition) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (number 40), node "MlKBuild" [build (.primitive .add), codes [], environment [],
        valueList [number 2], encodedRest]])
      (node "MlReturn" [value (number 42), encodedRest]) := by
  have invariant := primitive_append_source_invariant (patterns primitiveProgram) provider .add [number 40, number 2]
    (.ok (number 42)) (initial_source_provider_invariant _) (by rfl)
  have actual := prepared_primitive_return_path primitiveProgram prepared addition .add (number 40) [] [number 2]
    (.ok (number 42)) rest encodedRest built invariant (by simp [addition, GeneralPremise.ProviderAppend.appendRows]) (by rfl)
  obtain ⟨_, target, encoded, path⟩ := actual
  have same : target = node "MlReturn" [value (number 42), encodedRest] := Option.some.inj encoded.symm
  exact same ▸ path

theorem division_fault_has_actual_path (prepared : Prepared) (built : prepare primitiveProgram = .ok prepared) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared division) [] (.base "MlConfig")).Step
      (node "MlPrimitiveRequest" [primitive .divide, valueList [number 42, number 0], encodedRest])
      (node "MlFault" [fault .divisionByZero]) := by
  have meaningful := primitive_append_preserves_meaning (patterns primitiveProgram) provider .divide [number 42, number 0]
    (.error .divisionByZero) (initial_provider_meaning _) (by rfl)
  obtain ⟨_, target, encoded, path⟩ := prepared_cached_primitive_path primitiveProgram prepared division .divide [number 42, number 0]
    (.error .divisionByZero) rest encodedRest built rfl meaningful
    (by simp [division, GeneralPremise.ProviderAppend.appendRows]) (by rfl)
  have same : target = node "MlFault" [fault .divisionByZero] := Option.some.inj encoded.symm
  exact same ▸ path

theorem division_cannot_cache_a_value (table : GeneralPremise.ProviderSnapshot) (answer : OCaml.Value)
    (invariant : SourceProviderInvariant (patterns primitiveProgram) table) :
    primitiveRow .divide [number 42, number 0] (.ok answer) ∉ table.rows := by
  intro present
  have source := invariant.meaningful.1 .divide [number 42, number 0] (.ok answer) present
  have actual : OCaml.Primitive.divide.eval [number 42, number 0] = .ok (.error .divisionByZero) := rfl
  rw [actual] at source
  cases source

theorem failed_lambda_has_fault_path (prepared : Prepared) (built : prepare lambdaProgram = .ok prepared) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared failure) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (.closure (.lambda 2) [number 99]), node "MlKFunction" [value (number 42), encodedRest]])
      (node "MlFault" [fault .matchFailure]) := by
  have invariant := failure_append_source_invariant (patterns lambdaProgram) provider 0 (.literal (.integer 0)) (number 42)
    (initial_source_provider_invariant _) (by rfl) (by rfl)
  exact (prepared_lambda_failure_path lambdaProgram prepared failure 2 1 0 (.literal (.integer 0)) [number 99] (number 42)
    rest encodedRest built rfl invariant.meaningful (by rfl) (by rfl) (by rfl) (by rfl)
    (by simp [failure, GeneralPremise.ProviderAppend.appendRows])).2

theorem failed_let_has_fault_path (prepared : Prepared) (built : prepare letProgram = .ok prepared) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (epochPlan prepared failure) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (number 42), node "MlKLet" [patternId 0, code 1, environment [number 99], encodedRest]])
      (node "MlFault" [fault .matchFailure]) := by
  have invariant := failure_append_source_invariant (patterns letProgram) provider 0 (.literal (.integer 0)) (number 42)
    (initial_source_provider_invariant _) (by rfl) (by rfl)
  exact (prepared_let_failure_path letProgram prepared failure 0 (.literal (.integer 0)) 1 [number 99] (number 42)
    rest encodedRest built rfl invariant.meaningful (by rfl) (by rfl) (by rfl)
    (by simp [failure, GeneralPremise.ProviderAppend.appendRows])).2

#print axioms addition_retains_outer_continuation
#print axioms division_fault_has_actual_path
#print axioms division_cannot_cache_a_value
#print axioms failed_lambda_has_fault_path
#print axioms failed_let_has_fault_path

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ServiceControls
