import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWrittenChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.NativeSyntax

/-!
# Scope decoding joined to executable annotated checking

Raw numeric indices are accepted only after scope recovery. Decoding preserves
the exact annotated source, and the checking procedure reconstructs its typed
interpretation. This symbolic boundary does not assert a C implementation
refinement or decide typing when it finds no derivation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableRawChecking

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] (S : Setting Head L)
  [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (headSteps : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R)
  (evaluator : ExecutableReduction.Reducer S.R)

def accepts {n : Nat} (fuel : Nat) (context : ExecutableWrittenChecking.SourceContext Head n)
    (term type : NativeSyntax.Raw Head) : Bool :=
  match NativeSyntax.decode n term, NativeSyntax.decode n type with
  | some term', some type' =>
      ExecutableWrittenChecking.acceptsSource S facts roots headSteps algebra declared choices evaluator
        fuel context term' type'
  | _, _ => false

@[simp] theorem accepts_encoded {n : Nat} (fuel : Nat)
    (context : ExecutableWrittenChecking.SourceContext Head n) (term type : ATm Head n) :
    accepts S facts roots headSteps algebra declared choices evaluator fuel context
      (NativeSyntax.encode term) (NativeSyntax.encode type) =
      ExecutableWrittenChecking.acceptsSource S facts roots headSteps algebra declared choices evaluator
        fuel context term type := by
  simp only [accepts, NativeSyntax.decode_encode]

theorem accepts_sound {n fuel : Nat} {context : ExecutableWrittenChecking.SourceContext Head n}
    {term type : NativeSyntax.Raw Head}
    (accepted : accepts S facts roots headSteps algebra declared choices evaluator
      fuel context term type = true) :
    ∃ source expected : ATm Head n,
      NativeSyntax.decode n term = some source ∧ NativeSyntax.decode n type = some expected ∧
      NativeSyntax.encode source = term ∧ NativeSyntax.encode expected = type ∧
      ATyped S.R context.erase source expected.erase := by
  cases termDecoded : NativeSyntax.decode n term with
  | none => simp only [accepts, termDecoded, Bool.false_eq_true] at accepted
  | some source =>
      cases typeDecoded : NativeSyntax.decode n type with
      | none => simp only [accepts, termDecoded, typeDecoded, Bool.false_eq_true] at accepted
      | some expected =>
          simp only [accepts, termDecoded, typeDecoded] at accepted
          exact ⟨source, expected, rfl, rfl, NativeSyntax.encode_decode termDecoded,
            NativeSyntax.encode_decode typeDecoded,
            ExecutableWrittenChecking.acceptsSource_sound S facts roots headSteps algebra declared
              choices evaluator accepted⟩

end TypedEquality.Normalization.ExecutableRawChecking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
