import Mettapedia.Languages.VibeITP.Native.ComputedArithmetic
import Mettapedia.Languages.VibeITP.Presentation.KernelControls

/-! Positive and negative uses of computed evidence inside actual Vibe rules. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.VibeITP.Native.ComputedArithmetic.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.Languages.VibeITP.Presentation
open Mettapedia.Languages.VibeITP.Presentation.KernelControls

def addProof (a b result : Nat) : CompactProof Claim :=
  .node ⟨⟨rLitAdd.id⟩,
    [encNat a, encNat b, encNat (a + b), encNat result,
      encBytes (natLiteral a), encBytes (natLiteral b), encBytes (natLiteral result)]⟩
    [.computed (.word a), .computed (.word b), .computed (.add a b (a + b)),
      .computed (.mod64 (a + b) result), .computed (.natLiteral a (natLiteral a)),
      .computed (.natLiteral b (natLiteral b)), .computed (.natLiteral result (natLiteral result))]

def addGoal (a b result : Nat) : Pattern :=
  jThm (encTerm controlTheory.sig
    (.eq (.app (.builtin .litAdd) [.natLit a, .natLit b]) (.natLit result)))

/-- The actual theorem-producing rule surrounds seven compressed arithmetic
subtrees. The addition intermediate is 2^64; only the modulo step wraps. -/
theorem maximal_word_add_accepts :
    check (kernelValidated controlTheory 4) evaluate
      (addGoal 18446744073709551615 1 0)
      (addProof 18446744073709551615 1 0) = true := by decide +kernel

theorem wrong_wrapped_result_rejects :
    check (kernelValidated controlTheory 4) evaluate
      (addGoal 18446744073709551615 1 1)
      (addProof 18446744073709551615 1 1) = false := by decide +kernel

theorem maximal_word_add_has_original_replay :
    ∃ raw, checkRaw (kernelValidated controlTheory 4)
      (addGoal 18446744073709551615 1 0) raw = true :=
  accepted_has_replay (computation controlTheory_hosted) maximal_word_add_accepts

theorem original_mp_still_accepts :
    check (kernelValidated controlTheory 4) evaluate
      (jThm (encTerm controlTheory.sig atomB)) (.replay mpArticle) = true := by
  simpa only [check] using modus_ponens_accepts

theorem missing_mp_premise_rejects :
    check (kernelValidated controlTheory 4) evaluate
      (jThm (encTerm controlTheory.sig atomB))
      (.node ⟨⟨rMp.id⟩, mpArguments⟩ [.replay (axiomLeaf 1)]) = false := by decide +kernel

theorem reversed_mp_premises_reject :
    check (kernelValidated controlTheory 4) evaluate
      (jThm (encTerm controlTheory.sig atomB))
      (.node ⟨⟨rMp.id⟩, mpArguments⟩
        [.replay (axiomLeaf 2), .replay (axiomLeaf 1)]) = false := by decide +kernel

theorem division_zero_computed_rejects (a q r : Nat) :
    evaluate (.divMod a 0 q r) = none := by simp [evaluate, valid]

theorem division_zero_no_replay {T : Theory} {n : Nat} (hosted : Hosted T n)
    (a q r : Nat) (raw : RawProof) :
    checkRaw (kernelValidated T n) (judgment (.divMod a 0 q r)) raw = false :=
  invalid_rejects_every_replay hosted (by simp [valid]) raw

theorem swapped_goal_rejects :
    check (kernelValidated controlTheory 4) evaluate (judgment (.add 2 2 5))
      (.computed (.add 2 2 4)) = false := by decide +kernel

theorem false_arithmetic_has_no_replay (raw : RawProof) :
    checkRaw (kernelValidated controlTheory 4) (judgment (.add 2 2 5)) raw = false :=
  invalid_rejects_every_replay controlTheory_hosted (by decide +kernel) raw

/-- An evaluator that merely echoes claimed answers cannot be qualified. -/
theorem unchecked_answers_not_qualified :
    ¬ ∃ candidate : QualifiedComputation (kernelValidated controlTheory 4) Claim,
      candidate.evaluate = (fun claim => some (judgment claim)) := by
  apply unqualified_of_extra_output (kernelValidated controlTheory 4)
    (fun claim => some (judgment claim)) (query := .add 2 2 5) rfl
  rintro ⟨raw, accepted⟩
  have refused := false_arithmetic_has_no_replay raw
  rw [refused] at accepted
  contradiction

end Mettapedia.Languages.VibeITP.Native.ComputedArithmetic.Controls
