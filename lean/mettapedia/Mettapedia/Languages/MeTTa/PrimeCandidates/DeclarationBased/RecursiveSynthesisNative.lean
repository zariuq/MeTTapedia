import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativePrimitiveRecursion
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeNaturalVectorFamilySource

/-!
# Recursive synthesis realized in the authored native Nat declaration world

The public doubling program becomes an actual native Peano recursor with a
typed lambda successor branch. Its evaluation agrees with the source program
on every natural input, and its universal half specification follows from
the independent source theorem. Zero and successor firings are retained as
typed occurrences of the already authored Nat/Vec source.

This is a declaration-world computation bridge, not a claim that the MIL
primitive/chain library synthesizes recursive functions or that a runtime
implements this Nat declaration package. A finite training prefix is shown
to leave behavior at the next input unconstrained.

The result of the program is a value: no computation step leaves it
(`doubleFunction_reaches_value`). That it is the only value the program can
reach would follow from confluence of the Nat rules, which is not proved
here; computation is a relation closed under every term constructor, not a
fixed evaluation order.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RecursiveSynthesisNative

open Presentation NativeNaturalVectorFamilies NativePrimitiveRecursion

namespace Source
export Mettapedia.Logic.Saturation.RecursiveSynthesis (half double double_correct)
end Source

variable {n : Nat}

/-- The successor branch ignores the predecessor but retains its binder;
the recursive value is the most recently bound variable. -/
def doubleStep : Tower.Tm n := .lam (.lam (succApp (succApp (.var 0))))

theorem doubleStep_typed (context : Tower.Ctx n) :
    Presentation.HasType rules context doubleStep (constantStepType natTm) :=
  .lamIntro (.lamIntro (succApp_hasType (succApp_hasType (.var 0))))

theorem nat_at_motive_level (context : Tower.Ctx n) :
    Presentation.HasType rules context natTm (sortTm motiveLevel) :=
  .cumul natTm_hasType (by
    intro valuation
    exact Nat.zero_le _)

def doubleProgram (input : Nat) : Tower.Tm n :=
  run (constantMotive natTm) zeroTm doubleStep input

/-- Doubling is also available as an ordinary first-class native function. -/
def doubleFunction : Tower.Tm n := program (constantMotive natTm) zeroTm doubleStep

theorem doubleFunction_typed (context : Tower.Ctx n) :
    Presentation.HasType rules context doubleFunction (SchemaElaboration.arrow natTm natTm) :=
  program_typed (nat_at_motive_level context) zeroTm_hasType (doubleStep_typed context)

theorem doubleProgram_typed (context : Tower.Ctx n) (input : Nat) :
    Presentation.HasType rules context (doubleProgram input) natTm :=
  constant_eliminate_typed (nat_at_motive_level context) zeroTm_hasType
    (doubleStep_typed context) (numeral_typed context input)

/-- Two ordinary beta reductions implement the source successor program. -/
theorem doubleStep_computes (input output : Nat) :
    Computes (.app (.app (doubleStep : Tower.Tm n) (numeral input)) (numeral output))
      (numeral (output + 2)) := by
  have first : Computes (.app (doubleStep : Tower.Tm n) (numeral input))
      (.lam (succApp (succApp (.var 0)))) :=
    Computes.beta _ _
  exact (first.appFun (numeral output)).trans (Computes.beta _ _)

/-- The native program realizes the source recursion at every input. -/
theorem doubleProgram_computes (input : Nat) :
    Computes (doubleProgram input : Tower.Tm n) (numeral (Source.double input)) :=
  realizes_primitiveRecursion numeral 0 (fun _ output => output + 2)
    (constantMotive natTm) zeroTm doubleStep .refl doubleStep_computes input

theorem doubleFunction_computes (input : Nat) :
    Computes (.app (doubleFunction : Tower.Tm n) (numeral input))
      (numeral (Source.double input)) :=
  program_realizes_primitiveRecursion numeral 0 (fun _ output => output + 2)
    (constantMotive natTm) zeroTm doubleStep .refl doubleStep_computes input

/-- The doubling function applied to a numeral computes to a value: the
numeral of the source result, which no computation step leaves. -/
theorem doubleFunction_reaches_value (input : Nat) :
    Computes (.app (doubleFunction : Tower.Tm n) (numeral input))
        (numeral (Source.double input)) ∧
      ∀ next : Tower.Tm n,
        ¬ StepCore rules.computation (fun _ _ => False) (numeral (Source.double input)) next :=
  ⟨doubleFunction_computes input, numeral_irreducible _⟩

/-- The source universal specification survives native realization. -/
theorem doubleProgram_correct (context : Tower.Ctx n) (input : Nat) :
    ∃ output, Presentation.HasType rules context (doubleProgram input) natTm ∧
      Computes (doubleProgram input : Tower.Tm n) (numeral output) ∧
      Presentation.HasType rules context (numeral output) natTm ∧
      Source.half output = input :=
  ⟨Source.double input, doubleProgram_typed context input, doubleProgram_computes input,
    numeral_typed context _, Source.double_correct input⟩

/-- The zero firing has both independently typed endpoints and an exact
occurrence in the single authored Nat/Vec declaration world. -/
noncomputable def doubleZeroOccurrence (context : Tower.Ctx n) :
    AuthoredIndexedFamilyTypedConversion.TypedOccurrence
      NativeNaturalVectorFamilySource.natPresentedCandidate context
      (doubleProgram 0) zeroTm natTm where
  authored := NativeNaturalVectorFamilySource.natPresentedCandidate.receiptEquiv.symm
    (IotaEvidence.natZero (constantMotive natTm) zeroTm doubleStep)
  sourceTyping := doubleProgram_typed context 0
  targetTyping := zeroTm_hasType

/-- The successor firing retains the predecessor, the recursive call and
the authored rule receipt before either beta reduction of the branch. -/
noncomputable def doubleSuccOccurrence (context : Tower.Ctx n) (input : Nat) :
    AuthoredIndexedFamilyTypedConversion.TypedOccurrence
      NativeNaturalVectorFamilySource.natPresentedCandidate context
      (doubleProgram (input + 1))
      (.app (.app doubleStep (numeral input)) (doubleProgram input)) natTm where
  authored := NativeNaturalVectorFamilySource.natPresentedCandidate.receiptEquiv.symm
    (IotaEvidence.natSucc (constantMotive natTm) zeroTm doubleStep (numeral input))
  sourceTyping := doubleProgram_typed context (input + 1)
  targetTyping := Presentation.HasType.appElim
    (Presentation.HasType.appElim (doubleStep_typed context) (numeral_typed context input))
    (doubleProgram_typed context input)

theorem doubleZeroOccurrence_nativeEvidence (context : Tower.Ctx n) :
    (doubleZeroOccurrence context).nativeEvidence =
      IotaEvidence.natZero (constantMotive natTm) zeroTm doubleStep :=
  NativeNaturalVectorFamilySource.natPresentedCandidate.receiptEquiv.apply_symm_apply _

theorem doubleSuccOccurrence_nativeEvidence (context : Tower.Ctx n) (input : Nat) :
    (doubleSuccOccurrence context input).nativeEvidence =
      IotaEvidence.natSucc (constantMotive natTm) zeroTm doubleStep (numeral input) :=
  NativeNaturalVectorFamilySource.natPresentedCandidate.receiptEquiv.apply_symm_apply _

/-- No branch observation below the cutoff distinguishes this candidate
from doubling, but its next result violates the universal specification. -/
def finiteFit (cutoff input : Nat) : Nat :=
  if input ≤ cutoff then Source.double input else 0

theorem finiteFit_training (cutoff input : Nat) (within : input ≤ cutoff) :
    finiteFit cutoff input = Source.double input := by
  simp only [finiteFit, if_pos within]

theorem finiteFit_fails_universal (cutoff : Nat) :
    Source.half (finiteFit cutoff (cutoff + 1)) ≠ cutoff + 1 := by
  simp [finiteFit, Source.half]

/-- The source half specification is one-sided even after compiling its
correct recursive witness. -/
theorem double_half_not_left_inverse : Source.double (Source.half 1) ≠ 1 :=
  Mettapedia.Logic.Saturation.RecursiveSynthesis.half_double_not_left_inverse

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RecursiveSynthesisNative
