import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ProofRelevantStructuralComputation

/-!
# Universal certificates consumed by alternative value computations

The input theorem covers every argument admitted by its predicate-dependent
membership family. Applying it to one checked member constructs the exact
identity certificate between the original and alternative results. The
program returns a dependent pair, not an unchecked optimization assertion.

These laws concern value identity. They do not identify effect histories,
costs, multiplicities, or the native identity family with HOL equality.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace CertifiedFamilyShortcut

open Presentation FormationSensitive ProofRelevantStructuralComputation

variable {Head : Type} {n m : Nat}

/-- The relation certified at each member of the input family. -/
def equalityFamily (output : Tm Head (n + 1)) (f g : Tm Head n) : Tm Head (n + 1) :=
  .id output (.app (rename wk f) (.var 0)) (.app (rename wk g) (.var 0))

def guardedTheoremType (A : Tm Head n) (output : Tm Head (n + 1))
    (f g : Tm Head n) (membership : Tm Head (n + 1)) : Tm Head n :=
  .pi A (.pi membership (rename wk (equalityFamily output f g)))

def resultFamily (output originalResult : Tm Head n) : Tm Head (n + 1) :=
  .id (rename wk output) (rename wk originalResult) (.var 0)

/-- Only the alternative result and the applied theorem occur in the program
body. The original computation remains the endpoint of its certificate. -/
def run (alternative evidence argument member : Tm Head n) : Tm Head n :=
  .pair (.app alternative argument) (.app (.app evidence argument) member)

theorem instantiate_guarded (argument : Tm Head n) (membership conclusion : Tm Head (n + 1)) :
    inst0 argument (.pi membership (rename wk conclusion)) =
      .pi (inst0 argument membership) (rename wk (inst0 argument conclusion)) := by
  simp [inst0, subst]

theorem equalityFamily_at (output : Tm Head (n + 1)) (f g argument : Tm Head n) :
    inst0 argument (equalityFamily output f g) =
      .id (inst0 argument output) (.app f argument) (.app g argument) := by
  have eliminate (term : Tm Head n) : subst (subst0 argument) (rename wk term) = term :=
    inst0_rename_wk argument term
  simp [equalityFamily, inst0, subst, eliminate]

theorem resultFamily_at (output originalResult result : Tm Head n) :
    inst0 result (resultFamily output originalResult) =
      .id output originalResult result := by
  have eliminate (term : Tm Head n) : subst (subst0 result) (rename wk term) = term :=
    inst0_rename_wk result term
  simp [resultFamily, inst0, subst, eliminate]

/-- The actual universal theorem and checked membership give the instantiated
equality proof, by two dependent applications of the established typing rule. -/
theorem certificate_typed {R : Rules Head} {context : Ctx Head n}
    {A original alternative evidence argument member : Tm Head n}
    {output membership : Tm Head (n + 1)}
    (theoremTyped : Typing R context evidence
      (guardedTheoremType A output original alternative membership))
    (argumentTyped : Typing R context argument A)
    (memberTyped : Typing R context member (inst0 argument membership)) :
    Typing R context (.app (.app evidence argument) member)
      (.id (inst0 argument output) (.app original argument) (.app alternative argument)) := by
  have specialized := Typing.appElim theoremTyped argumentTyped
  rw [instantiate_guarded] at specialized
  simpa only [inst0_rename_wk, equalityFamily_at] using
    Typing.appElim specialized memberTyped

/-- Formation, the alternative computation and the actual instantiated
certificate construct the returned dependent package. -/
theorem run_typed {R : Rules Head} {context : Ctx Head n}
    {A original alternative evidence argument member : Tm Head n}
    {output membership : Tm Head (n + 1)} {v w : Head}
    (outputFormed : Typing R (.snoc context A) output (.head v))
    (isUniverse : R.isUniverse v)
    (join : R.join v v w) (resultUniverse : R.isUniverse w)
    (originalTyped : Typing R context original (.pi A output))
    (alternativeTyped : Typing R context alternative (.pi A output))
    (theoremTyped : Typing R context evidence
      (guardedTheoremType A output original alternative membership))
    (argumentTyped : Typing R context argument A)
    (memberTyped : Typing R context member (inst0 argument membership)) :
    Typing R context (run alternative evidence argument member)
      (.sigma (inst0 argument output)
        (resultFamily (inst0 argument output) (.app original argument))) := by
  have outputAtFormed : Typing R context (inst0 argument output) (.head v) := by
    simpa only [inst0, subst] using outputFormed.instantiate argumentTyped
  have originalResult := Typing.appElim originalTyped argumentTyped
  have alternativeResult := Typing.appElim alternativeTyped argumentTyped
  have relationFormed : Typing R (.snoc context (inst0 argument output))
      (resultFamily (inst0 argument output) (.app original argument)) (.head v) :=
    Typing.idForm outputAtFormed.weaken isUniverse originalResult.weaken (.var 0)
  have packageFormed := Typing.sigmaForm outputAtFormed isUniverse relationFormed isUniverse join
  have equalityTyped := certificate_typed theoremTyped argumentTyped memberTyped
  apply Typing.pairIntro packageFormed resultUniverse alternativeResult
  simpa only [resultFamily_at] using equalityTyped

/-- Context substitution acts on the same returned value and proof, rather
than reconstructing evidence with different provenance. -/
theorem run_substitute (sigma : Sub Head n m)
    (alternative evidence argument member : Tm Head n) :
    subst sigma (run alternative evidence argument member) =
      run (subst sigma alternative) (subst sigma evidence)
        (subst sigma argument) (subst sigma member) := rfl

/-- The projection retains the precise structural computation receipt. No
root rewrite or semantic equality oracle is used for this step. -/
def result_receipt (computation : Declaration.ProofRelevantRootComputation Head)
    (alternative evidence argument member : Tm Head n) :
    StructuralStepReceipt computation (fun _ _ => False)
      (.fst (run alternative evidence argument member)) (.app alternative argument) :=
  .betaSigmaFst _ _

def certificate_receipt (computation : Declaration.ProofRelevantRootComputation Head)
    (alternative evidence argument member : Tm Head n) :
    StructuralStepReceipt computation (fun _ _ => False)
      (.snd (run alternative evidence argument member))
      (.app (.app evidence argument) member) := .betaSigmaSnd _ _

#print axioms certificate_typed
#print axioms run_typed
#print axioms run_substitute
#print axioms result_receipt

end CertifiedFamilyShortcut
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
