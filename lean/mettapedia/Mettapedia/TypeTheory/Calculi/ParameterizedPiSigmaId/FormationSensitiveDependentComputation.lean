import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SigmaConversionBoundary
import Mettapedia.TypeTheory.ContextualDependentSequencing

/-!
# Effectful selection of formation-sensitive dependent pairs

The answer types of the existing contextual program carry complete native
formation-sensitive judgments. A selected admitted value `a : A` indexes the
continuation's admitted result `b : B[a]`; independently admitted Sigma
formation then licenses the existing native pair constructor.

The isolated-world handler retains the selected branch, final state and
ordered deferred intents. Renaming and substitution below concern native
values and their judgments, not effectful substitutions of an object-language
CBPV calculus. No new evaluator, total type checker, conversion qualification
or adoption of this candidate judgment is asserted.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive.DependentComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bindSigma)
open Mettapedia.TypeTheory.ContextualDependentSequencing

variable {Head : Type} {R : Rules Head} {n m : Nat}
variable {Γ : Ctx Head n} {Δ : Ctx Head m} {A : Tm Head n} {B : Tm Head (n + 1)}

/-- An existing native term with its full formation-sensitive admission. -/
abbrev TypedValue (R : Rules Head) (Γ : Ctx Head n) (A : Tm Head n) :=
  { term : Tm Head n // Judgment R Γ term A }

namespace TypedValue

def rename {ρ : Ren n m} (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (value : TypedValue R Γ A) : TypedValue R Δ (Presentation.rename ρ A) :=
  ⟨Presentation.rename ρ value.val, target, value.property.typing.renameTyping compatible⟩

def substitute {σ : Sub Head n m} (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (value : TypedValue R Γ A) : TypedValue R Δ (subst σ A) :=
  ⟨subst σ value.val, value.property.substitute target typed⟩

/-- Reindex the dependent fibre using the actual capture-avoiding law. -/
def renameFibre {ρ : Ren n m} (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue R Δ (inst0 (Presentation.rename ρ first.val)
      (Presentation.rename (liftRen ρ) B)) :=
  ⟨Presentation.rename ρ second.val, target, by
    have typing := second.property.typing.renameTyping compatible
    rw [rename_inst0] at typing
    exact typing⟩

/-- Typed substitution transports the fibre at the selected native value. -/
def substituteFibre {σ : Sub Head n m} (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue R Δ (inst0 (subst σ first.val) (subst (liftSub σ) B)) :=
  ⟨subst σ second.val, target, by
    have typing := second.property.typing.substitute typed
    rw [subst_inst0] at typing
    exact typing⟩

end TypedValue

/-- Native pair introduction requires independently admitted Sigma formation. -/
def sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (first : TypedValue R Γ A)
    (second : TypedValue R Γ (inst0 first.val B)) : TypedValue R Γ (.sigma A B) :=
  ⟨.pair first.val second.val, formed.context,
    .pairIntro formed.typing universeWitness first.property.typing second.property.typing⟩

theorem rename_sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) {ρ : Ren n m}
    (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue.rename target compatible (sigmaPair formed universeWitness first second) =
      sigmaPair ⟨target, formed.typing.renameTyping compatible⟩ universeWitness
        (TypedValue.rename target compatible first)
        (TypedValue.renameFibre target compatible first second) := by
  apply Subtype.ext
  rfl

theorem substitute_sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) {σ : Sub Head n m}
    (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue.substitute target typed (sigmaPair formed universeWitness first second) =
      sigmaPair (formed.substitute target typed) universeWitness
        (TypedValue.substitute target typed first)
        (TypedValue.substituteFibre target typed first second) := by
  apply Subtype.ext
  rfl

section Effects

variable {State Intent : Type}

/-- Existing dependent sequencing followed by native pair introduction. -/
def sigmaProgram {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent) :
    Program State (TypedValue R Γ (.sigma A B)) Intent :=
  Program.map (fun value => sigmaPair formed universeWitness value.1 value.2)
    (bindSigma indices next)

/-- Each selected world supplies its own continuation state and branch. Its
intents precede the continuation's intents, and its index remains in the pair. -/
theorem runWorldsAt_sigmaProgram {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (sigmaProgram formed universeWitness indices next) state branch =
      (runWorldsAt indices state branch).flatMap fun prior =>
        (runWorldsAt (next prior.answer) prior.state prior.branch).map fun suffix =>
          { branch := suffix.branch,
            answer := sigmaPair formed universeWitness prior.answer suffix.answer,
            state := suffix.state, intents := prior.intents ++ suffix.intents } := by
  rw [sigmaProgram, runWorldsAt_map, runWorldsAt_bindSigma]
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    WorldResult.mapAnswer, WorldResult.prependIntents]

/-- Forgetting the answer's admission evidence still yields an admitted
native term at every result of the actual contextual execution. -/
theorem result_judgment {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent)
    (state : State) (branch : BranchTrace)
    (output : WorldResult State (Tm Head n) Intent)
    (retained : output ∈ runWorldsAt
      (Program.map Subtype.val (sigmaProgram formed universeWitness indices next)) state branch) :
    Judgment R Γ output.answer (.sigma A B) := by
  rw [runWorldsAt_map] at retained
  obtain ⟨typedOutput, _, equality⟩ := List.mem_map.mp retained
  subst output
  exact typedOutput.answer.property

end Effects

/-! ## A genuinely indexed native identity family -/


#print axioms rename_sigmaPair
#print axioms substitute_sigmaPair
#print axioms runWorldsAt_sigmaProgram
#print axioms result_judgment

end FormationSensitive.DependentComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
