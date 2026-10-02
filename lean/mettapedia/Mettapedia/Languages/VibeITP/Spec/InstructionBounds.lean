import Mettapedia.Languages.VibeITP.Spec.Instr
import Mathlib.Data.List.Basic

/-!
# Machine-word domain of certificate instructions

The protocol is specified over natural numbers. Actual binary instructions
carry bounded machine operands, including their variable-length counts. The
bound here expresses that input domain, rather than a runtime resource cap.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

def Instr.machineWords : Instr → List Nat
  | .fvarNew arity dst => [arity, dst]
  | .constNew binders dst => binders.length :: dst :: binders
  | .symbolSwap first second => [first, second]
  | .symbolFree slot => [slot]
  | .termNewBVar index dst => [index, dst]
  | .termNewLiteral bytes dst => [bytes.length, dst]
  | .termNewApp symbol arguments dst => symbol :: arguments.length :: dst :: arguments
  | .termSwap first second => [first, second]
  | .termFree slot => [slot]
  | .addAxiom statement dst => [statement, dst]
  | .thmExchange theoremSlot statement => [theoremSlot, statement]
  | .thmFree slot => [slot]
  | .thmSwap first second => [first, second]
  | .challengeAdd statement dst => [statement, dst]
  | .challengeSatisfy challenge theoremSlot => [challenge, theoremSlot]
  | .modusPonens implication premise dst => [implication, premise, dst]
  | .thmInstantiate theoremSlot fvar value dst => [theoremSlot, fvar, value, dst]
  | .defineConst fvars hints value dstSymbol dstTheorem =>
      fvars.length :: hints.length :: value :: dstSymbol :: dstTheorem :: (fvars ++ hints)
  | .litIsNat value dst => [value, dst]
  | .litLt first second dst => [first, second, dst]
  | .litAdd first second dst => [first, second, dst]
  | .litMul first second dst => [first, second, dst]
  | .litDiv first second dst => [first, second, dst]
  | .litLength term dst => [term, dst]
  | .litGet term index dst => [term, index, dst]
  | .jit safe dst dstTerm => [safe, dst, dstTerm]

def Instr.MachineBounded (instruction : Instr) : Prop :=
  ∀ word ∈ instruction.machineWords, word < wordBound

def Parser.Establishes {α : Type} (parser : Parser α) (property : α → Prop) : Prop :=
  ∀ bytes value rest, parser bytes = .ok (value, rest) → property value

theorem Parser.pure_establishes {α : Type} (value : α) (property : α → Prop)
    (valid : property value) : (pure value).Establishes property := by
  intro bytes result rest accepted
  simp only [pure, Except.ok.injEq, Prod.mk.injEq] at accepted
  rw [← accepted.1]
  exact valid

theorem Parser.bind_establishes {α β : Type} (parser : Parser α) (next : α → Parser β)
    (firstProperty : α → Prop) (resultProperty : β → Prop)
    (first : parser.Establishes firstProperty)
    (following : ∀ value, firstProperty value → (next value).Establishes resultProperty) :
    (bind parser next).Establishes resultProperty := by
  intro bytes result rest accepted
  unfold bind at accepted
  cases parsed : parser bytes with
  | error error => simp [parsed] at accepted
  | ok pair =>
    rcases pair with ⟨value, remainder⟩
    simp only [parsed] at accepted
    exact following value (first bytes value remainder parsed) remainder result rest accepted

theorem Parser.raw_establishes (count : Nat) :
    (raw count).Establishes (fun bytes => bytes.length = count) := by
  intro bytes value rest accepted
  unfold raw at accepted
  split at accepted
  · cases accepted
  · rename_i enough
    have equal : bytes.take count = value := (Prod.mk.inj (Except.ok.inj accepted)).1
    rw [← equal, List.length_take]
    exact Nat.min_eq_left (by omega)

example : Instr.MachineBounded (.litIsNat 255 0) := by
  simp [Instr.MachineBounded, Instr.machineWords, wordBound]

example : ¬ Instr.MachineBounded (.litIsNat wordBound 0) := by
  intro bounded
  have impossible := bounded wordBound (by simp [Instr.machineWords])
  exact Nat.lt_irrefl _ impossible

end Mettapedia.Languages.VibeITP.Spec
