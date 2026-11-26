import Mettapedia.Machines.TIsa.StoreInstructions.PackedEquations
import Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist

/-!
# From packed knowledge to a resumable TEST

The term and equation arrays initialize the work-list unifier.
Malformed input and an unfinished run do not return a logical
answer. A completed run gives exactly the source TEST's result
and retains the original equations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedResolution

open Mettapedia.Logic.LP
open Derivation.FiniteUnifier (Configuration Conflict Trail readTrail meaning)
open UnifierHeaders (Symbols)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def preparePacked (terms : PackedTerms.Arena) (arena : PackedEquations.Arena)
    (head : Word) (base : PackedWorklist.Words) : Option PackedWorklist.State :=
  (PackedEquations.readWords arena head).map fun newer => .working ⟨terms, base ++ newer.reverse, []⟩

def runPacked (fuel : ℕ) (terms : PackedTerms.Arena) (arena : PackedEquations.Arena)
    (head : Word) (base : PackedWorklist.Words) : Option PackedWorklist.State :=
  (preparePacked terms arena head base).bind (PackedWorklist.run fuel)

private theorem read_reverse {A B : Type*} (read : A → Option B) (keys : List A) {values : List B}
    (known : keys.mapM read = some values) : keys.reverse.mapM read = some values.reverse := by
  induction keys generalizing values with
  | nil =>
    obtain rfl := Option.some.inj known
    rfl
  | cons first rest ih =>
    rw [List.mapM_cons] at known
    obtain ⟨value, head, continued⟩ := Option.bind_eq_some_iff.mp known
    obtain ⟨tail, prior, back⟩ := Option.bind_eq_some_iff.mp continued
    obtain rfl := Option.some.inj back
    simp [List.mapM_append, ih prior, head]

theorem prepare_packed_exact [DecidableEq (Term σ)] (symbols : Symbols σ) (terms : PackedTerms.Arena)
    (arena : PackedEquations.Arena) (head : Word) (words : PackedWorklist.Words)
    (base : SymbolicExecution.Equations σ) (work : SymbolicExecution.Work σ)
    {decoded : Array (Term σ)} (interned : PackedTerms.decode symbols terms = some decoded)
    (baseRead : PackedWorklist.readEquations symbols terms words = some base)
    (held : PackedEquations.read (PackedTerms.codebook decoded) arena head = some work.newer) :
    ∃ saved, preparePacked terms arena head words = some (PackedWorklist.State.working saved) ∧
      saved.arena = terms ∧ PackedWorklist.read symbols (.working saved) =
        some (Derivation.FiniteUnifier.start (work.problem base)) := by
  have raw := PackedEquations.read_words_exact (PackedTerms.codebook decoded) arena head
  rw [held] at raw
  obtain ⟨newer, readIds, contents⟩ := Option.bind_eq_some_iff.mp raw
  have decodePair : PackedEquations.decodePair (PackedTerms.codebook decoded) =
      PackedUnifierAction.pair (PackedTerms.lookup symbols terms) := by
    funext pair
    simp only [PackedEquations.decodePair, PackedUnifierAction.pair, PackedTerms.codebook, PackedTerms.lookup,
      interned, Option.bind_some]
  have reverseRead := read_reverse _ newer contents
  rw [decodePair] at reverseRead
  have problem :
      PackedWorklist.readEquations symbols terms (words ++ newer.reverse) = some (work.problem base) := by
    unfold PackedWorklist.readEquations at baseRead ⊢
    simp [List.mapM_append, baseRead, reverseRead, SymbolicExecution.Work.problem]
  refine ⟨⟨terms, words ++ newer.reverse, []⟩, by simp [preparePacked, readIds], rfl, ?_⟩
  simp [PackedWorklist.read, problem, PackedWorklist.readTrail, Derivation.FiniteUnifier.start]

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def prepare (symbols : Symbols σ) (terms : PackedTerms.Arena) (arena : PackedEquations.Arena)
    (head : Word) (base : SymbolicExecution.Equations σ) : Option (Configuration σ) :=
  (PackedTerms.decode symbols terms).bind fun decoded =>
    (PackedEquations.Symbolic.problem (PackedTerms.codebook decoded) base arena head).map Derivation.FiniteUnifier.start

def run (fuel : ℕ) (symbols : Symbols σ) (terms : PackedTerms.Arena)
    (arena : PackedEquations.Arena) (head : Word) (base : SymbolicExecution.Equations σ) :
    Option (Configuration σ) :=
  (prepare symbols terms arena head base).map (Derivation.FiniteUnifier.run fuel)

theorem prepare_exact (symbols : Symbols σ) (terms : PackedTerms.Arena) (arena : PackedEquations.Arena)
    (head : Word) (base : SymbolicExecution.Equations σ) (work : SymbolicExecution.Work σ)
    {decoded : Array (Term σ)} (interned : PackedTerms.decode symbols terms = some decoded)
    (held : PackedEquations.read (PackedTerms.codebook decoded) arena head = some work.newer) :
    prepare symbols terms arena head base = some (Derivation.FiniteUnifier.start (work.problem base)) := by
  simp only [prepare, interned, Option.bind_some, PackedEquations.Symbolic.problem_exact _ base held, Option.map_some]

theorem run_exact (fuel : ℕ) (symbols : Symbols σ) (terms : PackedTerms.Arena) (arena : PackedEquations.Arena)
    (head : Word) (base : SymbolicExecution.Equations σ) (work : SymbolicExecution.Work σ)
    {decoded : Array (Term σ)} (interned : PackedTerms.decode symbols terms = some decoded)
    (held : PackedEquations.read (PackedTerms.codebook decoded) arena head = some work.newer) :
    run fuel symbols terms arena head base = some (Derivation.FiniteUnifier.run fuel
      (Derivation.FiniteUnifier.start (work.problem base))) := by
  simp only [run, prepare_exact symbols terms arena head base work interned held, Option.map_some]

def answer : Configuration σ → Option (Option (Subst σ))
  | .working _ => none
  | .solved written => some (some (readTrail (Subst.id σ) written))
  | .inconsistent _ => some none

def observation (outcome : Option (Configuration σ)) : Option (Option (Subst σ)) :=
  outcome.bind answer

theorem answer_exact {config : Configuration σ} {result : Option (Subst σ)}
    (done : answer config = some result) : meaning config = result := by
  cases config <;> simp_all [answer, meaning]

theorem complete (symbols : Symbols σ) (terms : PackedTerms.Arena) (arena : PackedEquations.Arena)
    (head : Word) (base : SymbolicExecution.Equations σ) (work : SymbolicExecution.Work σ)
    {decoded : Array (Term σ)} (interned : PackedTerms.decode symbols terms = some decoded)
    (held : PackedEquations.read (PackedTerms.codebook decoded) arena head = some work.newer) :
    ∃ fuel, observation (run fuel symbols terms arena head base) = some (unifyTotal (work.problem base)) := by
  obtain ⟨fuel, finished, reference⟩ := Derivation.FiniteUnifier.complete (work.problem base)
  refine ⟨fuel, ?_⟩
  rw [run_exact fuel symbols terms arena head base work interned held]
  unfold observation
  generalize state : Derivation.FiniteUnifier.run fuel (Derivation.FiniteUnifier.start (work.problem base)) = config at *
  cases config with
  | working pending => simp [Derivation.FiniteUnifier.terminal] at finished
  | solved saved => exact congrArg some reference
  | inconsistent fault => exact congrArg some reference

theorem zero_does_not_return_a_word (symbols : Symbols σ) (terms : PackedTerms.Arena)
    (arena : PackedEquations.Arena) (head : Word) (base : SymbolicExecution.Equations σ)
    (work : SymbolicExecution.Work σ) {decoded : Array (Term σ)}
    (interned : PackedTerms.decode symbols terms = some decoded)
    (held : PackedEquations.read (PackedTerms.codebook decoded) arena head = some work.newer) :
    observation (run 0 symbols terms arena head base) = none := by
  rw [run_exact 0 symbols terms arena head base work interned held]
  rfl

theorem test_returns (fuel : ℕ) (symbols : Symbols σ) (terms : PackedTerms.Arena) (arena : PackedEquations.Arena)
    (head : Word) (base : SymbolicExecution.Equations σ) (st : SymbolicExecution.Frame σ) (level : ℕ)
    (destination : P1Source.Reg) {decoded : Array (Term σ)}
    (interned : PackedTerms.decode symbols terms = some decoded)
    (held : PackedEquations.read (PackedTerms.codebook decoded) arena head = some (st.levels level).bindings.newer)
    {solution : Option (Subst σ)}
    (finished : observation (run fuel symbols terms arena head base) = some solution) :
    executeInstructionWith (SymbolicExecution.profile base).step st (.transform (.test .resolve level destination)) =
      .ok (match solution with
        | none => st.write destination 0
        | some answer =>
          let entry := st.levels level
          let updated := {entry with bindings := {entry.bindings with answer := some answer}}
          (st.setLevel level updated).write destination 1) := by
  have exact := Derivation.FiniteUnifier.start_exact fuel ((st.levels level).bindings.problem base)
  rw [run_exact fuel symbols terms arena head base (st.levels level).bindings interned held] at finished
  have solved := (answer_exact finished).symm.trans exact
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, SymbolicExecution.profile,
    SymbolicExecution.test, SymbolicExecution.resolve_exact, ← solved]
  cases solution <;> rfl

theorem packed_test_completes (symbols : Symbols σ) (terms : PackedTerms.Arena)
    (arena : PackedEquations.Arena) (head : Word) (words : PackedWorklist.Words)
    (base : SymbolicExecution.Equations σ) (st : SymbolicExecution.Frame σ) (level : ℕ)
    (destination : P1Source.Reg) {decoded : Array (Term σ)}
    (interned : PackedTerms.decode symbols terms = some decoded)
    (baseRead : PackedWorklist.readEquations symbols terms words = some base)
    (held : PackedEquations.read (PackedTerms.codebook decoded) arena head = some (st.levels level).bindings.newer)
    (fits : PackedWorklist.Reserve
      (Derivation.FiniteUnifier.stepsToFinish ⟨(st.levels level).bindings.problem base, []⟩)
      terms.nodes.size terms.children.size) :
    ∃ fuel packed result,
      runPacked fuel terms arena head words = some packed ∧ PackedWorklist.terminal packed = true ∧
      observation (PackedWorklist.read symbols packed) = some result ∧
      executeInstructionWith (SymbolicExecution.profile base).step st (.transform (.test .resolve level destination)) =
        .ok (match result with
          | none => st.write destination 0
          | some solution =>
            let entry := st.levels level
            (st.setLevel level {entry with bindings := {entry.bindings with answer := some solution}}).write destination 1) := by
  obtain ⟨saved, loaded, original, known⟩ := prepare_packed_exact symbols terms arena head words base
    (st.levels level).bindings interned baseRead held
  obtain ⟨fuel, packed, typed, ran, terminal, interpreted, same⟩ :=
    PackedWorklist.complete symbols (.working saved) _ known
      (by simpa only [PackedWorklist.nodeCount, PackedWorklist.edgeCount, original] using fits)
  have readback : observation (PackedWorklist.read symbols packed) = some (unifyTotal ((st.levels level).bindings.problem base)) := by
    have finished := (PackedWorklist.terminal_read symbols packed typed interpreted).symm.trans terminal
    rw [interpreted]
    cases typed with
    | working _ => simp [Derivation.FiniteUnifier.terminal] at finished
    | solved _ => exact congrArg some same
    | inconsistent _ => exact congrArg some same
  refine ⟨fuel, packed, _, by simp [runPacked, loaded, ran], terminal, readback, ?_⟩
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, SymbolicExecution.profile,
    SymbolicExecution.test, SymbolicExecution.resolve_exact]
  cases unifyTotal ((st.levels level).bindings.problem base) <;> rfl

namespace Examples

private def terms : PackedTerms.Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 42⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩], #[0]⟩

theorem reads_the_stored_equation_and_solves_it :
    PackedWorklist.Examples.solvedTrail (runPacked 2 terms #[⟨0, 0, 1⟩] 1 []) = some [(7, 1)] := by
  decide +kernel

theorem a_real_equation_cycle_is_an_occurs_conflict :
    PackedWorklist.Examples.conflict (runPacked 1 terms #[⟨0, 0, 2⟩] 1 []) = some .occurs := by
  decide +kernel

theorem a_damaged_chain_does_not_produce_a_logical_answer :
    (runPacked 3 terms #[⟨1, 0, 2⟩] 1 []).isNone = true := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedResolution
