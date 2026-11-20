import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimedOutcomes

/-!
# A moded clause as a tcalc rule module

The clause carrier here is **after constructor encoding and mode
splitting**. It retains the input call and output tuple of every
intensional relation, and its separate extensional premises. The source
meaning is the least interpretation closed under the clauses. It is not
defined by running the compiled module.

There is one module rule per clause. The existing module reader supplies
its demand, stage, and value rules. Only the result of a completed run
is compared; this is neither an evaluation-order equation nor a native
compiler proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.ModedRuleModule

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
  (ModuleRule Premise readingSignature RangeRestricted Derives Demanded)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
  (Propagates DisciplinedStep TerminalWith)

universe u v

structure CallRow (ρ : LPSignature) where
  input : Term ρ
  output : Term ρ

namespace CallRow

variable {ρ : LPSignature}

def instantiate (row : CallRow ρ) (θ : Subst ρ) : Term ρ × Term ρ :=
  (θ.applyTerm row.input, θ.applyTerm row.output)

end CallRow

inductive BodyLiteral (ρ : LPSignature) where
  | intensional (row : CallRow ρ)
  | extensional (atom : Atom ρ)

structure Clause (ρ : LPSignature) where
  head : CallRow ρ
  body : List (BodyLiteral ρ)

variable {ρ : LPSignature} {L : Type v}

def lowerLiteral : BodyLiteral ρ → Premise ρ
  | .intensional row => .call row.input row.output
  | .extensional atom => .query atom

def lower (clauses : L → Clause ρ) (label : L) : ModuleRule ρ :=
  ⟨(clauses label).head.input, (clauses label).body.map lowerLiteral, (clauses label).head.output⟩

def literalHolds (facts : Set (Atom ρ)) (interpretation : Set (Term ρ × Term ρ))
    (θ : Subst ρ) : BodyLiteral ρ → Prop
  | .intensional row => row.instantiate θ ∈ interpretation
  | .extensional atom => θ.applyAtom atom ∈ facts

/-- A model of the source clauses must contain every conclusion of an
instance whose premises hold. Extensional facts are fixed separately. -/
def Closed (clauses : L → Clause ρ) (facts : Set (Atom ρ))
    (interpretation : Set (Term ρ × Term ρ)) : Prop :=
  ∀ label θ, (∀ p ∈ (clauses label).body, literalHolds facts interpretation θ p) →
    (clauses label).head.instantiate θ ∈ interpretation

def Least (clauses : L → Clause ρ) (facts : Set (Atom ρ)) (row : Term ρ × Term ρ) : Prop :=
  ∀ interpretation, Closed clauses facts interpretation → row ∈ interpretation

private theorem compiled_derivations_closed (clauses : L → Clause ρ) (facts : Set (Atom ρ)) :
    Closed clauses facts {row | Derives (lower clauses) facts row.1 row.2} := by
  intro label θ premises
  apply Derives.rule label θ
  · intro source target inside
    obtain ⟨literal, member, lowered⟩ := List.mem_map.mp inside
    cases literal with
    | extensional atom => cases lowered
    | intensional row =>
        cases row
        cases lowered
        exact premises _ member
  · intro atom inside
    obtain ⟨literal, member, lowered⟩ := List.mem_map.mp inside
    cases literal with
    | intensional row => cases lowered
    | extensional value =>
        cases lowered
        exact premises _ member

/-- Proof trees of the emitted module and membership in the least
source model agree on the split call/result pair. -/
theorem derives_iff_least (clauses : L → Clause ρ) (facts : Set (Atom ρ)) (input output : Term ρ) :
    Derives (lower clauses) facts input output ↔ Least clauses facts (input, output) := by
  constructor
  · intro derives interpretation closed
    induction derives with
    | rule label θ calls queries ih =>
        apply closed label θ
        intro literal member
        have retained : lowerLiteral literal ∈ (lower clauses label).premises :=
          List.mem_map.mpr ⟨literal, member, rfl⟩
        cases literal with
        | intensional row => exact ih _ _ retained
        | extensional atom => exact queries _ retained
  · intro least
    exact least _ (compiled_derivations_closed clauses facts)

section Every

variable {σ : LPSignature.{0,0,0,0}} {Labels : Type} [Fintype Labels] [DecidableEq Labels]
  [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.relationSymbols]
  [DecidableEq σ.functionSymbols]

local notation "Signature" => readingSignature σ Labels
local notation "Answers" => Finset (Term Signature)

omit [Fintype Labels] [DecidableEq Labels] [DecidableEq σ.constants]
  [DecidableEq σ.relationSymbols] [DecidableEq σ.functionSymbols] in
theorem module_propagates (clauses : Labels → Clause Signature)
    (modeSafe : ∀ label, RangeRestricted (lower clauses label)) :
    ∀ rule ∈ ModuleReading.reading (lower clauses), Propagates rule :=
  ModuleReading.reading_propagates modeSafe

/-- The actual quantified every-step run reads the least source model at
the initial demanded call. The explicit hypotheses are those of the
existing set-store module reader. -/
theorem completed_every_answers (slots : σ.vars ≃ Nat) (timing : SetStore.AskTiming)
    (clauses : Labels → Clause Signature) (facts : Finset (Atom Signature))
    (modeSafe : ∀ label, RangeRestricted (lower clauses label))
    (input output : Term Signature) (ground : input.isGround)
    (factsGround : ∀ atom ∈ facts, atom.isGround) {outcome : Answers}
    (run : Relation.ReflTransGen
      (SetStoreSyntax.QuantifiedStep .every timing (ModuleReading.reading (lower clauses)))
      (ModuleReading.seed input facts) outcome)
    (finished : SetStoreSyntax.QuantifiedTerminal .every timing
      (ModuleReading.reading (lower clauses)) outcome) :
    ModuleReading.valueRow input output ∈ outcome ↔ Least clauses facts (input, output) := by
  have noTell := fun rule member => (module_propagates clauses modeSafe rule member).noTell
  have ordinaryRun := (SetStoreSyntax.quantified_run_iff_of_no_tells noTell).mp run
  have ordinaryTerminal := (SetStoreSyntax.quantified_terminal_iff_of_no_tells noTell).mp finished
  have answers := (ModuleReading.terminal_run_rows slots .every timing modeSafe ground factsGround
    ordinaryRun ordinaryTerminal (by intro impossible; cases impossible)).2 input output
  exact (answers.trans (and_iff_right Demanded.seed)).trans (derives_iff_least clauses facts input output)

/-- Completed schedules of a propagation-safe compiled module agree.
This uses the existing completed-outcome theorem, not a new scheduler. -/
theorem compiled_completed_outcomes_agree (slots : σ.vars ≃ Nat)
    (clauses : Labels → Clause Signature) (modeSafe : ∀ label, RangeRestricted (lower clauses label))
    (input : Term Signature) (facts : Finset (Atom Signature)) (ground : input.isGround)
    (factsGround : ∀ atom ∈ facts, atom.isGround)
    (first second : SetStoreSyntax.Discipline) (leftTiming rightTiming : SetStore.AskTiming)
    {left right : Answers}
    (runLeft : Relation.ReflTransGen
      (DisciplinedStep first leftTiming (ModuleReading.reading (lower clauses)))
      (ModuleReading.seed input facts) left)
    (runRight : Relation.ReflTransGen
      (DisciplinedStep second rightTiming (ModuleReading.reading (lower clauses)))
      (ModuleReading.seed input facts) right)
    (endLeft : TerminalWith first leftTiming (ModuleReading.reading (lower clauses)) left)
    (endRight : TerminalWith second rightTiming (ModuleReading.reading (lower clauses)) right)
    (uniqueLeft : first = .unique → SetStoreSyntax.Determinate
      (P := ModuleReading.reading (lower clauses)) left)
    (uniqueRight : second = .unique → SetStoreSyntax.Determinate
      (P := ModuleReading.reading (lower clauses)) right) : left = right :=
  SetStoreSyntax.completed_outcomes_agree (signature := Signature)
    (P := ModuleReading.reading (lower clauses)) slots first second leftTiming rightTiming
    (module_propagates clauses modeSafe) (ModuleReading.readingRules (lower clauses))
    ModuleReading.readingRules_covers (ModuleReading.seed_ground ground factsGround)
    runLeft runRight endLeft endRight uniqueLeft uniqueRight

end Every

#print axioms derives_iff_least
#print axioms module_propagates
#print axioms completed_every_answers
#print axioms compiled_completed_outcomes_agree

end Mettapedia.GSLT.Compilation.ModedRuleModule
