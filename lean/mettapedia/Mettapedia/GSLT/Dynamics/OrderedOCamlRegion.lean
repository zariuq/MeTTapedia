import Mettapedia.Languages.OCaml.CompiledDispatch
import Mettapedia.Languages.OCaml.LiveCompiledDispatch
import Mettapedia.Languages.OCaml.MachineCompleteness
import Mettapedia.Languages.OCaml.TreeEvaluationEquivalence
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Ordered OCaml/CEK regions in the generic portfolio

The worker uses prepared instruction handlers and ordered constructor screens.
The page observer retains the full result, including pending environments and
continuations. A stronger observer also retains every visited machine state.
No join reordering, saturation or final-value quotient is used here.

Finite completion connects to the independent source evaluation and expression
tree judgments. The imported LanguageDef/emitted realization is a separate
implementation of those judgments, not the definition of their meaning.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified.OrderedOCaml

open Mettapedia.Languages.OCaml

inductive Observer | page | trace

abbrev Input := Nat × MachineState

def Answer : Observer → Type
  | .page => RunResult
  | .trace => RunResult × List MachineState

def questions (observer : Observer) : RegionObservations.Family (Answer observer) where
  Question := Answer observer → Bool
  Answer _ := Bool
  read question value := question value

def reference (program : Program) : (observer : Observer) → Input → Answer observer
  | .page, input => Mettapedia.Languages.OCaml.run program input.1 input.2
  | .trace, input => (Mettapedia.Languages.OCaml.run program input.1 input.2,
      CompiledDispatch.referenceTrace program input.1 input.2)

def boundary (program : Program) (observer : Observer) :
    Boundary Input (Answer observer) (Answer observer) where
  source := reference program observer
  summarize := id
  future := questions observer
  sufficient _ _ same question := congrArg question same

def worker (program : Program) : (observer : Observer) → Input → Answer observer
  | .page, input => CompiledDispatch.run program (CompiledDispatch.prepare program) input.1 input.2
  | .trace, input => (CompiledDispatch.run program (CompiledDispatch.prepare program) input.1 input.2,
      CompiledDispatch.trace program (CompiledDispatch.prepare program) input.1 input.2)

theorem worker_exact (program : Program) (observer : Observer) (input : Input) :
    worker program observer input = reference program observer input := by
  cases observer <;> simp only [worker, reference, CompiledDispatch.run_exact, CompiledDispatch.trace_exact]
  all_goals rfl

def region (program : Program) (observer : Observer) : CertifiedRegion (boundary program observer) Nat where
  regime := 0
  Artifact := Answer observer
  attempt input := .committed (worker program observer input)
  decode := id
  restores _ _ impossible := by cases impossible
  exact input _ committed := by cases committed; exact worker_exact program observer input

def liveRegion (saved current : Program) : CertifiedRegion (boundary current .page) Nat where
  regime := 1
  Artifact := RunResult
  attempt input := .committed (LiveCompiledDispatch.run saved current input.1 input.2)
  decode := id
  restores _ _ impossible := by cases impossible
  exact input _ committed := by
    cases committed
    exact LiveCompiledDispatch.run_exact saved current input.1 input.2

/-- Ranking can choose fresh specialization or read-qualified reuse of an
older table, but both retain the same complete current-program page. -/
def portfolio (saved current : Program) (freshCost liveCost : Input → Estimate) :
    List (Candidate (boundary current .page) Nat) :=
  [⟨region current .page, freshCost, 0⟩, ⟨liveRegion saved current, liveCost, 1⟩]

theorem portfolio_exact (saved current : Program) (freshCost liveCost : Input → Estimate) (input : Input) :
    RegionPortfolio.execute input (portfolio saved current freshCost liveCost) =
      Mettapedia.Languages.OCaml.run current input.1 input.2 := by
  exact RegionPortfolio.execute_exact input _

/-- Every caller of the exact page sees the same pending state, invalid
instruction report or completed value as the source machine. -/
theorem page_continuation (program : Program) (input : Input) {Result : Type}
    (continuation : RunResult → Result) :
    continuation ((region program .page).execute input) =
      continuation (Mettapedia.Languages.OCaml.run program input.1 input.2) := by
  rw [CertifiedRegion.execute_eq_reference]
  rfl

theorem split_pages (program : Program) (first later : Nat) (state : MachineState) :
    CompiledDispatch.resume program (CompiledDispatch.prepare program) later (worker program .page (first, state)) =
      reference program .page (first + later, state) :=
  CompiledDispatch.pages_exact program first later state

theorem source_evaluation_iff (program : Program) (result : Result) :
    Evaluates program [] program.entry result ↔
      ∃ budget, worker program .page (budget, begin program) = .complete result := by
  simp only [worker, CompiledDispatch.run_exact]
  exact evaluates_iff_completed_run

/-- The independent tree judgment, including closures and compound values,
is connected through the existing exact tree/indexed result relation. -/
theorem tree_evaluation_iff (program : Program) (tree : ExpressionTree)
    (read : ExpressionTree.Reads program.code tree program.entry) (result : TreeResult) :
    TreeEvaluates program.constructors [] tree result ↔
      ∃ actual budget, worker program .page (budget, begin program) = .complete actual ∧
        TreeResultRelated program.code result actual := by
  rw [Mettapedia.Languages.OCaml.tree_evaluation_iff program read (TreeValuesRelated.nil) result]
  constructor
  · rintro ⟨actual, evaluated, related⟩
    obtain ⟨budget, completed⟩ := (source_evaluation_iff program actual).mp evaluated
    exact ⟨actual, budget, completed, related⟩
  · rintro ⟨actual, budget, completed, related⟩
    exact ⟨actual, (source_evaluation_iff program actual).mpr ⟨budget, completed⟩, related⟩

theorem live_refusal_restores_page (program : Program) (observer : Observer)
    (enabled : Input → Bool) (input : Input) (declined : enabled input = false) :
    ((region program observer).restrict enabled).attempt input = .declined input :=
  CertifiedRegion.restrict_refusal _ enabled input declined

end Mettapedia.GSLT.Dynamics.ObservationQualified.OrderedOCaml
