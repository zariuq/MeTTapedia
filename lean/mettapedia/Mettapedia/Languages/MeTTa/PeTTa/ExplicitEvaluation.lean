import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences

/-!
# Explicit evaluation and translation-time callability

For the finite first-order fragment, source evaluation retains the call/data
classification of each occurrence. Direct dispatch changes only the root;
evaluation as code reclassifies every application in the current program.
These are different translations, even when every term is closed. `value`
denotes an opaque literal, not a variable-held expression to reinterpret.
The dispatch mode models direct calls and the admitted, callable part of
`reduce`; dynamic dispatch of an unknown head is outside this fragment.

The instruction language separates construction from application. The
compiler theorem preserves the complete answer list, hence multiplicities.
This models the evaluation boundary, not PeTTa's error handlers, effects,
quotation, variable substitution, or recursive equation execution.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ValueOccurrences (choices Program)

inductive Term where
  | value : Atom → Term
  | application : Bool → List Term → Term

def Term.syntax : Term → Atom
  | .value a => a
  | .application _ ts => .expression (syntaxList ts)
where
  syntaxList : List Term → List Atom
    | [] => []
    | t :: ts => Term.syntax t :: syntaxList ts

inductive Mode where
  | source
  | dispatch
  | code
  deriving DecidableEq

/-- Only code evaluation changes the interpretation of nested occurrences. -/
def childMode : Mode → Mode
  | .code => .code
  | _ => .source

def isCall (P : Program) (mode : Mode) (captured : Bool) (ts : List Term) : Bool :=
  match mode with
  | .source => captured
  | .dispatch => true
  | .code => P.isCall (Term.syntax.syntaxList ts)

/-- A denotational evaluator over source occurrences and their captured roles. -/
def evaluate (P : Program) (mode : Mode) : Term → List Atom
  | .value a => [a]
  | .application captured ts =>
      (choices (evaluateList P (childMode mode) ts)).flatMap fun args =>
        if isCall P mode captured ts then P.answers args else [.expression args]
where
  evaluateList (P : Program) (mode : Mode) : List Term → List (List Atom)
    | [] => []
    | t :: ts => evaluate P mode t :: evaluateList P mode ts

inductive Instruction where
  | literal : Atom → Instruction
  | construct : List Instruction → Instruction
  | apply : List Instruction → Instruction

/-- Execution does no callability classification. That decision is compiled. -/
def execute (P : Program) : Instruction → List Atom
  | .literal a => [a]
  | .construct code => (choices (executeList P code)).map Atom.expression
  | .apply code => (choices (executeList P code)).flatMap P.answers
where
  executeList (P : Program) : List Instruction → List (List Atom)
    | [] => []
    | i :: code => execute P i :: executeList P code

def compile (P : Program) (mode : Mode) : Term → Instruction
  | .value a => .literal a
  | .application captured ts =>
      let children := compileList P (childMode mode) ts
      if isCall P mode captured ts then .apply children else .construct children
where
  compileList (P : Program) (mode : Mode) : List Term → List Instruction
    | [] => []
    | t :: ts => compile P mode t :: compileList P mode ts

/-- Compiling each of the three evaluation boundaries preserves occurrences. -/
theorem execute_compile (P : Program) (mode : Mode) (t : Term) :
    execute P (compile P mode t) = evaluate P mode t := by
  match t with
  | .value a => rfl
  | .application captured ts =>
    have children := list P (childMode mode) ts
      (fun t _ => execute_compile P (childMode mode) t)
    by_cases call : isCall P mode captured ts = true
    · simp [compile, evaluate, call, execute, children]
    · simpa [compile, evaluate, call, execute, children] using
        (List.map_eq_flatMap (f := Atom.expression)
          (l := choices (evaluate.evaluateList P (childMode mode) ts)))
termination_by sizeOf t
where
  list (P : Program) (mode : Mode) (ts : List Term)
      (ih : ∀ t ∈ ts, execute P (compile P mode t) = evaluate P mode t) :
      execute.executeList P (compile.compileList P mode ts) =
        evaluate.evaluateList P mode ts := by
    induction ts with
    | nil => rfl
    | cons t ts tail =>
      simp only [compile.compileList, execute.executeList, evaluate.evaluateList]
      rw [ih t (by simp), tail (fun t h => ih t (by simp [h]))]

namespace Examples

def current : Program where
  isCall
    | .symbol "identity" :: _ => true
    | .symbol "late" :: _ => true
    | _ => false
  answers
    | [.symbol "identity", a] => [a]
    | [.symbol "late"] => [.symbol "answer", .symbol "answer"]
    | _ => []

def late : Term := .application false [.value (.symbol "late")]
def nested : Term := .application true [.value (.symbol "identity"), late]

theorem old_data_stays_data :
    execute current (compile current .source late) =
      [.expression [.symbol "late"]] := by decide

theorem dispatch_uses_current_definition :
    execute current (compile current .dispatch late) =
      [.symbol "answer", .symbol "answer"] := by decide

theorem dispatch_preserves_argument_roles :
    execute current (compile current .dispatch nested) =
      [.expression [.symbol "late"]] := by decide

theorem code_reclassifies_nested_occurrences :
    execute current (compile current .code nested) =
      [.symbol "answer", .symbol "answer"] := by decide

theorem dispatch_is_not_source :
    evaluate current .dispatch late ≠ evaluate current .source late := by decide

theorem code_is_not_dispatch :
    evaluate current .code nested ≠ evaluate current .dispatch nested := by decide

end Examples
end Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation
