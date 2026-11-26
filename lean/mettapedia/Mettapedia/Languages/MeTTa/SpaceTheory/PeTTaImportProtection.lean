import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution

/-!
# Protecting a PeTTa definition during import

For ordinary PeTTa, application reads the ordered function definitions
of its head, and argument demand also reads matching type assignments.
These finite projections give a sufficient protection test, including
the previously absent case. An explicit equational request has the
additional congruence dependency and is not covered by this test.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaImportProtection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open SpaceSemantics (Program Equation)
open PeTTaExecution (programAt programAt_exact)

def definitions (program : Program) (head : String) : List Equation :=
  program.equations.filter (·.head == head)

def formalFor (head : String) : Atom → Bool
  | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: _)] => name == head
  | _ => false

def assignments (program : Program) (head : String) : List Atom :=
  program.declarations.filter (formalFor head)

def view (program : Program) (head : String) : List Equation × List Atom :=
  (definitions program head, assignments program head)

private theorem any_iff (program : Program) (head : String) :
    program.equations.any (·.head == head) = true ↔ (definitions program head).isEmpty = false := by
  unfold definitions
  induction program.equations with
  | nil => simp
  | cons first rest ih =>
    by_cases same : first.head = head <;> simp [same, ih]

theorem clauses_from_definitions (first second : Program) (head : String)
    (same : definitions first head = definitions second head) (values : List Atom) :
    Eval.clauses first head values = Eval.clauses second head values := by
  let select : Equation → Option Eval.Control := fun equation =>
    (SpaceSemantics.matchValue.matchValues [] equation.arguments values).map
      (fun bindings => .evaluate bindings equation.body)
  have selections (source : List Equation) :
      source.filterMap (fun equation => if equation.head = head then select equation else none) =
        (source.filter (·.head == head)).filterMap select := by
    induction source with
    | nil => rfl
    | cons first rest ih =>
      by_cases same : first.head = head <;> simp [List.filterMap_cons, same, ih]
  change first.equations.filterMap (fun equation => if equation.head = head then select equation else none) =
    second.equations.filterMap (fun equation => if equation.head = head then select equation else none)
  rw [selections, selections]
  exact congrArg (·.filterMap select) same

theorem arities_from_definitions (first second : Program) (head : String)
    (same : definitions first head = definitions second head) :
    Eval.arities first head = Eval.arities second head :=
  congrArg (·.map (·.arguments.length)) same

private theorem application_from_definitions (first second : Program) (head : String)
    (same : definitions first head = definitions second head) (values : List Atom) :
    Eval.application first head values = Eval.application second head values := by
  have selected := clauses_from_definitions first second head same values
  have arities : Eval.arities first head = Eval.arities second head :=
    arities_from_definitions first second head same
  have known : Eval.knownArities first head = Eval.knownArities second head :=
    congrArg (·.foldr Eval.insertArity []) arities
  unfold Eval.application
  rw [selected, arities, known]

private theorem literal_assignment_membership (first second : Program) (head : String)
    (same : assignments first head = assignments second head) (types : List Atom) :
    let declaration := Atom.expression [.symbol ":", .symbol head, .expression (.symbol "->" :: types)]
    declaration ∈ first.declarations ↔ declaration ∈ second.declarations := by
  let declaration := Atom.expression [.symbol ":", .symbol head, .expression (.symbol "->" :: types)]
  have appropriate : formalFor head declaration = true := by simp [formalFor, declaration]
  constructor
  · intro member
    have viewed : declaration ∈ assignments first head := List.mem_filter.mpr ⟨member, appropriate⟩
    rw [same] at viewed
    exact (List.mem_filter.mp viewed).1
  · intro member
    have viewed : declaration ∈ assignments second head := List.mem_filter.mpr ⟨member, appropriate⟩
    rw [← same] at viewed
    exact (List.mem_filter.mp viewed).1

private theorem demand_from_assignments (first second : Program) (head : String)
    (same : assignments first head = assignments second head) (position : Nat) :
    Eval.argumentIsRaw first head position = Eval.argumentIsRaw second head position := by
  cases native : StdLib.known head with
  | true => simp [Eval.argumentIsRaw, native]
  | false =>
    apply Bool.eq_iff_iff.mpr
    rw [Eval.argumentIsRaw_iff_declaredAtom first head position native,
      Eval.argumentIsRaw_iff_declaredAtom second head position native]
    constructor
    · rintro ⟨types, stored, demanded⟩
      exact ⟨types, (literal_assignment_membership first second head same types).mp stored, demanded⟩
    · rintro ⟨types, stored, demanded⟩
      exact ⟨types, (literal_assignment_membership first second head same types).mpr stored, demanded⟩

theorem protects_queries {first second : Program} {allowed : String → Bool}
    (same : ∀ head, allowed head = true → view first head = view second head) :
    Eval.ProgramAgreementOn allowed first second := by
  constructor
  · intro head admitted
    have sameDefinitions : definitions first head = definitions second head := congrArg Prod.fst (same head admitted)
    apply Bool.eq_iff_iff.mpr
    rw [any_iff, any_iff, sameDefinitions]
  · intro head position admitted
    exact demand_from_assignments first second head (congrArg Prod.snd (same head admitted)) position
  · intro head values admitted
    exact application_from_definitions first second head (congrArg Prod.fst (same head admitted)) values

theorem append_view (first second : Program) (head : String) :
    view (first.append second) head =
      ((view first head).1 ++ (view second head).1, (view first head).2 ++ (view second head).2) := by
  simp only [view, definitions, assignments, Program.append, List.filter_append]

/-- This law is for the emitted declaration contribution, not for
execution of the importing module's initializers. -/
theorem unrelated_declarations_protect (base contributed : List Atom) (allowed : String → Bool)
    (untouched : ∀ head, allowed head = true → view (programAt contributed) head = ([], [])) :
    Eval.ProgramAgreementOn allowed (programAt base) (programAt (base ++ contributed)) := by
  apply protects_queries
  intro head allowedHead
  rw [PeTTaExecution.declaration_contributions_compose, append_view, untouched head allowedHead]
  simp

section Controls

private def localFunction : Atom := .expression
  [.symbol "=", .expression [.symbol "held", .var "x"], .var "x"]
private def otherFunction : Atom := .expression
  [.symbol "=", .expression [.symbol "other", .var "x"], .var "x"]
private def assignRaw : Atom := .expression
  [.symbol ":", .symbol "held", .expression [.symbol "->", .symbol "Atom", .symbol "Atom"]]
private def onlyHeld (head : String) : Bool := head == "held"

theorem unrelated_function_protects :
    Eval.ProgramAgreementOn onlyHeld (programAt [localFunction]) (programAt [localFunction, otherFunction]) := by
  exact unrelated_declarations_protect [localFunction] [otherFunction] onlyHeld (by
    intro head admitted
    obtain rfl : head = "held" := of_decide_eq_true admitted
    rw [programAt_exact]
    rfl)

theorem identical_definitions_do_not_protect_new_demand :
    definitions (programAt [localFunction]) "held" = definitions (programAt [localFunction, assignRaw]) "held" ∧
      ¬ Eval.ProgramAgreementOn onlyHeld (programAt [localFunction]) (programAt [localFunction, assignRaw]) := by
  refine ⟨?_, ?_⟩
  · simp only [programAt_exact]
    rfl
  · intro claimed
    have same := claimed.demand "held" 0 rfl
    rw [programAt_exact, programAt_exact] at same
    exact (by decide +kernel : Eval.argumentIsRaw (SpaceSemantics.index [localFunction]) "held" 0 ≠
      Eval.argumentIsRaw (SpaceSemantics.index [localFunction, assignRaw]) "held" 0) same

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaImportProtection
