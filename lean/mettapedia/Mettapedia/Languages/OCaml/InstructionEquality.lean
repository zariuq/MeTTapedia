import Mettapedia.Languages.OCaml.PatternEquality

/-!
# Exact executable equality for indexed OCaml instructions

The reflection theorem retains patterns, constructor identities, literal
kinds, code references and authored clause order. This is a source-reading
check for handler reuse, not a hash or an alpha-equivalence approximation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

def clauseEqual (first second : Clause) : Bool :=
  patternEqual first.pattern second.pattern && decide (first.body = second.body)

theorem clauseEqual_iff (first second : Clause) : clauseEqual first second = true ↔ first = second := by
  cases first
  cases second
  simp [clauseEqual, patternEqual_iff, Clause.mk.injEq]

def clausesEqual : List Clause → List Clause → Bool
  | [], [] => true
  | first :: rest, second :: later => clauseEqual first second && clausesEqual rest later
  | _, _ => false

theorem clausesEqual_iff (first : List Clause) : ∀ second, clausesEqual first second = true ↔ first = second := by
  induction first with
  | nil => intro second; cases second <;> simp [clausesEqual]
  | cons head rest ih =>
      intro second
      cases second <;> simp [clausesEqual, clauseEqual_iff, ih]

def instructionEqual : Instruction → Instruction → Bool
  | .literal first, .literal second => decide (first = second)
  | .variable first, .variable second => decide (first = second)
  | .lambda first body, .lambda second other => patternEqual first second && decide (body = other)
  | .apply first argument, .apply second other => decide (first = second ∧ argument = other)
  | .letValue first value body, .letValue second other next =>
      patternEqual first second && decide (value = other ∧ body = next)
  | .letRecursive first body, .letRecursive second other => decide (first = second ∧ body = other)
  | .branch test yes no, .branch other thenCode elseCode => decide (test = other ∧ yes = thenCode ∧ no = elseCode)
  | .andThen first second, .andThen other later => decide (first = other ∧ second = later)
  | .orElse first second, .orElse other later => decide (first = other ∧ second = later)
  | .tuple first, .tuple second => decide (first = second)
  | .cons head tail, .cons first rest => decide (head = first ∧ tail = rest)
  | .variant typeId constructor fields, .variant otherType otherConstructor others =>
      decide (typeId = otherType ∧ constructor = otherConstructor ∧ fields = others)
  | .matchValue scrutinee clauses, .matchValue other later => decide (scrutinee = other) && clausesEqual clauses later
  | .primitive first arguments, .primitive second others => decide (first = second ∧ arguments = others)
  | _, _ => false

theorem instructionEqual_iff (first second : Instruction) : instructionEqual first second = true ↔ first = second := by
  cases first <;> cases second <;> simp [instructionEqual, patternEqual_iff, clausesEqual_iff]

theorem instructionEqual_self (instruction : Instruction) : instructionEqual instruction instruction = true :=
  (instructionEqual_iff instruction instruction).mpr rfl

namespace InstructionEqualityControls

theorem boolean_literal_is_not_numeric_key :
    instructionEqual (.literal (.boolean true)) (.literal (.integer 1)) = false := by decide

theorem clause_order_is_part_of_instruction_identity :
    instructionEqual (.matchValue 0 [⟨.wildcard, 1⟩, ⟨.literal (.integer 0), 2⟩])
      (.matchValue 0 [⟨.literal (.integer 0), 2⟩, ⟨.wildcard, 1⟩]) = false := by decide +kernel

theorem capture_position_is_part_of_instruction_identity :
    instructionEqual (.variable 0) (.variable 1) = false := by decide

end InstructionEqualityControls

end Mettapedia.Languages.OCaml
