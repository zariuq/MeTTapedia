import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger

/-!
# Rule bodies have a finite data layout and a checked structural decoder

The layout records port counts and guard constructors. The payload retains
every term-bearing position, in the existing ruleTerms order. Decoding
consumes that payload without interpreting its terms or inventing missing
ones. A malformed payload fails; every encoded rule decodes to itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleBodySyntax

variable {T U : Type}

deriving instance DecidableEq for Check
deriving instance DecidableEq for RuleInstance

abbrev Layout := RuleInstance Unit

def layout (rule : RuleInstance T) : Layout := rule.map (fun _ => ())

def readList : List Unit → List T → Option (List T × List T)
  | [], values => some ([], values)
  | _ :: rest, value :: values => do
      let (selected, remaining) ← readList rest values
      pure (value :: selected, remaining)
  | _ :: _, [] => none

def readPairs : List (Unit × Unit) → List T → Option (List (T × T) × List T)
  | [], values => some ([], values)
  | _ :: rest, left :: right :: values => do
      let (selected, remaining) ← readPairs rest values
      pure ((left, right) :: selected, remaining)
  | _ :: _, _ => none

def readCheck : Check Unit → List T → Option (Check T × List T)
  | .equal _ _, left :: right :: values => some (.equal left right, values)
  | .absent _, value :: values => some (.absent value, values)
  | .count _ count, value :: values => some (.count value count, values)
  | _, _ => none

def readChecks : List (Check Unit) → List T → Option (List (Check T) × List T)
  | [], values => some ([], values)
  | first :: rest, values => do
      let (selected, remaining) ← readCheck first values
      let (others, final) ← readChecks rest remaining
      pure (selected :: others, final)

def parse (shape : Layout) (values : List T) : Option (RuleInstance T × List T) := do
  let (takes, rest) ← readList shape.take values
  let (reads, rest) ← readList shape.read rest
  let (tells, rest) ← readPairs shape.tell rest
  let (checks, rest) ← readChecks shape.checks rest
  let (outputs, rest) ← readList shape.produce rest
  pure (⟨takes, reads, tells, checks, outputs⟩, rest)

theorem readList_roundtrip (values tail : List T) :
    readList (values.map (fun _ => ())) (values ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, List.cons_append, readList, ih]; rfl

theorem readPairs_roundtrip (values : List (T × T)) (tail : List T) :
    readPairs (values.map (fun _ => ((), ()))) (values.flatMap (fun pair => [pair.1, pair.2]) ++ tail) =
      some (values, tail) := by
  induction values with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append, readPairs, ih]
      rfl

theorem readCheck_roundtrip (check : Check T) (tail : List T) :
    readCheck (check.map (fun _ => ())) (ContextualWorldScopeLedger.checkTerms check ++ tail) = some (check, tail) := by
  cases check <;> rfl

theorem readChecks_roundtrip (checks : List (Check T)) (tail : List T) :
    readChecks (checks.map (Check.map (fun _ => ())))
      (checks.flatMap ContextualWorldScopeLedger.checkTerms ++ tail) = some (checks, tail) := by
  induction checks with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.append_assoc, readChecks, readCheck_roundtrip]
      dsimp only [Bind.bind, Pure.pure, Option.bind]
      rw [ih]

/-- The structural source decoder returns all original ports and leaves
the caller's remaining stream untouched. -/
theorem parse_roundtrip (rule : RuleInstance T) (tail : List T) :
    parse (layout rule) (ContextualWorldScopeLedger.ruleTerms rule ++ tail) = some (rule, tail) := by
  rcases rule with ⟨takes, reads, tells, checks, outputs⟩
  simp only [parse, layout, RuleInstance.map, ContextualWorldScopeLedger.ruleTerms, List.append_assoc,
    readList_roundtrip]
  dsimp only [Bind.bind, Pure.pure, Option.bind]
  rw [readList_roundtrip]
  dsimp only [Option.bind]
  rw [readPairs_roundtrip]
  dsimp only [Option.bind]
  rw [readChecks_roundtrip]
  dsimp only [Option.bind]
  rw [readList_roundtrip]

theorem layout_map (change : T → U) (rule : RuleInstance T) : layout (rule.map change) = layout rule := by
  cases rule
  simp only [layout, RuleInstance.map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro check _
  cases check <;> rfl

theorem payload_length (rule : RuleInstance T) :
    (ContextualWorldScopeLedger.ruleTerms (layout rule)).length = (ContextualWorldScopeLedger.ruleTerms rule).length := by
  rw [layout, ContextualWorldScopeLedger.ruleTerms_map, List.length_map]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleBodySyntax
