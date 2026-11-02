import Mettapedia.Languages.OCaml.TreeValueCorrespondence
import Mettapedia.Languages.OCaml.TreePatternMatching
import Mettapedia.Languages.OCaml.PatternMatching

/-! Both successful bindings and failure are preserved by code allocation.
Clause correspondence retains the first successful clause and its body. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

inductive TreeMatchRelated (arena : Array Instruction) : Option (List TreeValue) → Option (List Value) → Prop where
  | none : TreeMatchRelated arena none none
  | some {trees values} (bindings : TreeValuesRelated arena trees values) : TreeMatchRelated arena (some trees) (some values)

private theorem TreeMatchRelated.append {arena : Array Instruction}
    {first rest : Option (List TreeValue)} {head tail : Option (List Value)}
    (front : TreeMatchRelated arena first head) (back : TreeMatchRelated arena rest tail) :
    TreeMatchRelated arena (do pure ((← first) ++ (← rest))) (do pure ((← head) ++ (← tail))) := by
  cases front <;> cases back <;> simp only [bind, Option.bind, pure]
  · exact .none
  · exact .none
  · exact .none
  · exact .some (TreeValuesRelated.append ‹_› ‹_›)

mutual
  theorem matchTreePattern_related {arena : Array Instruction} (pattern : MatchPattern)
      {tree : TreeValue} {value : Value} (related : TreeValueRelated arena tree value) :
      TreeMatchRelated arena (matchTreePattern pattern tree) (matchPattern pattern value) := by
    cases pattern with
    | bind => exact .some (.cons related .nil)
    | wildcard => exact .some .nil
    | literal expected =>
        cases related <;> simp only [matchTreePattern, matchPattern]
        case literal actual => split <;> first | exact .some .nil | exact .none
        all_goals exact .none
    | tuple patterns =>
        cases related <;> simp only [matchTreePattern, matchPattern]
        case tuple fields => exact matchTreeFields_related patterns fields
        all_goals exact .none
    | cons head tail =>
        cases related <;> simp only [matchTreePattern, matchPattern]
        case cons front back =>
          exact (matchTreePattern_related head front).append (matchTreePattern_related tail back)
        all_goals exact .none
    | variant typeId constructor patterns =>
        cases related <;> simp only [matchTreePattern, matchPattern]
        case variant fields =>
          split
          · exact matchTreeFields_related patterns fields
          · exact .none
        all_goals exact .none
    termination_by sizeOf pattern

  theorem matchTreeFields_related {arena : Array Instruction} (patterns : List MatchPattern)
      {trees : List TreeValue} {values : List Value} (related : TreeValuesRelated arena trees values) :
      TreeMatchRelated arena (matchTreeFields patterns trees) (matchFields patterns values) := by
    cases patterns with
    | nil => cases related <;> first | exact .some .nil | exact .none
    | cons pattern rest =>
        cases related with
        | nil => exact .none
        | cons head tail =>
            exact (matchTreePattern_related pattern head).append (matchTreeFields_related rest tail)
    termination_by sizeOf patterns
end

theorem TreeMatchRelated.failure_iff {arena : Array Instruction}
    {trees : Option (List TreeValue)} {values : Option (List Value)} (related : TreeMatchRelated arena trees values) :
    trees = Option.none ↔ values = Option.none := by cases related <;> simp

theorem TreeMatchRelated.success {arena : Array Instruction}
    {trees : Option (List TreeValue)} {values : Option (List Value)} (related : TreeMatchRelated arena trees values)
    {bindings : List TreeValue} (matched : trees = Option.some bindings) :
    ∃ actual, values = Option.some actual ∧ TreeValuesRelated arena bindings actual := by
  cases related with
  | none => cases matched
  | some fields => cases matched; exact ⟨_, rfl, fields⟩

theorem TreeMatchRelated.success_back {arena : Array Instruction}
    {trees : Option (List TreeValue)} {values : Option (List Value)} (related : TreeMatchRelated arena trees values)
    {bindings : List Value} (matched : values = Option.some bindings) :
    ∃ actual, trees = Option.some actual ∧ TreeValuesRelated arena actual bindings := by
  cases related with
  | none => cases matched
  | some fields => cases matched; exact ⟨_, rfl, fields⟩

inductive TreeClauseRelated (arena : Array Instruction) :
    Option (ExpressionTree × List TreeValue) → Option (Code × List Value) → Prop where
  | absent : TreeClauseRelated arena none none
  | selected {body code trees values} (read : ExpressionTree.Reads arena body code)
      (bindings : TreeValuesRelated arena trees values) :
      TreeClauseRelated arena (some (body, trees)) (some (code, values))

theorem selectTreeClause_related {arena : Array Instruction} {trees : List (MatchPattern × ExpressionTree)}
    {clauses : List Clause} (read : ExpressionTree.ClausesRead arena trees clauses)
    {tree : TreeValue} {value : Value} (related : TreeValueRelated arena tree value) :
    TreeClauseRelated arena (selectTreeClause trees tree) (selectClause clauses value) := by
  induction trees generalizing clauses with
  | nil => cases read; exact .absent
  | cons clause rest ih =>
    cases read with
    | @cons pattern body rest code clauses head tail =>
      have matching := matchTreePattern_related pattern related
      cases found : matchTreePattern pattern tree with
      | none =>
          have failed := matching.failure_iff.mp found
          simpa only [selectTreeClause, selectClause, found, failed] using ih tail
      | some bindings =>
          obtain ⟨values, matched, aligned⟩ := matching.success found
          simp only [selectTreeClause, selectClause, found, matched]
          exact .selected head aligned

theorem TreeClauseRelated.failure_iff {arena : Array Instruction}
    {trees : Option (ExpressionTree × List TreeValue)} {values : Option (Code × List Value)}
    (related : TreeClauseRelated arena trees values) : trees = none ↔ values = none := by cases related <;> simp

theorem TreeClauseRelated.success {arena : Array Instruction}
    {trees : Option (ExpressionTree × List TreeValue)} {values : Option (Code × List Value)}
    (related : TreeClauseRelated arena trees values) {body : ExpressionTree} {bindings : List TreeValue}
    (selected : trees = some (body, bindings)) :
    ∃ code actual, values = some (code, actual) ∧ ExpressionTree.Reads arena body code ∧ TreeValuesRelated arena bindings actual := by
  cases related with
  | absent => cases selected
  | selected read fields => cases selected; exact ⟨_, _, rfl, read, fields⟩

theorem TreeClauseRelated.success_back {arena : Array Instruction}
    {trees : Option (ExpressionTree × List TreeValue)} {values : Option (Code × List Value)}
    (related : TreeClauseRelated arena trees values) {code : Code} {bindings : List Value}
    (selected : values = some (code, bindings)) :
    ∃ body actual, trees = some (body, actual) ∧ ExpressionTree.Reads arena body code ∧ TreeValuesRelated arena actual bindings := by
  cases related with
  | absent => cases selected
  | selected read fields => cases selected; exact ⟨_, _, rfl, read, fields⟩

end Mettapedia.Languages.OCaml
