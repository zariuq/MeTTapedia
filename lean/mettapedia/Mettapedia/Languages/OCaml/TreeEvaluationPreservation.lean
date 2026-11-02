import Mettapedia.Languages.OCaml.TreeMatchingCorrespondence
import Mettapedia.Languages.OCaml.TreeRecursiveCorrespondence
import Mettapedia.Languages.OCaml.TreePrimitiveCorrespondence
import Mettapedia.Languages.OCaml.Evaluation

/-! Finite tree evaluations are realized by every instruction-graph reading,
with related environments and closure results. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

private theorem chooseRead {arena : Array Instruction} {yes no : ExpressionTree} {yesCode noCode : Code}
    (choice : Bool) (positive : ExpressionTree.Reads arena yes yesCode) (negative : ExpressionTree.Reads arena no noCode) :
    ExpressionTree.Reads arena (if choice then yes else no) (if choice then yesCode else noCode) := by
  cases choice <;> assumption

mutual
  theorem TreeEvaluates.toIndexed (program : Program) {environment : TreeEnvironment}
      {tree : ExpressionTree} {result : TreeResult} (evaluated : TreeEvaluates program.constructors environment tree result)
      {code : Code} (read : ExpressionTree.Reads program.code tree code)
      {values : Environment} (captures : TreeValuesRelated program.code environment values) :
      ∃ actual, Evaluates program values code actual ∧ TreeResultRelated program.code result actual :=
    match evaluated with
    | .literal => by cases read with | literal row => exact ⟨_, .literal row, .value (.literal _)⟩
    | .variable found => by
        cases read with
        | «variable» row =>
            obtain ⟨value, selected, aligned⟩ := captures.getElem? _ found
            exact ⟨_, .variable row selected, .value aligned⟩
    | .lambda => by
        cases read with
        | lambda row child => exact ⟨_, .lambda row, .value (.lambda (.lambda row child) captures)⟩
    | .recursive continued => by
        cases read with
        | letRecursive row functions child =>
            obtain ⟨actual, body, aligned⟩ := continued.toIndexed program child (captures.recursiveEnvironment row functions child)
            exact ⟨actual, .recursive row body, aligned⟩
    | .argumentFault argument => by
        cases read with
        | apply row function child =>
            have body := TreeResultRelated.faultWitness (argument.toIndexed program child captures)
            exact ⟨_, .argumentFault row body, .fault _⟩
    | .functionFault argument function => by
        cases read with
        | apply row first second =>
            obtain ⟨_, last, _⟩ := TreeResultRelated.valueWitness (argument.toIndexed program second captures)
            have body := TreeResultRelated.faultWitness (function.toIndexed program first captures)
            exact ⟨_, .functionFault row last body, .fault _⟩
    | .application argument function applied => by
        cases read with
        | apply row first second =>
            obtain ⟨_, last, argumentRel⟩ := TreeResultRelated.valueWitness (argument.toIndexed program second captures)
            obtain ⟨_, head, functionRel⟩ := TreeResultRelated.valueWitness (function.toIndexed program first captures)
            obtain ⟨actual, body, aligned⟩ := applied.toIndexed program functionRel argumentRel
            exact ⟨actual, .application row last head body, aligned⟩
    | .letFault value => by
        cases read with
        | letValue row child body =>
            have step := TreeResultRelated.faultWitness (value.toIndexed program child captures)
            exact ⟨_, .letFault row step, .fault _⟩
    | .letMismatch value mismatch => by
        cases read with
        | letValue row child body =>
            obtain ⟨_, step, aligned⟩ := TreeResultRelated.valueWitness (value.toIndexed program child captures)
            exact ⟨_, .letMismatch row step ((matchTreePattern_related _ aligned).failure_iff.mp mismatch), .fault _⟩
    | .letBody value matched continued => by
        cases read with
        | letValue row child body =>
            obtain ⟨_, step, aligned⟩ := TreeResultRelated.valueWitness (value.toIndexed program child captures)
            obtain ⟨actual, selected, bindings⟩ := (matchTreePattern_related _ aligned).success matched
            obtain ⟨result, rest, output⟩ := continued.toIndexed program body (captures.extend bindings)
            exact ⟨result, .letBody row step selected rest, output⟩
    | .conditionFault test => by
        cases read with
        | branch row condition yes no =>
            have body := TreeResultRelated.faultWitness (test.toIndexed program condition captures)
            exact ⟨_, .conditionFault row body, .fault _⟩
    | @TreeEvaluates.branch _ _ _ _ _ choice _ test continued => by
        cases read with
        | branch row condition yes no =>
            have checked := TreeResultRelated.literalWitness (test.toIndexed program condition captures)
            obtain ⟨result, body, output⟩ := continued.toIndexed program (chooseRead choice yes no) captures
            exact ⟨result, .branch row checked body, output⟩
    | .andFault first => by
        cases read with
        | andThen row child right =>
            have body := TreeResultRelated.faultWitness (first.toIndexed program child captures)
            exact ⟨_, .andFault row body, .fault _⟩
    | .andFalse first => by
        cases read with
        | andThen row child right =>
            have body := TreeResultRelated.literalWitness (first.toIndexed program child captures)
            exact ⟨_, .andFalse row body, .value (.literal _)⟩
    | .andRightFault first last => by
        cases read with
        | andThen row left right =>
            have checked := TreeResultRelated.literalWitness (first.toIndexed program left captures)
            have body := TreeResultRelated.faultWitness (last.toIndexed program right captures)
            exact ⟨_, .andRightFault row checked body, .fault _⟩
    | .andRightValue first last => by
        cases read with
        | andThen row left right =>
            have checked := TreeResultRelated.literalWitness (first.toIndexed program left captures)
            have body := TreeResultRelated.literalWitness (last.toIndexed program right captures)
            exact ⟨_, .andRightValue row checked body, .value (.literal _)⟩
    | .orFault first => by
        cases read with
        | orElse row child right =>
            have body := TreeResultRelated.faultWitness (first.toIndexed program child captures)
            exact ⟨_, .orFault row body, .fault _⟩
    | .orTrue first => by
        cases read with
        | orElse row child right =>
            have body := TreeResultRelated.literalWitness (first.toIndexed program child captures)
            exact ⟨_, .orTrue row body, .value (.literal _)⟩
    | .orRightFault first last => by
        cases read with
        | orElse row left right =>
            have checked := TreeResultRelated.literalWitness (first.toIndexed program left captures)
            have body := TreeResultRelated.faultWitness (last.toIndexed program right captures)
            exact ⟨_, .orRightFault row checked body, .fault _⟩
    | .orRightValue first last => by
        cases read with
        | orElse row left right =>
            have checked := TreeResultRelated.literalWitness (first.toIndexed program left captures)
            have body := TreeResultRelated.literalWitness (last.toIndexed program right captures)
            exact ⟨_, .orRightValue row checked body, .value (.literal _)⟩
    | .consTailFault tail => by
        cases read with
        | cons row head child =>
            have body := TreeResultRelated.faultWitness (tail.toIndexed program child captures)
            exact ⟨_, .consTailFault row body, .fault _⟩
    | .consHeadFault tail head => by
        cases read with
        | cons row first last =>
            obtain ⟨_, checked, _⟩ := TreeResultRelated.valueWitness (tail.toIndexed program last captures)
            have body := TreeResultRelated.faultWitness (head.toIndexed program first captures)
            exact ⟨_, .consHeadFault row checked body, .fault _⟩
    | .cons tail head => by
        cases read with
        | cons row first last =>
            obtain ⟨_, checked, tailRel⟩ := TreeResultRelated.valueWitness (tail.toIndexed program last captures)
            obtain ⟨_, body, headRel⟩ := TreeResultRelated.valueWitness (head.toIndexed program first captures)
            exact ⟨_, .cons row checked body, .value (.cons headRel tailRel)⟩
    | .tupleFault fields => by
        cases read with
        | tuple row children =>
            have body := TreeArgumentsRelated.faultWitness (fields.toIndexed program children captures)
            exact ⟨_, .tupleFault row body, .fault _⟩
    | .tuple fields arity => by
        cases read with
        | tuple row children =>
            obtain ⟨_, body, aligned⟩ := TreeArgumentsRelated.valuesWitness (fields.toIndexed program children captures)
            exact ⟨_, .tuple row body (aligned.length ▸ arity), .value (.tuple aligned)⟩
    | .variantFault fields => by
        cases read with
        | variant row children =>
            have body := TreeArgumentsRelated.faultWitness (fields.toIndexed program children captures)
            exact ⟨_, .variantFault row body, .fault _⟩
    | .variant fields declaration => by
        cases read with
        | variant row children =>
            obtain ⟨_, body, aligned⟩ := TreeArgumentsRelated.valuesWitness (fields.toIndexed program children captures)
            exact ⟨_, .variant row body (aligned.length ▸ declaration), .value (.variant aligned)⟩
    | .primitiveFault arguments => by
        cases read with
        | primitive row children =>
            have body := TreeArgumentsRelated.faultWitness (arguments.toIndexed program children captures)
            exact ⟨_, .primitiveFault row body, .fault _⟩
    | .primitive arguments calculated => by
        cases read with
        | primitive row children =>
            obtain ⟨_, body, aligned⟩ := TreeArgumentsRelated.valuesWitness (arguments.toIndexed program children captures)
            obtain ⟨actual, computed, output⟩ := calculated.toIndexed aligned
            exact ⟨actual, .primitive row body computed, output⟩
    | .matchFault scrutinee => by
        cases read with
        | matchValue row child branches =>
            have body := TreeResultRelated.faultWitness (scrutinee.toIndexed program child captures)
            exact ⟨_, .matchFault row body, .fault _⟩
    | .matchFailure scrutinee mismatch => by
        cases read with
        | matchValue row child branches =>
            obtain ⟨_, body, aligned⟩ := TreeResultRelated.valueWitness (scrutinee.toIndexed program child captures)
            exact ⟨_, .matchFailure row body ((selectTreeClause_related branches aligned).failure_iff.mp mismatch), .fault _⟩
    | .matchBody scrutinee selected continued => by
        cases read with
        | matchValue row child branches =>
            obtain ⟨_, body, aligned⟩ := TreeResultRelated.valueWitness (scrutinee.toIndexed program child captures)
            obtain ⟨code, bindings, chosen, bodyRead, bindingsRel⟩ := (selectTreeClause_related branches aligned).success selected
            obtain ⟨actual, rest, output⟩ := continued.toIndexed program bodyRead (captures.extend bindingsRel)
            exact ⟨actual, .matchBody row body chosen rest, output⟩
    termination_by structural evaluated

  theorem TreeApplies.toIndexed (program : Program) {function argument : TreeValue} {result : TreeResult}
      (applied : TreeApplies program.constructors function argument result) {callable actual : Value}
      (functionRel : TreeValueRelated program.code function callable) (argumentRel : TreeValueRelated program.code argument actual) :
      ∃ output, Applies program callable actual output ∧ TreeResultRelated program.code result output :=
    match applied with
    | .lambda matched evaluated => by
        cases functionRel with
        | lambda read captures =>
            cases read with
            | lambda row child =>
                obtain ⟨bindings, selected, aligned⟩ := (matchTreePattern_related _ argumentRel).success matched
                obtain ⟨output, body, resultRel⟩ := evaluated.toIndexed program child (captures.extend aligned)
                exact ⟨output, .lambda row selected body, resultRel⟩
    | .lambdaMismatch mismatch => by
        cases functionRel with
        | lambda read captures =>
            cases read with
            | lambda row child =>
                exact ⟨_, .lambdaMismatch row ((matchTreePattern_related _ argumentRel).failure_iff.mp mismatch), .fault _⟩
    | .recursive definition matched evaluated => by
        cases functionRel with
        | recursive read captures =>
            cases read with
            | letRecursive row functions child =>
                obtain ⟨code, selected, bodyRead⟩ := functions.getElem? _ definition
                cases bodyRead with
                | lambda instruction bodyRead =>
                    obtain ⟨bindings, matched, aligned⟩ := (matchTreePattern_related _ argumentRel).success matched
                    obtain ⟨output, body, resultRel⟩ := evaluated.toIndexed program bodyRead
                      ((captures.recursiveEnvironment row functions child).extend aligned)
                    exact ⟨output, .recursive row selected instruction matched body, resultRel⟩
    | .recursiveMismatch definition mismatch => by
        cases functionRel with
        | recursive read captures =>
            cases read with
            | letRecursive row functions child =>
                obtain ⟨code, selected, bodyRead⟩ := functions.getElem? _ definition
                cases bodyRead with
                | lambda instruction bodyRead =>
                    exact ⟨_, .recursiveMismatch row selected instruction ((matchTreePattern_related _ argumentRel).failure_iff.mp mismatch), .fault _⟩
    termination_by structural applied

  theorem TreeEvaluatesArguments.toIndexed (program : Program) {environment : TreeEnvironment}
      {trees : List ExpressionTree} {result : Except Fault (List TreeValue)}
      (evaluated : TreeEvaluatesArguments program.constructors environment trees result) {codes : List Code}
      (read : ExpressionTree.FieldsRead program.code trees codes) {values : Environment}
      (captures : TreeValuesRelated program.code environment values) :
      ∃ actual, EvaluatesArguments program values codes actual ∧ TreeArgumentsRelated program.code result actual :=
    match evaluated with
    | .nil => by cases read; exact ⟨_, .nil, .values .nil⟩
    | .tailFault last => by
        cases read with
        | cons head tail =>
            have body := TreeArgumentsRelated.faultWitness (last.toIndexed program tail captures)
            exact ⟨_, .tailFault body, .fault _⟩
    | .headFault last head => by
        cases read with
        | cons first rest =>
            obtain ⟨_, tail, _⟩ := TreeArgumentsRelated.valuesWitness (last.toIndexed program rest captures)
            have body := TreeResultRelated.faultWitness (head.toIndexed program first captures)
            exact ⟨_, .headFault tail body, .fault _⟩
    | .cons last head => by
        cases read with
        | cons first rest =>
            obtain ⟨_, tail, back⟩ := TreeArgumentsRelated.valuesWitness (last.toIndexed program rest captures)
            obtain ⟨_, body, front⟩ := TreeResultRelated.valueWitness (head.toIndexed program first captures)
            exact ⟨_, .cons tail body, .values (.cons front back)⟩
    termination_by structural evaluated
end

#print axioms TreeEvaluates.toIndexed
#print axioms TreeApplies.toIndexed
#print axioms TreeEvaluatesArguments.toIndexed

end Mettapedia.Languages.OCaml
