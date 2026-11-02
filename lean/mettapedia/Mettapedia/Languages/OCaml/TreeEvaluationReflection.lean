import Mettapedia.Languages.OCaml.TreeEvaluationPreservation
import Mettapedia.Languages.OCaml.ExpressionGraphInversion

/-! Allocated finite evaluations reflect to independent tree evaluations.
Instruction lookup, captured environments, primitive faults and ordered
clause selection authorize every reflected result. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

private theorem chooseRead {arena : Array Instruction} {yes no : ExpressionTree} {yesCode noCode : Code}
    (choice : Bool) (positive : ExpressionTree.Reads arena yes yesCode) (negative : ExpressionTree.Reads arena no noCode) :
    ExpressionTree.Reads arena (if choice then yes else no) (if choice then yesCode else noCode) := by
  cases choice <;> assumption

mutual
  theorem Evaluates.toTree (program : Program) {environment : Environment} {code : Code} {actual : Result}
      (evaluated : Evaluates program environment code actual) {tree : ExpressionTree}
      (read : ExpressionTree.Reads program.code tree code) {trees : TreeEnvironment}
      (captures : TreeValuesRelated program.code trees environment) :
      ∃ result, TreeEvaluates program.constructors trees tree result ∧ TreeResultRelated program.code result actual :=
    match evaluated with
    | .literal row => by
        have shape := read.view_literal _ row
        subst tree
        exact ⟨_, .literal, .value (.literal _)⟩
    | .variable row binding => by
        have shape := read.view_variable _ row
        subst tree
        obtain ⟨value, selected, aligned⟩ := captures.getElem?_back _ binding
        exact ⟨_, .variable selected, .value aligned⟩
    | .lambda row => by
        obtain ⟨body, rfl, bodyRead⟩ := read.view_lambda _ _ row
        exact ⟨_, .lambda, .value (.lambda (.lambda row bodyRead) captures)⟩
    | .recursive row continued => by
        obtain ⟨definitions, body, rfl, functions, child⟩ := read.view_letRecursive _ _ row
        obtain ⟨result, body, aligned⟩ := continued.toTree program child (captures.recursiveEnvironment row functions child)
        exact ⟨result, .recursive body, aligned⟩
    | .argumentFault row argument => by
        obtain ⟨function, child, rfl, first, last⟩ := read.view_apply _ _ row
        have body := TreeResultRelated.faultWitness_back (argument.toTree program last captures)
        exact ⟨_, .argumentFault body, .fault _⟩
    | .functionFault row argument function => by
        obtain ⟨functionTree, argumentTree, rfl, first, last⟩ := read.view_apply _ _ row
        obtain ⟨_, checked, _⟩ := TreeResultRelated.valueWitness_back (argument.toTree program last captures)
        have body := TreeResultRelated.faultWitness_back (function.toTree program first captures)
        exact ⟨_, .functionFault checked body, .fault _⟩
    | .application row argument function applied => by
        obtain ⟨functionTree, argumentTree, rfl, first, last⟩ := read.view_apply _ _ row
        obtain ⟨_, checked, argumentRel⟩ := TreeResultRelated.valueWitness_back (argument.toTree program last captures)
        obtain ⟨_, head, functionRel⟩ := TreeResultRelated.valueWitness_back (function.toTree program first captures)
        obtain ⟨result, body, aligned⟩ := applied.toTree program functionRel argumentRel
        exact ⟨result, .application checked head body, aligned⟩
    | .letFault row value => by
        obtain ⟨valueTree, bodyTree, rfl, first, last⟩ := read.view_letValue _ _ _ row
        have body := TreeResultRelated.faultWitness_back (value.toTree program first captures)
        exact ⟨_, .letFault body, .fault _⟩
    | .letMismatch row value mismatch => by
        obtain ⟨valueTree, bodyTree, rfl, first, last⟩ := read.view_letValue _ _ _ row
        obtain ⟨_, body, aligned⟩ := TreeResultRelated.valueWitness_back (value.toTree program first captures)
        exact ⟨_, .letMismatch body ((matchTreePattern_related _ aligned).failure_iff.mpr mismatch), .fault _⟩
    | .letBody row value matched continued => by
        obtain ⟨valueTree, bodyTree, rfl, first, last⟩ := read.view_letValue _ _ _ row
        obtain ⟨_, body, aligned⟩ := TreeResultRelated.valueWitness_back (value.toTree program first captures)
        obtain ⟨bindings, selected, bindingsRel⟩ := (matchTreePattern_related _ aligned).success_back matched
        obtain ⟨result, rest, output⟩ := continued.toTree program last (captures.extend bindingsRel)
        exact ⟨result, .letBody body selected rest, output⟩
    | .conditionFault row condition => by
        obtain ⟨test, yes, no, rfl, first, positive, negative⟩ := read.view_branch _ _ _ row
        have body := TreeResultRelated.faultWitness_back (condition.toTree program first captures)
        exact ⟨_, .conditionFault body, .fault _⟩
    | @Evaluates.branch _ _ _ _ _ _ choice _ row condition continued => by
        obtain ⟨test, yes, no, rfl, first, positive, negative⟩ := read.view_branch _ _ _ row
        have checked := TreeResultRelated.literalWitness_back (condition.toTree program first captures)
        obtain ⟨result, body, output⟩ := continued.toTree program (chooseRead choice positive negative) captures
        exact ⟨result, .branch checked body, output⟩
    | .andFault row left => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_andThen _ _ row
        have body := TreeResultRelated.faultWitness_back (left.toTree program head captures)
        exact ⟨_, .andFault body, .fault _⟩
    | .andFalse row left => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_andThen _ _ row
        have body := TreeResultRelated.literalWitness_back (left.toTree program head captures)
        exact ⟨_, .andFalse body, .value (.literal _)⟩
    | .andRightFault row left right => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_andThen _ _ row
        have checked := TreeResultRelated.literalWitness_back (left.toTree program head captures)
        have body := TreeResultRelated.faultWitness_back (right.toTree program tail captures)
        exact ⟨_, .andRightFault checked body, .fault _⟩
    | .andRightValue row left right => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_andThen _ _ row
        have checked := TreeResultRelated.literalWitness_back (left.toTree program head captures)
        have body := TreeResultRelated.literalWitness_back (right.toTree program tail captures)
        exact ⟨_, .andRightValue checked body, .value (.literal _)⟩
    | .orFault row left => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_orElse _ _ row
        have body := TreeResultRelated.faultWitness_back (left.toTree program head captures)
        exact ⟨_, .orFault body, .fault _⟩
    | .orTrue row left => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_orElse _ _ row
        have body := TreeResultRelated.literalWitness_back (left.toTree program head captures)
        exact ⟨_, .orTrue body, .value (.literal _)⟩
    | .orRightFault row left right => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_orElse _ _ row
        have checked := TreeResultRelated.literalWitness_back (left.toTree program head captures)
        have body := TreeResultRelated.faultWitness_back (right.toTree program tail captures)
        exact ⟨_, .orRightFault checked body, .fault _⟩
    | .orRightValue row left right => by
        obtain ⟨first, last, rfl, head, tail⟩ := read.view_orElse _ _ row
        have checked := TreeResultRelated.literalWitness_back (left.toTree program head captures)
        have body := TreeResultRelated.literalWitness_back (right.toTree program tail captures)
        exact ⟨_, .orRightValue checked body, .value (.literal _)⟩
    | .consTailFault row tail => by
        obtain ⟨first, last, rfl, head, rest⟩ := read.view_cons _ _ row
        have body := TreeResultRelated.faultWitness_back (tail.toTree program rest captures)
        exact ⟨_, .consTailFault body, .fault _⟩
    | .consHeadFault row tail head => by
        obtain ⟨first, last, rfl, child, rest⟩ := read.view_cons _ _ row
        obtain ⟨_, checked, _⟩ := TreeResultRelated.valueWitness_back (tail.toTree program rest captures)
        have body := TreeResultRelated.faultWitness_back (head.toTree program child captures)
        exact ⟨_, .consHeadFault checked body, .fault _⟩
    | .cons row tail head => by
        obtain ⟨first, last, rfl, child, rest⟩ := read.view_cons _ _ row
        obtain ⟨_, checked, tailRel⟩ := TreeResultRelated.valueWitness_back (tail.toTree program rest captures)
        obtain ⟨_, body, headRel⟩ := TreeResultRelated.valueWitness_back (head.toTree program child captures)
        exact ⟨_, .cons checked body, .value (.cons headRel tailRel)⟩
    | .tupleFault row fields => by
        obtain ⟨fieldsTree, rfl, children⟩ := read.view_tuple _ row
        have body := TreeArgumentsRelated.faultWitness_back (fields.toTree program children captures)
        exact ⟨_, .tupleFault body, .fault _⟩
    | .tuple row fields arity => by
        obtain ⟨fieldsTree, rfl, children⟩ := read.view_tuple _ row
        obtain ⟨_, body, aligned⟩ := TreeArgumentsRelated.valuesWitness_back (fields.toTree program children captures)
        exact ⟨_, .tuple body (aligned.length.symm ▸ arity), .value (.tuple aligned)⟩
    | .variantFault row fields => by
        obtain ⟨fieldsTree, rfl, children⟩ := read.view_variant _ _ _ row
        have body := TreeArgumentsRelated.faultWitness_back (fields.toTree program children captures)
        exact ⟨_, .variantFault body, .fault _⟩
    | .variant row fields declaration => by
        obtain ⟨fieldsTree, rfl, children⟩ := read.view_variant _ _ _ row
        obtain ⟨_, body, aligned⟩ := TreeArgumentsRelated.valuesWitness_back (fields.toTree program children captures)
        exact ⟨_, .variant body (aligned.length.symm ▸ declaration), .value (.variant aligned)⟩
    | .primitiveFault row arguments => by
        obtain ⟨argumentsTree, rfl, children⟩ := read.view_primitive _ _ row
        have body := TreeArgumentsRelated.faultWitness_back (arguments.toTree program children captures)
        exact ⟨_, .primitiveFault body, .fault _⟩
    | .primitive row arguments calculated => by
        obtain ⟨argumentsTree, rfl, children⟩ := read.view_primitive _ _ row
        obtain ⟨_, body, aligned⟩ := TreeArgumentsRelated.valuesWitness_back (arguments.toTree program children captures)
        obtain ⟨result, computed, output⟩ := TreePrimitive.fromIndexed aligned calculated
        exact ⟨result, .primitive body computed, output⟩
    | .matchFault row scrutinee => by
        obtain ⟨scrutineeTree, clausesTree, rfl, child, branches⟩ := read.view_matchValue _ _ row
        have body := TreeResultRelated.faultWitness_back (scrutinee.toTree program child captures)
        exact ⟨_, .matchFault body, .fault _⟩
    | .matchFailure row scrutinee mismatch => by
        obtain ⟨scrutineeTree, clausesTree, rfl, child, branches⟩ := read.view_matchValue _ _ row
        obtain ⟨_, body, aligned⟩ := TreeResultRelated.valueWitness_back (scrutinee.toTree program child captures)
        exact ⟨_, .matchFailure body ((selectTreeClause_related branches aligned).failure_iff.mpr mismatch), .fault _⟩
    | .matchBody row scrutinee selected continued => by
        obtain ⟨scrutineeTree, clausesTree, rfl, child, branches⟩ := read.view_matchValue _ _ row
        obtain ⟨_, body, aligned⟩ := TreeResultRelated.valueWitness_back (scrutinee.toTree program child captures)
        obtain ⟨sourceBody, bindings, chosen, bodyRead, bindingsRel⟩ := (selectTreeClause_related branches aligned).success_back selected
        obtain ⟨result, rest, output⟩ := continued.toTree program bodyRead (captures.extend bindingsRel)
        exact ⟨result, .matchBody body chosen rest, output⟩
    termination_by structural evaluated

  theorem Applies.toTree (program : Program) {function argument : Value} {actual : Result}
      (applied : Applies program function argument actual) {callable value : TreeValue}
      (functionRel : TreeValueRelated program.code callable function) (argumentRel : TreeValueRelated program.code value argument) :
      ∃ result, TreeApplies program.constructors callable value result ∧ TreeResultRelated program.code result actual :=
    match applied with
    | .lambda row matched evaluated => by
        cases functionRel with
        | lambda read captures =>
            cases read with
            | lambda sourceRow child =>
                have same := Option.some.inj (sourceRow.symm.trans row)
                cases same
                obtain ⟨bindings, selected, aligned⟩ := (matchTreePattern_related _ argumentRel).success_back matched
                obtain ⟨result, body, output⟩ := evaluated.toTree program child (captures.extend aligned)
                exact ⟨result, .lambda selected body, output⟩
    | .lambdaMismatch row mismatch => by
        cases functionRel with
        | lambda read captures =>
            cases read with
            | lambda sourceRow child =>
                have same := Option.some.inj (sourceRow.symm.trans row)
                cases same
                exact ⟨_, .lambdaMismatch ((matchTreePattern_related _ argumentRel).failure_iff.mpr mismatch), .fault _⟩
    | .recursive row selected instruction matched evaluated => by
        cases functionRel with
        | recursive read captures =>
            cases read with
            | letRecursive sourceRow functions child =>
                have same := Option.some.inj (sourceRow.symm.trans row)
                cases same
                obtain ⟨source, found, functionRead⟩ := functions.getElem?_back _ selected
                obtain ⟨body, shape, bodyRead⟩ := functionRead.view_lambda _ _ instruction
                rw [shape] at found
                obtain ⟨bindings, chosen, aligned⟩ := (matchTreePattern_related _ argumentRel).success_back matched
                obtain ⟨result, body, output⟩ := evaluated.toTree program bodyRead
                  ((captures.recursiveEnvironment row functions child).extend aligned)
                exact ⟨result, .recursive found chosen body, output⟩
    | .recursiveMismatch row selected instruction mismatch => by
        cases functionRel with
        | recursive read captures =>
            cases read with
            | letRecursive sourceRow functions child =>
                have same := Option.some.inj (sourceRow.symm.trans row)
                cases same
                obtain ⟨source, found, functionRead⟩ := functions.getElem?_back _ selected
                obtain ⟨body, shape, bodyRead⟩ := functionRead.view_lambda _ _ instruction
                rw [shape] at found
                exact ⟨_, .recursiveMismatch found ((matchTreePattern_related _ argumentRel).failure_iff.mpr mismatch), .fault _⟩
    termination_by structural applied

  theorem EvaluatesArguments.toTree (program : Program) {environment : Environment} {codes : List Code}
      {actual : Except Fault (List Value)} (evaluated : EvaluatesArguments program environment codes actual)
      {trees : List ExpressionTree} (read : ExpressionTree.FieldsRead program.code trees codes) {values : TreeEnvironment}
      (captures : TreeValuesRelated program.code values environment) :
      ∃ result, TreeEvaluatesArguments program.constructors values trees result ∧ TreeArgumentsRelated program.code result actual :=
    match evaluated with
    | .nil => by cases read; exact ⟨_, .nil, .values .nil⟩
    | .tailFault last => by
        cases read with
        | cons head tail =>
            have body := TreeArgumentsRelated.faultWitness_back (last.toTree program tail captures)
            exact ⟨_, .tailFault body, .fault _⟩
    | .headFault last head => by
        cases read with
        | cons first rest =>
            obtain ⟨_, tail, _⟩ := TreeArgumentsRelated.valuesWitness_back (last.toTree program rest captures)
            have body := TreeResultRelated.faultWitness_back (head.toTree program first captures)
            exact ⟨_, .headFault tail body, .fault _⟩
    | .cons last head => by
        cases read with
        | cons first rest =>
            obtain ⟨_, tail, back⟩ := TreeArgumentsRelated.valuesWitness_back (last.toTree program rest captures)
            obtain ⟨_, body, front⟩ := TreeResultRelated.valueWitness_back (head.toTree program first captures)
            exact ⟨_, .cons tail body, .values (.cons front back)⟩
    termination_by structural evaluated
end

#print axioms Evaluates.toTree
#print axioms Applies.toTree
#print axioms EvaluatesArguments.toTree

end Mettapedia.Languages.OCaml
