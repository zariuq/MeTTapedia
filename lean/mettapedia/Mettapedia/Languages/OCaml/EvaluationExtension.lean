import Mettapedia.Languages.OCaml.Evaluation

/-! Extending an instruction store preserves every existing independent
evaluation, application and argument evaluation. Closure references and
recursive-group identities remain fixed. This is preservation, not a claim
that arbitrary new code or new environment closures add no behavior. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  theorem Evaluates.mono {before after : Program}
      (kept : ∀ code instruction, before.instruction? code = some instruction → after.instruction? code = some instruction)
      (constructors : before.constructors ⊆ after.constructors)
      {environment : Environment} {code : Code} {result : Result}
      (evaluated : Evaluates before environment code result) : Evaluates after environment code result :=
    match evaluated with
    | .literal row => .literal (kept _ _ row)
    | .variable row found => .variable (kept _ _ row) found
    | .lambda row => .lambda (kept _ _ row)
    | .recursive row body => .recursive (kept _ _ row) (body.mono kept constructors)
    | .argumentFault row body => .argumentFault (kept _ _ row) (body.mono kept constructors)
    | .functionFault row argument body => .functionFault (kept _ _ row) (argument.mono kept constructors) (body.mono kept constructors)
    | .application row argument function applied =>
        .application (kept _ _ row) (argument.mono kept constructors) (function.mono kept constructors) (applied.mono kept constructors)
    | .letFault row body => .letFault (kept _ _ row) (body.mono kept constructors)
    | .letMismatch row body failed => .letMismatch (kept _ _ row) (body.mono kept constructors) failed
    | .letBody row value matched body => .letBody (kept _ _ row) (value.mono kept constructors) matched (body.mono kept constructors)
    | .conditionFault row body => .conditionFault (kept _ _ row) (body.mono kept constructors)
    | .branch row test body => .branch (kept _ _ row) (test.mono kept constructors) (body.mono kept constructors)
    | .andFault row body => .andFault (kept _ _ row) (body.mono kept constructors)
    | .andFalse row body => .andFalse (kept _ _ row) (body.mono kept constructors)
    | .andRightFault row first second => .andRightFault (kept _ _ row) (first.mono kept constructors) (second.mono kept constructors)
    | .andRightValue row first second => .andRightValue (kept _ _ row) (first.mono kept constructors) (second.mono kept constructors)
    | .orFault row body => .orFault (kept _ _ row) (body.mono kept constructors)
    | .orTrue row body => .orTrue (kept _ _ row) (body.mono kept constructors)
    | .orRightFault row first second => .orRightFault (kept _ _ row) (first.mono kept constructors) (second.mono kept constructors)
    | .orRightValue row first second => .orRightValue (kept _ _ row) (first.mono kept constructors) (second.mono kept constructors)
    | .consTailFault row body => .consTailFault (kept _ _ row) (body.mono kept constructors)
    | .consHeadFault row first second => .consHeadFault (kept _ _ row) (first.mono kept constructors) (second.mono kept constructors)
    | .cons row first second => .cons (kept _ _ row) (first.mono kept constructors) (second.mono kept constructors)
    | .tupleFault row fields => .tupleFault (kept _ _ row) (fields.mono kept constructors)
    | .tuple row fields arity => .tuple (kept _ _ row) (fields.mono kept constructors) arity
    | .variantFault row fields => .variantFault (kept _ _ row) (fields.mono kept constructors)
    | .variant row fields declared => .variant (kept _ _ row) (fields.mono kept constructors) (constructors declared)
    | .primitiveFault row arguments => .primitiveFault (kept _ _ row) (arguments.mono kept constructors)
    | .primitive row arguments calculated => .primitive (kept _ _ row) (arguments.mono kept constructors) calculated
    | .matchFault row body => .matchFault (kept _ _ row) (body.mono kept constructors)
    | .matchFailure row body failed => .matchFailure (kept _ _ row) (body.mono kept constructors) failed
    | .matchBody row scrutinee selected body =>
        .matchBody (kept _ _ row) (scrutinee.mono kept constructors) selected (body.mono kept constructors)
    termination_by structural evaluated

  theorem Applies.mono {before after : Program}
      (kept : ∀ code instruction, before.instruction? code = some instruction → after.instruction? code = some instruction)
      (constructors : before.constructors ⊆ after.constructors)
      {function argument : Value} {result : Result} (applied : Applies before function argument result) :
      Applies after function argument result :=
    match applied with
    | .lambda row matched body => .lambda (kept _ _ row) matched (body.mono kept constructors)
    | .lambdaMismatch row failed => .lambdaMismatch (kept _ _ row) failed
    | .recursive group selected row matched body =>
        .recursive (kept _ _ group) selected (kept _ _ row) matched (body.mono kept constructors)
    | .recursiveMismatch group selected row failed => .recursiveMismatch (kept _ _ group) selected (kept _ _ row) failed
    termination_by structural applied

  theorem EvaluatesArguments.mono {before after : Program}
      (kept : ∀ code instruction, before.instruction? code = some instruction → after.instruction? code = some instruction)
      (constructors : before.constructors ⊆ after.constructors)
      {environment : Environment} {codes : List Code} {result : Except Fault (List Value)}
      (evaluated : EvaluatesArguments before environment codes result) : EvaluatesArguments after environment codes result :=
    match evaluated with
    | .nil => .nil
    | .tailFault tail => .tailFault (tail.mono kept constructors)
    | .headFault tail head => .headFault (tail.mono kept constructors) (head.mono kept constructors)
    | .cons tail head => .cons (tail.mono kept constructors) (head.mono kept constructors)
    termination_by structural evaluated
end

#print axioms Evaluates.mono
#print axioms Applies.mono
#print axioms EvaluatesArguments.mono

end Mettapedia.Languages.OCaml
