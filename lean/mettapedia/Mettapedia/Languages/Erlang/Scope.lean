import Mettapedia.Languages.Erlang.Syntax

/-! Scope validation for the canonical postorder arena. Recursive functions
refer to their environment slots, so code references themselves are acyclic.
The check covers variable/pinned slots, opcode arity and guard effect use.
It is not the full source/static or primitive-profile admission theorem. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

def Primitive.arity : Primitive → Nat
  | .negate | .isInteger | .isAtom | .isTuple | .isList | .isPid | .isFunction | .notBool => 1
  | _ => 2

def ActorOperation.arity : ActorOperation → Nat
  | .spawn => 1
  | .send => 2
  | _ => 0

mutual
  def MatchPattern.checkScope (depth : Nat) : MatchPattern → Bool
    | .pinned index => index < depth
    | .alias pattern => pattern.checkScope depth
    | .tuple patterns => checkPatternScopes depth patterns
    | .cons head tail => head.checkScope depth && tail.checkScope depth
    | _ => true

  def checkPatternScopes (depth : Nat) : List MatchPattern → Bool
    | [] => true
    | pattern :: rest => pattern.checkScope depth && checkPatternScopes depth rest
end

def Instruction.children : Instruction → List Code
  | .literal _ | .variable _ => []
  | .lambda _ body => [body]
  | .apply function arguments => function :: arguments
  | .letValues _ argument body => [argument, body]
  | .letRecursive definitions body => definitions.map (·.body) ++ [body]
  | .sequence first second | .cons first second => [first, second]
  | .values fields | .tuple fields | .primitive _ fields | .actor _ fields => fields
  | .caseValues argument clauses => argument :: clauses.flatMap fun clause => [clause.guard, clause.body]
  | .matchFail reason => [reason]

def Program.backwardReferences (program : Program) : Bool :=
  program.code.toList.zipIdx.all fun (instruction, reference) => instruction.children.all (· < reference)

def checkCodeScope (program : Program) : Nat → Nat → Bool → Code → Bool
  | 0, _, _, _ => false
  | fuel + 1, depth, inGuard, reference =>
      match program.instruction? reference with
      | none => false
      | some instruction =>
          let check := checkCodeScope program fuel depth inGuard
          match instruction with
          | .literal _ => true
          | .variable index => index < depth
          | .lambda arity body => checkCodeScope program fuel (depth + arity) false body
          | .apply function arguments => !inGuard && check function && arguments.all check
          | .letValues arity argument body =>
              check argument && checkCodeScope program fuel (depth + arity) inGuard body
          | .letRecursive definitions body =>
              definitions.all (fun definition => checkCodeScope program fuel
                (depth + definitions.length + definition.arity) false definition.body) &&
              checkCodeScope program fuel (depth + definitions.length) inGuard body
          | .sequence first second | .cons first second => check first && check second
          | .values fields | .tuple fields => fields.all check
          | .primitive operator arguments => arguments.length == operator.arity && arguments.all check
          | .actor operation arguments =>
              (!inGuard || operation == .self) && arguments.length == operation.arity && arguments.all check
          | .caseValues argument clauses =>
              check argument && clauses.all fun clause =>
                let bound := depth + (clause.patterns.map MatchPattern.binders).sum
                checkPatternScopes depth clause.patterns &&
                  checkCodeScope program fuel bound true clause.guard &&
                  checkCodeScope program fuel bound inGuard clause.body
          | .matchFail reason => check reason

def Program.checkScope (program : Program) (initialDepth : Nat := 0) : Bool :=
  program.backwardReferences && program.entry < program.code.size &&
    checkCodeScope program (program.code.size + 1) initialDepth false program.entry

end Mettapedia.Languages.Erlang
