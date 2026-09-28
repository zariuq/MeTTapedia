import Mettapedia.OSLF.MeTTaIL.RuleBinding
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Matching and instantiation with rule occurrence contexts

This interpreter consumes a binding specification attached to an authored
`RewriteRule`. Each captured value retains its declared dependency context and
the caller's ambient context. An explicit occurrence substitution determines
how that value is used at each later site. The matcher supports injective
variable spines at input occurrences; output occurrences may supply general
terms. All collection choices remain list occurrences.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)

set_option autoImplicit false

abbrev Assignment := List (String × ContextualValue)

def lookup (assignment : Assignment) (name : String) : Option ContextualValue :=
  assignment.find? (fun entry => entry.1 == name) |>.map (·.2)

/-- Extend an assignment or check a repeated occurrence. A second occurrence
may have a different binder depth or spine, but must recover the same body. -/
def assign (assignment : Assignment) (name : String) (value : ContextualValue) :
    Option Assignment :=
  match lookup assignment name with
  | none => some ((name, value) :: assignment)
  | some prior => if prior == value then some assignment else none

/-- Capture at this exact occurrence; the source pattern, path and declared
spine are all read from the same authored rule. -/
def capture? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (target : Pattern) :
    Option Assignment := do
  let dependencies ← dependencies? spec name
  let arguments ← arguments? rule spec name site path
  let value ← recoverValue? dependencies ambient depth arguments target
  assign assignment name value

/-- Capture a collection rest with the same context semantics as an ordinary
metavariable, retaining its tag and the multiplicity/order of the residual. -/
def captureRest? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (kind : CollType)
    (elements : List Pattern) : Option Assignment :=
  capture? rule spec ambient depth site path assignment name
    (.collection kind elements none)

mutual
/-- Match a pattern under its actual binder depth. -/
def matchAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) : Pattern → Pattern → List Assignment
  | .fvar name, target =>
      (capture? rule spec ambient depth site path assignment name target).toList
  | .bvar expected, .bvar actual =>
      if expected == actual then [assignment] else []
  | .apply constructor patterns, .apply actualConstructor targets =>
      if constructor == actualConstructor then
        matchArgsAt rule spec ambient site path depth assignment 0 patterns targets
      else []
  | .lambda _ body, .lambda _ target =>
      matchAt rule spec ambient site (path ++ [0]) (depth + 1)
        assignment body target
  | .multiLambda arity _ body, .multiLambda actualArity _ target =>
      if arity == actualArity then
        matchAt rule spec ambient site (path ++ [0]) (depth + arity)
          assignment body target
      else []
  | .subst body replacement, .subst targetBody targetReplacement =>
      (matchAt rule spec ambient site (path ++ [0]) (depth + 1)
        assignment body targetBody).flatMap fun found =>
        matchAt rule spec ambient site (path ++ [1]) depth
          found replacement targetReplacement
  | .collection kind patterns rest, .collection actualKind targets actualRest =>
      if kind == actualKind && actualRest.isNone then
        if kind == .vec then
          match rest with
          | none =>
              matchArgsAt rule spec ambient site path depth assignment 0 patterns targets
          | some name =>
              (matchArgsAt rule spec ambient site path depth assignment 0
                patterns (targets.take patterns.length)).filterMap fun found =>
                  captureRest? rule spec ambient depth site
                    (path ++ [patterns.length]) found name kind
                    (targets.drop patterns.length)
        else
          matchBagAt rule spec ambient site path depth assignment 0
            patterns rest kind targets
      else []
  | _, _ => []
termination_by pattern _target => sizeOf pattern

/-- Match an ordered argument or vector-element row. -/
def matchArgsAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    List Pattern → List Pattern → List Assignment
  | [], [] => [assignment]
  | pattern :: patterns, target :: targets =>
      (matchAt rule spec ambient site (path ++ [index]) depth
        assignment pattern target).flatMap fun found =>
        matchArgsAt rule spec ambient site path depth found (index + 1)
          patterns targets
  | _, _ => []
termination_by patterns _targets => sizeOf patterns

/-- Enumerate bag/set element choices without collapsing occurrences. -/
def matchBagAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    List Pattern → Option String → CollType → List Pattern → List Assignment
  | [], none, _, targets => if targets.isEmpty then [assignment] else []
  | [], some name, kind, targets =>
      (captureRest? rule spec ambient depth site (path ++ [index])
        assignment name kind targets).toList
  | pattern :: patterns, rest, kind, targets =>
      targets.zipIdx.flatMap fun (target, selected) =>
        (matchAt rule spec ambient site (path ++ [index]) depth
          assignment pattern target).flatMap fun found =>
            matchBagAt rule spec ambient site path depth found (index + 1)
              patterns rest kind (targets.eraseIdx selected)
termination_by patterns _rest _kind _targets => sizeOf patterns
end

/-- Match one authored rule in a caller-supplied ambient context. -/
def matchRuleAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (target : Pattern) : List Assignment :=
  matchAt rule spec ambient .left [] 0 [] rule.left target

mutual
/-- Instantiate a rule pattern at one exact site. This uses the captured
context rather than reading the first LHS occurrence's depth. -/
def instantiateAt? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) : Pattern → Option Pattern
  | .fvar name => do
      let value ← lookup assignment name
      let arguments ← arguments? rule spec name site path
      instantiateValue? value ambient depth arguments
  | .bvar index => some (.bvar index)
  | .apply constructor arguments => do
      let results ← instantiateArgsAt? rule spec ambient site path depth
        assignment 0 arguments
      some (.apply constructor results)
  | .lambda binder body => do
      let result ← instantiateAt? rule spec ambient site (path ++ [0])
        (depth + 1) assignment body
      some (.lambda binder result)
  | .multiLambda arity binders body => do
      let result ← instantiateAt? rule spec ambient site (path ++ [0])
        (depth + arity) assignment body
      some (.multiLambda arity binders result)
  | .subst body replacement => do
      let body' ← instantiateAt? rule spec ambient site (path ++ [0])
        (depth + 1) assignment body
      let replacement' ← instantiateAt? rule spec ambient site (path ++ [1])
        depth assignment replacement
      some (instantiateBVar replacement' body')
  | .collection kind elements rest => do
      let explicit ← instantiateArgsAt? rule spec ambient site path depth
        assignment 0 elements
      match rest with
      | none => some (.collection kind explicit none)
      | some name =>
          let value ← lookup assignment name
          let arguments ← arguments? rule spec name site (path ++ [elements.length])
          match ← instantiateValue? value ambient depth arguments with
          | .collection actualKind residual none =>
              if actualKind == kind then
                some (.collection kind (explicit ++ residual) none)
              else none
          | _ => none
termination_by pattern => sizeOf pattern

/-- Instantiate an ordered row without changing its occurrence addresses. -/
def instantiateArgsAt? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    List Pattern → Option (List Pattern)
  | [] => some []
  | pattern :: patterns => do
      let head ← instantiateAt? rule spec ambient site (path ++ [index])
        depth assignment pattern
      let tail ← instantiateArgsAt? rule spec ambient site path depth assignment
        (index + 1) patterns
      some (head :: tail)
termination_by patterns => sizeOf patterns
end

/-- The reduct is the instantiated authored right-hand side. -/
def reduct? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) : Option Pattern :=
  instantiateAt? rule spec ambient .right [] 0 assignment rule.right

/-- Project values available at the rule root for the existing ordered
premise interpreter. A value that still needs a local binder is unavailable
there; its explicit occurrence spine must be interpreted in a later extension
of the premise machine. -/
def projectRoot? (ambient : Nat) (assignment : Assignment) : Option Bindings :=
  assignment.mapM fun (name, value) => do
    let result ← instantiateValue? value ambient 0 []
    some (name, result)

/-- Reconcile one root-premise output with a scoped assignment. Repeated
names retain their earlier contextual value when projection agrees. -/
def reconcileRootResult? (spec : RuleBindingSpec) (ambient : Nat)
    (assignment : Assignment) (entry : String × Pattern) : Option Assignment :=
  match entry with
  | (name, result) =>
    match lookup assignment name with
    | some existing => do
        let projected ← instantiateValue? existing ambient 0 []
        if projected == result then some assignment else none
    | none => do
        let dependencies ← dependencies? spec name
        let value ← recoverValue? dependencies ambient 0 [] result
        assign assignment name value

/-- Reconcile ordered premise machine results with the scoped assignment.
New outputs are recovered at the rule root and retain ambient variables. -/
def extendRoot? (spec : RuleBindingSpec) (ambient : Nat)
    (assignment : Assignment) (raw : Bindings) : Option Assignment :=
  raw.foldlM (init := assignment) (reconcileRootResult? spec ambient)

end Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
