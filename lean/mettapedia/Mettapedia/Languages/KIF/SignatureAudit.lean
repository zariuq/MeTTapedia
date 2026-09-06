import Mettapedia.Languages.KIF.BindingAudit
import Std.Data.HashMap.Basic

/-!
# Source-derived operator signatures for SUO-KIF

SUMO records fixed arity through ontology facts such as
`(instance agent BinaryPredicate)`. This pass derives operator arities from
those facts and the local subclass graph, then checks every application whose
arity is known. Symbols supplied by an imported ontology are reported
separately rather than treated as errors; that list is the exact dependency
surface needed for a later multi-source check.
 -/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

structure OperatorUse where
  name : String
  arity : Nat
  span : SourceSpan
  deriving DecidableEq, Repr

private structure ApplicationInventory where
  uses : List OperatorUse
  exhausted : List SourceSpan
  deriving Repr

private def ApplicationInventory.append
    (left right : ApplicationInventory) : ApplicationInventory :=
  ⟨left.uses ++ right.uses, left.exhausted ++ right.exhausted⟩

mutual
  private def applicationsInTerm : Nat → Term → ApplicationInventory
    | 0, term => ⟨[], [term.span]⟩
    | fuel + 1, term =>
        match term with
        | .atom _ => ⟨[], []⟩
        | .list _ children =>
            let nested := applicationsInTerms fuel children
            match children with
            | [] => nested
            | headTerm :: arguments =>
                match headTerm.asSymbol? with
                | none => nested
                | some head =>
                    { nested with
                      uses := ⟨head.text, arguments.length, head.span⟩ :: nested.uses }

  private def applicationsInTerms : Nat → List Term → ApplicationInventory
    | _, [] => ⟨[], []⟩
    | fuel, term :: rest =>
        (applicationsInTerm fuel term).append (applicationsInTerms fuel rest)
end

private def applicationInventory (fuel : Nat) (parsed : Parsed) :
    ApplicationInventory :=
  applicationsInTerms fuel parsed.forms

private def subclassEdges (declarations : List SuoDeclaration) :
    List (String × String) :=
  declarations.filterMap fun
    | .subclass child parent =>
        parent.asSymbol?.map fun parentSymbol => (child.text, parentSymbol.text)
    | _ => none

private def fixedArityClasses : List (String × Nat) :=
  [ ("NullaryPredicate", 0), ("UnaryPredicate", 1),
    ("BinaryPredicate", 2), ("TernaryPredicate", 3),
    ("QuaternaryPredicate", 4), ("QuintaryPredicate", 5),
    ("SextaryPredicate", 6), ("NullaryFunction", 0),
    ("UnaryFunction", 1), ("BinaryFunction", 2),
    ("TernaryFunction", 3), ("QuaternaryFunction", 4),
    ("QuintaryFunction", 5), ("SextaryFunction", 6) ]

private def builtinFixedArity? : String → Option Nat
  | "not" => some 1
  | "=>" | "<=>" => some 2
  | "forall" | "exists" => some 2
  | "equal" | "instance" | "subclass" => some 2
  | "domain" | "domainSubclass" => some 3
  | "range" | "rangeSubclass" => some 2
  | "documentation" => some 3
  | _ => none

private def builtinVariableArity : String → Bool
  | "and" | "or" => true
  | _ => false

private abbrev ArityMap := Std.HashMap String (List Nat)
private abbrev MarkerMap := Std.HashMap String Bool

private structure ClassMetadata where
  arities : ArityMap
  variableArity : MarkerMap
  complete : Bool

private structure PropagationState where
  arities : ArityMap
  variableArity : MarkerMap
  changed : Bool

private def unionArities (left right : List Nat) : List Nat :=
  (left ++ right).eraseDups

private def seedClassArities : ArityMap :=
  fixedArityClasses.foldl
    (fun arities entry => arities.insert entry.1 [entry.2]) {}

private def seedVariableArity : MarkerMap :=
  ({} : MarkerMap).insert "VariableArityRelation" true

private def propagateClassEdge
    (state : PropagationState) (edge : String × String) : PropagationState :=
  let childArities := state.arities.getD edge.1 []
  let parentArities := state.arities.getD edge.2 []
  let combinedArities := unionArities childArities parentArities
  let arityChanged := combinedArities != childArities
  let arities :=
    if arityChanged then state.arities.insert edge.1 combinedArities
    else state.arities
  let childVariable := state.variableArity.getD edge.1 false
  let parentVariable := state.variableArity.getD edge.2 false
  let variableChanged := parentVariable && !childVariable
  let variableArity :=
    if variableChanged then state.variableArity.insert edge.1 true
    else state.variableArity
  ⟨arities, variableArity, state.changed || arityChanged || variableChanged⟩

/-- Compute the finite subclass closure once. Each non-final pass adds at least
one previously absent inherited fact, so one pass per subclass edge plus a
stability pass is sufficient. The completion flag makes exhaustion observable
rather than silently accepting a partial signature environment. -/
private def propagateClassMetadata :
    Nat → List (String × String) → ArityMap → MarkerMap → ClassMetadata
  | 0, _, arities, variableArity => ⟨arities, variableArity, false⟩
  | fuel + 1, edges, arities, variableArity =>
      let pass := edges.foldl propagateClassEdge
        ⟨arities, variableArity, false⟩
      if pass.changed then
        propagateClassMetadata fuel edges pass.arities pass.variableArity
      else
        ⟨pass.arities, pass.variableArity, true⟩

private structure OperatorMetadata where
  arities : ArityMap
  variableArity : MarkerMap
  domainMax : Std.HashMap String Nat
  hasInstance : MarkerMap

private def recordDomainPosition
    (state : OperatorMetadata) (relation : LocatedSymbol) (position : Nat) :
    OperatorMetadata :=
  let previous := state.domainMax.getD relation.text 0
  { state with domainMax := state.domainMax.insert relation.text (max previous position) }

private def addOperatorMetadata
    (classes : ClassMetadata) (state : OperatorMetadata)
    (declaration : SuoDeclaration) : OperatorMetadata :=
  match declaration with
  | .instance individual className =>
      let inherited := classes.arities.getD className.text []
      let current := state.arities.getD individual.text []
      let arities := state.arities.insert individual.text
        (unionArities current inherited)
      let variableArity :=
        if classes.variableArity.getD className.text false then
          state.variableArity.insert individual.text true
        else
          state.variableArity
      ⟨arities, variableArity, state.domainMax,
        state.hasInstance.insert individual.text true⟩
  | .domain relation position _ | .domainSubclass relation position _ =>
      recordDomainPosition state relation position
  | _ => state

private structure SignatureEnvironment where
  operatorArities : ArityMap
  classArities : ArityMap
  variableOperators : MarkerMap
  variableClasses : MarkerMap
  domainMax : Std.HashMap String Nat
  declaredIndividuals : MarkerMap
  closureComplete : Bool

private def signatureEnvironment
    (declarations : List SuoDeclaration) : SignatureEnvironment :=
  let edges := subclassEdges declarations
  let classes := propagateClassMetadata (edges.length + 1) edges
    seedClassArities seedVariableArity
  let operators := declarations.foldl (addOperatorMetadata classes)
    ⟨{}, {}, {}, {}⟩
  ⟨operators.arities, classes.arities, operators.variableArity,
    classes.variableArity, operators.domainMax, operators.hasInstance,
    classes.complete⟩

private def declaredArities
    (environment : SignatureEnvironment) (name : String) : List Nat :=
  if environment.variableOperators.getD name false then []
  else
    match environment.operatorArities.getD name [] with
    | [] =>
        if environment.declaredIndividuals.getD name false then
          match environment.domainMax[name]? with
          | some arity => [arity]
          | none => []
        else
          []
    | arities => arities

private def inheritedClassArities
    (environment : SignatureEnvironment) (name : String) : List Nat :=
  if environment.variableClasses.getD name false then []
  else environment.classArities.getD name []

private def isVariableArity
    (environment : SignatureEnvironment) (name : String) : Bool :=
  builtinVariableArity name ||
    environment.variableOperators.getD name false ||
    environment.variableClasses.getD name false

private def expectedArities
    (environment : SignatureEnvironment) (name : String) : List Nat :=
  match builtinFixedArity? name with
  | some arity => [arity]
  | none => declaredArities environment name

inductive SignatureIssueKind : Type
  | conflictingFixedArities (name : String) (arities : List Nat)
  | wrongApplicationArity (name : String) (expected actual : Nat)
  | domainBeyondFixedArity (name : String) (arity position : Nat)
  | internalFuelExhausted
  | internalClassClosureFuelExhausted
  deriving DecidableEq, Repr

structure SignatureIssue where
  kind : SignatureIssueKind
  span : SourceSpan
  deriving DecidableEq, Repr

structure OperatorSummary where
  name : String
  observedArities : List Nat
  firstSpan : SourceSpan
  deriving DecidableEq, Repr

private def addOperatorSummary
    (summaries : List OperatorSummary) (use : OperatorUse) :
    List OperatorSummary :=
  match summaries.find? fun summary => summary.name = use.name with
  | none => summaries ++ [⟨use.name, [use.arity], use.span⟩]
  | some _ =>
      summaries.map fun summary =>
        if summary.name = use.name then
          { summary with
            observedArities := (summary.observedArities ++ [use.arity]).eraseDups }
        else
          summary

private def summarizeUses (uses : List OperatorUse) : List OperatorSummary :=
  uses.foldl addOperatorSummary []

private def instanceNames (declarations : List SuoDeclaration) : List String :=
  (declarations.filterMap fun
    | .instance individual _ => some individual.text
    | _ => none).eraseDups

private def firstDeclarationSpan
    (declarations : List SuoDeclaration) (name : String) : Option SourceSpan :=
  declarations.findSome? fun
    | .instance individual _ =>
        if individual.text = name then some individual.span else none
    | _ => none

private def conflictIssues
    (environment : SignatureEnvironment)
    (declarations : List SuoDeclaration) :
    List SignatureIssue :=
  (instanceNames declarations).filterMap fun name =>
    let arities := declaredArities environment name
    if arities.length > 1 then
      match firstDeclarationSpan declarations name with
      | some span => some ⟨.conflictingFixedArities name arities, span⟩
      | none => none
    else
      none

private def fixedArityIssue? (use : OperatorUse) (expected : Nat) :
    Option SignatureIssue :=
  if expected = use.arity then none
  else some ⟨.wrongApplicationArity use.name expected use.arity, use.span⟩

private def useIssues
    (environment : SignatureEnvironment) (uses : List OperatorUse) :
    List SignatureIssue :=
  uses.filterMap fun use =>
    match expectedArities environment use.name with
    | [expected] => fixedArityIssue? use expected
    | _ => none

private def domainIssues
    (environment : SignatureEnvironment)
    (declarations : List SuoDeclaration) :
    List SignatureIssue :=
  declarations.filterMap fun
    | .domain relation position _ | .domainSubclass relation position _ =>
        match declaredArities environment relation.text with
        | [arity] =>
            if position ≤ arity then none
            else some ⟨.domainBeyondFixedArity relation.text arity position,
              relation.span⟩
        | _ => none
    | _ => none

structure SignatureAudit where
  issues : List SignatureIssue
  unresolvedOperators : List OperatorSummary
  classOperators : List OperatorSummary
  deriving Repr

/-- Check fixed operator arities and report the exact unresolved import
surface. A locally declared class of operators used directly as an operator is
reported separately because it requires an explicit higher-order policy. -/
def signatureAudit
    (fuel : Nat) (declarations : List SuoDeclaration) (parsed : Parsed) :
    SignatureAudit :=
  let applications := applicationInventory fuel parsed
  let summaries := summarizeUses applications.uses
  let environment := signatureEnvironment declarations
  let classOperators := summaries.filter fun summary =>
    (expectedArities environment summary.name).isEmpty &&
      !(inheritedClassArities environment summary.name).isEmpty
  let unresolved := summaries.filter fun summary =>
    (expectedArities environment summary.name).isEmpty &&
      (inheritedClassArities environment summary.name).isEmpty &&
      !isVariableArity environment summary.name
  let fuelIssues := applications.exhausted.map fun span =>
    ⟨SignatureIssueKind.internalFuelExhausted, span⟩
  let closureIssues :=
    if environment.closureComplete then []
    else
      match parsed.forms with
      | [] => []
      | first :: _ =>
          [⟨SignatureIssueKind.internalClassClosureFuelExhausted, first.span⟩]
  ⟨fuelIssues ++ closureIssues ++ conflictIssues environment declarations ++
      useIssues environment applications.uses ++
      domainIssues environment declarations,
    unresolved, classOperators⟩

private def signatureCanaryPos : SourcePos := ⟨0, 1, 1⟩
private def signatureCanarySpan : SourceSpan :=
  ⟨signatureCanaryPos, signatureCanaryPos⟩

example : builtinFixedArity? "not" = some 1 := by
  rfl

example : builtinFixedArity? "and" = none := by
  rfl

example :
    fixedArityIssue? ⟨"ethicalRelation", 2, signatureCanarySpan⟩ 2 = none := by
  rfl

example :
    (fixedArityIssue? ⟨"ethicalRelation", 1, signatureCanarySpan⟩ 2).map
        (·.kind) = some (.wrongApplicationArity "ethicalRelation" 2 1) := by
  rfl

end Mettapedia.Languages.KIF
