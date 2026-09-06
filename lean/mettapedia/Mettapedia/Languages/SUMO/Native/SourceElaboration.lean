import Mettapedia.Languages.SUMO.Native.ProofSearch
import Mettapedia.Languages.KIF.DeclarationDecode
import Std.Data.HashMap.Basic

/-!
# Direct SUO-KIF elaboration into the native SUMO calculus

This module assigns native logical meaning to source-located SUO-KIF trees.
It preserves the features that distinguish SUMO from a many-sorted first-order
encoding:

* regular variables and row variables have independent intrinsic scopes;
* an arbitrary term, including a variable, may occur in operator position;
* a formula-valued argument is retained as a formula intension;
* `KappaFn` binds its regular variable in its formula body;
* free source variables receive SUO-KIF's implicit universal closure.

Formula-valued argument positions are derived from SUMO `domain` declarations
whose class is `Formula`.  The source tree alone cannot distinguish a formula
argument from an ordinary functional term, so the declaration environment is
an explicit input rather than a heuristic.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.SourceElaboration

open Mettapedia.Languages.SUMO.Native

inductive DomainKind where
  | object
  | class
  deriving DecidableEq, Repr

/-- One source-declared restriction on an operator argument.  Positions are
one-indexed, as they are in SUMO `domain` and `domainSubclass` declarations. -/
structure DomainRestriction where
  operator : String
  position : Nat
  kind : DomainKind
  className : String
  deriving DecidableEq, Repr

/-- Source facts needed to classify formula arguments and elaborate implicit
domain guards.  The lists retain only finite source declarations; their
transitive consequences are computed by bounded graph traversal. -/
structure SourceSignature where
  formulaArguments : List (String × Nat) := []
  domainRestrictions : List DomainRestriction := []
  subclassEdges : List (String × String) := []
  subrelationEdges : List (String × String) := []
  operatorClasses : List (String × String) := []
  subclassAncestors : Std.HashMap String (List String) := {}
  subrelationAncestors : Std.HashMap String (List String) := {}
  restrictionsByOperator : Std.HashMap String (List DomainRestriction) := {}
  restrictionTable : List (String × List DomainRestriction) := []
  variableArityOperators : Std.HashMap String Bool := {}
  variableArityNames : List String := []
  operatorArityCache : Std.HashMap String Nat := {}
  operatorArities : List (String × Nat) := []
  deriving Repr

namespace SourceSignature

/-- The signature with no formula-valued argument declarations. -/
def empty : SourceSignature :=
  {}

private def parents (edges : List (String × String)) (child : String) :
    List String :=
  edges.filterMap fun edge => if edge.1 = child then some edge.2 else none

private def reachable
    (edges : List (String × String)) : Nat -> String -> String -> Bool
  | 0, child, parent => child = parent
  | fuel + 1, child, parent =>
      child = parent ||
        (parents edges child).any (reachable edges fuel · parent)

private structure ClosurePass where
  ancestors : Std.HashMap String (List String)
  changed : Bool

private def insertDirectParent
    (ancestors : Std.HashMap String (List String))
    (edge : String × String) : Std.HashMap String (List String) :=
  ancestors.insert edge.1 ((edge.2 :: ancestors.getD edge.1 []).eraseDups)

private def propagateEdge
    (state : ClosurePass) (edge : String × String) : ClosurePass :=
  let current := state.ancestors.getD edge.1 []
  let inherited := state.ancestors.getD edge.2 []
  let expanded := (current ++ edge.2 :: inherited).eraseDups
  if expanded = current then state
  else ⟨state.ancestors.insert edge.1 expanded, true⟩

private def closeEdges :
    Nat -> List (String × String) -> Std.HashMap String (List String) ->
      Std.HashMap String (List String)
  | 0, _, ancestors => ancestors
  | fuel + 1, edges, ancestors =>
      let pass := edges.foldl propagateEdge ⟨ancestors, false⟩
      if pass.changed then closeEdges fuel edges pass.ancestors
      else pass.ancestors

private def closureMap (edges : List (String × String)) :
    Std.HashMap String (List String) :=
  closeEdges (edges.length + 1) edges (edges.foldl insertDirectParent {})

private def inClosure
    (ancestors : Std.HashMap String (List String))
    (child parent : String) : Bool :=
  child = parent || (ancestors.getD child []).contains parent

/-- Lookup in the finite proof-readable mirror of an executable cache. -/
def lookupTable? {Value : Type}
    (table : List (String × Value)) (key : String) : Option Value :=
  (table.find? fun entry => entry.1 == key).map (·.2)

/-- Reflexive-transitive source-declared subclass reachability. -/
def isSubclass (signature : SourceSignature) (child parent : String) : Bool :=
  if signature.subclassAncestors.isEmpty then
    reachable signature.subclassEdges (signature.subclassEdges.length + 1)
      child parent
  else
    inClosure signature.subclassAncestors child parent

/-- Reflexive-transitive source-declared subrelation reachability. -/
def isSubrelation (signature : SourceSignature) (child parent : String) : Bool :=
  if signature.subrelationAncestors.isEmpty then
    reachable signature.subrelationEdges (signature.subrelationEdges.length + 1)
      child parent
  else
    inClosure signature.subrelationAncestors child parent

/-- Whether an operator is declared in a class below the requested class. -/
def isOperatorInClass
    (signature : SourceSignature) (operator className : String) : Bool :=
  signature.operatorClasses.any fun membership =>
    membership.1 = operator && signature.isSubclass membership.2 className

/-- Whether the operator has SUMO's repeat-the-last-domain arity discipline. -/
def isVariableArityOperator
    (signature : SourceSignature) (operator : String) : Bool :=
  (if signature.variableArityOperators.isEmpty then
      signature.variableArityNames.contains operator
    else
      signature.variableArityOperators.getD operator false) ||
    signature.isOperatorInClass operator "VariableArityRelation" ||
    signature.isOperatorInClass operator "VariableArityFunction"

/-- Restrictions inherited by an operator through source-declared
subrelation edges. -/
def applicableRestrictions
    (signature : SourceSignature) (operator : String) :
    List DomainRestriction :=
  if signature.restrictionsByOperator.isEmpty then
    match lookupTable? signature.restrictionTable operator with
    | some restrictions => restrictions
    | none =>
        signature.domainRestrictions.filter fun restriction =>
          signature.isSubrelation operator restriction.operator
  else
    signature.restrictionsByOperator.getD operator []

/-- Greatest one-based argument position mentioned by a restriction list. -/
def finalDeclaredPosition (restrictions : List DomainRestriction) : Nat :=
  restrictions.foldl (fun position restriction => max position restriction.position) 0

/-- Whether one source restriction makes a distinct restriction redundant. -/
def restrictionSubsumes
    (signature : SourceSignature)
    (specific general : DomainRestriction) : Bool :=
  specific.kind = general.kind &&
    specific.className != general.className &&
    signature.isSubclass specific.className general.className

def reduceRestrictions
    (signature : SourceSignature) (restrictions : List DomainRestriction) :
    List DomainRestriction :=
  let distinct := restrictions.eraseDups
  distinct.filter fun restriction =>
    !(distinct.any fun other => signature.restrictionSubsumes other restriction)

/-- Whether an already-stated restriction is at least as strong as a required
restriction of the same kind. -/
def restrictionCovers
    (signature : SourceSignature)
    (stated required : DomainRestriction) : Bool :=
  stated.kind = required.kind &&
    signature.isSubclass stated.className required.className

/-- Whether any domain declaration applies to this operator or a superrelation. -/
def hasDomainRestrictions
    (signature : SourceSignature) (operator : String) : Bool :=
  !(signature.applicableRestrictions operator).isEmpty

/-- All nonredundant restrictions applying at one argument position.  For a
variable-arity operator, positions beyond the final required position inherit
that final position's restrictions. -/
def argumentRestrictions
    (signature : SourceSignature) (operator : String) (position : Nat) :
    List DomainRestriction :=
  let applicable := signature.applicableRestrictions operator
  let finalPosition := finalDeclaredPosition applicable
  let selectedPosition :=
    if signature.isVariableArityOperator operator && finalPosition < position then
      finalPosition
    else position
  signature.reduceRestrictions
    (applicable.filter fun restriction =>
      restriction.position = selectedPosition)

/-- The minimum arity determined by the consecutive source domain sequence.
This follows SUMO-K's rule: positions are read from one upward and the first
missing position ends the declared sequence.  A later declaration after a gap
does not silently fill that gap. -/
private def computeDeclaredArity
    (signature : SourceSignature) (operator : String) : Nat :=
  let applicable := signature.applicableRestrictions operator
  let upper := finalDeclaredPosition applicable
  ((List.range upper).takeWhile fun offset =>
    !(signature.argumentRestrictions operator (offset + 1)).isEmpty).length

/-- The minimum arity determined by the consecutive source domain sequence.
The compiled hash table is used by source processing; its finite table mirror
keeps the same extracted fact transparent to kernel proofs. -/
def declaredArity
    (signature : SourceSignature) (operator : String) : Nat :=
  if signature.operatorArityCache.isEmpty then
    match lookupTable? signature.operatorArities operator with
    | some arity => arity
    | none => computeDeclaredArity signature operator
  else
    signature.operatorArityCache.getD operator 0

private def normalizedRestrictions
    (operator : String) (position : Nat)
    (restrictions : List DomainRestriction) : List DomainRestriction :=
  restrictions.map fun restriction =>
    { restriction with operator := operator, position := position }

/-- A row spread can receive one bounded-universal guard exactly when every
position it may occupy has the same restriction profile.  Variable-arity
positions beyond the final declaration repeat that final profile. -/
def uniformRowRestrictions
    (signature : SourceSignature) (operator : String) (firstPosition : Nat) :
    Option (List DomainRestriction) :=
  if !signature.isVariableArityOperator operator then none
  else
    let applicable := signature.applicableRestrictions operator
    let finalPosition := finalDeclaredPosition applicable
    let positions :=
      if firstPosition < finalPosition then
        (List.range (finalPosition - firstPosition + 1)).map
          (fun offset => firstPosition + offset)
      else [firstPosition]
    let profiles := positions.map fun position =>
      normalizedRestrictions operator firstPosition
        (signature.argumentRestrictions operator position)
    match profiles with
    | [] => some []
    | first :: rest =>
        if rest.all (· = first) then some first else none

/-- Whether an operator's argument position is declared to contain a formula. -/
def isFormulaArgument
    (signature : SourceSignature) (operator : String) (position : Nat) : Bool :=
  signature.formulaArguments.contains (operator, position) ||
    (signature.argumentRestrictions operator position).any fun restriction =>
      restriction.kind = .object &&
        signature.isSubclass restriction.className "Formula"

/-- Every operator named by a source fact that contributes to elaboration.
The order is the first-occurrence order of the finite source inventory. -/
def declaredOperators (signature : SourceSignature) : List String :=
  ((signature.domainRestrictions.map (·.operator)) ++
    (signature.formulaArguments.map (·.1)) ++
    (signature.operatorClasses.map (·.1)) ++
    (signature.subrelationEdges.flatMap fun edge => [edge.1, edge.2])).eraseDups

private def directSubrelation? (source : KIF.Term) :
    Option (String × String) :=
  match source with
  | .list _ [head, child, parent] =>
      match head.asSymbol?, child.asSymbol?, parent.asSymbol? with
      | some headName, some childName, some parentName =>
          if headName.text = "subrelation" then
            some (childName.text, parentName.text)
          else none
      | _, _, _ => none
  | _ => none

private def compileCaches (signature : SourceSignature) : SourceSignature :=
  let subclassAncestors := closureMap signature.subclassEdges
  let subrelationAncestors := closureMap signature.subrelationEdges
  let operators := signature.declaredOperators
  let restrictionsByOperator := operators.foldl
    (fun cache operator =>
      let restrictions := signature.domainRestrictions.filter fun restriction =>
        inClosure subrelationAncestors operator restriction.operator
      cache.insert operator restrictions)
    ({} : Std.HashMap String (List DomainRestriction))
  let restrictionTable := operators.map fun operator =>
    (operator, restrictionsByOperator.getD operator [])
  let variableArityOperators := signature.operatorClasses.foldl
    (fun cache membership =>
      if inClosure subclassAncestors membership.2 "VariableArityRelation" ||
          inClosure subclassAncestors membership.2 "VariableArityFunction" then
        cache.insert membership.1 true
      else cache)
    ({} : Std.HashMap String Bool)
  let variableArityNames := operators.filter fun operator =>
    variableArityOperators.getD operator false
  let cachedSignature : SourceSignature :=
    { signature with
      subclassAncestors := subclassAncestors
      subrelationAncestors := subrelationAncestors
      restrictionsByOperator := restrictionsByOperator
      restrictionTable := restrictionTable
      variableArityOperators := variableArityOperators
      variableArityNames := variableArityNames
      operatorArityCache := {}
      operatorArities := [] }
  let operatorArities := operators.map fun operator =>
    (operator, computeDeclaredArity cachedSignature operator)
  let operatorArityCache := operatorArities.foldl
    (fun cache entry => cache.insert entry.1 entry.2)
    ({} : Std.HashMap String Nat)
  { cachedSignature with
    subclassAncestors := subclassAncestors
    subrelationAncestors := subrelationAncestors
    restrictionsByOperator := restrictionsByOperator
    restrictionTable := restrictionTable
    variableArityOperators := variableArityOperators
    variableArityNames := variableArityNames
    operatorArityCache := operatorArityCache
    operatorArities := operatorArities }

/-- Extract formula-valued argument positions from decoded SUMO declarations. -/
def ofDeclarations (declarations : List KIF.SuoDeclaration) : SourceSignature :=
  compileCaches
  { formulaArguments :=
      (declarations.filterMap fun
        | .domain relation position className =>
            if className.text = "Formula" then some (relation.text, position)
            else none
        | _ => none).eraseDups
    domainRestrictions :=
      (declarations.filterMap fun
        | .domain relation position className =>
            some ⟨relation.text, position, .object, className.text⟩
        | .domainSubclass relation position className =>
            some ⟨relation.text, position, .class, className.text⟩
        | _ => none).eraseDups
    subclassEdges :=
      (declarations.filterMap fun
        | .subclass child parent =>
            parent.asSymbol?.map fun parentName =>
              (child.text, parentName.text)
        | _ => none).eraseDups
    operatorClasses :=
      (declarations.filterMap fun
        | .instance individual className =>
            some (individual.text, className.text)
        | _ => none).eraseDups }

/-- Build the source signature and include direct `subrelation` facts retained
as ordinary source formulas by declaration decoding. -/
def ofDeclarationsAndForms
    (declarations : List KIF.SuoDeclaration) (forms : List KIF.Term) :
    SourceSignature :=
  compileCaches
    { ofDeclarations declarations with
      subrelationEdges := (forms.filterMap directSubrelation?).eraseDups }

end SourceSignature

inductive ElaborationIssueKind : Type
  | expectedFormula
  | emptyApplication
  | unboundRegularVariable (name : String)
  | unboundRowVariable (name : String)
  | rowVariableInTermPosition (name : String)
  | rowVariableInOperatorPosition (name : String)
  | wrongLogicalArity (head : String) (expected actual : Nat)
  | expectedNonemptyBinderList (quantifier : String)
  | expectedBinderList (quantifier : String)
  | expectedBinderVariable (quantifier : String)
  | wrongKappaArity (actual : Nat)
  | expectedKappaRegularVariable
  | internalFuelExhausted
  deriving DecidableEq, Repr

structure ElaborationIssue where
  kind : ElaborationIssueKind
  span : KIF.SourceSpan
  deriving DecidableEq, Repr

private abbrev NativeTerm (ordinary rows : Nat) :=
  Term String String ordinary rows

private abbrev NativeSpine (ordinary rows : Nat) :=
  Spine String String ordinary rows

private abbrev NativeFormula (ordinary rows : Nat) :=
  Formula String String ordinary rows

private def lookupName (name : String) :
    (names : List String) -> Option (Fin names.length)
  | [] => none
  | current :: rest =>
      if name = current then some 0
      else (lookupName name rest).map Fin.succ

private def symbolText? : KIF.Term -> Option String
  | .atom value =>
      if value.kind = .symbol then some value.text else none
  | .list _ _ => none

mutual
  /-- Number of source nodes in one KIF tree. -/
  private def sourceWeight : KIF.Term -> Nat
    | .atom _ => 1
    | .list _ children => 1 + sourceWeights children

  /-- Number of source nodes in a forest. -/
  private def sourceWeights : List KIF.Term -> Nat
    | [] => 0
    | source :: rest => sourceWeight source + sourceWeights rest
end

private def wrongArity {α : Type}
    (head : KIF.Atom) (expected actual : Nat) :
    Except ElaborationIssue α :=
  .error ⟨.wrongLogicalArity head.text expected actual, head.span⟩

private inductive QuantifierKind
  | universal
  | existential

private def QuantifierKind.object
    {ordinary rows : Nat}
    (kind : QuantifierKind)
    (body : NativeFormula (ordinary + 1) rows) :
    NativeFormula ordinary rows :=
  match kind with
  | .universal => .allObject body
  | .existential => .someObject body

private def QuantifierKind.row
    {ordinary rows : Nat}
    (kind : QuantifierKind)
    (body : NativeFormula ordinary (rows + 1)) :
    NativeFormula ordinary rows :=
  match kind with
  | .universal => .allRow body
  | .existential => .someRow body

private def conjunction
    {ordinary rows : Nat} (formulas : List (NativeFormula ordinary rows)) :
    NativeFormula ordinary rows :=
  formulas.foldr Formula.and .top

private def disjunction
    {ordinary rows : Nat} (formulas : List (NativeFormula ordinary rows)) :
    NativeFormula ordinary rows :=
  formulas.foldr Formula.or .bottom

private structure SourceName where
  kind : KIF.AtomKind
  text : String
  span : KIF.SourceSpan
  deriving DecidableEq, Repr

mutual
  private inductive NamedTerm where
    | variable (name : SourceName)
    | constant (name : String)
    | literal (value : String)
    | application (operator : NamedTerm) (arguments : NamedSpine)
    | quote (body : NamedFormula)
    | kappa (binder : SourceName) (body : NamedFormula)

  private inductive NamedSpine where
    | nil
    | term (value : NamedTerm) (rest : NamedSpine)
    | row (name : SourceName) (rest : NamedSpine)

  private inductive NamedFormula where
    | top
    | bottom
    | atom (operator : NamedTerm) (arguments : NamedSpine)
    | asserted (value : NamedTerm)
    | equal (left right : NamedTerm)
    | not (body : NamedFormula)
    | and (left right : NamedFormula)
    | or (left right : NamedFormula)
    | implies (left right : NamedFormula)
    | iff (left right : NamedFormula)
    | allObject (binder : SourceName) (body : NamedFormula)
    | someObject (binder : SourceName) (body : NamedFormula)
    | allRow (binder : SourceName) (body : NamedFormula)
    | someRow (binder : SourceName) (body : NamedFormula)
end

private inductive ClassSort
  | term
  | spine
  | formula

private def ClassResult : ClassSort -> Type
  | .term => NamedTerm
  | .spine => NamedSpine
  | .formula => NamedFormula

private inductive ClassRequest : ClassSort -> Type
  | term (source : KIF.Term) : ClassRequest .term
  | arguments (staticHead : Option String) (position : Nat)
      (sources : List KIF.Term) : ClassRequest .spine
  | conjunction (sources : List KIF.Term) : ClassRequest .formula
  | disjunction (sources : List KIF.Term) : ClassRequest .formula
  | quantified (kind : QuantifierKind) (quantifier : String)
      (binders : List KIF.Term) (body : KIF.Term) : ClassRequest .formula
  | formula (source : KIF.Term) : ClassRequest .formula

private def requestSpan : {sort : ClassSort} -> ClassRequest sort -> KIF.SourceSpan
  | _, .term source | _, .formula source => source.span
  | _, .arguments _ _ sources | _, .conjunction sources |
      _, .disjunction sources =>
      match sources with
      | source :: _ => source.span
      | [] => ⟨KIF.SourcePos.start, KIF.SourcePos.start⟩
  | _, .quantified _ _ _ body => body.span

private def classify (signature : SourceSignature) :
    (fuel : Nat) -> {sort : ClassSort} -> (request : ClassRequest sort) ->
      Except ElaborationIssue (ClassResult sort)
  | 0, _, request => .error ⟨.internalFuelExhausted, requestSpan request⟩
  | fuel + 1, _, .term source =>
      match source with
      | .atom value =>
          match value.kind with
          | .symbol => .ok (.constant value.text)
          | .stringLiteral => .ok (.literal value.text)
          | .regularVariable =>
              .ok (.variable ⟨value.kind, value.text, value.span⟩)
          | .sequenceVariable =>
              .error ⟨.rowVariableInTermPosition value.text, value.span⟩
      | .list span [] => .error ⟨.emptyApplication, span⟩
      | .list _ (head :: arguments) =>
          match symbolText? head with
          | some "KappaFn" =>
              match arguments with
              | [.atom binder, body] =>
                  if binder.kind = .regularVariable then do
                    let formula <- classify signature fuel (.formula body)
                    pure (.kappa ⟨binder.kind, binder.text, binder.span⟩ formula)
                  else .error ⟨.expectedKappaRegularVariable, binder.span⟩
              | [binder, _] =>
                  .error ⟨.expectedKappaRegularVariable, binder.span⟩
              | _ => .error ⟨.wrongKappaArity arguments.length, head.span⟩
          | staticHead => do
              let operator <- classify signature fuel (.term head)
              let spine <-
                classify signature fuel (.arguments staticHead 1 arguments)
              pure (.application operator spine)
  | fuel + 1, _, .arguments staticHead position sources =>
      match sources with
      | [] => .ok .nil
      | argument :: rest => do
          let tail <-
            classify signature fuel (.arguments staticHead (position + 1) rest)
          match argument with
          | .atom value =>
              if value.kind = .sequenceVariable then
                pure (.row ⟨value.kind, value.text, value.span⟩ tail)
              else
                let term <- classify signature fuel (.term argument)
                pure (.term term tail)
          | .list _ _ =>
              match staticHead with
              | some operator =>
                  if signature.isFormulaArgument operator position then
                    let body <- classify signature fuel (.formula argument)
                    pure (.term (.quote body) tail)
                  else
                    let term <- classify signature fuel (.term argument)
                    pure (.term term tail)
              | none =>
                  let term <- classify signature fuel (.term argument)
                  pure (.term term tail)
  | fuel + 1, _, .conjunction sources =>
      match sources with
      | [] => .ok .top
      | source :: rest => do
          let left <- classify signature fuel (.formula source)
          let right <- classify signature fuel (.conjunction rest)
          pure (.and left right)
  | fuel + 1, _, .disjunction sources =>
      match sources with
      | [] => .ok .bottom
      | source :: rest => do
          let left <- classify signature fuel (.formula source)
          let right <- classify signature fuel (.disjunction rest)
          pure (.or left right)
  | fuel + 1, _, .quantified kind quantifier binders body =>
      match binders with
      | [] => classify signature fuel (.formula body)
      | binder :: rest =>
          match binder with
          | .atom value =>
              let name : SourceName := ⟨value.kind, value.text, value.span⟩
              match value.kind with
              | .regularVariable => do
                  let nested <-
                    classify signature fuel (.quantified kind quantifier rest body)
                  pure (match kind with
                    | .universal => .allObject name nested
                    | .existential => .someObject name nested)
              | .sequenceVariable => do
                  let nested <-
                    classify signature fuel (.quantified kind quantifier rest body)
                  pure (match kind with
                    | .universal => .allRow name nested
                    | .existential => .someRow name nested)
              | _ => .error ⟨.expectedBinderVariable quantifier, value.span⟩
          | .list span _ => .error ⟨.expectedBinderVariable quantifier, span⟩
  | fuel + 1, _, .formula source =>
      match source with
      | .atom value =>
          if value.kind = .regularVariable then
            .ok (.asserted (.variable ⟨value.kind, value.text, value.span⟩))
          else
            .error ⟨.expectedFormula, value.span⟩
      | .list span [] => .error ⟨.expectedFormula, span⟩
      | .list _ (head :: arguments) =>
          match head with
          | .atom headAtom =>
              if headAtom.kind = .symbol then
                match headAtom.text with
                | "not" =>
                    match arguments with
                    | [body] => (classify signature fuel (.formula body)).map .not
                    | _ => wrongArity headAtom 1 arguments.length
                | "and" => classify signature fuel (.conjunction arguments)
                | "or" => classify signature fuel (.disjunction arguments)
                | "=>" =>
                    match arguments with
                    | [left, right] => do
                        let leftBody <- classify signature fuel (.formula left)
                        let rightBody <- classify signature fuel (.formula right)
                        pure (.implies leftBody rightBody)
                    | _ => wrongArity headAtom 2 arguments.length
                | "<=>" =>
                    match arguments with
                    | [left, right] => do
                        let leftBody <- classify signature fuel (.formula left)
                        let rightBody <- classify signature fuel (.formula right)
                        pure (.iff leftBody rightBody)
                    | _ => wrongArity headAtom 2 arguments.length
                | "equal" =>
                    match arguments with
                    | [left, right] => do
                        let leftTerm <- classify signature fuel (.term left)
                        let rightTerm <- classify signature fuel (.term right)
                        pure (.equal leftTerm rightTerm)
                    | _ => wrongArity headAtom 2 arguments.length
                | "forall" | "exists" =>
                    match arguments with
                    | [binderSource, body] =>
                        match binderSource with
                        | .list binderSpan binders =>
                            if binders.isEmpty then
                              .error ⟨.expectedNonemptyBinderList headAtom.text,
                                binderSpan⟩
                            else
                              classify signature fuel
                                (.quantified
                                  (if headAtom.text = "forall" then
                                    .universal else .existential)
                                  headAtom.text binders body)
                        | _ => .error ⟨.expectedBinderList headAtom.text,
                            binderSource.span⟩
                    | _ => wrongArity headAtom 2 arguments.length
                | _ => do
                    let operator <- classify signature fuel (.term head)
                    let spine <- classify signature fuel
                      (.arguments (some headAtom.text) 1 arguments)
                    pure (.atom operator spine)
              else if headAtom.kind = .sequenceVariable then
                .error ⟨.rowVariableInOperatorPosition headAtom.text,
                  headAtom.span⟩
              else do
                let operator <- classify signature fuel (.term head)
                let spine <- classify signature fuel (.arguments none 1 arguments)
                pure (.atom operator spine)
          | .list _ _ => do
              let operator <- classify signature fuel (.term head)
              let spine <- classify signature fuel (.arguments none 1 arguments)
              pure (.atom operator spine)

mutual
  private def resolveTerm (objects rows : List String) : NamedTerm ->
      Except ElaborationIssue (NativeTerm objects.length rows.length)
    | .variable name =>
        match lookupName name.text objects with
        | some index => .ok (.var index)
        | none => .error ⟨.unboundRegularVariable name.text, name.span⟩
    | .constant name => .ok (.constant name)
    | .literal value => .ok (.literal value)
    | .application operator arguments => do
        let resolvedOperator <- resolveTerm objects rows operator
        let resolvedArguments <- resolveSpine objects rows arguments
        pure (.application resolvedOperator resolvedArguments)
    | .quote body => (resolveFormula objects rows body).map .quote
    | .kappa binder body =>
        (resolveFormula (binder.text :: objects) rows body).map .kappa

  private def resolveSpine (objects rows : List String) : NamedSpine ->
      Except ElaborationIssue (NativeSpine objects.length rows.length)
    | .nil => .ok .nil
    | .term value rest => do
        let resolvedValue <- resolveTerm objects rows value
        let resolvedRest <- resolveSpine objects rows rest
        pure (.term resolvedValue resolvedRest)
    | .row name rest =>
        match lookupName name.text rows with
        | none => .error ⟨.unboundRowVariable name.text, name.span⟩
        | some index => (resolveSpine objects rows rest).map (.row index)

  private def resolveFormula (objects rows : List String) : NamedFormula ->
      Except ElaborationIssue (NativeFormula objects.length rows.length)
    | .top => .ok .top
    | .bottom => .ok .bottom
    | .atom operator arguments => do
        let resolvedOperator <- resolveTerm objects rows operator
        let resolvedArguments <- resolveSpine objects rows arguments
        pure (.atom resolvedOperator resolvedArguments)
    | .asserted value => (resolveTerm objects rows value).map .asserted
    | .equal left right => do
        let resolvedLeft <- resolveTerm objects rows left
        let resolvedRight <- resolveTerm objects rows right
        pure (.equal resolvedLeft resolvedRight)
    | .not body => (resolveFormula objects rows body).map .not
    | .and left right => do
        let resolvedLeft <- resolveFormula objects rows left
        let resolvedRight <- resolveFormula objects rows right
        pure (.and resolvedLeft resolvedRight)
    | .or left right => do
        let resolvedLeft <- resolveFormula objects rows left
        let resolvedRight <- resolveFormula objects rows right
        pure (.or resolvedLeft resolvedRight)
    | .implies left right => do
        let resolvedLeft <- resolveFormula objects rows left
        let resolvedRight <- resolveFormula objects rows right
        pure (.implies resolvedLeft resolvedRight)
    | .iff left right => do
        let resolvedLeft <- resolveFormula objects rows left
        let resolvedRight <- resolveFormula objects rows right
        pure (.iff resolvedLeft resolvedRight)
    | .allObject binder body =>
        (resolveFormula (binder.text :: objects) rows body).map .allObject
    | .someObject binder body =>
        (resolveFormula (binder.text :: objects) rows body).map .someObject
    | .allRow binder body =>
        (resolveFormula objects (binder.text :: rows) body).map .allRow
    | .someRow binder body =>
        (resolveFormula objects (binder.text :: rows) body).map .someRow
end

private def sameSourceName (left right : SourceName) : Bool :=
  left.kind = right.kind && left.text = right.text

private def addSourceName (names : List SourceName) (name : SourceName) :
    List SourceName :=
  if names.any (sameSourceName name) then names else names ++ [name]

private def mergeSourceNames (left right : List SourceName) : List SourceName :=
  right.foldl addSourceName left

private def removeSourceName (binder : SourceName) (names : List SourceName) :
    List SourceName :=
  names.filter fun name => !sameSourceName binder name

mutual
  private def freeTermNames : NamedTerm -> List SourceName
    | .variable name => [name]
    | .constant _ | .literal _ => []
    | .application operator arguments =>
        mergeSourceNames (freeTermNames operator) (freeSpineNames arguments)
    | .quote body => freeFormulaNames body
    | .kappa binder body => removeSourceName binder (freeFormulaNames body)

  private def freeSpineNames : NamedSpine -> List SourceName
    | .nil => []
    | .term value rest =>
        mergeSourceNames (freeTermNames value) (freeSpineNames rest)
    | .row name rest => addSourceName (freeSpineNames rest) name

  private def freeFormulaNames : NamedFormula -> List SourceName
    | .top | .bottom => []
    | .atom operator arguments =>
        mergeSourceNames (freeTermNames operator) (freeSpineNames arguments)
    | .asserted value => freeTermNames value
    | .equal left right => mergeSourceNames (freeTermNames left) (freeTermNames right)
    | .not body => freeFormulaNames body
    | .and left right | .or left right | .implies left right | .iff left right =>
        mergeSourceNames (freeFormulaNames left) (freeFormulaNames right)
    | .allObject binder body | .someObject binder body |
        .allRow binder body | .someRow binder body =>
        removeSourceName binder (freeFormulaNames body)
end

private def universallyClose : List SourceName -> NamedFormula -> NamedFormula
  | [], body => body
  | name :: rest, body =>
      match name.kind with
      | .regularVariable => .allObject name (universallyClose rest body)
      | .sequenceVariable => .allRow name (universallyClose rest body)
      | _ => universallyClose rest body

/-- Elaborate one source term in explicit name scopes. -/
def elaborateTerm
    (signature : SourceSignature) (objects rows : List String)
    (source : KIF.Term) :
    Except ElaborationIssue (NativeTerm objects.length rows.length) := do
  let named <- classify signature (sourceWeight source + 1) (.term source)
  resolveTerm objects rows named

/-- Elaborate one source formula in explicit name scopes. -/
def elaborateFormula
    (signature : SourceSignature) (objects rows : List String)
    (source : KIF.Term) :
    Except ElaborationIssue (NativeFormula objects.length rows.length) := do
  let named <- classify signature (sourceWeight source + 1) (.formula source)
  resolveFormula objects rows named

/-- Elaborate one top-level SUO-KIF formula and universally close exactly its
free regular and row variables, in first-occurrence order. -/
def elaborateSentence
    (signature : SourceSignature) (source : KIF.Term) :
    Except ElaborationIssue (Sentence String String) := do
  let named <- classify signature (sourceWeight source + 1) (.formula source)
  resolveFormula [] [] (universallyClose (freeFormulaNames named) named)

inductive SourceIssue : Type
  | lexical (failure : KIF.LexError)
  | structural (failures : List KIF.ParseError)
  | expectedOneForm (actual : Nat)
  | elaboration (failure : ElaborationIssue)
  deriving DecidableEq, Repr

/-- Lex, parse, and elaborate exactly one source formula. -/
def elaborateSource
    (signature : SourceSignature) (source : String) :
    Except SourceIssue (Sentence String String) := do
  let lexed <- (KIF.lex source).mapError .lexical
  let parsed := KIF.parse lexed
  if parsed.errors.isEmpty then
    match parsed.forms with
    | [form] => (elaborateSentence signature form).mapError .elaboration
    | forms => .error (.expectedOneForm forms.length)
  else
    .error (.structural parsed.errors)

end Mettapedia.Languages.SUMO.Native.SourceElaboration
