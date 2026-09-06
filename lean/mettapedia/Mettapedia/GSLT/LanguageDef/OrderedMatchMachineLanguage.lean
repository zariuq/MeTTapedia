import Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
import Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
import Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation

/-!
# The ordered-match machine language

The fused decision programs of the generic lowering (constructor switches,
projection drops, ordered rule attempts with residual structural patterns,
and first-order rule plans at the leaves) are here a language definition.
One complete run of the machine on a subject is one rewrite step of the
source language whose rules were compiled: the machine dispatches on the
constructor key of the focused subject, filters a leaf by its residual
structural patterns, matches the leaf's left-hand side with the
binding-decision rules, evaluates the leaf's relation premises in authored
order through the source relation environment, instantiates the leaf's
right-hand side template, and stops at a result.

Nondeterminism is fallback: an attempt and its continuation are both
successors, exactly as the fused evaluator lists every successful leaf.  The
eight binding-decision rules are included unchanged; matching ends in a
frame that hands the bindings to premise evaluation.  Premise evaluation
consults the source relation environment through one reflective catalog
relation whose meaning is the ordinary relation-query step of the source
language; the remaining catalog relations are total primitive observations
and constructions on encoded terms (constructor key, unfolding a subject
into its children, list append, binding lookup, bound-variable and
application construction).

The typed reference machine below is a proof device for the exactness
theorem of the next module; no downstream theorem consumes it directly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.PatternPlanBindingDecisionCompilation
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation (PatternPlan PremisePlan)
open Mettapedia.GSLT.LanguageDef.BindingDecisionLanguage
  (encodeName decodeName? decodeName?_encodeName encodePath decodePath? encodeBindings
    decodeBindings? decodeBindings?_encodeBindings encodeDecision isBoundAt isConstructorOf
    pathType indexType nameType subjectType decisionType bindingsType frameType kontType
    stateType metavariable runPattern retPattern donePattern succeedPattern
    capturePattern checkBoundPattern checkConstructorPattern joinPattern nilBindingsPattern
    bindPattern joinRightPattern joinMergePattern knilPattern kconsPattern projectRelation
    boundRelation constructorRelation mergeRelation succeedRewrite captureRewrite
    checkBoundRewrite checkConstructorRewrite joinRewrite joinRightRewrite joinMergeRewrite
    finishRewrite rowWhen)
open Mettapedia.GSLT.Core.ConservativeExtension (encodeNat decodeNat? decodeNat?_encodeNat)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis

namespace OPM

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
  (Pattern ConstructorKey Subject structuralMatch structuralMatchList)

end OPM

namespace Fusion

export Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion (CompiledRule Program Branches)

end Fusion

/-! ## Typed data -/

/-- Rigid head observations of the row-to-matrix bridge. -/
abbrev Head := Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation.Matrix.Head

abbrev Key := OPM.ConstructorKey Head

abbrev MatrixPattern := OPM.Pattern Head

/-- The machine's plan at a leaf: the left-hand side as a binding decision,
the ordered relation premises, and the right-hand side template. -/
structure MachinePlan where
  decision : Decision
  premises : List PremisePlan
  template : PatternPlan

abbrev Leaf := Fusion.CompiledRule Nat MachinePlan

abbrev Program := Fusion.Program Head Nat MachinePlan

abbrev Branches := Fusion.Branches Head Nat MachinePlan

/-- The rigid head of a subject, as the row-to-matrix bridge observes it. -/
def subjectHead : Pattern → Head
  | .fvar name => .freeVariable name
  | .bvar index => .boundVariable index
  | .apply constructor arguments => .application constructor arguments.length
  | .lambda _ _ => .lambda
  | .multiLambda arity _ _ => .multiLambda arity
  | .subst _ _ => .substitution
  | .collection kind _ _ => .collection kind

/-- The children a subject exposes to the decision program. -/
def subjectChildren : Pattern → List Pattern
  | .fvar _ => []
  | .bvar _ => []
  | .apply _ arguments => arguments
  | .lambda _ body => [body]
  | .multiLambda _ _ body => [body]
  | .subst body replacement => [body, replacement]
  | .collection _ _ _ => []

/-- The constructor key of a subject. -/
def subjectKey (subject : Pattern) : Key :=
  ⟨subjectHead subject, (subjectChildren subject).length⟩

/-- Lowering a subject observes exactly the head and the children above. -/
theorem lowerSubject_eq (subject : Pattern) :
    Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject =
      .node (subjectHead subject)
        ((subjectChildren subject).map
          Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation.Matrix.lowerSubject) := by
  cases subject <;>
    simp [Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilation.Matrix.lowerSubject,
      subjectHead, subjectChildren]

/-- Template variables read their binding, or stay free: the metavariable
case of plan instantiation. -/
def lookupOrVariable (bindings : Bindings) (name : String) : Pattern :=
  match bindings.find? (fun entry => entry.1 == name) with
  | some (_, value) => value
  | none => .fvar name

theorem instantiate_metavariable (bindings : Bindings) (name : String) :
    PatternPlan.instantiate bindings (.metavariable name) = lookupOrVariable bindings name := by
  rw [PatternPlan.instantiate]
  rfl

/-! ## Encodings -/

def encodeKind : CollType → Pattern
  | .vec => .apply "mm-vec" []
  | .hashBag => .apply "mm-bag" []
  | .hashSet => .apply "mm-set" []

def decodeKind? : Pattern → Option CollType
  | .apply "mm-vec" [] => some .vec
  | .apply "mm-bag" [] => some .hashBag
  | .apply "mm-set" [] => some .hashSet
  | _ => none

@[simp] theorem decodeKind?_encodeKind : ∀ kind : CollType, decodeKind? (encodeKind kind) = some kind
  | .vec => rfl
  | .hashBag => rfl
  | .hashSet => rfl

def encodeHead : Head → Pattern
  | .freeVariable name => .apply "mm-head-fvar" [encodeName name]
  | .boundVariable index => .apply "mm-head-bvar" [encodeNat index]
  | .application constructor arity => .apply "mm-head-app" [encodeName constructor, encodeNat arity]
  | .lambda => .apply "mm-head-lambda" []
  | .multiLambda arity => .apply "mm-head-multi" [encodeNat arity]
  | .substitution => .apply "mm-head-subst" []
  | .collection kind => .apply "mm-head-coll" [encodeKind kind]

def decodeHead? : Pattern → Option Head
  | .apply "mm-head-fvar" [name] => (decodeName? name).map .freeVariable
  | .apply "mm-head-bvar" [index] => (decodeNat? index).map .boundVariable
  | .apply "mm-head-app" [constructor, arity] => do
      let head ← decodeName? constructor
      let count ← decodeNat? arity
      some (.application head count)
  | .apply "mm-head-lambda" [] => some .lambda
  | .apply "mm-head-multi" [arity] => (decodeNat? arity).map .multiLambda
  | .apply "mm-head-subst" [] => some .substitution
  | .apply "mm-head-coll" [kind] => (decodeKind? kind).map .collection
  | _ => none

@[simp] theorem decodeHead?_encodeHead : ∀ head : Head, decodeHead? (encodeHead head) = some head
  | .freeVariable name => by simp [encodeHead, decodeHead?, encodeName, decodeName?]
  | .boundVariable index => by simp [encodeHead, decodeHead?]
  | .application constructor arity => by simp [encodeHead, decodeHead?, encodeName, decodeName?]
  | .lambda => rfl
  | .multiLambda arity => by simp [encodeHead, decodeHead?]
  | .substitution => rfl
  | .collection kind => by simp [encodeHead, decodeHead?]

def encodeKey (key : Key) : Pattern := .apply "mm-key" [encodeHead key.head, encodeNat key.arity]

def decodeKey? : Pattern → Option Key
  | .apply "mm-key" [head, arity] => do
      let decodedHead ← decodeHead? head
      let decodedArity ← decodeNat? arity
      some ⟨decodedHead, decodedArity⟩
  | _ => none

@[simp] theorem decodeKey?_encodeKey (key : Key) : decodeKey? (encodeKey key) = some key := by
  simp [encodeKey, decodeKey?]

theorem encodeKey_injective : Function.Injective encodeKey := by
  intro left right equal
  have := congrArg decodeKey? equal
  simpa using this

mutual
  def encodeMatrixPattern : MatrixPattern → Pattern
    | .wildcard => .apply "mm-wild" []
    | .node head children =>
        .apply "mm-node" [encodeKey ⟨head, children.length⟩, encodePatterns children]

  def encodePatterns : List MatrixPattern → Pattern
    | [] => .apply "mm-pnil" []
    | pattern :: patterns => .apply "mm-pcons" [encodeMatrixPattern pattern, encodePatterns patterns]
end

mutual
  def decodeMatrixPattern? : Pattern → Option MatrixPattern
    | .apply "mm-wild" [] => some .wildcard
    | .apply "mm-node" [key, children] => do
        let decodedKey ← decodeKey? key
        let decodedChildren ← decodePatterns? children
        if decodedKey.arity = decodedChildren.length then
          some (.node decodedKey.head decodedChildren)
        else
          none
    | _ => none

  def decodePatterns? : Pattern → Option (List MatrixPattern)
    | .apply "mm-pnil" [] => some []
    | .apply "mm-pcons" [pattern, patterns] => do
        let head ← decodeMatrixPattern? pattern
        let tail ← decodePatterns? patterns
        some (head :: tail)
    | _ => none
end

mutual
  theorem decodeMatrixPattern?_encodeMatrixPattern : ∀ pattern : MatrixPattern,
      decodeMatrixPattern? (encodeMatrixPattern pattern) = some pattern
    | .wildcard => rfl
    | .node head children => by
        simp [encodeMatrixPattern, decodeMatrixPattern?,
          decodePatterns?_encodePatterns children]

  theorem decodePatterns?_encodePatterns : ∀ patterns : List MatrixPattern,
      decodePatterns? (encodePatterns patterns) = some patterns
    | [] => rfl
    | pattern :: patterns => by
        simp [encodePatterns, decodePatterns?,
          decodeMatrixPattern?_encodeMatrixPattern pattern,
          decodePatterns?_encodePatterns patterns]
end

attribute [simp] decodeMatrixPattern?_encodeMatrixPattern decodePatterns?_encodePatterns

def encodeCursor : List Pattern → Pattern
  | [] => .apply "mm-cnil" []
  | subject :: cursor => .apply "mm-ccons" [subject, encodeCursor cursor]

def decodeCursor? : Pattern → Option (List Pattern)
  | .apply "mm-cnil" [] => some []
  | .apply "mm-ccons" [subject, cursor] => (decodeCursor? cursor).map (subject :: ·)
  | _ => none

@[simp] theorem decodeCursor?_encodeCursor : ∀ cursor : List Pattern,
    decodeCursor? (encodeCursor cursor) = some cursor
  | [] => rfl
  | subject :: cursor => by simp [encodeCursor, decodeCursor?, decodeCursor?_encodeCursor cursor]

mutual
  def encodeTemplate : PatternPlan → Pattern
    | .metavariable name => .apply "mm-tvar" [encodeName name]
    | .bound index => .apply "mm-tbvar" [encodeNat index]
    | .application constructor arguments =>
        .apply "mm-tapp" [encodeName constructor, encodeTemplates arguments]

  def encodeTemplates : List PatternPlan → Pattern
    | [] => .apply "mm-tnil" []
    | template :: templates => .apply "mm-tcons" [encodeTemplate template, encodeTemplates templates]
end

mutual
  def decodeTemplate? : Pattern → Option PatternPlan
    | .apply "mm-tvar" [name] => (decodeName? name).map .metavariable
    | .apply "mm-tbvar" [index] => (decodeNat? index).map .bound
    | .apply "mm-tapp" [constructor, arguments] => do
        let head ← decodeName? constructor
        let decodedArguments ← decodeTemplates? arguments
        some (.application head decodedArguments)
    | _ => none

  def decodeTemplates? : Pattern → Option (List PatternPlan)
    | .apply "mm-tnil" [] => some []
    | .apply "mm-tcons" [template, templates] => do
        let head ← decodeTemplate? template
        let tail ← decodeTemplates? templates
        some (head :: tail)
    | _ => none
end

mutual
  theorem decodeTemplate?_encodeTemplate : ∀ template : PatternPlan,
      decodeTemplate? (encodeTemplate template) = some template
    | .metavariable name => by simp [encodeTemplate, decodeTemplate?, encodeName, decodeName?]
    | .bound index => by simp [encodeTemplate, decodeTemplate?]
    | .application constructor arguments => by
        simp [encodeTemplate, decodeTemplate?, encodeName, decodeName?,
          decodeTemplates?_encodeTemplates arguments]

  theorem decodeTemplates?_encodeTemplates : ∀ templates : List PatternPlan,
      decodeTemplates? (encodeTemplates templates) = some templates
    | [] => rfl
    | template :: templates => by
        simp [encodeTemplates, decodeTemplates?, decodeTemplate?_encodeTemplate template,
          decodeTemplates?_encodeTemplates templates]
end

attribute [simp] decodeTemplate?_encodeTemplate decodeTemplates?_encodeTemplates

def encodeNames : List String → Pattern
  | [] => .apply "mm-nnil" []
  | name :: names => .apply "mm-ncons" [encodeName name, encodeNames names]

def decodeNames? : Pattern → Option (List String)
  | .apply "mm-nnil" [] => some []
  | .apply "mm-ncons" [name, names] => do
      let head ← decodeName? name
      let tail ← decodeNames? names
      some (head :: tail)
  | _ => none

@[simp] theorem decodeNames?_encodeNames : ∀ names : List String,
    decodeNames? (encodeNames names) = some names
  | [] => rfl
  | name :: names => by
      simp [encodeNames, decodeNames?, encodeName, decodeName?, decodeNames?_encodeNames names]

def encodeQuery (query : PremisePlan) : Pattern :=
  .apply "mm-query" [encodeName query.relation, encodeNames query.arguments]

def decodeQuery? : Pattern → Option PremisePlan
  | .apply "mm-query" [relation, arguments] => do
      let decodedRelation ← decodeName? relation
      let decodedArguments ← decodeNames? arguments
      some ⟨decodedRelation, decodedArguments⟩
  | _ => none

@[simp] theorem decodeQuery?_encodeQuery (query : PremisePlan) :
    decodeQuery? (encodeQuery query) = some query := by
  simp [encodeQuery, decodeQuery?, encodeName, decodeName?]

def encodeQueries : List PremisePlan → Pattern
  | [] => .apply "mm-qnil" []
  | query :: queries => .apply "mm-qcons" [encodeQuery query, encodeQueries queries]

def decodeQueries? : Pattern → Option (List PremisePlan)
  | .apply "mm-qnil" [] => some []
  | .apply "mm-qcons" [query, queries] => do
      let head ← decodeQuery? query
      let tail ← decodeQueries? queries
      some (head :: tail)
  | _ => none

@[simp] theorem decodeQueries?_encodeQueries : ∀ queries : List PremisePlan,
    decodeQueries? (encodeQueries queries) = some queries
  | [] => rfl
  | query :: queries => by simp [encodeQueries, decodeQueries?, decodeQueries?_encodeQueries queries]

def encodeLeaf (leaf : Leaf) : Pattern :=
  .apply "mm-plan"
    [encodeNat leaf.occurrence, encodeDecision leaf.plan.decision,
      encodeQueries leaf.plan.premises, encodeTemplate leaf.plan.template]

mutual
  def encodeProgram : Program → Pattern
    | .failure => .apply "mm-failure" []
    | .drop next => .apply "mm-drop" [encodeProgram next]
    | .tryRule leaf patterns onFailure =>
        .apply "mm-try" [encodeLeaf leaf, encodePatterns patterns, encodeProgram onFailure]
    | .switch branches default => .apply "mm-switch" [encodeBranches branches, encodeProgram default]

  def encodeBranches : Branches → Pattern
    | .nil => .apply "mm-bnil" []
    | .cons key program rest =>
        .apply "mm-bcons" [encodeKey key, encodeProgram program, encodeBranches rest]
end

/-- Continuation frames of the matching phase: the two binding-decision
frames, and the frame that hands the matched bindings to premise evaluation. -/
inductive Frame where
  | joinRight (tail : Decision)
  | joinMerge (bindings : Bindings)
  | afterMatch (premises : List PremisePlan) (template : PatternPlan)

def encodeFrame : Frame → Pattern
  | .joinRight tail => .apply "bd-join-right" [encodeDecision tail]
  | .joinMerge bindings => .apply "bd-join-merge" [encodeBindings bindings]
  | .afterMatch premises template =>
      .apply "mm-after" [encodeQueries premises, encodeTemplate template]

def encodeKont : List Frame → Pattern
  | [] => .apply "bd-knil" []
  | frame :: rest => .apply "bd-kcons" [encodeFrame frame, encodeKont rest]

/-- Frames of the instantiation phase: an application under construction. -/
inductive InstantiateFrame where
  | argument (constructor : String) (accumulated : List Pattern) (remaining : List PatternPlan)

def encodeInstantiateFrame : InstantiateFrame → Pattern
  | .argument constructor accumulated remaining =>
      .apply "mm-arg" [encodeName constructor, encodeCursor accumulated, encodeTemplates remaining]

def encodeInstantiateKont : List InstantiateFrame → Pattern
  | [] => .apply "mm-inil" []
  | frame :: rest => .apply "mm-icons" [encodeInstantiateFrame frame, encodeInstantiateKont rest]

/-- States of the typed reference machine. -/
inductive MachineState where
  | run (program : Program) (subject : Pattern) (cursor : List Pattern)
  | dispatch (branches : Branches) (subject focused : Pattern) (cursor : List Pattern)
  | prefilter (patterns : List MatrixPattern) (cursor : List Pattern) (leaf : Leaf)
      (subject : Pattern)
  | bdRun (decision : Decision) (subject : Pattern) (kont : List Frame)
  | bdRet (bindings : Bindings) (subject : Pattern) (kont : List Frame)
  | bdDone (bindings : Bindings)
  | premises (queries : List PremisePlan) (template : PatternPlan) (bindings : Bindings)
  | instantiate (template : PatternPlan) (bindings : Bindings) (kont : List InstantiateFrame)
  | instantiateArguments (constructor : String) (accumulated : List Pattern)
      (remaining : List PatternPlan) (bindings : Bindings) (kont : List InstantiateFrame)
  | instantiated (value : Pattern) (bindings : Bindings) (kont : List InstantiateFrame)
  | done (result : Pattern)

def encodeState : MachineState → Pattern
  | .run program subject cursor =>
      .apply "mm-run" [encodeProgram program, subject, encodeCursor cursor]
  | .dispatch branches subject focused cursor =>
      .apply "mm-dispatch" [encodeBranches branches, subject, focused, encodeCursor cursor]
  | .prefilter patterns cursor leaf subject =>
      .apply "mm-prefilter" [encodePatterns patterns, encodeCursor cursor, encodeLeaf leaf, subject]
  | .bdRun decision subject kont =>
      .apply "bd-run" [encodeDecision decision, subject, encodeKont kont]
  | .bdRet bindings subject kont =>
      .apply "bd-ret" [encodeBindings bindings, subject, encodeKont kont]
  | .bdDone bindings => .apply "bd-done" [encodeBindings bindings]
  | .premises queries template bindings =>
      .apply "mm-premises" [encodeQueries queries, encodeTemplate template, encodeBindings bindings]
  | .instantiate template bindings kont =>
      .apply "mm-inst" [encodeTemplate template, encodeBindings bindings, encodeInstantiateKont kont]
  | .instantiateArguments constructor accumulated remaining bindings kont =>
      .apply "mm-instargs"
        [encodeName constructor, encodeCursor accumulated, encodeTemplates remaining,
          encodeBindings bindings, encodeInstantiateKont kont]
  | .instantiated value bindings kont =>
      .apply "mm-iret" [value, encodeBindings bindings, encodeInstantiateKont kont]
  | .done result => .apply "mm-done" [result]

/-! ## The typed reference machine -/

/-- The successors of a state, in the order the authored rules list them.  A
stuck state has none. -/
def machineStep (relations : RelationEnv) (source : LanguageDef) :
    MachineState → List MachineState
  | .run .failure _ _ => []
  | .run (.drop _) _ [] => []
  | .run (.drop next) subject (_ :: cursor) => [.run next subject cursor]
  | .run (.tryRule leaf patterns onFailure) subject cursor =>
      [.prefilter patterns cursor leaf subject, .run onFailure subject cursor]
  | .run (.switch _ default) subject [] => [.run default subject []]
  | .run (.switch branches default) subject (focused :: cursor) =>
      [.run default subject (focused :: cursor), .dispatch branches subject focused cursor]
  | .dispatch .nil _ _ _ => []
  | .dispatch (.cons key program rest) subject focused cursor =>
      if subjectKey focused = key then
        [.run program subject (subjectChildren focused ++ cursor)]
      else
        [.dispatch rest subject focused cursor]
  | .prefilter [] [] leaf subject =>
      [.bdRun leaf.plan.decision subject [.afterMatch leaf.plan.premises leaf.plan.template]]
  | .prefilter [] (_ :: _) _ _ => []
  | .prefilter (_ :: _) [] _ _ => []
  | .prefilter (.wildcard :: patterns) (_ :: cursor) leaf subject =>
      [.prefilter patterns cursor leaf subject]
  | .prefilter (.node head children :: patterns) (focused :: cursor) leaf subject =>
      if subjectKey focused = ⟨head, children.length⟩ then
        [.prefilter (children ++ patterns) (subjectChildren focused ++ cursor) leaf subject]
      else
        []
  | .bdRun .succeed subject kont => [.bdRet [] subject kont]
  | .bdRun (.capture path name) subject kont =>
      match path.project? subject with
      | some focused => [.bdRet [(name, focused)] subject kont]
      | none => []
  | .bdRun (.checkBound path expected) subject kont =>
      match path.project? subject with
      | some focused => if isBoundAt focused expected then [.bdRet [] subject kont] else []
      | none => []
  | .bdRun (.checkConstructor path expected arity children) subject kont =>
      match path.project? subject with
      | some focused =>
          if isConstructorOf focused expected arity then [.bdRun children subject kont] else []
      | none => []
  | .bdRun (.join head tail) subject kont => [.bdRun head subject (.joinRight tail :: kont)]
  | .bdRet bindings subject (.joinRight tail :: kont) =>
      [.bdRun tail subject (.joinMerge bindings :: kont)]
  | .bdRet tailBindings subject (.joinMerge headBindings :: kont) =>
      match mergeBindings headBindings tailBindings with
      | some merged => [.bdRet merged subject kont]
      | none => []
  | .bdRet bindings _ (.afterMatch premises template :: _) => [.premises premises template bindings]
  | .bdRet bindings _ [] => [.bdDone bindings]
  | .bdDone _ => []
  | .premises [] template bindings => [.instantiate template bindings []]
  | .premises (query :: queries) template bindings =>
      (query.run relations source bindings).map fun next => .premises queries template next
  | .instantiate (.metavariable name) bindings kont =>
      [.instantiated (lookupOrVariable bindings name) bindings kont]
  | .instantiate (.bound index) bindings kont => [.instantiated (.bvar index) bindings kont]
  | .instantiate (.application constructor arguments) bindings kont =>
      [.instantiateArguments constructor [] arguments bindings kont]
  | .instantiateArguments constructor accumulated [] bindings kont =>
      [.instantiated (.apply constructor accumulated.reverse) bindings kont]
  | .instantiateArguments constructor accumulated (template :: templates) bindings kont =>
      [.instantiate template bindings (.argument constructor accumulated templates :: kont)]
  | .instantiated value bindings (.argument constructor accumulated templates :: kont) =>
      [.instantiateArguments constructor (value :: accumulated) templates bindings kont]
  | .instantiated value _ [] => [.done value]
  | .done _ => []

/-! ## Authored syntax -/

private def constructor (label category : String)
    (parameters : List (String × TypeExpr)) : GrammarRule :=
  { label
    category
    params := parameters.map fun parameter => .simple parameter.1 parameter.2
    syntaxPattern := [] }

def rootConstructor : GrammarRule := constructor "bd-root" "Path" []
def childConstructor : GrammarRule :=
  constructor "bd-child" "Path" [("parent", .base "Path"), ("index", .base "Index")]
def zeroConstructor : GrammarRule := constructor "zero" "Index" []
def succConstructor : GrammarRule := constructor "succ" "Index" [("pred", .base "Index")]
def succeedConstructor : GrammarRule := constructor "bd-succeed" "Decision" []
def captureConstructor : GrammarRule :=
  constructor "bd-capture" "Decision" [("path", .base "Path"), ("name", .base "Name")]
def checkBoundConstructor : GrammarRule :=
  constructor "bd-check-bound" "Decision" [("path", .base "Path"), ("index", .base "Index")]
def checkConstructorConstructor : GrammarRule :=
  constructor "bd-check-constructor" "Decision"
    [("path", .base "Path"), ("head", .base "Name"), ("arity", .base "Index"),
      ("child", .base "Decision")]
def joinConstructor : GrammarRule :=
  constructor "bd-join" "Decision" [("head", .base "Decision"), ("tail", .base "Decision")]
def nilBindingsConstructor : GrammarRule := constructor "bd-nil" "Bindings" []
def bindConstructor : GrammarRule :=
  constructor "bd-bind" "Bindings"
    [("name", .base "Name"), ("value", .base "Subject"), ("rest", .base "Bindings")]
def joinRightConstructor : GrammarRule :=
  constructor "bd-join-right" "Frame" [("tail", .base "Decision")]
def joinMergeConstructor : GrammarRule :=
  constructor "bd-join-merge" "Frame" [("bindings", .base "Bindings")]
def knilConstructor : GrammarRule := constructor "bd-knil" "Kont" []
def kconsConstructor : GrammarRule :=
  constructor "bd-kcons" "Kont" [("frame", .base "Frame"), ("rest", .base "Kont")]
def runConstructor : GrammarRule :=
  constructor "bd-run" "State"
    [("decision", .base "Decision"), ("subject", .base "Subject"), ("kont", .base "Kont")]
def retConstructor : GrammarRule :=
  constructor "bd-ret" "State"
    [("bindings", .base "Bindings"), ("subject", .base "Subject"), ("kont", .base "Kont")]
def doneConstructor : GrammarRule :=
  constructor "bd-done" "State" [("bindings", .base "Bindings")]

def headType : TypeDecl := TypeDecl.plain "Head"
def kindType : TypeDecl := TypeDecl.plain "Kind"
def keyType : TypeDecl := TypeDecl.plain "Key"
def matrixPatternType : TypeDecl := TypeDecl.plain "MatrixPattern"
def patternsType : TypeDecl := TypeDecl.plain "Patterns"
def cursorType : TypeDecl := TypeDecl.plain "Cursor"
def templateType : TypeDecl := TypeDecl.plain "Template"
def templatesType : TypeDecl := TypeDecl.plain "Templates"
def namesType : TypeDecl := TypeDecl.plain "Names"
def queryType : TypeDecl := TypeDecl.plain "Query"
def queriesType : TypeDecl := TypeDecl.plain "Queries"
def planType : TypeDecl := TypeDecl.plain "Plan"
def programType : TypeDecl := TypeDecl.plain "Program"
def branchesType : TypeDecl := TypeDecl.plain "Branches"
def instantiateFrameType : TypeDecl := TypeDecl.plain "InstantiateFrame"
def instantiateKontType : TypeDecl := TypeDecl.plain "InstantiateKont"

def vecConstructor : GrammarRule := constructor "mm-vec" "Kind" []
def bagConstructor : GrammarRule := constructor "mm-bag" "Kind" []
def setConstructor : GrammarRule := constructor "mm-set" "Kind" []
def headFvarConstructor : GrammarRule := constructor "mm-head-fvar" "Head" [("name", .base "Name")]
def headBvarConstructor : GrammarRule :=
  constructor "mm-head-bvar" "Head" [("index", .base "Index")]
def headAppConstructor : GrammarRule :=
  constructor "mm-head-app" "Head" [("name", .base "Name"), ("arity", .base "Index")]
def headLambdaConstructor : GrammarRule := constructor "mm-head-lambda" "Head" []
def headMultiConstructor : GrammarRule :=
  constructor "mm-head-multi" "Head" [("arity", .base "Index")]
def headSubstConstructor : GrammarRule := constructor "mm-head-subst" "Head" []
def headCollConstructor : GrammarRule := constructor "mm-head-coll" "Head" [("kind", .base "Kind")]
def keyConstructor : GrammarRule :=
  constructor "mm-key" "Key" [("head", .base "Head"), ("arity", .base "Index")]
def wildConstructor : GrammarRule := constructor "mm-wild" "MatrixPattern" []
def nodeConstructor : GrammarRule :=
  constructor "mm-node" "MatrixPattern" [("key", .base "Key"), ("children", .base "Patterns")]
def pnilConstructor : GrammarRule := constructor "mm-pnil" "Patterns" []
def pconsConstructor : GrammarRule :=
  constructor "mm-pcons" "Patterns"
    [("pattern", .base "MatrixPattern"), ("patterns", .base "Patterns")]
def cnilConstructor : GrammarRule := constructor "mm-cnil" "Cursor" []
def cconsConstructor : GrammarRule :=
  constructor "mm-ccons" "Cursor" [("subject", .base "Subject"), ("cursor", .base "Cursor")]
def tvarConstructor : GrammarRule := constructor "mm-tvar" "Template" [("name", .base "Name")]
def tbvarConstructor : GrammarRule := constructor "mm-tbvar" "Template" [("index", .base "Index")]
def tappConstructor : GrammarRule :=
  constructor "mm-tapp" "Template" [("name", .base "Name"), ("arguments", .base "Templates")]
def tnilConstructor : GrammarRule := constructor "mm-tnil" "Templates" []
def tconsConstructor : GrammarRule :=
  constructor "mm-tcons" "Templates"
    [("template", .base "Template"), ("templates", .base "Templates")]
def nnilConstructor : GrammarRule := constructor "mm-nnil" "Names" []
def nconsConstructor : GrammarRule :=
  constructor "mm-ncons" "Names" [("name", .base "Name"), ("names", .base "Names")]
def queryConstructor : GrammarRule :=
  constructor "mm-query" "Query" [("relation", .base "Name"), ("arguments", .base "Names")]
def qnilConstructor : GrammarRule := constructor "mm-qnil" "Queries" []
def qconsConstructor : GrammarRule :=
  constructor "mm-qcons" "Queries" [("query", .base "Query"), ("queries", .base "Queries")]
def planConstructor : GrammarRule :=
  constructor "mm-plan" "Plan"
    [("occurrence", .base "Index"), ("decision", .base "Decision"),
      ("premises", .base "Queries"), ("template", .base "Template")]
def failureConstructor : GrammarRule := constructor "mm-failure" "Program" []
def dropConstructor : GrammarRule := constructor "mm-drop" "Program" [("next", .base "Program")]
def tryConstructor : GrammarRule :=
  constructor "mm-try" "Program"
    [("leaf", .base "Plan"), ("patterns", .base "Patterns"), ("next", .base "Program")]
def switchConstructor : GrammarRule :=
  constructor "mm-switch" "Program" [("branches", .base "Branches"), ("default", .base "Program")]
def bnilConstructor : GrammarRule := constructor "mm-bnil" "Branches" []
def bconsConstructor : GrammarRule :=
  constructor "mm-bcons" "Branches"
    [("key", .base "Key"), ("program", .base "Program"), ("rest", .base "Branches")]
def afterConstructor : GrammarRule :=
  constructor "mm-after" "Frame" [("premises", .base "Queries"), ("template", .base "Template")]
def argConstructor : GrammarRule :=
  constructor "mm-arg" "InstantiateFrame"
    [("name", .base "Name"), ("accumulated", .base "Cursor"), ("remaining", .base "Templates")]
def inilConstructor : GrammarRule := constructor "mm-inil" "InstantiateKont" []
def iconsConstructor : GrammarRule :=
  constructor "mm-icons" "InstantiateKont"
    [("frame", .base "InstantiateFrame"), ("rest", .base "InstantiateKont")]
def mmRunConstructor : GrammarRule :=
  constructor "mm-run" "State"
    [("program", .base "Program"), ("subject", .base "Subject"), ("cursor", .base "Cursor")]
def dispatchConstructor : GrammarRule :=
  constructor "mm-dispatch" "State"
    [("branches", .base "Branches"), ("subject", .base "Subject"), ("focused", .base "Subject"),
      ("cursor", .base "Cursor")]
def prefilterConstructor : GrammarRule :=
  constructor "mm-prefilter" "State"
    [("patterns", .base "Patterns"), ("cursor", .base "Cursor"), ("leaf", .base "Plan"),
      ("subject", .base "Subject")]
def premisesConstructor : GrammarRule :=
  constructor "mm-premises" "State"
    [("queries", .base "Queries"), ("template", .base "Template"), ("bindings", .base "Bindings")]
def instConstructor : GrammarRule :=
  constructor "mm-inst" "State"
    [("template", .base "Template"), ("bindings", .base "Bindings"),
      ("kont", .base "InstantiateKont")]
def instargsConstructor : GrammarRule :=
  constructor "mm-instargs" "State"
    [("name", .base "Name"), ("accumulated", .base "Cursor"), ("remaining", .base "Templates"),
      ("bindings", .base "Bindings"), ("kont", .base "InstantiateKont")]
def iretConstructor : GrammarRule :=
  constructor "mm-iret" "State"
    [("value", .base "Subject"), ("bindings", .base "Bindings"), ("kont", .base "InstantiateKont")]
def mmDoneConstructor : GrammarRule := constructor "mm-done" "State" [("result", .base "Subject")]

/-! ## Pattern helpers for the rules -/

def mmRunPattern (program subject cursor : Pattern) : Pattern :=
  .apply "mm-run" [program, subject, cursor]
def dispatchPattern (branches subject focused cursor : Pattern) : Pattern :=
  .apply "mm-dispatch" [branches, subject, focused, cursor]
def prefilterPattern (patterns cursor leaf subject : Pattern) : Pattern :=
  .apply "mm-prefilter" [patterns, cursor, leaf, subject]
def premisesPattern (queries template bindings : Pattern) : Pattern :=
  .apply "mm-premises" [queries, template, bindings]
def instPattern (template bindings kont : Pattern) : Pattern :=
  .apply "mm-inst" [template, bindings, kont]
def instargsPattern (name accumulated remaining bindings kont : Pattern) : Pattern :=
  .apply "mm-instargs" [name, accumulated, remaining, bindings, kont]
def iretPattern (value bindings kont : Pattern) : Pattern := .apply "mm-iret" [value, bindings, kont]
def mmDonePattern (result : Pattern) : Pattern := .apply "mm-done" [result]
def dropPattern (next : Pattern) : Pattern := .apply "mm-drop" [next]
def tryPattern (leaf patterns next : Pattern) : Pattern := .apply "mm-try" [leaf, patterns, next]
def switchPattern (branches default : Pattern) : Pattern := .apply "mm-switch" [branches, default]
def bconsPattern (key program rest : Pattern) : Pattern := .apply "mm-bcons" [key, program, rest]
def cconsPattern (subject cursor : Pattern) : Pattern := .apply "mm-ccons" [subject, cursor]
def cnilPattern : Pattern := .apply "mm-cnil" []
def pnilPattern : Pattern := .apply "mm-pnil" []
def pconsPattern (pattern patterns : Pattern) : Pattern := .apply "mm-pcons" [pattern, patterns]
def wildPattern : Pattern := .apply "mm-wild" []
def nodePattern (key children : Pattern) : Pattern := .apply "mm-node" [key, children]
def planPattern (occurrence decision premises template : Pattern) : Pattern :=
  .apply "mm-plan" [occurrence, decision, premises, template]
def afterPattern (premises template : Pattern) : Pattern := .apply "mm-after" [premises, template]
def qnilPattern : Pattern := .apply "mm-qnil" []
def qconsPattern (query queries : Pattern) : Pattern := .apply "mm-qcons" [query, queries]
def queryPattern (relation arguments : Pattern) : Pattern := .apply "mm-query" [relation, arguments]
def tvarPattern (name : Pattern) : Pattern := .apply "mm-tvar" [name]
def tbvarPattern (index : Pattern) : Pattern := .apply "mm-tbvar" [index]
def tappPattern (name arguments : Pattern) : Pattern := .apply "mm-tapp" [name, arguments]
def tnilPattern : Pattern := .apply "mm-tnil" []
def tconsPattern (template templates : Pattern) : Pattern := .apply "mm-tcons" [template, templates]
def inilPattern : Pattern := .apply "mm-inil" []
def iconsPattern (frame rest : Pattern) : Pattern := .apply "mm-icons" [frame, rest]
def argPattern (name accumulated remaining : Pattern) : Pattern :=
  .apply "mm-arg" [name, accumulated, remaining]

def keyIsRelation : String := "mm-key-is"
def keyNotRelation : String := "mm-key-not"
def unfoldRelation : String := "mm-unfold"
def appendRelation : String := "mm-pappend"
def sourceQueryRelation : String := "mm-source-query"
def lookupRelation : String := "mm-lookup"
def bvarRelation : String := "mm-bvar"
def buildRelation : String := "mm-build"

/-! ## The twenty machine rules -/

/-- A projection drop discards the focused subject. -/
def dropRewrite : RewriteRule :=
  { name := "mm-drop"
    typeContext :=
      [("next", .base "Program"), ("subject", .base "Subject"), ("focused", .base "Subject"),
        ("cursor", .base "Cursor")]
    premises := []
    left := mmRunPattern (dropPattern (metavariable "next")) (metavariable "subject")
      (cconsPattern (metavariable "focused") (metavariable "cursor"))
    right := mmRunPattern (metavariable "next") (metavariable "subject") (metavariable "cursor") }

/-- An attempt filters its leaf by the residual patterns. -/
def tryLeafRewrite : RewriteRule :=
  { name := "mm-try-leaf"
    typeContext :=
      [("leaf", .base "Plan"), ("patterns", .base "Patterns"), ("next", .base "Program"),
        ("subject", .base "Subject"), ("cursor", .base "Cursor")]
    premises := []
    left := mmRunPattern (tryPattern (metavariable "leaf") (metavariable "patterns") (metavariable "next"))
      (metavariable "subject") (metavariable "cursor")
    right := prefilterPattern (metavariable "patterns") (metavariable "cursor") (metavariable "leaf")
      (metavariable "subject") }

/-- An attempt also continues with the next row: fallback is a successor. -/
def tryNextRewrite : RewriteRule :=
  { name := "mm-try-next"
    typeContext :=
      [("leaf", .base "Plan"), ("patterns", .base "Patterns"), ("next", .base "Program"),
        ("subject", .base "Subject"), ("cursor", .base "Cursor")]
    premises := []
    left := mmRunPattern (tryPattern (metavariable "leaf") (metavariable "patterns") (metavariable "next"))
      (metavariable "subject") (metavariable "cursor")
    right := mmRunPattern (metavariable "next") (metavariable "subject") (metavariable "cursor") }

/-- A switch always runs its default. -/
def switchDefaultRewrite : RewriteRule :=
  { name := "mm-switch-default"
    typeContext :=
      [("branches", .base "Branches"), ("default", .base "Program"), ("subject", .base "Subject"),
        ("cursor", .base "Cursor")]
    premises := []
    left := mmRunPattern (switchPattern (metavariable "branches") (metavariable "default"))
      (metavariable "subject") (metavariable "cursor")
    right := mmRunPattern (metavariable "default") (metavariable "subject") (metavariable "cursor") }

/-- A switch with a focused subject dispatches on it. -/
def switchDispatchRewrite : RewriteRule :=
  { name := "mm-switch-dispatch"
    typeContext :=
      [("branches", .base "Branches"), ("default", .base "Program"), ("subject", .base "Subject"),
        ("focused", .base "Subject"), ("cursor", .base "Cursor")]
    premises := []
    left := mmRunPattern (switchPattern (metavariable "branches") (metavariable "default"))
      (metavariable "subject") (cconsPattern (metavariable "focused") (metavariable "cursor"))
    right := dispatchPattern (metavariable "branches") (metavariable "subject") (metavariable "focused")
      (metavariable "cursor") }

/-- The branch whose key is the focused subject's key runs on the children. -/
def dispatchHitRewrite : RewriteRule :=
  { name := "mm-dispatch-hit"
    typeContext :=
      [("key", .base "Key"), ("program", .base "Program"), ("rest", .base "Branches"),
        ("subject", .base "Subject"), ("focused", .base "Subject"), ("cursor", .base "Cursor"),
        ("unfolded", .base "Cursor")]
    premises :=
      [.relationQuery keyIsRelation [metavariable "focused", metavariable "key"],
       .relationQuery unfoldRelation
        [metavariable "focused", metavariable "cursor", metavariable "unfolded"]]
    left := dispatchPattern
      (bconsPattern (metavariable "key") (metavariable "program") (metavariable "rest"))
      (metavariable "subject") (metavariable "focused") (metavariable "cursor")
    right := mmRunPattern (metavariable "program") (metavariable "subject") (metavariable "unfolded") }

/-- A branch with another key is skipped. -/
def dispatchMissRewrite : RewriteRule :=
  { name := "mm-dispatch-miss"
    typeContext :=
      [("key", .base "Key"), ("program", .base "Program"), ("rest", .base "Branches"),
        ("subject", .base "Subject"), ("focused", .base "Subject"), ("cursor", .base "Cursor")]
    premises := [.relationQuery keyNotRelation [metavariable "focused", metavariable "key"]]
    left := dispatchPattern
      (bconsPattern (metavariable "key") (metavariable "program") (metavariable "rest"))
      (metavariable "subject") (metavariable "focused") (metavariable "cursor")
    right := dispatchPattern (metavariable "rest") (metavariable "subject") (metavariable "focused")
      (metavariable "cursor") }

/-- Residual patterns and cursor exhausted together: matching the leaf's
left-hand side against the original subject starts, with premise evaluation
pending.  A leftover cursor is a structural rejection. -/
def prefilterDoneRewrite : RewriteRule :=
  { name := "mm-prefilter-done"
    typeContext :=
      [("occurrence", .base "Index"), ("decision", .base "Decision"),
        ("premises", .base "Queries"), ("template", .base "Template"), ("subject", .base "Subject")]
    premises := []
    left := prefilterPattern pnilPattern cnilPattern
      (planPattern (metavariable "occurrence") (metavariable "decision") (metavariable "premises")
        (metavariable "template"))
      (metavariable "subject")
    right := runPattern (metavariable "decision") (metavariable "subject")
      (kconsPattern (afterPattern (metavariable "premises") (metavariable "template")) knilPattern) }

/-- A wildcard accepts any focused subject. -/
def prefilterWildRewrite : RewriteRule :=
  { name := "mm-prefilter-wild"
    typeContext :=
      [("patterns", .base "Patterns"), ("focused", .base "Subject"), ("cursor", .base "Cursor"),
        ("leaf", .base "Plan"), ("subject", .base "Subject")]
    premises := []
    left := prefilterPattern (pconsPattern wildPattern (metavariable "patterns"))
      (cconsPattern (metavariable "focused") (metavariable "cursor")) (metavariable "leaf")
      (metavariable "subject")
    right := prefilterPattern (metavariable "patterns") (metavariable "cursor") (metavariable "leaf")
      (metavariable "subject") }

/-- A node pattern requires the focused subject's key and continues on the
children of both. -/
def prefilterNodeRewrite : RewriteRule :=
  { name := "mm-prefilter-node"
    typeContext :=
      [("key", .base "Key"), ("children", .base "Patterns"), ("patterns", .base "Patterns"),
        ("focused", .base "Subject"), ("cursor", .base "Cursor"), ("leaf", .base "Plan"),
        ("subject", .base "Subject"), ("appended", .base "Patterns"), ("unfolded", .base "Cursor")]
    premises :=
      [.relationQuery keyIsRelation [metavariable "focused", metavariable "key"],
       .relationQuery appendRelation
        [metavariable "children", metavariable "patterns", metavariable "appended"],
       .relationQuery unfoldRelation
        [metavariable "focused", metavariable "cursor", metavariable "unfolded"]]
    left := prefilterPattern
      (pconsPattern (nodePattern (metavariable "key") (metavariable "children"))
        (metavariable "patterns"))
      (cconsPattern (metavariable "focused") (metavariable "cursor")) (metavariable "leaf")
      (metavariable "subject")
    right := prefilterPattern (metavariable "appended") (metavariable "unfolded") (metavariable "leaf")
      (metavariable "subject") }

/-- Matched bindings are handed to premise evaluation. -/
def afterMatchRewrite : RewriteRule :=
  { name := "mm-after-match"
    typeContext :=
      [("bindings", .base "Bindings"), ("subject", .base "Subject"), ("premises", .base "Queries"),
        ("template", .base "Template"), ("kont", .base "Kont")]
    premises := []
    left := retPattern (metavariable "bindings") (metavariable "subject")
      (kconsPattern (afterPattern (metavariable "premises") (metavariable "template"))
        (metavariable "kont"))
    right := premisesPattern (metavariable "premises") (metavariable "template")
      (metavariable "bindings") }

/-- One relation premise is evaluated through the source relation environment. -/
def premiseRewrite : RewriteRule :=
  { name := "mm-premise"
    typeContext :=
      [("relation", .base "Name"), ("arguments", .base "Names"), ("queries", .base "Queries"),
        ("template", .base "Template"), ("bindings", .base "Bindings"), ("extended", .base "Bindings")]
    premises :=
      [.relationQuery sourceQueryRelation
        [metavariable "relation", metavariable "arguments", metavariable "bindings",
          metavariable "extended"]]
    left := premisesPattern
      (qconsPattern (queryPattern (metavariable "relation") (metavariable "arguments"))
        (metavariable "queries"))
      (metavariable "template") (metavariable "bindings")
    right := premisesPattern (metavariable "queries") (metavariable "template")
      (metavariable "extended") }

/-- Exhausted premises start instantiating the template. -/
def premisesDoneRewrite : RewriteRule :=
  { name := "mm-premises-done"
    typeContext := [("template", .base "Template"), ("bindings", .base "Bindings")]
    premises := []
    left := premisesPattern qnilPattern (metavariable "template") (metavariable "bindings")
    right := instPattern (metavariable "template") (metavariable "bindings") inilPattern }

/-- A template variable is looked up. -/
def instVarRewrite : RewriteRule :=
  { name := "mm-inst-var"
    typeContext :=
      [("name", .base "Name"), ("bindings", .base "Bindings"), ("kont", .base "InstantiateKont"),
        ("value", .base "Subject")]
    premises :=
      [.relationQuery lookupRelation
        [metavariable "bindings", metavariable "name", metavariable "value"]]
    left := instPattern (tvarPattern (metavariable "name")) (metavariable "bindings")
      (metavariable "kont")
    right := iretPattern (metavariable "value") (metavariable "bindings") (metavariable "kont") }

/-- A bound-variable template constructs the bound occurrence. -/
def instBvarRewrite : RewriteRule :=
  { name := "mm-inst-bvar"
    typeContext :=
      [("index", .base "Index"), ("bindings", .base "Bindings"), ("kont", .base "InstantiateKont"),
        ("value", .base "Subject")]
    premises := [.relationQuery bvarRelation [metavariable "index", metavariable "value"]]
    left := instPattern (tbvarPattern (metavariable "index")) (metavariable "bindings")
      (metavariable "kont")
    right := iretPattern (metavariable "value") (metavariable "bindings") (metavariable "kont") }

/-- An application template starts instantiating its arguments. -/
def instAppRewrite : RewriteRule :=
  { name := "mm-inst-app"
    typeContext :=
      [("name", .base "Name"), ("arguments", .base "Templates"), ("bindings", .base "Bindings"),
        ("kont", .base "InstantiateKont")]
    premises := []
    left := instPattern (tappPattern (metavariable "name") (metavariable "arguments"))
      (metavariable "bindings") (metavariable "kont")
    right := instargsPattern (metavariable "name") cnilPattern (metavariable "arguments")
      (metavariable "bindings") (metavariable "kont") }

/-- Exhausted arguments construct the application. -/
def instargsDoneRewrite : RewriteRule :=
  { name := "mm-instargs-done"
    typeContext :=
      [("name", .base "Name"), ("accumulated", .base "Cursor"), ("bindings", .base "Bindings"),
        ("kont", .base "InstantiateKont"), ("value", .base "Subject")]
    premises :=
      [.relationQuery buildRelation
        [metavariable "name", metavariable "accumulated", metavariable "value"]]
    left := instargsPattern (metavariable "name") (metavariable "accumulated") tnilPattern
      (metavariable "bindings") (metavariable "kont")
    right := iretPattern (metavariable "value") (metavariable "bindings") (metavariable "kont") }

/-- The next argument is instantiated under an application frame. -/
def instargsNextRewrite : RewriteRule :=
  { name := "mm-instargs-next"
    typeContext :=
      [("name", .base "Name"), ("accumulated", .base "Cursor"), ("template", .base "Template"),
        ("templates", .base "Templates"), ("bindings", .base "Bindings"),
        ("kont", .base "InstantiateKont")]
    premises := []
    left := instargsPattern (metavariable "name") (metavariable "accumulated")
      (tconsPattern (metavariable "template") (metavariable "templates")) (metavariable "bindings")
      (metavariable "kont")
    right := instPattern (metavariable "template") (metavariable "bindings")
      (iconsPattern
        (argPattern (metavariable "name") (metavariable "accumulated") (metavariable "templates"))
        (metavariable "kont")) }

/-- An instantiated argument is accumulated. -/
def iretArgRewrite : RewriteRule :=
  { name := "mm-iret-arg"
    typeContext :=
      [("value", .base "Subject"), ("bindings", .base "Bindings"), ("name", .base "Name"),
        ("accumulated", .base "Cursor"), ("templates", .base "Templates"),
        ("kont", .base "InstantiateKont")]
    premises := []
    left := iretPattern (metavariable "value") (metavariable "bindings")
      (iconsPattern
        (argPattern (metavariable "name") (metavariable "accumulated") (metavariable "templates"))
        (metavariable "kont"))
    right := instargsPattern (metavariable "name")
      (cconsPattern (metavariable "value") (metavariable "accumulated")) (metavariable "templates")
      (metavariable "bindings") (metavariable "kont") }

/-- A fully instantiated template is the result. -/
def iretDoneRewrite : RewriteRule :=
  { name := "mm-iret-done"
    typeContext := [("value", .base "Subject"), ("bindings", .base "Bindings")]
    premises := []
    left := iretPattern (metavariable "value") (metavariable "bindings") inilPattern
    right := mmDonePattern (metavariable "value") }

/-- The ordered-match machine language definition.  The binding-decision
rules come first, unchanged. -/
def language : LanguageDef :=
  { name := "ordered-match-machine"
    types :=
      [pathType, indexType, nameType, subjectType, decisionType, bindingsType, frameType,
        kontType, stateType, headType, kindType, keyType, matrixPatternType, patternsType,
        cursorType, templateType, templatesType, namesType, queryType, queriesType, planType,
        programType, branchesType, instantiateFrameType, instantiateKontType]
    terms :=
      [rootConstructor, childConstructor, zeroConstructor, succConstructor, succeedConstructor,
        captureConstructor, checkBoundConstructor, checkConstructorConstructor, joinConstructor,
        nilBindingsConstructor, bindConstructor, joinRightConstructor, joinMergeConstructor,
        knilConstructor, kconsConstructor, runConstructor, retConstructor, doneConstructor,
        vecConstructor, bagConstructor, setConstructor, headFvarConstructor, headBvarConstructor,
        headAppConstructor, headLambdaConstructor, headMultiConstructor, headSubstConstructor,
        headCollConstructor, keyConstructor, wildConstructor, nodeConstructor, pnilConstructor,
        pconsConstructor, cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor,
        tappConstructor, tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor,
        queryConstructor, qnilConstructor, qconsConstructor, planConstructor, failureConstructor,
        dropConstructor, tryConstructor, switchConstructor, bnilConstructor, bconsConstructor,
        afterConstructor, argConstructor, inilConstructor, iconsConstructor, mmRunConstructor,
        dispatchConstructor, prefilterConstructor, premisesConstructor, instConstructor,
        instargsConstructor, iretConstructor, mmDoneConstructor]
    equations := []
    rewrites :=
      [succeedRewrite, captureRewrite, checkBoundRewrite, checkConstructorRewrite, joinRewrite,
        joinRightRewrite, joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite,
        tryNextRewrite, switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite,
        dispatchMissRewrite, prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite,
        afterMatchRewrite, premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite,
        instAppRewrite, instargsDoneRewrite, instargsNextRewrite, iretArgRewrite,
        iretDoneRewrite] }

/-! ## The relation catalog -/

/-- The catalog: the binding-decision relations unchanged, the reflective
source query, and the primitive observations and constructions. -/
def relationEnv (relations : RelationEnv) (source : LanguageDef) : RelationEnv where
  tuples relation arguments :=
    if relation = keyIsRelation then
      match arguments with
      | [focused, key] => rowWhen (encodeKey (subjectKey focused) = key) arguments
      | _ => []
    else if relation = keyNotRelation then
      match arguments with
      | [focused, key] => rowWhen (encodeKey (subjectKey focused) ≠ key) arguments
      | _ => []
    else if relation = unfoldRelation then
      match arguments with
      | [focused, cursor, .fvar _] =>
          match decodeCursor? cursor with
          | some rest => [[focused, cursor, encodeCursor (subjectChildren focused ++ rest)]]
          | none => []
      | _ => []
    else if relation = appendRelation then
      match arguments with
      | [children, patterns, .fvar _] =>
          match decodePatterns? children, decodePatterns? patterns with
          | some first, some second => [[children, patterns, encodePatterns (first ++ second)]]
          | _, _ => []
      | _ => []
    else if relation = sourceQueryRelation then
      match arguments with
      | [relationName, argumentNames, bindings, .fvar _] =>
          match decodeName? relationName, decodeNames? argumentNames, decodeBindings? bindings with
          | some name, some names, some current =>
              (relationQueryStep relations source current name (names.map Pattern.fvar)).map
                fun extended => [relationName, argumentNames, bindings, encodeBindings extended]
          | _, _, _ => []
      | _ => []
    else if relation = lookupRelation then
      match arguments with
      | [bindings, name, .fvar _] =>
          match decodeBindings? bindings, decodeName? name with
          | some current, some variableName =>
              [[bindings, name, lookupOrVariable current variableName]]
          | _, _ => []
      | _ => []
    else if relation = bvarRelation then
      match arguments with
      | [index, .fvar _] =>
          match decodeNat? index with
          | some bound => [[index, .bvar bound]]
          | none => []
      | _ => []
    else if relation = buildRelation then
      match arguments with
      | [name, accumulated, .fvar _] =>
          match decodeName? name, decodeCursor? accumulated with
          | some head, some reversed => [[name, accumulated, .apply head reversed.reverse]]
          | _, _ => []
      | _ => []
    else
      BindingDecisionLanguage.relationEnv.tuples relation arguments


/-! ## Validation, one certificate per rule -/

private theorem labels_nodup : (language.terms.map (·.label)).Nodup := by
  decide

private theorem succeed_validate : LanguageDef.validateRewrite language succeedRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem capture_validate : LanguageDef.validateRewrite language captureRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem checkBound_validate : LanguageDef.validateRewrite language checkBoundRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem checkConstructor_validate : LanguageDef.validateRewrite language checkConstructorRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem join_validate : LanguageDef.validateRewrite language joinRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem joinRight_validate : LanguageDef.validateRewrite language joinRightRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem joinMerge_validate : LanguageDef.validateRewrite language joinMergeRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem finish_validate : LanguageDef.validateRewrite language finishRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem drop_validate : LanguageDef.validateRewrite language dropRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem tryLeaf_validate : LanguageDef.validateRewrite language tryLeafRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem tryNext_validate : LanguageDef.validateRewrite language tryNextRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem switchDefault_validate : LanguageDef.validateRewrite language switchDefaultRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem switchDispatch_validate : LanguageDef.validateRewrite language switchDispatchRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem dispatchHit_validate : LanguageDef.validateRewrite language dispatchHitRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem dispatchMiss_validate : LanguageDef.validateRewrite language dispatchMissRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem prefilterDone_validate : LanguageDef.validateRewrite language prefilterDoneRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem prefilterWild_validate : LanguageDef.validateRewrite language prefilterWildRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem prefilterNode_validate : LanguageDef.validateRewrite language prefilterNodeRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem afterMatch_validate : LanguageDef.validateRewrite language afterMatchRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem premise_validate : LanguageDef.validateRewrite language premiseRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem premisesDone_validate : LanguageDef.validateRewrite language premisesDoneRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem instVar_validate : LanguageDef.validateRewrite language instVarRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem instBvar_validate : LanguageDef.validateRewrite language instBvarRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem instApp_validate : LanguageDef.validateRewrite language instAppRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem instargsDone_validate : LanguageDef.validateRewrite language instargsDoneRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.freeFvarNames,
      TypeExpr.baseNames, TypeDecl.plain])

private theorem instargsNext_validate : LanguageDef.validateRewrite language instargsNextRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem iretArg_validate : LanguageDef.validateRewrite language iretArgRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem iretDone_validate : LanguageDef.validateRewrite language iretDoneRewrite = [] :=
  RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup (by
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, succeedRewrite, captureRewrite,
      checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite,
      joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite,
      switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite,
      prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite,
      premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite,
      instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite, runPattern,
      retPattern, donePattern, succeedPattern, capturePattern, checkBoundPattern,
      checkConstructorPattern, joinPattern, nilBindingsPattern, bindPattern, joinRightPattern,
      joinMergePattern, knilPattern, kconsPattern, metavariable, mmRunPattern, dispatchPattern,
      prefilterPattern, premisesPattern, instPattern, instargsPattern, iretPattern,
      mmDonePattern, dropPattern, tryPattern, switchPattern, bconsPattern, cconsPattern,
      cnilPattern, pnilPattern, pconsPattern, wildPattern, nodePattern, planPattern,
      afterPattern, qnilPattern, qconsPattern, queryPattern, tvarPattern, tbvarPattern,
      tappPattern, tnilPattern, tconsPattern, inilPattern, iconsPattern, argPattern,
      projectRelation, boundRelation, constructorRelation, mergeRelation, keyIsRelation,
      keyNotRelation, unfoldRelation, appendRelation, sourceQueryRelation, lookupRelation,
      bvarRelation, buildRelation, pathType, indexType, nameType, subjectType, decisionType,
      bindingsType, frameType, kontType, stateType, headType, kindType, keyType,
      matrixPatternType, patternsType, cursorType, templateType, templatesType, namesType,
      queryType, queriesType, planType, programType, branchesType, instantiateFrameType,
      instantiateKontType, rootConstructor, childConstructor, zeroConstructor, succConstructor,
      succeedConstructor, captureConstructor, checkBoundConstructor,
      checkConstructorConstructor, joinConstructor, nilBindingsConstructor, bindConstructor,
      joinRightConstructor, joinMergeConstructor, knilConstructor, kconsConstructor,
      runConstructor, retConstructor, doneConstructor, vecConstructor, bagConstructor,
      setConstructor, headFvarConstructor, headBvarConstructor, headAppConstructor,
      headLambdaConstructor, headMultiConstructor, headSubstConstructor, headCollConstructor,
      keyConstructor, wildConstructor, nodeConstructor, pnilConstructor, pconsConstructor,
      cnilConstructor, cconsConstructor, tvarConstructor, tbvarConstructor, tappConstructor,
      tnilConstructor, tconsConstructor, nnilConstructor, nconsConstructor, queryConstructor,
      qnilConstructor, qconsConstructor, planConstructor, failureConstructor, dropConstructor,
      tryConstructor, switchConstructor, bnilConstructor, bconsConstructor, afterConstructor,
      argConstructor, inilConstructor, iconsConstructor, mmRunConstructor, dispatchConstructor,
      prefilterConstructor, premisesConstructor, instConstructor, instargsConstructor,
      iretConstructor, mmDoneConstructor, constructor, LanguageDef.typeNames,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain])

private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites, LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite rewriteMember
  change rewrite ∈
    [succeedRewrite, captureRewrite, checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite, joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite, switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite, prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite, premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite, instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite] at rewriteMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at rewriteMember
  rcases rewriteMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact succeed_validate
  · exact capture_validate
  · exact checkBound_validate
  · exact checkConstructor_validate
  · exact join_validate
  · exact joinRight_validate
  · exact joinMerge_validate
  · exact finish_validate
  · exact drop_validate
  · exact tryLeaf_validate
  · exact tryNext_validate
  · exact switchDefault_validate
  · exact switchDispatch_validate
  · exact dispatchHit_validate
  · exact dispatchMiss_validate
  · exact prefilterDone_validate
  · exact prefilterWild_validate
  · exact prefilterNode_validate
  · exact afterMatch_validate
  · exact premise_validate
  · exact premisesDone_validate
  · exact instVar_validate
  · exact instBvar_validate
  · exact instApp_validate
  · exact instargsDone_validate
  · exact instargsNext_validate
  · exact iretArg_validate
  · exact iretDone_validate

/-- The authored definition passes the ordinary structural validator. -/
theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  exact rewrites_validate

def validatedLanguage : ValidatedLanguageDef := ⟨language, language_validate⟩

/-- The ordered-match machine representation over a source relation
environment and source language: the rules are fixed, the catalog consults
the source. -/
def ir (relations : RelationEnv) (source : LanguageDef) : IRLanguage :=
  ⟨validatedLanguage, relationEnv relations source⟩

private theorem rules_noncontextual :
    ∀ rule, rule ∈ language.rewrites → NoncontextualPremises rule.premises := by
  intro rule ruleMember
  change rule ∈
    [succeedRewrite, captureRewrite, checkBoundRewrite, checkConstructorRewrite, joinRewrite, joinRightRewrite, joinMergeRewrite, finishRewrite, dropRewrite, tryLeafRewrite, tryNextRewrite, switchDefaultRewrite, switchDispatchRewrite, dispatchHitRewrite, dispatchMissRewrite, prefilterDoneRewrite, prefilterWildRewrite, prefilterNodeRewrite, afterMatchRewrite, premiseRewrite, premisesDoneRewrite, instVarRewrite, instBvarRewrite, instAppRewrite, instargsDoneRewrite, instargsNextRewrite, iretArgRewrite, iretDoneRewrite] at ruleMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ruleMember
  rcases ruleMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact .nil
    | exact .relationQuery .nil
    | exact .relationQuery (.relationQuery .nil)
    | exact .relationQuery (.relationQuery (.relationQuery .nil))

theorem language_isEquationFree : language.isEquationFree = true := by decide

/-- The representation's step is membership in the generic root executor. -/
theorem step_iff_mem_executor (relations : RelationEnv) (source : LanguageDef)
    (state target : Pattern) :
    (ir relations source).semantics.Step state target ↔
      target ∈ rewriteStepWithPremisesUsing (relationEnv relations source) language state := by
  change StepModuloEquations (engineBasePremises (relationEnv relations source)) language
    state target ↔ _
  rw [stepModuloEquations_iff_step_of_no_generators language_isEquationFree]
  rw [step_iff_rootStep_of_noncontextualRules rules_noncontextual]
  simp [RootStep, rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing]

end Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage
