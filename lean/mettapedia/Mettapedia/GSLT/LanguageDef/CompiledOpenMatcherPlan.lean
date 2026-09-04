import Mettapedia.GSLT.LanguageDef.CompiledPlanConstructorGuidedCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Basic

/-!
# Source-derived plans for open matching

An authored rule pattern is immutable within a revision-pinned program.  Its
constructor and variable classification can therefore be performed once when
the program is built, rather than rediscovered for every activation.  This
module gives that plan an independent tree carrier and connects every admitted
rigid step to the existing Martelli--Montanari unifier.

The cost result is intentionally narrow.  It counts source-tree
classification, not total matching work: dereferencing, occurs checking,
binding writes, rollback, and dynamic-query inspection remain present.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledOpenMatcherPlan

open CompiledPlanAdmission
open CompiledPlanConstructorGuidedCompilation
open Mettapedia.Logic.LP

/-! ## Independent plan carrier -/

/-- A rule-pattern plan records one classification per authored occurrence.
Children use an ordinary ordered list, rather than the source carrier's mutual
`Terms` representation. -/
inductive PatternPlan where
  | symbol (name : List UInt8)
  | variable (slot : UInt32)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (children : List PatternPlan)
  deriving Repr

mutual

/-- Compile one immutable source pattern exactly once. -/
def compile : Term -> PatternPlan
  | .symbol name => .symbol name
  | .variable slot => .variable slot
  | .string value => .string value
  | .integer value => .integer value
  | .application head arguments =>
      .application head (compileTerms arguments)

def compileTerms : Terms -> List PatternPlan
  | .nil => []
  | .cons head tail => compile head :: compileTerms tail

end

mutual

/-- Erase generated plan metadata back to the authored term carrier. -/
def erase : PatternPlan -> Term
  | .symbol name => .symbol name
  | .variable slot => .variable slot
  | .string value => .string value
  | .integer value => .integer value
  | .application head children =>
      .application head (eraseTerms children)

def eraseTerms : List PatternPlan -> Terms
  | [] => .nil
  | head :: tail => .cons (erase head) (eraseTerms tail)

end


mutual

/-- Compilation preserves the complete authored tree, including order and
repeated variable occurrences. -/
theorem erase_compile (source : Term) : erase (compile source) = source := by
  cases source with
  | symbol name => rfl
  | «variable» slot => rfl
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      simp only [compile, erase]
      rw [eraseTerms_compileTerms arguments]

theorem eraseTerms_compileTerms (sources : Terms) :
    eraseTerms (compileTerms sources) = sources := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp only [compileTerms, eraseTerms]
      rw [erase_compile head, eraseTerms_compileTerms tail]

end

theorem compile_injective : Function.Injective compile := by
  intro left right equal
  have erased := congrArg erase equal
  simpa [erase_compile] using erased

/-! ## Exact source-occurrence accounting -/

mutual

def sourceNodes : Term -> Nat
  | .symbol _ | .variable _ | .string _ | .integer _ => 1
  | .application _ arguments => 1 + sourceNodesTerms arguments

def sourceNodesTerms : Terms -> Nat
  | .nil => 0
  | .cons head tail => sourceNodes head + sourceNodesTerms tail

end


mutual

def planNodes : PatternPlan -> Nat
  | .symbol _ | .variable _ | .string _ | .integer _ => 1
  | .application _ children => 1 + planNodesList children

def planNodesList : List PatternPlan -> Nat
  | [] => 0
  | head :: tail => planNodes head + planNodesList tail

end

/-! ## Linear physical realization -/

/-- One preorder instruction retains the exact source-plan occurrence and the
size of its complete subtree.  The source plan remains semantic authority;
`subtreeSpan` is only proof-erased cursor metadata. -/
structure LinearNode where
  plan : PatternPlan
  subtreeSpan : Nat
  deriving Repr

/-! A linear node is a convenient proof presentation, but retaining the whole
plan in every physical instruction would merely move the interpreter's tree
behind another pointer.  The executable lowering below keeps only metadata
derived from that presentation plus the exact authored occurrence. -/

/-- Proof-erased operation class for one authored pattern occurrence. -/
inductive PatternOpcode where
  | symbol
  | variable
  | string
  | integer
  | application (arity : Nat)
  deriving DecidableEq, Repr

/-- Operation class derived from the semantic plan presentation. -/
def opcode : PatternPlan -> PatternOpcode
  | .symbol _ => .symbol
  | .variable _ => .variable
  | .string _ => .string
  | .integer _ => .integer
  | .application _ children => .application children.length

mutual

/-- Variable-slot occurrences in exact authored preorder. -/
def variableSlotOccurrences : PatternPlan -> List UInt32
  | .symbol _ | .string _ | .integer _ => []
  | .variable slot => [slot]
  | .application _ children => variableSlotOccurrencesList children

def variableSlotOccurrencesList : List PatternPlan -> List UInt32
  | [] => []
  | head :: tail =>
      variableSlotOccurrences head ++ variableSlotOccurrencesList tail

end

/-- Exact finite support of one source subtree. -/
def variableSupport (plan : PatternPlan) : List UInt32 :=
  (variableSlotOccurrences plan).dedup

/-- Direct executable metadata.  It deliberately contains no `PatternPlan`:
the source occurrence and derived fields are sufficient for execution, while
the independently retained plan remains the proof/semantic authority. -/
structure ExecutableNode where
  source : Term
  opcode : PatternOpcode
  variableSupport : List UInt32
  subtreeSpan : Nat
  deriving Repr

/-- Lower one proof-oriented linear node to direct executable metadata. -/
def lowerLinearNode (node : LinearNode) : ExecutableNode :=
  { source := erase node.plan
    opcode := opcode node.plan
    variableSupport := variableSupport node.plan
    subtreeSpan := node.subtreeSpan }

mutual

/-- Compile a plan tree to a contiguous preorder instruction program. -/
def linearize : PatternPlan -> List LinearNode
  | plan@(.symbol _) | plan@(.variable _) | plan@(.string _) |
      plan@(.integer _) =>
      [{ plan, subtreeSpan := 1 }]
  | plan@(.application _ children) =>
      { plan, subtreeSpan := planNodes plan } :: linearizeList children

/-- Concatenate the preorder programs of an ordered source forest. -/
def linearizeList : List PatternPlan -> List LinearNode
  | [] => []
  | head :: tail => linearize head ++ linearizeList tail

end

/-- Direct contiguous program generated from one semantic pattern plan. -/
def executableProgram (plan : PatternPlan) : List ExecutableNode :=
  (linearize plan).map lowerLinearNode

/-- Number of authored children in the source term carrier. -/
def termsLength : Terms -> Nat
  | .nil => 0
  | .cons _ tail => 1 + termsLength tail

/-- Independently classify a source occurrence, without consulting its plan. -/
def sourceOpcode : Term -> PatternOpcode
  | .symbol _ => .symbol
  | .variable _ => .variable
  | .string _ => .string
  | .integer _ => .integer
  | .application _ children => .application (termsLength children)

/-- Erasing a plan forest preserves its exact child count. -/
theorem termsLength_eraseTerms (plans : List PatternPlan) :
    termsLength (eraseTerms plans) = plans.length := by
  induction plans with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [eraseTerms, termsLength, List.length_cons]
      rw [inductionHypothesis]
      omega

/-- Plan-side classification agrees with independent source classification. -/
theorem opcode_erase (plan : PatternPlan) :
    opcode plan = sourceOpcode (erase plan) := by
  cases plan with
  | symbol name => rfl
  | «variable» slot => rfl
  | string value => rfl
  | integer value => rfl
  | application head children =>
      simp only [opcode, erase, sourceOpcode]
      rw [termsLength_eraseTerms]

/-- Every lowered instruction's operation class is independently recoverable
from its exact source occurrence. -/
theorem lowerLinearNode_opcode_exact (node : LinearNode) :
    (lowerLinearNode node).opcode =
      sourceOpcode (lowerLinearNode node).source := by
  exact opcode_erase node.plan

/-- Direct lowering retains precisely the source subtree's finite support. -/
theorem lowerLinearNode_support_exact (node : LinearNode) :
    (lowerLinearNode node).variableSupport =
      variableSupport node.plan := by
  rfl

mutual

/-- Linearization stores exactly one instruction per authored plan
occurrence. -/
theorem linearize_length (plan : PatternPlan) :
    (linearize plan).length = planNodes plan := by
  cases plan with
  | symbol name => rfl
  | «variable» slot => rfl
  | string value => rfl
  | integer value => rfl
  | application head children =>
      simp only [linearize, List.length_cons, planNodes]
      rw [linearizeList_length]
      omega

theorem linearizeList_length (plans : List PatternPlan) :
    (linearizeList plans).length = planNodesList plans := by
  cases plans with
  | nil => rfl
  | cons head tail =>
      simp only [linearizeList, List.length_append, planNodesList]
      rw [linearize_length, linearizeList_length]

end


/-- The first instruction names the exact plan root and the exact extent of
its contiguous subtree program. -/
theorem linearize_head (plan : PatternPlan) :
    (linearize plan).head? =
      some { plan, subtreeSpan := planNodes plan } := by
  cases plan <;> rfl

/-- Advancing by the compiled root span skips exactly that subtree and lands
on the following program, independently of its contents. -/
theorem drop_linearize_span_append (plan : PatternPlan)
    (following : List LinearNode) :
    (linearize plan ++ following).drop (planNodes plan) = following := by
  rw [← linearize_length]
  simp

mutual

/-- Ordered source occurrences, including the root. -/
def sourcePreorder : Term -> List Term
  | source@(.symbol _) | source@(.variable _) | source@(.string _) |
      source@(.integer _) => [source]
  | source@(.application _ arguments) =>
      source :: sourcePreorderTerms arguments

def sourcePreorderTerms : Terms -> List Term
  | .nil => []
  | .cons head tail => sourcePreorder head ++ sourcePreorderTerms tail

end


mutual

/-- Linearization preserves the exact ordered authored occurrence stream,
not merely its cardinality. -/
theorem linearize_compile_preorder (source : Term) :
    (linearize (compile source)).map (fun node => erase node.plan) =
      sourcePreorder source := by
  cases source with
  | symbol name => rfl
  | «variable» slot => rfl
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      simp only [compile, linearize, sourcePreorder, List.map_cons]
      have rootExact :
          erase (.application head (compileTerms arguments)) =
            .application head arguments := by
        simpa only [compile] using
          erase_compile (.application head arguments)
      rw [rootExact]
      rw [linearizeList_compileTerms_preorder]

theorem linearizeList_compileTerms_preorder (sources : Terms) :
    (linearizeList (compileTerms sources)).map
        (fun node => erase node.plan) =
      sourcePreorderTerms sources := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp only [compileTerms, linearizeList, List.map_append,
        sourcePreorderTerms]
      rw [linearize_compile_preorder, linearizeList_compileTerms_preorder]

end

/-- Direct executable lowering preserves the exact ordered authored
occurrence stream without retaining plan nodes in the instruction carrier. -/
theorem executableProgram_compile_preorder (source : Term) :
    (executableProgram (compile source)).map ExecutableNode.source =
      sourcePreorder source := by
  simp only [executableProgram, List.map_map]
  exact linearize_compile_preorder source

mutual

/-- The generated plan neither duplicates nor drops source occurrences. -/
theorem planNodes_compile (source : Term) :
    planNodes (compile source) = sourceNodes source := by
  cases source with
  | symbol name => rfl
  | «variable» slot => rfl
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      simp only [compile, planNodes, sourceNodes]
      rw [planNodesList_compileTerms arguments]

theorem planNodesList_compileTerms (sources : Terms) :
    planNodesList (compileTerms sources) = sourceNodesTerms sources := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp only [compileTerms, planNodesList, sourceNodesTerms]
      rw [planNodes_compile head, planNodesList_compileTerms tail]

end

/-- The physical instruction vector has exactly the source occurrence
cardinality. -/
theorem linearize_compile_length (source : Term) :
    (linearize (compile source)).length = sourceNodes source := by
  rw [linearize_length, planNodes_compile]

/-- Direct lowering also has exactly one executable instruction per authored
occurrence. -/
theorem executableProgram_compile_length (source : Term) :
    (executableProgram (compile source)).length = sourceNodes source := by
  simp only [executableProgram, List.length_map]
  exact linearize_compile_length source

/-- The root cursor span is the exact source-subtree occurrence count. -/
theorem linearize_compile_root_span (source : Term) :
    ((linearize (compile source)).head?).map LinearNode.subtreeSpan =
      some (sourceNodes source) := by
  rw [linearize_head]
  simp [planNodes_compile]

/-- Source classification repeats once per activation in the uncompiled cost
model. -/
def repeatedSourceClassificationCost (activations : Nat)
    (source : Term) : Nat := activations * sourceNodes source

/-- Plan construction classifies each immutable source occurrence once. -/
def plannedSourceClassificationCost (source : Term) : Nat :=
  sourceNodes source

/-- After the first activation, compiling once removes exactly one complete
source-classification pass per additional activation.  This theorem does not
count dynamic query work or binding-store operations. -/
theorem sourceClassification_savings (additionalActivations : Nat)
    (source : Term) :
    repeatedSourceClassificationCost (additionalActivations + 1) source =
      plannedSourceClassificationCost source +
        additionalActivations * sourceNodes source := by
  simp [repeatedSourceClassificationCost,
    plannedSourceClassificationCost, Nat.add_mul, Nat.add_comm]

/-! ## Connection to scoped first-order unification -/

mutual

def encodePlan (origin : VariableOrigin) :
    PatternPlan -> Mettapedia.Logic.LP.Term signature
  | .symbol name => .const (.symbol name)
  | .variable slot => .var { origin, slot }
  | .string value => .const (.string value)
  | .integer value => .const (.integer value)
  | .application name children =>
      let encoded := encodePlanList origin children
      .app { name, arity := encoded.length } fun index => encoded.get index

def encodePlanList (origin : VariableOrigin) :
    List PatternPlan -> List (Mettapedia.Logic.LP.Term signature)
  | [] => []
  | head :: tail => encodePlan origin head :: encodePlanList origin tail

end


mutual

/-- The plan and source encodings denote the same scoped first-order term. -/
theorem encodePlan_compile (origin : VariableOrigin) (source : Term) :
    encodePlan origin (compile source) = encodeTerm origin source := by
  cases source with
  | symbol name => rfl
  | «variable» slot => rfl
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      simp only [compile, encodePlan, encodeTerm]
      rw [encodePlanList_compileTerms origin arguments]

theorem encodePlanList_compileTerms (origin : VariableOrigin)
    (sources : Terms) :
    encodePlanList origin (compileTerms sources) = encodeTerms origin sources := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp only [compileTerms, encodePlanList, encodeTerms]
      rw [encodePlan_compile origin head,
        encodePlanList_compileTerms origin tail]

end

/-- Constructor-guided matching reads its rigid rule side from the compiled
plan while the query remains dynamic. -/
def decompose?
    (plan : PatternPlan) (query : Term) (rest : List Equation) :
    Option (List Equation) :=
  ConstructorGuidedUnificationCompilation.decompose?
    (encodePlan .rule plan) (encodeTerm .query query) rest

/-- Compiling the source tree does not change which rigid-root decomposition
is admitted or which ordered child equations it emits. -/
theorem decompose?_compile (source query : Term) (rest : List Equation) :
    decompose? (compile source) query rest =
      CompiledPlanConstructorGuidedCompilation.decompose?
        source query rest := by
  simp [decompose?, CompiledPlanConstructorGuidedCompilation.decompose?,
    encodePlan_compile]

/-- Every successful rigid plan step is exactly one ordinary
Martelli--Montanari step, including its fuel decrement and complete returned
substitution. -/
theorem unifyFuel_decompose?
    (fuel : Nat) (plan : PatternPlan) (query : Term)
    (rest equations : List Equation)
    (accepted : decompose? plan query rest = some equations) :
    Mettapedia.Logic.LP.unifyFuel (fuel + 1)
        ((encodePlan .rule plan, encodeTerm .query query) :: rest) =
      Mettapedia.Logic.LP.unifyFuel fuel equations := by
  exact ConstructorGuidedUnificationCompilation.unifyFuel_decompose?
    fuel (encodePlan .rule plan) (encodeTerm .query query)
    rest equations accepted

/-! ## Composing exact rigid steps -/

abbrev ScopedEquation :=
  ConstructorGuidedUnificationCompilation.Equation signature

/-- A finite prefix of source-derived rigid decompositions.  The trace stops
wherever dynamic variables require the ordinary unifier; it does not claim
that an open match is wholly rigid. -/
inductive RigidPlanTrace :
    Nat -> List ScopedEquation -> List ScopedEquation -> Prop where
  | refl (equations : List ScopedEquation) :
      RigidPlanTrace 0 equations equations
  | step (plan : PatternPlan) (query : Term)
      (rest next finish : List ScopedEquation) (steps : Nat)
      (accepted : decompose? plan query rest = some next)
      (tail : RigidPlanTrace steps next finish) :
      RigidPlanTrace (Nat.succ steps)
        ((encodePlan .rule plan, encodeTerm .query query) :: rest) finish

/-- Any finite compiled prefix may be followed by the unchanged unifier.
Every direct rigid step consumes exactly the same one unit of unification fuel
and returns the same complete substitution as the source route. -/
theorem unifyFuel_rigidPlanTrace
    {steps : Nat} {start finish : List ScopedEquation}
    (trace : RigidPlanTrace steps start finish) (fuel : Nat) :
    Mettapedia.Logic.LP.unifyFuel (fuel + steps) start =
      Mettapedia.Logic.LP.unifyFuel fuel finish := by
  induction trace generalizing fuel with
  | refl equations => rfl
  | step plan query rest next finish steps accepted tail induction =>
      rw [Nat.add_succ]
      rw [unifyFuel_decompose? (fuel + steps) plan query rest next accepted]
      exact induction fuel

/-- A rigid trace selected from one immutable linear program.  Membership
keeps source provenance explicit; every step still carries the independent
unifier acceptance witness. -/
inductive LinearRigidTrace (program : List LinearNode) :
    Nat -> List ScopedEquation -> List ScopedEquation -> Prop where
  | refl (equations : List ScopedEquation) :
      LinearRigidTrace program 0 equations equations
  | step (node : LinearNode) (present : node ∈ program)
      (query : Term) (rest next finish : List ScopedEquation) (steps : Nat)
      (accepted : decompose? node.plan query rest = some next)
      (tail : LinearRigidTrace program steps next finish) :
      LinearRigidTrace program (Nat.succ steps)
        ((encodePlan .rule node.plan, encodeTerm .query query) :: rest) finish

/-- Forgetting the physical program membership yields the semantic rigid
trace already related to ordinary unification. -/
theorem LinearRigidTrace.toRigidPlanTrace
    {program : List LinearNode} {steps : Nat}
    {start finish : List ScopedEquation}
    (trace : LinearRigidTrace program steps start finish) :
    RigidPlanTrace steps start finish := by
  induction trace with
  | refl equations => exact .refl equations
  | step node present query rest next finish steps accepted tail induction =>
      exact .step node.plan query rest next finish steps accepted induction

/-- Linear physical traversal therefore preserves the complete substitution
and consumes the same unification fuel for every admitted rigid prefix. -/
theorem unifyFuel_linearRigidTrace
    {program : List LinearNode} {steps : Nat}
    {start finish : List ScopedEquation}
    (trace : LinearRigidTrace program steps start finish) (fuel : Nat) :
    Mettapedia.Logic.LP.unifyFuel (fuel + steps) start =
      Mettapedia.Logic.LP.unifyFuel fuel finish :=
  unifyFuel_rigidPlanTrace trace.toRigidPlanTrace fuel

/-- The source route reclassifies one immutable rule constructor per rigid
step; the compiled route reads the already classified plan node. -/
def repeatedRigidSourceClassifications (steps : Nat) : Nat := steps

def compiledRigidSourceClassifications (_steps : Nat) : Nat := 0

/-- Every nonempty compiled rigid prefix strictly reduces source-side
classification work.  Dynamic query-root observations are accounted for
separately below. -/
theorem compiledRigidSourceClassifications_lt
    {steps : Nat} (nonempty : 0 < steps) :
    compiledRigidSourceClassifications steps <
      repeatedRigidSourceClassifications steps := by
  simpa [compiledRigidSourceClassifications,
    repeatedRigidSourceClassifications] using nonempty

/-! ## The remaining dynamic observation is necessary -/

/-- The one dynamic fact needed before rigid decomposition: an exposed
application's function symbol, whose type already includes its arity. -/
def applicationRoot? (term : Mettapedia.Logic.LP.Term signature) :
    Option signature.functionSymbols :=
  match term with
  | .app head _ => some head
  | _ => none

def plannedApplicationRoot? (plan : PatternPlan) :
    Option signature.functionSymbols :=
  applicationRoot? (encodePlan .rule plan)

def queryApplicationRoot? (query : Term) :
    Option signature.functionSymbols :=
  applicationRoot? (encodeTerm .query query)

/-- Rigid-root compatibility factors through one observation of the dynamic
query root.  Descendant equations remain the ordinary unifier's work. -/
def rigidRootCompatible (plan : PatternPlan) (query : Term) : Bool :=
  (plannedApplicationRoot? plan).isSome &&
    decide (plannedApplicationRoot? plan = queryApplicationRoot? query)

private def rootObservationPlan : PatternPlan :=
  compile (.application [61] .nil)

private def sameRootQuery : Term := .application [61] .nil
private def differentRootQuery : Term := .application [62] .nil

private theorem sameRootQuery_compatible :
    rigidRootCompatible rootObservationPlan sameRootQuery = true := by
  decide

private theorem differentRootQuery_incompatible :
    rigidRootCompatible rootObservationPlan differentRootQuery = false := by
  decide

/-- No query-blind (zero-observation) answer can decide even this one fixed
rigid plan: two dynamic queries require different answers.  Thus plan-time
classification can remove every repeated source inspection, but it cannot
lawfully remove the dynamic root observation. -/
theorem rigidRootDecision_not_queryBlind :
    ¬ ∃ answer : Bool, ∀ query : Term,
      rigidRootCompatible rootObservationPlan query = answer := by
  intro claimed
  obtain ⟨answer, allQueries⟩ := claimed
  have same := allQueries sameRootQuery
  have different := allQueries differentRootQuery
  rw [sameRootQuery_compatible] at same
  rw [differentRootQuery_incompatible] at different
  have impossible : true = false := same.trans different.symm
  contradiction

/-! ## Direct binding keys -/

open CompiledPlanOpenActivationViewCompilation

/-- Physical matching may keep several rule generations live, so its direct
key map retains both coordinates. -/
abbrev ScopedOpenEnvironment := LogicVariable -> Option OpenTerm

/-- The logical binding map is keyed by the generation/slot coordinate.  A
temporary syntax node carrying that coordinate is not part of the map's
meaning. -/
def writeDirectKey (environment : ScopedOpenEnvironment)
    (key : LogicVariable) (value : OpenTerm) : ScopedOpenEnvironment :=
  fun candidate => if candidate = key then some value else environment candidate

/-- Reference boundary that first packages a key as open variable syntax. -/
def writeThroughVariableSyntax (environment : ScopedOpenEnvironment)
    (keySyntax value : OpenTerm) : Option ScopedOpenEnvironment :=
  match keySyntax with
  | .variable key => some (writeDirectKey environment key value)
  | _ => none

/-- Passing the generation-qualified key directly to the binding store is
exactly the variable-syntax route, without allocating the temporary syntax
node. -/
theorem writeThroughVariableSyntax_eq_direct
    (environment : ScopedOpenEnvironment) (key : LogicVariable)
    (value : OpenTerm) :
    writeThroughVariableSyntax environment (.variable key) value =
      some (writeDirectKey environment key value) := by
  rfl

/-- A constructor is not silently reinterpreted as a binding key. -/
example :
    writeThroughVariableSyntax (fun _ => none)
      (.symbol [1]) (.symbol [2]) = none := by
  rfl

/-! ## Derived dense views of one fresh rule generation -/

mutual

/-- Exact authored occurrence count for one dense rule slot. -/
def variableOccurrences (slot : UInt32) : PatternPlan -> Nat
  | .symbol _ | .string _ | .integer _ => 0
  | .variable candidate => if candidate = slot then 1 else 0
  | .application _ children => variableOccurrencesList slot children

def variableOccurrencesList (slot : UInt32) : List PatternPlan -> Nat
  | [] => 0
  | head :: tail =>
      variableOccurrences slot head + variableOccurrencesList slot tail

end

/-- The ordinary path consults the authoritative map once per occurrence. -/
def authoritativeSlotLookupCost (plan : PatternPlan) (slot : UInt32) : Nat :=
  variableOccurrences slot plan

/-- A positive match-local view still consults authority on the first
occurrence and can answer only subsequent occurrences. -/
def positiveSlotViewLookupCost (plan : PatternPlan) (slot : UInt32) : Nat :=
  min (variableOccurrences slot plan) 1

/-- A positive slot view reduces the number of authoritative map lookups
exactly for a repeated authored variable.  This is only a lookup-count law:
it does not yet account for probing and recording the derived view. -/
theorem positiveSlotView_reduces_authoritative_lookups_iff
    (plan : PatternPlan) (slot : UInt32) :
    positiveSlotViewLookupCost plan slot <
        authoritativeSlotLookupCost plan slot <->
      2 <= variableOccurrences slot plan := by
  simp only [positiveSlotViewLookupCost, authoritativeSlotLookupCost]
  omega

/-- A linear variable has no slot-view lookup saving. -/
example :
    positiveSlotViewLookupCost (.application [1] [.variable 3]) 3 =
      authoritativeSlotLookupCost (.application [1] [.variable 3]) 3 := by
  decide

/-- Abstract physical cost of consulting the authoritative store at every
authored occurrence. -/
def authoritativeSlotPhysicalCost (plan : PatternPlan) (slot : UInt32)
    (lookupCost : Nat) : Nat :=
  variableOccurrences slot plan * lookupCost

/-- Abstract physical cost of a positive derived view: one authoritative
lookup when the variable occurs, one view probe per occurrence, and one
record when the first lookup succeeds. -/
def positiveSlotViewPhysicalCost (plan : PatternPlan) (slot : UInt32)
    (lookupCost probeCost recordCost : Nat) : Nat :=
  min (variableOccurrences slot plan) 1 * lookupCost +
    variableOccurrences slot plan * probeCost +
    min (variableOccurrences slot plan) 1 * recordCost

/-- If the authoritative store already offers a lookup no more expensive
than probing the extra view, the view cannot improve physical cost.  Thus a
lookup-count reduction alone is insufficient admission evidence. -/
theorem positiveSlotView_not_profitable_when_probe_dominates_lookup
    (plan : PatternPlan) (slot : UInt32)
    (lookupCost probeCost recordCost : Nat)
    (dominated : lookupCost <= probeCost) :
    authoritativeSlotPhysicalCost plan slot lookupCost <=
      positiveSlotViewPhysicalCost plan slot
        lookupCost probeCost recordCost := by
  have scaled :
      variableOccurrences slot plan * lookupCost <=
        variableOccurrences slot plan * probeCost :=
    Nat.mul_le_mul_left _ dominated
  simp only [authoritativeSlotPhysicalCost, positiveSlotViewPhysicalCost]
  omega

/-- A nonlinear variable admits exactly one authoritative lookup followed by
one derived-view hit. -/
example :
    positiveSlotViewLookupCost
        (.application [1] [.variable 3, .variable 3]) 3 = 1 /\
      authoritativeSlotLookupCost
        (.application [1] [.variable 3, .variable 3]) 3 = 2 := by
  decide

/-- A match-local slot view is deliberately only a cache of positive
bindings.  Missing entries mean "consult the authoritative environment", not
"unbound".  This distinction makes a finite physical array a sound candidate
for repeated rule variables without making it a second substitution authority;
physical-cost admission remains a separate obligation. -/
abbrev RuleSlotView := UInt32 -> Option OpenTerm

/-- Every cached positive binding must be the binding denoted by the
generation-qualified authoritative environment. -/
def RuleSlotView.Sound (generation : UInt32) (view : RuleSlotView)
    (environment : ScopedOpenEnvironment) : Prop :=
  forall slot value, view slot = some value ->
    environment { generation, slot } = some value

/-- A hit in a sound slot view is exactly the authoritative lookup. -/
theorem RuleSlotView.lookup_exact
    {generation slot : UInt32} {view : RuleSlotView}
    {environment : ScopedOpenEnvironment} {value : OpenTerm}
    (sound : RuleSlotView.Sound generation view environment)
    (hit : view slot = some value) :
    environment { generation, slot } = some value :=
  sound slot value hit

/-- Record the same successful write in the derived slot view. -/
def RuleSlotView.write (view : RuleSlotView) (slot : UInt32)
    (value : OpenTerm) : RuleSlotView :=
  fun candidate => if candidate = slot then some value else view candidate

/-- Writing the authoritative generation-qualified key and its derived slot
view together preserves exactness.  The cache still authorizes no write: the
authoritative environment is updated independently and remains the denotation.
-/
theorem RuleSlotView.sound_write
    {generation slot : UInt32} {view : RuleSlotView}
    {environment : ScopedOpenEnvironment} {value : OpenTerm}
    (sound : RuleSlotView.Sound generation view environment) :
    RuleSlotView.Sound generation
      (RuleSlotView.write view slot value)
      (writeDirectKey environment { generation, slot } value) := by
  intro candidate cached cachedEq
  by_cases same : candidate = slot
  · subst candidate
    simpa [RuleSlotView.write, writeDirectKey] using cachedEq
  · have prior : view candidate = some cached := by
      simpa [RuleSlotView.write, same] using cachedEq
    have authoritative := sound candidate cached prior
    simpa [writeDirectKey, same] using authoritative

/-- Updating one generation cannot change the same dense slot in another
generation.  A slot number alone is therefore never sufficient identity. -/
theorem writeDirectKey_other_generation
    (environment : ScopedOpenEnvironment) (generation other slot : UInt32)
    (value : OpenTerm) (different : other ≠ generation) :
    writeDirectKey environment { generation, slot } value
        { generation := other, slot } =
      environment { generation := other, slot } := by
  simp [writeDirectKey, different]

/-- Positive nonlinear canary: a cached repeated occurrence reads the exact
binding written through the authoritative generation-qualified key. -/
example :
    let empty : ScopedOpenEnvironment := fun _ => none
    let emptyView : RuleSlotView := fun _ => none
    let value : OpenTerm := .symbol [42]
    let environment := writeDirectKey empty { generation := 7, slot := 3 } value
    let view := RuleSlotView.write emptyView 3 value
    view 3 = some value /\ environment { generation := 7, slot := 3 } = some value := by
  decide

/-- Negative alias canary: the same physical slot in a different generation
does not observe the cached generation's binding. -/
example :
    let empty : ScopedOpenEnvironment := fun _ => none
    let value : OpenTerm := .symbol [42]
    writeDirectKey empty { generation := 7, slot := 3 } value
        { generation := 8, slot := 3 } = none := by
  decide

/-! ## Shared query observation and occurrence-local projection -/

universe uPath uOccurrence uSlot uValue

section SharedQueryObservation

variable {Path : Type uPath} [DecidableEq Path]
  {Occurrence : Type uOccurrence} {Slot : Type uSlot}
  {Value : Type uValue}

/-- One authored binding demand reads a dynamic query path and writes the
result to an occurrence-local slot. -/
structure BindingDemand where
  path : Path
  slot : Slot

/-- One authored occurrence retains its identity and ordered binding
demands.  Equal source patterns at two positions remain two projections. -/
structure OccurrenceProjection where
  occurrence : Occurrence
  demands : List (BindingDemand (Path := Path) (Slot := Slot))

/-- Binding authority is generation/occurrence qualified.  A slot number
alone is never a logical key. -/
abbrev AuthoritativeKey := Occurrence × Slot

/-- The reference route observes the dynamic query separately at every
authored demand occurrence. -/
def referenceDemands (occurrence : Occurrence) (query : Path -> Value) :
    List (BindingDemand (Path := Path) (Slot := Slot)) ->
      List (AuthoritativeKey (Occurrence := Occurrence) (Slot := Slot) × Value)
  | [] => []
  | demand :: rest =>
      ((occurrence, demand.slot), query demand.path) ::
        referenceDemands occurrence query rest

/-- A compiled projection reads an independently supplied observation
table.  Missing observations are an honest decline, not a logical mismatch. -/
def compiledDemands (occurrence : Occurrence)
    (observation : Path -> Option Value) :
    List (BindingDemand (Path := Path) (Slot := Slot)) ->
      Option (List
        (AuthoritativeKey (Occurrence := Occurrence) (Slot := Slot) × Value))
  | [] => some []
  | demand :: rest =>
      match observation demand.path,
          compiledDemands occurrence observation rest with
      | some value, some tail =>
          some (((occurrence, demand.slot), value) :: tail)
      | _, _ => none

/-- Evaluate a finite support once.  The table has no authority outside that
support and never manufactures an unavailable value. -/
def sharedObservation (query : Path -> Value) (support : List Path) :
    Path -> Option Value :=
  fun path => if path ∈ support then some (query path) else none

/-- Every covered compiled projection is exactly the occurrence-by-occurrence
reference projection. -/
theorem compiledDemands_shared_exact
    (occurrence : Occurrence) (query : Path -> Value) (support : List Path)
    (demands : List (BindingDemand (Path := Path) (Slot := Slot)))
    (covered : ∀ demand ∈ demands, demand.path ∈ support) :
    compiledDemands occurrence (sharedObservation query support) demands =
      some (referenceDemands occurrence query demands) := by
  induction demands with
  | nil => simp [compiledDemands, referenceDemands]
  | cons demand rest inductionHypothesis =>
      have headCovered : demand.path ∈ support :=
        covered demand (by simp)
      have tailCovered : ∀ item ∈ rest, item.path ∈ support := by
        intro item member
        exact covered item (by simp [member])
      rw [compiledDemands, referenceDemands]
      simp only [sharedObservation, if_pos headCovered]
      rw [inductionHypothesis tailCovered]

/-- Ordered source occurrences evaluated by the reference route. -/
def referenceFamily (query : Path -> Value)
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))) :
    List (List
      (AuthoritativeKey (Occurrence := Occurrence) (Slot := Slot) × Value) ) :=
  match family with
  | [] => []
  | projection :: rest =>
      referenceDemands projection.occurrence query projection.demands ::
        referenceFamily query rest

/-- The same family evaluated from one shared observation table. -/
def compiledFamily (observation : Path -> Option Value)
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))) :
    Option (List (List
      (AuthoritativeKey (Occurrence := Occurrence) (Slot := Slot) × Value))) :=
  match family with
  | [] => some []
  | projection :: rest =>
      match compiledDemands projection.occurrence observation
              projection.demands,
          compiledFamily observation rest with
      | some bindings, some tail => some (bindings :: tail)
      | _, _ => none

/-- The ordered multiset of every demanded path before sharing. -/
def demandedPaths
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))) : List Path :=
  family.flatMap fun projection => projection.demands.map BindingDemand.path

omit [DecidableEq Path] in
theorem demand_mem_demandedPaths
    {family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))}
    {projection : OccurrenceProjection
      (Path := Path) (Occurrence := Occurrence) (Slot := Slot)}
    {demand : BindingDemand (Path := Path) (Slot := Slot)}
    (projectionMember : projection ∈ family)
    (demandMember : demand ∈ projection.demands) :
    demand.path ∈ demandedPaths family := by
  simp only [demandedPaths, List.mem_flatMap, List.mem_map]
  exact ⟨projection, projectionMember, demand, demandMember, rfl⟩

/-- Any shared table covering every demand in the ordered source family is
exact. -/
theorem compiledFamily_covered_exact
    (query : Path -> Value) (support : List Path)
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot)))
    (covered : ∀ projection ∈ family, ∀ demand ∈ projection.demands,
      demand.path ∈ support) :
    compiledFamily (sharedObservation query support) family =
      some (referenceFamily query family) := by
  induction family with
  | nil => simp [compiledFamily, referenceFamily]
  | cons projection rest inductionHypothesis =>
      have projectionCovered : ∀ demand ∈ projection.demands,
          demand.path ∈ support := by
        intro demand member
        exact covered projection (by simp) demand member
      have restCovered : ∀ item ∈ rest, ∀ demand ∈ item.demands,
          demand.path ∈ support := by
        intro item itemMember demand demandMember
        exact covered item (by simp [itemMember]) demand demandMember
      rw [compiledFamily, referenceFamily]
      rw [compiledDemands_shared_exact projection.occurrence query support
        projection.demands projectionCovered]
      rw [inductionHypothesis restCovered]

/-- Sharing query observations changes neither authored occurrence order nor
duplicate occurrences, and every resulting key retains its occurrence
coordinate. -/
theorem compiledFamily_shared_exact
    (query : Path -> Value)
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))) :
    compiledFamily (sharedObservation query (demandedPaths family)) family =
      some (referenceFamily query family) := by
  apply compiledFamily_covered_exact
  intro projection projectionMember demand demandMember
  exact demand_mem_demandedPaths projectionMember demandMember

/-- A different authored occurrence can never alias the same dense slot. -/
theorem authoritativeKey_ne_of_occurrence_ne
    {first second : Occurrence} {firstSlot secondSlot : Slot}
    (different : first ≠ second) :
    (first, firstSlot) ≠ (second, secondSlot) := by
  intro equal
  exact different (congrArg Prod.fst equal)

/-- Work in the reference route: one dynamic observation per authored demand
occurrence. -/
def separateObservationCost
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))) : Nat :=
  (demandedPaths family).length

/-- Work in the shared route: one dynamic observation per distinct demanded
path. -/
def sharedObservationCost
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))) : Nat :=
  (demandedPaths family).dedup.length

/-- Sharing never performs more dynamic path observations than the separate
reference traversals. -/
theorem sharedObservationCost_le_separateObservationCost
    (family : List
      (OccurrenceProjection (Path := Path) (Occurrence := Occurrence)
        (Slot := Slot))) :
    sharedObservationCost family ≤ separateObservationCost family := by
  exact (List.dedup_sublist (demandedPaths family)).length_le

/-- The exact binding projection over a demanded finite support. -/
def bindingProjection (demanded : Finset Path) (query : Path -> Bool) :
    Path -> Option Bool :=
  fun path => if path ∈ demanded then some (query path) else none

/-- An algorithm depends only on its declared sampled support when queries
that agree there always receive the same output. -/
def DependsOnlyOn (sampled : Finset Path)
    (algorithm : (Path -> Bool) -> Path -> Option Bool) : Prop :=
  ∀ left right,
    (∀ path ∈ sampled, left path = right path) ->
      algorithm left = algorithm right

/-- Black-box lower bound: if one demanded path is not observed, no algorithm
depending only on the remaining sample can reproduce the exact binding
projection for all dynamic queries.  Thus deduplicating equal paths is
lawful, while dropping a distinct demanded path is not. -/
theorem omitted_path_prevents_exact_projection
    (demanded sampled : Finset Path) {omitted : Path}
    (isDemanded : omitted ∈ demanded) (notSampled : omitted ∉ sampled) :
    ¬ ∃ algorithm : (Path -> Bool) -> Path -> Option Bool,
        DependsOnlyOn sampled algorithm ∧
          ∀ query, algorithm query = bindingProjection demanded query := by
  rintro ⟨algorithm, depends, exactProjection⟩
  let allFalse : Path -> Bool := fun _ => false
  let oneTrue : Path -> Bool := fun path => decide (path = omitted)
  have agree : ∀ path ∈ sampled, allFalse path = oneTrue path := by
    intro path member
    have different : path ≠ omitted := by
      intro equal
      exact notSampled (equal ▸ member)
    simp [allFalse, oneTrue, different]
  have same := congrFun (depends allFalse oneTrue agree) omitted
  rw [exactProjection allFalse, exactProjection oneTrue] at same
  simp [bindingProjection, isDemanded, allFalse, oneTrue] at same

end SharedQueryObservation

/-! ## Independent positive and negative canaries -/

private def parserPattern : Term :=
  .application [1]
    (.cons (.symbol [2])
      (.cons (.application [3] (.cons (.variable 0) .nil)) .nil))

private def proofPattern : Term :=
  .application [10]
    (.cons (.application [11] (.cons (.variable 0) .nil))
      (.cons (.symbol [12]) .nil))

private def graphPattern : Term :=
  .application [20]
    (.cons (.variable 0) (.cons (.variable 1) .nil))

private def evidencePattern : Term :=
  .application [30]
    (.cons (.application [31]
      (.cons (.integer 1) (.cons (.variable 2) .nil))) .nil)

private def arithmeticPattern : Term :=
  .application [40]
    (.cons (.integer 0) (.cons (.string [41]) .nil))

/-- Five independently shaped source families compile without occurrence
loss or duplication. -/
example :
    [parserPattern, proofPattern, graphPattern,
      evidencePattern, arithmeticPattern].all
        (fun source =>
          planNodes (compile source) == sourceNodes source) = true := by
  decide

/-- The same five families receive one flat instruction per occurrence. -/
example :
    [parserPattern, proofPattern, graphPattern,
      evidencePattern, arithmeticPattern].all
        (fun source =>
          (linearize (compile source)).length == sourceNodes source) = true := by
  decide

private def orderedPattern : Term :=
  .application [60] (.cons (.symbol [61]) (.cons (.symbol [62]) .nil))

/-- Preorder linearization keeps the two authored children in source order. -/
example :
    (linearize (compile orderedPattern)).map
        (fun node => erase node.plan) =
      [orderedPattern, .symbol [61], .symbol [62]] := by
  decide

/-- Reversing the child instruction occurrences is observably a different
source program, even though cardinality is unchanged. -/
example :
    (linearize (compile orderedPattern)).map
        (fun node => erase node.plan) !=
      [orderedPattern, .symbol [62], .symbol [61]] := by
  decide

/-- Repeated variables remain repeated authored occurrences in the plan. -/
example :
    compile (.application [50]
      (.cons (.variable 7) (.cons (.variable 7) .nil))) =
      .application [50] [.variable 7, .variable 7] := by
  rfl

/-- A variable query is not misclassified as an exposed constructor. -/
example : (decompose? (compile parserPattern) (.variable 9) []).isSome =
    false := by
  decide

/-- A constructor disagreement remains an exact decline. -/
example :
    (decompose? (compile graphPattern)
      (.application [99]
        (.cons (.variable 4) (.cons (.variable 5) .nil))) []).isSome =
      false := by
  decide

private def sharedProjectionFamily :
    List (OccurrenceProjection (Path := Nat) (Occurrence := Nat)
      (Slot := Nat)) :=
  [ { occurrence := 11, demands := [{ path := 3, slot := 0 }] },
    { occurrence := 12, demands := [{ path := 3, slot := 0 }] } ]

/-- Positive transfer: two authored occurrences share one dynamic path read
while retaining distinct occurrence-qualified binding keys. -/
example :
    compiledFamily
        (sharedObservation (fun path : Nat => path + 20)
          (demandedPaths sharedProjectionFamily))
        sharedProjectionFamily =
      some [[((11, 0), 23)], [((12, 0), 23)]] := by
  decide

/-- The shared observation graph performs one read where independent
occurrence traversals perform two. -/
example :
    sharedObservationCost sharedProjectionFamily = 1 /\
      separateObservationCost sharedProjectionFamily = 2 := by
  decide

/-- Negative identity control: equal physical slots in different authored
occurrences are not the same logical key. -/
example : ((11, 0) : Nat × Nat) ≠ (12, 0) := by
  decide

#print axioms erase_compile
#print axioms linearize_compile_preorder
#print axioms unifyFuel_linearRigidTrace
#print axioms RuleSlotView.lookup_exact
#print axioms RuleSlotView.sound_write
#print axioms compiledDemands_shared_exact
#print axioms compiledFamily_shared_exact
#print axioms sharedObservationCost_le_separateObservationCost
#print axioms omitted_path_prevents_exact_projection

end Mettapedia.GSLT.LanguageDef.CompiledOpenMatcherPlan
