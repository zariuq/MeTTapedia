import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.RigidHeadPrefilter

/-!
# Rigid-coordinate discrimination for first-order rule heads

After relation-and-arity bucketing, a rule machine may index one argument by
its visible rigid root.  Variables remain wildcard candidates.  Atomic names,
integers, and application constructor/arity pairs form the index keys.

The central theorem is independent of a guest language: two terms with a
common ground instance always select one another.  Consequently an indexed
candidate list preserves every possible rule application, source order, and
multiplicity.  A virtual scan still charges one unit of fuel per source rule,
while invoking the expensive rule step only for selected candidates.
-/

namespace Mettapedia.GSLT.LanguageDef.RigidCoordinateIndexCompilation

open Mettapedia.GSLT.Parsing.HornCertificate
open Mettapedia.GSLT.LanguageDef.RigidHeadPrefilter

/-- The finite rigid-root vocabulary available without unification. -/
inductive DispatchKey where
  | atom (name : String)
  | integer (value : Int)
  | application (constructor : String) (arity : Nat)
  deriving DecidableEq, Repr

/-- Number of immediate arguments in the first-order term-list encoding. -/
def termsLength : Terms → Nat
  | .nil => 0
  | .cons _ tail => termsLength tail + 1

/-- Extract a rigid root.  Variables deliberately have no key. -/
def rootKey? : Term → Option DispatchKey
  | .var _ => none
  | .atom name => some (.atom name)
  | .integer value => some (.integer value)
  | .app constructor arguments =>
      some (.application constructor (termsLength arguments))

/-- Two roots can share a bucket when either is a variable, or when both
expose the same rigid key. -/
def rootCompatible (left right : Term) : Bool :=
  match rootKey? left, rootKey? right with
  | some leftKey, some rightKey => leftKey == rightKey
  | _, _ => true

/-- Rigid compatibility of term lists entails equal immediate arity. -/
theorem termsLength_eq_of_compatible :
    ∀ (left right : Terms), compatibleTerms left right = true →
      termsLength left = termsLength right
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, compatible => by
      simp [compatibleTerms] at compatible
  | .cons _ _, .nil, compatible => by
      simp [compatibleTerms] at compatible
  | .cons _ leftTail, .cons _ rightTail, compatible => by
      simp only [compatibleTerms, Bool.and_eq_true] at compatible
      simp [termsLength,
        termsLength_eq_of_compatible leftTail rightTail compatible.2]

/-- A common ground instance must agree on every visible rigid root. -/
theorem rootCompatible_of_commonGroundInstance
    (left right : Term) (leftSubstitution rightSubstitution : Substitution)
    (target : GroundTerm)
    (leftInstantiated :
      instantiateTerm leftSubstitution left = some target)
    (rightInstantiated :
      instantiateTerm rightSubstitution right = some target) :
    rootCompatible left right = true := by
  have compatible := compatibleTerm_of_commonGroundInstance
    left right leftSubstitution rightSubstitution target
    leftInstantiated rightInstantiated
  cases left with
  | var identifier => simp [rootCompatible, rootKey?]
  | atom leftName =>
      cases right <;>
        simp_all [rootCompatible, rootKey?, compatibleTerm]
  | integer leftValue =>
      cases right <;>
        simp_all [rootCompatible, rootKey?, compatibleTerm]
  | app leftConstructor leftArguments =>
      cases right with
      | var identifier => simp [rootCompatible, rootKey?]
      | atom rightName => simp [compatibleTerm] at compatible
      | integer rightValue => simp [compatibleTerm] at compatible
      | app rightConstructor rightArguments =>
          simp only [compatibleTerm, Bool.and_eq_true] at compatible
          obtain ⟨sameConstructor, compatibleArguments⟩ := compatible
          have sameConstructorEq :
              leftConstructor = rightConstructor := by
            simpa using sameConstructor
          have sameArity := termsLength_eq_of_compatible
            leftArguments rightArguments compatibleArguments
          simp [rootCompatible, rootKey?, sameConstructorEq, sameArity]

/-- A rule projected to the argument coordinate selected by the generated
plan.  The surrounding relation-and-arity index is an earlier compilation
stage, so this stage operates only on the chosen terms. -/
structure CoordinateRule where
  name : String
  coordinate : Term
  deriving DecidableEq, Repr

/-- Exact ordered candidate selection for one query coordinate. -/
def candidates (query : Term) (rules : List CoordinateRule) :
    List CoordinateRule :=
  rules.filter fun rule => rootCompatible query rule.coordinate

/-- Every rule coordinate with a common ground instance remains in the
indexed candidate list. -/
theorem mem_candidates_of_commonGroundInstance
    (query : Term) (rules : List CoordinateRule) (rule : CoordinateRule)
    (member : rule ∈ rules)
    (querySubstitution ruleSubstitution : Substitution)
    (target : GroundTerm)
    (queryInstantiated :
      instantiateTerm querySubstitution query = some target)
    (ruleInstantiated :
      instantiateTerm ruleSubstitution rule.coordinate = some target) :
    rule ∈ candidates query rules := by
  apply List.mem_filter.mpr
  exact ⟨member,
    rootCompatible_of_commonGroundInstance
      query rule.coordinate querySubstitution ruleSubstitution target
      queryInstantiated ruleInstantiated⟩

/-- Rejecting a coordinate is a certificate that the two terms have no
common ground instance. -/
theorem no_commonGroundInstance_of_coordinate_rejection
    (query candidate : Term)
    (rejected : rootCompatible query candidate = false) :
    ¬∃ querySubstitution candidateSubstitution target,
      instantiateTerm querySubstitution query = some target ∧
      instantiateTerm candidateSubstitution candidate = some target := by
  rintro ⟨querySubstitution, candidateSubstitution, target,
    queryInstantiated, candidateInstantiated⟩
  have accepted := rootCompatible_of_commonGroundInstance
    query candidate querySubstitution candidateSubstitution target
    queryInstantiated candidateInstantiated
  simp [rejected] at accepted

/-- Observable result of a bounded source-order rule scan. -/
inductive ScanResult (Observation : Type) where
  | completed (observations : List Observation)
  | exhausted (observations : List Observation)
  deriving DecidableEq, Repr

/-- Scan in source order.  Fuel is charged for every source rule, including a
candidate rejected by the index; `inspect` controls only whether the expensive
rule step is invoked. -/
def scan (inspect : CoordinateRule → Bool)
    (step : CoordinateRule → Option Observation) :
    Nat → List CoordinateRule → ScanResult Observation
  | _, [] => .completed []
  | 0, _ :: _ => .exhausted []
  | fuel + 1, rule :: rules =>
      let observation := if inspect rule then (step rule).toList else []
      match scan inspect step fuel rules with
      | .completed observations =>
          .completed (observation ++ observations)
      | .exhausted observations =>
          .exhausted (observation ++ observations)

/-- Full source scan, used as the reference observation. -/
def fullScan (step : CoordinateRule → Option Observation) :
    Nat → List CoordinateRule → ScanResult Observation :=
  scan (fun _ => true) step

/-- A rigid-coordinate scan invokes the step only on selected candidates but
retains the full source scan's fuel boundary and observation order. -/
def indexedScan (query : Term)
    (step : CoordinateRule → Option Observation) :
    Nat → List CoordinateRule → ScanResult Observation :=
  scan (fun rule => rootCompatible query rule.coordinate) step

/-- Exact bounded refinement.  If rejected rules cannot produce an
observation, indexed scanning has the same result—including exhaustion and
output order—as scanning every source rule. -/
theorem indexedScan_eq_fullScan
    (query : Term) (step : CoordinateRule → Option Observation)
    (rules : List CoordinateRule) (fuel : Nat)
    (rejectedSilent : ∀ rule ∈ rules,
      rootCompatible query rule.coordinate = false → step rule = none) :
    indexedScan query step fuel rules = fullScan step fuel rules := by
  induction rules generalizing fuel with
  | nil => simp [indexedScan, fullScan, scan]
  | cons rule rules inductionHypothesis =>
      cases fuel with
      | zero => simp [indexedScan, fullScan, scan]
      | succ fuel =>
          have tailSilent : ∀ candidate ∈ rules,
              rootCompatible query candidate.coordinate = false →
                step candidate = none := by
            intro candidate member rejected
            exact rejectedSilent candidate (by simp [member]) rejected
          have tailEquality := inductionHypothesis fuel tailSilent
          unfold indexedScan fullScan at tailEquality ⊢
          cases compatibleEq : rootCompatible query rule.coordinate with
          | false =>
              have silent := rejectedSilent rule (by simp) compatibleEq
              simp [scan, compatibleEq, silent]
              rw [tailEquality]
          | true =>
              simp [scan, compatibleEq]
              rw [tailEquality]

/-- Concrete abstract artifact emitted by the coordinate-index stage.  Each
source occurrence is retained together with the generated decision of whether
the expensive step is needed. -/
structure IndexedScanArtifact (Observation : Type) where
  entries : List (CoordinateRule × Bool)
  step : CoordinateRule → Option Observation

/-- Generate the per-occurrence inspection plan from the local rigid shape. -/
def compileEntries (query : Term) (rules : List CoordinateRule) :
    List (CoordinateRule × Bool) :=
  rules.map fun rule =>
    (rule, rootCompatible query rule.coordinate)

/-- Execute a generated inspection plan with source-order virtual fuel. -/
def executeEntries (step : CoordinateRule → Option Observation) :
    Nat → List (CoordinateRule × Bool) → ScanResult Observation
  | _, [] => .completed []
  | 0, _ :: _ => .exhausted []
  | fuel + 1, (rule, inspect) :: entries =>
      let observation := if inspect then (step rule).toList else []
      match executeEntries step fuel entries with
      | .completed observations =>
          .completed (observation ++ observations)
      | .exhausted observations =>
          .exhausted (observation ++ observations)

/-- Generated inspection flags implement exactly the indexed source scan. -/
theorem executeEntries_compileEntries
    (query : Term) (step : CoordinateRule → Option Observation)
    (rules : List CoordinateRule) (fuel : Nat) :
    executeEntries step fuel (compileEntries query rules) =
      indexedScan query step fuel rules := by
  induction rules generalizing fuel with
  | nil => simp [compileEntries, executeEntries, indexedScan, scan]
  | cons rule rules inductionHypothesis =>
      cases fuel with
      | zero =>
          simp [compileEntries, executeEntries, indexedScan, scan]
      | succ fuel =>
          unfold compileEntries indexedScan at inductionHypothesis
          simp only [compileEntries, List.map_cons, executeEntries,
            indexedScan, scan]
          cases compiledTailEq :
              executeEntries step fuel
                (List.map
                  (fun candidate =>
                    (candidate,
                      rootCompatible query candidate.coordinate)) rules) <;>
            cases sourceTailEq :
              scan (fun candidate =>
                rootCompatible query candidate.coordinate) step fuel rules <;>
            simp_all

/-- Source package accepted by the optimization.  The silence obligation is
the semantic certificate produced from rigid incompatibility. -/
structure AdmittedScan (Observation : Type) where
  query : Term
  rules : List CoordinateRule
  step : CoordinateRule → Option Observation
  rejectedSilent : ∀ rule ∈ rules,
    rootCompatible query rule.coordinate = false → step rule = none

/-- Compile an admitted source scan to its explicit inspection artifact. -/
def compileScan (source : AdmittedScan Observation) :
    IndexedScanArtifact Observation :=
  { entries := compileEntries source.query source.rules
    step := source.step }

/-- Coordinate discrimination as a composable certified realization. -/
def indexedScanRealization :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedScan Observation)
      (IndexedScanArtifact Observation)
      (Nat → ScanResult Observation) where
  compile := fun _ source => compileScan source
  observeSource := fun _ source fuel =>
    fullScan source.step fuel source.rules
  observeArtifact := fun _ artifact fuel =>
    executeEntries artifact.step fuel artifact.entries
  adequate := by
    intro _ source
    funext fuel
    change executeEntries source.step fuel
        (compileEntries source.query source.rules) =
      fullScan source.step fuel source.rules
    rw [executeEntries_compileEntries]
    exact indexedScan_eq_fullScan
      source.query source.step source.rules fuel source.rejectedSilent

/-- The number of expensive rule inspections is never greater than a full
scan. -/
theorem candidates_length_le (query : Term) (rules : List CoordinateRule) :
    (candidates query rules).length ≤ rules.length := by
  exact List.length_filter_le _ _

/-- A coordinate is useful precisely when two authored rules expose distinct
rigid roots there.  This is a local, decidable profitability recognizer; it
does not inspect guest-language names. -/
def useful (rules : List CoordinateRule) : Bool :=
  rules.any fun left =>
    rules.any fun right =>
      match rootKey? left.coordinate, rootKey? right.coordinate with
      | some leftKey, some rightKey => leftKey != rightKey
      | _, _ => false

/-! ## Independent positive and negative canaries -/

private def evaluatorRules : List CoordinateRule :=
  [{ name := "evaluate", coordinate := .app "eval" (.ofList [.var 0]) },
   { name := "quote", coordinate := .app "quote" (.ofList [.var 1]) },
   { name := "fallback", coordinate := .var 2 }]

private def literalRules : List CoordinateRule :=
  [{ name := "positive", coordinate := .app "positive" (.ofList [.var 0]) },
   { name := "negative", coordinate := .app "negative" (.ofList [.var 0]) }]

/-- A reflective evaluator keeps its exact constructor branch plus the
wildcard fallback, in authored order. -/
example :
    candidates (.app "eval" (.ofList [.atom "x"])) evaluatorRules =
      [evaluatorRules[0], evaluatorRules[2]] := by
  decide

/-- A first-order literal dispatcher independently exercises the same
recognizer with no wildcard branch. -/
example :
    useful literalRules = true ∧
    candidates (.app "negative" (.ofList [.atom "p"])) literalRules =
      [literalRules[1]] := by
  decide

/-- An all-variable coordinate is correctly recognized as unprofitable. -/
example :
    useful [{ name := "left", coordinate := .var 0 },
      { name := "right", coordinate := .var 1 }] = false := by
  decide

/-- Bounded virtual scanning preserves both successful and exhausted
observations while avoiding the rejected step. -/
example :
    let query := Term.app "eval" (.ofList [.atom "x"])
    let step : CoordinateRule → Option String := fun rule =>
      if rule.name = "quote" then none else some rule.name
    indexedScan query step 3 evaluatorRules =
        fullScan step 3 evaluatorRules ∧
      indexedScan query step 2 evaluatorRules =
        fullScan step 2 evaluatorRules := by
  decide

end Mettapedia.GSLT.LanguageDef.RigidCoordinateIndexCompilation
