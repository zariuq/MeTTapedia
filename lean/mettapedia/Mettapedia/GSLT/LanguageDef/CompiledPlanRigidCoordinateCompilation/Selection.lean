import Mettapedia.GSLT.LanguageDef.CompiledPlanFixedHeadIndexCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics
import Mettapedia.Data.List.OrderedPrefilter

/-!
# Rigid-coordinate selection for the admitted plan carrier

This is one instance of ordered prefiltering. A chosen coordinate is
an input to the theorem; there is no scoring, tie policy, or scratch
allocation here. Missing rigid keys retain the candidate. For a closed
query with the chosen coordinate available, exact per-rule matching after
the filter preserves the whole ordered answer word.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanRigidCoordinateCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open CompiledPlanTermSemantics

/-- Closed vocabulary of immediate rigid roots available in the admitted
typed carrier. -/
inductive DispatchKey where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (arity : Nat)
  deriving DecidableEq, Repr

/-- Number of immediate arguments in a closed value. -/
def groundTermsLength : GroundTerms -> Nat
  | .nil => 0
  | .cons _ tail => groundTermsLength tail + 1

/-- A variable has no rigid key and is therefore compiled as a wildcard. -/
def rootKey? : Term -> Option DispatchKey
  | .symbol name => some (.symbol name)
  | .variable _ => none
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .application head arguments =>
      some (.application head
        (CompiledPlanFixedHeadIndexCompilation.termsLength arguments))

/-- Every closed value exposes exactly one rigid root. -/
def groundRootKey : GroundTerm -> DispatchKey
  | .symbol name => .symbol name
  | .string value => .string value
  | .integer value => .integer value
  | .application head arguments =>
      .application head (groundTermsLength arguments)

/-- A missing key cannot refute a candidate. A known key compares only
the chosen rigid root, not the complete term. -/
def keyCompatible (query : GroundTerm) : Option DispatchKey → Bool
  | none => true
  | some key => key == groundRootKey query

/-- The same rigid test on a source term and a closed target. -/
def rootCompatible (source : Term) (target : GroundTerm) : Bool :=
  keyCompatible target (rootKey? source)

/-- Instantiation preserves the immediate arity of a term list. -/
theorem groundTermsLength_eq_of_instantiateTerms :
    forall (source : Terms) (substitution : Substitution)
      (target : GroundTerms),
      instantiateTerms substitution source = some target ->
        groundTermsLength target =
          CompiledPlanFixedHeadIndexCompilation.termsLength source
  | .nil, _, target, instantiated => by
      simp [instantiateTerms] at instantiated
      subst target
      rfl
  | .cons head tail, substitution, target, instantiated => by
      cases headInstantiated : instantiateTerm substitution head with
      | none =>
          simp [instantiateTerms, headInstantiated] at instantiated
      | some groundedHead =>
          cases tailInstantiated : instantiateTerms substitution tail with
          | none =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
          | some groundedTail =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
              subst target
              simp [groundTermsLength,
                CompiledPlanFixedHeadIndexCompilation.termsLength,
                groundTermsLength_eq_of_instantiateTerms tail substitution
                  groundedTail tailInstantiated]

/-- A successfully instantiated term always agrees with its target on every
visible rigid-root component. -/
theorem rootCompatible_of_instance
    (source : Term) (substitution : Substitution) (target : GroundTerm)
    (instantiated : instantiateTerm substitution source = some target) :
    rootCompatible source target = true := by
  cases source with
  | symbol name =>
      simp [instantiateTerm] at instantiated
      subst target
      simp [rootCompatible, keyCompatible, rootKey?, groundRootKey]
  | «variable» slot =>
      simp [rootCompatible, keyCompatible, rootKey?]
  | «string» value =>
      simp [instantiateTerm] at instantiated
      subst target
      simp [rootCompatible, keyCompatible, rootKey?, groundRootKey]
  | integer value =>
      simp [instantiateTerm] at instantiated
      subst target
      simp [rootCompatible, keyCompatible, rootKey?, groundRootKey]
  | application head arguments =>
      cases argumentsInstantiated :
          instantiateTerms substitution arguments with
      | none =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
      | some groundedArguments =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
          subst target
          have sameLength := groundTermsLength_eq_of_instantiateTerms
            arguments substitution groundedArguments argumentsInstantiated
          simp [rootCompatible, keyCompatible, rootKey?, groundRootKey, sameLength]

/-! ## Exact immediate-coordinate projection -/

/-- Read one immediate source argument. -/
def termAt? : Terms -> Nat -> Option Term
  | .nil, _ => none
  | .cons head _, 0 => some head
  | .cons _ tail, coordinate + 1 => termAt? tail coordinate

/-- Read one immediate closed argument. -/
def groundTermAt? : GroundTerms -> Nat -> Option GroundTerm
  | .nil, _ => none
  | .cons head _, 0 => some head
  | .cons _ tail, coordinate + 1 => groundTermAt? tail coordinate

/-- Project a source head to one argument coordinate. -/
def headCoordinate? (head : Term) (coordinate : Nat) : Option Term :=
  match head with
  | .application _ arguments => termAt? arguments coordinate
  | _ => none

/-- Project a closed query head to one argument coordinate. -/
def groundHeadCoordinate? (head : GroundTerm) (coordinate : Nat) :
    Option GroundTerm :=
  match head with
  | .application _ arguments => groundTermAt? arguments coordinate
  | _ => none

/-- Instantiating a term list preserves every coordinate and its exact
instantiated value. -/
theorem instantiateTerms_termAt? :
    forall (source : Terms) (substitution : Substitution)
      (target : GroundTerms) (coordinate : Nat) (sourceTerm : Term),
      instantiateTerms substitution source = some target ->
        termAt? source coordinate = some sourceTerm ->
          exists targetTerm,
            groundTermAt? target coordinate = some targetTerm /\
              instantiateTerm substitution sourceTerm = some targetTerm
  | .nil, _, _, _, _, _, sourceFound => by
      simp [termAt?] at sourceFound
  | .cons head tail, substitution, target, coordinate, sourceTerm,
      instantiated, sourceFound => by
      cases headInstantiated : instantiateTerm substitution head with
      | none =>
          simp [instantiateTerms, headInstantiated] at instantiated
      | some groundedHead =>
          cases tailInstantiated : instantiateTerms substitution tail with
          | none =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
          | some groundedTail =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
              subst target
              cases coordinate with
              | zero =>
                  simp [termAt?] at sourceFound
                  subst sourceTerm
                  exact ⟨groundedHead, rfl, headInstantiated⟩
              | succ coordinate =>
                  exact instantiateTerms_termAt? tail substitution
                    groundedTail coordinate sourceTerm tailInstantiated
                    sourceFound

/-- When a complete rule head instantiates to a closed query, the same
selected coordinate exists on both sides and remains rigid-compatible. -/
theorem coordinateCompatible_of_headInstance
    (source : Term) (substitution : Substitution) (target : GroundTerm)
    (coordinate : Nat) (sourceTerm : Term)
    (instantiated : instantiateTerm substitution source = some target)
    (sourceFound : headCoordinate? source coordinate = some sourceTerm) :
    exists targetTerm,
      groundHeadCoordinate? target coordinate = some targetTerm /\
        rootCompatible sourceTerm targetTerm = true := by
  cases source with
  | symbol name => simp [headCoordinate?] at sourceFound
  | «variable» slot => simp [headCoordinate?] at sourceFound
  | «string» value => simp [headCoordinate?] at sourceFound
  | integer value => simp [headCoordinate?] at sourceFound
  | application head arguments =>
      cases argumentsInstantiated :
          instantiateTerms substitution arguments with
      | none =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
      | some groundedArguments =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
          subst target
          obtain ⟨targetTerm, targetFound, coordinateInstantiated⟩ :=
            instantiateTerms_termAt? arguments substitution
              groundedArguments coordinate sourceTerm argumentsInstantiated
              sourceFound
          exact ⟨targetTerm, targetFound,
            rootCompatible_of_instance sourceTerm substitution targetTerm
              coordinateInstantiated⟩

/-- Generated key for one source rule at a candidate coordinate. -/
def ruleCoordinateKey? (coordinate : Nat) (rule : TypedRule) :
    Option DispatchKey :=
  (headCoordinate? rule.head coordinate).bind rootKey?

/-- One generated occurrence in a dispatch plan. -/
structure Entry where
  rule : TypedRule
  key : Option DispatchKey
  deriving DecidableEq, Repr

/-- Generated per-occurrence key inventory. -/
def compileEntries (coordinate : Nat) (rules : List TypedRule) : List Entry :=
  rules.map fun rule =>
    { rule, key := ruleCoordinateKey? coordinate rule }

/-- Execute the selected occurrence inventory in its original order. -/
def executeEntries (query : GroundTerm) (entries : List Entry) : List TypedRule :=
  entries.filterMap fun entry =>
    if keyCompatible query entry.key then some entry.rule else none

/-- Source-order specification for rigid-coordinate candidates. -/
def sourceCandidates (coordinate : Nat) (query : GroundTerm)
    (rules : List TypedRule) : List TypedRule :=
  rules.filter fun rule =>
    keyCompatible query (ruleCoordinateKey? coordinate rule)

/-- Generated entries retain exactly the source scan, including order and
multiplicity. -/
theorem executeEntries_compileEntries
    (coordinate : Nat) (query : GroundTerm) (rules : List TypedRule) :
    executeEntries query (compileEntries coordinate rules) =
      sourceCandidates coordinate query rules := by
  simp only [executeEntries, compileEntries, List.filterMap_map, Function.comp_def,
    sourceCandidates, ← List.filterMap_eq_filter, Option.guard]

/-- Compiling entries never changes the underlying source occurrence list. -/
theorem compileEntries_rules (coordinate : Nat) (rules : List TypedRule) :
    (compileEntries coordinate rules).map Entry.rule = rules := by
  simp [compileEntries, Function.comp_def]

/-- A possible rule application survives generated rigid-coordinate
selection. -/
theorem mem_sourceCandidates_of_headInstance
    (coordinate : Nat) (queryCoordinate : GroundTerm)
    (rules : List TypedRule) (rule : TypedRule)
    (member : rule ∈ rules) (substitution : Substitution)
    (queryHead : GroundTerm)
    (instantiated :
      instantiateTerm substitution rule.head = some queryHead)
    (queryFound :
      groundHeadCoordinate? queryHead coordinate = some queryCoordinate) :
    rule ∈ sourceCandidates coordinate queryCoordinate rules := by
  apply List.mem_filter.mpr
  refine ⟨member, ?_⟩
  cases sourceFound : headCoordinate? rule.head coordinate with
  | none => simp [ruleCoordinateKey?, sourceFound, keyCompatible]
  | some sourceTerm =>
      obtain ⟨targetTerm, targetFound, compatible⟩ :=
        coordinateCompatible_of_headInstance rule.head substitution queryHead
          coordinate sourceTerm instantiated sourceFound
      rw [queryFound] at targetFound
      cases targetFound
      simpa [ruleCoordinateKey?, sourceFound, rootCompatible] using compatible

/-- Therefore the exact generated entry program never removes a rule that
can instantiate to the closed query. -/
theorem mem_executeEntries_of_headInstance
    (coordinate : Nat) (queryCoordinate : GroundTerm)
    (rules : List TypedRule) (rule : TypedRule)
    (member : rule ∈ rules) (substitution : Substitution)
    (queryHead : GroundTerm)
    (instantiated :
      instantiateTerm substitution rule.head = some queryHead)
    (queryFound :
      groundHeadCoordinate? queryHead coordinate = some queryCoordinate) :
    rule ∈ executeEntries queryCoordinate
      (compileEntries coordinate rules) := by
  rw [executeEntries_compileEntries]
  exact mem_sourceCandidates_of_headInstance coordinate queryCoordinate rules
    rule member substitution queryHead instantiated queryFound

/-- Coordinate selection preserves exact results, even when one rule
occurrence yields several results. The observer must be fixed on this word;
the only per-rule obligation is that emission implies a head instance. -/
theorem executeEntries_flatMap_eq {Answer : Type*}
    (coordinate : Nat) (queryHead queryCoordinate : GroundTerm)
    (rules : List TypedRule) (observe : TypedRule → List Answer)
    (queryFound : groundHeadCoordinate? queryHead coordinate = some queryCoordinate)
    (sound : ∀ rule ∈ rules, observe rule ≠ [] →
      ∃ substitution, instantiateTerm substitution rule.head = some queryHead) :
    (executeEntries queryCoordinate (compileEntries coordinate rules)).flatMap observe =
      rules.flatMap observe := by
  rw [executeEntries_compileEntries]
  apply (Mettapedia.Data.List.OrderedPrefilter.filter_flatMap_eq_iff _ observe rules).mpr
  intro rule member produces
  obtain ⟨substitution, instantiated⟩ := sound rule member produces
  exact (List.mem_filter.mp (mem_sourceCandidates_of_headInstance coordinate queryCoordinate
    rules rule member substitution queryHead instantiated queryFound)).2

#print axioms executeEntries_compileEntries
#print axioms executeEntries_flatMap_eq

end Mettapedia.GSLT.LanguageDef.CompiledPlanRigidCoordinateCompilation
