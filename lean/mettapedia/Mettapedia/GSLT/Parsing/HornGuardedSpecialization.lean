import Mettapedia.GSLT.Parsing.HornSpecializationBody
import Mettapedia.GSLT.Parsing.GuardCorrespondence

/-!
# Guard-preserving specialization of Horn parser rules

Linear stream extraction alone weakens two ordinary Horn shapes: a literal
`nil` output means physical EOF, and an existential recursive call whose input
and head output are the same is positive lookahead.  This module classifies
those shapes generically from a checked `StreamProduction` and retains them as
ordinary normalized guards.  It does not inspect grammar constructors or
guest-language names.
-/

namespace Mettapedia.GSLT.Parsing.HornGuardedSpecialization

open CompilerCorrespondence GuardCorrespondence HornCertificate HornStream
open HornSpecialization HornSpecializationBody

def eofGuards : StreamTerm → List SourceGuard
  | .nil => [.atEnd]
  | _ => []

def LookaheadShape (production : StreamProduction)
    (category : Category) : Prop :=
  ∃ call : ParseCall,
    production.calls = [call] ∧
    production.start = production.finish ∧
    call.input = production.start ∧
    call.output ≠ production.start ∧
    call.category = category

def detectLookahead (production : StreamProduction) : Option Category :=
  if production.start != production.finish then none
  else match production.calls with
    | [call] =>
        if call.input != production.start then none
        else if call.output = production.start then none
        else some call.category
    | _ => none

theorem detectLookahead_iff (production : StreamProduction)
    (category : Category) :
    detectLookahead production = some category ↔
      LookaheadShape production category := by
  rcases production with ⟨sourceRule, productionCategory, start, finish, calls⟩
  cases calls with
  | nil => simp [detectLookahead, LookaheadShape]
  | cons call rest =>
      cases rest with
      | nil =>
          by_cases sameCursor : start = finish
          · by_cases sameInput : call.input = start
            · by_cases consumes : call.output = start
              · simp [detectLookahead, LookaheadShape, sameCursor, sameInput,
                  consumes]
              · simp [detectLookahead, LookaheadShape, sameCursor, sameInput]
            · simp [detectLookahead, LookaheadShape, sameCursor]
          · simp [detectLookahead, LookaheadShape, sameCursor]
      | cons another more => simp [detectLookahead, LookaheadShape]

inductive StreamShape (production : StreamProduction) :
    List SourceSymbol → List SourceGuard → Prop where
  | lookahead (category : Category)
      (shape : LookaheadShape production category) :
      StreamShape production []
        (.lookahead category :: eofGuards production.finish)
  | linear (symbols : List SourceSymbol)
      (notLookahead : detectLookahead production = none)
      (path : Linearizes [] production.start production.finish production.calls
        symbols) :
      StreamShape production symbols (eofGuards production.finish)

def classifyStream (fuel : Nat) (production : StreamProduction) :
    Option (List SourceSymbol × List SourceGuard) :=
  match detectLookahead production with
  | some category =>
      some ([], .lookahead category :: eofGuards production.finish)
  | none => do
      let symbols ← linearize fuel [] production.start production.finish
        production.calls
      pure (symbols, eofGuards production.finish)

theorem classifyStream_sound (fuel : Nat) (production : StreamProduction)
    (symbols : List SourceSymbol) (guards : List SourceGuard)
    (accepted : classifyStream fuel production = some (symbols, guards)) :
    StreamShape production symbols guards := by
  unfold classifyStream at accepted
  cases detected : detectLookahead production with
  | some category =>
      simp only [detected] at accepted
      simp only [Option.some.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact .lookahead category ((detectLookahead_iff production category).mp
        detected)
  | none =>
      simp only [detected] at accepted
      cases linearized : linearize fuel [] production.start production.finish
          production.calls with
      | none => simp [linearized] at accepted
      | some actualSymbols =>
          simp [linearized] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact .linear actualSymbols detected
            (linearize_sound fuel [] production.start production.finish
              production.calls actualSymbols linearized)

theorem StreamShape.hasClassification
    {production : StreamProduction} {symbols : List SourceSymbol}
    {guards : List SourceGuard}
    (shape : StreamShape production symbols guards) :
    ∃ fuel, classifyStream fuel production = some (symbols, guards) := by
  cases shape with
  | lookahead category lookahead =>
      have detected := (detectLookahead_iff production category).mpr lookahead
      exact ⟨0, by simp [classifyStream, detected]⟩
  | linear symbols notLookahead path =>
      obtain ⟨fuel, linearized⟩ := linearize_complete path
      exact ⟨fuel, by simp [classifyStream, notLookahead, linearized]⟩

def sourceRuleOf (production : StreamProduction) (symbols : List SourceSymbol)
    (guards : List SourceGuard) : GuardCorrespondence.SourceRule :=
  { sourceRule := production.sourceRule
    category := production.category
    symbols := symbols
    guards := guards }

structure GuardedRequest where
  certificate : SpecializationCertificate
  fuel : Nat
  deriving DecidableEq, Repr

def compileGuardedRequest (program : Program) (parseRelation : String)
    (request : GuardedRequest) : Option GuardCorrespondence.SourceRule := do
  let production ← specialize program parseRelation request.certificate
  let (symbols, guards) ← classifyStream request.fuel production
  pure (sourceRuleOf production symbols guards)

inductive GuardedCompilation (program : Program) (parseRelation : String) :
    GuardedRequest → GuardCorrespondence.SourceRule → Prop where
  | intro (request : GuardedRequest) (production : StreamProduction)
      (symbols : List SourceSymbol) (guards : List SourceGuard)
      (specialization : Specializes program parseRelation request.certificate
        production)
      (shape : StreamShape production symbols guards) :
      GuardedCompilation program parseRelation request
        (sourceRuleOf production symbols guards)

theorem compileGuardedRequest_sound (program : Program) (parseRelation : String)
    (request : GuardedRequest) (rule : GuardCorrespondence.SourceRule)
    (accepted : compileGuardedRequest program parseRelation request = some rule) :
    GuardedCompilation program parseRelation request rule := by
  unfold compileGuardedRequest at accepted
  cases specialized : specialize program parseRelation request.certificate with
  | none => simp [specialized] at accepted
  | some production =>
      cases classified : classifyStream request.fuel production with
      | none => simp [specialized, classified] at accepted
      | some result =>
          rcases result with ⟨symbols, guards⟩
          simp [specialized, classified] at accepted
          subst rule
          exact .intro request production symbols guards
            (specialize_sound program parseRelation request.certificate production
              specialized)
            (classifyStream_sound request.fuel production symbols guards classified)

theorem GuardedCompilation.hasCheckedRequest
    {program : Program} {parseRelation : String} {request : GuardedRequest}
    {rule : GuardCorrespondence.SourceRule}
    (semantic : GuardedCompilation program parseRelation request rule) :
    ∃ checked : GuardedRequest,
      checked.certificate = request.certificate ∧
      compileGuardedRequest program parseRelation checked = some rule := by
  cases semantic with
  | intro production symbols guards specialization shape =>
      obtain ⟨fuel, classified⟩ := StreamShape.hasClassification shape
      let checked : GuardedRequest :=
        { certificate := request.certificate, fuel := fuel }
      refine ⟨checked, rfl, ?_⟩
      simp [compileGuardedRequest,
        specialize_complete program parseRelation request.certificate production
          specialization,
        classified, checked]

/-- Certificate-independent meaning of one guard-preserving specialization. -/
inductive SemanticGuardedCompilation (program : Program)
    (parseRelation : String) (rule : Rule)
    (substitution : SymbolicSubstitution) (categories : CategoryTable)
    (normalized : GuardCorrespondence.SourceRule) : Prop where
  | intro (production : StreamProduction) (symbols : List SourceSymbol)
      (guards : List SourceGuard)
      (specialization :
        SemanticSpecializes program parseRelation rule substitution categories
          production)
      (shape : StreamShape production symbols guards)
      (normalizedEq : normalized = sourceRuleOf production symbols guards) :
      SemanticGuardedCompilation program parseRelation rule substitution
        categories normalized

theorem semanticGuardedCompilation_iff_exists_checkedRequest
    (program : Program) (parseRelation : String) (rule : Rule)
    (substitution : SymbolicSubstitution) (categories : CategoryTable)
    (normalized : GuardCorrespondence.SourceRule) :
    SemanticGuardedCompilation program parseRelation rule substitution categories
        normalized ↔
      ∃ sides : List SideCertificate, ∃ fuel,
        compileGuardedRequest program parseRelation
          { certificate :=
              { rule := rule, substitution := substitution,
                categories := categories, sides := sides }
            fuel := fuel } = some normalized := by
  constructor
  · intro semantic
    cases semantic with
    | intro production symbols guards specialization shape normalizedEq =>
        obtain ⟨sides, specializes⟩ := specialization.hasCertificate
        obtain ⟨fuel, classified⟩ := shape.hasClassification
        refine ⟨sides, fuel, ?_⟩
        rw [normalizedEq]
        simp [compileGuardedRequest,
          specialize_complete program parseRelation
            { rule := rule, substitution := substitution,
              categories := categories, sides := sides }
            production specializes,
          classified]
  · rintro ⟨sides, fuel, accepted⟩
    have checked := compileGuardedRequest_sound program parseRelation
      { certificate :=
          { rule := rule, substitution := substitution, categories := categories,
            sides := sides }
        fuel := fuel }
      normalized accepted
    cases checked with
    | intro production symbols guards specializes shape =>
        exact .intro production symbols guards
          (HornSpecializationBody.Specializes.toSemantic specializes) shape rfl

def SemanticallyCompilableGuardedRule (program : Program)
    (parseRelation : String) (normalized : GuardCorrespondence.SourceRule) : Prop :=
  ∃ rule substitution categories,
    SemanticGuardedCompilation program parseRelation rule substitution categories
      normalized

theorem compileGuardedRequest_semantically
    {program : Program} {parseRelation : String} {request : GuardedRequest}
    {normalized : GuardCorrespondence.SourceRule}
    (accepted : compileGuardedRequest program parseRelation request =
      some normalized) :
    SemanticallyCompilableGuardedRule program parseRelation normalized := by
  have compiled := compileGuardedRequest_sound program parseRelation request
    normalized accepted
  cases compiled with
  | intro production symbols guards specializes shape =>
      exact ⟨request.certificate.rule, request.certificate.substitution,
        request.certificate.categories,
        .intro production symbols guards
          (HornSpecializationBody.Specializes.toSemantic specializes) shape rfl⟩

/-- Semantic guard-preserving compilability is exactly the existence of a
checked request accepted by the executable compiler.  This theorem does not
restrict the witness to a precomputed finite candidate list. -/
theorem semanticallyCompilableGuardedRule_iff_exists_checkedRequest
    (program : Program) (parseRelation : String)
    (normalized : GuardCorrespondence.SourceRule) :
    SemanticallyCompilableGuardedRule program parseRelation normalized ↔
      ∃ request : GuardedRequest,
        compileGuardedRequest program parseRelation request = some normalized := by
  constructor
  · rintro ⟨rule, substitution, categories, semantic⟩
    obtain ⟨sides, fuel, accepted⟩ :=
      (semanticGuardedCompilation_iff_exists_checkedRequest program parseRelation
        rule substitution categories normalized).mp semantic
    exact ⟨
      { certificate :=
          { rule := rule, substitution := substitution,
            categories := categories, sides := sides }
        fuel := fuel },
      accepted⟩
  · rintro ⟨request, accepted⟩
    exact compileGuardedRequest_semantically accepted

def discoveredGuardedRules (program : Program) (parseRelation : String)
    (candidates : List GuardedRequest) : List GuardCorrespondence.SourceRule :=
  candidates.filterMap (compileGuardedRequest program parseRelation)

theorem mem_discoveredGuardedRules_iff (program : Program)
    (parseRelation : String) (candidates : List GuardedRequest)
    (normalized : GuardCorrespondence.SourceRule) :
    normalized ∈ discoveredGuardedRules program parseRelation candidates ↔
      ∃ request ∈ candidates,
        compileGuardedRequest program parseRelation request = some normalized := by
  simp [discoveredGuardedRules]

/-- A finite list observation.  Membership here is bookkeeping evidence, not a
definition of semantic admission. -/
def ListedGuardedRule (expected : List GuardCorrespondence.SourceRule)
    (normalized : GuardCorrespondence.SourceRule) : Prop :=
  normalized ∈ expected

/-- The additional obligation needed to turn a finite request basis into a
complete decision procedure for semantic guard-preserving compilability. -/
structure GuardedSemanticCompleteness (program : Program)
    (parseRelation : String) (candidates : List GuardedRequest) : Prop where
  covers : ∀ normalized,
    SemanticallyCompilableGuardedRule program parseRelation normalized →
    ∃ request ∈ candidates,
      compileGuardedRequest program parseRelation request = some normalized

theorem discoveredGuardedRules_iff_semanticallyCompilable
    (program : Program) (parseRelation : String)
    (candidates : List GuardedRequest)
    (complete : GuardedSemanticCompleteness program parseRelation candidates)
    (normalized : GuardCorrespondence.SourceRule) :
    normalized ∈ discoveredGuardedRules program parseRelation candidates ↔
      SemanticallyCompilableGuardedRule program parseRelation normalized := by
  constructor
  · intro discovered
    obtain ⟨request, _requestMember, accepted⟩ :=
      (mem_discoveredGuardedRules_iff program parseRelation candidates
        normalized).mp discovered
    exact compileGuardedRequest_semantically accepted
  · intro semantic
    obtain ⟨request, requestMember, accepted⟩ := complete.covers normalized semantic
    exact (mem_discoveredGuardedRules_iff program parseRelation candidates
      normalized).mpr ⟨request, requestMember, accepted⟩

structure GuardedSemanticCandidateCoverage (program : Program)
    (parseRelation : String)
    (admittedRule : GuardCorrespondence.SourceRule → Prop)
    (candidates : List GuardedRequest) : Prop where
  eligible : ∀ request, request ∈ candidates → ∀ normalized,
    compileGuardedRequest program parseRelation request = some normalized →
      admittedRule normalized
  covers : ∀ normalized,
    admittedRule normalized →
    SemanticallyCompilableGuardedRule program parseRelation normalized →
    ∃ request ∈ candidates,
      compileGuardedRequest program parseRelation request = some normalized

theorem discoveredGuardedRules_iff_admittedSemantic
    (program : Program) (parseRelation : String)
    (admittedRule : GuardCorrespondence.SourceRule → Prop)
    (candidates : List GuardedRequest)
    (coverage : GuardedSemanticCandidateCoverage program parseRelation
      admittedRule candidates)
    (normalized : GuardCorrespondence.SourceRule) :
    normalized ∈ discoveredGuardedRules program parseRelation candidates ↔
      admittedRule normalized ∧
        SemanticallyCompilableGuardedRule program parseRelation normalized := by
  constructor
  · intro member
    obtain ⟨request, requestMember, accepted⟩ :=
      (mem_discoveredGuardedRules_iff program parseRelation candidates
        normalized).1 member
    exact ⟨coverage.eligible request requestMember normalized accepted,
      compileGuardedRequest_semantically accepted⟩
  · rintro ⟨admitted, semantic⟩
    obtain ⟨request, requestMember, accepted⟩ :=
      coverage.covers normalized admitted semantic
    exact (mem_discoveredGuardedRules_iff program parseRelation candidates
      normalized).2 ⟨request, requestMember, accepted⟩

/-- Exact output of one finite compiler run.  This records which rules were
found; it does not establish that the finite candidates cover every semantic
witness. -/
structure ExactGuardedCompilationManifest (program : Program)
    (parseRelation : String) (expected : List GuardCorrespondence.SourceRule)
    (candidates : List GuardedRequest) : Prop where
  exact : discoveredGuardedRules program parseRelation candidates = expected

theorem ExactGuardedCompilationManifest.listedCandidateCoverage
    {program : Program} {parseRelation : String}
    {expected : List GuardCorrespondence.SourceRule}
    {candidates : List GuardedRequest}
    (manifest : ExactGuardedCompilationManifest program parseRelation expected
      candidates) :
    GuardedSemanticCandidateCoverage program parseRelation
      (ListedGuardedRule expected) candidates := by
  constructor
  · intro request requestMember normalized accepted
    have discovered :
        normalized ∈ discoveredGuardedRules program parseRelation candidates :=
      (mem_discoveredGuardedRules_iff program parseRelation candidates
        normalized).2 ⟨request, requestMember, accepted⟩
    simpa [ListedGuardedRule, manifest.exact] using discovered
  · intro normalized admitted _semantic
    have discovered :
        normalized ∈ discoveredGuardedRules program parseRelation candidates := by
      simpa [ListedGuardedRule, manifest.exact] using admitted
    exact (mem_discoveredGuardedRules_iff program parseRelation candidates
      normalized).1 discovered

theorem ExactGuardedCompilationManifest.listed_iff_discovered
    {program : Program} {parseRelation : String}
    {expected : List GuardCorrespondence.SourceRule}
    {candidates : List GuardedRequest}
    (manifest : ExactGuardedCompilationManifest program parseRelation expected
      candidates) (normalized : GuardCorrespondence.SourceRule) :
    ListedGuardedRule expected normalized ↔
      normalized ∈ discoveredGuardedRules program parseRelation candidates := by
  simp only [ListedGuardedRule, manifest.exact]

theorem ExactGuardedCompilationManifest.listed_semanticallyCompilable
    {program : Program} {parseRelation : String}
    {expected : List GuardCorrespondence.SourceRule}
    {candidates : List GuardedRequest}
    (manifest : ExactGuardedCompilationManifest program parseRelation expected
      candidates) {normalized : GuardCorrespondence.SourceRule}
    (listed : ListedGuardedRule expected normalized) :
    SemanticallyCompilableGuardedRule program parseRelation normalized := by
  have discovered :
      normalized ∈ discoveredGuardedRules program parseRelation candidates :=
    (manifest.listed_iff_discovered normalized).mp listed
  obtain ⟨request, _requestMember, accepted⟩ :=
    (mem_discoveredGuardedRules_iff program parseRelation candidates
      normalized).mp discovered
  exact compileGuardedRequest_semantically accepted

/-! Small positive and negative shape controls. -/

def eofProduction : StreamProduction :=
  { sourceRule := "eof"
    category := "eof"
    start := .nil
    finish := .nil
    calls := [] }

def lookaheadProduction : StreamProduction :=
  { sourceRule := "peek"
    category := "peek"
    start := .var 0
    finish := .var 0
    calls := [{ input := .var 0, output := .var 1, category := "child" }] }

def malformedLookaheadProduction : StreamProduction :=
  { lookaheadProduction with
    calls := [{ input := .var 0, output := .var 0, category := "child" }] }

theorem eof_shape_keeps_physical_end :
    classifyStream 1 eofProduction = some ([], [.atEnd]) := by
  decide

theorem positive_lookahead_shape_is_detected :
    classifyStream 1 lookaheadProduction =
      some ([], [.lookahead "child"]) := by
  decide

theorem nonconsuming_recursive_cycle_is_not_lookahead :
    detectLookahead malformedLookaheadProduction = none := by
  decide

end Mettapedia.GSLT.Parsing.HornGuardedSpecialization
