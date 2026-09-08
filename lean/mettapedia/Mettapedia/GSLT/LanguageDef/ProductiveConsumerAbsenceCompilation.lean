import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Absence of productive consumers in a finite source program

The source scan visits arbitrary expression children, including expression
heads. A variable-headed expression is a possible direct consumer; a named
expression head is a conservative forwarding edge. Other head forms contribute
no local seed or edge and their children are still scanned. This approximates
an analysis of authored syntax, not the evaluator's possible dynamic calls.

Cached productive records seed both their source and specialized names. A
bounded worklist can close a recursive component without declaring recursion
productive. Incomplete syntax or graph traversal remains unknown. Negative
results exclude independently defined finite analysis traces whose routes come
from actual source occurrences.

The finite source and record lists are mathematical inputs. Correspondence to
a live equation collector, freshening and matching, generated definitions,
record eligibility, symbol registries, and mutable authority is a separate
implementation bridge. No parameter-specific demand or evaluator equivalence
is claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProductiveConsumerAbsenceCompilation

open Mettapedia.Languages.MeTTa.OSLFCore

def syntaxChildren : Atom -> List Atom
  | .expression children => children
  | _ => []

def dynamicHead : Atom -> Bool
  | .expression (.var _ :: _) => true
  | _ => false

def namedHead? : Atom -> Option String
  | .expression (.symbol name :: _) => some name
  | _ => none

/-- A direct consumer occurrence described by source constructors, independently
of the executable scan. Nesting includes the head of an expression. -/
inductive DynamicOccurrence : Atom -> Prop
  | direct (name : String) (arguments : List Atom) :
      DynamicOccurrence (.expression (.var name :: arguments))
  | nested {container child : Atom}
      (present : child ∈ syntaxChildren container)
      (occurrence : DynamicOccurrence child) : DynamicOccurrence container

inductive NamedOccurrence (name : String) : Atom -> Prop
  | direct (arguments : List Atom) :
      NamedOccurrence name (.expression (.symbol name :: arguments))
  | nested {container child : Atom}
      (present : child ∈ syntaxChildren container)
      (occurrence : NamedOccurrence name child) : NamedOccurrence name container

theorem dynamicOccurrence_root_or_child
    (atom : Atom) (occurrence : DynamicOccurrence atom) :
    dynamicHead atom = true ∨
      ∃ child ∈ syntaxChildren atom, DynamicOccurrence child := by
  cases occurrence with
  | direct name arguments => exact Or.inl rfl
  | nested present occurrence => exact Or.inr ⟨_, present, occurrence⟩

theorem namedOccurrence_root_or_child
    (name : String) (atom : Atom) (occurrence : NamedOccurrence name atom) :
    namedHead? atom = some name ∨
      ∃ child ∈ syntaxChildren atom, NamedOccurrence name child := by
  cases occurrence with
  | direct arguments => exact Or.inl rfl
  | nested present occurrence => exact Or.inr ⟨_, present, occurrence⟩

inductive SyntaxResult where
  | closed (edges : List String)
  | possible
  | unknown
  deriving DecidableEq, Repr

def prependNamed (name : Option String) : SyntaxResult -> SyntaxResult
  | .closed edges => .closed (name.toList ++ edges)
  | .possible => .possible
  | .unknown => .unknown

/-- One unit of fuel permits one Atom visit. All expression children are put
on the frontier, including an arbitrary expression-valued head. Empty work is
complete even at zero fuel; nonempty unfinished work is unknown. -/
def scanSyntax : Nat -> List Atom -> SyntaxResult
  | _, [] => .closed []
  | 0, _ :: _ => .unknown
  | fuel + 1, atom :: rest =>
      if dynamicHead atom then .possible
      else prependNamed (namedHead? atom)
        (scanSyntax fuel (syntaxChildren atom ++ rest))

/-- A completed negative syntax scan contains every named-head occurrence and
rules out every variable-headed occurrence in the original forest. -/
theorem scanSyntax_closed_sound
    (fuel : Nat) (forest : List Atom) (edges : List String)
    (completed : scanSyntax fuel forest = .closed edges) :
    (∀ atom ∈ forest, ¬ DynamicOccurrence atom) ∧
      (∀ atom ∈ forest, ∀ name, NamedOccurrence name atom -> name ∈ edges) := by
  induction fuel generalizing forest edges with
  | zero =>
      cases forest with
      | nil => constructor <;> intro atom present <;> cases present
      | cons atom rest => simp [scanSyntax] at completed
  | succ fuel inductionHypothesis =>
      cases forest with
      | nil => constructor <;> intro atom present <;> cases present
      | cons atom rest =>
          by_cases seeded : dynamicHead atom = true
          · simp [scanSyntax, seeded] at completed
          · cases scanned : scanSyntax fuel (syntaxChildren atom ++ rest) with
            | possible => simp [scanSyntax, seeded, scanned, prependNamed] at completed
            | unknown => simp [scanSyntax, seeded, scanned, prependNamed] at completed
            | closed found =>
                have same : (namedHead? atom).toList ++ found = edges := by
                  simpa [scanSyntax, seeded, scanned, prependNamed] using completed
                obtain ⟨noDynamic, namedCovered⟩ :=
                  inductionHypothesis (syntaxChildren atom ++ rest) found scanned
                constructor
                · intro member present occurrence
                  rcases List.mem_cons.mp present with rfl | inRest
                  · rcases dynamicOccurrence_root_or_child member occurrence with
                      atRoot | ⟨child, inChildren, nested⟩
                    · exact seeded atRoot
                    · exact noDynamic child
                        (List.mem_append.mpr (Or.inl inChildren)) nested
                  · exact noDynamic member
                      (List.mem_append.mpr (Or.inr inRest)) occurrence
                · intro member present name occurrence
                  rw [← same]
                  rcases List.mem_cons.mp present with rfl | inRest
                  · rcases namedOccurrence_root_or_child name member occurrence with
                      atRoot | ⟨child, inChildren, nested⟩
                    · simp [atRoot]
                    · exact List.mem_append.mpr (Or.inr
                        (namedCovered child
                          (List.mem_append.mpr (Or.inl inChildren)) name nested))
                  · exact List.mem_append.mpr (Or.inr
                      (namedCovered member
                        (List.mem_append.mpr (Or.inr inRest)) name occurrence))

structure Equation where
  lhs : Atom
  rhs : Atom
  deriving Repr, DecidableEq

/-- Only records already established to be productive belong in this list.
The runtime's eligibility and authority check is outside this source model. -/
structure ProductiveRecord where
  source : String
  specialized : String
  deriving Repr, DecidableEq

structure Program where
  equations : List Equation
  records : List ProductiveRecord
  deriving Repr, DecidableEq

/-- An authored equation whose ordinary named root is the selected relation.
The constructor exposes actual equation-list membership and LHS syntax. -/
inductive SourceClause (program : Program) (name : String) (rhs : Atom) : Prop
  | declared (arguments : List Atom)
      (present : { lhs := .expression (.symbol name :: arguments), rhs } ∈
        program.equations) : SourceClause program name rhs

def collectRhs (program : Program) (name : String) : List Atom :=
  program.equations.filterMap fun equation =>
    match equation.lhs with
    | .expression (.symbol head :: _) =>
        if head = name then some equation.rhs else none
    | _ => none

/-- The collector covers each independently described named source clause;
this is proved by inspecting its concrete filter, not supplied as a premise. -/
theorem sourceClause_collected
    (program : Program) (name : String) (rhs : Atom)
    (clause : SourceClause program name rhs) : rhs ∈ collectRhs program name := by
  cases clause with
  | declared arguments present =>
      exact List.mem_filterMap.mpr ⟨_, present, by simp⟩

def CachedSeed (program : Program) (name : String) : Prop :=
  ∃ record ∈ program.records,
    name = record.source ∨ name = record.specialized

def cachedSeed? (program : Program) (name : String) : Bool :=
  program.records.any fun record =>
    record.source == name || record.specialized == name

theorem cachedSeed_possible
    (program : Program) (name : String) (seed : CachedSeed program name) :
    cachedSeed? program name = true := by
  obtain ⟨record, present, related⟩ := seed
  apply List.any_eq_true.mpr
  refine ⟨record, present, ?_⟩
  rcases related with rfl | rfl <;> simp

def LocalSeed (program : Program) (name : String) : Prop :=
  CachedSeed program name ∨
    ∃ rhs, SourceClause program name rhs ∧ DynamicOccurrence rhs

def SourceEdge (program : Program) (source target : String) : Prop :=
  ∃ rhs, SourceClause program source rhs ∧ NamedOccurrence target rhs

def scanRelation (syntaxFuel : Nat) (program : Program) (name : String) : SyntaxResult :=
  if cachedSeed? program name then .possible
  else scanSyntax syntaxFuel (collectRhs program name)

theorem scanRelation_closed_sound
    (syntaxFuel : Nat) (program : Program) (name : String) (edges : List String)
    (completed : scanRelation syntaxFuel program name = .closed edges) :
    ¬ LocalSeed program name ∧
      ∀ target, SourceEdge program name target -> target ∈ edges := by
  by_cases cached : cachedSeed? program name = true
  · simp [scanRelation, cached] at completed
  · have syntaxCompleted : scanSyntax syntaxFuel (collectRhs program name) =
        .closed edges := by
      simpa [scanRelation, cached] using completed
    obtain ⟨noDynamic, namedCovered⟩ :=
      scanSyntax_closed_sound syntaxFuel (collectRhs program name) edges syntaxCompleted
    constructor
    · intro seed
      rcases seed with record | ⟨rhs, clause, occurrence⟩
      · exact cached (cachedSeed_possible program name record)
      · exact noDynamic rhs (sourceClause_collected program name rhs clause) occurrence
    · intro target edge
      obtain ⟨rhs, clause, occurrence⟩ := edge
      exact namedCovered rhs (sourceClause_collected program name rhs clause)
        target occurrence

/-- Finite productive analysis routes. Every direct or forwarded step names an
actual RHS syntax occurrence; recursive forwarding alone creates no trace. -/
inductive ProductiveTrace (program : Program) : String -> Prop
  | direct (name : String) (rhs : Atom)
      (clause : SourceClause program name rhs)
      (occurrence : DynamicOccurrence rhs) : ProductiveTrace program name
  | cached (name : String) (seed : CachedSeed program name) :
      ProductiveTrace program name
  | forwarded (name target : String) (rhs : Atom)
      (clause : SourceClause program name rhs)
      (occurrence : NamedOccurrence target rhs)
      (continuation : ProductiveTrace program target) : ProductiveTrace program name

inductive AnalysisResult where
  | absent (checked : List String)
  | possible
  | unknown
  deriving Repr, DecidableEq

/-- The traversal has its own graph frontier and visited set. One graph-fuel
unit removes one pending item, including a visited back-edge. A fresh node is
marked visited only after a complete negative local scan. -/
def explore (syntaxFuel : Nat) (program : Program) :
    Nat -> List String -> List String -> AnalysisResult
  | _, seen, [] => .absent seen
  | 0, _, _ :: _ => .unknown
  | fuel + 1, seen, name :: rest =>
      if name ∈ seen then explore syntaxFuel program fuel seen rest
      else
        match scanRelation syntaxFuel program name with
        | .possible => .possible
        | .unknown => .unknown
        | .closed edges =>
            explore syntaxFuel program fuel (name :: seen) (edges ++ rest)

/-- Only nodes added during this traversal must be justified here. This
invariant permits induction over the executable visited-set algorithm without
assuming that an arbitrary incoming visited set is already sound. -/
def ClosedOutside (program : Program) (before checked : List String) : Prop :=
  ∀ name ∈ checked, name ∉ before ->
    ¬ LocalSeed program name ∧
      ∀ target, SourceEdge program name target -> target ∈ checked

/-- A negative traversal has exhausted the original frontier, retained the
incoming visited set, and justified every newly visited node by concrete
source-scan coverage. No graph-coverage certificate is an input. -/
theorem explore_absent_certificate
    (syntaxFuel fuel : Nat) (program : Program)
    (seen pending checked : List String)
    (completed : explore syntaxFuel program fuel seen pending = .absent checked) :
    seen ⊆ checked ∧ pending ⊆ checked ∧ ClosedOutside program seen checked := by
  induction fuel generalizing seen pending checked with
  | zero =>
      cases pending with
      | nil =>
          simp only [explore, AnalysisResult.absent.injEq] at completed
          subst checked
          refine ⟨fun _ present => present, ?_, ?_⟩
          · intro name present
            cases present
          · intro name present fresh
            exact False.elim (fresh present)
      | cons name rest => simp [explore] at completed
  | succ fuel inductionHypothesis =>
      cases pending with
      | nil =>
          simp only [explore, AnalysisResult.absent.injEq] at completed
          subst checked
          refine ⟨fun _ present => present, ?_, ?_⟩
          · intro name present
            cases present
          · intro name present fresh
            exact False.elim (fresh present)
      | cons name rest =>
          by_cases visited : name ∈ seen
          · have continued : explore syntaxFuel program fuel seen rest =
                .absent checked := by
              simpa [explore, visited] using completed
            obtain ⟨seenIncluded, restIncluded, newlyClosed⟩ :=
              inductionHypothesis seen rest checked continued
            refine ⟨seenIncluded, ?_, newlyClosed⟩
            intro member present
            rcases List.mem_cons.mp present with rfl | inRest
            · exact seenIncluded visited
            · exact restIncluded inRest
          · cases scanned : scanRelation syntaxFuel program name with
            | possible => simp [explore, visited, scanned] at completed
            | unknown => simp [explore, visited, scanned] at completed
            | closed edges =>
                have continued : explore syntaxFuel program fuel (name :: seen)
                    (edges ++ rest) = .absent checked := by
                  simpa [explore, visited, scanned] using completed
                obtain ⟨seenIncluded, frontierIncluded, newlyClosed⟩ :=
                  inductionHypothesis (name :: seen) (edges ++ rest) checked continued
                obtain ⟨noSeed, edgesCovered⟩ :=
                  scanRelation_closed_sound syntaxFuel program name edges scanned
                refine ⟨?_, ?_, ?_⟩
                · intro member present
                  exact seenIncluded (List.mem_cons.mpr (Or.inr present))
                · intro member present
                  rcases List.mem_cons.mp present with rfl | inRest
                  · exact seenIncluded (List.mem_cons_self)
                  · exact frontierIncluded (List.mem_append.mpr (Or.inr inRest))
                · intro member present notBefore
                  by_cases same : member = name
                  · subst member
                    refine ⟨noSeed, ?_⟩
                    intro target edge
                    exact frontierIncluded
                      (List.mem_append.mpr (Or.inl (edgesCovered target edge)))
                  · exact newlyClosed member present (by simp [same, notBefore])

/-- A finite productive trace cannot stay inside a seed-free edge-closed
region. The proof is induction on the independently generated source trace. -/
theorem productiveTrace_exits_seed_free_closed_region
    (program : Program) (checked : List String)
    (closed : ∀ name ∈ checked, ¬ LocalSeed program name ∧
      ∀ target, SourceEdge program name target -> target ∈ checked)
    (name : String) (trace : ProductiveTrace program name) :
    name ∈ checked -> False := by
  induction trace with
  | direct name rhs clause occurrence =>
      intro present
      exact (closed name present).1 (Or.inr ⟨rhs, clause, occurrence⟩)
  | cached name seed =>
      intro present
      exact (closed name present).1 (Or.inl seed)
  | forwarded name target rhs clause occurrence continuation inductionHypothesis =>
      intro present
      exact inductionHypothesis
        ((closed name present).2 target ⟨rhs, clause, occurrence⟩)

def analyze (syntaxFuel graphFuel : Nat) (program : Program)
    (name : String) : AnalysisResult :=
  explore syntaxFuel program graphFuel [] [name]

/-- The complete negative result excludes every finite productive analysis
trace rooted at the requested relation. Direct and forwarded routes were
derived from source occurrences, rather than assumed graph coverage. -/
theorem analyze_absent_no_productive_trace
    (syntaxFuel graphFuel : Nat) (program : Program) (name : String)
    (checked : List String)
    (absent : analyze syntaxFuel graphFuel program name = .absent checked) :
    ¬ ProductiveTrace program name := by
  obtain ⟨_, frontierIncluded, closed⟩ :=
    explore_absent_certificate syntaxFuel graphFuel program [] [name] checked absent
  intro trace
  exact productiveTrace_exits_seed_free_closed_region program checked
    (fun member present => closed member present (by simp)) name trace
    (frontierIncluded (List.mem_singleton_self name))

/-- Missing source or productive-record coverage is an explicit unavailable
input. Supplying either list is not itself a proof of correspondence to a
physical runtime's collector or registry. -/
def analyzeAvailable (syntaxFuel graphFuel : Nat)
    (equations : Option (List Equation)) (records : Option (List ProductiveRecord))
    (name : String) : AnalysisResult :=
  match equations, records with
  | some source, some cached => analyze syntaxFuel graphFuel ⟨source, cached⟩ name
  | _, _ => .unknown

theorem unavailable_equations_unknown
    (syntaxFuel graphFuel : Nat) (records : Option (List ProductiveRecord))
    (name : String) :
    analyzeAvailable syntaxFuel graphFuel none records name = .unknown := by
  cases records <;> rfl

theorem unavailable_records_unknown
    (syntaxFuel graphFuel : Nat) (equations : Option (List Equation))
    (name : String) :
    analyzeAvailable syntaxFuel graphFuel equations none name = .unknown := by
  cases equations <;> rfl

/-! ## Discriminating source programs -/

namespace Canaries

private def call (name : String) (arguments : List Atom) : Atom :=
  .expression (.symbol name :: arguments)

private def equation (name : String) (arguments : List Atom) (rhs : Atom) : Equation :=
  { lhs := call name arguments, rhs }

/-- The first RHS has an expression-valued head, as a syntax container may.
Its nested named occurrence must still be discovered. -/
private def cycle : Program where
  equations :=
    [equation "first" [.var "x"]
      (.expression [call "second" [.var "x"]]),
     equation "second" [.var "x"] (call "first" [.var "x"])]
  records := []

theorem expression_head_container_scanned :
    scanSyntax 8 [.expression [call "next" [], .grounded (.int 0)]] =
      .closed ["next"] ∧
    scanSyntax 8 [.expression [.expression [.var "operator", .grounded (.int 1)]]] =
      .possible := by
  decide

/-- A genuinely cyclic source graph closes after visiting both definitions
and removing its visited back-edge; recursion is not a consumer seed. -/
theorem no_consumer_recursive_component_absent :
    analyze 16 3 cycle "first" = .absent ["second", "first"] := by
  decide

theorem no_consumer_recursive_component_has_no_trace :
    ¬ ProductiveTrace cycle "first" :=
  analyze_absent_no_productive_trace 16 3 cycle "first" ["second", "first"]
    no_consumer_recursive_component_absent

/-- A new directly consuming equation destroys the previous absence result.
A cached negative summary must therefore include equation authority. -/
theorem added_consumer_changes_result :
    analyze 16 3
      { cycle with
        equations := equation "second" [.var "operator"]
          (.expression [.var "operator", .grounded (.int 1)]) :: cycle.equations }
      "first" = .possible := by
  decide

private def forwardedRhs : Atom :=
  call "apply" [.symbol "fixed-operator", .var "x"]

private def directRhs : Atom :=
  .expression [.var "operator", .grounded (.int 1)]

/-- The forwarded source parameter reaches only the unused parameter of the
callee. The callee is nevertheless a productive relation because its other
parameter is called. A relation-wide graph must preserve that distinction. -/
private def unusedArgument : Program where
  equations :=
    [equation "forwarder" [.var "x"] forwardedRhs,
     equation "apply" [.var "operator", .var "unused"] directRhs,
     equation "fixed-operator" [.var "n"] (.grounded (.int 11)),
     equation "unused-operator" [.var "n"] (.grounded (.int 22))]
  records := []

theorem unused_argument_counterexample_remains_possible :
    analyze 16 2 unusedArgument "forwarder" = .possible := by
  decide

/-- This positive is backed by a real source-derived route, independently of
the executable graph result. It does not attribute productivity to `x`. -/
theorem unused_argument_counterexample_has_trace :
    ProductiveTrace unusedArgument "forwarder" := by
  exact .forwarded "forwarder" "apply" forwardedRhs
    (.declared [.var "x"] (by decide))
    (.direct [.symbol "fixed-operator", .var "x"])
    (.direct "apply" directRhs
      (.declared [.var "operator", .var "unused"] (by decide))
      (.direct "operator" [.grounded (.int 1)]))

private def cached : Program where
  equations :=
    [equation "entry" [] (call "base-specialized" [])]
  records := [{ source := "base", specialized := "base-specialized" }]

theorem cached_source_and_specialized_names_seed :
    analyze 0 1 cached "base" = .possible ∧
    analyze 0 1 cached "base-specialized" = .possible ∧
    analyze 4 2 cached "entry" = .possible := by
  decide

theorem cached_specialized_name_has_trace :
    ProductiveTrace cached "base-specialized" := by
  apply ProductiveTrace.cached
  exact ⟨{ source := "base", specialized := "base-specialized" },
    by decide, Or.inr rfl⟩

/-- Adding a productive record changes the graph even if authored equations
are unchanged. Record authority cannot be omitted from a negative cache key. -/
theorem productive_record_changes_result :
    analyze 16 3
      { cycle with records := [{ source := "second", specialized := "second-specialized" }] }
      "first" = .possible := by
  decide

/-- Neither an unfinished syntax forest nor an unfinished graph frontier is
silently interpreted as absence. This graph bound counts the visited back-edge. -/
theorem insufficient_budgets_unknown :
    analyze 0 3 cycle "first" = .unknown ∧
    analyze 16 2 cycle "first" = .unknown ∧
    analyze 16 0 unusedArgument "forwarder" = .unknown := by
  decide

theorem incomplete_source_or_record_coverage_unknown :
    analyzeAvailable 16 3 none (some []) "first" = .unknown ∧
    analyzeAvailable 16 3 (some cycle.equations) none "first" = .unknown := by
  decide

/-- A symbol with no named equation and no productive record is a leaf of
this analysis graph. This does not classify its evaluator behavior. -/
theorem complete_empty_program_has_no_trace :
    ¬ ProductiveTrace { equations := [], records := [] } "leaf" := by
  exact analyze_absent_no_productive_trace 0 1 _ "leaf" ["leaf"] (by decide)

end Canaries

#print axioms scanSyntax_closed_sound
#print axioms sourceClause_collected
#print axioms cachedSeed_possible
#print axioms scanRelation_closed_sound
#print axioms explore_absent_certificate
#print axioms productiveTrace_exits_seed_free_closed_region
#print axioms analyze_absent_no_productive_trace
#print axioms Canaries.no_consumer_recursive_component_has_no_trace
#print axioms Canaries.unused_argument_counterexample_has_trace
#print axioms Canaries.cached_specialized_name_has_trace
#print axioms Canaries.insufficient_budgets_unknown

end Mettapedia.GSLT.LanguageDef.ProductiveConsumerAbsenceCompilation
