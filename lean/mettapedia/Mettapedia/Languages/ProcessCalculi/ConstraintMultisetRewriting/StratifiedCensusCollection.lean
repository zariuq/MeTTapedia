import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation
import Mettapedia.GSLT.LanguageDef.TemplateScope.RolesCollection

/-!
# Actual query collection at a stratified binding cut

The collection runs the existing single-read source program and instantiates
its returned templates. It keeps the ordered read transcript and the complete
predicate census. The role theorem is applied to this concrete observation,
not to a separate hand-written answer list.

Pointwise dependency contracts for the match region and emitted values imply
the whole packet reads only the declared shared names. Once those names are
determined, refinement preserves the packet. Observing after the frame's
constraints has the same declarative meaning in every order of those
constraints. The row view and scanner order stay fixed in that result;
changed rows and changed order require their own read validation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StratifiedCensusCollection

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Collection

universe uN uT uP uO
variable {N : Type uN} {T : Type uT} {P : Type uP} {O : Type uO}

def values (layer : Sources.TermLayer N T P) (template : P)
    (found : List (Sources.Subst N T × Sources.Pick O T)) : List T :=
  found.filterMap fun row => layer.inst row.1 template

def emitted (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (pattern template : P) (state : Store N T) (value : T) : List T :=
  (matcher pattern state value).filterMap fun answer => layer.inst answer template

variable [DecidableEq O]

def program (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (pattern template : P) (state : Store N T) :
    ReadOnlyQuery.Program (T → Bool) (List O) (List T) :=
  ReadOnlyQuery.map (values layer template) (Sources.Query.step matcher label (.read pattern) state)

def observe (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P) (state : Store N T) :=
  ReadOnlyQuery.run (Sources.Query.scanList label contents) (program layer matcher label pattern template state)

theorem observe_answer (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P) (state : Store N T) :
    (observe layer matcher label contents pattern template state).answer =
      (Sources.Query.scanList label contents (Sources.Matcher.region matcher state pattern)).flatMap
        (fun occurrence => emitted layer matcher pattern template state (label occurrence)) := by
  simp only [observe, program, ReadOnlyQuery.run_map, Sources.Query.step, ReadOnlyQuery.run,
    values, List.filterMap_flatMap, List.filterMap_map, Function.comp_def, emitted]

theorem observe_reads (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P) (state : Store N T) :
    (observe layer matcher label contents pattern template state).reads =
      [(Sources.Matcher.region matcher state pattern,
        Sources.Query.scanList label contents (Sources.Matcher.region matcher state pattern))] := rfl

def census (matcher : Sources.Matcher N T P) (label : O → T) (contents : List O)
    (pattern : P) (state : Store N T) : PredicateQuery O T :=
  ⟨Sources.Matcher.region matcher state pattern,
    (Sources.Query.scanList label contents (Sources.Matcher.region matcher state pattern)).toFinset⟩

theorem census_holds (matcher : Sources.Matcher N T P) (label : O → T) (contents : List O)
    (unique : contents.Nodup) (pattern : P) (state : Store N T) :
    (census matcher label contents pattern state).Holds label contents.toFinset :=
  (Sources.Query.scanList_complete label contents unique).seen _ |>.symm

def packet (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P) (state : Store N T) :=
  (observe layer matcher label contents pattern template state, census matcher label contents pattern state)

theorem packet_reads_only (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P) (names : List N)
    (regionReads : ∀ value, ReadsOnly names (fun state => Sources.Matcher.region matcher state pattern value))
    (valueReads : ∀ value, ReadsOnly names (fun state => emitted layer matcher pattern template state value)) :
    ReadsOnly names (packet layer matcher label contents pattern template) := by
  intro first second same
  have region : Sources.Matcher.region matcher first pattern = Sources.Matcher.region matcher second pattern :=
    funext fun value => regionReads value first second same
  have answers : (observe layer matcher label contents pattern template first).answer =
      (observe layer matcher label contents pattern template second).answer := by
    rw [observe_answer, observe_answer, region]
    apply congrArg (fun emit =>
      (Sources.Query.scanList label contents (Sources.Matcher.region matcher second pattern)).flatMap emit)
    funext occurrence
    exact valueReads (label occurrence) first second same
  have reads : (observe layer matcher label contents pattern template first).reads =
      (observe layer matcher label contents pattern template second).reads := by
    rw [observe_reads, observe_reads, region]
  have observations : observe layer matcher label contents pattern template first =
      observe layer matcher label contents pattern template second := by
    cases one : observe layer matcher label contents pattern template first
    cases two : observe layer matcher label contents pattern template second
    simp only [one, two] at answers reads
    cases answers
    cases reads
    rfl
  have censuses : census matcher label contents pattern first = census matcher label contents pattern second := by
    unfold census
    rw [region]
  exact Prod.ext observations censuses

theorem stable_after_determination (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P) (names : List N)
    (regionReads : ∀ value, ReadsOnly names (fun state => Sources.Matcher.region matcher state pattern value))
    (valueReads : ∀ value, ReadsOnly names (fun state => emitted layer matcher pattern template state value))
    {first second : Store N T} (determined : Determined names first) (refines : first ⊑ second) :
    packet layer matcher label contents pattern template second = packet layer matcher label contents pattern template first :=
  stratified_stable (packet_reads_only layer matcher label contents pattern template names regionReads valueReads)
    determined refines

variable [DecidableEq N] [DecidableEq T]

/-- The existing generic role theorem now observes the actual query packet,
including its answer order, census and retained scanner transcript. -/
theorem stratified_census_meaning (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P)
    {constraints reordered : Steps N T} (permuted : constraints.Perm reordered) :
    constrainFirst (packet layer matcher label contents pattern template) Store.empty reordered =
      (solveConj constraints).map fun state => (packet layer matcher label contents pattern template state, state) :=
  stratified_meaning _ permuted

theorem stratified_census_permutation (layer : Sources.TermLayer N T P) (matcher : Sources.Matcher N T P)
    (label : O → T) (contents : List O) (pattern template : P)
    {constraints reordered : Steps N T} (permuted : constraints.Perm reordered) :
    constrainFirst (packet layer matcher label contents pattern template) Store.empty constraints =
      constrainFirst (packet layer matcher label contents pattern template) Store.empty reordered :=
  stratified_perm _ permuted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StratifiedCensusCollection
