import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryBagMaterialization
import Mettapedia.Logic.CTLFormula

/-!
# CTL predecessor production at the bag-source boundary

The source core is the authored nested query followed by raw insertion and
`size-atom (collapse ...)`. Producer occurrences are ordered and counted;
their support is a separate Boolean observation. A set-space constructor is
not inferred from this ordinary PeTTa bag semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

private abbrev number (value : Nat) : Atom := .grounded (.int value)
def row (head : String) (left right : Atom) : Atom := .expression [.symbol head, left, right]
def satisfaction (head label : String) (state : Nat) : Atom := row head (.symbol label) (number state)
def reverseEdge (head : String) (edge : Nat × Nat) : Atom := row head (number edge.2) (number edge.1)

structure Names where
  space : String
  input : String
  output : String
  prior : String
  next : String
  distinct : [space, input, output, prior, next].Nodup

def satPattern (head : String) (names : Names) : Atom := row head (.var names.input) (.var names.next)
def reversePattern (head : String) (names : Names) : Atom := row head (.var names.next) (.var names.prior)
def template (head : String) (names : Names) : Atom := row head (.var names.output) (.var names.prior)
def legs (satHead reverseHead : String) (names : Names) (table graph : Handle) : List NestedQuerySource.Leg :=
  [(table, satPattern satHead names), (graph, reversePattern reverseHead names)]

def source (satHead reverseHead : String) (names : Names) (table graph : Handle) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse",
    NestedQuerySource.source (legs satHead reverseHead names table graph)
      (QueryBagMaterialization.insertion names.space (template satHead names))]]

def run (satHead reverseHead : String) (names : Names) (table graph : Handle) : Body :=
  NestedQuerySource.run (QueryBagMaterialization.emit table (template satHead names))
    (legs satHead reverseHead names table graph)

theorem source_returns (program : Program) (satHead reverseHead : String) (names : Names) (table graph : Handle)
    (caller : Subst) (before after : Effects.State) (answers : List Atom)
    (location : Subst.lookup caller names.space = some (Effects.handleValue table))
    (completed : run satHead reverseHead names table graph caller before = some (after, answers)) :
    PureReturns program caller before (source satHead reverseHead names table graph) after (.grounded (.int answers.length)) :=
  QueryBagMaterialization.counted_returns program names.space table (template satHead names) _ caller before after answers location completed

def operand (label : String) (rows : List (String × Nat)) : List Nat :=
  rows.filterMap (fun entry => if entry.1 = label then some entry.2 else none)

def predecessors (edges : List (Nat × Nat)) (next : Nat) : List Nat :=
  edges.filterMap (fun edge => if edge.2 = next then some edge.1 else none)

def produced (edges : List (Nat × Nat)) (targets : List Nat) : List Nat := targets.flatMap (predecessors edges)

theorem satisfaction_injective (head label : String) : Function.Injective (satisfaction head label) := by
  intro first second same
  simpa [satisfaction, row, number] using same

theorem mem_predecessors (edges : List (Nat × Nat)) (next prior : Nat) :
    prior ∈ predecessors edges next ↔ (prior, next) ∈ edges := by
  simp only [predecessors, List.mem_filterMap]
  constructor
  · rintro ⟨⟨left, right⟩, member, returned⟩
    split at returned
    next same =>
      change right = next at same
      subst right
      cases Option.some.inj returned
      exact member
    next => cases returned
  · intro member
    exact ⟨(prior, next), member, by simp⟩

theorem produced_support (edges : List (Nat × Nat)) (targets : List Nat) :
    {prior | prior ∈ produced edges targets} =
      Mettapedia.Logic.CTLFixedPoints.pre (fun prior next => (prior, next) ∈ edges) {next | next ∈ targets} := by
  ext prior
  simp only [produced, List.mem_flatMap, mem_predecessors, Mettapedia.Logic.CTLFixedPoints.pre, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨next, first, second⟩ <;> exact ⟨next, second, first⟩

/-- The valid-state domain must contain both ends of every retained edge.
Without that evidence, unqualified predecessor production is not CTL EX on
the declared model. -/
theorem produced_ex_readout (domain : Set Nat) (edges : List (Nat × Nat)) (targets : List Nat)
    (valid : ∀ edge ∈ edges, edge.1 ∈ domain ∧ edge.2 ∈ domain) :
    {prior | prior ∈ produced edges targets} = domain ∩
      Mettapedia.Logic.CTLFixedPoints.pre (fun prior next => (prior, next) ∈ edges)
        (domain ∩ {next | next ∈ targets}) := by
  rw [produced_support]
  ext prior
  constructor
  · rintro ⟨next, edge, member⟩
    exact ⟨(valid (prior, next) edge).1, next, edge, (valid (prior, next) edge).2, member⟩
  · rintro ⟨_, next, edge, _, member⟩
    exact ⟨next, edge, member⟩

theorem appended_support (head label : String) (before : List Atom) (edges : List (Nat × Nat)) (targets : List Nat) :
    {state | satisfaction head label state ∈ before ++ (produced edges targets).map (satisfaction head label)} =
      {state | satisfaction head label state ∈ before} ∪
        Mettapedia.Logic.CTLFixedPoints.pre (fun prior next => (prior, next) ∈ edges) {next | next ∈ targets} := by
  rw [← produced_support]
  ext state
  simp only [Set.mem_ofPred_eq, List.mem_append, Set.mem_union, List.mem_map]
  constructor
  · rintro (old | ⟨other, member, same⟩)
    · exact Or.inl old
    · exact Or.inr ((satisfaction_injective head label same) ▸ member)
  · rintro (old | member)
    · exact Or.inl old
    · exact Or.inr ⟨state, member, rfl⟩

theorem fresh_output_support (head label : String) (before : List Atom) (edges : List (Nat × Nat)) (targets : List Nat)
    (fresh : ∀ state, satisfaction head label state ∉ before) :
    {state | satisfaction head label state ∈ before ++ (produced edges targets).map (satisfaction head label)} =
      Mettapedia.Logic.CTLFixedPoints.pre (fun prior next => (prior, next) ∈ edges) {next | next ∈ targets} := by
  rw [appended_support]
  have empty : {state | satisfaction head label state ∈ before} = (∅ : Set Nat) := by
    ext state
    simp [fresh state]
  rw [empty, Set.empty_union]

private theorem binary_match (caller : Subst) (head firstSlot secondSlot : String) (ordinary : head ≠ "cons")
    (expected left right : Atom) (captured : Subst.lookup caller firstSlot = some expected)
    (fresh : Subst.lookup caller secondSlot = none) :
    matchValue caller (row head (.var firstSlot) (.var secondSlot)) (row head left right) =
      if left = expected then some ((secondSlot, right) :: caller) else none := by
  unfold row
  rw [matchValue_expression_of_not_cons _ _ _ (by
    intro name rest same
    exact ordinary (by simpa using (List.cons.inj same).1))]
  by_cases same : left = expected <;>
    simp [matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, captured, fresh, same]

theorem satisfaction_choices (caller : Subst) (head : String) (names : Names) (ordinary : head ≠ "cons")
    (label : String) (rows : List (String × Nat))
    (captured : Subst.lookup caller names.input = some (.symbol label)) (fresh : Subst.lookup caller names.next = none) :
    choices caller (satPattern head names) (rows.map (fun entry => satisfaction head entry.1 entry.2)) =
      (operand label rows).map (fun state => (names.next, number state) :: caller) := by
  simp only [choices, scan_bindings, List.filterMap_map, operand, List.map_filterMap]
  congr 1
  funext entry
  by_cases same : entry.1 = label <;>
    simp [satisfaction, satPattern,
      binary_match caller head names.input names.next ordinary _ _ _ captured fresh, same]

theorem reverse_choices (caller : Subst) (head : String) (names : Names) (ordinary : head ≠ "cons")
    (next : Nat) (edges : List (Nat × Nat))
    (captured : Subst.lookup caller names.next = some (number next)) (fresh : Subst.lookup caller names.prior = none) :
    choices caller (reversePattern head names) (edges.map (reverseEdge head)) =
      (predecessors edges next).map (fun prior => (names.prior, number prior) :: caller) := by
  simp only [choices, scan_bindings, List.filterMap_map, predecessors, List.map_filterMap]
  congr 1
  funext edge
  by_cases same : edge.2 = next <;>
    simp [reverseEdge, reversePattern,
      binary_match caller head names.next names.prior ordinary _ _ _ captured fresh, number, same]

def candidates (satHead reverseHead : String) (names : Names) (caller : Subst)
    (satRows graphRows : List Atom) : List Subst :=
  (choices caller (satPattern satHead names) satRows).flatMap
    (fun bindings => choices bindings (reversePattern reverseHead names) graphRows)

theorem rendered_candidates (satHead reverseHead : String) (names : Names) (caller : Subst)
    (satOrdinary : satHead ≠ "cons") (reverseOrdinary : reverseHead ≠ "cons")
    (inputLabel outputLabel : String) (satRows : List (String × Nat)) (edges : List (Nat × Nat))
    (inputRead : Subst.lookup caller names.input = some (.symbol inputLabel))
    (outputRead : Subst.lookup caller names.output = some (.symbol outputLabel))
    (nextFresh : Subst.lookup caller names.next = none) (priorFresh : Subst.lookup caller names.prior = none) :
    (candidates satHead reverseHead names caller (satRows.map (fun entry => satisfaction satHead entry.1 entry.2))
      (edges.map (reverseEdge reverseHead))).map (fun bindings => applySubst bindings (template satHead names)) =
      (produced edges (operand inputLabel satRows)).map (satisfaction satHead outputLabel) := by
  have separated := names.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at separated
  have inner (next : Nat) : choices ((names.next, number next) :: caller) (reversePattern reverseHead names)
      (edges.map (reverseEdge reverseHead)) =
      (predecessors edges next).map (fun prior => (names.prior, number prior) :: (names.next, number next) :: caller) := by
    apply reverse_choices _ reverseHead names reverseOrdinary next edges (by simp [Subst.lookup])
    simpa [Subst.lookup, Ne.symm separated.2.2.2] using priorFresh
  have rendered (next prior : Nat) :
      applySubst ((names.prior, number prior) :: (names.next, number next) :: caller) (template satHead names) =
        satisfaction satHead outputLabel prior := by
    have readOutput : Subst.lookup ((names.prior, number prior) :: (names.next, number next) :: caller) names.output =
        some (.symbol outputLabel) := by
      simpa [Subst.lookup, Ne.symm separated.2.2.1.1, Ne.symm separated.2.2.1.2] using outputRead
    simp only [applySubst, applySubst.applySubstList, template, row, satisfaction, readOutput, Option.getD_some]
    simp [Subst.lookup]
  unfold candidates
  rw [satisfaction_choices caller satHead names satOrdinary inputLabel satRows inputRead nextFresh]
  simp only [List.flatMap_map]
  simp_rw [inner]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  simp_rw [rendered]
  simp only [produced, List.map_flatMap]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageSource
