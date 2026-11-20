import Mettapedia.Machines.Cursor.ListCells
import Mettapedia.Data.List.OrderedOccurrenceCursor
import Mettapedia.Data.List.OrderedPrefilter
import Mettapedia.Machines.OrderedDependencyOverlay

/-!
# Candidate and occurrence projections for indexed matching

A structural index must not read an internal list cell as a three-element
expression. Closed spines can be indexed through their flat reading. If a
partial or nested cell remains, offering every occurrence is complete; the
original pattern still decides unification. This projection never changes
variables or merges equal occurrences.

Sparse candidates retain their original coordinates through nested logical
views. The ordered projection is compared with `OrderedDependencyOverlay`'s
independent full-row observation, then instantiated for declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MatchIndexProjection

open Cursor.ListCells
open Tm (TagFree)

mutual
/-- Constructor summaries may establish this predicate without a term walk. -/
def structural : Tm → Bool
  | .sym _ | .var _ => true
  | .tag => false
  | .expr xs => structuralList xs
def structuralList : List Tm → Bool
  | [] => true
  | x :: xs => structural x && structuralList xs
end

theorem structuralList_eq_all (xs : List Tm) : structuralList xs = xs.all structural := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [structuralList, ih]

theorem structural_tagFree {t : Tm} (h : structural t = true) : TagFree t := by
  induction t using Tm.induction with
  | sym s => exact .sym s
  | var v => exact .var v
  | tag => cases h
  | expr xs ih =>
    exact .expr xs fun x hx => ih x hx ((List.all_eq_true.mp (by simpa [structural, structuralList_eq_all] using h)) x hx)

/-- `none` requests the complete occurrence frontier. -/
def project (pattern : Tm) : Option Tm :=
  if structural pattern then some pattern
  else match pattern.closedElems with
    | none => none
    | some xs => if structural (.expr xs) then some (.expr xs) else none

theorem project_denote {pattern query : Tm} (h : project pattern = some query) :
    query.denote = pattern.denote := by
  unfold project at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · rename_i xs hx
      split at h
      · rename_i hs
        cases h
        rw [(structural_tagFree hs).denote_expr]
        exact Tm.denoteList_closedElems hx
      · cases h

/-- A concrete index query retains exactly the original unifiers. -/
theorem project_unifies {pattern query : Tm} (h : project pattern = some query)
    (θ : ℕ → PT) (row : Tm) : Unifies θ query row ↔ Unifies θ pattern row := by
  unfold Unifies
  rw [project_denote h]

/-- The semantic requirement on candidates, before exact matching. -/
def Candidate (θ : ℕ → PT) (query : Option Tm) (row : Tm) : Prop :=
  match query with
  | none => True
  | some q => Unifies θ q row

theorem candidate_complete (pattern row : Tm) (θ : ℕ → PT)
    (h : Unifies θ pattern row) : Candidate θ (project pattern) row := by
  cases hp : project pattern with
  | none => trivial
  | some q => exact (project_unifies hp θ row).mpr h

export Mettapedia.Data.List.OrderedPrefilter (filter_candidates)

/-- Filtering the candidate frontier and then unifying retains the exact
occurrence list, including duplicates and its original order. -/
theorem filter_occurrences (pattern : Tm) (θ : ℕ → PT) (rows : List Tm) :
    (rows.filter (fun row => by classical exact decide (Candidate θ (project pattern) row))).filter
        (fun row => by classical exact decide (Unifies θ pattern row)) =
      rows.filter (fun row => by classical exact decide (Unifies θ pattern row)) := by
  classical
  apply filter_candidates
  intro row accepted
  simpa only [decide_eq_true_eq] using
    candidate_complete pattern row θ (of_decide_eq_true accepted)

/-- A closed cell exposes its logical list length to the index. -/
example : project (.cell (.sym 1) (.expr [.var 0, .var 1])) =
    some (.expr [.sym 1, .var 0, .var 1]) := rfl

/-- A partial tail must not be mistaken for a rigid three-element list. -/
example : project (.cell (.sym 1) (.var 0)) = none := rfl

/-- A nested cell uses the complete frontier until the index supports it. -/
example : project (.expr [.sym 2, .cell (.sym 1) (.expr [])]) = none := rfl

/-- Structural equality of the physical representations can reject a real
match. This is a negative control for indexing the carrier unchanged. -/
example :
    Unifies PT.var (.cell (.sym 1) (.expr [.sym 2])) (.expr [.sym 1, .sym 2]) ∧
    (Tm.cell (.sym 1) (.expr [.sym 2])).subst Tm.var ≠
      (Tm.expr [.sym 1, .sym 2]).subst Tm.var := by
  constructor
  · exact ⟨_, _, rfl, rfl, rfl⟩
  · intro h
    simp [Tm.subst, Tm.substList] at h


/-- Enumerating match environments through a host and resuming the body for
each is the same occurrence-preserving bind as running the body per row.
The constant host result does not replace the environment in this protocol. -/
theorem host_match_bind {Row Env Answer : Type} (rows : List Row)
    (matchRow : Row → List Env) (body : Env → List Answer) :
    (rows.flatMap matchRow).flatMap body =
      rows.flatMap (fun row => (matchRow row).flatMap body) := by
  exact List.flatMap_assoc ..

namespace Ordered

open Mettapedia.Data.List.OrderedOccurrenceCursor
open OrderedDependencyOverlay (Layer)

/-- Sparse candidate rows retain coordinates in the complete local source.
The size counts all rows, including rows absent from the candidate frontier. -/
@[ext] structure Frontier (Entry : Type*) where
  size : Nat
  rows : List (Entry × Nat)
  deriving DecidableEq, Repr

variable {Entry : Type*}

def localIndex (candidate : Entry → Bool) (rows : List Entry) : Frontier Entry :=
  ⟨rows.length, rows.zipIdx.filter fun row => candidate row.1⟩

def append (first second : Frontier Entry) : Frontier Entry :=
  ⟨first.size + second.size,
    first.rows ++ second.rows.map (Prod.map id (· + first.size))⟩

theorem local_append (candidate : Entry → Bool) (first second : List Entry) :
    localIndex candidate (first ++ second) = append (localIndex candidate first) (localIndex candidate second) := by
  apply Frontier.ext
  · simp [localIndex, append]
  · simp only [localIndex, append, List.zipIdx_append, Nat.zero_add, List.filter_append]
    congr 1
    have shifted := List.map_snd_add_zipIdx_eq_zipIdx (l := second) (n := first.length) (k := 0)
    simp only [Nat.add_zero] at shifted
    rw [← shifted]
    simp [List.filter_map, Function.comp_def]

theorem local_rows (candidate : Entry → Bool) (rows : List Entry) :
    (localIndex candidate rows).rows.map Prod.fst = rows.filter candidate := by
  simpa only [localIndex, List.zipIdx_map_fst, Function.comp_def] using
    (List.filter_map (f := Prod.fst) (p := candidate) (l := rows.zipIdx)).symm

def retained (layer : Layer Entry) (position : Nat) : Bool :=
  decide (position < layer.ceiling ∧ position ∉ layer.hidden)

/-- Independent logical overlays use bounded prefix coordinates before
deletion. The index projection uses exactly that same visibility gate. -/
theorem layer_view (layer : Layer Entry) (parent : List Entry) :
    layer.view parent = Positions.visible (retained layer) parent ++ layer.own := by
  have prefixRows := Positions.zipIdx_filter_prefix parent layer.ceiling 0
  simp only [Nat.zero_add] at prefixRows
  unfold Layer.view Positions.visible
  rw [← prefixRows]
  congr 1
  generalize parent.zipIdx = rows
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      by_cases bounded : row.2 < layer.ceiling <;> by_cases hidden : row.2 ∈ layer.hidden <;>
        simp [retained, bounded, hidden, ih]

/-- Project the inherited indexed rows first, then append the local indexed
suffix at the number of visible inherited rows. -/
def projectLayer (candidate : Entry → Bool) (layer : Layer Entry)
    (parent : Frontier Entry) : Frontier Entry :=
  append ⟨Positions.rankBefore (retained layer) parent.size,
      Positions.project (retained layer) parent.rows⟩ (localIndex candidate layer.own)

theorem projectLayer_exact (candidate : Entry → Bool) (layer : Layer Entry)
    (parent : List Entry) :
    projectLayer candidate layer (localIndex candidate parent) = localIndex candidate (layer.view parent) := by
  rw [layer_view, local_append]
  unfold projectLayer
  congr 1
  apply Frontier.ext
  · exact (Positions.visible_length (retained layer) parent).symm
  · exact Positions.project_candidates (retained layer) candidate parent

def projectLayers (candidate : Entry → Bool) : List (Layer Entry) → Frontier Entry → Frontier Entry
  | [], parent => parent
  | layer :: rest, parent => projectLayers candidate rest (projectLayer candidate layer parent)

/-- Nested filters compose by translating each surviving source coordinate
before the next layer reads it. No candidate-list coordinate is substituted. -/
theorem projectLayers_exact (candidate : Entry → Bool) (layers : List (Layer Entry))
    (parent : List Entry) :
    projectLayers candidate layers (localIndex candidate parent) =
      localIndex candidate (layers.foldl (fun own layer => layer.view own) parent) := by
  induction layers generalizing parent with
  | nil => rfl
  | cons layer rest ih =>
      simp only [projectLayers, List.foldl_cons, projectLayer_exact]
      exact ih (layer.view parent)

def select {Source : Type*} (candidate : Entry → Bool) (layers : List (Layer Entry))
    (parts : List Entry × List (Source × List Entry)) : List Entry :=
  (projectLayers candidate layers (localIndex candidate parts.1)).rows.map Prod.fst ++
    parts.2.flatMap fun source => (localIndex candidate source.2).rows.map Prod.fst

/-- Local layers never mask or duplicate dependency own slices. Their order
is appended once, as in the maintained independent module observation. -/
theorem select_exact {size : Nat} (candidate : Entry → Bool) (layers : List (Layer Entry))
    (parts : List Entry × List (Fin size × List Entry)) :
    select candidate layers parts = (OrderedDependencyOverlay.observe layers parts).filter candidate := by
  simp only [select, projectLayers_exact, local_rows, OrderedDependencyOverlay.observe,
    List.filter_append, List.filter_flatMap]

/-- A root reader can request its local suffix before the imported prefix.
The comparison is made in root logical coordinates, after nested projection. -/
theorem own_before_imported (candidate : Entry → Bool) (rows : List Entry) (imported : Nat) :
    (((localIndex candidate rows).rows.filter fun row => decide (imported ≤ row.2)).map Prod.fst ++
      ((localIndex candidate rows).rows.filter fun row => decide (row.2 < imported)).map Prod.fst) =
        (rows.drop imported ++ rows.take imported).filter candidate := by
  have prefixRows := Positions.zipIdx_filter_prefix rows imported 0
  have suffixRows := Positions.zipIdx_filter_suffix rows imported 0
  simp only [Nat.zero_add] at prefixRows suffixRows
  simp only [localIndex, List.filter_append]
  rw [List.filter_comm (p := fun row : Entry × Nat => decide (imported ≤ row.2))
      (fun row : Entry × Nat => candidate row.1) rows.zipIdx,
    List.filter_comm (p := fun row : Entry × Nat => decide (row.2 < imported))
      (fun row : Entry × Nat => candidate row.1) rows.zipIdx]
  rw [prefixRows, suffixRows]
  have erase (source : List Entry) (start : Nat) :
      ((source.zipIdx start).filter fun row => candidate row.1).map Prod.fst =
        source.filter candidate := by
    simpa only [List.zipIdx_map_fst, Function.comp_def] using
      (List.filter_map (f := Prod.fst) (p := candidate) (l := source.zipIdx start)).symm
  exact congrArg₂ List.append (erase (rows.drop imported) imported) (erase (rows.take imported) 0)

end Ordered

namespace Declaration

open Mettapedia.Data.List.OrderedOccurrenceCursor (Occurrence)

/-- A known rigid head can exclude a declaration. Unknown and variable heads
retain candidates, including cases in which substitution creates a head. -/
def headSymbol : PT → Option Nat
  | .atom symbol => some symbol
  | .cons (.atom symbol) _ => some symbol
  | _ => none

theorem headSymbol_subst (θ : Nat → PT) (value : PT) (head : Nat)
    (known : headSymbol value = some head) : headSymbol (value.subst θ) = some head := by
  cases value with
  | atom symbol => simpa only [PT.subst] using known
  | var name => cases known
  | nil => cases known
  | cons first rest =>
      cases first <;> simp_all [headSymbol, PT.subst]

def subjectMatches (θ : Nat → PT) (query : Tm) (subject : PT) : Bool :=
  match query.denote with
  | none => false
  | some pattern => decide (pattern.subst θ = subject.subst θ)

/-- The maintained cell projection supplies the index's query reading.
A declined projection leaves the entire declaration frontier available. -/
def possible (query : Tm) (subject : PT) : Bool :=
  match project query with
  | none => true
  | some pattern => match pattern.denote.bind headSymbol, headSymbol subject with
    | some first, some second => decide (first = second)
    | _, _ => true

theorem matches_possible (θ : Nat → PT) (query : Tm) (subject : PT)
    (matched : subjectMatches θ query subject = true) : possible query subject = true := by
  cases projected : project query with
  | none => simp [possible, projected]
  | some pattern =>
      have reading := project_denote projected
      simp only [possible, projected, reading]
      cases source : query.denote with
      | none => simp [subjectMatches, source] at matched
      | some value =>
          have equality : value.subst θ = subject.subst θ := by
            simpa only [subjectMatches, source, decide_eq_true_eq] using matched
          simp only [Option.bind_some]
          cases first : headSymbol value with
          | none => rfl
          | some head =>
              cases second : headSymbol subject with
              | none => rfl
              | some other =>
                  have same := congrArg headSymbol equality
                  rw [headSymbol_subst θ value head first,
                    headSymbol_subst θ subject other second] at same
                  simpa only [Option.some.injEq, decide_eq_true_eq] using same

def subjectOf (marker : Nat) : PT → Option PT
  | .cons (.atom tag) (.cons subject (.cons _ .nil)) =>
      if tag = marker then some subject else none
  | _ => none

def accepts (marker : Nat) (θ : Nat → PT) (query : Tm) (row : Occurrence PT) : Bool :=
  match subjectOf marker row.value with
  | none => false
  | some subject => subjectMatches θ query subject

def candidate (marker : Nat) (query : Tm) (row : Occurrence PT) : Bool :=
  match subjectOf marker row.value with
  | none => false
  | some subject => possible query subject

theorem accepts_candidate (marker : Nat) (θ : Nat → PT) (query : Tm) (row : Occurrence PT)
    (accepted : accepts marker θ query row = true) : candidate marker query row = true := by
  cases declaration : subjectOf marker row.value with
  | none => simp [accepts, declaration] at accepted
  | some subject =>
      simpa only [candidate, declaration] using
        matches_possible θ query subject (by simpa only [accepts, declaration] using accepted)

/-- Filtering declarations and subjects after indexed nested visibility gives
the exact independent ordered occurrence observation. At identity substitution
the subject test is equality; the stronger statement also permits relational
subject instances without treating variables as rigid index heads. -/
theorem indexed_lookup_exact {size : Nat} (marker : Nat) (θ : Nat → PT) (query : Tm)
    (layers : List (OrderedDependencyOverlay.Layer (Occurrence PT)))
    (parts : List (Occurrence PT) × List (Fin size × List (Occurrence PT))) :
    (Ordered.select (candidate marker query) layers parts).filter (accepts marker θ query) =
      (OrderedDependencyOverlay.observe layers parts).filter (accepts marker θ query) := by
  rw [Ordered.select_exact]
  exact filter_candidates (candidate marker query) (accepts marker θ query)
    (accepts_candidate marker θ query) _

/-- The same selection law applies to the maintained module query loop,
using its existing segment and logical-observation correspondence. -/
theorem indexed_query_exact {size : Nat} (marker : Nat) (θ : Nat → PT) (query : Tm)
    (state : OrderedDependencyOverlay.State (Occurrence PT) size) :
    (Ordered.select (candidate marker query) state.layers
      (OrderedDependencyStore.segments state.store state.reader)).filter (accepts marker θ query) =
        (OrderedDependencyOverlay.query state).filter (accepts marker θ query) := by
  rw [OrderedDependencyOverlay.query_eq_view]
  exact indexed_lookup_exact marker θ query state.layers _

/-- Pure per-occurrence validation and answer enumeration receive the same
ordered occurrences, rather than one Boolean success or a deduplicated list.
A stateful fresh-name supply requires its own transport law. -/
theorem indexed_trials_exact {size : Nat} {Answer : Type*} (marker : Nat)
    (θ : Nat → PT) (query : Tm)
    (layers : List (OrderedDependencyOverlay.Layer (Occurrence PT)))
    (parts : List (Occurrence PT) × List (Fin size × List (Occurrence PT)))
    (trial : Occurrence PT → List Answer) :
    ((Ordered.select (candidate marker query) layers parts).filter (accepts marker θ query)).flatMap trial =
      ((OrderedDependencyOverlay.observe layers parts).filter (accepts marker θ query)).flatMap trial := by
  rw [indexed_lookup_exact]

namespace Controls

def annotation (identity : Nat) (subject type : PT) : Occurrence PT :=
  ⟨identity, .cons (.atom 90) (.cons subject (.cons type .nil))⟩

def first : Occurrence PT := annotation 1 (.atom 5) (.atom 7)
def duplicate : Occurrence PT := annotation 3 (.atom 5) (.atom 7)
def appended : Occurrence PT := annotation 4 (.atom 5) (.atom 7)
def outerLocal : Occurrence PT := annotation 5 (.atom 5) (.atom 8)
def imported : Occurrence PT := annotation 6 (.atom 5) (.atom 7)

def parent : List (Occurrence PT) :=
  [⟨0, .atom 99⟩, first, annotation 2 (.atom 6) (.atom 9), duplicate]

def inner : OrderedDependencyOverlay.Layer (Occurrence PT) := ⟨4, {1}, [appended]⟩
def outer : OrderedDependencyOverlay.Layer (Occurrence PT) := ⟨3, {1}, [outerLocal]⟩

def parts : List (Occurrence PT) × List (Fin 1 × List (Occurrence PT)) :=
  (parent, [(0, [imported])])

def lookup : List (Occurrence PT) :=
  (Ordered.select (candidate 90 (.sym 5)) [inner, outer] parts).filter
    (accepts 90 PT.var (.sym 5))

/-- Equal declarations retain separate identities. Nested parent masks do
not apply to the dependency own slice, which follows the local declarations. -/
theorem nested_declarations_keep_order_and_duplicates :
    lookup = [duplicate, outerLocal, imported] ∧
      lookup.map Occurrence.identity = [3, 5, 6] ∧
      duplicate.value = imported.value ∧ duplicate.identity ≠ imported.identity := by
  decide

/-- A native head chain keeps source positions 1 and 3. Applying removal 1
to its newly numbered candidate list instead would remove occurrence 3. -/
theorem removal_after_candidate_renumbering_is_wrong :
    (Ordered.projectLayer (candidate 90 (.sym 5)) inner
        (Ordered.localIndex (candidate 90 (.sym 5)) parent)).rows.map Prod.fst =
      [duplicate, appended] ∧
      inner.view (parent.filter (candidate 90 (.sym 5))) = [first, appended] ∧
      [duplicate, appended] ≠ [first, appended] := by
  decide

/-- The appended suffix starts after every visible inherited row, rather
than after just the candidate rows. This matters to the next layer's ceiling. -/
theorem local_suffix_uses_full_visible_offset :
    (Ordered.projectLayer (candidate 90 (.sym 5)) inner
      (Ordered.localIndex (candidate 90 (.sym 5)) parent)).rows =
        [(duplicate, 2), (appended, 3)] ∧
      (Ordered.projectLayers (candidate 90 (.sym 5)) [inner, outer]
        (Ordered.localIndex (candidate 90 (.sym 5)) parent)).rows =
        [(duplicate, 1), (outerLocal, 2)] := by
  decide

theorem deduplication_or_reordering_changes_lookup :
    (lookup.map Occurrence.value).eraseDups ≠ lookup.map Occurrence.value ∧
      lookup.reverse ≠ lookup := by
  decide

theorem own_declarations_precede_imported_prefix :
    let rows := [imported, duplicate, outerLocal]
    (((Ordered.localIndex (candidate 90 (.sym 5)) rows).rows.filter
          fun row => decide (1 ≤ row.2)).map Prod.fst ++
      ((Ordered.localIndex (candidate 90 (.sym 5)) rows).rows.filter
          fun row => decide (row.2 < 1)).map Prod.fst) =
        [duplicate, outerLocal, imported] := by
  decide

theorem head_exclusion_is_conservative :
    possible (.sym 5) (.atom 6) = false ∧
      possible (.sym 5) (.cons (.atom 5) .nil) = true ∧
      subjectMatches PT.var (.sym 5) (.cons (.atom 5) .nil) = false ∧
      subjectMatches (fun _ => .atom 5) (.sym 5) (.var 0) = true ∧
      possible (.sym 5) (.var 0) = true ∧
      subjectMatches PT.var (.cell (.sym 5) (.expr [])) (.cons (.atom 5) .nil) = true ∧
      possible (.cell (.sym 5) (.expr [])) (.cons (.atom 5) .nil) = true := by
  decide

end Controls

end Declaration

#print axioms filter_occurrences
#print axioms Ordered.layer_view
#print axioms Ordered.projectLayer_exact
#print axioms Ordered.projectLayers_exact
#print axioms Ordered.select_exact
#print axioms Ordered.own_before_imported
#print axioms Declaration.matches_possible
#print axioms Declaration.accepts_candidate
#print axioms Declaration.indexed_lookup_exact
#print axioms Declaration.indexed_query_exact
#print axioms Declaration.indexed_trials_exact
#print axioms Declaration.Controls.nested_declarations_keep_order_and_duplicates
#print axioms Declaration.Controls.removal_after_candidate_renumbering_is_wrong
#print axioms Declaration.Controls.local_suffix_uses_full_visible_offset
#print axioms Declaration.Controls.deduplication_or_reordering_changes_lookup
#print axioms Declaration.Controls.own_declarations_precede_imported_prefix
#print axioms Declaration.Controls.head_exclusion_is_conservative

/-- Replacing two environments by one successful Boolean loses answers. -/
example : ([1, 2] : List Nat).flatMap (fun n => [n + 10]) ≠
    [1].flatMap (fun n => [n + 10]) := by decide

end Mettapedia.Machines.MatchIndexProjection
