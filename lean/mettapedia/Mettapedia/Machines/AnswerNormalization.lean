import Mettapedia.Machines.DemandSummary
import Mettapedia.Machines.Cursor.ListCells

/-!
# Answer normalization behind quotation and callable boundaries

The reference operation first removes the private list carrier at the root,
then recognizes quotation or a suspended callable, and only then normalizes
children. A carrier can expose a quotation, so an unconditional children-first
fold is not this operation.

`ViewGraph` records source terms and their immediate, structurally checked
normalization dependencies. Its contract contains no normalized results. The
existing memo evaluator is proved equal to the independent fuel-indexed tree
operation, for several roots sharing a single cache. Fuel exhaustion is explicit;
the graph's rank supplies sufficient fuel, rather than imposing a language bound.

Bindings have already been applied. A graph and its interpretation stay fixed
for a cache session. The results do not justify memoizing an unresolved root,
reusing an arena address after reset, or treating quoted payloads as collector-free.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AnswerNormalization

open Cursor.ListCells (Tm)

/-- Symbol identities are parameters of the language interpretation. -/
structure Vocabulary where
  quote : Nat
  lam : Nat
  marker : Nat
  nullary : Nat
  partialSymbol : Nat
  cons : Nat
  deriving DecidableEq, Repr

/-- Only the tail spine is opened here. Heads are neither interpreted nor copied. -/
def splitSpine : Tm → List Tm × Tm
  | .cell head tail =>
      let following := splitSpine tail
      (head :: following.1, following.2)
  | other => ([], other)

def authoredCons (vocabulary : Vocabulary) (head tail : Tm) : Tm :=
  .expr [.sym vocabulary.cons, head, tail]

def assembleSpine (vocabulary : Vocabulary) (heads : List Tm) (tail : Tm) : Tm :=
  match tail with
  | .expr children => .expr (heads ++ children)
  | _ => heads.foldr (authoredCons vocabulary) tail

/-- The one-root list-carrier operation, before any opacity decision. -/
def shallow (vocabulary : Vocabulary) (source : Tm) : Tm :=
  let parts := splitSpine source
  assembleSpine vocabulary parts.1 parts.2

/-- These are syntax-shape tests, including the arity of suspended callables. -/
def isOpaque (vocabulary : Vocabulary) : Tm → Bool
  | .expr (.sym head :: arguments) =>
      decide (head = vocabulary.quote) ||
      (match arguments with
       | [.sym marker, _] => decide (head = vocabulary.lam ∧ marker = vocabulary.marker)
       | _ => false) ||
      (match arguments with
       | [_] => decide (head = vocabulary.nullary)
       | _ => false) ||
      (match arguments with
       | [_, .expr _] => decide (head = vocabulary.partialSymbol)
       | _ => false)
  | _ => false

inductive View where
  | keep (value : Tm)
  | descend (children : List Tm)
  deriving Repr

/-- Opaque payloads have no normalization dependencies. They still contain
physical references that a collector may have to trace. -/
def expose (vocabulary : Vocabulary) (source : Tm) : View :=
  let value := shallow vocabulary source
  match value with
  | .expr [] => .keep value
  | .expr children => if isOpaque vocabulary value then .keep value else .descend children
  | _ => .keep value

def View.reassemble : View → Tm
  | .keep value => value
  | .descend children => .expr children

theorem expose_reassembles (vocabulary : Vocabulary) (source : Tm) :
    (expose vocabulary source).reassemble = shallow vocabulary source := by
  unfold expose
  cases value : shallow vocabulary source with
  | sym symbol => rfl
  | var name => rfl
  | tag => rfl
  | expr children =>
      cases children with
      | nil => rfl
      | cons head rest => dsimp only; split <;> rfl

theorem splitSpine_of_not_cell (source : Tm) (notCell : ¬ source.IsCell) :
    splitSpine source = ([], source) := by
  unfold splitSpine
  split
  · exact False.elim (notCell ⟨_, _, rfl⟩)
  · rfl

theorem shallow_tagFree (vocabulary : Vocabulary) {source : Tm}
    (free : source.TagFree) : shallow vocabulary source = source := by
  rw [shallow, splitSpine_of_not_cell source free.not_isCell]
  cases source <;> rfl

/-- Independent tree semantics. Exhaustion is `none`, never an unchanged value. -/
def normalize (vocabulary : Vocabulary) : Nat → Tm → Option Tm
  | 0, _ => none
  | fuel + 1, source =>
      match expose vocabulary source with
      | .keep value => some value
      | .descend children => (children.mapM (normalize vocabulary fuel)).map Tm.expr

theorem splitSpine_cell (head tail : Tm) :
    splitSpine (.cell head tail) =
      (head :: (splitSpine tail).1, (splitSpine tail).2) := rfl

theorem shallow_closed_spine (vocabulary : Vocabulary) (heads children : List Tm) :
    assembleSpine vocabulary heads (.expr children) = .expr (heads ++ children) := rfl

theorem assembleSpine_append (vocabulary : Vocabulary) (left right : List Tm)
    (tail : Tm) (notExpression : ∀ children, tail ≠ .expr children) :
    assembleSpine vocabulary (left ++ right) tail =
      left.foldr (authoredCons vocabulary) (assembleSpine vocabulary right tail) := by
  cases tail <;> simp_all [assembleSpine, List.foldr_append]

theorem normalize_keep (vocabulary : Vocabulary) (source value : Tm)
    (view : expose vocabulary source = .keep value) (fuel : Nat) :
    normalize vocabulary (fuel + 1) source = some value := by
  simp [normalize, view]

theorem normalize_descend (vocabulary : Vocabulary) (source : Tm) (children : List Tm)
    (view : expose vocabulary source = .descend children) (fuel : Nat) :
    normalize vocabulary (fuel + 1) source =
      (children.mapM (normalize vocabulary fuel)).map Tm.expr := by
  simp [normalize, view]

private theorem mapM_some_of_pointwise {A B : Type} (xs : List A)
    (step : A → Option B) (value : A → B)
    (each : ∀ x ∈ xs, step x = some (value x)) :
    xs.mapM step = some (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, List.map_cons]
      rw [each x (by simp), ih (fun y hy => each y (by simp [hy]))]
      rfl

/-- A finite graph supplies just the immediate view decomposition. Checking
this contract does not run normalization or compare normalized results. -/
structure ViewGraph (vocabulary : Vocabulary) where
  source : Nat → Tm
  children : (i : Nat) → List (Fin i)
  keep_children : ∀ i value,
    expose vocabulary (source i) = .keep value → children i = []
  descend_children : ∀ i terms,
    expose vocabulary (source i) = .descend terms →
      (children i).map (fun child => source child.val) = terms

namespace ViewGraph

variable {vocabulary : Vocabulary}

def graph (view : ViewGraph vocabulary) : DemandSummary.Graph (Option Tm) where
  label i := match expose vocabulary (view.source i) with
    | .keep value => some value
    | .descend _ => none
  children := view.children

def algebra : Option Tm → List Tm → Tm
  | some value, _ => value
  | none, children => .expr children

/-- Rank supplies sufficient tree fuel. The proof uses only the immediate
source decomposition; cached values occur in neither its assumptions nor the
reference operation. -/
theorem reference_eq_eager (view : ViewGraph vocabulary) (fuel root : Nat)
    (within : root < fuel) :
    normalize vocabulary fuel (view.source root) =
      some (DemandSummary.eager view.graph algebra root) := by
  induction fuel generalizing root with
  | zero => omega
  | succ fuel ih =>
      rw [normalize, DemandSummary.eager]
      cases exposed : expose vocabulary (view.source root) with
      | keep value => simp [graph, exposed, algebra]
      | descend terms =>
          simp only [graph, exposed, algebra]
          rw [← view.descend_children root terms exposed]
          rw [List.mapM_map]
          simp only [Function.comp_def]
          rw [mapM_some_of_pointwise (view.children root)
            (fun child => normalize vocabulary fuel (view.source child.val))
            (fun child => DemandSummary.eager view.graph algebra child.val) (by
              intro child _
              apply ih
              have := child.isLt
              omega)]
          rfl

/-- A sound absence-of-private-tag fact licenses the complete identity
shortcut. Unknown facts do not satisfy this premise. -/
theorem eager_tagFree (view : ViewGraph vocabulary) (root : Nat)
    (free : (view.source root).TagFree) :
    DemandSummary.eager view.graph algebra root = view.source root := by
  induction root using Nat.strong_induction_on with
  | h root ih =>
      have reconstructed := expose_reassembles vocabulary (view.source root)
      rw [shallow_tagFree vocabulary free] at reconstructed
      rw [DemandSummary.eager]
      cases exposed : expose vocabulary (view.source root) with
      | keep value =>
          simpa [exposed, View.reassemble, graph, algebra] using reconstructed
      | descend terms =>
          simp only [exposed, View.reassemble] at reconstructed
          have freeTerms : ∀ term ∈ terms, term.TagFree := by
            rw [← reconstructed] at free
            cases free with
            | expr _ each => exact each
          simp only [graph, exposed, algebra]
          calc
            Tm.expr ((view.children root).map
                (fun child => DemandSummary.eager view.graph algebra child.val)) =
                Tm.expr ((view.children root).map (fun child => view.source child.val)) := by
              congr 1
              apply List.map_congr_left
              intro child member
              apply ih child.val child.isLt
              apply freeTerms
              rw [← view.descend_children root terms exposed]
              exact List.mem_map.mpr ⟨child, member, rfl⟩
            _ = view.source root := by
              rw [view.descend_children root terms exposed]
              exact reconstructed

def run (view : ViewGraph vocabulary) (roots : List Nat)
    (cache : DemandSummary.Cache Tm) : DemandSummary.Result (List Tm) Tm :=
  DemandSummary.sequence roots (DemandSummary.demand view.graph algebra) cache

/-- One fixed resolved graph, any ordered list of roots, and one shared cache.
Output multiplicities and order remain those of the requested roots. -/
theorem run_valid (view : ViewGraph vocabulary) (roots : List Nat) (bound : Nat)
    (within : ∀ root ∈ roots, root < bound) (cache : DemandSummary.Cache Tm)
    (sound : DemandSummary.Sound view.graph algebra cache) :
    DemandSummary.Valid view.graph algebra cache (view.run roots cache)
      (roots.map (DemandSummary.eager view.graph algebra)) bound := by
  apply DemandSummary.sequence_valid
  · intro root member initial valid
    have one := DemandSummary.demand_valid view.graph algebra root initial valid
    refine { one with bounded := ?_ }
    intro node computed
    have := one.bounded node computed
    have := within root member
    omega
  · exact sound

/-- Equality with independently executed tree normalization, including the
fact that the chosen rank is sufficient for every root. -/
theorem run_matches_reference (view : ViewGraph vocabulary) (roots : List Nat) (bound : Nat)
    (within : ∀ root ∈ roots, root < bound) (cache : DemandSummary.Cache Tm)
    (sound : DemandSummary.Sound view.graph algebra cache) :
    roots.mapM (fun root => normalize vocabulary bound (view.source root)) =
      some (view.run roots cache).value := by
  rw [(view.run_valid roots bound within cache sound).value_eq]
  exact mapM_some_of_pointwise roots _ _
    (fun root member => view.reference_eq_eager bound root (within root member))

theorem run_computes_each_node_once (view : ViewGraph vocabulary)
    (roots : List Nat) (bound : Nat) (within : ∀ root ∈ roots, root < bound)
    (cache : DemandSummary.Cache Tm) (sound : DemandSummary.Sound view.graph algebra cache) :
    (view.run roots cache).computed.Nodup :=
  (view.run_valid roots bound within cache sound).nodup

theorem run_preserves_cache (view : ViewGraph vocabulary)
    (roots : List Nat) (bound : Nat) (within : ∀ root ∈ roots, root < bound)
    (cache : DemandSummary.Cache Tm) (sound : DemandSummary.Sound view.graph algebra cache) :
    DemandSummary.Extends cache (view.run roots cache).cache :=
  (view.run_valid roots bound within cache sound).preserves

/-- Normalization requests are bounded by the retained observation graph,
including duplicate child slots and requested root occurrences. Opening list
spines and retaining opaque payload graphs are separately charged operations. -/
theorem run_requests_le_reachable_edges (view : ViewGraph vocabulary)
    (roots : List Nat) (cache : DemandSummary.Cache Tm)
    (sound : DemandSummary.Sound view.graph algebra cache) :
    DemandSummary.sequenceRequests roots (DemandSummary.demand view.graph algebra)
        (DemandSummary.demandRequests view.graph algebra) cache ≤
      roots.length + ∑ node ∈ roots.toFinset.biUnion (DemandSummary.reachable view.graph),
        (view.graph.children node).length :=
  DemandSummary.sequenceRequests_le_reachable_edges view.graph algebra roots cache sound

end ViewGraph

namespace Examples

def symbols : Vocabulary := ⟨0, 1, 2, 3, 4, 5⟩
def item : Tm := .sym 10
def wrapper : Tm := .sym 11
def carrier : Tm := .cell item (.expr [])
def revealedQuote : Tm := .cell (.sym symbols.quote) (.expr [carrier])

/-- Opening the outer carrier discovers quotation before interpreting its payload. -/
theorem quotation_revealed_by_carrier :
    normalize symbols 1 revealedQuote = some (.expr [.sym symbols.quote, carrier]) := rfl

theorem plain_wrapper_normalizes_payload :
    normalize symbols 3 (.expr [wrapper, carrier]) =
      some (.expr [wrapper, .expr [item]]) := rfl

theorem suspended_lambda_keeps_payload :
    normalize symbols 1 (.expr [.sym symbols.lam, .sym symbols.marker, carrier]) =
      some (.expr [.sym symbols.lam, .sym symbols.marker, carrier]) := rfl

theorem suspended_nullary_keeps_payload :
    normalize symbols 1 (.expr [.sym symbols.nullary, carrier]) =
      some (.expr [.sym symbols.nullary, carrier]) := rfl

theorem suspended_partial_keeps_payload :
    normalize symbols 1 (.expr [.sym symbols.partialSymbol, wrapper, carrier]) =
      some (.expr [.sym symbols.partialSymbol, wrapper, carrier]) := rfl

theorem open_tail_becomes_authored_cons :
    normalize symbols 2 (.cell item (.var 7)) =
      some (.expr [.sym symbols.cons, item, .var 7]) := rfl

/-- Insufficient fuel does not silently claim successful normalization. -/
theorem exhaustion_is_explicit :
    normalize symbols 1 (.expr [wrapper, carrier]) = none := rfl

/-- Unconditional recursive list flattening crosses the quotation boundary. -/
theorem children_first_changes_quoted_payload :
    Cursor.ListCells.Tm.flat revealedQuote ≠ .expr [.sym symbols.quote, carrier] := by
  intro wrong
  cases wrong

/-- A resolved graph with shared payloads and a carrier exposing quotation.
The final case permits arbitrarily many layers of binary sharing. -/
def source : Nat → Tm
  | 0 => item
  | 1 => wrapper
  | 2 => carrier
  | 3 => .expr [wrapper, carrier]
  | 4 => revealedQuote
  | 5 => .expr [source 3, source 4]
  | n + 6 => .expr [source (n + 5), source (n + 5)]

def dependencies : (i : Nat) → List (Fin i)
  | 0 => []
  | 1 => []
  | 2 => [⟨0, by decide⟩]
  | 3 => [⟨1, by decide⟩, ⟨2, by decide⟩]
  | 4 => []
  | 5 => [⟨3, by decide⟩, ⟨4, by decide⟩]
  | n + 6 => [⟨n + 5, by omega⟩, ⟨n + 5, by omega⟩]

theorem source_after_five_is_expression (n : Nat) :
    ∃ children, source (n + 5) = .expr children := by
  cases n with
  | zero => exact ⟨_, rfl⟩
  | succ n => exact ⟨_, rfl⟩

def view : ViewGraph symbols where
  source := source
  children := dependencies
  keep_children := by
    intro i value kept
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => cases kept
    | 3 => cases kept
    | 4 => rfl
    | 5 => cases kept
    | n + 6 =>
        obtain ⟨children, shape⟩ := source_after_five_is_expression n
        simp only [source, shape, expose, shallow, splitSpine, assembleSpine,
          List.nil_append, isOpaque, Bool.false_eq_true, ↓reduceIte] at kept
        cases kept
  descend_children := by
    intro i terms opened
    match i with
    | 0 => cases opened
    | 1 => cases opened
    | 2 => cases opened; rfl
    | 3 => cases opened; rfl
    | 4 => cases opened
    | 5 => cases opened; rfl
    | n + 6 =>
        obtain ⟨children, shape⟩ := source_after_five_is_expression n
        simp only [source, shape, expose, shallow, splitSpine, assembleSpine,
          List.nil_append, isOpaque, Bool.false_eq_true, ↓reduceIte,
          View.descend.injEq] at opened
        rw [← opened]
        simp only [dependencies, List.map_cons, List.map_nil, shape]

private theorem eager_plain :
    DemandSummary.eager view.graph ViewGraph.algebra 3 =
      .expr [wrapper, .expr [item]] := by
  have exact := view.reference_eq_eager 4 3 (by decide)
  change some (Tm.expr [wrapper, .expr [item]]) = _ at exact
  exact (Option.some.inj exact).symm

private theorem eager_quoted :
    DemandSummary.eager view.graph ViewGraph.algebra 4 =
      .expr [.sym symbols.quote, carrier] := by
  have exact := view.reference_eq_eager 5 4 (by decide)
  change some (Tm.expr [.sym symbols.quote, carrier]) = _ at exact
  exact (Option.some.inj exact).symm

theorem repeated_roots_preserve_occurrences :
    (view.run [3, 3] (fun _ => none)).value =
      [.expr [wrapper, .expr [item]], .expr [wrapper, .expr [item]]] := by
  have valid := view.run_valid [3, 3] 4 (by simp) (fun _ => none)
    (DemandSummary.empty_sound _ _)
  simpa only [List.map_cons, List.map_nil, eager_plain] using valid.value_eq

/-- The second root is an output occurrence, but contributes no new work. -/
theorem repeated_roots_compute_once :
    (view.run [3, 3] (fun _ => none)).computed =
      (view.run [3] (fun _ => none)).computed := by
  simp only [ViewGraph.run, DemandSummary.sequence, DemandSummary.demand_again,
    List.append_nil]

theorem shared_payload_has_distinct_opaque_observation :
    (view.run [3, 4] (fun _ => none)).value =
      [.expr [wrapper, .expr [item]], .expr [.sym symbols.quote, carrier]] := by
  have valid := view.run_valid [3, 4] 5 (by simp) (fun _ => none)
    (DemandSummary.empty_sound _ _)
  simpa only [List.map_cons, List.map_nil, eager_plain, eager_quoted] using valid.value_eq

theorem opaque_root_does_not_demand_payload :
    (view.run [4] (fun _ => none)).computed = [4] := by
  change (DemandSummary.demand view.graph ViewGraph.algebra 4 (fun _ => none)).computed ++
    [] = [4]
  rw [DemandSummary.demand]
  simp [ViewGraph.graph, view, dependencies, DemandSummary.sequence]

/-- Extensional equality of a previously normalized child does not license
using it inside an opaque parent's retained source payload. -/
theorem cached_payload_must_not_replace_quoted_source :
    (view.run [3, 4] (fun _ => none)).value ≠
      [.expr [wrapper, .expr [item]], .expr [.sym symbols.quote, .expr [item]]] := by
  rw [shared_payload_has_distinct_opaque_observation]
  intro wrong
  cases wrong

end Examples

end Mettapedia.Machines.AnswerNormalization
