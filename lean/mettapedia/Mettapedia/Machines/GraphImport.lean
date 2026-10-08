import Mettapedia.Machines.DemandSummary
import Mettapedia.Machines.SubstitutionFold

/-!
# Importing shared terms under one fixed name interpretation

`DemandSummary` already supplies the executable memoized DAG fold and its
distinct-node accounting. This module connects that construction to ordinary
term substitution, rather than building a second cache framework.

The source graph is acyclic, with its rank as a termination witness. A fixed
import context supplies each name's image throughout one invocation.
Keeping that context fixed permits source-node memoization. Reusing the same
node-only cache with another context or freshening scope is unsound.

The results concern term denotation, algebra combinations and graph requests.
They do not prove C pointer relocation, allocation order, lifetime management,
or an effectful fresh-cell allocator correct.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.GraphImport

open SubstitutionFold (Term)

universe u v w

section Fusion

variable {Label : Type u} {Source : Type v} {Target : Type w}

/-- A homomorphism of the local node algebras commutes with unfolding the
whole ranked graph. The source and target folds are independently evaluated. -/
theorem eager_fusion (graph : DemandSummary.Graph Label)
    (source : Label → List Source → Source)
    (target : Label → List Target → Target) (transform : Source → Target)
    (homomorphism : ∀ label children,
      transform (source label children) = target label (children.map transform))
    (root : Nat) :
    transform (DemandSummary.eager graph source root) =
      DemandSummary.eager graph target root := by
  induction root using Nat.strong_induction_on with
  | h root ih =>
      rw [DemandSummary.eager, DemandSummary.eager, homomorphism, List.map_map]
      congr 1
      apply List.map_congr_left
      intro child _
      exact ih child.val child.isLt

end Fusion

section Terms

variable {V W L : Type u}

mutual
/-- Simultaneous substitution on ordinary trees, with no graph cache. -/
def substitute (image : V → Term W L) : Term V L → Term W L
  | .var name => image name
  | .leaf leaf => .leaf leaf
  | .expr children => .expr (substituteAll image children)

def substituteAll (image : V → Term W L) : List (Term V L) → List (Term W L)
  | [] => []
  | child :: rest => substitute image child :: substituteAll image rest
end

theorem substituteAll_eq_map (image : V → Term W L) (children : List (Term V L)) :
    substituteAll image children = children.map (substitute image) := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp [substituteAll, ih]

/-- A semantic dependency of tree substitution; repeated occurrences still
refer to the same source variable. -/
inductive HasVariable (name : V) : Term V L → Prop
  | here : HasVariable name (.var name)
  | child {term : Term V L} {children : List (Term V L)} :
      term ∈ children → HasVariable name term → HasVariable name (.expr children)

theorem substitute_congr (image other : V → Term W L) (term : Term V L)
    (agree : ∀ name, HasVariable name term → image name = other name) :
    substitute image term = substitute other term := by
  refine Term.rec
    (motive_1 := fun term =>
      (∀ name, HasVariable name term → image name = other name) →
      substitute image term = substitute other term)
    (motive_2 := fun children =>
      (∀ name term, term ∈ children → HasVariable name term → image name = other name) →
      substituteAll image children = substituteAll other children)
    ?_ ?_ ?_ ?_ ?_ term agree
  · intro name agree
    exact agree name .here
  · intro leaf _
    rfl
  · intro children ih agree
    apply congrArg Term.expr
    exact ih (fun name term member occurrence => agree name (.child member occurrence))
  · intro _
    rfl
  · intro child rest first following agree
    exact congrArg₂ List.cons
      (first (fun name occurrence => agree name child (by simp) occurrence))
      (following (fun name term member occurrence =>
        agree name term (by simp [member]) occurrence))

inductive Label (V L : Type u) where
  | var (name : V)
  | leaf (value : L)
  | expr

/-- The name interpretation includes the import mode and its stable
context. A name may denote an entire term rather than merely a name. -/
def algebra (image : V → Term W L) : Label V L → List (Term W L) → Term W L
  | .var name, _ => image name
  | .leaf value, _ => .leaf value
  | .expr, children => .expr children

/-- Independent source unfolding; variables remain source variables. -/
def unfold (graph : DemandSummary.Graph (Label V L)) (root : Nat) : Term V L :=
  match graph.label root with
  | .var name => .var name
  | .leaf value => .leaf value
  | .expr => .expr ((graph.children root).map fun child => unfold graph child.val)
termination_by root

theorem unfold_eq_eager (graph : DemandSummary.Graph (Label V L)) (root : Nat) :
    unfold graph root = DemandSummary.eager graph (algebra Term.var) root := by
  induction root using Nat.strong_induction_on with
  | h root ih =>
      rw [unfold, DemandSummary.eager]
      cases graph.label root with
      | var name => rfl
      | leaf value => rfl
      | expr =>
          simp only [algebra]
          congr 1
          apply List.map_congr_left
          intro child _
          exact ih child.val child.isLt

theorem substitution_algebra (image : V → Term W L)
    (label : Label V L) (children : List (Term V L)) :
    substitute image (algebra Term.var label children) =
      algebra image label (children.map (substitute image)) := by
  cases label <;> simp [algebra, substitute, substituteAll_eq_map]

/-- The semantic bridge: substituting in the unfolded source equals the
target graph fold under the same fixed interpretation of variables. -/
theorem substitution_unfold (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (root : Nat) :
    substitute image (unfold graph root) = DemandSummary.eager graph (algebra image) root := by
  rw [unfold_eq_eager]
  exact eager_fusion graph (algebra Term.var) (algebra image)
    (substitute image) (substitution_algebra image) root

/-- A fresh-variable table can grow while existing images remain valid.
Only variables on which a cached node depends must keep their images. -/
theorem cache_sound_of_stable_images (graph : DemandSummary.Graph (Label V L))
    (image other : V → Term W L) (cache : DemandSummary.Cache (Term W L))
    (sound : DemandSummary.Sound graph (algebra image) cache)
    (stable : ∀ root value, cache root = some value →
      ∀ name, HasVariable name (unfold graph root) → image name = other name) :
    DemandSummary.Sound graph (algebra other) cache := by
  intro root value present
  calc
    value = DemandSummary.eager graph (algebra image) root := sound root value present
    _ = substitute image (unfold graph root) := (substitution_unfold _ _ _).symm
    _ = substitute other (unfold graph root) :=
      substitute_congr image other _ (stable root value present)
    _ = DemandSummary.eager graph (algebra other) root := substitution_unfold _ _ _

theorem cached_import_after_context_extension
    (graph : DemandSummary.Graph (Label V L))
    (image other : V → Term W L) (cache : DemandSummary.Cache (Term W L))
    (sound : DemandSummary.Sound graph (algebra image) cache)
    (stable : ∀ root value, cache root = some value →
      ∀ name, HasVariable name (unfold graph root) → image name = other name)
    (root : Nat) :
    (DemandSummary.demand graph (algebra other) root cache).value =
      substitute other (unfold graph root) := by
  rw [DemandSummary.demand_exact _ _ _ _
    (cache_sound_of_stable_images graph image other cache sound stable), substitution_unfold]

/-- An invocation starts with its own empty cache; source pointer identity
can serve as node identity only within the fixed graph and interpretation. -/
def run (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (root : Nat) :
    DemandSummary.Result (Term W L) (Term W L) :=
  DemandSummary.demand graph (algebra image) root (fun _ => none)

theorem run_exact (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (root : Nat) :
    (run graph image root).value = substitute image (unfold graph root) := by
  rw [run, DemandSummary.demand_exact _ _ _ _ (DemandSummary.empty_sound _ _),
    substitution_unfold]

theorem run_computes_each_node_once (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (root : Nat) :
    (run graph image root).computed.Nodup :=
  (DemandSummary.demand_valid graph (algebra image) root _
    (DemandSummary.empty_sound _ _)).nodup

/-- This bounds node constructions, not edge visits or cache lookup cost. -/
theorem run_combinations_le_reachable (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (root : Nat) :
    (run graph image root).computed.length ≤ (DemandSummary.reachable graph root).card := by
  simpa [run] using DemandSummary.demand_combinations_le_uncached_reachable
    graph (algebra image) root (fun _ => none) (DemandSummary.empty_sound _ _)

theorem run_combinations_le_rank (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (root : Nat) :
    (run graph image root).computed.length ≤ root + 1 := by
  have valid := DemandSummary.demand_valid graph (algebra image) root
    (fun _ => none) (DemandSummary.empty_sound _ _)
  have nodup : (run graph image root).computed.Nodup := valid.nodup
  rw [← List.toFinset_card_of_nodup nodup]
  calc
    (run graph image root).computed.toFinset.card ≤ (Finset.range (root + 1)).card := by
      apply Finset.card_le_card
      intro node member
      exact Finset.mem_range.mpr (valid.bounded node (by simpa [run] using member))
    _ = root + 1 := Finset.card_range _

/-- Related roots use one cache and one interpretation, in their original
order. Repeating a root repeats its output occurrence, without reconstructing
its nodes. -/
def runMany (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (roots : List Nat) :
    DemandSummary.Result (List (Term W L)) (Term W L) :=
  DemandSummary.sequence roots
    (fun root cache => DemandSummary.demand graph (algebra image) root cache)
    (fun _ => none)

private theorem runMany_valid (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (roots : List Nat) :
    DemandSummary.Valid graph (algebra image) (fun _ => none)
      (runMany graph image roots)
      (roots.map (DemandSummary.eager graph (algebra image))) (roots.sum + 1) := by
  exact DemandSummary.sequence_demand_valid graph (algebra image) roots (fun _ => none)
    (DemandSummary.empty_sound _ _)

/-- The reference independently unfolds and substitutes each requested root.
List equality retains duplicate roots and the order of all child edges. -/
theorem runMany_exact (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (roots : List Nat) :
    (runMany graph image roots).value =
      roots.map (fun root => substitute image (unfold graph root)) := by
  rw [(runMany_valid graph image roots).value_eq]
  apply List.map_congr_left
  intro root _
  exact (substitution_unfold graph image root).symm

theorem runMany_computes_each_node_once (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (roots : List Nat) :
    (runMany graph image roots).computed.Nodup :=
  (runMany_valid graph image roots).nodup

def runManyRequests (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (roots : List Nat) : Nat :=
  DemandSummary.sequenceRequests roots
    (fun root cache => DemandSummary.demand graph (algebra image) root cache)
    (fun root cache => DemandSummary.demandRequests graph (algebra image) root cache)
    (fun _ => none)

theorem runManyRequests_eq (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (roots : List Nat) :
    runManyRequests graph image roots = roots.length +
      DemandSummary.edgeCount graph (runMany graph image roots).computed := by
  exact DemandSummary.sequenceRequests_eq graph _ _ _
    (fun root _ cache => DemandSummary.demandRequests_eq graph (algebra image) root cache) _

/-- One request per root and per physical edge of the reachable graph.
Payload construction and memo-table representation have separate costs. -/
theorem runManyRequests_le_reachable_edges (graph : DemandSummary.Graph (Label V L))
    (image : V → Term W L) (roots : List Nat) :
    runManyRequests graph image roots ≤ roots.length +
      ∑ node ∈ roots.toFinset.biUnion (DemandSummary.reachable graph),
        (graph.children node).length := by
  exact DemandSummary.sequenceRequests_le_reachable_edges graph (algebra image) roots
    (fun _ => none) (DemandSummary.empty_sound _ _)

end Terms

/-! ## Context and sharing controls -/

namespace Examples

/-- Each nonleaf source node points twice to the same preceding node. -/
def doubled : DemandSummary.Graph (Label Nat Nat) where
  label
    | 0 => .var 0
    | _ + 1 => .expr
  children
    | 0 => []
    | n + 1 => [⟨n, Nat.lt_succ_self n⟩, ⟨n, Nat.lt_succ_self n⟩]

def fresh (answer : Nat) (name : Nat) : Term (Nat × Nat) Nat :=
  .var (answer, name)

theorem fresh_identity_iff (answer other name different : Nat) :
    fresh answer name = fresh other different ↔ answer = other ∧ name = different := by
  simp [fresh]

theorem distinct_answers_have_distinct_variables {answer other : Nat}
    (different : answer ≠ other) (name : Nat) :
    fresh answer name ≠ fresh other name := by
  intro same
  exact different ((fresh_identity_iff _ _ _ _).mp same).1

theorem doubled_import_preserves_repeated_variable :
    (run doubled (fresh 7) 1).value = .expr [.var (7, 0), .var (7, 0)] := by
  rw [run_exact]
  simp [unfold, doubled, substitute, substituteAll, fresh]

theorem new_answer_changes_freshening_scope :
    (run doubled (fresh 7) 0).value ≠ (run doubled (fresh 8) 0).value := by
  simp [run_exact, unfold, doubled, substitute, fresh]

/-- The old cache returns answer 7's name inside answer 8. The source
node is unchanged: the omitted interpretation context alone breaks reuse. -/
theorem stale_answer_cache_reuses_wrong_variable :
    let old := run doubled (fresh 7) 0
    (DemandSummary.demand doubled (algebra (fresh 8)) 0 old.cache).value = .var (7, 0) ∧
    (run doubled (fresh 8) 0).value = .var (8, 0) := by
  constructor
  · simp [run, DemandSummary.demand, DemandSummary.sequence, doubled, algebra, fresh]
  · rw [run_exact]
    simp [unfold, doubled, substitute, fresh]

/-- Extending the variable interpretation at an unused source name does
not invalidate this cached node or force its reconstruction. -/
theorem extending_unused_variable_keeps_cached_image :
    let old := run doubled (fresh 7) 0
    let extended := Function.update (fresh 7) 1 (.var (7, 99))
    let next := DemandSummary.demand doubled (algebra extended) 0 old.cache
    next.value = .var (7, 0) ∧ next.computed = [] ∧ extended 1 = .var (7, 99) := by
  simp [run, DemandSummary.demand, DemandSummary.sequence, doubled, algebra, fresh]

/-- A host-mapped name and a fresh row name may share the source
pointer while denoting different target cells. -/
theorem mode_is_part_of_import_context :
    let callImage : Nat → Term Nat Nat := fun _ => .var 42
    let rowImage : Nat → Term Nat Nat := fun _ => .var 99
    (run doubled callImage 0).value ≠ (run doubled rowImage 0).value := by
  simp [run_exact, unfold, doubled, substitute]

mutual
def occurrences : Term (Nat × Nat) Nat → Nat
  | .var _ => 1
  | .leaf _ => 1
  | .expr children => 1 + occurrencesAll children

def occurrencesAll : List (Term (Nat × Nat) Nat) → Nat
  | [] => 0
  | child :: rest => occurrences child + occurrencesAll rest
end

theorem doubled_unfold_occurrences (answer root : Nat) :
    occurrences (substitute (fresh answer) (unfold doubled root)) + 1 = 2 ^ (root + 1) := by
  induction root with
  | zero => simp [unfold, doubled, substitute, fresh, occurrences]
  | succ root ih =>
      rw [unfold]
      simp only [doubled, List.map_cons, List.map_nil,
        substitute, substituteAll, occurrences, occurrencesAll]
      change 1 + (occurrences (substitute (fresh answer) (unfold doubled root)) +
        (occurrences (substitute (fresh answer) (unfold doubled root)) + 0)) + 1 =
          2 ^ (root + 1 + 1)
      rw [pow_succ]
      omega

/-- Exponentially many expanded occurrences coexist with only linearly many
node combinations. This is a work bound for importing the represented DAG,
not a bound for subsequently printing every expanded occurrence. -/
theorem doubled_import_linear_combinations_exponential_occurrences (answer root : Nat) :
    (run doubled (fresh answer) root).computed.length ≤ root + 1 ∧
    occurrences (run doubled (fresh answer) root).value + 1 = 2 ^ (root + 1) := by
  exact ⟨run_combinations_le_rank _ _ _, by rw [run_exact]; exact doubled_unfold_occurrences _ _⟩

/-- Two observations remain two, although their construction is shared. -/
theorem duplicate_roots_share_construction_not_occurrences :
    (runMany doubled (fresh 7) [3, 3]).value.length = 2 ∧
    (runMany doubled (fresh 7) [3, 3]).computed = [0, 1, 2, 3] ∧
    runManyRequests doubled (fresh 7) [3, 3] = 8 := by
  decide +kernel

theorem deduplicating_requested_roots_changes_observation :
    (runMany doubled (fresh 7) [3, 3]).value ≠
      (runMany doubled (fresh 7) [3]).value := by
  intro same
  have lengths := congrArg List.length same
  change 2 = 1 at lengths
  omega

end Examples

end Mettapedia.Machines.GraphImport
