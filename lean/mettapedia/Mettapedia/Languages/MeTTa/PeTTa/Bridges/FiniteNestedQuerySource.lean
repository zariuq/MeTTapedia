import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryDomainInvariant
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FreshNestedQuerySource

/-!
# Domain-preserving fresh insertion through dynamic nested source queries

The checked emitter reads actual output slots and refuses unbound ones.
Accepted execution agrees with the existing source emitter and retains its
ordered answers. A single finite value domain survives same-space writes,
including writes which alter later query results.

Failure is a private-worker refusal, not permission to erase an already
published native prefix. These are completed, no-I/O source laws, not exact
evaluator-page or whole recursive-dispatch correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance
open FlatQueryRowCodec FlatQueryDomainInvariant
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

variable {Value : Type} [DecidableEq Value]

def emit {codec : Codec Value} {names : Inventory String} (head : FlatQueryOutputDomain.Head codec names)
    (target : Handle) : Body := fun bindings state => do
  let values ← ConjunctiveOutputDomain.instantiate (readback codec names bindings) head.2.cells
  if GuardedInsertionSource.dataRow (row codec head.2.head values) then
    (FreshInsertionSource.update state target (row codec head.2.head values)).map
      (fun result => (result.1, FreshInsertionSource.answers result.2))
  else none

omit [DecidableEq Value] in
theorem emit_refines {codec : Codec Value} {names : Inventory String} (head : FlatQueryOutputDomain.Head codec names)
    (target : Handle) (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (represented : Represents codec names (readback codec names bindings) bindings)
    (completed : emit head target bindings before = some (after, answers)) :
    FreshQueryMaterialization.emit target head.1 bindings before = some (after, answers) := by
  obtain ⟨values, rendered, result⟩ := Option.bind_eq_some_iff.mp completed
  split at result
  next accepted =>
    have source := FlatQueryOutputDomain.instantiate_head head.2 _ bindings represented values rendered
    simpa only [FreshQueryMaterialization.emit, source] using result
  next refused => cases result

theorem emit_preserves {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain queries before)
    (completed : emit head target bindings before = some (after, answers)) : ViewsInDomain domain queries after := by
  obtain ⟨values, rendered, result⟩ := Option.bind_eq_some_iff.mp completed
  split at result
  next accepted =>
    obtain ⟨receipt, inserted, same⟩ := Option.map_eq_some_iff.mp result
    rcases receipt with ⟨next, changed⟩
    cases same
    have inside := ConjunctiveOutputDomain.instantiate_domain domain _ bound.2 head.2.cells values constants rendered
    have length := ((ConjunctiveOutputDomain.instantiate_iff _ head.2.cells values).mp rendered).length_eq
    have member : row codec head.2.head values ∈
        FlatQueryOutputDomain.catalogue codec domain { (head.2.head, head.2.cells.length) } := by
      apply Finset.mem_image.mpr
      refine ⟨(head.2.head, values), (ConjunctiveOutputDomain.mem_catalogue _ _ _ _).mpr ⟨?_, inside⟩, rfl⟩
      simp only [Finset.mem_singleton, Prod.mk.injEq, true_and]
      exact length.symm
    exact fresh_preserves domain queries _ before next target _ changed valid member inserted
  next refused => cases result

def run {codec : Codec Value} {names : Inventory String} (queries : List (Query codec names))
    (head : FlatQueryOutputDomain.Head codec names) (target : Handle) : Body :=
  NestedQuerySource.run (emit head target) (queries.map Query.leg)

theorem run_preserves {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (footprint queries : List (Query codec names)) (within : ∀ query ∈ queries, query ∈ footprint)
    (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain footprint before)
    (completed : run queries head target bindings before = some (after, answers)) : ViewsInDomain domain footprint after :=
  nested_preserves domain footprint (emit head target)
    (fun bindings before after answers => emit_preserves domain footprint head constants target bindings before after answers)
    queries within bindings before after answers bound valid completed

private theorem traverse_refines (worker reference : Body) (invariant : Effects.State → Prop) (captured : List Subst)
    (law : ∀ bindings ∈ captured, ∀ before after answers, invariant before →
      worker bindings before = some (after, answers) →
      invariant after ∧ reference bindings before = some (after, answers))
    (before after : Effects.State) (collected answers : List Atom) (valid : invariant before)
    (completed : traverse worker captured (before, collected) = some (after, answers)) :
    traverse reference captured (before, collected) = some (after, answers) := by
  induction captured generalizing before collected with
  | nil => exact completed
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨nextValid, firstRef⟩ := law bindings List.mem_cons_self before next.1 next.2 valid first
      have laterRef := ih (fun bindings member => law bindings (List.mem_cons_of_mem _ member))
        next.1 (collected ++ next.2) nextValid later
      simpa only [EffectfulQuerySource.traverse, firstRef, Option.bind_some] using laterRef

theorem run_refines {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (footprint queries : List (Query codec names)) (within : ∀ query ∈ queries, query ∈ footprint)
    (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain footprint before)
    (completed : run queries head target bindings before = some (after, answers)) :
    FreshNestedQuerySource.run target head.1 (queries.map Query.leg) bindings before = some (after, answers) := by
  induction queries generalizing bindings before after answers with
  | nil => exact emit_refines head target bindings before after answers bound.1 completed
  | cons query queries ih =>
      obtain ⟨rows, snapshot, traversed⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨old, oldRead, ready⟩ := valid query (within query List.mem_cons_self)
      have same : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
      subst old
      have remaining : ∀ item ∈ queries, item ∈ footprint := fun item member => within item (List.mem_cons_of_mem _ member)
      have refined := traverse_refines (run queries head target)
        (FreshNestedQuerySource.run target head.1 (queries.map Query.leg)) (ViewsInDomain domain footprint)
        (choices bindings query.source rows) (fun selected member current next values currentValid returned => by
          have nextBound := choices_preserve query.pattern domain rows bindings selected ready bound member
          exact ⟨run_preserves domain footprint queries remaining head constants target selected current next values
            nextBound currentValid returned,
            ih remaining selected current next values nextBound currentValid returned⟩)
        before after [] answers valid traversed
      simpa only [FreshNestedQuerySource.run, List.map_cons, Query.leg, NestedQuerySource.run,
        snapshot, bind, Option.bind] using refined

theorem source_returns {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (program : Program) (spaceName temporary : String) (target : Handle)
    (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain queries before)
    (different : temporary ≠ spaceName)
    (outside : ∀ query ∈ queries, temporary ∉ atomFreeVars query.source)
    (ready : FreshNestedQuerySource.BindingsReady spaceName temporary target bindings)
    (completed : run queries head target bindings before = some (after, answers)) :
    Returns program bindings before
      (NestedQuerySource.source (queries.map Query.leg) (FreshQueryMaterialization.bodySource spaceName temporary head.1))
      after answers := by
  apply FreshNestedQuerySource.source_returns program spaceName temporary target head.1 (queries.map Query.leg)
    bindings before after answers different _ ready
    (run_refines domain queries queries (fun _ member => member) head constants target bindings before after answers bound valid completed)
  intro leg member
  obtain ⟨query, present, rfl⟩ := List.mem_map.mp member
  exact outside query present

theorem quiet_is_saturated {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before after : Effects.State)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain queries before)
    (completed : run queries head target bindings before = some (after, [])) :
    before = after ∧ FreshNestedQuerySource.SaturatedAt before target head.1 (queries.map Query.leg) bindings :=
  (FreshNestedQuerySource.zero_iff_saturated target head.1 (queries.map Query.leg) bindings before after).mp
    (run_refines domain queries queries (fun _ member => member) head constants target bindings before after [] bound valid completed)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQuerySource
