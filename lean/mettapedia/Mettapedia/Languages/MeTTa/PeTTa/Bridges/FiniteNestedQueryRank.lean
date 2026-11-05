import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryCompletion

/-!
# Exact remaining-head balance for dynamic insertion phases

The current query values stay in one fixed domain. Every accepted fresh
insertion consumes one previously absent catalogue head; a held head consumes
nothing. The source answer count therefore accounts for the rank decrease
through every nested read and ordered body traversal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryRank

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance
open FlatQueryRowCodec FlatQueryDomainInvariant FiniteNestedQuerySource
open NamedSpaces EffectfulQuerySource

variable {Value : Type} [DecidableEq Value]

def catalogue {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (head : FlatQueryOutputDomain.Head codec names) : Finset Atom :=
  FlatQueryOutputDomain.catalogue codec domain {(head.2.head, head.2.cells.length)}

def rank {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (head : FlatQueryOutputDomain.Head codec names) (rows : List Atom) : Nat :=
  FreshInsertionRank.remaining (catalogue domain head) rows

theorem rendered_member {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (bindings : Subst) (bound : BindingsInDomain codec names domain bindings) (values : List Value)
    (rendered : ConjunctiveOutputDomain.instantiate (readback codec names bindings) head.2.cells = some values) :
    row codec head.2.head values ∈ catalogue domain head := by
  have inside := ConjunctiveOutputDomain.instantiate_domain domain _ bound.2 head.2.cells values constants rendered
  have length := ((ConjunctiveOutputDomain.instantiate_iff _ head.2.cells values).mp rendered).length_eq
  apply Finset.mem_image.mpr
  refine ⟨(head.2.head, values), (ConjunctiveOutputDomain.mem_catalogue _ _ _ _).mpr ⟨?_, inside⟩, rfl⟩
  simp only [Finset.mem_singleton, Prod.mk.injEq, true_and]
  exact length.symm

theorem emit_balance {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before after : Effects.State) (rows answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (snapshot : before.read target = some rows)
    (completed : emit head target bindings before = some (after, answers)) :
    ∃ result, after.read target = some result ∧ rank domain head result + answers.length = rank domain head rows := by
  obtain ⟨values, rendered, tail⟩ := Option.bind_eq_some_iff.mp completed
  split at tail
  next accepted =>
    obtain ⟨receipt, updated, same⟩ := Option.map_eq_some_iff.mp tail
    rcases receipt with ⟨next, changed⟩
    cases same
    cases changed with
    | false =>
        have unchanged := FreshInsertionSource.zero_progress_preserves_state updated
        subst next
        exact ⟨rows, snapshot, by simp [FreshInsertionSource.answers]⟩
    | true =>
        obtain ⟨old, result, _, reading, _⟩ := FreshInsertionSource.update_growth updated
        have balance := FreshInsertionRank.fresh_entry_decreases (catalogue domain head) target _ before next rows result
          (rendered_member domain head constants bindings bound values rendered) snapshot reading updated
        exact ⟨result, reading, by simpa [rank, FreshInsertionSource.answers] using balance⟩
  next refused => cases tail

private theorem traverse_balance (body : Body) (invariant : Effects.State → Prop) (target : Handle)
    (measure : List Atom → Nat) (captured : List Subst)
    (law : ∀ bindings ∈ captured, ∀ before after answers rows, invariant before → before.read target = some rows →
      body bindings before = some (after, answers) → invariant after ∧
      ∃ result, after.read target = some result ∧ measure result + answers.length = measure rows)
    (before after : Effects.State) (rows collected answers : List Atom)
    (valid : invariant before) (snapshot : before.read target = some rows)
    (completed : traverse body captured (before, collected) = some (after, answers)) :
    ∃ result, after.read target = some result ∧ measure result + answers.length = measure rows + collected.length := by
  induction captured generalizing before rows collected with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
      exact ⟨rows, snapshot, rfl⟩
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨nextValid, middleRows, middleRead, firstBalance⟩ := law bindings List.mem_cons_self
        before next.1 next.2 rows valid snapshot first
      obtain ⟨result, reading, laterBalance⟩ := ih (fun selected member => law selected (List.mem_cons_of_mem _ member))
        next.1 middleRows (collected ++ next.2) nextValid middleRead later
      refine ⟨result, reading, ?_⟩
      simp only [List.length_append] at laterBalance
      omega

theorem run_balance {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (footprint queries : List (Query codec names)) (within : ∀ query ∈ queries, query ∈ footprint)
    (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before after : Effects.State) (targetRows answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain footprint before)
    (snapshot : before.read target = some targetRows)
    (completed : run queries head target bindings before = some (after, answers)) :
    ∃ result, after.read target = some result ∧ rank domain head result + answers.length = rank domain head targetRows := by
  induction queries generalizing bindings before after targetRows answers with
  | nil => exact emit_balance domain head constants target bindings before after targetRows answers bound snapshot completed
  | cons query queries ih =>
      obtain ⟨rows, reading, traversed⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨old, oldRead, ready⟩ := valid query (within query List.mem_cons_self)
      have equalRows : old = rows := Option.some.inj (oldRead.symm.trans reading)
      subst old
      have remaining : ∀ item ∈ queries, item ∈ footprint := fun item member => within item (List.mem_cons_of_mem _ member)
      obtain ⟨result, finalRead, balance⟩ := traverse_balance (run queries head target) (ViewsInDomain domain footprint)
        target (rank domain head) (choices bindings query.source rows) (fun selected member current next values currentRows currentValid currentRead returned => by
          have nextBound := choices_preserve query.pattern domain rows bindings selected ready bound member
          exact ⟨run_preserves domain footprint queries remaining head constants target selected current next values nextBound currentValid returned,
            ih remaining selected current next currentRows values nextBound currentValid currentRead returned⟩)
        before after targetRows [] answers valid snapshot traversed
      exact ⟨result, finalRead, by simpa using balance⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryRank
