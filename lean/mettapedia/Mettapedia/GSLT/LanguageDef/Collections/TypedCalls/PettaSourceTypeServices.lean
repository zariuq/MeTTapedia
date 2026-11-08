import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeRows
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedTypeRelation

/-!
# Live-world services for the occurrence-wise typed source owner

Call rows, the declaration environment of every type query, and metatypes
come from the reached source world. Type consistency is solved by the existing
total unifier. No supplied row list, answer list, or body-evaluation oracle is
needed. Native registry loading and carrier/binding readback are separate
implementation correspondences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PettaOccurrenceOverlay (Store)

/-- The source library already owns registry-sensitive metatype dispatch. -/
def kind (world : EagerDFS.World) (value : Atom) : String :=
  match StdLib.metatype world.state value with
  | .symbol name => name
  | _ => ""

theorem kind_is_source_metatype (world : EagerDFS.World) (value : Atom) :
    StdLib.metatype world.state value = .symbol (kind world value) := by
  cases value with
  | symbol name => simp only [kind, StdLib.metatype]; split <;> rfl
  | var name | grounded name | expression name => rfl

def orderedGuard (intrinsicRows : List Atom) (world : EagerDFS.World) (index : Nat)
    (store : Store) (expected : Ty String) (value : Atom) : Option (List Store) :=
  if PettaSourceTypeRows.supported intrinsicRows world && EagerDFS.Destination.finiteStructural value then
    some (OrderedTypeRelation.guardOrdered (atGuard index) store (expected.map Sum.inl)
      (OrderedTypeRelation.infer (PettaSourceTypeRows.declarations intrinsicRows world) value)
      (kind world value))
  else none

theorem orderedGuard_exact (intrinsicRows : List Atom) (world : EagerDFS.World) (index : Nat)
    (store : Store) (expected : Ty String) (value : Atom) (answers : List Store)
    (served : orderedGuard intrinsicRows world index store expected value = some answers) :
    (answers : Multiset Store) = guard (atGuard index) store (expected.map Sum.inl)
      (info (PettaSourceTypeRows.declarations intrinsicRows world) value) (kind world value) := by
  unfold orderedGuard at served
  split at served
  · cases Option.some.inj served
    rw [OrderedTypeRelation.guardOrdered_erases, OrderedTypeRelation.infer_erases]
  · cases served

def services (intrinsicRows : List Atom := []) : PettaOccurrenceOverlay.Services Unit where
  rows world _ := PettaSourceTypeRows.lookup intrinsicRows world
  declarations := PettaSourceTypeRows.declarations intrinsicRows
  kind := kind
  userSupport _ := ∅
  orderedGuard := orderedGuard intrinsicRows
  guard_exact := orderedGuard_exact intrinsicRows

/-- This is equality of the returned list, not just a bag certificate. The
source realization uses the explicit written/depth-first derivation order. -/
theorem orderedGuard_order (intrinsicRows : List Atom) (world : EagerDFS.World) (index : Nat)
    (store : Store) (expected : Ty String) (value : Atom)
    (sourceSupported : PettaSourceTypeRows.supported intrinsicRows world = true)
    (valueSupported : EagerDFS.Destination.finiteStructural value = true) :
    orderedGuard intrinsicRows world index store expected value =
      some (OrderedTypeRelation.guardOrdered (atGuard index) store (expected.map Sum.inl)
        (OrderedTypeRelation.infer (PettaSourceTypeRows.declarations intrinsicRows world) value)
        (kind world value)) := by
  simp [orderedGuard, sourceSupported, valueSupported]

theorem unsupported_source_retained (intrinsicRows : List Atom) (world : EagerDFS.World) (index : Nat)
    (store : Store) (expected : Ty String) (value : Atom)
    (unsupported : PettaSourceTypeRows.supported intrinsicRows world = false) :
    orderedGuard intrinsicRows world index store expected value = none := by
  simp [orderedGuard, unsupported]

theorem unsupported_carrier_retained (intrinsicRows : List Atom) (world : EagerDFS.World) (index : Nat)
    (store : Store) (expected : Ty String) (value : Atom)
    (unsupported : EagerDFS.Destination.finiteStructural value = false) :
    orderedGuard intrinsicRows world index store expected value = none := by
  simp [orderedGuard, unsupported]

/-- Concrete source guard replies retain all equations learned by the same
row's earlier argument guards. This applies to result guards as well. -/
theorem orderedGuard_extends_store (intrinsicRows : List Atom) (world : EagerDFS.World) (index : Nat)
    (store answer : Store) (expected : Ty String) (value : Atom) (answers : List Store)
    (served : orderedGuard intrinsicRows world index store expected value = some answers)
    (member : answer ∈ answers) :
    ∃ suffix, answer = store ++ suffix ∧ Sat answer := by
  unfold orderedGuard at served
  split at served
  · cases Option.some.inj served
    exact OrderedTypeRelation.guardOrdered_extends _ _ _ _ _ _ member
  · cases served

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices
