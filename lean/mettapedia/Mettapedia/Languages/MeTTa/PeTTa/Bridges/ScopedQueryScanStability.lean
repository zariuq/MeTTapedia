import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource

/-!
# Append-stable source query occurrences

Appending unmatched rows preserves both bindings and original scan ordinals.
The capture worker also preserves refusal. These are scan/capture laws, not
whole-world equalities: the updated world must still be threaded to bodies,
and complete-domain admission must be re-established independently.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryScanStability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open EagerDFS.Destination
open FlatQueryRelationCompilation (sourceScan)

theorem scan_append (bindings : Subst) (pattern : Atom) (offset : Nat) (first second : List Atom) :
    sourceScan bindings pattern offset (first ++ second) =
      sourceScan bindings pattern offset first ++ sourceScan bindings pattern (offset + first.length) second := by
  induction first generalizing offset with
  | nil => simp [sourceScan]
  | cons row rest ih =>
      have shift : offset + 1 + rest.length = offset + (rest.length + 1) := by omega
      simp only [List.cons_append, sourceScan, ih, List.length_cons, List.append_assoc, shift]

theorem scan_unmatched (bindings : Subst) (pattern : Atom) (offset : Nat) (rows : List Atom)
    (unmatched : ∀ row ∈ rows, SpaceSemantics.matchValue bindings pattern row = none) :
    sourceScan bindings pattern offset rows = [] := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rest ih =>
      simp only [sourceScan, unmatched row List.mem_cons_self, Option.map_none, Option.toList_none,
        List.nil_append, ih (offset + 1) (fun value member => unmatched value (List.mem_cons_of_mem _ member))]

theorem append_unmatched_keeps_ordinals (bindings : Subst) (pattern : Atom) (offset : Nat) (rows added : List Atom)
    (unmatched : ∀ row ∈ added, SpaceSemantics.matchValue bindings pattern row = none) :
    sourceScan bindings pattern offset (rows ++ added) = sourceScan bindings pattern offset rows := by
  rw [scan_append, scan_unmatched bindings pattern _ added unmatched, List.append_nil]

theorem capture_unmatched (caller : Control) (pattern body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom)
    (unmatched : ∀ row ∈ rows, SpaceSemantics.matchValue [] pattern row = none) :
    ScopedQuerySource.capture caller pattern body destination older offset rows = some [] := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rest ih =>
      simp only [ScopedQuerySource.capture, unmatched row List.mem_cons_self]
      exact ih (offset + 1) (fun value member => unmatched value (List.mem_cons_of_mem _ member))

theorem capture_append_unmatched (caller : Control) (pattern body destination : Atom) (older : List Goal)
    (offset : Nat) (rows added : List Atom)
    (unmatched : ∀ row ∈ added, SpaceSemantics.matchValue [] pattern row = none) :
    ScopedQuerySource.capture caller pattern body destination older offset (rows ++ added) =
      ScopedQuerySource.capture caller pattern body destination older offset rows := by
  induction rows generalizing offset with
  | nil => exact capture_unmatched caller pattern body destination older offset added unmatched
  | cons row rest ih =>
      simp only [List.cons_append, ScopedQuerySource.capture]
      cases matched : SpaceSemantics.matchValue [] pattern row with
      | none => exact ih (offset + 1)
      | some bindings => simp only [ih]

theorem domain_admission_append (pattern : Atom) (rows added : List Atom) :
    ClosedQueryAdmission.rowsReady pattern (rows ++ added) = true ↔
      ClosedQueryAdmission.rowsReady pattern rows = true ∧ ClosedQueryAdmission.rowsReady pattern added = true := by
  simp [ClosedQueryAdmission.rowsReady]

namespace Controls

def row (head : String) (value : Atom) : Atom := .expression [.symbol head, value]
def seven : Atom := .grounded (.int 7)
def query : Atom := row "p" seven
def other : Atom := row "q" seven

theorem appended_unmatched_keeps_two_occurrences :
    sourceScan [] query 0 [query, other, query, other] = [(0, []), (2, [])] := by decide +kernel

theorem prepending_unmatched_changes_ordinals :
    (sourceScan [] query 0 [query, query]).map Prod.snd =
      (sourceScan [] query 0 [other, query, query]).map Prod.snd ∧
      sourceScan [] query 0 [query, query] ≠ sourceScan [] query 0 [other, query, query] := by decide +kernel

def openRow : Atom := row "p" (.var "stored")

theorem unchanged_one_way_scan_does_not_certify_new_admission :
    sourceScan [] query 0 [query, openRow] = sourceScan [] query 0 [query] ∧
      ClosedQueryAdmission.rowsReady query [query] = true ∧
      ClosedQueryAdmission.rowsReady query [query, openRow] = false := by decide +kernel

end Controls

#print axioms append_unmatched_keeps_ordinals
#print axioms capture_append_unmatched

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryScanStability
