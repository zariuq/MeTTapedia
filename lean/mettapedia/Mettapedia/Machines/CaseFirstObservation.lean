import Mettapedia.Machines.SourceCase

/-!
# A first-match case observer retains its selected binding

The source scans rows by the maintained literal matcher, keeps the first
produced key, then enters the maintained case selector. The target tests exact
membership and installs the selected variable's binding before entering the
body. A branch that ignores that variable does not erase the caller's binding.

This is the literal-row, initially unbound case-variable observer. Native
admission must establish exact matching, an inert completed template, source
first-success and literal-default authority, and the absence of an observable
source-step boundary. Budgeted execution retains ordinary entry. Native C,
concurrent storage and broader unification remain correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CaseFirstObservation

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK
abbrev Atom := Mettapedia.Languages.MeTTa.OSLFCore.Atom
abbrev Bindings := Mettapedia.Languages.ProcessCalculi.MORK.Subst

def sourceKeys (bindings : Bindings) (pattern key : Atom) (rows : List Atom) : List Atom :=
  rows.filterMap fun row => (SpaceSemantics.matchValue bindings pattern row).map fun _ => key

theorem first_key_refines (bindings : Bindings) (pattern key : Atom)
    (literal : SpaceSemantics.Literal pattern) (rows : List Atom) :
    (sourceKeys bindings pattern key rows).head? =
      if pattern ∈ rows then some key else none := by
  induction rows with
  | nil => simp [sourceKeys]
  | cons row rows ih =>
      by_cases same : pattern = row
      · subst row
        simp [sourceKeys, SpaceSemantics.matchValue_literal literal]
      · simpa [sourceKeys, SpaceSemantics.matchValue_literal literal, same] using ih

def source {Effect Fault Delay Suspension : Type} (bindings : Bindings)
    (pattern key : Atom) (rows : List Atom) (name : String) (no yes : Atom) :
    ContextualCBPV.Code Atom (Bindings × Atom) Effect Fault Delay Suspension :=
  match (sourceKeys bindings pattern key rows).head? with
  | none => .invoke (bindings, no)
  | some value => SourceCase.sourceReady bindings value [(.var name, yes)]

def target {Effect Fault Delay Suspension : Type} (bindings : Bindings)
    (pattern key : Atom) (rows : List Atom) (name : String) (no yes : Atom) :
    ContextualCBPV.Code Atom (Bindings × Atom) Effect Fault Delay Suspension :=
  if pattern ∈ rows then .invoke ((name, key) :: bindings, yes)
  else .invoke (bindings, no)

theorem observation_refines {Effect Fault Delay Suspension : Type}
    (bindings : Bindings) (pattern key : Atom) (literal : SpaceSemantics.Literal pattern)
    (rows : List Atom) (name : String) (unbound : bindings.lookup name = none) (no yes : Atom) :
    target (Effect := Effect) (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
        bindings pattern key rows name no yes =
      source bindings pattern key rows name no yes := by
  unfold source target
  rw [first_key_refines bindings pattern key literal rows]
  split <;> simp_all [SourceCase.sourceReady, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, matchAtom]

theorem selected_binding (bindings : Bindings) (name : String) (key : Atom) :
    (((name, key) :: bindings) : Bindings).lookup name = some key := by
  simp

theorem dropping_binding_changes_result :
    (target (Effect := Unit) (Fault := Unit) (Delay := Unit) (Suspension := Unit)
      [] (.symbol "row") (.symbol "hit") [.symbol "row"] "v"
      (.symbol "absent") (.symbol "present")) ≠
      .invoke ([], .symbol "present") := by
  simp [target]

theorem selected_body_stays_pending :
    (target (Effect := Unit) (Fault := Unit) (Delay := Unit) (Suspension := Unit)
      [] (.symbol "row") (.symbol "hit") [.symbol "row"] "v"
      (.symbol "absent") (.expression [.symbol "effect"])) =
      .invoke ([("v", .symbol "hit")], .expression [.symbol "effect"]) := by
  simp [target]

end Mettapedia.Machines.CaseFirstObservation

#print axioms Mettapedia.Machines.CaseFirstObservation.first_key_refines
#print axioms Mettapedia.Machines.CaseFirstObservation.observation_refines
#print axioms Mettapedia.Machines.CaseFirstObservation.selected_binding
#print axioms Mettapedia.Machines.CaseFirstObservation.dropping_binding_changes_result
#print axioms Mettapedia.Machines.CaseFirstObservation.selected_body_stays_pending
