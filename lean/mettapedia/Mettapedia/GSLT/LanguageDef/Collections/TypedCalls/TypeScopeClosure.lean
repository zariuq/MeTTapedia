import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyAdmission

/-!
# Complete source-scope closure for an executable conservative gate

The scope graph contains each space's actual rows, and edges include its
overlay and imported spaces. This gate checks all rows, not only the queried
head. A finite recursion allowance is conservative: exhausting it declines;
success certifies every reachable node, including paths longer than the
allowance (such paths cannot exist in an accepted scope).

The generated packet preserves the selected occurrence order and duplicates.
Its visits must be actual reachable spaces. The native enumeration's coverage
of all overlay/import dependencies and its revision tracking remain separate
adapter obligations. In particular, this all-row gate is stronger than the
native identity flag on declaration/subtype rows.

The subtype query below matches the complete `(:< input $fresh)` row with
the existing total atom unifier. It therefore also detects why headless rows
cannot simply be discarded by a declaration collector. These are primitive
source-query laws, not a second whole-language type inference service.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypeDependencyAdmission
open RetainedTypePayloads (ExternalView observe observeList)

structure ScopeGraph (Id : Type) where
  rows : Id → List Atom
  dependencies : Id → List Id
  intrinsicRows : List Atom

inductive Reach {Id : Type} (graph : ScopeGraph Id) : Id → Id → Prop where
  | here {root : Id} : Reach graph root root
  | via {root child target : Id} : child ∈ graph.dependencies root →
      Reach graph child target → Reach graph root target

def checkScope {Id : Type} (graph : ScopeGraph Id) : Nat → Id → Bool
  | 0, _ => false
  | fuel + 1, root => resourceFreeList (graph.rows root) &&
      (graph.dependencies root).all (checkScope graph fuel)

theorem checkScope_reachable {Id : Type} (graph : ScopeGraph Id) :
    ∀ fuel root, checkScope graph fuel root = true →
      ∀ target, Reach graph root target → resourceFreeList (graph.rows target) = true
  | 0, _, accepted, _, _ => by simp [checkScope] at accepted
  | fuel + 1, root, accepted, target, reached => by
      simp only [checkScope, Bool.and_eq_true, List.all_eq_true] at accepted
      cases reached with
      | here => exact accepted.1
      | via member later => exact checkScope_reachable graph fuel _ (accepted.2 _ member) target later

def capturedRows {Id : Type} (graph : ScopeGraph Id) (visits : List Id) : List Atom :=
  visits.flatMap graph.rows

theorem capturedRows_resourceFree {Id : Type} (graph : ScopeGraph Id) (fuel : Nat) (root : Id)
    (accepted : checkScope graph fuel root = true) (visits : List Id)
    (visited : ∀ node ∈ visits, Reach graph root node) :
    resourceFreeList (capturedRows graph visits) = true := by
  apply (resourceFreeList_iff _).mpr
  intro row member
  obtain ⟨node, occurs, stored⟩ := List.mem_flatMap.mp member
  exact (resourceFreeList_iff _).mp
    (checkScope_reachable graph fuel root accepted node (visited node occurs)) row stored

def checkInput {Id : Type} (graph : ScopeGraph Id) (fuel : Nat) (root : Id) (input : Atom) : Bool :=
  checkScope graph fuel root && resourceFreeList graph.intrinsicRows && resourceFree input

def packet {Id : Type} (graph : ScopeGraph Id) (visits : List Id) (input : Atom) : SourcePacket :=
  ⟨capturedRows graph visits, graph.intrinsicRows, input⟩

theorem captured_packet_passes {Id : Type} (graph : ScopeGraph Id) (fuel : Nat) (root : Id)
    (input : Atom) (accepted : checkInput graph fuel root input = true) (visits : List Id)
    (visited : ∀ node ∈ visits, Reach graph root node) :
    TypeDependencyAdmission.check (packet graph visits input) = true := by
  simp only [checkInput, Bool.and_eq_true] at accepted
  simp only [TypeDependencyAdmission.check, packet, Bool.and_eq_true]
  exact ⟨⟨capturedRows_resourceFree graph fuel root accepted.1.1 visits visited,
    accepted.1.2⟩, accepted.2⟩

theorem captured_annotation_world {Id : Type} (graph : ScopeGraph Id) (fuel : Nat) (root : Id)
    (input : Atom) (accepted : checkInput graph fuel root input = true) (visits : List Id)
    (visited : ∀ node ∈ visits, Reach graph root node) (first second : ExternalView) :
    Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes
        (observedSpace first (capturedRows graph visits)) (observe first input) =
      Mettapedia.Languages.MeTTa.HE.getAnnotatedTypes
        (observedSpace second (capturedRows graph visits)) (observe second input) :=
  annotation_world_independent first second
    (captured_packet_passes graph fuel root input accepted visits visited)

def subtypePattern (input : Atom) (fresh : String) : Atom :=
  .expression [.symbol ":<", input, .var fresh]

def subtypeRow (external : ExternalView) (input : Atom) (fresh : String) (row : Atom) : Option Atom := do
  let theta ← UnifyAtoms.unify (observe external (subtypePattern input fresh)) (observe external row)
  let result := UnifyAtoms.readBack theta fresh
  if result == Atom.var fresh then none else some result

def subtypeQuery (external : ExternalView) (input : Atom) (fresh : String) (rows : List Atom) : List Atom :=
  rows.filterMap (subtypeRow external input fresh)

theorem subtypeRow_resourceFree (external : ExternalView) (input : Atom) (fresh : String)
    (inputSafe : resourceFree input = true) (row : Atom) (rowSafe : resourceFree row = true)
    (result : Atom) (returned : subtypeRow external input fresh row = some result) :
    resourceFree result = true := by
  have patternSafe : resourceFree (subtypePattern input fresh) = true := by
    simp [subtypePattern, resourceFree, resourceFreeList, inputSafe]
  simp only [subtypeRow, observe_resourceFree external _ patternSafe,
    observe_resourceFree external _ rowSafe] at returned
  cases matched : UnifyAtoms.unify (subtypePattern input fresh) row with
  | none => simp [matched] at returned
  | some theta =>
      simp only [matched] at returned
      change (if UnifyAtoms.readBack theta fresh == Atom.var fresh then none
        else some (UnifyAtoms.readBack theta fresh)) = some result at returned
      split at returned
      · contradiction
      · cases Option.some.inj returned
        exact unify_resourceFree matched patternSafe rowSafe fresh

theorem subtypeQuery_resourceFree (external : ExternalView) (input : Atom) (fresh : String)
    (inputSafe : resourceFree input = true) (rows : List Atom) (rowsSafe : resourceFreeList rows = true) :
    resourceFreeList (subtypeQuery external input fresh rows) = true := by
  apply (resourceFreeList_iff _).mpr
  intro result member
  obtain ⟨row, occurs, returned⟩ := List.mem_filterMap.mp member
  exact subtypeRow_resourceFree external input fresh inputSafe row
    ((resourceFreeList_iff _).mp rowsSafe row occurs) result returned

theorem subtypeRow_world (first second : ExternalView) (input : Atom) (fresh : String)
    (inputSafe : resourceFree input = true) (row : Atom) (rowSafe : resourceFree row = true) :
    subtypeRow first input fresh row = subtypeRow second input fresh row := by
  have patternSafe : resourceFree (subtypePattern input fresh) = true := by
    simp [subtypePattern, resourceFree, resourceFreeList, inputSafe]
  simp [subtypeRow, observe_resourceFree first _ patternSafe, observe_resourceFree second _ patternSafe,
    observe_resourceFree first _ rowSafe, observe_resourceFree second _ rowSafe]

theorem subtypeQuery_world (first second : ExternalView) (input : Atom) (fresh : String)
    (inputSafe : resourceFree input = true) (rows : List Atom) (rowsSafe : resourceFreeList rows = true) :
    subtypeQuery first input fresh rows = subtypeQuery second input fresh rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [resourceFreeList, Bool.and_eq_true] at rowsSafe
      simp only [subtypeQuery, List.filterMap_cons]
      rw [subtypeRow_world first second input fresh inputSafe row rowsSafe.1]
      rw [show List.filterMap (subtypeRow first input fresh) rows =
        List.filterMap (subtypeRow second input fresh) rows from ih rowsSafe.2]

namespace Controls

def symbolGraph : ScopeGraph Nat where
  rows := fun node => if node = 0 then
    [.expression [.symbol ":", .symbol "f", .expression [.symbol "->", .var "t", .var "t", .symbol "R"]]]
    else [.expression [.symbol ":", .symbol "a", .symbol "Number"]]
  dependencies := fun node => if node = 0 then [1] else []
  intrinsicRows := []

theorem ordinary_variables_and_import_admitted :
    checkInput symbolGraph 2 0 (.expression [.symbol "f", .symbol "a", .symbol "a"]) = true := by decide

def mutableChildGraph : ScopeGraph Nat := { symbolGraph with
  rows := fun node => if node = 0 then symbolGraph.rows 0 else
    [.expression [.symbol ":", .symbol "a", RetainedTypePayloads.Controls.state "A"]] }

theorem mutable_child_annotation_declines : checkScope mutableChildGraph 2 0 = false := by decide

def mutableFormalGraph : ScopeGraph Nat := { symbolGraph with
  rows := fun _ => [.expression [.symbol ":", .symbol "f",
    .expression [.symbol "->", RetainedTypePayloads.Controls.state "A", .symbol "R"]]] }

theorem mutable_formal_declines : checkScope mutableFormalGraph 2 0 = false := by decide

def mutableSubtypeGraph : ScopeGraph Nat := { symbolGraph with
  rows := fun node => if node = 0 then symbolGraph.rows 0 else
    [.expression [.symbol ":<", .symbol "Number", RetainedTypePayloads.Controls.state "A"]] }

theorem mutable_subtype_declines : checkScope mutableSubtypeGraph 2 0 = false := by decide

theorem shallow_scope_cannot_certify_import : checkScope symbolGraph 1 0 = false := by decide

theorem headless_subtype_row_is_not_discarded :
    subtypeQuery RetainedTypePayloads.Controls.initial (.symbol "Number") "fresh"
      [.expression [.var "row-head", .symbol "Number", .symbol "R"]] = [.symbol "R"] := by
  cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeClosure
