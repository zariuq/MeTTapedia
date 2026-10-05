import Mettapedia.Languages.MeTTa.HE.ModuleSpace
import Mettapedia.Machines.OrderedDependencyStore
import Mettapedia.Machines.OrderedDependencyProjection
import Mettapedia.Machines.OrderedDependencyOverlay

/-!
# HE module observations and finite store notifications

The generic finite store embeds into the existing HE module-space semantics.
Every dependency has an in-range identity. Out-of-range natural IDs are absent
from the embedded finite store and cannot occur in an embedded node's imports.

An accepted read stamp after the executable store update algorithm preserves the
existing ordered HE module observation, including its annotation lookups. This
is an adapter theorem for the model, not a refinement proof for C execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ModuleInvalidation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

open Mettapedia.Machines
open Mettapedia.Machines.OrderedDependencyStore

variable {size : Nat}

def ownStore (s : Store Atom size) : ModuleStore := fun identity =>
  if bound : identity < size then ⟨(s.members ⟨identity, bound⟩).own⟩ else ⟨[]⟩

def moduleNode (s : Store Atom size) (reader : Fin size) : ModuleNode :=
  ⟨⟨(s.members reader).own⟩, (s.members reader).deps.map Fin.val⟩

@[simp] theorem ownStore_member (s : Store Atom size) (source : Fin size) :
    (ownStore s source.val).atoms = (s.members source).own := by
  simp [ownStore, source.isLt]

theorem module_observation_eq (s : Store Atom size) (reader : Fin size) :
    (moduleNode s reader).view (ownStore s) = view s reader := by
  simp [ModuleNode.view, ModuleStore.depAtoms, moduleNode, view,
    List.flatMap_map]

theorem finite_query_realizes_module_observation
    (s : Store Atom size) (reader : Fin size) :
    query s reader = (moduleNode s reader).view (ownStore s) := by
  rw [query_eq_view, module_observation_eq]

/-- On an acyclic import, the finite store's identity insertion is the existing
HE module insertion. The finite algorithm also filters a reader from its own
imports, so the acyclic hypotheses are needed for this comparison. -/
theorem finite_import_realizes_module_import
    (s : Store Atom size) (reader source : Fin size)
    (different : reader ≠ source)
    (acyclic : reader ∉ (s.members source).deps) :
    moduleNode (importModule s reader source) reader =
      (moduleNode s reader).importModule source.val
        ((s.members source).deps.map Fin.val) := by
  have membership : source.val ∈ (s.members reader).deps.map Fin.val ↔
      source ∈ (s.members reader).deps := by
    rw [List.mem_map]
    constructor
    · rintro ⟨member, included, same⟩
      exact Fin.val_injective same ▸ included
    · intro included
      exact ⟨source, included, rfl⟩
  have filtered : ((source :: (s.members source).deps).filter
      fun member => member ≠ reader) = source :: (s.members source).deps := by
    apply List.filter_eq_self.mpr
    intro member included
    simp only [decide_eq_true_eq]
    intro same
    subst member
    rcases List.mem_cons.mp included with same | included
    · exact different same
    · exact acyclic included
  calc
    moduleNode (importModule s reader source) reader =
        ⟨⟨(s.members reader).own⟩, (moduleDependencies s reader source).map Fin.val⟩ := by
      simp [moduleNode, importModule, setDependencies_own]
    _ = _ := by
      by_cases present : source ∈ (s.members reader).deps
      · simp [ModuleNode.importModule, moduleNode, moduleDependencies,
          present, membership]
      · rw [moduleDependencies, if_neg (by simp [different, present]), filtered,
          OrderedDependencyIds.map_insertDeps Fin.val Fin.val_injective]
        simp [ModuleNode.importModule, moduleNode, membership, present,
          ModuleNode.insertDeps]

theorem validated_module_observation (s : Store Atom size)
    (h : ObserverInvariant s) (actions : List (Action Atom size))
    (reader : Fin size)
    (valid : checkRead (execute s actions) (readStamp s reader) = true) :
    (moduleNode (execute s actions) reader).view (ownStore (execute s actions)) =
      (moduleNode s reader).view (ownStore s) := by
  rw [← finite_query_realizes_module_observation,
    ← finite_query_realizes_module_observation]
  exact validated_query s h actions reader valid

theorem validated_annotation_lookup (s : Store Atom size)
    (h : ObserverInvariant s) (actions : List (Action Atom size))
    (reader : Fin size) (subject : Atom)
    (valid : checkRead (execute s actions) (readStamp s reader) = true) :
    getAnnotatedTypes ((moduleNode (execute s actions) reader).toSpace
      (ownStore (execute s actions))) subject =
    getAnnotatedTypes ((moduleNode s reader).toSpace (ownStore s)) subject := by
  have equal := validated_module_observation s h actions reader valid
  exact congrArg (fun atoms => getAnnotatedTypes ⟨atoms⟩ subject) equal

inductive ModuleProjection where
  | equations
  | annotations (subject : Atom)
  deriving DecidableEq

/-- Equation syntax and subject-specific type annotations are separate
observations. This does not freshen or execute the selected equations. -/
def project : ModuleProjection → Atom → Option Atom
  | .equations, atom => if Space.isEquation atom then some atom else none
  | .annotations subject, atom =>
    match atom with
    | .expression [.symbol ":", annotated, type] =>
      if annotated == subject then some type else none
    | _ => none

theorem projected_annotation_query_realizes_lookup
    (s : OrderedDependencyProjection.State Atom ModuleProjection size)
    (reader : Fin size) (subject : Atom) :
    OrderedDependencyProjection.query project s reader (.annotations subject) =
      getAnnotatedTypes ((moduleNode s.store reader).toSpace (ownStore s.store)) subject := by
  unfold OrderedDependencyProjection.query
  rw [finite_query_realizes_module_observation]
  rfl

theorem validated_projected_annotation_lookup
    (s : OrderedDependencyProjection.State Atom ModuleProjection size)
    (h : ObserverInvariant s.store) (actions : List (Action Atom size))
    (reader : Fin size) (subject : Atom)
    (valid : OrderedDependencyProjection.checkStamp
      (OrderedDependencyProjection.execute project s actions)
      (OrderedDependencyProjection.stamp s reader (.annotations subject)) = true) :
    getAnnotatedTypes ((moduleNode
      (OrderedDependencyProjection.execute project s actions).store reader).toSpace
      (ownStore (OrderedDependencyProjection.execute project s actions).store)) subject =
      getAnnotatedTypes ((moduleNode s.store reader).toSpace (ownStore s.store)) subject := by
  rw [← projected_annotation_query_realizes_lookup,
    ← projected_annotation_query_realizes_lookup]
  exact OrderedDependencyProjection.validated_query project s h actions reader
    (.annotations subject) valid

theorem validated_projected_equation_syntax
    (s : OrderedDependencyProjection.State Atom ModuleProjection size)
    (h : ObserverInvariant s.store) (actions : List (Action Atom size))
    (reader : Fin size)
    (valid : OrderedDependencyProjection.checkStamp
      (OrderedDependencyProjection.execute project s actions)
      (OrderedDependencyProjection.stamp s reader .equations) = true) :
    OrderedDependencyProjection.query project
      (OrderedDependencyProjection.execute project s actions) reader .equations =
      OrderedDependencyProjection.query project s reader .equations :=
  OrderedDependencyProjection.validated_query project s h actions reader .equations valid

end Mettapedia.Languages.MeTTa.HE.ModuleInvalidation
