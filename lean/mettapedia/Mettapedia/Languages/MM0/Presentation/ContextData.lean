import Mettapedia.Languages.MM0.Presentation.Data
import Mettapedia.Languages.MM0.Kernel.Typing
import Mathlib.Data.Finset.Sort

/-!
# MM0 declaration profiles as computational data

Bound and regular binders retain distinct tags. Dependencies are encoded in
increasing order by executable finite-set sorting; no choice of a list
representative is needed. Context order and all natural indices are retained.
These codecs prepare inputs for authored typing equations, not a host typing
primitive. Raw decoded profiles still require the kernel's admission checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalContext

open Kernel
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeNaturals (values : List Nat) : Term := .list (values.map natural)

def decodeNaturalItems : List Term → Option (List Nat)
  | [] => some []
  | first :: rest => do
      let value ← natural? first
      let values ← decodeNaturalItems rest
      pure (value :: values)

def decodeNaturals : Term → Option (List Nat)
  | .list values => decodeNaturalItems values
  | _ => none

@[simp] theorem decodeNaturalItems_encode (values : List Nat) :
    decodeNaturalItems (values.map natural) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [decodeNaturalItems, ih]

@[simp] theorem decodeNaturals_encode (values : List Nat) :
    decodeNaturals (encodeNaturals values) = some values := decodeNaturalItems_encode values

def encodeDependencies (dependencies : Finset Nat) : Term := encodeNaturals (dependencies.sort (· ≤ ·))

def decodeDependencies (data : Term) : Option (Finset Nat) :=
  (decodeNaturals data).map List.toFinset

@[simp] theorem decodeDependencies_encode (dependencies : Finset Nat) :
    decodeDependencies (encodeDependencies dependencies) = some dependencies := by
  simp [decodeDependencies, encodeDependencies]

def encodeBinder : Kernel.Binder → Term
  | .bound sort => .list [.sym "MM0:Bound", natural sort]
  | .regular sort dependencies =>
      .list [.sym "MM0:Regular", natural sort, encodeDependencies dependencies]

def decodeBinder : Term → Option Kernel.Binder
  | .list [.sym "MM0:Bound", sort] => (natural? sort).map Kernel.Binder.bound
  | .list [.sym "MM0:Regular", sort, dependencies] => do
      let sort ← natural? sort
      let dependencies ← decodeDependencies dependencies
      pure (.regular sort dependencies)
  | _ => none

@[simp] theorem decodeBinder_encode (binder : Kernel.Binder) :
    decodeBinder (encodeBinder binder) = some binder := by
  cases binder <;> simp [encodeBinder, decodeBinder]

def encodeContext (context : Context) : Term := .list (context.map encodeBinder)

def decodeBinderItems : List Term → Option Context
  | [] => some []
  | first :: rest => do
      let binder ← decodeBinder first
      let context ← decodeBinderItems rest
      pure (binder :: context)

def decodeContext : Term → Option Context
  | .list items => decodeBinderItems items
  | _ => none

@[simp] theorem decodeBinderItems_encode (context : Context) :
    decodeBinderItems (context.map encodeBinder) = some context := by
  induction context with
  | nil => rfl
  | cons first rest ih => simp [decodeBinderItems, ih]

@[simp] theorem decodeContext_encode (context : Context) :
    decodeContext (encodeContext context) = some context := decodeBinderItems_encode context

def encodeDeclaration (declaration : TermDecl) : Term :=
  .list [.sym "MM0:TermDecl", encodeContext declaration.arguments,
    natural declaration.resultSort, encodeDependencies declaration.dependencies]

def decodeDeclaration : Term → Option TermDecl
  | .list [.sym "MM0:TermDecl", arguments, sort, dependencies] => do
      let arguments ← decodeContext arguments
      let sort ← natural? sort
      let dependencies ← decodeDependencies dependencies
      pure ⟨arguments, sort, dependencies⟩
  | _ => none

@[simp] theorem decodeDeclaration_encode (declaration : TermDecl) :
    decodeDeclaration (encodeDeclaration declaration) = some declaration := by
  simp [decodeDeclaration, encodeDeclaration]

theorem encodeBinder_injective : Function.Injective encodeBinder := by
  intro first second same
  have decoded := congrArg decodeBinder same
  simpa using decoded

theorem encodeContext_injective : Function.Injective encodeContext := by
  intro first second same
  have decoded := congrArg decodeContext same
  simpa using decoded

theorem encodeDeclaration_injective : Function.Injective encodeDeclaration := by
  intro first second same
  have decoded := congrArg decodeDeclaration same
  simpa using decoded

theorem encodeNaturals_passive (P : Program) (H : Host) (values : List Nat) :
    PassiveData P H (encodeNaturals values) := by
  apply PassiveData.list
  intro item member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  exact natural_passive _ _ _

theorem encodeBinder_passive (P : Program) (H : Host) (binder : Kernel.Binder) :
    PassiveData P H (encodeBinder binder) := by
  cases binder <;> apply PassiveData.list <;> intro item member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .sym _
    · exact natural_passive _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .sym _
    · exact natural_passive _ _ _
    · exact encodeNaturals_passive _ _ _

theorem encodeContext_passive (P : Program) (H : Host) (context : Context) :
    PassiveData P H (encodeContext context) := by
  apply PassiveData.list
  intro item member
  obtain ⟨binder, _, rfl⟩ := List.mem_map.mp member
  exact encodeBinder_passive _ _ _

theorem bound_and_regular_remain_distinct (sort : Nat) (dependencies : Finset Nat) :
    encodeBinder (.bound sort) ≠ encodeBinder (.regular sort dependencies) := by
  intro same
  have impossible := encodeBinder_injective same
  cases impossible

theorem large_dependency_index_preserved :
    decodeBinder (encodeBinder (.regular 0 {18446744073709551616})) =
      some (.regular 0 {18446744073709551616}) := decodeBinder_encode _

theorem foreign_binder_tag_refuses :
    decodeBinder (.list [.sym "MM0:Free", natural 0]) = none := rfl

theorem missing_regular_dependencies_refuses :
    decodeBinder (.list [.sym "MM0:Regular", natural 0]) = none := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalContext
