import Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
import Mettapedia.Machines.RevisionDependencySet

/-!
# Explicit names for versioned and live value contexts

A reference either names one context version or explicitly selects the live
revision of a name. The context table and live revision selector are separate
inputs. Publication below rejects replacement of an occupied version, so an
existing versioned reference retains its interpretation across accepted
publications and changes of the live selector.

Inspection reads a caller-selected finite binding footprint. Execution is a
separate operation supplied with an evaluator. The construction does not
select a default reference mode, copy a reachable heap, or retain execution
history. A context may itself contain handles whose operational meaning is
outside these lexical lookup laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NamedValueContexts

open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

universe uContext uCode uKey uValue uResult

variable {Name Revision : Type} {Context : Type uContext}
variable {Code : Type uCode} {Key : Type uKey} {Value : Type uValue}
variable {Result : Type uResult}

/-- Reference mode is explicit; neither constructor is a language default. -/
inductive Reference (Name Revision : Type) where
  | versioned (version : StoreReadToken Name Revision)
  | live (name : Name)
deriving DecidableEq

abbrev ContextTable (Name Revision : Type) (Context : Type uContext) :=
  SourceEnvironment (StoreReadToken Name Revision) Context

def resolve (table : ContextTable Name Revision Context)
    (current : RevisionEnvironment Name Revision) : Reference Name Revision → Option Context
  | .versioned version => table version
  | .live name => table ⟨name, current.current name⟩

/-- Capture the currently selected version, not the transitive contents of
any mutable handles that its lexical bindings may contain. -/
def capture (current : RevisionEnvironment Name Revision) (name : Name) :
    Reference Name Revision := .versioned ⟨name, current.current name⟩

theorem resolve_capture (table : ContextTable Name Revision Context)
    (current : RevisionEnvironment Name Revision) (name : Name) :
    resolve table current (capture current name) = resolve table current (.live name) := rfl

theorem versioned_resolution_ignores_live_selector
    (table : ContextTable Name Revision Context)
    (first second : RevisionEnvironment Name Revision) (version : StoreReadToken Name Revision) :
    resolve table first (.versioned version) = resolve table second (.versioned version) := rfl

theorem live_resolution_update_other [DecidableEq Name]
    (table : ContextTable Name Revision Context) (current : RevisionEnvironment Name Revision)
    (observed changed : Name) (revision : Revision) (different : observed ≠ changed) :
    resolve table (current.update changed revision) (.live observed) =
      resolve table current (.live observed) := by
  simp [resolve, RevisionEnvironment.update, different]

/-! ## Fresh version publication -/

/-- An executable freshness check, not a field assuming publication safety.
The finite-environment write is used only after its target is absent. -/
def publishVersion? [DecidableEq Name] [DecidableEq Revision]
    (table : ContextTable Name Revision Context) (version : StoreReadToken Name Revision)
    (context : Context) : Option (ContextTable Name Revision Context) :=
  if (table version).isNone then some (writeSource table (version, context)) else none

theorem publishVersion?_eq_some_iff [DecidableEq Name] [DecidableEq Revision]
    (table updated : ContextTable Name Revision Context)
    (version : StoreReadToken Name Revision) (context : Context) :
    publishVersion? table version context = some updated ↔
      table version = none ∧ updated = writeSource table (version, context) := by
  cases found : table version <;> simp [publishVersion?, found, eq_comm]

theorem publishVersion?_rejects_occupied [DecidableEq Name] [DecidableEq Revision]
    (table : ContextTable Name Revision Context) (version : StoreReadToken Name Revision)
    (old replacement : Context) (occupied : table version = some old) :
    publishVersion? table version replacement = none := by
  simp [publishVersion?, occupied]

theorem published_version_resolves [DecidableEq Name] [DecidableEq Revision]
    (table updated : ContextTable Name Revision Context)
    (version : StoreReadToken Name Revision) (context : Context)
    (published : publishVersion? table version context = some updated) :
    updated version = some context := by
  rw [(publishVersion?_eq_some_iff table updated version context).mp published |>.2]
  simp [writeSource]

/-- Every occupied version survives an accepted fresh publication. No claim
is made about arbitrary table replacement outside this operation. -/
theorem publication_preserves_existing [DecidableEq Name] [DecidableEq Revision]
    (table updated : ContextTable Name Revision Context)
    (newVersion oldVersion : StoreReadToken Name Revision) (newContext oldContext : Context)
    (published : publishVersion? table newVersion newContext = some updated)
    (existing : table oldVersion = some oldContext) : updated oldVersion = some oldContext := by
  obtain ⟨fresh, rfl⟩ :=
    (publishVersion?_eq_some_iff table updated newVersion newContext).mp published
  have different : oldVersion ≠ newVersion := by
    intro same
    rw [same, fresh] at existing
    cases existing
  simp [writeSource, different, existing]

theorem versioned_resolution_preserved [DecidableEq Name] [DecidableEq Revision]
    (table updated : ContextTable Name Revision Context)
    (before after : RevisionEnvironment Name Revision)
    (newVersion oldVersion : StoreReadToken Name Revision) (newContext oldContext : Context)
    (published : publishVersion? table newVersion newContext = some updated)
    (existing : resolve table before (.versioned oldVersion) = some oldContext) :
    resolve updated after (.versioned oldVersion) = some oldContext :=
  publication_preserves_existing table updated newVersion oldVersion newContext oldContext
    published existing

/-! ## Finite, pure binding inspection -/

/-- Missing names stay visible as `none`; inspection neither evaluates a
binding nor claims the requested footprint is a complete environment. -/
def inspectBindings (environment : SourceEnvironment Key Value) (footprint : List Key) :
    List (Key × Option Value) := footprint.map (fun key => (key, environment key))

theorem inspectBindings_eq_iff (left right : SourceEnvironment Key Value)
    (footprint : List Key) :
    inspectBindings left footprint = inspectBindings right footprint ↔
      ∀ key ∈ footprint, left key = right key := by
  simp [inspectBindings, List.map_inj_left]

/-- A write outside the inspected footprint preserves the exact ordered
inspection, without requiring equality of the whole value environment. -/
theorem inspectBindings_write_unrelated [DecidableEq Key]
    (environment : SourceEnvironment Key Value) (footprint : List Key)
    (changed : Key) (value : Value) (outside : changed ∉ footprint) :
    inspectBindings (writeSource environment (changed, value)) footprint =
      inspectBindings environment footprint := by
  apply (inspectBindings_eq_iff _ _ _).mpr
  intro key member
  have different : key ≠ changed := fun equal => outside (equal ▸ member)
  simp [writeSource, different]

/-- An ordinary code object has an explicit named context reference. -/
structure NamedCode (Name Revision : Type) (Code : Type uCode) where
  code : Code
  context : Reference Name Revision

/-- Resolve code and selected bindings only. There is no evaluator argument
and no execution state, so this operation cannot invoke the code. -/
def inspect (table : ContextTable Name Revision Context)
    (current : RevisionEnvironment Name Revision) (lookup : Context → SourceEnvironment Key Value)
    (object : NamedCode Name Revision Code) (footprint : List Key) :
    Option (Code × List (Key × Option Value)) :=
  (resolve table current object.context).map fun context =>
    (object.code, inspectBindings (lookup context) footprint)

/-- Execution is explicitly requested and uses a separately supplied source
evaluator. The outer option reports unresolved context, not evaluator failure. -/
def execute (table : ContextTable Name Revision Context)
    (current : RevisionEnvironment Name Revision) (evaluate : Code → Context → Result)
    (object : NamedCode Name Revision Code) : Option Result :=
  (resolve table current object.context).map (evaluate object.code)

theorem execute_resolved (table : ContextTable Name Revision Context)
    (current : RevisionEnvironment Name Revision) (evaluate : Code → Context → Result)
    (object : NamedCode Name Revision Code) (context : Context)
    (found : resolve table current object.context = some context) :
    execute table current evaluate object = some (evaluate object.code context) := by
  simp [execute, found]

/-- Inspection retains exactly the quoted source, even when different
source programs compute the same result. -/
theorem inspect_source (table : ContextTable Name Revision Context)
    (current : RevisionEnvironment Name Revision) (lookup : Context → SourceEnvironment Key Value)
    (object : NamedCode Name Revision Code) (footprint : List Key)
    (observed : Code × List (Key × Option Value))
    (inspected : inspect table current lookup object footprint = some observed) :
    observed.1 = object.code := by
  unfold inspect at inspected
  cases found : resolve table current object.context with
  | none => simp [found] at inspected
  | some context =>
      simp only [found, Option.map_some, Option.some.injEq] at inspected
      exact (congrArg Prod.fst inspected).symm

#print axioms publication_preserves_existing
#print axioms versioned_resolution_preserved
#print axioms inspectBindings_eq_iff
#print axioms inspectBindings_write_unrelated
#print axioms inspect_source

end Mettapedia.TypeTheory.NamedValueContexts
