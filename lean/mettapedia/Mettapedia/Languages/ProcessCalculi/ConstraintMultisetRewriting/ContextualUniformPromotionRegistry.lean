import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotionAuthority

/-!
# Named uniform definitions and authorized lookup

A list of installed names cannot identify which expansion a name denotes.
This registry stores the actual parameter family and its typed expansion.
Fresh registration preserves every earlier lookup and every primitive
prerequisite. Invocation executes the looked-up body and rechecks its own
guard questions and situated rights.

The registry certifies finite expansion into installed source activations.
It does not synthesize a generalization or grant publication authority from
an inference-provenance fact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion

variable {S : Signature} {Local O R N : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq R]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}
  {Inputs : Endpoint locals O Γ sort → Type}
  {activate : Activation locals Inputs (R := R)}

structure Definition (locals : Local → MetaArity S)
    (Inputs : Endpoint locals O Γ sort → Type) (activate : Activation locals Inputs (R := R)) : Type 1 where
  Parameter : Type
  source : Parameter → Endpoint locals O Γ sort
  target : Parameter → Endpoint locals O Γ sort
  family : Family (locals := locals) (Inputs := Inputs) (activate := activate) source target

structure Registry (locals : Local → MetaArity S)
    (Inputs : Endpoint locals O Γ sort → Type) (activate : Activation locals Inputs (R := R)) (N : Type) : Type 1 where
  process : SchemaPublicationAuthority.Process R N
  definitions : List (R × Definition locals Inputs activate)

namespace Registry

def lookupList (name : R) : List (R × Definition locals Inputs activate) → Option (Definition locals Inputs activate)
  | [] => none
  | (key, definition) :: rest => if name = key then some definition else lookupList name rest

def lookup (registry : Registry locals Inputs activate N) (name : R) : Option (Definition locals Inputs activate) :=
  lookupList name registry.definitions

def WellFormed (registry : Registry locals Inputs activate N) : Prop :=
  ∀ name definition, registry.lookup name = some definition →
    name ∈ registry.process.schemas ∧
      ∀ required ∈ definition.family.requires, required ∈ registry.process.schemas

def insert (registry : Registry locals Inputs activate N) (name : R)
    (definition : Definition locals Inputs activate) : Registry locals Inputs activate N :=
  ⟨register registry.process name, (name, definition) :: registry.definitions⟩

theorem lookup_insert (registry : Registry locals Inputs activate N) (name : R)
    (definition : Definition locals Inputs activate) :
    (registry.insert name definition).lookup name = some definition := by
  simp [lookup, insert, lookupList]

theorem lookup_insert_other (registry : Registry locals Inputs activate N) (name query : R)
    (definition : Definition locals Inputs activate) (different : query ≠ name) :
    (registry.insert name definition).lookup query = registry.lookup query := by
  simp [lookup, insert, lookupList, different]

theorem lookup_unavailable (registry : Registry locals Inputs activate N)
    (well : registry.WellFormed) (name : R) (missing : name ∉ registry.process.schemas) :
    registry.lookup name = none := by
  cases found : registry.lookup name with
  | none => rfl
  | some definition => exact False.elim (missing (well name definition found).1)

theorem authorized_insert_preserves_registry (registry : Registry locals Inputs activate N)
    (well : registry.WellFormed) (registrySite : N) (name : R)
    (definition : Definition locals Inputs activate)
    (authorized : Installation registry.process registrySite name definition.family) :
    (registry.insert name definition).WellFormed := by
  intro query found lookupFound
  by_cases same : query = name
  · subst query
    rw [lookup_insert] at lookupFound
    cases Option.some.inj lookupFound
    exact installation_retains_prerequisites registry.process registrySite name definition.family authorized
  · rw [lookup_insert_other registry name query definition same] at lookupFound
    obtain ⟨registered, prerequisites⟩ := well query found lookupFound
    exact ⟨List.mem_cons_of_mem _ registered,
      fun required member => List.mem_cons_of_mem _ (prerequisites required member)⟩

theorem authorized_insert_keeps_each_previous_definition (registry : Registry locals Inputs activate N)
    (well : registry.WellFormed) (registrySite : N) (name : R)
    (definition : Definition locals Inputs activate)
    (authorized : Installation registry.process registrySite name definition.family)
    (query : R) (old : Definition locals Inputs activate) (found : registry.lookup query = some old) :
    (registry.insert name definition).lookup query = some old := by
  have different : query ≠ name := by
    intro same
    subst query
    exact authorized.fresh_name (well name old found).1
  rw [lookup_insert_other registry name query definition different]
  exact found

theorem checked_lookup_has_the_original_authorized_execution
    (registry : Registry locals Inputs activate N) (well : registry.WellFormed)
    (name : R) (definition : Definition locals Inputs activate)
    (found : registry.lookup name = some definition) (input : definition.Parameter)
    (location : O → N) (sites : Sites locals Inputs (R := R) (N := N))
    (permissions : (definition.family.body input).Permissions registry.process location sites)
    (guards : Checked locals (definition.family.body input).erase.questions) :
    ∃ path : Quiver.Path (definition.source input) (definition.target input),
      LicensedPath (activate := activate) registry.process location sites path :=
  definition.family.realizes_each_checked_use registry.process name (well name definition found)
    input location sites permissions guards

theorem same_name_cannot_select_a_different_definition
    (registry : Registry locals Inputs activate N) (name : R)
    (first second : Definition locals Inputs activate)
    (firstFound : registry.lookup name = some first) (secondFound : registry.lookup name = some second) :
    first = second := Option.some.inj (firstFound.symm.trans secondFound)

end Registry

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotion
