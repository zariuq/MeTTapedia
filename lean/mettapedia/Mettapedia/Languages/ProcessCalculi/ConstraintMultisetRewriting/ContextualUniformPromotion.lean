import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSituatedFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority

/-!
# Uniform guarded expansion retains its installed schema prerequisites

A use records an actual activation of a named source schema and its prepared
contextual data. A finite plan computes its prerequisite list from those uses;
the list is not supplied by an inference-provenance assertion. Its guard
questions remain the original heterogeneous schedule questions.

Uniform families are built by single uses and composition. Installation keeps
their declared prerequisite coverage, requires publication authority at the
schema registry, and introduces a fresh schema name. Every invocation rechecks
its guards and situated rights. The construction certifies expansion into
existing steps; it does not infer an anti-unifier from one successful run.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open ContextualExecution ContextualSchedulePromotion

variable {S : Signature} {Local O R N : Type} (locals : Local → MetaArity S)
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}
  (Inputs : Endpoint locals O Γ sort → Type)

abbrev Activation := (before : Endpoint locals O Γ sort) → R → Inputs before →
  Option (RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))

abbrev Sites := (before : Endpoint locals O Γ sort) → R → Inputs before →
  Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort) → Finset N

variable (activate : Activation locals Inputs (R := R)) (sites : Sites locals Inputs (R := R) (N := N))

structure Use (before : Endpoint locals O Γ sort) : Type 1 where
  schema : R
  inputs : Inputs before
  prepared : Prepared locals before
  activated : activate before schema inputs = some prepared.rule

inductive Plan : Endpoint locals O Γ sort → Endpoint locals O Γ sort → Type 1
  | nil (before) : Plan before before
  | snoc {before middle} (past : Plan before middle) (next : Use locals Inputs activate middle) :
      Plan before next.prepared.target

namespace Plan

variable {locals Inputs activate sites}
  {source middle target : Endpoint locals O Γ sort}

def erase {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Plan locals Inputs activate source target → Certificate locals source target
  | _, .nil _ => .nil source
  | _, .snoc past next => .snoc past.erase next.prepared

def prerequisites {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Plan locals Inputs activate source target → List R
  | _, .nil _ => []
  | _, .snoc past next => past.prerequisites ++ [next.schema]

def append (first : Plan locals Inputs activate source middle) :
    {target : Endpoint locals O Γ sort} → Plan locals Inputs activate middle target →
      Plan locals Inputs activate source target
  | _, .nil _ => first
  | _, .snoc past next => .snoc (first.append past) next

theorem erase_append (first : Plan locals Inputs activate source middle)
    (second : Plan locals Inputs activate middle target) :
    (first.append second).erase = first.erase.append second.erase := by
  induction second with
  | nil => rfl
  | snoc past next earlier => simp only [append, erase, Certificate.append, earlier]

theorem prerequisites_append (first : Plan locals Inputs activate source middle)
    (second : Plan locals Inputs activate middle target) :
    (first.append second).prerequisites = first.prerequisites ++ second.prerequisites := by
  induction second with
  | nil => simp [append, prerequisites]
  | snoc past next earlier => simp only [append, prerequisites, earlier, List.append_assoc]

def Permissions (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) {source : Endpoint locals O Γ sort} :
    {target : Endpoint locals O Γ sort} → Plan locals Inputs activate source target → Prop
  | _, .nil _ => True
  | _, .snoc (middle := middle) past next => Permissions process location sites past ∧
      ContextualSituatedFormation.Authority process.rights location (sites middle next.schema next.inputs)
        (ContextualActivatedStep.prepared locals middle.declarations middle.occupied next.prepared.selection
          next.prepared.rule middle.inventory.rows).rule.checks
        next.prepared.selection middle.inventory.configuration.present

def Ready (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) (plan : Plan locals Inputs activate source target) : Prop :=
  (∀ schema ∈ plan.prerequisites, schema ∈ process.schemas) ∧
    plan.Permissions process location sites ∧ Checked locals plan.erase.questions

def realize (plan : Plan locals Inputs activate source target)
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) (ready : plan.Ready process location sites) :
    Quiver.Path source target := plan.erase.realize ready.2.2

end Plan

variable {locals Inputs activate sites}

def EdgeLicensed (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) {before after : Endpoint locals O Γ sort}
    (edge : Firing locals before after) : Prop :=
  ∃ schema ∈ process.schemas, ∃ inputs,
    activate before schema inputs = some edge.rule ∧
      ContextualSituatedFormation.Authority process.rights location (sites before schema inputs)
        (ContextualActivatedStep.prepared locals before.declarations before.occupied edge.selection
          edge.rule before.inventory.rows).rule.checks edge.selection before.inventory.configuration.present

def LicensedPath (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) {source : Endpoint locals O Γ sort} :
    {target : Endpoint locals O Γ sort} → Quiver.Path source target → Prop
  | _, .nil => True
  | _, .cons past edge => LicensedPath process location sites past ∧ EdgeLicensed (activate := activate) process location sites edge

namespace Plan

variable {source target : Endpoint locals O Γ sort}

theorem realize_licensed (plan : Plan locals Inputs activate source target)
    (process : SchemaPublicationAuthority.Process R N) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N)) (ready : plan.Ready process location sites) :
    LicensedPath (activate := activate) process location sites (plan.realize process location sites ready) := by
  induction plan with
  | nil => trivial
  | snoc past next earlier =>
      have checked := (checked_append_iff locals past.erase.questions next.prepared.questions).mp ready.2.2
      have oldReady : past.Ready process location sites :=
        ⟨fun schema member => ready.1 schema (List.mem_append_left _ member), ready.2.1.1, checked.1⟩
      refine ⟨earlier oldReady, next.schema, ready.1 next.schema (List.mem_append_right _ (List.mem_singleton_self _)),
        next.inputs, next.activated, ready.2.1.2⟩

end Plan

variable {Parameter : Type} {source middle target : Parameter → Endpoint locals O Γ sort}

/-- Prerequisite coverage refers to the actual activated uses of every input's
data expansion. It does not assume guard acceptance or source execution. -/
structure Family (source target : Parameter → Endpoint locals O Γ sort) : Type 1 where
  body : ∀ input, Plan locals Inputs activate (source input) (target input)
  requires : List R
  covers : ∀ input schema, schema ∈ (body input).prerequisites → schema ∈ requires

namespace Family

def single (schema : R) (source : Parameter → Endpoint locals O Γ sort)
    (inputs : ∀ input, Inputs (source input)) (prepared : ∀ input, Prepared locals (source input))
    (activated : ∀ input, activate (source input) schema (inputs input) = some (prepared input).rule) :
    Family (locals := locals) (Inputs := Inputs) (activate := activate) source (fun input => (prepared input).target) where
  body input := .snoc (.nil (source input)) ⟨schema, inputs input, prepared input, activated input⟩
  requires := [schema]
  covers _ _ member := member

def append (first : Family (locals := locals) (Inputs := Inputs) (activate := activate) source middle)
    (second : Family (locals := locals) (Inputs := Inputs) (activate := activate) middle target) :
    Family (locals := locals) (Inputs := Inputs) (activate := activate) source target where
  body input := (first.body input).append (second.body input)
  requires := first.requires ++ second.requires
  covers input schema member := by
    rw [Plan.prerequisites_append] at member
    rcases List.mem_append.mp member with left | right
    · exact List.mem_append_left _ (first.covers input schema left)
    · exact List.mem_append_right _ (second.covers input schema right)

/-- Process-side name and prerequisite availability. This predicate alone
does not associate the name with this definition; the typed definition
registry supplies that lookup boundary. -/
def Installed (process : SchemaPublicationAuthority.Process R N) (name : R)
    (family : Family (locals := locals) (Inputs := Inputs) (activate := activate) source target) : Prop :=
  name ∈ process.schemas ∧ ∀ required ∈ family.requires, required ∈ process.schemas

theorem ready_at_each_use (process : SchemaPublicationAuthority.Process R N) (name : R)
    (family : Family (locals := locals) (Inputs := Inputs) (activate := activate) source target)
    (installed : family.Installed process name) (input : Parameter) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N))
    (permissions : (family.body input).Permissions process location sites)
    (guards : Checked locals (family.body input).erase.questions) :
    (family.body input).Ready process location sites :=
  ⟨fun schema member => installed.2 schema (family.covers input schema member), permissions, guards⟩

theorem realizes_each_checked_use (process : SchemaPublicationAuthority.Process R N) (name : R)
    (family : Family (locals := locals) (Inputs := Inputs) (activate := activate) source target)
    (installed : family.Installed process name) (input : Parameter) (location : O → N)
    (sites : Sites locals Inputs (R := R) (N := N))
    (permissions : (family.body input).Permissions process location sites)
    (guards : Checked locals (family.body input).erase.questions) :
    ∃ path : Quiver.Path (source input) (target input),
      LicensedPath (activate := activate) process location sites path := by
  let ready := family.ready_at_each_use process name installed input location sites permissions guards
  exact ⟨(family.body input).realize process location sites ready,
    (family.body input).realize_licensed process location sites ready⟩

end Family

def register (process : SchemaPublicationAuthority.Process R N) (name : R) :
    SchemaPublicationAuthority.Process R N := ⟨process.rights, name :: process.schemas⟩

structure Installation (process : SchemaPublicationAuthority.Process R N) (registry : N) (name : R)
    (family : Family (locals := locals) (Inputs := Inputs) (activate := activate) source target) : Prop where
  may_publish : process.rights registry .send = true
  fresh_name : name ∉ process.schemas
  prerequisites : ∀ required ∈ family.requires, required ∈ process.schemas

theorem installation_retains_prerequisites (process : SchemaPublicationAuthority.Process R N)
    (registry : N) (name : R)
    (family : Family (locals := locals) (Inputs := Inputs) (activate := activate) source target)
    (installed : Installation process registry name family) : family.Installed (register process name) name :=
  ⟨List.mem_cons_self, fun required member => List.mem_cons_of_mem _ (installed.prerequisites required member)⟩

theorem installation_requires_registry_send (process : SchemaPublicationAuthority.Process R N)
    (registry : N) (name : R)
    (family : Family (locals := locals) (Inputs := Inputs) (activate := activate) source target)
    (denied : process.rights registry .send = false) : ¬ Installation process registry name family := by
  intro installed
  have allowed := installed.may_publish
  rw [denied] at allowed
  cases allowed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformPromotion
