import Mettapedia.GSLT.LanguageDef.ExecutableProtocolSafety

/-!
# Resource-indexed executable protocol facts

Version-two protocol plans retain instance identities separately from linear
owner tokens. A hook may read or write named instances. Facts declare the
instances on which their current truth depends. A write conservatively forgets
every overlapping fact on both Boolean branches; an explicit proof hook may
establish it again on its successful branch.

This does not identify historical truth with current storage. A fact without a
currentness dependency remains stable under an unrelated write. Linear resource
claims use the existing acquire/release/transfer semantics. Bound-owner metadata
records the native predicate used to re-observe the persistent owner.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Resources

open Mettapedia.GSLT.LanguageDef.ExecutableProtocol

structure HookAccess where
  hook : String
  reads : List String
  writes : List String
  deriving DecidableEq, Repr

structure Dependency where
  fact : String
  instances : List String
  deriving DecidableEq, Repr

structure BoundOwner where
  resource : String
  predicate : String
  deriving DecidableEq, Repr

structure BoundPlan where
  base : Protocol
  instances : List String
  accesses : List HookAccess
  dependencies : List Dependency
  owners : List BoundOwner
  deriving DecidableEq, Repr

def findAccess (plan : BoundPlan) (hook : String) : HookAccess :=
  (plan.accesses.find? (·.hook == hook)).getD ⟨hook, [], []⟩

def dependsOn (plan : BoundPlan) (fact location : String) : Bool :=
  plan.dependencies.any fun dependency =>
    dependency.fact == fact && dependency.instances.contains location

def invalidated (plan : BoundPlan) (hook : Hook) (fact : String) : Bool :=
  hook.invalidates.contains fact ||
    (findAccess plan hook.id).writes.any fun location => dependsOn plan fact location

def callContext (plan : BoundPlan) (c : Context) (hook : Hook) (reply : Bool) : Context :=
  { c with
    facts := (if reply then hook.proves else []) ++
      c.facts.filter (fun fact => !invalidated plan hook fact)
    irreversible := c.irreversible || hook.kind == .effect }

def declaredFacts (p : Protocol) : List String :=
  (p.entryFacts ++ p.hooks.flatMap fun hook =>
    hook.requires ++ hook.proves ++ hook.invalidates).eraseDups

def checkAccess (plan : BoundPlan) (access : HookAccess) : Bool :=
  (plan.base.hooks.any (·.id == access.hook)) &&
  decide access.reads.Nodup && decide access.writes.Nodup &&
  access.reads.all plan.instances.contains &&
  access.writes.all plan.instances.contains

def checkDependency (plan : BoundPlan) (dependency : Dependency) : Bool :=
  (declaredFacts plan.base).contains dependency.fact &&
  !dependency.instances.isEmpty && decide dependency.instances.Nodup &&
  dependency.instances.all plan.instances.contains

def checkOwner (plan : BoundPlan) (owner : BoundOwner) : Bool :=
  plan.base.resources.any (·.id == owner.resource) && !owner.predicate.isEmpty

def checkBody (plan : BoundPlan) : Context → Body → Bool
  | c, .ret outcome => c.owned.isEmpty &&
      (!c.irreversible || outcome != .declined) &&
      (exitRequires plan.base outcome).all c.facts.contains
  | c, .call id yes no =>
      match findHook plan.base id with
      | none => false
      | some hook => hook.requires.all c.facts.contains &&
          hook.uses.all c.owned.contains &&
          checkBody plan (callContext plan c hook true) yes &&
          checkBody plan (callContext plan c hook false) no
  | c, .acquire id yes no =>
      match findResource plan.base id with
      | none => false
      | some resource => !c.owned.contains id &&
          resource.acquireRequires.all c.facts.contains &&
          checkBody plan (acquireContext c id true) yes &&
          checkBody plan (acquireContext c id false) no
  | c, .release id next =>
      (findResource plan.base id).isSome && c.owned.contains id &&
        checkBody plan (disposeContext c id) next
  | c, .transfer id next =>
      match findResource plan.base id with
      | none => false
      | some resource => c.owned.contains id &&
          resource.transferRequires.all c.facts.contains &&
          checkBody plan (transferContext c id) next

def checkBoundPlan (plan : BoundPlan) : Bool :=
  checkMetadata plan.base && checkBody plan (initial plan.base) plan.base.body &&
  decide plan.instances.Nodup &&
  decide (plan.accesses.map HookAccess.hook).Nodup &&
  decide (plan.dependencies.map Dependency.fact).Nodup &&
  decide (plan.owners.map BoundOwner.resource).Nodup &&
  plan.accesses.all (checkAccess plan) &&
  plan.dependencies.all (checkDependency plan) &&
  plan.owners.all (checkOwner plan)

structure BoundPlanValid (plan : BoundPlan) : Prop where
  metadata : MetadataValid plan.base
  body : checkBody plan (initial plan.base) plan.base.body = true
  instances : plan.instances.Nodup
  accessUnique : (plan.accesses.map HookAccess.hook).Nodup
  dependencyUnique : (plan.dependencies.map Dependency.fact).Nodup
  ownerUnique : (plan.owners.map BoundOwner.resource).Nodup
  access : ∀ item ∈ plan.accesses, checkAccess plan item = true
  dependency : ∀ item ∈ plan.dependencies, checkDependency plan item = true
  owner : ∀ item ∈ plan.owners, checkOwner plan item = true

theorem checkBoundPlan_iff (plan : BoundPlan) :
    checkBoundPlan plan = true ↔ BoundPlanValid plan := by
  simp only [checkBoundPlan, Bool.and_eq_true, checkMetadata_iff, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨metadata, body⟩, instances⟩, accessUnique⟩, dependencyUnique⟩, ownerUnique⟩,
      access⟩, dependency⟩, owner⟩
    exact ⟨metadata, body, instances, accessUnique, dependencyUnique, ownerUnique,
      fun item member => access item member,
      fun item member => dependency item member,
      fun item member => owner item member⟩
  · rintro ⟨metadata, body, instances, accessUnique, dependencyUnique, ownerUnique,
      access, dependency, owner⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨metadata, body⟩, instances⟩, accessUnique⟩, dependencyUnique⟩, ownerUnique⟩,
      access⟩, dependency⟩, owner⟩

theorem dependsOn_of_mem (plan : BoundPlan) (dependency : Dependency)
    (member : dependency ∈ plan.dependencies) (location : String)
    (read : location ∈ dependency.instances) :
    dependsOn plan dependency.fact location = true := by
  rw [dependsOn, List.any_eq_true]
  exact ⟨dependency, member, by simp [read]⟩

theorem written_dependency_invalidated (plan : BoundPlan) (hook : Hook)
    (dependency : Dependency) (member : dependency ∈ plan.dependencies)
    (location : String) (written : location ∈ (findAccess plan hook.id).writes)
    (dependent : location ∈ dependency.instances) :
    invalidated plan hook dependency.fact = true := by
  simp only [invalidated, Bool.or_eq_true]
  right
  rw [List.any_eq_true]
  exact ⟨location, written, dependsOn_of_mem plan dependency member location dependent⟩

theorem invalidated_absent (plan : BoundPlan) (c : Context) (hook : Hook)
    (reply : Bool) (fact : String) (forgotten : invalidated plan hook fact = true)
    (notReproved : reply = true → fact ∉ hook.proves) :
    fact ∉ (callContext plan c hook reply).facts := by
  cases reply <;> simp_all [callContext]

theorem unrelated_fact_preserved (plan : BoundPlan) (c : Context) (hook : Hook)
    (reply : Bool) (fact : String) (known : fact ∈ c.facts)
    (stable : invalidated plan hook fact = false) :
    fact ∈ (callContext plan c hook reply).facts := by
  cases reply <;> simp [callContext, stable, known]

theorem successful_refresh_reestablishes (plan : BoundPlan) (c : Context)
    (hook : Hook) (fact : String) (proved : fact ∈ hook.proves) :
    fact ∈ (callContext plan c hook true).facts := by
  simp [callContext, proved]

theorem changed_bound_plan_refused {plan : BoundPlan} (_valid : BoundPlanValid plan)
    (changed : BoundPlan) (different : checkBoundPlan changed = false) :
    checkBoundPlan changed = false := different

namespace Controls

def observe : Hook := ⟨"observe", "observe_c", .guard, [], [], ["current"], []⟩
def mutate : Hook := ⟨"mutate", "mutate_c", .effect, ["current"], [], [], []⟩
def refresh : Hook := ⟨"refresh", "refresh_c", .guard, [], [], ["current"], []⟩

def base : Protocol := {
  name := "bound"
  contextType := "Context"
  hooks := [observe, mutate, refresh]
  resources := []
  entryFacts := []
  entryOwned := []
  body := .ret .done
}

def plan : BoundPlan := {
  base
  instances := ["store"]
  accesses := [⟨"observe", ["store"], []⟩, ⟨"mutate", [], ["store"]⟩,
    ⟨"refresh", ["store"], []⟩]
  dependencies := [⟨"current", ["store"]⟩]
  owners := []
}

theorem write_forgets_current :
    "current" ∉ (callContext plan ⟨["current"], [], false⟩ mutate true).facts := by decide

theorem read_preserves_current :
    "current" ∈ (callContext plan ⟨["current"], [], false⟩ observe false).facts := by decide

theorem refresh_restores_current :
    "current" ∈ (callContext plan ⟨[], [], true⟩ refresh true).facts := by decide

end Controls

#print axioms checkBoundPlan_iff
#print axioms written_dependency_invalidated
#print axioms invalidated_absent
#print axioms unrelated_fact_preserved

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol.Resources
