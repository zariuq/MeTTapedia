import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets

/-!
# Contextual formation with scopes, declared locations and handle rights

This interface adds situated formation to the existing contextual firing.
The actual root inventory covers incoming equations, shared rows, retained
continuations and stored template captures. Location lists describe authored
ports. Observation sites are declared regions, including empty regions; they
must cover all occurrences inspected by each whole-world absence/count ask.

Authority is separate from availability. Having a receive facet cannot make
a missing row present, and a present row cannot supply a missing facet.
These are formation conditions on the existing step, not a second evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSituatedFormation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open ContextualActivatedStep ContextualScopeSupport ContextualWorldScopeLedger

universe u v
variable {S : Signature} {Local Shared : Type} {O : Type u} {N : Type v}

structure PortLocations (N : Type v) where
  take : List N
  read : List N
  produce : List N

def Regional {T : Type*} : Check T → Prop
  | .equal _ _ => False
  | .absent _ | .count _ _ => True

structure Authority [DecidableEq O] {T : Type*} (rights : Rights N) (location : O → N)
    (sites : Check T → Finset N) (checks : List (Check T))
    (selection : Selection O) (world : Finset O) : Prop where
  physical : FormedUnder location id rights (selection.commit (T := N))
  regions : ∀ check ∈ checks, Regional check → ∀ site ∈ sites check, rights site .observe = true
  coverage : ∀ check ∈ checks, Regional check → ∀ occurrence ∈ world, location occurrence ∈ sites check

variable (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

structure Formed [DecidableEq O] (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (inventory : Inventory locals captures (O := O) Γ sort)
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (ports : PortLocations N) (location : O → N) (rights : Rights N)
    (sites : Check (Term (signature S (target locals captures)) Γ sort) → Finset N) : Prop where
  shape : ContextualInteractionFactors.Formation locals captures occupied selection rule inventory.rows outputs
  world_scoped : CoveredWorld locals captures scopes occupied inventory
  rule_scoped : RuleCovered (privateScopes scopes) occupied rule
  take_locations : selection.taken.map location = ports.take
  read_locations : selection.read.map location = ports.read
  output_locations : selection.made.map location = ports.produce
  authority : Authority rights location sites
    (prepared locals captures occupied selection rule inventory.rows).rule.checks selection inventory.configuration.present

variable [DecidableEq O] {scopes : Shared → Finset Nat} {occupied : Finset Nat}
  {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
  {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
  {inventory : Inventory locals captures (O := O) Γ sort}
  {outputs : O → Term (signature S (target locals captures)) Γ sort}
  {ports : PortLocations N} {location : O → N} {rights : Rights N}
  {sites : Check (Term (signature S (target locals captures)) Γ sort) → Finset N}

theorem Formed.fresh_from_every_root
    (formed : Formed locals captures scopes occupied selection rule inventory outputs ports location rights sites)
    (port : ContextualActivationScopes.Port selection) :
    ContextualActivationScopes.scopeAt occupied port ∉ footprint locals captures scopes inventory := by
  intro member
  exact ContextualActivationScopes.at_fresh occupied port
    ((coveredWorld_iff locals captures scopes occupied inventory).mp formed.world_scoped member)

theorem Formed.successor_scope_coverage
    (formed : Formed locals captures scopes occupied selection rule inventory outputs ports location rights sites)
    (resource : ContextualInteractionFactors.Resources selection inventory.configuration.present) :
    CoveredWorld locals (target locals captures) (activeScopes scopes)
      (ContextualActivationScopes.after occupied selection)
      (afterInventory locals captures occupied selection rule inventory outputs) :=
  afterInventory_covered locals captures scopes occupied selection rule inventory outputs
    formed.world_scoped formed.rule_scoped
    ((ContextualInteractionFactors.resources_iff outputs _ _).mp resource).2.2 formed.shape.outputs

theorem Formed.receive_required
    (formed : Formed locals captures scopes occupied selection rule inventory outputs ports location rights sites)
    {occurrence : O} (selected : occurrence ∈ selection.taken) : rights (location occurrence) .receive = true :=
  formed.authority.physical.taken occurrence (by simpa only [Selection.commit, List.mem_toFinset] using selected)

theorem Formed.peek_required
    (formed : Formed locals captures scopes occupied selection rule inventory outputs ports location rights sites)
    {occurrence : O} (selected : occurrence ∈ selection.read) : rights (location occurrence) .peek = true :=
  formed.authority.physical.kept occurrence (by simpa only [Selection.commit, List.mem_toFinset] using selected)

theorem Formed.send_required
    (formed : Formed locals captures scopes occupied selection rule inventory outputs ports location rights sites)
    {occurrence : O} (selected : occurrence ∈ selection.made) : rights (location occurrence) .send = true :=
  formed.authority.physical.made occurrence (by simpa only [Selection.commit, List.mem_toFinset] using selected)

theorem Formed.observe_required
    (formed : Formed locals captures scopes occupied selection rule inventory outputs ports location rights sites)
    {check : Check (Term (signature S (target locals captures)) Γ sort)}
    (selected : check ∈ (prepared locals captures occupied selection rule inventory.rows).rule.checks)
    (regional : Regional check) {site : N} (declared : site ∈ sites check) :
    rights site .observe = true := formed.authority.regions check selected regional site declared

theorem Authority.region_restricts_no_observed_row [DecidableEq N] {T : Type*}
    {sites : Check T → Finset N} {checks : List (Check T)} {world : Finset O}
    (authority : Authority rights location sites checks selection world)
    {check : Check T} (selected : check ∈ checks) (regional : Regional check) :
    (world.filter fun occurrence => location occurrence ∈ sites check) = world := by
  classical
  exact Finset.filter_eq_self.mpr (authority.coverage check selected regional)

structure Admitted (scopes : Shared → Finset Nat) (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (inventory : Inventory locals captures (O := O) Γ sort)
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (ports : PortLocations N) (location : O → N) (rights : Rights N)
    (sites : Check (Term (signature S (target locals captures)) Γ sort) → Finset N) : Prop where
  formation : Formed locals captures scopes occupied selection rule inventory outputs ports location rights sites
  resources : ContextualInteractionFactors.Resources selection inventory.configuration.present
  information : ContextualInteractionFactors.Information locals captures occupied selection rule
    inventory.rows inventory.configuration

theorem Admitted.original_firing
    (admitted : Admitted locals captures scopes occupied selection rule inventory outputs ports location rights sites) :
    ContextualGuardedStep.Valid locals captures occupied selection rule inventory.rows inventory.configuration outputs :=
  (ContextualGuardedStep.valid_iff_factors locals captures occupied selection rule inventory.rows
    inventory.configuration outputs).mpr ⟨admitted.formation.shape, admitted.resources, admitted.information⟩

theorem Admitted.original_step
    (admitted : Admitted locals captures scopes occupied selection rule inventory outputs ports location rights sites) :
    ContextualGuardedStep.Step locals captures occupied rule inventory.rows inventory.configuration outputs
      (result locals captures occupied selection rule inventory.rows inventory.configuration)
      (resultRows locals captures selection outputs inventory.rows)
      (ContextualActivationScopes.after occupied selection) :=
  ⟨selection, ⟨admitted.formation.shape, admitted.resources, admitted.information⟩, rfl, rfl, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSituatedFormation
