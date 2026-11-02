import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSituatedFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorControls

/-! # Location and observation authority remain formation obligations even on an empty world -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSituatedControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open ContextualActivatedStep ContextualWorldScopeLedger ContextualScopeSupport
open ContextualSituatedFormation
open ContextualSelectionViews.Controls (base locals captures raw active RawTerm atom rawA)
open ContextualGuardedStep.Controls (occupied selection bare outputs trueRule)
open ContextualFactorControls (rows)

def scopes (_ : Nat) : Finset Nat := ∅
def inventory : Inventory locals captures (O := Nat) [] () :=
  ⟨bare, rows, [], []⟩
def locations (_ : Nat) : Nat := 3
def ports : PortLocations Nat := ⟨[], [], [3]⟩
def allow : Rights Nat := fun _ _ => true
def deny : Rights Nat := fun _ _ => false
def sites (_ : Check (Term (signature base active) [] ())) : Finset Nat := {3}

theorem ordinary_world_is_covered : CoveredWorld locals captures scopes occupied inventory := by
  refine ⟨by simp [equationScopes, ContextualScopeSupport.names, inventory, bare], ?_, ?_, ?_⟩
  · intro occurrence _member
    change (∅ : Finset Nat) ⊆ occupied
    exact Finset.empty_subset _
  · simp [inventory, ContextualScopeSupport.observations, ContextualScopeSupport.names]
  · simp [inventory, ContextualScopeSupport.observations, ContextualScopeSupport.names]

theorem reflexive_rule_is_covered : RuleCovered (privateScopes scopes) occupied trueRule := by
  intro value member
  change value ∈ [rawA, rawA, rawA] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst value
  change (∅ : Finset Nat) ⊆ occupied
  exact Finset.empty_subset _

theorem concrete_formed_activation :
    Formed locals captures scopes occupied selection trueRule inventory outputs ports locations allow sites := by
  refine ⟨⟨rfl, rfl, rfl⟩, ordinary_world_is_covered, reflexive_rule_is_covered,
    rfl, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by intros; rfl, by intros; rfl, by intros; rfl, by simp [Selection.commit]⟩
  · intro check _member _regional site _declared
    rfl
  · intro check member regional _occurrence _present
    have only : check = .equal (atom active) (atom active) := List.mem_singleton.mp member
    subst check
    exact False.elim regional

theorem concrete_admitted_activation :
    Admitted locals captures scopes occupied selection trueRule inventory outputs ports locations allow sites := by
  have factors := (ContextualGuardedStep.valid_iff_factors locals captures occupied selection
    trueRule rows bare outputs).mp ContextualFactorControls.true_guard_forms_an_actual_step
  exact ⟨concrete_formed_activation, factors.resources, factors.information⟩

theorem the_actual_successor_has_a_covered_inventory :
    CoveredWorld locals (target locals captures) (activeScopes scopes)
      (ContextualActivationScopes.after occupied selection)
      (afterInventory locals captures occupied selection trueRule inventory outputs) :=
  concrete_formed_activation.successor_scope_coverage locals captures
    concrete_admitted_activation.resources

theorem missing_send_cannot_be_repaired_by_available_resources :
    ¬ Formed locals captures scopes occupied selection trueRule inventory outputs ports locations deny sites := by
  intro formed
  have allowed := formed.send_required locals captures (occurrence := 99) (by decide)
  cases allowed

def absentCheck : Check Nat := .absent 5
def onlySite (_ : Check Nat) : Finset Nat := {3}
def noPorts : Selection Nat := ⟨[], [], []⟩

theorem an_empty_region_still_requires_its_declared_observe_right :
    ¬ Authority deny locations onlySite [absentCheck] noPorts ∅ := by
  intro authority
  have allowed := authority.regions absentCheck (List.mem_singleton_self _) (by trivial) 3 (by decide)
  cases allowed

theorem an_empty_authorized_region_is_formed :
    Authority allow locations onlySite [absentCheck] noPorts ∅ := by
  refine ⟨?_, by intros; rfl, ?_⟩
  · exact ⟨by simp [noPorts, Selection.commit], by simp [noPorts, Selection.commit],
      by simp [noPorts, Selection.commit], by simp [Selection.commit]⟩
  · intro _check _member _regional occurrence impossible
    exact False.elim (Finset.notMem_empty occurrence impossible)

theorem undeclared_live_region_is_rejected_even_with_all_rights :
    ¬ Authority allow locations (fun _ : Check Nat => ∅) [absentCheck] noPorts {7} := by
  intro authority
  exact Finset.notMem_empty _
    (authority.coverage absentCheck (List.mem_singleton_self _) (by trivial) 7 (by decide))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSituatedControls
