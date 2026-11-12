import Mettapedia.Machines.ProfileRecoveryContract
import Mettapedia.Machines.HierarchyCompactionContract
import Mettapedia.Machines.HandleNameDomain
import Mettapedia.Machines.CollectorEvacuation

/-!
Concrete witnesses to missing links in four original draft runtime contracts.
The historical rules remain executable beside the repaired interfaces.  The
old declarations still exhibit their defects; new theorems check closure-aware
admission, owner isolation, and exact ordered transport.
-/

namespace Mettapedia.Machines.RuntimeContractReviewWitnesses

namespace Admission
open ProfileRecoveryContract

def incompleteDeclaration : Profile :=
  { supported := heSupported
    required := [.nativeLlm]
    roots := [.nativeLlm] }

def answer : Answer Nat Nat := ⟨7, 42⟩

theorem incomplete_declaration_is_admitted :
    legacyAdmit incompleteDeclaration answer = some (initial answer) := rfl

theorem admitted_declaration_is_not_closed : ¬ Closed incompleteDeclaration := by
  intro closed
  have missing := closed (start := .nativeLlm) (target := .libImport)
    (by simp [incompleteDeclaration]) he_missing_reachable_capability.1
  simp [incompleteDeclaration, heSupported] at missing

theorem successful_admission_does_not_imply_dependency_closure :
    ∃ profile, (legacyAdmit profile answer).isSome = true ∧ ¬ Closed profile :=
  ⟨incompleteDeclaration, rfl, admitted_declaration_is_not_closed⟩

theorem repaired_admission_refuses_incomplete_declaration :
    admit incompleteDeclaration answer = none := rfl

theorem repaired_successful_admission_implies_dependency_closure
    {state : State Nat Nat} (admitted : admit incompleteDeclaration answer = some state) :
    Closed incompleteDeclaration :=
  admit_some_closed incompleteDeclaration answer admitted
end Admission

namespace Entrypoint
open ProfileRecoveryContract

def emptyProfile : Profile := ⟨fun _ => false, [], []⟩
def answer : Answer Nat Nat := ⟨7, 42⟩

theorem empty_graph_is_closed : Closed emptyProfile := by
  intro start target member _
  simp [emptyProfile] at member

/-- The former consumer could submit a provider request after validating an
empty graph that declared none of the modules the consumer actually uses. -/
theorem legacy_consumer_executes_without_its_entrypoint :
    (legacyRecoverSupported emptyProfile answer 0).map State.providerRequests = some 1 := rfl

theorem repaired_consumer_refuses_missing_entrypoint :
    recoverSupported emptyProfile answer 0 = none := rfl
end Entrypoint

namespace Publication
open HierarchyCompactionContract

def oldStore : Store Nat Nat := ⟨[⟨7, 1, 42⟩], [], .allVersions⟩
def emptyStore : Store Nat Nat := ⟨[], [], .allVersions⟩
def before : Publication Nat Nat :=
  ⟨[⟨0, oldStore, true⟩], [⟨1, emptyStore, true⟩], some 0⟩

theorem old_history_is_recoverable :
    (recover before).bind (fun store => read store 7 1) = some 42 := rfl

theorem empty_replacement_is_complete_and_closed :
    referentiallyClosed emptyStore = true := rfl

theorem accepted_commit_loses_retained_history :
    (commit before 1).isSome = true ∧
      (commit before 1).bind (fun published =>
        (recover published).bind (fun store => read store 7 1)) = none := by
  exact ⟨rfl, rfl⟩

theorem repaired_compaction_publication_preserves_retained_history :
    ((stageCompaction before 2 true).bind (fun staged =>
      (commit staged 2).bind recover)).bind (fun store => read store 7 1) = some 42 := by
  rfl

/-- Appending the correct candidate does not help if commit finds an earlier
candidate with the same generation identity. -/
theorem unchecked_compaction_collision_loses_history :
    ((legacyStageCompaction before 1 true).bind (fun staged =>
      (commit staged 1).bind recover)).bind (fun store => read store 7 1) = none := rfl

theorem repaired_compaction_rejects_pending_and_published_collisions :
    stageCompaction before 1 true = none ∧ stageCompaction before 0 true = none :=
  ⟨rfl, rfl⟩
end Publication

namespace Authority
open HandleNameDomain

def names : NameDomains Nat := ⟨fun domain name =>
  if domain = 0 ∧ name = 7 then some "owned-resource" else none⟩

def wire : WireHandle := ⟨7, 1⟩
def authority : Capability Nat Nat := ⟨0, 0, "owned-resource", 1, 1⟩

def registry (payload : Nat) : Registry Nat Nat := ⟨0, fun domain id =>
  if domain = 0 ∧ id = 1 then
    some ⟨0, 0, "owned-resource", 1, payload, true⟩ else none⟩

theorem one_capability_is_accepted_by_two_distinct_registries :
    legacyAcquire names (registry 42) 0 wire (some authority) = some 42 ∧
      legacyAcquire names (registry 99) 0 wire (some authority) = some 99 := by
  exact ⟨rfl, rfl⟩

def repairedRegistry (owner : Bool) (payload : Nat) : Registry Nat Bool :=
  ⟨owner, fun domain id =>
    if domain = 0 ∧ id = 1 then
      some ⟨0, owner, "owned-resource", 1, payload, true⟩ else none⟩

def repairedAuthority : Capability Nat Bool := ⟨0, false, "owned-resource", 1, 1⟩

theorem repaired_acquisition_separates_owner_from_name_domain :
    acquire names (repairedRegistry false 42) 0 wire (some repairedAuthority) = some 42 ∧
      acquire names (repairedRegistry true 42) 0 wire (some repairedAuthority) = none := by
  exact ⟨rfl, rfl⟩
end Authority

namespace Collector
open CollectorEvacuation

universe u v
variable {Source : Type u} {Label : Type v} [Fintype Source] [LinearOrder Source]

/-- The declared contract sees root membership and length, but neither order
nor the multiplicity of an individual repeated root. -/
theorem same_support_and_length_preserve_contract
    (graph : SourceGraph Source Label) (roots : List Source) (capacity : Nat)
    (state : CopyState Source) (target : TargetGraph Label)
    (valid : LegacyPublishedContract graph roots capacity state target)
    (replacement : List Target)
    (support : ∀ image, image ∈ replacement ↔ image ∈ target.roots)
    (length : replacement.length = target.roots.length) :
    LegacyPublishedContract graph roots capacity state { target with roots := replacement } := by
  rcases valid with ⟨exhausted, total, injective, keys, storage, bounds, members, count, nodes⟩
  refine ⟨exhausted, total, injective, keys, storage, bounds, ?_, length.trans count, nodes⟩
  intro root member
  obtain ⟨image, found, present⟩ := members root member
  exact ⟨image, found, (support image).mpr present⟩

theorem repeated_roots_can_have_equal_support_and_length_but_different_counts :
    (∀ image : Target,
      image ∈ [⟨0⟩, ⟨1⟩, ⟨1⟩] ↔ image ∈ [⟨0⟩, ⟨0⟩, ⟨1⟩]) ∧
    ([⟨0⟩, ⟨1⟩, ⟨1⟩] : List Target).length =
      ([⟨0⟩, ⟨0⟩, ⟨1⟩] : List Target).length ∧
    ([⟨0⟩, ⟨1⟩, ⟨1⟩] : List Target).count ⟨0⟩ ≠
      ([⟨0⟩, ⟨0⟩, ⟨1⟩] : List Target).count ⟨0⟩ := by
  constructor
  · intro image
    simp
  · decide

theorem repaired_contract_exposes_exact_ordered_transport
    (graph : SourceGraph Source Label) (roots : List Source) (capacity : Nat)
    (state : CopyState Source) (target : TargetGraph Label)
    (valid : PublishedContract graph roots capacity state target) :
    target.roots = roots.map (relocatedOrZero state) := valid.roots_ordered
end Collector

#print axioms Admission.successful_admission_does_not_imply_dependency_closure
#print axioms Publication.accepted_commit_loses_retained_history
#print axioms Publication.unchecked_compaction_collision_loses_history
#print axioms Publication.repaired_compaction_rejects_pending_and_published_collisions
#print axioms Entrypoint.legacy_consumer_executes_without_its_entrypoint
#print axioms Entrypoint.repaired_consumer_refuses_missing_entrypoint
#print axioms Publication.repaired_compaction_publication_preserves_retained_history
#print axioms Authority.one_capability_is_accepted_by_two_distinct_registries
#print axioms Collector.same_support_and_length_preserve_contract
#print axioms Collector.repeated_roots_can_have_equal_support_and_length_but_different_counts
#print axioms Admission.repaired_admission_refuses_incomplete_declaration
#print axioms Authority.repaired_acquisition_separates_owner_from_name_domain
#print axioms Collector.repaired_contract_exposes_exact_ordered_transport

end Mettapedia.Machines.RuntimeContractReviewWitnesses
