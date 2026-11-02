import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotReadExecution

/-!
# Original context weakening through the actual canonical private snapshot

The original weakening rule retains its request, private availability and
inclusion reads, protected theorem read and exact theorem output. This adapter
adds the actual private snapshot read and consults its finite context and
canonical inclusion lookups. It never decides derivability or replays source
admissions. Old immutable context IDs remain usable.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransport

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotActivation

def liftLocation : HOLLightLicensedActivation.Location → Location
  | .inl space => .inl space
  | .inr () => licenses

def lift (value : HOLLightLicensedActivation.Value) : Value := (liftLocation value.1, value.2)

def rule (snapshot : Snapshot) (before after : Nat) (fact : Theorem) : RuleInstance Value :=
  let original := HOLLightLicensedActivation.weakeningRule before after fact
  { original.map lift with read := (snapshots, snapshotPayload snapshot) :: original.read.map lift }

theorem exact_take (snapshot : Snapshot) (before after : Nat) (fact : Theorem) :
    (rule snapshot before after fact).take = [(requests, HOLLightLicensedActivation.weakeningRequest before after fact)] := rfl

theorem exact_reads (snapshot : Snapshot) (before after : Nat) (fact : Theorem) :
    (rule snapshot before after fact).read =
      [(snapshots, snapshotPayload snapshot), (licenses, HOLLightLicensedActivation.available after),
        (licenses, HOLLightLicensedActivation.included before after),
        (judgments, HOLLightContextActivation.theoremPayload before fact)] := rfl

theorem exact_output (snapshot : Snapshot) (before after : Nat) (fact : Theorem) :
    (rule snapshot before after fact).produce = [(judgments, HOLLightContextActivation.theoremPayload after fact)] := rfl

def activate (snapshot : Snapshot) (before after : Nat) (fact : Theorem) : Option (RuleInstance Value) := do
  let _ ← context snapshot before
  let _ ← context snapshot after
  let _ ← snapshot.store.lookup (.inl after)
  let _ ← snapshot.store.lookup (.inr (before, after))
  pure (rule snapshot before after fact)

theorem activation_origin (snapshot : Snapshot) (before after : Nat) (fact : Theorem) {raw : RuleInstance Value}
    (computed : activate snapshot before after fact = some raw) :
    ∃ beforeContext afterContext, context snapshot before = some beforeContext ∧ context snapshot after = some afterContext ∧
      (snapshot.store.lookup (.inl after)).isSome = true ∧
      (snapshot.store.lookup (.inr (before, after))).isSome = true ∧ raw = rule snapshot before after fact := by
  cases beforeKnown : context snapshot before with
  | none => simp [activate, beforeKnown] at computed
  | some beforeContext =>
      cases afterKnown : context snapshot after with
      | none => simp [activate, beforeKnown, afterKnown] at computed
      | some afterContext =>
          cases available : snapshot.store.lookup (.inl after) with
          | none => simp [activate, beforeKnown, afterKnown, available] at computed
          | some availability =>
              cases included : snapshot.store.lookup (.inr (before, after)) with
              | none => simp [activate, beforeKnown, afterKnown, available, included] at computed
              | some inclusion =>
                  have same : rule snapshot before after fact = raw := by
                    simpa [activate, beforeKnown, afterKnown, available, included] using computed
                  exact ⟨beforeContext, afterContext, rfl, rfl, rfl, rfl, same.symm⟩

theorem unknown_source_context_refused (snapshot : Snapshot) (before after : Nat) (fact : Theorem)
    (missing : context snapshot before = none) : activate snapshot before after fact = none := by simp [activate, missing]

theorem unknown_target_context_refused (snapshot : Snapshot) (before after : Nat) (fact : Theorem)
    (missing : context snapshot after = none) : activate snapshot before after fact = none := by simp [activate, missing]

theorem missing_inclusion_refused (snapshot : Snapshot) (before after : Nat) (fact : Theorem)
    (missing : snapshot.store.lookup (.inr (before, after)) = none) : activate snapshot before after fact = none := by simp [activate, missing]

theorem missing_target_license_refused (snapshot : Snapshot) (before after : Nat) (fact : Theorem)
    (missing : snapshot.store.lookup (.inl after) = none) : activate snapshot before after fact = none := by simp [activate, missing]

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotContextTransport
