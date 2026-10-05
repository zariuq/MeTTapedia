import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryImage

/-!
# Actual channel matching respects the unary compiler's namespaces

Source channels are injectively allocated seeds, persistent implementation
channels are distinct unused seeds, and allocator channels are reserved free
names. The concrete canonical rho comparator identifies two rendered ports
exactly when their roles and values agree. This is a namespace separation
theorem about actual core names, not a scheduling rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryRoles

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryWorld RhoUnaryActive
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

inductive Port (Γ : Ctx sig) where
  | user (name : Var Γ .nm)
  | self (seed : Nat)
  | reserved (channel : Reserved)

def Port.term {Γ : Ctx sig} (world : SeedWorld Γ) : Port Γ → Pattern
  | .user name => (world.world name).term
  | .self seed => allocatedName seed
  | .reserved channel => (reservedChannel channel).term

def Port.Fresh {Γ : Ctx sig} (world : SeedWorld Γ) : Port Γ → Prop
  | .self seed => ∀ name, seed ≠ world.index name
  | _ => True

private theorem match_symmetric {first second : Pattern} :
    rhoCanonicalEquivalent first second = true ↔ rhoCanonicalEquivalent second first = true := by
  rw [rhoCanonicalEquivalent_iff, rhoCanonicalEquivalent_iff]
  exact eq_comm

private theorem reserved_injective : Function.Injective Reserved.label := by
  intro first second same
  cases first <;> cases second <;> simp_all [Reserved.label]

private theorem reserved_match (first second : Reserved) :
    rhoCanonicalEquivalent (reservedChannel first).term (reservedChannel second).term = true ↔
      first = second := by
  rw [rhoCanonicalEquivalent_iff]
  change (Pattern.fvar first.label = Pattern.fvar second.label) ↔ first = second
  exact ⟨fun same => reserved_injective (Pattern.fvar.inj same), fun same => congrArg (fun r => Pattern.fvar r.label) same⟩

/-- Matching reflects both the syntactic role and the actual intrinsic name.
The freshness conditions exclude implementation channels from source ports. -/
theorem port_match_iff {Γ : Ctx sig} (world : SeedWorld Γ) (first second : Port Γ)
    (firstFresh : first.Fresh world) (secondFresh : second.Fresh world) :
    rhoCanonicalEquivalent (first.term world) (second.term world) = true ↔ first = second := by
  cases first with
  | user name =>
      cases second with
      | user other =>
          simpa [Port.term] using world.match_iff name other
      | self seed =>
          constructor
          · intro matched
            have equal := (seed_match_iff (world.index name) seed).mp matched
            exact False.elim (secondFresh name equal.symm)
          · intro impossible; cases impossible
      | reserved channel =>
          constructor
          · intro matched
            have impossible := seed_reserved_no_match (world.index name) channel
            change rhoCanonicalEquivalent (allocatedName (world.index name)) (reservedChannel channel).term = true at matched
            rw [impossible] at matched
            cases matched
          · intro impossible; cases impossible
  | self seed =>
      cases second with
      | user name =>
          constructor
          · intro matched
            have equal := (seed_match_iff seed (world.index name)).mp matched
            exact False.elim (firstFresh name equal)
          · intro impossible; cases impossible
      | self other => simpa [Port.term] using seed_match_iff seed other
      | reserved channel =>
          constructor
          · intro matched
            have impossible := seed_reserved_no_match seed channel
            change rhoCanonicalEquivalent (allocatedName seed) (reservedChannel channel).term = true at matched
            rw [impossible] at matched
            cases matched
          · intro impossible; cases impossible
  | reserved channel =>
      cases second with
      | user name =>
          constructor
          · intro matched
            have reverse := match_symmetric.mp matched
            have impossible := seed_reserved_no_match (world.index name) channel
            change rhoCanonicalEquivalent (allocatedName (world.index name)) (reservedChannel channel).term = true at reverse
            rw [impossible] at reverse
            cases reverse
          · intro impossible; cases impossible
      | self seed =>
          constructor
          · intro matched
            have reverse := match_symmetric.mp matched
            have impossible := seed_reserved_no_match seed channel
            change rhoCanonicalEquivalent (allocatedName seed) (reservedChannel channel).term = true at reverse
            rw [impossible] at reverse
            cases reverse
          · intro impossible; cases impossible
      | reserved other => simpa [Port.term] using reserved_match channel other

def _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive.Activity.port {Γ : Ctx sig} : Activity Γ → Port Γ
  | .output channel _ | .input channel _ _ | .ready channel _ _ _ => .user channel
  | .privateScope _ _ | .install _ _ _ | .reply _ => .reserved .reply
  | .rearm _ _ _ self | .sendCode _ _ _ self => .self self
  | .request | .allocatorReady => .reserved .request
  | .allocatorRearm | .allocatorSendCode => .reserved .code
  | .seedInput | .token _ => .reserved .state

def _root_.Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion.Header.channel : Header → Pattern
  | .input channel _ | .output channel _ => channel

theorem _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive.Activity.header_channel {Γ : Ctx sig} (world : SeedWorld Γ) (activity : Activity Γ) :
    (activity.header world.world).channel = activity.port.term world := by
  cases activity <;> rfl

/-- Formation of the initial compiled image requires no implementation
channel allocation: its ports are user ports and reserved request/reply. -/
theorem initial_fresh {Γ : Ctx sig} (world : SeedWorld Γ) (activity : Activity Γ)
    (initial : RhoUnaryImage.Initial activity) : activity.port.Fresh world := by
  cases activity <;> simp_all [RhoUnaryImage.Initial, Activity.port, Port.Fresh]

/-- The selected original occurrences in any actual authored firing have
the same source or infrastructure port. Canonical inversion supplies this
selection even after sorting the header bag. -/
theorem selected_port_eq {Γ : Ctx sig} (world : SeedWorld Γ)
    (activities : List (Activity Γ))
    (fresh : ∀ activity ∈ activities, activity.port.Fresh world)
    (selected : Selection (headers world.world activities)) :
    (activities[selected.inputIndex]'(by simpa [headers] using selected.inputBound)).port =
      ((activities.eraseIdx selected.inputIndex)[selected.outputIndex]'
        (by simpa [headers, List.eraseIdx_map] using selected.outputBound)).port := by
  let input : Activity Γ := activities[selected.inputIndex]'(by simpa [headers] using selected.inputBound)
  let output : Activity Γ := (activities.eraseIdx selected.inputIndex)[selected.outputIndex]'
    (by simpa [headers, List.eraseIdx_map] using selected.outputBound)
  have inputEq : input.header world.world = .input selected.inputChannel selected.body := by
    simpa [input, headers] using selected.inputEq
  have outputEq : output.header world.world = .output selected.outputChannel selected.payload := by
    simpa [output, headers, List.eraseIdx_map] using selected.outputEq
  have inputChannel : selected.inputChannel = input.port.term world := by
    rw [← input.header_channel world, inputEq]
    rfl
  have outputChannel : selected.outputChannel = output.port.term world := by
    rw [← output.header_channel world, outputEq]
    rfl
  have inputMember : input ∈ activities := List.getElem_mem _
  have outputMember : output ∈ activities := List.mem_of_mem_eraseIdx (List.getElem_mem _)
  exact (port_match_iff world input.port output.port (fresh input inputMember) (fresh output outputMember)).mp
    (by simpa [inputChannel, outputChannel] using selected.channels)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryRoles
