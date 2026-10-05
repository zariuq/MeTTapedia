import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryTargetSteps

/-!
# Administrative progress of the concrete unary rho runtime

Positive remaining credit identifies an actual pending scope, installation,
request, seed receiver, or rearm. The existing occurrence inventory supplies
its partner, including the same persistent handler and the unique live token.
Exposing these two occurrences preserves the entire residual list. Their
authored COMM consumes one unit of credit and preserves the source by its
actual structural equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministrativeProgress

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryInventory RhoUnaryCredit
open RhoUnaryReadback RhoUnaryReadbackStep RhoUnaryTargetSteps ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

/-- These are the six existing administrative COMM shapes. The source
communication shapes are deliberately absent from this classification. -/
inductive Administrative {Γ : Ctx sig} : Activity Γ → Activity Γ → Prop where
  | privateScope (body : Proc (.nm :: Γ)) (guarded : GuardedUnary body) (seed : Nat) :
      Administrative (.privateScope body guarded) (.reply seed)
  | install (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
      (guarded : GuardedUnary body) (seed : Nat) :
      Administrative (.install channel body guarded) (.reply seed)
  | rearm (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
      (guarded : GuardedUnary body) (self : Nat) :
      Administrative (.rearm channel body guarded self) (.sendCode channel body guarded self)
  | allocatorRequest : Administrative (.allocatorReady : Activity Γ) .request
  | allocatorRearm : Administrative (.allocatorRearm : Activity Γ) .allocatorSendCode
  | token (seed : Nat) : Administrative (.seedInput : Activity Γ) (.token seed)

private theorem weighted_member {Γ : Ctx sig} (weight : Activity Γ → Nat)
    {activities : List (Activity Γ)} (positive : 0 < (activities.map weight).sum) :
    ∃ activity ∈ activities, 0 < weight activity := by
  induction activities with
  | nil => simp at positive
  | cons activity rest ih =>
      by_cases head : 0 < weight activity
      · exact ⟨activity, by simp, head⟩
      · have tail : 0 < (rest.map weight).sum := by
          simp only [List.map_cons, List.sum_cons] at positive
          omega
        obtain ⟨chosen, member, nonzero⟩ := ih tail
        exact ⟨chosen, List.mem_cons_of_mem _ member, nonzero⟩

private theorem count_member {Γ : Ctx sig} (kind : CountKind)
    {activities : List (Activity Γ)} (positive : 0 < count kind activities) :
    ∃ activity ∈ activities, 0 < contribution kind activity :=
  weighted_member (contribution kind) positive

private theorem allocator_rearm_available {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (member : Activity.allocatorRearm ∈ activities) :
    Activity.allocatorSendCode ∈ activities := by
  have nonzero : 0 < count .allocatorRearm activities := by
    unfold count
    exact List.sum_pos_iff_exists_pos_nat.mpr
      ⟨1, List.mem_map.mpr ⟨_, member, rfl⟩, by omega⟩
  rw [← inventory.allocator_code] at nonzero
  obtain ⟨activity, member, positive⟩ := count_member .allocatorSendCode nonzero
  cases activity <;> simp_all [contribution]

private theorem allocator_partner {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (request : Activity.request ∈ activities) :
    ∃ input ∈ activities, ∃ output ∈ activities, Administrative input output := by
  by_cases ready : 0 < count .allocatorReady activities
  · obtain ⟨activity, member, positive⟩ := count_member .allocatorReady ready
    have actual : activity = .allocatorReady := by cases activity <;> simp_all [contribution]
    subst activity
    exact ⟨.allocatorReady, member, .request, request, .allocatorRequest⟩
  · have positive : 0 < count .allocatorRearm activities := by
      have phase := inventory.allocator_phase
      omega
    obtain ⟨activity, member, positive⟩ := count_member .allocatorRearm positive
    have actual : activity = .allocatorRearm := by cases activity <;> simp_all [contribution]
    subst activity
    exact ⟨.allocatorRearm, member, .allocatorSendCode,
      allocator_rearm_available inventory member, .allocatorRearm⟩

private theorem token_partner {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (receiver : Activity.seedInput ∈ activities) :
    ∃ input ∈ activities, ∃ output ∈ activities, Administrative input output := by
  have tokenMember : world.available ∈ tokens activities := by rw [inventory.token_unique]; simp
  obtain ⟨activity, member, same⟩ := List.mem_filterMap.mp tokenMember
  have actual : activity = .token world.available := by cases activity <;> simp_all [tokenSeed]
  subst activity
  exact ⟨.seedInput, receiver, .token world.available, member, .token _⟩

private theorem rearm_partner {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (channel : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (self : Nat) (member : Activity.rearm channel body guarded self ∈ activities) :
    ∃ input ∈ activities, ∃ output ∈ activities, Administrative input output := by
  have owner : (⟨self, channel, body⟩ : Owner Γ) ∈ rearms activities :=
    List.mem_filterMap.mpr ⟨_, member, rfl⟩
  have code : (⟨self, channel, body⟩ : Owner Γ) ∈ codes activities :=
    inventory.rearm_code.mem_iff.mp owner
  obtain ⟨activity, codeMember, same⟩ := List.mem_filterMap.mp code
  have actual : activity = .sendCode channel body guarded self := by
    cases activity <;> simp_all [RhoUnaryInventory.storedCode]
  subst activity
  exact ⟨.rearm channel body guarded self, member, .sendCode channel body guarded self,
    codeMember, .rearm channel body guarded self⟩

private theorem pending_partner {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (client : Activity Γ) (member : client ∈ activities)
    (pending : 0 < RhoUnaryImage.pendingWeight client) :
    ∃ input ∈ activities, ∃ output ∈ activities, Administrative input output := by
  have clients : 0 < RhoUnaryImage.clientCount activities := by
    exact List.sum_pos_iff_exists_pos_nat.mpr
      ⟨_, List.mem_map.mpr ⟨_, member, rfl⟩, pending⟩
  by_cases request : 0 < RhoUnaryImage.requestCount activities
  · obtain ⟨activity, requestMember, positive⟩ := weighted_member RhoUnaryImage.requestWeight request
    have actual : activity = .request := by cases activity <;> simp_all [RhoUnaryImage.requestWeight]
    subst activity
    exact allocator_partner inventory requestMember
  · by_cases receiver : 0 < count .seedInput activities
    · obtain ⟨activity, receiverMember, positive⟩ := count_member .seedInput receiver
      have actual : activity = .seedInput := by cases activity <;> simp_all [contribution]
      subst activity
      exact token_partner inventory receiverMember
    · have repliesPositive : 0 < (replies activities).length := by
        have balance := inventory.pending_balance
        omega
      obtain ⟨seed, rest, same⟩ := List.exists_cons_of_length_pos repliesPositive
      have returned : seed ∈ replies activities := by rw [same]; simp
      obtain ⟨activity, replyMember, sameReply⟩ := List.mem_filterMap.mp returned
      have actual : activity = .reply seed := by cases activity <;> simp_all [replySeed]
      subst activity
      cases client <;> simp only [RhoUnaryImage.pendingWeight] at pending
      all_goals first
        | omega
        | exact ⟨_, member, .reply seed, replyMember, .privateScope _ _ _⟩
        | exact ⟨_, member, .reply seed, replyMember, .install _ _ _ _⟩

/-- Ownership and the pending-request balance prohibit an administrative
deadlock while any concrete initialization work remains. -/
theorem enabled_pair {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (positive : 0 < total activities) :
    ∃ input ∈ activities, ∃ output ∈ activities, Administrative input output := by
  obtain ⟨activity, member, pending⟩ := weighted_member credit positive
  cases activity with
  | privateScope body guarded => exact pending_partner inventory _ member (by simp [RhoUnaryImage.pendingWeight])
  | install channel body guarded => exact pending_partner inventory _ member (by simp [RhoUnaryImage.pendingWeight])
  | rearm channel body guarded self => exact rearm_partner inventory channel guarded self member
  | request => exact allocator_partner inventory member
  | allocatorRearm => exact ⟨.allocatorRearm, member, .allocatorSendCode,
      allocator_rearm_available inventory member, .allocatorRearm⟩
  | seedInput => exact token_partner inventory member
  | output channel datum => simp [credit] at pending
  | input channel body guarded => simp [credit] at pending
  | ready channel body guarded self => simp [credit] at pending
  | sendCode channel body guarded self => simp [credit] at pending
  | reply seed => simp [credit] at pending
  | allocatorReady => simp [credit] at pending
  | allocatorSendCode => simp [credit] at pending
  | token seed => simp [credit] at pending

private theorem expose_pair {Γ : Ctx sig} {activities : List (Activity Γ)}
    {input output : Activity Γ} (inputMember : input ∈ activities) (outputMember : output ∈ activities)
    (phase : Administrative input output) : ∃ frame, activities.Perm (input :: output :: frame) := by
  classical
  have different : output ≠ input := by cases phase <;> intro same <;> cases same
  have remaining : output ∈ activities.erase input := (List.mem_erase_of_ne different).mpr outputMember
  exact ⟨(activities.erase input).erase output,
    (List.perm_cons_erase inputMember).trans ((List.perm_cons_erase remaining).cons input)⟩

private theorem phase_shape {Γ : Ctx sig} (world : SeedWorld Γ)
    {input output : Activity Γ} (phase : Administrative input output) :
    ∃ channel body payload, input.header world.world = .input channel body ∧
      output.header world.world = .output channel payload := by
  cases phase <;> exact ⟨_, _, _, rfl, rfl⟩

private theorem phase_result {Γ : Ctx sig} (world : SeedWorld Γ)
    {input output : Activity Γ} (phase : Administrative input output) (frame : List (Activity Γ))
    (inventory : Inventory world (input :: output :: frame)) :
    ∃ result : Result world (input :: output :: frame) (contractum world input output frame),
      result.charge = 0 := by
  cases phase with
  | privateScope body guarded seed =>
      simpa only [contractum, Activity.header, Header.content] using
        private_scope_administrative world guarded seed frame inventory
  | install channel body guarded seed =>
      simpa only [contractum, Activity.header, Header.content] using
        install_administrative world channel guarded seed frame inventory
  | rearm channel body guarded self =>
      simpa only [contractum, Activity.header, Header.content] using
        rearm_administrative world channel guarded self frame inventory
  | allocatorRequest => exact allocator_request_administrative world frame inventory
  | allocatorRearm => exact allocator_rearm_administrative world frame inventory
  | token seed =>
      have member : seed ∈ tokens (.seedInput :: .token seed :: frame) := by simp [tokens, tokenSeed]
      rw [inventory.token_unique] at member
      have same : seed = world.available := by simpa using member
      subst seed
      exact token_administrative world frame inventory

/-- The next target state is obtained by a real authored COMM. It has the
same reflected source and one less unit of concrete pending work. -/
theorem administrative_step {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (positive : 0 < before.credit) :
    ∃ next : TargetProcess, Target.Step current next ∧
      ∃ witness : Witness initialWorld origin next, witness.credit + 1 = before.credit := by
  obtain ⟨input, inputMember, output, outputMember, phase⟩ := enabled_pair before.inventory positive
  obtain ⟨frame, permutation⟩ := expose_pair inputMember outputMember phase
  obtain ⟨result, zero⟩ := phase_result before.world phase frame (before.inventory.perm permutation)
  obtain ⟨channel, body, payload, inputEq, outputEq⟩ := phase_shape before.world phase
  let selected : Selection (headers before.world.world (input :: output :: frame)) :=
    { inputIndex := 0, inputBound := by simp [headers]
      outputIndex := 0, outputBound := by simp [headers]
      inputChannel := channel, body := body, outputChannel := channel, payload := payload
      inputEq := by simpa [headers] using inputEq
      outputEq := by simpa [headers] using outputEq
      channels := (rhoCanonicalEquivalent_iff _ _).mpr rfl }
  have contractumEq : selected.contractum = contractum before.world input output frame := by
    simp [selected, Selection.contractum, Selection.residue, contractum, headers, inputEq, outputEq,
      Header.content]
  let next := frontierProcess result.world.world result.activities
  have sourceEq : StructuralCongruence current.1
      (actual before.world.world (input :: output :: frame)) :=
    .trans _ _ _ (Canonical.structuralCongruence_of_canonicalize_eq before.endpoint)
      (StructuralCongruence.par_perm _ _ ((permutation.map (Activity.header before.world.world)).map Header.pattern))
  have targetEq : StructuralCongruence selected.contractum next.1 := by
    rw [contractumEq]
    exact result.endpoint
  have actualStep : Target.Step current next := supplied_selection_step before.world.world _ selected
    current next sourceEq targetEq
  have unchanged : StructuralEq (source (input :: output :: frame))
      (result.scope.close (source result.activities)) := by
    rcases result.status with status | status
    · exact status.2
    · omega
  let nextWitness : Witness initialWorld origin next :=
    { context := result.context, scope := before.scope.append result.scope
      world := result.world, activities := result.activities, inventory := result.inventory
      names := fun name => by rw [Scope.inclusion_append, result.names, before.names]
      cursor := before.cursor.trans result.cursor
      source := by
        rw [Scope.close_append]
        exact .trans before.source (before.scope.congr
          (.trans (parallel_perm (permutation.map Activity.source)) unchanged))
      endpoint := rfl }
  refine ⟨next, actualStep, nextWitness, ?_⟩
  change total result.activities + 1 = total before.activities
  rw [total_perm permutation, ← Nat.add_zero (total (input :: output :: frame)), ← zero]
  exact result.credit

/-- Every related phase can finish its pending initialization by actual
authored steps, without committing any source communication. The exact
number of these steps is the independently computed remaining credit. -/
theorem drain {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current) :
    ∃ final : TargetProcess, ∃ path : ExecutionPath Target current final,
      ∃ witness : Witness initialWorld origin final,
        witness.credit = 0 ∧ path.length = before.credit := by
  have solve : ∀ remaining : Nat, ∀ {state : TargetProcess}
      (witness : Witness initialWorld origin state), witness.credit = remaining →
      ∃ final : TargetProcess, ∃ path : ExecutionPath Target state final,
        ∃ finalWitness : Witness initialWorld origin final,
          finalWitness.credit = 0 ∧ path.length = witness.credit := by
    intro remaining
    induction remaining with
    | zero =>
        intro state witness zero
        exact ⟨state, .refl state, witness, zero, zero.symm⟩
    | succ remaining ih =>
        intro state witness positive
        obtain ⟨next, step, nextWitness, decreased⟩ := administrative_step witness (by omega)
        have remainingEq : nextWitness.credit = remaining := by omega
        obtain ⟨final, tail, finalWitness, done, length⟩ := ih nextWitness remainingEq
        refine ⟨final, .cons ⟨step⟩ tail, finalWitness, done, ?_⟩
        change tail.length + 1 = witness.credit
        omega
  exact solve before.credit before rfl

/-- A ready frontier consists only of actual source guards/messages and
the idle allocator/token. No suspended initialization activity remains. -/
def Stable {Γ : Ctx sig} : Activity Γ → Prop
  | .output _ _ | .input _ _ _ | .ready _ _ _ _ | .allocatorReady | .token _ => True
  | _ => False

theorem stable_of_zero_credit {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (zero : total activities = 0) : ∀ activity ∈ activities, Stable activity := by
  have creditZero : ∀ activity ∈ activities, credit activity = 0 := by
    intro activity member
    exact List.sum_eq_zero_iff_forall_eq_nat.mp zero _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  have noRearms : rearms activities = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro activity member
    have empty := creditZero activity member
    cases activity <;> simp_all [rearming, credit]
  have noCodes : codes activities = [] := by
    have code := inventory.rearm_code
    rw [noRearms] at code
    exact code.nil_eq.symm
  have noClients : RhoUnaryImage.clientCount activities = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro amount sumMember
    obtain ⟨activity, activityMember, rfl⟩ := List.mem_map.mp sumMember
    have empty := creditZero activity activityMember
    cases activity <;> simp_all [RhoUnaryImage.pendingWeight, credit]
  have noRequests : RhoUnaryImage.requestCount activities = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro amount sumMember
    obtain ⟨activity, activityMember, rfl⟩ := List.mem_map.mp sumMember
    have empty := creditZero activity activityMember
    cases activity <;> simp_all [RhoUnaryImage.requestWeight, credit]
  have noReceivers : count .seedInput activities = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro amount sumMember
    obtain ⟨activity, activityMember, rfl⟩ := List.mem_map.mp sumMember
    have empty := creditZero activity activityMember
    cases activity <;> simp_all [contribution, credit]
  have noReplies : replies activities = [] := by
    have balance := inventory.pending_balance
    rw [noClients, noRequests, noReceivers] at balance
    exact List.eq_nil_of_length_eq_zero (by omega)
  intro activity member
  have empty := creditZero activity member
  cases activity with
  | sendCode channel body guarded self =>
      have codeMember : (⟨self, channel, body⟩ : Owner Γ) ∈ codes activities :=
        List.mem_filterMap.mpr ⟨_, member, rfl⟩
      rw [noCodes] at codeMember
      simp at codeMember
  | reply seed =>
      have replyMember : seed ∈ replies activities := List.mem_filterMap.mpr ⟨_, member, rfl⟩
      rw [noReplies] at replyMember
      simp at replyMember
  | output channel datum => trivial
  | input channel body guarded => trivial
  | ready channel body guarded self => trivial
  | allocatorReady => trivial
  | token seed => trivial
  | privateScope body guarded => simp [credit] at empty
  | install channel body guarded => simp [credit] at empty
  | rearm channel body guarded self => simp [credit] at empty
  | request => simp [credit] at empty
  | allocatorRearm => simp [credit] at empty
  | allocatorSendCode =>
      have readyCount : count .allocatorRearm activities = 0 := by
        apply List.sum_eq_zero_iff_forall_eq_nat.mpr
        intro amount sumMember
        obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp sumMember
        have otherZero := creditZero other otherMember
        cases other <;> simp_all [contribution, credit]
      have codeCount : count .allocatorSendCode activities = 0 := inventory.allocator_code.trans readyCount
      have positive : 0 < count .allocatorSendCode activities :=
        List.sum_pos_iff_exists_pos_nat.mpr ⟨1, List.mem_map.mpr ⟨_, member, rfl⟩, by omega⟩
      omega
  | seedInput => simp [credit] at empty

/-- A terminal target cannot still have initialization work: progress
constructs an actual authored successor whenever its credit is positive. -/
theorem zero_credit_of_terminal {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (witness : Witness initialWorld origin current)
    (terminal : ∀ next, ¬ Target.Step current next) : witness.credit = 0 := by
  by_contra nonzero
  obtain ⟨next, step, _, _⟩ := administrative_step witness (Nat.pos_of_ne_zero nonzero)
  exact terminal next step

/-- For a source that cannot communicate, target normal form is exactly
the absence of pending initialization. This compares actual operational
relations, rather than a prescribed implementation schedule. -/
theorem terminal_iff_zero_credit {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (witness : Witness initialWorld origin current)
    (sourceTerminal : ∀ after, ¬ (NativeTypes.operationalTheory Γ).Step origin after) :
    (∀ next, ¬ Target.Step current next) ↔ witness.credit = 0 := by
  constructor
  · exact zero_credit_of_terminal witness
  · intro zero next step
    have bound := terminal_witness_prefix_bound witness sourceTerminal
      (.cons ⟨step⟩ (.refl next))
    change 1 ≤ witness.credit at bound
    omega

/-- Every maximal finite execution of a terminal source pays exactly the
same remaining initialization credit. Selected schedules are unnecessary. -/
theorem maximal_terminal_path_exact {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current final : TargetProcess} (witness : Witness initialWorld origin current)
    (sourceTerminal : ∀ after, ¬ (NativeTypes.operationalTheory Γ).Step origin after)
    (path : ExecutionPath Target current final) (terminal : ∀ next, ¬ Target.Step final next) :
    path.length = witness.credit := by
  obtain ⟨result⟩ := retainPrefix witness path
  have finalZero := zero_credit_of_terminal result.witness terminal
  have sourceZero : result.sourcePath.length = 0 :=
    terminal_source_length sourceTerminal result.sourcePath
  have chargesEmpty : result.charges = [] :=
    List.length_eq_zero_iff.mp (result.chargedLength.trans sourceZero)
  have balance := result.balance
  simpa only [finalZero, chargesEmpty, List.sum_nil, Nat.zero_add, Nat.add_zero] using balance

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministrativeProgress
