import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputRoot
import Mathlib.Data.List.Dedup

/-!
# Coordinates and materialization for independent intrinsic type answers

The native representation packs a frame identity and local slot into one
variable identifier. The coordinate layer below preserves both fields;
caller variables and private query allocations occupy disjoint model
namespaces. Materialization changes private coordinates with one shared map
for the complete ordered answer vector and fixes every caller coordinate.

These are mathematical representation and publication theorems. They do
not verify C atomics, arena ownership, declaration-index revision tracking,
or the implementation of the first-order matcher. Native calls must also
exclude authored classifiers and declarations that refine a subject.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.NativeAdmission

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open Mettapedia.Logic.LP.IndependentOutputUnification
open IntrinsicTypeFacts (signature TypeTerm Declaration)

/-- The low and high halves of a native variable identifier are unsigned
32-bit fields. This arithmetic is over naturals, with the field bounds in
the type, so it cannot silently wrap. -/
def wordRadix : Nat := 4294967296

structure VariableCoordinate where
  identity : Fin wordRadix
  slot : Fin wordRadix
  deriving DecidableEq

def VariableCoordinate.packed (coordinate : VariableCoordinate) : Nat :=
  coordinate.identity.val * wordRadix + coordinate.slot.val

theorem packed_injective : Function.Injective VariableCoordinate.packed := by
  rintro ⟨⟨first, firstBound⟩, ⟨slot, slotBound⟩⟩
    ⟨⟨second, secondBound⟩, ⟨other, otherBound⟩⟩ same
  simp only [VariableCoordinate.packed] at same
  have identities : first = second := by unfold wordRadix at *; omega
  have slots : slot = other := by rw [identities] at same; omega
  subst second
  subst other
  rfl

theorem packed_fits (coordinate : VariableCoordinate) :
    coordinate.packed < wordRadix * wordRadix := by
  have first := coordinate.identity.isLt
  have second := coordinate.slot.isLt
  unfold VariableCoordinate.packed wordRadix at *
  omega

/-- A frame packs a 20-bit handle below its generation. Distinct generations
of a reused handle remain distinct identities. -/
def frameIdentity (generation handle : Nat) : Nat := generation * 1048576 + handle

theorem frame_identity_injective (first second left right : Nat)
    (leftBound : left < 1048576) (rightBound : right < 1048576) :
    frameIdentity first left = frameIdentity second right ↔
      first = second ∧ left = right := by
  unfold frameIdentity
  omega

theorem live_frame_identity_fits (generation handle : Nat)
    (generationPositive : 0 < generation) (generationBound : generation ≤ 4094)
    (handlePositive : 0 < handle) (handleBound : handle < 1048576) :
    0 < frameIdentity generation handle ∧ frameIdentity generation handle < wordRadix := by
  unfold frameIdentity wordRadix
  omega

/-- The sequential history at an acquisition boundary records the greatest
generation issued for each handle. The native atomic/free-list implementation
must realize these boundaries; it is not part of this state model. -/
abbrev GenerationHistory := Nat → Nat

def previouslyIssued (history : GenerationHistory) (identity : Nat) : Prop :=
  identity = 0 ∨ ∃ generation handle,
    0 < generation ∧ handle < 1048576 ∧ generation ≤ history handle ∧
      identity = frameIdentity generation handle

/-- A successful acquisition increases a handle's generation. The maximum
retired generation cannot be acquired again. -/
def acquireFrame (history : GenerationHistory) (handle : Nat) :
    Option (Nat × GenerationHistory) :=
  if 0 < handle ∧ handle < 1048576 ∧ history handle < 4094 then
    some (frameIdentity (history handle + 1) handle,
      Function.update history handle (history handle + 1))
  else none

theorem acquired_frame_fresh (history : GenerationHistory) (handle identity : Nat)
    (later : GenerationHistory) (acquired : acquireFrame history handle = some (identity, later)) :
    0 < identity ∧ identity < wordRadix ∧ ¬ previouslyIssued history identity ∧
      previouslyIssued later identity ∧
      (∀ old, previouslyIssued history old → previouslyIssued later old) := by
  unfold acquireFrame at acquired
  split at acquired
  · rename_i allowed
    simp only [Option.some.injEq, Prod.mk.injEq] at acquired
    obtain ⟨rfl, rfl⟩ := acquired
    obtain ⟨positive, bounded, available⟩ := allowed
    obtain ⟨idPositive, idBound⟩ := live_frame_identity_fits (history handle + 1) handle
      (by omega) (by omega) positive bounded
    refine ⟨idPositive, idBound, ?_, ?_, ?_⟩
    · rintro (ambient | ⟨oldGeneration, oldHandle, _, oldBound, issued, same⟩)
      · omega
      · obtain ⟨generations, handles⟩ :=
          (frame_identity_injective _ _ _ _ bounded oldBound).mp same
        subst oldHandle
        omega
    · right
      exact ⟨history handle + 1, handle, by omega, bounded, by simp, rfl⟩
    · intro old issued
      rcases issued with ambient | ⟨oldGeneration, oldHandle, oldPositive, oldBound, count, same⟩
      · exact Or.inl ambient
      · refine Or.inr ⟨oldGeneration, oldHandle, oldPositive, oldBound, ?_, same⟩
        by_cases equal : oldHandle = handle
        · subst oldHandle
          simpa using Nat.le.step count
        · simpa only [Function.update_of_ne equal] using count
  · cases acquired

/-- Every previously issued coordinate, including the ambient namespace, is
separate from a successfully acquired new frame. This is the freshness
premise needed when lowering a finite private inventory to native slots. -/
theorem acquired_frame_avoids_caller (history : GenerationHistory) (handle identity : Nat)
    (later : GenerationHistory) (acquired : acquireFrame history handle = some (identity, later))
    (caller : VariableCoordinate) (issued : previouslyIssued history caller.identity.val) :
    identity ≠ caller.identity.val := by
  intro same
  exact (acquired_frame_fresh history handle identity later acquired).2.2.1 (same ▸ issued)

/-- Successful slot reservation advances beyond both the current extent and
an imported inventory. Exhaustion is explicit, rather than a wrapped slot. -/
def reserveSlot (current inventory : Nat) : Option Nat :=
  let previous := max current inventory
  if previous < wordRadix - 1 then some (previous + 1) else none

theorem reserved_slot_fresh (current inventory slot : Nat)
    (reserved : reserveSlot current inventory = some slot) :
    current < slot ∧ inventory < slot ∧ slot < wordRadix := by
  unfold reserveSlot at reserved
  dsimp only at reserved
  split at reserved
  · rename_i available
    simp only [Option.some.injEq] at reserved
    have first := Nat.le_max_left current inventory
    have second := Nat.le_max_right current inventory
    unfold wordRadix at *
    omega
  · cases reserved

def reserveSlots : Nat → List Nat → Option (List Nat × Nat)
  | current, [] => some ([], current)
  | current, inventory :: later =>
      match reserveSlot current inventory with
      | none => none
      | some slot =>
          match reserveSlots slot later with
          | none => none
          | some (slots, final) => some (slot :: slots, final)

/-- Successful batches never repeat a slot or reuse an already occupied
prefix, even when later reservations have larger imported inventories. -/
theorem reserved_slots_distinct (inventories : List Nat) (current : Nat)
    (slots : List Nat) (final : Nat)
    (reserved : reserveSlots current inventories = some (slots, final)) :
    slots.Nodup ∧ (∀ slot ∈ slots, current < slot ∧ slot < wordRadix) ∧ current ≤ final := by
  induction inventories generalizing current slots final with
  | nil =>
      simp only [reserveSlots, Option.some.injEq, Prod.mk.injEq] at reserved
      obtain ⟨rfl, rfl⟩ := reserved
      simp
  | cons inventory later ih =>
      cases here : reserveSlot current inventory with
      | none => simp [reserveSlots, here] at reserved
      | some slot =>
          cases tail : reserveSlots slot later with
          | none => simp [reserveSlots, here, tail] at reserved
          | some result =>
              rcases result with ⟨rest, ending⟩
              simp only [reserveSlots, here, tail, Option.some.injEq, Prod.mk.injEq] at reserved
              obtain ⟨rfl, rfl⟩ := reserved
              obtain ⟨distinct, bounded, finalBound⟩ := ih slot rest ending tail
              obtain ⟨larger, _, fits⟩ := reserved_slot_fresh current inventory slot here
              refine ⟨List.nodup_cons.mpr ⟨?_, distinct⟩, ?_, by omega⟩
              · intro member
                have impossible := (bounded slot member).1
                omega
              · intro name member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨larger, fits⟩
                · obtain ⟨afterSlot, nameFits⟩ := bounded name member
                  exact ⟨by omega, nameFits⟩

/-- The ambient allocator leases blocks from a wider monotone cursor. Its
last lease ends at the exhaustion sentinel, without reusing identifier zero. -/
def reserveAmbientBlock (next : Nat) : Option (Nat × Nat) :=
  if 0 < next ∧ next < wordRadix then
    let count := min 4096 (wordRadix - next)
    some (count, next + count)
  else none

theorem ambient_block_bounds (next count after : Nat)
    (reserved : reserveAmbientBlock next = some (count, after)) :
    0 < next ∧ 0 < count ∧ count ≤ 4096 ∧ after = next + count ∧ after ≤ wordRadix := by
  unfold reserveAmbientBlock at reserved
  split at reserved
  · rename_i available
    dsimp only at reserved
    simp only [Option.some.injEq, Prod.mk.injEq] at reserved
    obtain ⟨rfl, rfl⟩ := reserved
    have limited := Nat.min_le_right 4096 (wordRadix - next)
    have maximum := Nat.min_le_left 4096 (wordRadix - next)
    have positive : 0 < min 4096 (wordRadix - next) := by
      exact Nat.lt_min.mpr ⟨by omega, by omega⟩
    exact ⟨available.1, positive, maximum, rfl, by omega⟩
  · cases reserved

theorem ambient_block_no_wrap (next count after : Nat)
    (reserved : reserveAmbientBlock next = some (count, after))
    (offset : Nat) (within : offset < count) :
    0 < next + offset ∧ next + offset < wordRadix := by
  obtain ⟨positive, _, _, ending, fits⟩ := ambient_block_bounds next count after reserved
  omega

/-- Threads may consume their leases in any order. Separate successful
cursor intervals still cannot produce the same ambient identifier. -/
theorem ambient_blocks_disjoint (first firstCount firstAfter second : Nat)
    (firstLease : reserveAmbientBlock first = some (firstCount, firstAfter))
    (ordered : firstAfter ≤ second) (left right : Nat)
    (leftWithin : left < firstCount) :
    first + left ≠ second + right := by
  have firstBounds := ambient_block_bounds first firstCount firstAfter firstLease
  omega

/-- A monotone cursor inside one lease preserves distinct slot identities. -/
theorem ambient_lease_distinct (start first second : Nat) (different : first ≠ second) :
    start + first ≠ start + second := by omega

/-- Encoding the full identifier preserves sharing between all occurrences
of a caller variable, regardless of its original lexical frame. -/
def callerTerm (term : TypeTerm) : TypeTerm := rename callerName term

theorem caller_name_injective : Function.Injective callerName := by
  intro first second same
  exact (Nat.pair_eq_pair.mp same).2

theorem caller_coordinate_sharing (first second : VariableCoordinate) :
    callerName first.packed = callerName second.packed ↔ first = second := by
  constructor
  · exact fun same => packed_injective (caller_name_injective same)
  · rintro rfl
    rfl

theorem caller_term_names (term : TypeTerm) :
    ∀ name ∈ (callerTerm term).freeVars, ∃ original ∈ term.freeVars,
      name = callerName original := by
  intro name member
  have origin := (Subst.mem_freeVars_applyTerm (σ := signature)).mp member
  obtain ⟨original, present, occurs⟩ := origin
  exact ⟨original, present, (Term.mem_freeVars_var (σ := signature)).mp occurs⟩

theorem caller_term_independent (term : TypeTerm) (output : Nat)
    (independent : output ∉ term.freeVars) :
    callerName output ∉ (callerTerm term).freeVars := by
  intro member
  obtain ⟨original, present, same⟩ := caller_term_names term _ member
  exact independent (caller_name_injective same ▸ present)

/-- One caller-fixed renaming is shared by the whole answer vector. Private
names are placed beneath the invocation coordinate; callers keep their full
original identifier. -/
def activationName (invocation name : Nat) : Nat :=
  if (Nat.unpair name).1 = 0 then name else Nat.pair 1 (Nat.pair invocation name)

def activationInverse (name : Nat) : Nat :=
  if (Nat.unpair name).1 = 0 then name else (Nat.unpair (Nat.unpair name).2).2

theorem activation_left_inverse (invocation : Nat) :
    Function.LeftInverse activationInverse (activationName invocation) := by
  intro name
  unfold activationName
  split
  · rename_i caller
    simp [activationInverse, caller]
  · simp [activationInverse]

theorem activation_injective (invocation : Nat) :
    Function.Injective (activationName invocation) :=
  (activation_left_inverse invocation).injective

@[simp] theorem activation_fixes_caller (invocation name : Nat) :
    activationName invocation (callerName name) = callerName name := by
  simp [activationName, callerName]

/-- No private name of one activation can equal a private name of another.
This says nothing about caller names, which intentionally stay shared. -/
theorem activation_private_disjoint (first second left right : Nat)
    (different : first ≠ second)
    (leftPrivate : (Nat.unpair left).1 ≠ 0) (rightPrivate : (Nat.unpair right).1 ≠ 0) :
    activationName first left ≠ activationName second right := by
  simp only [activationName, if_neg leftPrivate, if_neg rightPrivate,
    Nat.pair_eq_pair, true_and, ne_eq]
  exact fun same => different same.1

def activate (invocation : Nat) (term : TypeTerm) : TypeTerm :=
  rename (activationName invocation) term

theorem activation_preserves_sharing (invocation : Nat) (first second : TypeTerm) :
    activate invocation first = activate invocation second ↔ first = second := by
  constructor
  · intro same
    exact rename_injective (σ := signature) _ _ (activation_left_inverse invocation) same
  · rintro rfl
    rfl

/-- Applying a substitution after a coordinate change is precomposition on
variable bindings. The terms assigned to variables are not renamed here. -/
private theorem substitute_renamed (mapping : Nat → Nat) (theta : Subst signature)
    (term : TypeTerm) :
    theta.applyTerm (rename mapping term) =
      Subst.applyTerm (σ := signature) (fun name => theta (mapping name)) term := by
  induction term with
  | var name => rfl
  | const value => rfl
  | app symbol children ih => simp only [rename_app, Subst.applyTerm, ih]

/-- A lossless renaming that fixes the observations preserves their full
joint solution family. This transports substitutions in both directions;
it does not merely compare unifiability or individual observations. -/
theorem publication_renaming_exact (mapping inverse : Nat → Nat)
    (leftInverse : Function.LeftInverse inverse mapping)
    (problem : List (TypeTerm × TypeTerm)) (observations : List TypeTerm)
    (fixed : ∀ term ∈ observations, ∀ name ∈ term.freeVars, mapping name = name) :
    solutions (equations mapping problem) observations = solutions problem observations := by
  have restore (theta : Subst signature) (term : TypeTerm) :
      Subst.applyTerm (σ := signature) (fun name => theta (inverse name)) (rename mapping term) =
        theta.applyTerm term := by
    induction term with
    | var name => exact congrArg theta (leftInverse name)
    | const value => rfl
    | app symbol children ih => simp only [rename_app, Subst.applyTerm, ih]
  ext values
  constructor
  · rintro ⟨theta, solves, published⟩
    refine ⟨fun name => theta (mapping name), ?_, ?_⟩
    · intro pair member
      have accepted := solves _ (List.mem_map.mpr ⟨pair, member, rfl⟩)
      simpa only [substitute_renamed] using accepted
    · rw [published]
      apply List.map_congr_left
      intro term member
      apply Subst.applyTerm_congr
      intro name present
      rw [fixed term member name present]
  · rintro ⟨theta, solves, published⟩
    refine ⟨fun name => theta (inverse name), ?_, ?_⟩
    · intro pair member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      simp only [restore]
      exact solves original present
    · rw [published]
      apply List.map_congr_left
      intro term member
      apply Subst.applyTerm_congr
      intro name present
      have kept := fixed term member name present
      have inverseKept : inverse name = name := by
        simpa only [kept] using leftInverse name
      rw [inverseKept]

/-- Private freshening is transparent to an output equation and every
caller observation, including shared caller variables. -/
theorem activated_publication_exact (invocation output : Nat) (answer : TypeTerm)
    (observations : List TypeTerm)
    (callerNames : ∀ term ∈ observations, ∀ name ∈ term.freeVars,
      ∃ original, name = callerName original) :
    solutions [(activate invocation answer, .var (callerName output))] observations =
      solutions [(answer, .var (callerName output))] observations := by
  have exact := publication_renaming_exact (activationName invocation) activationInverse
    (activation_left_inverse invocation) [(answer, .var (callerName output))] observations
    (by
      intro term member name present
      obtain ⟨original, rfl⟩ := callerNames term member name present
      exact activation_fixes_caller invocation original)
  simpa only [equations, List.map_cons, List.map_nil, rename_var,
    activation_fixes_caller, activate] using exact

/-- The completed independent-output shortcut remains exact after freshening
its ordered fact vector. The caller encoding is constructed here from the
full input identities, rather than assumed to satisfy separation. -/
theorem completed_materialization_exact (library : List Declaration)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (independent : output ∉ subject.freeVars) (invocation : Nat)
    (bound fresh : List TypeTerm)
    (boundRun : run library freshSupply boundFuel path (callerTerm subject)
      (some (.var (callerName output))) = some bound)
    (freshRun : run library freshSupply freshFuel path (callerTerm subject) none = some fresh)
    (observations : List TypeTerm) :
    bound.map (fun answer => solutions [(answer, .var (callerName output))]
      (observations.map callerTerm)) =
    (fresh.map (activate invocation)).map (fun answer =>
      solutions [(answer, .var (callerName output))] (observations.map callerTerm)) := by
  have observationNames : ∀ term ∈ observations.map callerTerm,
      ∀ name ∈ term.freeVars, ∃ original, name = callerName original := by
    intro term member name present
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    obtain ⟨index, _, same⟩ := caller_term_names original name present
    exact ⟨index, same⟩
  have root := Root.caller_output_publication_exact library boundFuel freshFuel path
    (callerTerm subject) output
    (by
      intro name present
      obtain ⟨index, _, same⟩ := caller_term_names subject name present
      exact ⟨index, same⟩)
    (caller_term_independent subject output independent)
    bound fresh boundRun freshRun (observations.map callerTerm) observationNames
  rw [root, List.map_map]
  apply List.map_congr_left
  intro answer _
  exact (activated_publication_exact invocation output answer _ observationNames).symm

/-- A finite inventory assigns one-based slots to distinct source variables.
Outside that inventory the map has a disjoint mathematical extension. The
extension is used only to transport substitutions, not to allocate native
variables. Callers are fixed before consulting the private inventory. -/
def inventoryName (identity : Nat) (inventory : List Nat) (name : Nat) : Nat :=
  if (Nat.unpair name).1 = 0 then name
  else if name ∈ inventory then
    Nat.pair 1 (identity * wordRadix + (inventory.idxOf name + 1))
  else Nat.pair 2 name

def inventoryInverse (identity : Nat) (inventory : List Nat) (name : Nat) : Nat :=
  if (Nat.unpair name).1 = 0 then name
  else if (Nat.unpair name).1 = 1 then
    (inventory[(Nat.unpair name).2 - identity * wordRadix - 1]?).getD name
  else (Nat.unpair name).2

theorem inventory_left_inverse (identity : Nat) (inventory : List Nat) :
    Function.LeftInverse (inventoryInverse identity inventory)
      (inventoryName identity inventory) := by
  intro name
  unfold inventoryName
  split
  · rename_i caller
    simp [inventoryInverse, caller]
  · split
    · rename_i _ present
      simp [inventoryInverse, List.getElem?_idxOf present]
    · simp [inventoryInverse]

@[simp] theorem inventory_fixes_caller (identity : Nat) (inventory : List Nat) (name : Nat) :
    inventoryName identity inventory (callerName name) = callerName name := by
  simp [inventoryName, callerName]

/-- This is the bounded native coordinate on an inventory member. -/
def inventoryCoordinate (identity : Fin wordRadix) (inventory : List Nat)
    (fits : inventory.length < wordRadix) (name : Nat) (present : name ∈ inventory) :
    VariableCoordinate :=
  ⟨identity, ⟨inventory.idxOf name + 1, by
    have indexBound := List.idxOf_lt_length_of_mem present
    omega⟩⟩

theorem inventory_names_are_packed (identity : Fin wordRadix) (inventory : List Nat)
    (fits : inventory.length < wordRadix) (name : Nat) (present : name ∈ inventory)
    (isPrivate : (Nat.unpair name).1 ≠ 0) :
    inventoryName identity.val inventory name =
      Nat.pair 1 (inventoryCoordinate identity inventory fits name present).packed := by
  simp [inventoryName, isPrivate, present, inventoryCoordinate, VariableCoordinate.packed]

theorem inventory_coordinate_injective (identity : Fin wordRadix) (inventory : List Nat)
    (fits : inventory.length < wordRadix) (first second : Nat)
    (firstPresent : first ∈ inventory) (secondPresent : second ∈ inventory) :
    (inventoryCoordinate identity inventory fits first firstPresent).packed =
      (inventoryCoordinate identity inventory fits second secondPresent).packed ↔ first = second := by
  simp only [inventoryCoordinate, VariableCoordinate.packed, Nat.add_right_inj, Nat.add_left_inj]
  exact List.idxOf_inj firstPresent

/-- A fresh frame does not capture any caller from another frame, including
ambient variables. Bounds exclude the possibility of low-slot overflow. -/
theorem inventory_coordinate_avoids_caller (identity : Fin wordRadix) (inventory : List Nat)
    (fits : inventory.length < wordRadix) (name : Nat) (present : name ∈ inventory)
    (caller : VariableCoordinate) (freshFrame : identity ≠ caller.identity) :
    (inventoryCoordinate identity inventory fits name present).packed ≠ caller.packed := by
  intro same
  exact freshFrame (congrArg VariableCoordinate.identity (packed_injective same))

/-- A successful generation increment supplies the freshness condition for
every retained caller coordinate from the recorded history. -/
theorem acquired_inventory_avoids_caller (history : GenerationHistory) (handle : Nat)
    (identity : Fin wordRadix) (later : GenerationHistory)
    (acquired : acquireFrame history handle = some (identity.val, later))
    (inventory : List Nat) (fits : inventory.length < wordRadix)
    (name : Nat) (present : name ∈ inventory) (caller : VariableCoordinate)
    (issued : previouslyIssued history caller.identity.val) :
    (inventoryCoordinate identity inventory fits name present).packed ≠ caller.packed := by
  apply inventory_coordinate_avoids_caller identity inventory fits name present caller
  intro same
  exact acquired_frame_avoids_caller history handle identity.val later acquired caller issued
    (congrArg Fin.val same)

/-- The same finite mapping is applied to every alternative. A repeated
source name therefore has one coordinate even across different answers. -/
def materialize (identity : Nat) (inventory : List Nat) (answers : List TypeTerm) :
    List TypeTerm := answers.map (rename (inventoryName identity inventory))

theorem materialization_preserves_ordered_sharing (identity : Nat) (inventory : List Nat)
    (first second : List TypeTerm) :
    materialize identity inventory first = materialize identity inventory second ↔ first = second := by
  constructor
  · intro same
    have inj := rename_injective (σ := signature) _ _ (inventory_left_inverse identity inventory)
    exact List.map_injective_iff.mpr inj same
  · rintro rfl
    rfl

/-- Fresh intrinsic answers contain no caller variable. This justifies
freshening every variable of a retained answer, while leaving its later
caller output and observations untouched. -/
theorem fresh_answers_private (library : List Declaration) (fuel : Nat) (path : Path)
    (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library freshSupply fuel path subject none = some answers) :
    ∀ answer ∈ answers, ∀ name ∈ answer.freeVars, (Nat.unpair name).1 ≠ 0 := by
  intro answer present name occurs caller
  have same : name = callerName (Nat.unpair name).2 := by
    simpa only [callerName, caller] using (Nat.pair_unpair name).symm
  have absent := Admission.run_output_excludes_name library fuel path subject none answers
    (callerName (Nat.unpair name).2)
    (fun stem slot => fresh_supply_separate (stem ++ path) slot _)
    (by simp) returned answer present
  exact absent (same ▸ occurs)

/-- On a private answer scheme the caller-fixed activation is precisely the
existing fact materializer's nested scope. Its extension to callers supplies
the fixed-observation property required by root publication. -/
theorem private_activation_is_fact_scope (invocation : Nat) (term : TypeTerm)
    (privateNames : ∀ name ∈ term.freeVars, (Nat.unpair name).1 ≠ 0) :
    activate invocation term =
      IntrinsicTypeFacts.scope 1 (IntrinsicTypeFacts.scope invocation term) := by
  unfold activate IntrinsicTypeFacts.scope
  rw [rename_comp]
  apply Subst.applyTerm_congr
  intro name present
  simp only [activationName, if_neg (privateNames name present), Function.comp_apply]

/-- The shared inventory renaming is transparent to root publication.
The bounded coordinate theorem below identifies its supported variables
with actual frame/slot coordinates. -/
theorem completed_inventory_publication_exact (library : List Declaration)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (independent : output ∉ subject.freeVars) (identity : Nat) (inventory : List Nat)
    (bound fresh : List TypeTerm)
    (boundRun : run library freshSupply boundFuel path (callerTerm subject)
      (some (.var (callerName output))) = some bound)
    (freshRun : run library freshSupply freshFuel path (callerTerm subject) none = some fresh)
    (observations : List TypeTerm) :
    bound.map (fun answer => solutions [(answer, .var (callerName output))]
      (observations.map callerTerm)) =
    (materialize identity inventory fresh).map (fun answer =>
      solutions [(answer, .var (callerName output))] (observations.map callerTerm)) := by
  have observationNames : ∀ term ∈ observations.map callerTerm,
      ∀ name ∈ term.freeVars, ∃ original, name = callerName original := by
    intro term member name present
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    obtain ⟨index, _, same⟩ := caller_term_names original name present
    exact ⟨index, same⟩
  have root := Root.caller_output_publication_exact library boundFuel freshFuel path
    (callerTerm subject) output
    (by
      intro name present
      obtain ⟨index, _, same⟩ := caller_term_names subject name present
      exact ⟨index, same⟩)
    (caller_term_independent subject output independent)
    bound fresh boundRun freshRun (observations.map callerTerm) observationNames
  rw [root, materialize, List.map_map]
  apply List.map_congr_left
  intro answer _
  have same := publication_renaming_exact (inventoryName identity inventory)
    (inventoryInverse identity inventory) (inventory_left_inverse identity inventory)
    [(answer, .var (callerName output))] (observations.map callerTerm)
    (by
      intro term member name present
      obtain ⟨original, rfl⟩ := observationNames term member name present
      exact inventory_fixes_caller identity inventory original)
  simpa only [equations, List.map_cons, List.map_nil, rename_var,
    inventory_fixes_caller, Function.comp_apply] using same.symm

/-- One inventory covers the entire answer vector. Its order is immaterial
to publication, but it is shared rather than rebuilt for each answer. -/
def variableOccurrences : TypeTerm → List Nat
  | .var name => [name]
  | .const _ => []
  | .app _ children => (List.ofFn fun index => variableOccurrences (children index)).flatten

theorem variable_occurrences_exact (term : TypeTerm) (name : Nat) :
    name ∈ variableOccurrences term ↔ name ∈ term.freeVars := by
  induction term with
  | var other => simp [variableOccurrences, Term.freeVars]
  | const value => simp [variableOccurrences, Term.freeVars]
  | app symbol children ih => simp [variableOccurrences, Term.freeVars, ih]

def answerInventory (answers : List TypeTerm) : List Nat :=
  (answers.flatMap variableOccurrences).dedup

theorem answer_inventory_complete (answers : List TypeTerm) (answer : TypeTerm)
    (present : answer ∈ answers) (name : Nat) (occurs : name ∈ answer.freeVars) :
    name ∈ answerInventory answers := by
  simp only [answerInventory, List.mem_dedup, List.mem_flatMap, variable_occurrences_exact]
  exact ⟨answer, present, occurs⟩

theorem answer_inventory_distinct (answers : List TypeTerm) :
    (answerInventory answers).Nodup := List.nodup_dedup _

/-- Every variable actually published by a completed query materializes to
an in-bounds frame/slot coordinate. The out-of-inventory extension of the
renaming is never used on an answer. -/
theorem completed_materialized_coordinates (library : List Declaration)
    (fuel : Nat) (path : Path) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library freshSupply fuel path subject none = some answers)
    (identity : Fin wordRadix) (fits : (answerInventory answers).length < wordRadix)
    (answer : TypeTerm) (present : answer ∈ answers) (name : Nat)
    (occurs : name ∈ (rename (inventoryName identity.val (answerInventory answers)) answer).freeVars) :
    ∃ original, ∃ source : original ∈ answer.freeVars,
      name = Nat.pair 1 (inventoryCoordinate identity (answerInventory answers) fits original
        (answer_inventory_complete answers answer present original source)).packed := by
  obtain ⟨original, source, renamed⟩ :=
    (Subst.mem_freeVars_applyTerm (σ := signature)).mp occurs
  have named : name = inventoryName identity.val (answerInventory answers) original :=
    (Term.mem_freeVars_var (σ := signature)).mp renamed
  refine ⟨original, source, named.trans ?_⟩
  exact inventory_names_are_packed identity (answerInventory answers) fits original
    (answer_inventory_complete answers answer present original source)
    (fresh_answers_private library fuel path subject answers returned answer present original source)

/-- The one-inventory materializer preserves tree size. Any cost account for
warm publication must still charge the retained answer occurrences; a cache
hit alone does not imply constant work. -/
def materializationNodes (answers : List TypeTerm) : Nat :=
  (answers.map Term.size).sum

theorem rename_preserves_size (mapping : Nat → Nat) (term : TypeTerm) :
    (rename mapping term).size = term.size := by
  induction term with
  | var name => rfl
  | const value => rfl
  | app symbol children ih => simp only [rename_app, Term.size, ih]

theorem materialization_nodes_exact (identity : Nat) (inventory : List Nat)
    (answers : List TypeTerm) :
    materializationNodes (materialize identity inventory answers) = materializationNodes answers := by
  simp only [materializationNodes, materialize, List.map_map]
  congr 1
  apply List.map_congr_left
  intro answer _
  exact rename_preserves_size _ answer

/-- Repeated answer occurrences have repeated materialization size even when
their private variable is shared. -/
theorem repeated_variable_materialization (count name identity : Nat) :
    materializationNodes (materialize identity [name]
      (List.replicate count (.var name))) = count := by
  rw [materialization_nodes_exact]
  simp [materializationNodes, Term.size]

section RetainedFacts

open Mettapedia.Machines.RevisionedQueryFacts

variable {Stamp Key : Type} [DecidableEq Stamp] [DecidableEq Key]

/-- Cache transparency and root publication compose at a completed intrinsic
computation. Cache validity is the existing immutable-fact invariant; the
completion premise refers to the executable Lean query, not to unverified C.
No incomplete evaluation is converted into an empty fact vector. -/
theorem retained_completed_publication_exact
    (compute : Stamp → Key → List TypeTerm) (query : Request Stamp Key)
    (cache : Cache Stamp Key TypeTerm) (valid : Valid compute cache)
    (library : List Declaration) (boundFuel freshFuel : Nat) (path : Path)
    (subject : TypeTerm) (output : Nat) (independent : output ∉ subject.freeVars)
    (identity : Nat) (inventory : List Nat) (bound : List TypeTerm)
    (boundRun : run library freshSupply boundFuel path (callerTerm subject)
      (some (.var (callerName output))) = some bound)
    (freshRun : run library freshSupply freshFuel path (callerTerm subject) none =
      some (compute query.stamp query.key)) (observations : List TypeTerm) :
    bound.map (fun answer => solutions [(answer, .var (callerName output))]
      (observations.map callerTerm)) =
    (materialize identity inventory (request compute query cache).facts).map (fun answer =>
      solutions [(answer, .var (callerName output))] (observations.map callerTerm)) := by
  rw [request_exact compute query cache valid]
  exact completed_inventory_publication_exact library boundFuel freshFuel path subject output
    independent identity inventory bound (compute query.stamp query.key) boundRun freshRun observations

/-- A resident fact avoids the service computation, while materialization
still traverses each answer occurrence. This is an exact count in the fact
interface; it makes no constant-time claim about native lookup or copying. -/
theorem resident_materialization_work (compute : Stamp → Key → List TypeTerm)
    (query : Request Stamp Key) (cache : Cache Stamp Key TypeTerm)
    (valid : Valid compute cache) (hit : (lookup query.stamp query.key cache).isSome)
    (identity : Nat) (inventory : List Nat) :
    (request compute query cache).computations = 0 ∧
      (materialize identity inventory (request compute query cache).facts).length =
        (compute query.stamp query.key).length := by
  exact ⟨hit_skips_computation compute query cache hit,
    by simp only [materialize, List.length_map, request_exact compute query cache valid]⟩

end RetainedFacts

/-- Equal low slots in different frames are different caller variables. -/
example : callerName (VariableCoordinate.packed ⟨⟨1, by decide⟩, ⟨7, by decide⟩⟩) ≠
    callerName (VariableCoordinate.packed ⟨⟨2, by decide⟩, ⟨7, by decide⟩⟩) := by
  decide

/-- Forgetting the high half would merge precisely those distinct variables. -/
example : (VariableCoordinate.slot ⟨⟨1, by decide⟩, ⟨7, by decide⟩⟩).val =
    (VariableCoordinate.slot ⟨⟨2, by decide⟩, ⟨7, by decide⟩⟩).val := rfl

/-- The same private variable in two answers stays shared. -/
example : [Nat.pair 1 0, Nat.pair 1 0].map (inventoryName 17 [Nat.pair 1 0]) =
    [Nat.pair 1 (17 * wordRadix + 1), Nat.pair 1 (17 * wordRadix + 1)] := by
  simp [inventoryName]

/-- Per-answer freshening would destroy sharing across the ordered vector. -/
example : inventoryName 17 [Nat.pair 1 0] (Nat.pair 1 0) ≠
    inventoryName 18 [Nat.pair 1 0] (Nat.pair 1 0) := by
  simp [inventoryName, Nat.pair_eq_pair, wordRadix]

/-- Two slots of one activation stay distinct; callers are unchanged. -/
example : inventoryName 17 [2, 3] 2 ≠ inventoryName 17 [2, 3] 3 := by
  exact fun same => (inventory_left_inverse 17 [2, 3]).injective.ne (by decide) same
example : inventoryName 17 [1, 2] (callerName 9) = callerName 9 :=
  inventory_fixes_caller 17 [1, 2] 9

example : reserveSlots 0 [0, 0, 7] = some ([1, 2, 8], 8) := by decide
example : reserveSlot 4294967295 0 = none := by decide

example : reserveAmbientBlock 4294967295 = some (1, 4294967296) := by decide
example : reserveAmbientBlock 4294967296 = none := by decide


example : (acquireFrame (fun _ => 0) 7).map Prod.fst = some (frameIdentity 1 7) := by
  simp [acquireFrame]

example : acquireFrame (fun _ => 4094) 7 = none := by simp [acquireFrame]


end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.NativeAdmission
