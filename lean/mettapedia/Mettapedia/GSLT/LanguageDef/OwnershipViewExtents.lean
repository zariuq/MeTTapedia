import Mettapedia.GSLT.LanguageDef.OwnershipAdmission
import Mettapedia.Machines.CMemory.RegionScaling

/-!
# Interpreting whole-view permission units

Whole dynamic spans retain their complete footprint without choosing a byte
length during native checking. A unit on such an input root is interpreted by
the caller's byte extent; ordinary C object roots have weight one. This module
proves the state and access interpretation for every extent, including zero.
It does not authorize numeric pointer accesses to an abstract unit.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Ownership

open Mettapedia.Machines.CMemory
open Borrowing

def scaleAllocation (weight : Nat → Nat) (a : Allocation) : Allocation :=
  { a with count := a.count * weight a.root }

def scaleField (weight : Nat → Nat) (f : FieldResult) : FieldResult :=
  { f with region := f.region.map (Region.scale weight) }

def scaleState (weight : Nat → Nat) (s : State) : State :=
  { s with loans := s.loans.map (Loan.scale weight)
           allocations := s.allocations.map (scaleAllocation weight)
           result := s.result.map (Region.scale weight)
           transfers := s.transfers.map (fun t => { t with region := t.region.scale weight })
           fieldResults := s.fieldResults.map (scaleField weight)
           recordResults := s.recordResults.map (scaleField weight) }

theorem scale_allocation_region (weight : Nat → Nat) (a : Allocation) :
    (scaleAllocation weight a).region = a.region.scale weight := by
  simp [scaleAllocation, Allocation.region, Region.scale]

theorem compatible_scale (weight : Nat → Nat) {a b : Loan} (compatible : Compatible a b) :
    Compatible (Loan.scale weight a) (Loan.scale weight b) := by
  rcases compatible with parent | parent | apart | shared
  · exact Or.inl parent
  · exact Or.inr (Or.inl parent)
  · exact Or.inr (Or.inr (Or.inl (Region.scale_disjoint weight apart)))
  · exact Or.inr (Or.inr (Or.inr shared))

theorem valid_scale (weight : Nat → Nat) {s : State} (valid : Valid s) :
    Valid (scaleState weight s) := by
  obtain ⟨ids, roots, authorities, ordered, covered, parents, compatible, live, holders⟩ := valid
  refine ⟨?_, ?_, authorities, ordered_scale weight ordered, ?_, ?_, ?_, ?_, holders⟩
  · simpa [scaleState, Loan.scale, List.map_map, Function.comp_def] using ids
  · simpa [scaleState, scaleAllocation, List.map_map, Function.comp_def] using roots
  · intro l present
    obtain ⟨before, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨a, allocated, inside⟩ := covered before member
    refine ⟨scaleAllocation weight a, List.mem_map.mpr ⟨a, allocated, rfl⟩, ?_⟩
    rw [scale_allocation_region]
    exact Region.scale_contains weight inside
  · intro l present id ancestor
    obtain ⟨before, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨p, pmem, same, inside, mode⟩ := parents before member id ancestor
    exact ⟨Loan.scale weight p, List.mem_map.mpr ⟨p, pmem, rfl⟩, same,
      Region.scale_contains weight inside, mode⟩
  · intro a ma b mb different
    obtain ⟨oldA, oldMA, rfl⟩ := List.mem_map.mp ma
    obtain ⟨oldB, oldMB, rfl⟩ := List.mem_map.mp mb
    exact compatible_scale weight (compatible oldA oldMA oldB oldMB different)
  · intro token present
    obtain ⟨a, member, root, origin⟩ := live token present
    exact ⟨scaleAllocation weight a, List.mem_map.mpr ⟨a, member, rfl⟩, root, origin⟩

theorem accessed_footprint_scale (weight : Nat → Nat) {s : State} {id : Nat}
    {region : Region} {writing : Bool} (access : Access s.loans id region writing) :
    Access (scaleState weight s).loans id (region.scale weight) writing :=
  access_scale weight access

/-- At every intermediate point permitted by the recorded control flow, the
interpreted loans remain compatible for arbitrary whole-span extents. -/
theorem prefix_valid_scale (weight : Nat → Nat) {callables : List Callable}
    {f : Function} {reached : State}
    (path : PermissionFlow.Prefix (enabled callables f) f.body initial reached) :
    Valid (scaleState weight reached) :=
  valid_scale weight (path.invariant (fun _ _ _ step state => enabled_valid step state) initial_valid)

/-- Only roots declared as whole-view inputs change units. Local records,
ordinary pointees and static storage retain their existing byte geometry. -/
def viewWeight (f : Function) (bytes : Nat → Nat) (root : Nat) : Nat :=
  if wholeInput f root then bytes root else 1

theorem ordinary_frame_unchanged (f : Function) (bytes : Nat → Nat) (region : Region)
    (ordinary : wholeInput f region.root = false) :
    region.scale (viewWeight f bytes) = region := by
  apply preserve_concrete
  simp [viewWeight, ordinary]

theorem admitted_whole_region (f : Function) (region : Region)
    (whole : wholeInput f region.root = true) (accepted : wholeRegion f region = true) :
    region.first = 0 ∧ region.count = 1 := by
  simpa [wholeRegion, whole] using accepted

theorem findLoan_scale (weight : Nat → Nat) (s : State) (id : Nat) :
    findLoan (scaleState weight s) id = (findLoan s id).map (Loan.scale weight) := by
  simp only [findLoan, scaleState, List.find?_map, Function.comp_def, Loan.scale]

/-- The actual view-call permission check succeeds at every interpreted byte
extent, including an empty span. No fixed positive length is assumed. -/
theorem view_call_scale (weight : Nat → Nat) {s after : State} {id : Nat} {writing : Bool}
    (passed : passArgument s (.viewed writing) (.loan id) = some after) :
    passArgument (scaleState weight s) (.viewed writing) (.loan id) =
      some (scaleState weight s) := by
  obtain ⟨l, found, rest⟩ := Option.bind_eq_some_iff.mp passed
  obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨_, access, _⟩ := Option.bind_eq_some_iff.mp rest
  have usable : Access s.loans id l.region writing := of_decide_eq_true (require_some access)
  have scaled := accessed_footprint_scale weight usable
  simp only [passArgument, passBorrow, findLoan_scale, found, Option.map_some]
  simp [require, scaled, Loan.scale]

namespace WholeViewControls

def reader : Function :=
  ⟨"reader", ⟨[.viewed false], false, .value, [], []⟩, [7], [], .value, .done⟩

def inputState : State :=
  { initial with loans := initial.loans ++ [⟨7, ⟨7, 0, 1⟩, .shared, []⟩]
                 allocations := initial.allocations ++ [⟨7, 1, .input⟩] }

def dynamicCallee : Callable := ⟨"dynamic", ⟨[.viewed false], false, .value, [], []⟩⟩
def byteCallee : Callable := ⟨"byte", ⟨[.borrowed 1 false], false, .value, [], []⟩⟩

theorem acquire_input :
    enabled [] reader initial (.root 7 1 .shared .input 0) = some inputState := by decide

theorem dynamic_call :
    enabled [dynamicCallee] reader inputState (.invoke "dynamic" [.loan 7]) = some inputState := by decide

theorem fixed_byte_call_refused :
    enabled [byteCallee] reader inputState (.invoke "byte" [.loan 7]) = none := by decide

theorem symbolic_subextent_refused :
    enabled [] reader inputState (.restrict 7 ⟨7, 0, 0⟩) = none := by decide

theorem view_length_cannot_be_forged :
    enabled [] reader inputState (.view 7 ⟨7, 0, 1⟩ 2 false) = none := by decide

theorem concrete_zero_bytes :
    (findLoan (scaleState (viewWeight reader (fun _ => 0)) inputState) 7).map
      (fun l => l.region.count) = some 0 := by decide

theorem concrete_large_bytes :
    (findLoan (scaleState (viewWeight reader (fun _ => 4096)) inputState) 7).map
      (fun l => l.region.count) = some 4096 := by decide

theorem actual_span_call (n : Nat) :
    passArgument (scaleState (viewWeight reader (fun _ => n)) inputState) (.viewed false) (.loan 7) =
      some (scaleState (viewWeight reader (fun _ => n)) inputState) :=
  view_call_scale _ (by decide : passArgument inputState (.viewed false) (.loan 7) = some inputState)

end WholeViewControls

end Mettapedia.GSLT.LanguageDef.Ownership
