import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionSelections

/-!
# Region ownership survives every actual streaming transition

The proof follows the existing placement, delivery and controller rules.
Opening a region earns a fresh marker; alternatives share the ordered older
markers. Cuts retain a valid suffix, and collection updates keep association.
No assumption about source termination or completed operand batches is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions

theorem open_collection (state : State) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (control : Unifying.Control) (caller : List Frame) (older : List Job)
    (pending : valid state.nextBoundary older) (fits : framesFit (markers older) caller) :
    WellFormed (openCollection state bindings control caller older) := by
  refine ⟨⟨Nat.lt_succ_self _,pending.1⟩,?_,fits,pending.2⟩
  exact ⟨[],markers older,rfl,fits⟩

theorem open_handler (state : State) (control : Unifying.Control) (caller : List Frame) (older : List Job)
    (pending : valid state.nextBoundary older) (fits : framesFit (markers older) caller) :
    WellFormed (openHandler state control caller older) := by
  refine ⟨⟨Nat.lt_succ_self _,pending.1⟩,?_,True.intro,pending.2⟩
  exact ⟨[],markers older,rfl,fits⟩

theorem open_first (state : State) (control : Unifying.Control) (caller : List Frame) (older : List Job)
    (pending : valid state.nextBoundary older) (fits : framesFit (markers older) caller) :
    WellFormed (openFirst state control caller older) := by
  refine ⟨⟨Nat.lt_succ_self _,pending.1⟩,?_,True.intro,pending.2⟩
  exact ⟨[],markers older,rfl,fits⟩

theorem placement_wellFormed {state : State} {after : Unifying.Configuration}
    {caller : List Frame} {older : List Job} {target : State}
    (placement : Placement state after caller older target)
    (pending : valid state.nextBoundary older) (fits : framesFit (markers older) caller) :
    WellFormed target := by
  cases placement with
  | plain => exact valid_execute pending fits
  | collection => exact open_collection _ _ _ _ _ pending fits
  | handler => exact open_handler _ _ _ _ pending fits
  | waiting => exact valid_execute pending fits

theorem delivery_wellFormed {registry : SpaceSemantics.Program} {state target : State}
    {answer : Unifying.Answer} {frames : List Frame} {older : List Job}
    (delivery : Delivery registry state answer frames older target)
    (pending : valid state.nextBoundary older) (fits : framesFit (markers older) frames) :
    WellFormed target := by
  cases delivery with
  | root => exact pending
  | source source placement => exact placement_wellFormed placement pending fits
  | collection recorded => exact collection_valid recorded pending
  | handler => exact valid_execute pending (frames_tail fits)
  | first found => exact valid_execute (selected_suffix_valid pending found) (first_cut pending.1 fits found)

theorem head_and_tail {state : State} {job : Job} {older : List Job}
    (good : WellFormed state) (agenda : state.agenda = job :: older) :
    jobFits (markers older) job ∧ valid state.nextBoundary older := by
  change valid state.nextBoundary state.agenda at good
  rw [agenda] at good
  exact ⟨good.2.1,valid_tail good⟩

theorem transition_wellFormed {registry : SpaceSemantics.Program} {before after : State}
    (transition : Transition registry before after) (good : WellFormed before) : WellFormed after := by
  cases transition with
  | collection_done agenda =>
      obtain ⟨fits,pending⟩ := head_and_tail good agenda
      exact valid_execute pending fits
  | handler_done agenda | first_done agenda | empty agenda => exact (head_and_tail good agenda).2
  | answer agenda delivered =>
      obtain ⟨fits,pending⟩ := head_and_tail good agenda
      apply delivery_wellFormed delivered (valid_later_answers _ pending fits)
      simpa only [markers_later_answers,jobFits] using fits
  | alternatives agenda =>
      obtain ⟨fits,pending⟩ := head_and_tail good agenda
      apply valid_later_answers _ (valid_alternatives _ pending fits)
      simpa only [markers_alternatives,jobFits] using fits
  | collection_enter agenda =>
      obtain ⟨fits,pending⟩ := head_and_tail good agenda
      exact open_collection _ _ _ _ _ pending fits
  | first_enter agenda =>
      obtain ⟨fits,pending⟩ := head_and_tail good agenda
      exact open_first _ _ _ _ pending fits
  | caught agenda handler closed => exact selected_suffix_valid (head_and_tail good agenda).2 closed
  | phase agenda ordinary source placed =>
      obtain ⟨fits,pending⟩ := head_and_tail good agenda
      exact placement_wellFormed placed pending fits

/-! ## Exact issuance and retirement -/

/-- A controller step either retains an ordered subset of its old
markers without allocating, or issues its next identity in front of
all its old markers. Bank contents are not ownership metadata. -/
def MarkerDelta (limit : Nat) (previous : List Boundary) (after : State) : Prop :=
  (after.nextBoundary = limit ∧ (markers after.agenda).Sublist previous) ∨
    ∃ born : Boundary, born.key = limit ∧ after.nextBoundary = limit + 1 ∧
      markers after.agenda = born :: previous

private theorem markers_execute (task : Task) (older : List Job) :
    markers (.execute task :: older) = markers older := rfl

private theorem markers_after_sublist {pick : Job → Bool} {older remaining : List Job}
    (cut : List.FirstSelection.After pick older remaining) : (markers remaining).Sublist (markers older) := by
  have suffix : remaining.Sublist older := by
    induction cut with
    | here _ => exact List.sublist_cons_self ..
    | skip _ _ ih => exact ih.cons _
  exact suffix.filterMap boundary

private theorem placement_marker_delta {state : State} {after : Unifying.Configuration} {caller : List Frame}
    {older : List Job} {target : State} (placed : Placement state after caller older target) :
    MarkerDelta state.nextBoundary (markers older) target := by
  cases placed with
  | plain | waiting => exact .inl ⟨rfl, List.Sublist.refl _⟩
  | collection => exact .inr ⟨.collection state.nextBoundary caller, rfl, rfl, rfl⟩
  | handler => exact .inr ⟨.handler state.nextBoundary, rfl, rfl, rfl⟩

private theorem delivery_marker_delta {registry : SpaceSemantics.Program} {state target : State}
    {answer : Unifying.Answer} {frames : List Frame} {older : List Job}
    (delivery : Delivery registry state answer frames older target) :
    MarkerDelta state.nextBoundary (markers older) target := by
  cases delivery with
  | root | handler => exact .inl ⟨rfl, List.Sublist.refl _⟩
  | source _ placed => exact placement_marker_delta placed
  | collection recorded => exact .inl ⟨rfl, (collection_markers recorded).symm ▸ List.Sublist.refl _⟩
  | first found => exact .inl ⟨rfl, by simpa only [markers_execute] using markers_after_sublist found⟩

/-- The actual transitions determine exactly which marker identities
may appear. Delivering into a bank is not an allocation. Closing,
cutting to a first answer and unwinding an error cannot revive a marker. -/
theorem transition_marker_delta {registry : SpaceSemantics.Program} {before after : State}
    (transition : Transition registry before after) :
    MarkerDelta before.nextBoundary (markers before.agenda) after := by
  cases transition with
  | collection_done agenda | handler_done agenda | first_done agenda =>
      rw [agenda]
      exact .inl ⟨rfl, List.sublist_cons_self ..⟩
  | empty agenda =>
      rw [agenda]
      exact .inl ⟨rfl, List.Sublist.refl _⟩
  | answer agenda delivered =>
      rw [agenda, markers_execute]
      simpa only [markers_later_answers] using delivery_marker_delta delivered
  | alternatives agenda =>
      rw [agenda]
      left
      refine ⟨rfl, ?_⟩
      rw [markers_later_answers, markers_alternatives]
      exact List.Sublist.refl _
  | collection_enter agenda =>
      rw [agenda]
      exact .inr ⟨.collection before.nextBoundary _, rfl, rfl, rfl⟩
  | first_enter agenda =>
      rw [agenda]
      exact .inr ⟨.first before.nextBoundary, rfl, rfl, rfl⟩
  | caught agenda _ closed =>
      rw [agenda, markers_execute]
      exact .inl ⟨rfl, markers_after_sublist closed⟩
  | phase agenda _ _ placed =>
      rw [agenda, markers_execute]
      exact placement_marker_delta placed

/-- This is stronger than monotonicity of the allocation counter: a
retired, previously issued marker cannot silently reappear in an
arbitrary later controller state on the same request. -/
theorem transition_no_reissue {registry : SpaceSemantics.Program} {before after : State} {key : Nat}
    (transition : Transition registry before after) (issued : key < before.nextBoundary)
    (retired : ∀ b ∈ markers before.agenda, b.key ≠ key) :
    ∀ b ∈ markers after.agenda, b.key ≠ key := by
  rcases transition_marker_delta transition with ⟨_, keep⟩ | ⟨born, identity, _, all⟩
  · exact fun b member => retired b (keep.subset member)
  · intro b member
    rw [all] at member
    rcases List.mem_cons.mp member with rfl | older
    · intro same
      omega
    · exact retired b older

theorem path_no_reissue {registry : SpaceSemantics.Program} {before after : State} {key : Nat}
    (path : Relation.ReflTransGen (Transition registry) before after) (issued : key < before.nextBoundary)
    (retired : ∀ b ∈ markers before.agenda, b.key ≠ key) :
    ∀ b ∈ markers after.agenda, b.key ≠ key := by
  induction path with
  | refl => exact retired
  | tail previous taken ih =>
      exact transition_no_reissue taken (issued.trans_le (path_boundary_mono previous)) ih

theorem step_wellFormed {registry : SpaceSemantics.Program} {before after : State}
    (computed : step registry before = some after) (good : WellFormed before) : WellFormed after :=
  transition_wellFormed ((step_iff_transition registry before after).mp computed) good

theorem path_wellFormed {registry : SpaceSemantics.Program} {before after : State}
    (path : Relation.ReflTransGen (Transition registry) before after) (good : WellFormed before) :
    WellFormed after := by
  induction path with
  | refl => exact good
  | tail previous taken ih => exact transition_wellFormed taken ih

theorem advance_wellFormed (registry : SpaceSemantics.Program) (fuel : Nat) (state : State)
    (good : WellFormed state) : WellFormed (advance registry fuel state) :=
  path_wellFormed (advance_reachable registry fuel state) good

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions
