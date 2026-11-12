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
