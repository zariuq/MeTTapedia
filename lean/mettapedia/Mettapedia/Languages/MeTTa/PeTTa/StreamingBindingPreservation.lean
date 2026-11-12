import Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingInvariant

/-!
# Every actual streaming step preserves branch binding validity

The proof follows the independent controller, delivery and placement rules.
Ordinary phases reuse the existing unifier's actual refinement theorem.
Collection, first demand and caught faults preserve the retained frontier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.BindingInvariant

open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

theorem placement_refines {initial : Subst} {state : State} {after : Unifying.Configuration}
    {caller : List Frame} {older : List Job} {target : State}
    (placement : Placement state after caller older target)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.BindingRefines initial answer.bindings)
    (localPhase : Unifying.ConfigurationRefines initial after)
    (frames : framesRefine initial caller) (pending : agendaRefines initial older) :
    stateRefines initial target := by
  cases placement with
  | plain =>
      exact ⟨(agenda_cons _ _ _).mpr ⟨⟨localPhase.1,frames⟩,pending⟩,rootAnswers⟩
  | collection frameShape =>
      apply open_collection _ _ _ _ _ _ rootAnswers _ localPhase.1 frames pending
      exact localPhase.2 _ (by rw [frameShape]; exact List.mem_singleton_self _)
  | handler => exact open_handler _ _ _ _ _ rootAnswers localPhase.1 frames pending
  | waiting frameShape ordinary =>
      refine ⟨(agenda_cons _ _ _).mpr ⟨⟨localPhase.1,?_⟩,pending⟩,rootAnswers⟩
      apply (frames_cons _ _ _).mpr
      exact ⟨localPhase.2 _ (by rw [frameShape]; exact List.mem_singleton_self _),frames⟩

theorem delivery_refines {registry : SpaceSemantics.Program} {initial : Subst} {state target : State}
    {answer : Unifying.Answer} {frames : List Frame} {older : List Job}
    (delivery : Delivery registry state answer frames older target)
    (rootAnswers : ∀ packet ∈ state.answers, Unifying.BindingRefines initial packet.bindings)
    (validAnswer : Unifying.BindingRefines initial answer.bindings)
    (caller : framesRefine initial frames) (pending : agendaRefines initial older) :
    stateRefines initial target := by
  cases delivery with
  | root =>
      refine ⟨pending,?_⟩
      intro packet present
      rcases List.mem_append.mp present with previous | added
      · exact rootAnswers packet previous
      · have same := List.mem_singleton.mp added
        subst packet
        exact validAnswer
  | source source placement =>
      obtain ⟨frameValid,tailValid⟩ := (frames_cons _ _ _).mp caller
      apply placement_refines placement rootAnswers _ tailValid pending
      apply Unifying.transition_refines source
      constructor
      · simpa only [World.configuration,Unifying.ControlRefines,List.mem_singleton,forall_eq] using validAnswer
      · intro frame present
        have same := List.mem_singleton.mp present
        subst frame
        exact frameValid
  | collection changed =>
      exact ⟨collection_record _ _ answer validAnswer _ _ pending changed,rootAnswers⟩
  | handler =>
      refine ⟨(agenda_cons _ _ _).mpr ⟨⟨?_,((frames_cons _ _ _).mp caller).2⟩,pending⟩,rootAnswers⟩
      simpa only [Unifying.ControlRefines,List.mem_singleton,forall_eq] using validAnswer
  | first found =>
      refine ⟨(agenda_cons _ _ _).mpr ⟨⟨?_,((frames_cons _ _ _).mp caller).2⟩,
        selected_suffix _ _ _ _ pending found⟩,rootAnswers⟩
      simpa only [Unifying.ControlRefines,List.mem_singleton,forall_eq] using validAnswer

theorem head_and_tail {initial : Subst} {state : State} {first : Job} {older : List Job}
    (good : stateRefines initial state) (agenda : state.agenda = first :: older) :
    jobRefines initial first ∧ agendaRefines initial older := by
  have pending := good.1
  rw [agenda] at pending
  exact (agenda_cons _ _ _).mp pending

theorem transition_refines {registry : SpaceSemantics.Program} {initial : Subst} {before after : State}
    (transition : Transition registry before after) (good : stateRefines initial before) :
    stateRefines initial after := by
  cases transition with
  | collection_done agenda =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      refine ⟨(agenda_cons _ _ _).mpr ⟨⟨?_,active.2.1⟩,pending⟩,good.2⟩
      simpa only [Unifying.ControlRefines,List.mem_singleton,forall_eq] using active.1
  | handler_done agenda | first_done agenda | empty agenda =>
      exact ⟨(head_and_tail good agenda).2,good.2⟩
  | answer agenda delivered =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      have packets := active.1
      simp only [Unifying.ControlRefines] at packets
      apply delivery_refines delivered good.2 (packets _ List.mem_cons_self) active.2
      apply later_answers _ _ _ _ _ active.2 pending
      intro packet present
      exact packets packet (List.mem_cons_of_mem _ present)
  | alternatives agenda =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      have sequence := active.1
      simp only [Unifying.ControlRefines] at sequence
      refine ⟨later_answers _ _ _ _ sequence.2 active.2 ?_,good.2⟩
      intro job present
      rcases List.mem_append.mp present with added | previous
      · obtain ⟨control,inControls,rfl⟩ := List.mem_map.mp added
        exact ⟨sequence.1 control inControls,active.2⟩
      · exact pending job previous
  | collection_enter agenda =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      have binding := active.1
      simp only [Unifying.ControlRefines] at binding
      apply open_collection _ _ _ _ _ _ good.2 binding _ active.2 pending
      simpa only [Unifying.ControlRefines] using binding
  | first_enter agenda =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      have binding := active.1
      simp only [Unifying.ControlRefines] at binding
      apply open_first _ _ _ _ _ good.2 _ active.2 pending
      simpa only [Unifying.ControlRefines] using binding
  | caught agenda handler closed =>
      exact ⟨selected_suffix _ _ _ _ (head_and_tail good agenda).2 closed,good.2⟩
  | phase agenda ordinary source placed =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      apply placement_refines placed good.2 _ active.2 pending
      apply Unifying.transition_refines source
      exact ⟨active.1,by intro frame present; cases present⟩

theorem step_refines {registry : SpaceSemantics.Program} {initial : Subst} {before after : State}
    (computed : step registry before = some after) (good : stateRefines initial before) :
    stateRefines initial after := transition_refines ((step_iff_transition registry before after).mp computed) good

theorem path_refines {registry : SpaceSemantics.Program} {initial : Subst} {before after : State}
    (path : Relation.ReflTransGen (Transition registry) before after) (good : stateRefines initial before) :
    stateRefines initial after := by
  induction path with
  | refl => exact good
  | tail previous taken ih => exact transition_refines taken ih

theorem advance_refines (registry : SpaceSemantics.Program) (fuel : Nat) (initial : Subst) (state : State)
    (good : stateRefines initial state) : stateRefines initial (advance registry fuel state) :=
  path_refines (advance_reachable registry fuel state) good

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.BindingInvariant
