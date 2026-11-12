import Mettapedia.Languages.MeTTa.PeTTa.StreamingScopeInvariant

/-!
# Allocation support survives every actual streaming transition

Existing source-phase preservation earns the reached world and active payload.
Monotone allocation weakens the untouched frontier; actual collection copies
earn their new identities. No template scan or reserved source names is added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.ScopeInvariant

theorem placement_supported {allowed : String → Prop} {state : State} {after : Unifying.Configuration}
    {caller : List Frame} {older : List Job} {target : State}
    (placement : Placement state after caller older target)
    (rootAnswers : ∀ answer ∈ state.answers, Unifying.AnswerSupported allowed answer)
    (localPhase : Unifying.ConfigurationSupported allowed after)
    (frames : framesSupported allowed caller) (pending : agendaSupported allowed older) :
    stateSupported allowed target := by
  have world : worldSupported allowed (World.fromConfiguration after) := ⟨localPhase.2.2.1,localPhase.2.2.2⟩
  cases placement with
  | plain => exact ⟨world,(agenda_cons _ _ _).mpr ⟨⟨localPhase.1,frames⟩,pending⟩,rootAnswers⟩
  | collection frameShape =>
      apply open_collection _ {state with world := World.fromConfiguration after} _ _ _ _ world rootAnswers _ localPhase.1 frames pending
      exact localPhase.2.1 _ (by rw [frameShape]; exact List.mem_singleton_self _)
  | handler => exact open_handler _ _ _ _ _ world rootAnswers localPhase.1 frames pending
  | waiting frameShape ordinary =>
      refine ⟨world,(agenda_cons _ _ _).mpr ⟨⟨localPhase.1,?_⟩,pending⟩,rootAnswers⟩
      exact (frames_cons _ _ _).mpr
        ⟨localPhase.2.1 _ (by rw [frameShape]; exact List.mem_singleton_self _),frames⟩

theorem delivery_wellScoped {registry : SpaceSemantics.Program} {state target : State}
    {answer : Unifying.Answer} {frames : List Frame} {older : List Job}
    (delivery : Delivery registry state answer frames older target)
    (world : worldSupported (Mettapedia.ScopedString.Before state.world.uses) state.world)
    (rootAnswers : ∀ packet ∈ state.answers, Unifying.AnswerSupported (Mettapedia.ScopedString.Before state.world.uses) packet)
    (packet : Unifying.AnswerSupported (Mettapedia.ScopedString.Before state.world.uses) answer)
    (caller : framesSupported (Mettapedia.ScopedString.Before state.world.uses) frames)
    (pending : agendaSupported (Mettapedia.ScopedString.Before state.world.uses) older) : WellScoped target := by
  cases delivery with
  | root =>
      refine ⟨world,pending,?_⟩
      intro value present
      rcases List.mem_append.mp present with previous | added
      · exact rootAnswers value previous
      · have same := List.mem_singleton.mp added
        subst value
        exact packet
  | source source placement =>
      obtain ⟨frameValid,tailValid⟩ := (frames_cons _ _ _).mp caller
      have localPhase := Unifying.transition_wellScoped source (by
        refine ⟨?_,?_,world.1,world.2⟩
        · simpa only [World.configuration,Unifying.ControlSupported,List.mem_singleton,forall_eq] using packet
        · intro frame present
          have same := List.mem_singleton.mp present
          subst frame
          exact frameValid)
      have grows := ScopedSource.transition_uses_mono source
      have included : ∀ key, Mettapedia.ScopedString.Before state.world.uses key →
          Mettapedia.ScopedString.Before _ key := fun _ old => Mettapedia.ScopedString.before_mono grows old
      change stateSupported (Mettapedia.ScopedString.Before target.world.uses) target
      rw [placement.world]
      exact placement_supported placement (fun value present => (rootAnswers value present).mono included)
        localPhase (frames_mono included tailValid) (agenda_mono included pending)
  | collection changed =>
      exact ⟨world,collection_record _ _ answer packet _ _ pending changed,rootAnswers⟩
  | handler =>
      refine ⟨world,(agenda_cons _ _ _).mpr ⟨⟨?_,((frames_cons _ _ _).mp caller).2⟩,pending⟩,rootAnswers⟩
      simpa only [Unifying.ControlSupported,List.mem_singleton,forall_eq] using packet
  | first found =>
      refine ⟨world,(agenda_cons _ _ _).mpr ⟨⟨?_,((frames_cons _ _ _).mp caller).2⟩,
        selected_suffix _ _ _ _ pending found⟩,rootAnswers⟩
      simpa only [Unifying.ControlSupported,List.mem_singleton,forall_eq] using packet

theorem head_and_tail {allowed : String → Prop} {state : State} {first : Job} {older : List Job}
    (good : stateSupported allowed state) (agenda : state.agenda = first :: older) :
    jobSupported allowed first ∧ agendaSupported allowed older := by
  have pending := good.2.1
  rw [agenda] at pending
  exact (agenda_cons _ _ _).mp pending

theorem transition_wellScoped {registry : SpaceSemantics.Program} {before after : State}
    (transition : Transition registry before after) (good : WellScoped before) : WellScoped after := by
  have grows := transition.uses_mono
  have promoted := state_mono (fun key old => Mettapedia.ScopedString.before_mono grows old) good
  cases transition with
  | collection_done agenda =>
      obtain ⟨active,pending⟩ := head_and_tail promoted agenda
      refine ⟨promoted.1,(agenda_cons _ _ _).mpr ⟨⟨?_,active.2.1⟩,pending⟩,promoted.2.2⟩
      simp only [Unifying.ControlSupported,List.mem_singleton,forall_eq,Unifying.AnswerSupported]
      exact ⟨(Unifying.supported_expression _ _).mpr (Unifying.copies_supported _ _ _ (Nat.le_refl _)),active.1⟩
  | handler_done agenda | first_done agenda | empty agenda =>
      exact ⟨promoted.1,(head_and_tail promoted agenda).2,promoted.2.2⟩
  | answer agenda delivered =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      have packets := active.1
      simp only [Unifying.ControlSupported] at packets
      apply delivery_wellScoped delivered good.1 good.2.2 (packets _ List.mem_cons_self) active.2
      apply later_answers _ _ _ _ _ active.2 pending
      intro value present
      exact packets value (List.mem_cons_of_mem _ present)
  | alternatives agenda =>
      obtain ⟨active,pending⟩ := head_and_tail promoted agenda
      have sequence := active.1
      simp only [Unifying.ControlSupported] at sequence
      refine ⟨promoted.1,later_answers _ _ _ _ sequence.2 active.2 ?_,promoted.2.2⟩
      intro job present
      rcases List.mem_append.mp present with added | previous
      · obtain ⟨control,inControls,rfl⟩ := List.mem_map.mp added
        exact ⟨sequence.1 control inControls,active.2⟩
      · exact pending job previous
  | collection_enter agenda =>
      obtain ⟨active,pending⟩ := head_and_tail promoted agenda
      have control := active.1
      simp [Unifying.ControlSupported,Unifying.supported_expression,Unifying.supported_symbol] at control
      apply open_collection _ _ _ _ _ _ promoted.1 promoted.2.2 control.1 _ active.2 pending
      simpa only [Unifying.ControlSupported] using control
  | first_enter agenda =>
      obtain ⟨active,pending⟩ := head_and_tail promoted agenda
      have control := active.1
      simp [Unifying.ControlSupported,Unifying.supported_expression,Unifying.supported_symbol] at control
      apply open_first _ _ _ _ _ promoted.1 promoted.2.2 _ active.2 pending
      simpa only [Unifying.ControlSupported] using control
  | caught agenda handler closed =>
      exact ⟨promoted.1,selected_suffix _ _ _ _ (head_and_tail promoted agenda).2 closed,promoted.2.2⟩
  | phase agenda ordinary source placed =>
      obtain ⟨active,pending⟩ := head_and_tail good agenda
      have localPhase := Unifying.transition_wellScoped source (by
        simp only [Unifying.WellScoped,Unifying.ConfigurationSupported,World.configuration]
        refine ⟨active.1,?_,good.1.1,good.1.2⟩
        intro frame present
        cases present)
      have included : ∀ key, Mettapedia.ScopedString.Before before.world.uses key →
          Mettapedia.ScopedString.Before _ key :=
        fun _ old => Mettapedia.ScopedString.before_mono (ScopedSource.transition_uses_mono source) old
      change stateSupported (Mettapedia.ScopedString.Before after.world.uses) after
      rw [placed.world]
      exact placement_supported placed (fun answer present => (good.2.2 answer present).mono included)
        localPhase (frames_mono included active.2) (agenda_mono included pending)

theorem step_wellScoped {registry : SpaceSemantics.Program} {before after : State}
    (computed : step registry before = some after) (good : WellScoped before) : WellScoped after :=
  transition_wellScoped ((step_iff_transition registry before after).mp computed) good

theorem path_wellScoped {registry : SpaceSemantics.Program} {before after : State}
    (path : Relation.ReflTransGen (Transition registry) before after) (good : WellScoped before) : WellScoped after := by
  induction path with
  | refl => exact good
  | tail previous taken ih => exact transition_wellScoped taken ih

theorem advance_wellScoped (registry : SpaceSemantics.Program) (fuel : Nat) (state : State)
    (good : WellScoped state) : WellScoped (advance registry fuel state) :=
  path_wellScoped (advance_reachable registry fuel state) good

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.ScopeInvariant
