import Mettapedia.Languages.CHR.MachineSelection

/-! The search phase of the machine. A frame stack has a finite weight that
every silent move decreases, so a search reaches a decision after finitely
many ticks; the decision is the one `judge` makes in a single pass over the
pending selections. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

section Weight

variable (store : Store) (position active : Nat) (values : List Value)

/-- Two for each candidate below a head position, plus what lies below it. -/
def nodes : Nat → List Head → Environment → List Nat → Nat
  | _, [], _, _ => 0
  | index, head :: later, environment, used =>
    ((candidates index position active values head store).map fun candidate =>
      2 + if candidate.id ∈ used ∨ (index ≠ position ∧ candidate.id = active) then 0
          else
            match matchTerms head.arguments candidate.values environment with
            | none => 0
            | some bound => nodes (index + 1) later bound (candidate.id :: used)).sum

def below (index : Nat) (head : Head) (later : List Head) (environment : Environment) (used : List Nat)
    (candidate : Occ) : Nat :=
  2 + if candidate.id ∈ used ∨ (index ≠ position ∧ candidate.id = active) then 0
      else
        match matchTerms head.arguments candidate.values environment with
        | none => 0
        | some bound => nodes store position active values (index + 1) later bound (candidate.id :: used)

def frameWeight (frame : Frame) : Nat :=
  match frame.heads with
  | [] => 2 * frame.candidates.length
  | head :: later =>
    (frame.candidates.map (below store position active values frame.index head later frame.environment frame.used)).sum

def weight (frames : List Frame) : Nat :=
  (frames.map (frameWeight store position active values)).sum + frames.length

theorem nodes_cons (index : Nat) (head : Head) (later : List Head) (environment : Environment) (used : List Nat) :
    nodes store position active values index (head :: later) environment used =
      ((candidates index position active values head store).map
        (below store position active values index head later environment used)).sum := by
  rw [nodes]
  rfl

end Weight

theorem weight_move (store : Store) (position active : Nat) (values : List Value) (frames : List Frame) :
    match move store position active values frames with
    | .silent next => weight store position active values next < weight store position active values frames
    | .produce _ _ stay => weight store position active values stay < weight store position active values frames
    | .exhausted => True := by
  unfold move
  rcases frames with _ | ⟨frame, rest⟩
  · trivial
  · rcases frame with ⟨index, heads, candidates', environment, picks, used⟩
    rcases candidates' with _ | ⟨candidate, others⟩
    · rcases heads with _ | ⟨head, later⟩ <;> simp [weight, frameWeight]
    · dsimp only
      by_cases rejected : candidate.id ∈ used ∨ (index ≠ position ∧ candidate.id = active)
      · simp only [rejected, if_true]
        rcases heads with _ | ⟨head, later⟩
        · simp [weight, frameWeight]
        · simp [weight, frameWeight, below, rejected]
      · simp only [rejected, if_false]
        rcases heads with _ | ⟨head, later⟩
        · simp [weight, frameWeight]
        · dsimp only
          cases matched : matchTerms head.arguments candidate.values environment with
          | none => simp [weight, frameWeight, below, rejected, matched]
          | some bound =>
            rcases later with _ | ⟨nextHead, rest'⟩
            · simp [weight, frameWeight, below, rejected, matched, nodes]
            · simp [weight, frameWeight, below, rejected, matched, nodes_cons]
              omega

/-- `ticks` machine ticks. -/
def iterate (table : Table) : Nat → State → State
  | 0, state => state
  | ticks + 1, state => iterate table ticks (tick table state)

/-- The decision a single pass over pending selections makes. -/
def judge (occurrence : At) (history : List CHR.Key) :
    List (Environment × List Pick) → Except ArithmeticFault (Option (Environment × List Pick))
  | [] => .ok none
  | (environment, picks) :: rest =>
    if occurrence.body.propagation ∧ (⟨occurrence.rule, ids picks⟩ : CHR.Key) ∈ history then
      judge occurrence history rest
    else
      match guardsEval environment occurrence.body.guards with
      | .error reason => .error reason
      | .ok true => .ok (some (environment, picks))
      | .ok false => judge occurrence history rest

/-- Where a search ends: at the next occurrence, at a firing, or faulted with
store and history unchanged. -/
def Decided (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (tail : List Task) (state : State) (final : State) :
    Except ArithmeticFault (Option (Environment × List Pick)) → Prop
  | .ok none => final = { state with tasks := .scan active key values after :: tail }
  | .ok (some (environment, picks)) => final = fire active key values occurrence after environment picks tail state
  | .error reason => final.status = .faulted reason ∧ final.store = state.store ∧ final.history = state.history ∧
      final.next = state.next ∧ final.seeds = state.seeds

theorem search_phase (table : Table) (active : Nat) (key : Key) (values : List Value) (occurrence : At)
    (after : List At) (tail : List Task) :
    ∀ (measure : Nat) (frames : List Frame) (state : State),
      weight state.store occurrence.head active values frames ≤ measure →
      state.status = .running →
      state.tasks = .search active key values occurrence after frames :: tail →
      ∃ ticks, Decided active key values occurrence after tail state (iterate table ticks state)
        (judge occurrence state.history (pending state.store occurrence.head active values frames))
  | measure, frames, state, bounded, running, tasks => by
    have ticked : tick table state = search active key values occurrence after frames tail state := by
      unfold tick
      rw [running, tasks]
    have moved := search_move active key values occurrence after frames tail state
    have pendingMoved := pending_move state.store occurrence.head active values frames
    have weightMoved := weight_move state.store occurrence.head active values frames
    cases decision : move state.store occurrence.head active values frames with
    | exhausted =>
      rw [decision] at moved pendingMoved
      refine ⟨1, ?_⟩
      simp only [iterate, ticked, moved, pendingMoved, judge, Decided]
    | silent next =>
      rw [decision] at moved pendingMoved weightMoved
      cases measure with
      | zero => omega
      | succ smaller =>
        let nextState := { state with tasks := .search active key values occurrence after next :: tail }
        obtain ⟨ticks, decided⟩ := search_phase table active key values occurrence after tail smaller next
          nextState (by simp only [nextState]; omega) running rfl
        refine ⟨ticks + 1, ?_⟩
        rw [iterate, ticked, moved]
        simp only [nextState] at decided
        rw [pendingMoved] at decided
        cases judgement : judge occurrence state.history (pending state.store occurrence.head active values frames) with
        | error reason =>
          rw [judgement] at decided
          simpa [Decided] using decided
        | ok outcome =>
          rcases outcome with _ | ⟨environment, picks⟩
          · rw [judgement] at decided
            simpa [Decided] using decided
          · rw [judgement] at decided
            simp only [Decided] at decided ⊢
            rw [decided]
            simp [fire]
    | produce environment picks stay =>
      rw [decision] at moved pendingMoved weightMoved
      rw [pendingMoved]
      by_cases stale : occurrence.body.propagation ∧ (⟨occurrence.rule, ids picks⟩ : CHR.Key) ∈ state.history
      · cases measure with
        | zero => omega
        | succ smaller =>
          let nextState := { state with tasks := .search active key values occurrence after stay :: tail }
          obtain ⟨ticks, decided⟩ := search_phase table active key values occurrence after tail smaller stay
            nextState (by simp only [nextState]; omega) running rfl
          refine ⟨ticks + 1, ?_⟩
          rw [iterate, ticked, moved]
          dsimp only
          have retried : complete active key values occurrence after stay environment picks tail state = nextState := by
            rw [complete, if_pos stale]
          rw [retried]
          simp only [judge, stale]
          simp only [nextState] at decided
          cases judgement : judge occurrence state.history (pending state.store occurrence.head active values stay) with
          | error reason => rw [judgement] at decided; simpa [Decided] using decided
          | ok outcome =>
            rcases outcome with _ | ⟨environment', picks'⟩
            · rw [judgement] at decided; simpa [Decided] using decided
            · rw [judgement] at decided
              simp only [Decided] at decided ⊢
              rw [decided]
              simp [fire]
      · cases guarded : guardsEval environment occurrence.body.guards with
        | error reason =>
          refine ⟨1, ?_⟩
          simp [iterate, ticked, moved, judge, stale, guarded, Decided, complete]
        | ok holds =>
          cases holds with
          | true =>
            refine ⟨1, ?_⟩
            simp [iterate, ticked, moved, judge, stale, guarded, Decided, complete]
          | false =>
            cases measure with
            | zero => omega
            | succ smaller =>
              let nextState := { state with tasks := .search active key values occurrence after stay :: tail }
              obtain ⟨ticks, decided⟩ := search_phase table active key values occurrence after tail smaller stay
                nextState (by simp only [nextState]; omega) running rfl
              refine ⟨ticks + 1, ?_⟩
              rw [iterate, ticked, moved]
              dsimp only
              have retried : complete active key values occurrence after stay environment picks tail state = nextState := by
                rw [complete, if_neg stale, guarded]
              rw [retried]
              simp only [judge, stale, if_false, guarded]
              simp only [nextState] at decided
              cases judgement : judge occurrence state.history (pending state.store occurrence.head active values stay) with
              | error reason => rw [judgement] at decided; simpa [Decided] using decided
              | ok outcome =>
                rcases outcome with _ | ⟨environment', picks'⟩
                · rw [judgement] at decided; simpa [Decided] using decided
                · rw [judgement] at decided
                  simp only [Decided] at decided ⊢
                  rw [decided]
                  simp [fire]

#print axioms weight_move
#print axioms search_phase

end Mettapedia.Languages.CHR.Machine
