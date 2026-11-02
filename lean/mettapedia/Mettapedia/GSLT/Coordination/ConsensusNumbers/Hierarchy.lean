import Mettapedia.GSLT.Coordination.ConsensusNumbers.Universality
import Mettapedia.GSLT.Coordination.ConsensusNumbers.RemovalAnswers

/-!
# What an implementation transfers: consensus

If a base object implements a consensus object for `n` processes (wait-free and linearizable), it
solves `n`-process consensus: each process proposes its input once through the implementation and
decides the answer (`oneShot`, `solvable_of_implements_consensus`). Agreement and validity come from
linearizability (the answers are those of a consensus object used atomically: all equal to the first
proposal to take effect, which was someone's input); wait-freedom comes from the implementation's.

So an object that cannot solve `n`-process consensus implements no consensus object for `n`
processes, and is **not universal** for `n` processes (`Universal`, `not_universal_of_not_solvable`).

## Consequences for spaces

* MeTTa's separate operations with silent removal (what Hyperon Experimental, PeTTa and CeTTa do for
  data atoms), even with any number of spaces and registers, are not universal for two or more
  processes (`silentSpaces_not_universal`).
* With removals answering anything at all (whether they removed, how many, which atoms), they are not
  universal for three or more processes (`spacesWith_not_universal`); in particular with counting
  removal (`countSpace_not_universal`) and with PeTTa's removal of every match answering the count
  (`patternSpace_not_universal`).
* Steps are universal (`Universal.steps_universal`): they implement every object, the consensus
  object included, for any number of processes.

## Controls

* `Controls.ownInput_consensus_not_linearizable`: a front-end that answers each proposal with the
  proposer's own value, without any base operation, is not linearizable for two processes: two
  proposals of different values answered by themselves are not a history of a consensus object
  (negative).
* `Controls.atomic_consensus_solves`: the consensus object used atomically solves consensus for any
  number of processes (positive).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

open Implementation

/-! ## The consensus object used atomically -/

section AtomicConsensus

variable {V : Type} {n : ℕ}

/-- What an atomic run of a consensus object from `none` keeps: a pending proposal was proposed; and
either nothing is decided and nothing answered, or the decided value was proposed and every answer,
given or about to be given, is it. -/
def ConsensusGood (A : (atomic (consensusObject V) none n).Config)
    (h : List (Event n (consensusObject V).Op (consensusObject V).Res)) : Prop :=
  (∀ i v, A.loc i = .busy (.pending v) → ∃ j, Event.invoke j v ∈ h) ∧
    match A.obj with
    | none => (∀ i r, A.loc i ≠ .busy (.done r)) ∧ ∀ i r, Event.respond i r ∉ h
    | some w => (∃ j, Event.invoke j w ∈ h) ∧ (∀ i r, A.loc i = .busy (.done r) → r = w) ∧
        ∀ i r, Event.respond i r ∈ h → r = w

theorem consensusGood_step {A A' : (atomic (consensusObject V) none n).Config}
    {c : Choice n (consensusObject V).Op} {e : Option (Event n (consensusObject V).Op (consensusObject V).Res)} {h : List (Event n (consensusObject V).Op (consensusObject V).Res)}
    (good : ConsensusGood A h) (step : (atomic (consensusObject V) none n).Step A c e A') :
    ConsensusGood A' (h ++ e.toList) := by
  obtain ⟨pend, rest⟩ := good
  have keepMem : ∀ ev, ev ∈ h → ev ∈ h ++ e.toList := fun ev mem => List.mem_append_left _ mem
  cases step with
  | @invoke i m op hi =>
      refine ⟨fun j v hj => ?_, ?_⟩
      · by_cases same : j = i
        · subst same
          simp only [Function.update_self] at hj
          cases hj
          exact ⟨j, by simp⟩
        · simp only [Function.update_of_ne same] at hj
          obtain ⟨k, hk⟩ := pend j v hj
          exact ⟨k, keepMem _ hk⟩
      · revert rest
        cases A.obj with
        | none =>
            rintro ⟨noDone, noResp⟩
            refine ⟨fun j r hj => ?_, fun j r mem => ?_⟩
            · by_cases same : j = i
              · subst same; simp at hj; cases hj
              · simp only [Function.update_of_ne same] at hj; exact noDone j r hj
            · simp only [Option.toList_some, List.mem_append, List.mem_cons, reduceCtorEq,
                List.not_mem_nil, or_false] at mem
              exact noResp j r mem
        | some w =>
            rintro ⟨⟨k, hk⟩, doneW, respW⟩
            refine ⟨⟨k, keepMem _ hk⟩, fun j r hj => ?_, fun j r mem => ?_⟩
            · by_cases same : j = i
              · subst same; simp at hj; cases hj
              · simp only [Function.update_of_ne same] at hj; exact doneW j r hj
            · simp only [Option.toList_some, List.mem_append, List.mem_cons, reduceCtorEq,
                List.not_mem_nil, or_false] at mem
              exact respW j r mem
  | @call i w a s r hl hm hf =>
      cases w with
      | done r' => exact absurd hm (by simp [atomic])
      | pending v =>
          have ha : v = a := by simpa [atomic] using hm
          subst ha
          have hf' : (consensusObject V).apply A.obj v = (s, r) := hf
          simp only [Option.toList_none, List.append_nil]
          obtain ⟨j₀, hj₀⟩ := pend i v hl
          revert rest hf'
          cases hobj : A.obj with
          | none =>
              rintro ⟨noDone, noResp⟩ hf'
              simp only [consensusObject] at hf'
              obtain ⟨rfl, rfl⟩ := hf'
              refine ⟨fun j v' hj => ?_, ⟨j₀, hj₀⟩, fun j r' hj => ?_, fun j r' mem => ?_⟩
              · by_cases same : j = i
                · subst same; simp [atomic] at hj
                · simp only [Function.update_of_ne same] at hj; exact pend j v' hj
              · by_cases same : j = i
                · subst same
                  simp [atomic] at hj
                  exact hj.symm
                · simp only [Function.update_of_ne same] at hj; exact absurd hj (noDone j r')
              · exact absurd mem (noResp j r')
          | some w =>
              rintro ⟨hw, doneW, respW⟩ hf'
              simp only [consensusObject] at hf'
              obtain ⟨rfl, rfl⟩ := hf'
              refine ⟨fun j v' hj => ?_, hw, fun j r' hj => ?_, respW⟩
              · by_cases same : j = i
                · subst same; simp [atomic] at hj
                · simp only [Function.update_of_ne same] at hj; exact pend j v' hj
              · by_cases same : j = i
                · subst same
                  simp [atomic] at hj
                  exact hj.symm
                · simp only [Function.update_of_ne same] at hj; exact doneW j r' hj
  | @wait i w a hl hm never =>
      cases w with
      | done r' => exact absurd hm (by simp [atomic])
      | pending v =>
          have ha : v = a := by simpa [atomic] using hm
          subst ha
          exact absurd rfl (never _ _)
  | @ret i w r m hl hm =>
      cases w with
      | pending v => exact absurd hm (by simp [atomic])
      | done r' =>
          have hr : r' = r := (Move.ret.inj hm).1
          subst hr
          refine ⟨fun j v hj => ?_, ?_⟩
          · by_cases same : j = i
            · subst same; simp at hj
            · simp only [Function.update_of_ne same] at hj
              obtain ⟨k, hk⟩ := pend j v hj
              exact ⟨k, keepMem _ hk⟩
          · revert rest
            cases A.obj with
            | none => rintro ⟨noDone, -⟩; exact absurd hl (noDone i r')
            | some w =>
                rintro ⟨⟨k, hk⟩, doneW, respW⟩
                have rw' := doneW i r' hl
                refine ⟨⟨k, keepMem _ hk⟩, fun j r'' hj => ?_, fun j r'' mem => ?_⟩
                · by_cases same : j = i
                  · subst same; simp at hj
                  · simp only [Function.update_of_ne same] at hj; exact doneW j r'' hj
                · simp only [Option.toList_some, List.mem_append, List.mem_cons,
                    Event.respond.injEq, List.not_mem_nil, or_false] at mem
                  rcases mem with mem | ⟨-, rfl⟩
                  · exact respW j r'' mem
                  · exact rw'
  | rest _ =>
      simp only [Option.toList_none, List.append_nil]
      exact ⟨pend, rest⟩

theorem consensusGood_initial :
    ConsensusGood (atomic (consensusObject V) none n).initial ([] : List (Event n (consensusObject V).Op (consensusObject V).Res)) := by
  refine ⟨fun i v hi => ?_, ?_⟩
  · simp [Implementation.initial, atomic] at hi
  · show (∀ i r, (atomic (consensusObject V) none n).initial.loc i ≠ .busy (.done r)) ∧
      ∀ i r, Event.respond i r ∉ ([] : List (Event n (consensusObject V).Op (consensusObject V).Res))
    exact ⟨fun i r hi => by simp [Implementation.initial, atomic] at hi, fun i r hi => by simp at hi⟩

theorem consensusGood_run {A A' : (atomic (consensusObject V) none n).Config}
    {cs : List (Choice n (consensusObject V).Op)} {h : List (Event n (consensusObject V).Op (consensusObject V).Res)} (pre : List (Event n (consensusObject V).Op (consensusObject V).Res))
    (good : ConsensusGood A pre) (run : (atomic (consensusObject V) none n).Run A cs h A') :
    ConsensusGood A' (pre ++ h) := by
  induction cs generalizing A pre h with
  | nil =>
      obtain ⟨rfl, rfl⟩ := run
      simpa using good
  | cons c cs ih =>
      obtain ⟨e, E, h', step, rest, rfl⟩ := run
      have := ih (pre ++ e.toList) (consensusGood_step good step) rest
      simpa [List.append_assoc] using this

/-- **Every history of a consensus object used atomically**: all answers agree, and each answer was
proposed. -/
theorem consensus_history {h : List (Event n (consensusObject V).Op (consensusObject V).Res)}
    (hist : LinearizableHistory (consensusObject V) none h) :
    (∀ i r i' r', Event.respond i r ∈ h → Event.respond i' r' ∈ h → r = r') ∧
      ∀ i r, Event.respond i r ∈ h → ∃ j, Event.invoke j r ∈ h := by
  obtain ⟨cs, D, run⟩ := hist
  have good := consensusGood_run [] consensusGood_initial run
  simp only [List.nil_append] at good
  obtain ⟨-, rest⟩ := good
  rcases hobj : D.obj with _ | w
  · rw [hobj] at rest
    obtain ⟨-, noResp⟩ := rest
    exact ⟨fun i r _ _ mem _ => absurd mem (noResp i r), fun i r mem => absurd mem (noResp i r)⟩
  · rw [hobj] at rest
    obtain ⟨hw, -, respW⟩ := rest
    refine ⟨fun i r i' r' mem mem' => by rw [respW i r mem, respW i' r' mem'], fun i r mem => ?_⟩
    rw [respW i r mem]; exact hw

end AtomicConsensus

/-! ## One proposal each -/

section OneShot

variable {X : ObjectType} {V : Type} {n : ℕ}

/-- **One proposal each**: the consensus protocol made from an implementation of a consensus object.
Each process starts the implementation's program for proposing its input, calls the base operations
it says, and decides the answer when it returns. -/
def oneShot (I : Implementation X (consensusObject V) n) : Protocol X n V where
  Local := I.Work
  start i v := I.begin i (I.mem₀ i) v
  init := I.init
  action i w := match I.move i w with
    | .call a => .invoke a
    | .ret r _ => .decide r
  next i w r := I.next i w r

variable {I : Implementation X (consensusObject V) n}

theorem oneShot_action_call {i : Fin n} {w : I.Work} {a : X.Op} (h : I.move i w = .call a) :
    (oneShot I).action i w = .invoke a := by
  simp only [oneShot, h]

theorem oneShot_action_ret {i : Fin n} {w : I.Work} {r : V} {m : I.Mem} (h : I.move i w = .ret r m) :
    (oneShot I).action i w = .decide r := by
  simp only [oneShot, h]

theorem oneShot_action_cases (i : Fin n) (w : I.Work) :
    (∃ a, I.move i w = .call a ∧ (oneShot I).action i w = .invoke a) ∨
      ∃ r m, I.move i w = .ret r m ∧ (oneShot I).action i w = .decide r := by
  cases h : I.move i w with
  | call a => exact Or.inl ⟨a, rfl, oneShot_action_call h⟩
  | ret r m => exact Or.inr ⟨r, m, rfl, oneShot_action_ret h⟩

theorem oneShot_decision_ret {C : (oneShot I).Config} {i : Fin n} {r : V} {m : I.Mem}
    (h : I.move i (C.loc i) = .ret r m) : (oneShot I).decision C i = some r := by
  unfold Protocol.decision; rw [oneShot_action_ret h]

/-- A configuration of the protocol beside one of the implementation: the same base state, and each
process busy with the same working state, or returned with what it decided. -/
def Beside (C : (oneShot I).Config) (E : I.Config) : Prop :=
  E.obj = C.obj ∧ ∀ i, E.loc i = .busy (C.loc i) ∨
    ∃ r m, I.move i (C.loc i) = .ret r m ∧ E.loc i = .idle m

/-- What a run of the implementation beside the protocol's has shown: only the initial proposals
were made, each answer is the answerer's decision, and every returned process has answered. -/
def Track (x : Fin n → V) (C : (oneShot I).Config) (E : I.Config)
    (h : List (Event n (consensusObject V).Op (consensusObject V).Res)) : Prop :=
  Beside C E ∧ (∀ j v, Event.invoke j v ∈ h → v = x j) ∧
    (∀ j r, Event.respond j r ∈ h → (oneShot I).decision C j = some r) ∧
    (∀ j m, E.loc j = .idle m → ∃ r, Event.respond j r ∈ h)

/-- **A step of the protocol is a move of the implementation.** -/
theorem beside_step {C D : (oneShot I).Config} {E : I.Config} {i : Fin n} (rel : Beside C E)
    (step : (oneShot I).Step C i D) :
    ∃ e E', I.Step E (.move i) e E' ∧ Beside D E' ∧
      (e = none ∨ ∃ r m, e = some (.respond i r) ∧ I.move i (C.loc i) = .ret r m) := by
  obtain ⟨obj, locs⟩ := rel
  rcases locs i with busyI | ⟨r, m, hr, idleI⟩
  · cases step with
    | @decided v hd =>
        rcases oneShot_action_cases i (C.loc i) with ⟨a, ha, hact⟩ | ⟨r, m, hr, hact⟩
        · rw [hact] at hd; cases hd
        · refine ⟨_, _, Step.ret busyI hr, ⟨obj, fun j => ?_⟩, Or.inr ⟨r, m, rfl, hr⟩⟩
          by_cases same : j = i
          · subst same; exact Or.inr ⟨r, m, hr, by simp⟩
          · simp only [Function.update_of_ne same]; exact locs j
    | @fires op s r' hact hf =>
        rcases oneShot_action_cases i (C.loc i) with ⟨a, ha, hact'⟩ | ⟨r, m, hr, hact'⟩
        · rw [hact'] at hact; cases hact
          refine ⟨none, _, Step.call busyI ha (by rw [obj]; exact hf), ⟨rfl, fun j => ?_⟩, Or.inl rfl⟩
          by_cases same : j = i
          · subst same; left; simp; rfl
          · simp only [Function.update_of_ne same]; exact locs j
        · rw [hact'] at hact; cases hact
    | @waits op hact never =>
        rcases oneShot_action_cases i (C.loc i) with ⟨a, ha, hact'⟩ | ⟨r, m, hr, hact'⟩
        · rw [hact'] at hact; cases hact
          exact ⟨none, E, Step.wait busyI ha (by rw [obj]; exact never), ⟨obj, locs⟩, Or.inl rfl⟩
        · rw [hact'] at hact; cases hact
  · have decided : (oneShot I).action i (C.loc i) = .decide r := oneShot_action_ret hr
    have same := step.eq_of_decide decided
    subst same
    exact ⟨none, E, Step.rest idleI, ⟨obj, locs⟩, Or.inl rfl⟩

theorem track_step {x : Fin n → V} {C D : (oneShot I).Config} {E : I.Config}
    {h : List (Event n (consensusObject V).Op (consensusObject V).Res)} {i : Fin n}
    (tr : Track x C E h) (step : (oneShot I).Step C i D) :
    ∃ e E', I.Step E (.move i) e E' ∧ Track x D E' (h ++ e.toList) := by
  obtain ⟨rel, invokes, answers, returned⟩ := tr
  obtain ⟨e, E', stepI, rel', ev⟩ := beside_step rel step
  refine ⟨e, E', stepI, rel', fun j v mem => ?_, fun j r mem => ?_, fun j m hj => ?_⟩
  · rcases List.mem_append.mp mem with mem | mem
    · exact invokes j v mem
    · rcases ev with rfl | ⟨r, m, rfl, -⟩ <;> simp at mem
  · rcases List.mem_append.mp mem with mem | mem
    · exact step.decision_of_decided (answers j r mem)
    · rcases ev with rfl | ⟨r', m, rfl, hr⟩
      · simp at mem
      · simp only [Option.toList_some, List.mem_singleton, Event.respond.injEq] at mem
        obtain ⟨rfl, rfl⟩ := mem
        exact step.decision_of_decided (oneShot_decision_ret hr)
  · by_cases same : j = i
    · subst same
      rcases ev with rfl | ⟨r, m', rfl, hr⟩
      · cases stepI with
        | call hl _ _ => simp at hj
        | wait _ _ _ =>
            obtain ⟨r, hr⟩ := returned j m hj
            exact ⟨r, List.mem_append_left _ hr⟩
        | rest _ =>
            obtain ⟨r, hr⟩ := returned j m hj
            exact ⟨r, List.mem_append_left _ hr⟩
      · exact ⟨r, by simp⟩
    · have : E'.loc j = E.loc j := stepI.loc_of_ne same
      rw [this] at hj
      obtain ⟨r, hr⟩ := returned j m hj
      exact ⟨r, List.mem_append_left _ hr⟩

/-- The configuration after calling the first `k` processes with their inputs. -/
def called (I : Implementation X (consensusObject V) n) (x : Fin n → V) (k : ℕ) : I.Config :=
  ⟨I.init, fun i => if i.val < k then .busy (I.begin i (I.mem₀ i) (x i)) else .idle (I.mem₀ i)⟩

theorem called_zero (x : Fin n → V) : called I x 0 = I.initial := by
  refine Implementation.Config.ext rfl (funext fun i => ?_)
  simp [called, Implementation.initial]

theorem called_step (x : Fin n → V) (k : ℕ) (hk : k < n) :
    I.Step (called I x k) (.invoke ⟨k, hk⟩ (x ⟨k, hk⟩)) (some (.invoke ⟨k, hk⟩ (x ⟨k, hk⟩)))
      (called I x (k + 1)) := by
  have step := Step.invoke (I := I) (C := called I x k) (i := ⟨k, hk⟩) (m := I.mem₀ ⟨k, hk⟩)
    (x ⟨k, hk⟩) (by simp [called])
  convert step using 1
  refine Implementation.Config.ext rfl (funext fun i => ?_)
  by_cases same : i = ⟨k, hk⟩
  · subst same; simp [called]
  · have ne : i.val ≠ k := fun h => same (Fin.ext h)
    simp only [called, Function.update_of_ne same]
    by_cases lt : i.val < k
    · rw [if_pos (by omega), if_pos lt]
    · rw [if_neg (by omega), if_neg lt]

theorem run_called (x : Fin n → V) :
    ∀ k, k ≤ n → ∃ cs h, I.Run I.initial cs h (called I x k) ∧
      (∀ j v, Event.invoke j v ∈ h → v = x j) ∧ ∀ j r, Event.respond j r ∉ h := by
  intro k
  induction k with
  | zero => intro _; exact ⟨[], [], by rw [called_zero]; exact run_nil _, by simp, by simp⟩
  | succ k ih =>
      intro hk
      obtain ⟨cs, h, run, invokes, noResp⟩ := ih (by omega)
      refine ⟨cs ++ [.invoke ⟨k, by omega⟩ (x ⟨k, by omega⟩)],
        h ++ [.invoke ⟨k, by omega⟩ (x ⟨k, by omega⟩)],
        run_append run (run_single (called_step x k (by omega))), fun j v mem => ?_,
        fun j r mem => ?_⟩
      · rcases List.mem_append.mp mem with mem | mem
        · exact invokes j v mem
        · simp only [List.mem_singleton] at mem
          obtain ⟨rfl, rfl⟩ := mem; rfl
      · rcases List.mem_append.mp mem with mem | mem
        · exact noResp j r mem
        · simp at mem

theorem track_called (x : Fin n → V) {h : List (Event n (consensusObject V).Op (consensusObject V).Res)}
    (invokes : ∀ j v, Event.invoke j v ∈ h → v = x j) (noResp : ∀ j r, Event.respond j r ∉ h) :
    Track x ((oneShot I).initial x) (called I x n) h := by
  refine ⟨⟨rfl, fun i => Or.inl (by simp [called]; rfl)⟩, invokes,
    fun j r mem => absurd mem (noResp j r), fun j m hj => ?_⟩
  simp [called] at hj

theorem track_run {x : Fin n → V} {C D : (oneShot I).Config} {E : I.Config}
    {h : List (Event n (consensusObject V).Op (consensusObject V).Res)} (tr : Track x C E h)
    {σ : List (Fin n)} (run : (oneShot I).Run C σ D) :
    ∃ cs E' h', I.Run E cs h' E' ∧ Track x D E' (h ++ h') := by
  induction σ generalizing C E h with
  | nil => rw [run]; exact ⟨[], E, [], run_nil E, by simpa using tr⟩
  | cons i σ ih =>
      obtain ⟨F, step, rest⟩ := run
      obtain ⟨e, E₁, stepI, tr₁⟩ := track_step tr step
      obtain ⟨cs, E', h', run', tr'⟩ := ih tr₁ rest
      exact ⟨.move i :: cs, E', e.toList ++ h', ⟨e, E₁, h', stepI, run', rfl⟩,
        by simpa [List.append_assoc] using tr'⟩

/-- A decided process can be moved until it has answered with its decision. -/
theorem track_answer {x : Fin n → V} {C : (oneShot I).Config} {E : I.Config}
    {h : List (Event n (consensusObject V).Op (consensusObject V).Res)} (tr : Track x C E h)
    {i : Fin n} {v : V} (dec : (oneShot I).decision C i = some v) :
    ∃ e E', I.Step E (.move i) e E' ∧ Track x C E' (h ++ e.toList) ∧
      Event.respond i v ∈ h ++ e.toList := by
  obtain ⟨⟨obj, locs⟩, invokes, answers, returned⟩ := tr
  have hact := Protocol.decision_eq_some_iff.mp dec
  obtain ⟨r, m, hr, -⟩ : ∃ r m, I.move i (C.loc i) = .ret r m ∧ True := by
    rcases oneShot_action_cases i (C.loc i) with ⟨a, ha, h'⟩ | ⟨r, m, hr, h'⟩
    · rw [h'] at hact; cases hact
    · exact ⟨r, m, hr, trivial⟩
  have rv : r = v := by
    have := oneShot_action_ret hr; rw [this] at hact; cases hact; rfl
  subst rv
  rcases locs i with busyI | ⟨r', m', hr', idleI⟩
  · refine ⟨_, _, Step.ret busyI hr, ⟨⟨obj, fun j => ?_⟩, fun j v' mem => ?_, fun j r' mem => ?_,
      fun j m' hj => ?_⟩, List.mem_append_right _ (List.mem_singleton_self _)⟩
    · by_cases same : j = i
      · subst same; exact Or.inr ⟨r, m, hr, by simp⟩
      · simp only [Function.update_of_ne same]; exact locs j
    · rcases List.mem_append.mp mem with mem | mem
      · exact invokes j v' mem
      · simp at mem
    · rcases List.mem_append.mp mem with mem | mem
      · exact answers j r' mem
      · simp only [Option.toList_some, List.mem_singleton, Event.respond.injEq] at mem
        obtain ⟨rfl, rfl⟩ := mem; exact dec
    · by_cases same : j = i
      · subst same; exact ⟨r, by simp⟩
      · simp only [Function.update_of_ne same] at hj
        obtain ⟨r'', hr''⟩ := returned j m' hj
        exact ⟨r'', List.mem_append_left _ hr''⟩
  · obtain ⟨r'', hr''⟩ := returned i m' idleI
    have same : r'' = r := by
      have := answers i r'' hr''; rw [dec] at this; exact (Option.some.inj this).symm
    subst same
    refine ⟨none, E, Step.rest idleI, ?_, ?_⟩
    · simp only [Option.toList_none, List.append_nil]
      exact ⟨⟨obj, locs⟩, invokes, answers, returned⟩
    · simp only [Option.toList_none, List.append_nil]
      exact hr''

/-- The executions of the implementation beside an execution of the protocol. -/
noncomputable def besideSeq {σ : ℕ → Fin n} {c : ℕ → (oneShot I).Config}
    (exec : (oneShot I).Execution σ c) (E₀ : I.Config) (h₀ : Beside (c 0) E₀) :
    (m : ℕ) → {E : I.Config // Beside (c m) E}
  | 0 => ⟨E₀, h₀⟩
  | m + 1 =>
      ⟨(beside_step (besideSeq exec E₀ h₀ m).2 (exec m)).choose_spec.choose,
        (beside_step (besideSeq exec E₀ h₀ m).2 (exec m)).choose_spec.choose_spec.2.1⟩

theorem besideSeq_step {σ : ℕ → Fin n} {c : ℕ → (oneShot I).Config}
    (exec : (oneShot I).Execution σ c) (E₀ : I.Config) (h₀ : Beside (c 0) E₀) (m : ℕ) :
    ∃ e, I.Step (besideSeq exec E₀ h₀ m).1 (.move (σ m)) e (besideSeq exec E₀ h₀ (m + 1)).1 :=
  ⟨_, (beside_step (besideSeq exec E₀ h₀ m).2 (exec m)).choose_spec.choose_spec.1⟩

/-- **An implementation of a consensus object solves consensus.** If a base object implements a
consensus object for `n` processes, wait-free and linearizable, then it solves `n`-process
consensus. -/
theorem solvable_of_implements_consensus (impl : Implements X (consensusObject V) none n) :
    Solvable X n V := by
  obtain ⟨I, lin, wf⟩ := impl
  refine ⟨oneShot I, ⟨?_, ?_, ?_⟩⟩
  · -- agreement: move both deciders until they have answered; a consensus object's answers agree
    intro x C reach i j v w hv hw
    obtain ⟨cs₀, h₀, run₀, invokes₀, noResp₀⟩ := run_called (I := I) x n le_rfl
    obtain ⟨σ, runP⟩ := reach
    obtain ⟨cs₁, E₁, h₁, run₁, tr₁⟩ := track_run (track_called (I := I) x invokes₀ noResp₀) runP
    obtain ⟨e₂, E₂, step₂, tr₂, mem₂⟩ := track_answer tr₁ hv
    obtain ⟨e₃, E₃, step₃, tr₃, mem₃⟩ := track_answer tr₂ hw
    have trace : I.Trace (h₀ ++ h₁ ++ e₂.toList ++ e₃.toList) :=
      ⟨cs₀ ++ cs₁ ++ [.move i] ++ [.move j], E₃,
        run_append (run_append (run_append run₀ run₁) (run_single step₂)) (run_single step₃)⟩
    exact ((consensus_history (lin _ trace)).1 i v j w (List.mem_append_left _ mem₂) mem₃)
  · -- validity: an answer was proposed, and only the inputs were proposed
    intro x C reach i v hv
    obtain ⟨cs₀, h₀, run₀, invokes₀, noResp₀⟩ := run_called (I := I) x n le_rfl
    obtain ⟨σ, runP⟩ := reach
    obtain ⟨cs₁, E₁, h₁, run₁, tr₁⟩ := track_run (track_called (I := I) x invokes₀ noResp₀) runP
    obtain ⟨e₂, E₂, step₂, tr₂, mem₂⟩ := track_answer tr₁ hv
    have trace : I.Trace (h₀ ++ h₁ ++ e₂.toList) :=
      ⟨cs₀ ++ cs₁ ++ [.move i], E₂, run_append (run_append run₀ run₁) (run_single step₂)⟩
    obtain ⟨j, hj⟩ := (consensus_history (lin _ trace)).2 i v mem₂
    exact ⟨j, (tr₂.2.1 j v hj).symm⟩
  · -- wait-freedom: the implementation's, along an execution of it beside the protocol's
    intro x σ c start exec i often
    have h₀ : Beside (c 0) (called I x n) := by
      rw [start]; exact ⟨rfl, fun j => Or.inl (by simp [called]; rfl)⟩
    obtain ⟨cs', c', start', exec', cn⟩ : ∃ (cs' : ℕ → Choice n (consensusObject V).Op)
        (c' : ℕ → I.Config), c' 0 = I.initial ∧ I.Execution cs' c' ∧
        ∀ k, n ≤ k → c' k = (besideSeq exec (called I x n) h₀ (k - n)).1 ∧
          cs' k = .move (σ (k - n)) := by
      refine ⟨fun k => if hk : k < n then .invoke ⟨k, hk⟩ (x ⟨k, hk⟩) else .move (σ (k - n)),
        fun k => if k < n then called I x k else (besideSeq exec (called I x n) h₀ (k - n)).1,
        ?_, ?_, ?_⟩
      · by_cases hn : 0 < n
        · simp only [if_pos hn]; exact called_zero x
        · simp only [if_neg hn]
          rw [Nat.zero_sub]
          show called I x n = I.initial
          have : n = 0 := by omega
          subst this
          exact called_zero x
      · intro k
        by_cases hk : k < n
        · refine ⟨some (.invoke ⟨k, hk⟩ (x ⟨k, hk⟩)), ?_⟩
          simp only [dif_pos hk, if_pos hk]
          by_cases hk' : k + 1 < n
          · simp only [if_pos hk']; exact called_step x k hk
          · simp only [if_neg hk']
            have last := called_step (I := I) x k hk
            rw [show k + 1 = n by omega] at last
            rw [show k + 1 - n = 0 by omega]
            exact last
        · obtain ⟨e, step⟩ := besideSeq_step exec (called I x n) h₀ (k - n)
          refine ⟨e, ?_⟩
          simp only [dif_neg hk, if_neg hk, if_neg (show ¬ k + 1 < n by omega)]
          rw [show k + 1 - n = k - n + 1 by omega]
          exact step
      · intro k hk
        simp [show ¬ k < n by omega]
    have busy : I.Busy (c' n) i := by
      rw [(cn n le_rfl).1, Nat.sub_self]
      exact ⟨I.begin i (I.mem₀ i) (x i), by show (called I x n).loc i = _; simp [called]⟩
    have often' : ∀ N, ∃ k, N ≤ k ∧ cs' k = .move i := by
      intro N
      obtain ⟨m, hm, hσ⟩ := often N
      exact ⟨n + m, by omega, by rw [(cn (n + m) (by omega)).2, Nat.add_sub_cancel_left, hσ]⟩
    obtain ⟨k, hk, notBusy⟩ := wf cs' c' start' exec' i n busy often'
    rw [(cn k hk).1] at notBusy
    obtain ⟨-, locs⟩ := (besideSeq exec (called I x n) h₀ (k - n)).2
    rcases locs i with busyI | ⟨r, m, hr, -⟩
    · exact absurd ⟨_, busyI⟩ notBusy
    · exact ⟨k - n, by rw [oneShot_decision_ret hr]; rfl⟩

end OneShot

/-! ## Universality and its absence -/

/-- An object is **universal for `n` processes** when it implements every object given by a
sequential specification, from every state, wait-free and linearizably. -/
def UniversalFor (X : ObjectType) (n : ℕ) : Prop :=
  ∀ (Y : DetObject) (s₀ : Y.State), Implements X Y s₀ n

/-- An object that cannot solve `n`-process consensus implements no consensus object for `n`
processes. -/
theorem not_implements_consensus {X : ObjectType} {n : ℕ} (h : ¬ Solvable X n Bool) :
    ¬ Implements X (consensusObject Bool) none n :=
  fun impl => h (solvable_of_implements_consensus impl)

/-- **An object that cannot solve `n`-process consensus is not universal for `n` processes.** -/
theorem not_universal_of_not_solvable {X : ObjectType} {n : ℕ} (h : ¬ Solvable X n Bool) :
    ¬ UniversalFor X n :=
  fun u => not_implements_consensus h (u _ _)

section Spaces

variable {A : Type} [DecidableEq A]

/-- **MeTTa's separate operations with silent removal are not universal for two or more
processes**, even with any number of spaces and registers. -/
theorem silentSpaces_not_universal (K ι V : Type) [DecidableEq K] [DecidableEq ι] {n : ℕ}
    (two : 2 ≤ n) : ¬ UniversalFor (silentSpacesAndRegisters A K ι V).toObject n :=
  not_universal_of_not_solvable (silentSpaces_registers_not_solvable_two K ι V two)

/-- **Whatever its removals answer, MeTTa's separate operations are not universal for three or more
processes**, even with any number of spaces and registers. -/
theorem spacesWith_not_universal {R : Type} (reply : Multiset A → SpaceOp A → R) (K ι V : Type)
    [DecidableEq K] [DecidableEq ι] {n : ℕ} (three : 3 ≤ n) :
    ¬ UniversalFor (spacesWithAndRegisters A reply K ι V).toObject n :=
  not_universal_of_not_solvable (spacesWith_registers_not_solvable_three reply K ι V three)

/-- Removal reporting success: not universal for three or more processes. -/
theorem separateSpace_not_universal {n : ℕ} (three : 3 ≤ n) :
    ¬ UniversalFor (separateSpace A).toObject n :=
  not_universal_of_not_solvable (separateSpace_not_solvable_three three)

/-- Counting removal: not universal for three or more processes. -/
theorem countSpace_not_universal {n : ℕ} (three : 3 ≤ n) :
    ¬ UniversalFor (countSpace A).toObject n :=
  not_universal_of_not_solvable (spaceWith_not_solvable_three countReply three)

/-- PeTTa's operations with counting removal of every match: not universal for three or more
processes. -/
theorem patternSpace_not_universal {n : ℕ} (three : 3 ≤ n) :
    ¬ UniversalFor (patternSpace A).toObject n :=
  not_universal_of_not_solvable (not_solvable_of_stateBlind three patternSpace_stateBlind)

/-- Hyperon's operations with a removal answering `0` or `1`: not universal for three or more
processes. -/
theorem oneRemovalSpace_not_universal {n : ℕ} (three : 3 ≤ n) :
    ¬ UniversalFor (oneRemovalSpace A).toObject n :=
  not_universal_of_not_solvable (not_solvable_of_stateBlind three oneRemovalSpace_stateBlind)

/-- Registers alone are not universal for two or more processes. -/
theorem registers_not_universal {ι V : Type} [DecidableEq ι] {n : ℕ} (two : 2 ≤ n) :
    ¬ UniversalFor (registers ι V).toObject n :=
  not_universal_of_not_solvable (registers_not_solvable_two two)

/-- **Steps implement a consensus object for any number of processes**, when atoms can encode the
log; so steps reach consensus for any number of processes, as `StepSpace` found directly. -/
theorem steps_implement_consensus {n : ℕ} (enc : Universal.Code n Bool → A)
    (inj : Function.Injective enc) : Implements (stepSpace A).toObject (consensusObject Bool) none n :=
  Universal.steps_universal (consensusObject Bool) none enc inj

theorem steps_solvable_via_universality {n : ℕ} (enc : Universal.Code n Bool → A)
    (inj : Function.Injective enc) : Solvable (stepSpace A).toObject n Bool :=
  solvable_of_implements_consensus (steps_implement_consensus enc inj)

end Spaces

/-! ## Controls -/

namespace Controls

/-- **Positive control**: a consensus object used atomically solves consensus for any number of
processes. -/
theorem atomic_consensus_solves (V : Type) (n : ℕ) :
    Solvable (consensusObject V).toObject n V :=
  solvable_of_implements_consensus ⟨atomic _ none n, atomic_linearizable (Y := consensusObject V) none,
    atomic_waitFree (Y := consensusObject V) none⟩

/-- A front-end that answers each proposal with the proposer's own value, without any base
operation. -/
def ownAnswer (X : ObjectType) (s : X.State) : Implementation X (consensusObject Bool) 2 where
  init := s
  Mem := Unit
  Work := Bool
  mem₀ _ := ()
  begin _ _ v := v
  move _ v := .ret v ()
  next _ v _ := v

/-- **Negative control**: answering one's own proposal is not a linearizable consensus object: the
answers `false` and `true` disagree. -/
theorem ownAnswer_not_linearizable (X : ObjectType) (s : X.State) :
    ¬ (ownAnswer X s).Linearizable none := by
  intro lin
  let I := ownAnswer X s
  have s1 := Step.invoke (I := I) (C := I.initial) (i := 0) (m := ()) false rfl
  have s2 := Step.ret (I := I) (C := ⟨I.initial.obj, Function.update I.initial.loc 0
    (.busy (I.begin 0 () false))⟩) (i := 0) (w := false) (r := false) (m := ()) (by simp; rfl) rfl
  have s3 := Step.invoke (I := I) (C := ⟨I.initial.obj, Function.update (Function.update
    I.initial.loc 0 (.busy (I.begin 0 () false))) 0 (.idle ())⟩) (i := 1) (m := ()) true
    (by simp; rfl)
  have s4 := Step.ret (I := I) (C := ⟨I.initial.obj, Function.update (Function.update
    (Function.update I.initial.loc 0 (.busy (I.begin 0 () false))) 0 (.idle ())) 1
    (.busy (I.begin 1 () true))⟩) (i := 1) (w := true) (r := true) (m := ()) (by simp; rfl) rfl
  have trace : I.Trace [.invoke 0 false, .respond 0 false, .invoke 1 true, .respond 1 true] :=
    ⟨[.invoke 0 false, .move 0, .invoke 1 true, .move 1], _,
      ⟨_, _, _, s1, ⟨_, _, _, s2, ⟨_, _, _, s3, ⟨_, _, _, s4, ⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩⟩
  have := (consensus_history (lin _ trace)).1 0 false 1 true (by simp) (by simp)
  cases this

end Controls

end Mettapedia.GSLT.Coordination.ConsensusNumbers
