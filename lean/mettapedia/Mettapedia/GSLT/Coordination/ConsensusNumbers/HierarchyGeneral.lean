import Mettapedia.GSLT.Coordination.ConsensusNumbers.Hierarchy

/-!
# The hierarchy theorem for general implementations

**If `X` implements `Y` (wait-free and linearizable) for `n` processes, and `Y` solves `n`-process
consensus, then `X` solves `n`-process consensus** (`solvable_of_implements`). So an object cannot
implement one of a higher consensus number (`not_implements_of_consensusNumber`).

The consensus protocol over `X` runs the protocol over `Y`, each of its operations on `Y` performed
by the implementation's program (`compose`). One more ingredient is needed: a step of the composed
protocol must call some operation of `X`, also when a process only starts an operation or returns
from one. Here `X` has an operation that always fires and changes nothing (`NoOp`, for example a
read); the composed protocol calls it at those moments.

## Why the composed protocol is correct

* **Agreement and validity.** Take a reachable configuration. The calls and returns of the target's
  operations form a history of the implementation, hence a linearizable one: a history of `Y` used
  atomically. Replaying that atomic run step by step is a run of the protocol over `Y`
  (`replay_atomic`), in which each process that has decided in the composed protocol has the same local
  state. The protocol over `Y` agrees and is valid there, so the composed one is.
* **Wait-freedom.** A wait-free protocol over a deterministic object is **bounded**: from the
  initial configuration, runs in which every step is taken by a process that has not decided are
  boundedly long (`Solves.bounded`; otherwise an infinite such run would exist, and some process
  would be scheduled in it infinitely often without deciding). If a process of the composed protocol
  never decided while being scheduled infinitely often, the implementation's wait-freedom would make
  it complete more and more operations on `Y`; replaying a long enough history gives a run of the
  protocol over `Y` longer than the bound.

## Words

* **Client state** (`client`): the local state of a process of the protocol over `Y`, as it follows
  from the answers it received so far. Example: in a protocol that claims then reads, after the
  answer "lost" the client state is "about to read".
* **Consistent history** (`Consistent`): every call in it is the call the caller's client state asks
  for.
* **Effective run** (`Effective`): every step is taken by a process that has not decided. A decided
  process's steps change nothing; dropping them leaves an effective run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

open Implementation

/-! ## Wait-free protocols are bounded -/

namespace Protocol

variable {T : DetObject} {n : ℕ} {V : Type} {P : Protocol T.toObject n V}

variable (P) in
/-- A run in which every step is taken by a process that has not decided. -/
def Effective : P.Config → List (Fin n) → Prop
  | _, [] => True
  | C, i :: σ => P.decision C i = none ∧ Effective (P.go C i) σ

variable (P) in
/-- From `C`, effective runs are arbitrarily long. -/
def Unbounded (C : P.Config) : Prop := ∀ B, ∃ σ, P.Effective C σ ∧ B ≤ σ.length

/-- An unbounded configuration has an undecided process whose step keeps it unbounded. -/
theorem Unbounded.child {C : P.Config} (h : P.Unbounded C) :
    ∃ i, P.decision C i = none ∧ P.Unbounded (P.go C i) := by
  by_contra noChild
  have bounds : ∀ i, ∃ B, P.decision C i = none → ∀ σ, P.Effective (P.go C i) σ → σ.length < B := by
    intro i
    by_cases und : P.decision C i = none
    · have notUnb : ¬ P.Unbounded (P.go C i) := fun hu => noChild ⟨i, und, hu⟩
      unfold Unbounded at notUnb
      push Not at notUnb
      obtain ⟨B, hB⟩ := notUnb
      exact ⟨B, fun _ σ eff => hB σ eff⟩
    · exact ⟨0, fun h' => absurd h' und⟩
  choose B hB using bounds
  obtain ⟨σ, eff, len⟩ := h (Finset.univ.sup B + 1)
  cases σ with
  | nil => simp at len
  | cons i τ =>
      obtain ⟨und, eff'⟩ := eff
      have short := hB i und τ eff'
      have le : B i ≤ Finset.univ.sup B := Finset.le_sup (Finset.mem_univ i)
      simp only [List.length_cons] at len
      omega

/-- **A wait-free protocol is bounded**: from each initial configuration, effective runs are boundedly
long. -/
theorem Solves.bounded (S : P.Solves) (x : Fin n → V) :
    ∃ B, ∀ σ, P.Effective (P.initial x) σ → σ.length ≤ B := by
  by_contra hcon
  push Not at hcon
  have start : P.Unbounded (P.initial x) := fun B => by
    obtain ⟨σ, eff, len⟩ := hcon B
    exact ⟨σ, eff, le_of_lt len⟩
  let Good := {C : P.Config // P.Reach x C ∧ P.Unbounded C}
  let pick : Good → Fin n := fun C => C.2.2.child.choose
  let adv : Good → Good := fun C =>
    ⟨P.go C.1 (pick C), C.2.1.go _, C.2.2.child.choose_spec.2⟩
  let seq : ℕ → Good := fun m => adv^[m] ⟨P.initial x, Reach.initial x, start⟩
  let σ : ℕ → Fin n := fun m => pick (seq m)
  let c : ℕ → P.Config := fun m => (seq m).1
  have exec : P.Execution σ c := by
    intro m
    apply step_iff_go.mpr
    show (adv^[m + 1] _).1 = _
    rw [Function.iterate_succ_apply']
  obtain ⟨i, infinite⟩ := Finite.exists_infinite_fiber σ
  have often : InfinitelyOften σ i := by
    intro N
    obtain ⟨m, mem, lt⟩ := (Set.infinite_coe_iff.mp infinite).exists_gt N
    exact ⟨m, le_of_lt lt, mem⟩
  obtain ⟨m, hm⟩ := S.waitFree x σ c rfl exec i often
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
  obtain ⟨m', hm', hσ⟩ := often m
  have stays : ∀ d, P.decision (c (m + d)) i = some v := by
    intro d
    induction d with
    | zero => exact hv
    | succ d ih => exact (exec (m + d)).decision_of_decided ih
  have decided : P.decision (c m') i = some v := by
    have := stays (m' - m); rwa [Nat.add_sub_cancel' hm'] at this
  have undecided : P.decision (c m') (σ m') = none := (seq m').2.2.child.choose_spec.1
  rw [hσ, decided] at undecided
  cases undecided

end Protocol

/-! ## Open calls -/

section Open

variable {n : ℕ} {Op Res : Type}

/-- Whether process `j` has a call without its return, after `h`, starting from `b`. -/
def openAfter (j : Fin n) (b : Bool) (h : List (Event n Op Res)) : Bool :=
  h.foldl (fun b e => match e with
    | .invoke k _ => if k = j then true else b
    | .respond k _ => if k = j then false else b) b

/-- How many answers process `j` got in `h`. -/
def respCount (j : Fin n) (h : List (Event n Op Res)) : ℕ :=
  h.countP fun e => match e with
    | .respond k _ => decide (k = j)
    | .invoke _ _ => false

theorem openAfter_append (j : Fin n) (b : Bool) (h h' : List (Event n Op Res)) :
    openAfter j b (h ++ h') = openAfter j (openAfter j b h) h' := by
  simp [openAfter, List.foldl_append]

theorem respCount_append (j : Fin n) (h h' : List (Event n Op Res)) :
    respCount j (h ++ h') = respCount j h + respCount j h' := by
  simp [respCount, List.countP_append]

/-- A call that was open and is now closed was answered. -/
theorem respCount_pos_of_closed (j : Fin n) :
    ∀ (h : List (Event n Op Res)), openAfter j true h = false → 1 ≤ respCount j h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => simp [openAfter]
  | append_singleton h e ih =>
      intro closed
      rw [openAfter_append] at closed
      rw [respCount_append]
      cases e with
      | invoke k op =>
          have step : openAfter j (openAfter j true h) [(Event.invoke k op : Event n Op Res)] =
              if k = j then true else openAfter j true h := rfl
          rw [step] at closed
          have zero : respCount j [(Event.invoke k op : Event n Op Res)] = 0 := by simp [respCount]
          by_cases hk : k = j
          · rw [if_pos hk] at closed; cases closed
          · rw [if_neg hk] at closed
            have := ih closed; omega
      | respond k r =>
          by_cases hk : k = j
          · subst hk; simp [respCount]
          · have step : openAfter j (openAfter j true h) [(Event.respond k r : Event n Op Res)] =
                openAfter j true h := by
              simp [openAfter, hk]
            rw [step] at closed
            have := ih closed; omega

variable {X : ObjectType} {Y : DetObject} {J : Implementation X Y n}

/-- Whether a status is busy. -/
def isBusy : J.Status → Bool
  | .busy _ => true
  | .idle _ => false

/-- **Busy exactly when the call is open**: along any run, a process is busy at the end exactly when
its last event in the history is a call (or, with no event of it, when it was busy at the start). -/
theorem run_isBusy {C D : J.Config} {cs : List (Choice n Y.Op)} {h : List (Event n Y.Op Y.Res)}
    (run : J.Run C cs h D) (j : Fin n) :
    isBusy (D.loc j) = openAfter j (isBusy (C.loc j)) h := by
  induction cs generalizing C h with
  | nil => obtain ⟨rfl, hD⟩ := run; rw [hD]; rfl
  | cons c cs ih =>
      obtain ⟨e, E, h', step, rest, rfl⟩ := run
      rw [ih rest, openAfter_append]
      congr 1
      cases step with
      | @invoke i m op hi =>
          by_cases same : j = i
          · subst same; simp [openAfter, isBusy]
          · simp [openAfter, Function.update_of_ne same, Ne.symm same]
      | @call i w a s r hl hm hf =>
          by_cases same : j = i
          · subst same; simp [openAfter, isBusy, hl]
          · simp [openAfter, Function.update_of_ne same]
      | wait _ _ _ => rfl
      | @ret i w r m hl hm =>
          by_cases same : j = i
          · subst same; simp [openAfter, isBusy]
          · simp [openAfter, Function.update_of_ne same, Ne.symm same]
      | rest _ => rfl

end Open

/-! ## Replaying an atomic run as a run of the protocol -/

section Replay

variable {Y : DetObject} {n : ℕ} {V : Type} (P : Protocol Y.toObject n V) (x : Fin n → V)

/-- What one event does to process `j`'s client state: an answer to `j` advances it. -/
def clientStep (j : Fin n) (l : P.Local) : Event n Y.Op Y.Res → P.Local
  | .respond k r => if k = j then P.next j l r else l
  | .invoke _ _ => l

/-- **Process `j`'s client state** after the history `h`. -/
def client (j : Fin n) (h : List (Event n Y.Op Y.Res)) : P.Local :=
  h.foldl (clientStep P j) (P.start j (x j))

/-- **A consistent history**: every call is the call its caller's client state asks for. -/
def Consistent (h : List (Event n Y.Op Y.Res)) : Prop :=
  ∀ h₁ h₂ j op, h = h₁ ++ Event.invoke j op :: h₂ → P.action j (client P x j h₁) = .invoke op

variable {P x}

theorem client_snoc (j : Fin n) (h : List (Event n Y.Op Y.Res)) (e : Event n Y.Op Y.Res) :
    client P x j (h ++ [e]) = clientStep P j (client P x j h) e := by
  simp [client, List.foldl_append]

theorem consistent_nil : Consistent P x [] := by
  intro h₁ h₂ j op h; simp at h

theorem consistent_snoc {h : List (Event n Y.Op Y.Res)} {e : Event n Y.Op Y.Res}
    (cons : Consistent P x h)
    (asks : ∀ j op, e = Event.invoke j op → P.action j (client P x j h) = .invoke op) :
    Consistent P x (h ++ [e]) := by
  intro h₁ h₂ j op split
  rcases List.eq_nil_or_concat h₂ with rfl | ⟨L, b, rfl⟩
  · have := List.append_inj' split (by simp)
    obtain ⟨rfl, he⟩ := this
    exact asks j op (List.singleton_inj.mp he)
  · have split' : h ++ [e] = (h₁ ++ Event.invoke j op :: L) ++ [b] := by simpa using split
    obtain ⟨hh, -⟩ := List.append_inj' split' (by simp)
    exact cons h₁ L j op hh

/-- Whether an atomic status holds an answer not yet returned. -/
def doneFlag {s₀ : Y.State} : (atomic Y s₀ n).Status → ℕ
  | .busy (.done _) => 1
  | _ => 0

/-- How a status of the target used atomically matches a local state of the protocol over `Y`,
after the history `h`. -/
def ReplayLoc (j : Fin n) (h : List (Event n Y.Op Y.Res)) :
    (atomic Y P.init n).Status → P.Local → Prop
  | .idle _, l => l = client P x j h
  | .busy (.pending op), l => l = client P x j h ∧ P.action j (client P x j h) = .invoke op
  | .busy (.done r), l => ∃ op, P.action j (client P x j h) = .invoke op ∧
      l = P.next j (client P x j h) r

/-- How a configuration of the target used atomically matches one of the protocol over `Y`. -/
def ReplayRel (h : List (Event n Y.Op Y.Res)) (A : (atomic Y P.init n).Config) (D : P.Config) :
    Prop :=
  D.obj = A.obj ∧ ∀ j, ReplayLoc (P := P) (x := x) j h (A.loc j) (D.loc j)

theorem replayLoc_invoke_other {j : Fin n} {h : List (Event n Y.Op Y.Res)}
    {st : (atomic Y P.init n).Status} {l : P.Local} (k : Fin n) (op : Y.Op)
    (m : ReplayLoc (P := P) (x := x) j h st l) :
    ReplayLoc (P := P) (x := x) j (h ++ [.invoke k op]) st l := by
  have same : client P x j (h ++ [.invoke k op]) = client P x j h := by rw [client_snoc]; rfl
  cases st with
  | idle u => show l = _; rw [same]; exact m
  | busy w =>
      cases w with
      | pending op' => show l = _ ∧ _; rw [same]; exact m
      | done r => show ∃ _, _; rw [same]; exact m

theorem replayLoc_respond_other {j k : Fin n} (ne : k ≠ j) {h : List (Event n Y.Op Y.Res)}
    {st : (atomic Y P.init n).Status} {l : P.Local} (r : Y.Res)
    (m : ReplayLoc (P := P) (x := x) j h st l) :
    ReplayLoc (P := P) (x := x) j (h ++ [.respond k r]) st l := by
  have same : client P x j (h ++ [.respond k r]) = client P x j h := by
    rw [client_snoc]; simp [clientStep, ne]
  cases st with
  | idle u => show l = _; rw [same]; exact m
  | busy w =>
      cases w with
      | pending op' => show l = _ ∧ _; rw [same]; exact m
      | done r' => show ∃ _, _; rw [same]; exact m

theorem doneFlag_update_pending {A : (atomic Y P.init n).Config} {j : Fin n} {m : Unit}
    (hj : A.loc j = .idle m) (op : Y.Op) (i : Fin n) :
    doneFlag (Function.update A.loc j (.busy ((atomic Y P.init n).begin j m op)) i) =
      doneFlag (A.loc i) := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, hj]; rfl
  · rw [Function.update_of_ne hi]

theorem doneFlag_update_done {A : (atomic Y P.init n).Config} {j : Fin n} {op : Y.Op}
    (hj : A.loc j = .busy (.pending op)) (r : Y.Res) (i : Fin n) :
    doneFlag (Function.update A.loc j (.busy ((atomic Y P.init n).next j (.pending op) r)) i) =
      doneFlag (A.loc i) + if i = j then 1 else 0 := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, hj, if_pos rfl]; rfl
  · rw [Function.update_of_ne hi, if_neg hi, add_zero]

theorem doneFlag_update_idle {A : (atomic Y P.init n).Config} {j : Fin n} {r : Y.Res}
    (hj : A.loc j = .busy (.done r)) (m : Unit) (i : Fin n) :
    doneFlag (Function.update A.loc j (.idle m) i) + (if i = j then 1 else 0) =
      doneFlag (A.loc i) := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, hj, if_pos rfl]; rfl
  · rw [Function.update_of_ne hi, if_neg hi, add_zero]

theorem count_cons_ite (j i : Fin n) (σ : List (Fin n)) :
    (j :: σ).count i = σ.count i + if i = j then 1 else 0 := by
  by_cases hi : i = j
  · subst hi; simp
  · simp [Ne.symm hi, hi]

theorem respCount_respond (i j : Fin n) (r : Y.Res) :
    respCount i [(Event.respond j r : Event n Y.Op Y.Res)] = if i = j then 1 else 0 := by
  by_cases hi : i = j
  · subst hi; simp [respCount]
  · simp [respCount, Ne.symm hi, hi]

theorem respCount_invoke (i j : Fin n) (op : Y.Op) :
    respCount i [(Event.invoke j op : Event n Y.Op Y.Res)] = 0 := by
  simp [respCount]

/-- **Replay**: a run of the target used atomically, over a consistent history, is matched by an
effective run of the protocol over `Y`, one step per operation taking effect; each answer counts one
such step. -/
theorem replay_atomic {pre h : List (Event n Y.Op Y.Res)} {A A' : (atomic Y P.init n).Config}
    {cs : List (Choice n Y.Op)} {D : P.Config}
    (cons : Consistent P x (pre ++ h)) (rel : ReplayRel (P := P) (x := x) pre A D)
    (run : (atomic Y P.init n).Run A cs h A') :
    ∃ σ, P.Effective D σ ∧ ReplayRel (P := P) (x := x) (pre ++ h) A' (P.run D σ) ∧
      ∀ i, respCount i h + doneFlag (A'.loc i) = σ.count i + doneFlag (A.loc i) := by
  induction cs generalizing pre h A D with
  | nil =>
      obtain ⟨rfl, hA⟩ := run
      rw [hA, List.append_nil]
      exact ⟨[], trivial, rel, fun i => by simp [respCount]⟩
  | cons c cs ih =>
      obtain ⟨e, E, h', step, rest, rfl⟩ := run
      obtain ⟨obj, locs⟩ := rel
      cases step with
      | @invoke j m op hj =>
          have asks : P.action j (client P x j pre) = .invoke op := cons pre h' j op (by simp)
          have same : client P x j (pre ++ [.invoke j op]) = client P x j pre := by
            rw [client_snoc]; rfl
          have rel' : ReplayRel (P := P) (x := x) (pre ++ [.invoke j op])
              ⟨A.obj, Function.update A.loc j (.busy ((atomic Y P.init n).begin j m op))⟩ D := by
            refine ⟨obj, fun k => ?_⟩
            by_cases hk : k = j
            · subst hk
              simp only [Function.update_self]
              have mk := locs k
              rw [hj] at mk
              exact ⟨by rw [same]; exact mk, by rw [same]; exact asks⟩
            · simp only [Function.update_of_ne hk]; exact replayLoc_invoke_other j op (locs k)
          have cons' : Consistent P x ((pre ++ [.invoke j op]) ++ h') := by
            simpa [List.append_assoc] using cons
          obtain ⟨σ, eff, rel'', counts⟩ := ih cons' rel' rest
          have hist : pre ++ ((some (Event.invoke j op)).toList ++ h') =
              (pre ++ [.invoke j op]) ++ h' := by simp
          refine ⟨σ, eff, by rw [hist]; exact rel'', fun i => ?_⟩
          have := counts i
          have flag := doneFlag_update_pending (P := P) hj op i
          rw [show (some (Event.invoke j op)).toList ++ h' = [Event.invoke j op] ++ h' from rfl,
            respCount_append, respCount_invoke]
          change _ = _ + doneFlag (Function.update A.loc j
            (.busy ((atomic Y P.init n).begin j m op)) i) at this
          omega
      | @call j w a s r hl hm hf =>
          cases w with
          | done r' => exact absurd hm (by simp [atomic])
          | pending op =>
              have ha : op = a := by simpa [atomic] using hm
              subst ha
              have hf' : Y.apply A.obj op = (s, r) := hf
              have mj := locs j
              rw [hl] at mj
              obtain ⟨hD, asks⟩ := mj
              have act : P.action j (D.loc j) = .invoke op := by rw [hD]; exact asks
              have und : P.decision D j = none := by
                unfold Protocol.decision; rw [act]
              have goD : P.go D j =
                  ⟨s, Function.update D.loc j (P.next j (client P x j pre) r)⟩ := by
                rw [Protocol.go_of_invoke act, obj, hf', hD]
              have rel' : ReplayRel (P := P) (x := x) pre
                  ⟨s, Function.update A.loc j (.busy ((atomic Y P.init n).next j (.pending op) r))⟩
                  (P.go D j) := by
                rw [goD]
                refine ⟨rfl, fun k => ?_⟩
                by_cases hk : k = j
                · subst hk
                  simp only [Function.update_self]
                  exact ⟨op, asks, rfl⟩
                · simp only [Function.update_of_ne hk]; exact locs k
              have cons' : Consistent P x (pre ++ h') := by simpa using cons
              obtain ⟨σ, eff, rel'', counts⟩ := ih cons' rel' rest
              have hist : pre ++ ((none : Option (Event n Y.Op Y.Res)).toList ++ h') = pre ++ h' := by
                simp
              refine ⟨j :: σ, ⟨und, eff⟩, by rw [hist]; exact rel'', fun i => ?_⟩
              have := counts i
              have flag := doneFlag_update_done (P := P) hl r i
              rw [show (none : Option (Event n Y.Op Y.Res)).toList ++ h' = h' from rfl,
                count_cons_ite]
              change _ = _ + doneFlag (Function.update A.loc j
                (.busy ((atomic Y P.init n).next j (.pending op) r)) i) at this
              split_ifs at flag ⊢ <;> omega
      | @wait j w a hl hm never =>
          cases w with
          | done r' => exact absurd hm (by simp [atomic])
          | pending op =>
              have ha : op = a := by simpa [atomic] using hm
              subst ha
              exact absurd rfl (never (Y.apply A.obj op).1 (Y.apply A.obj op).2)
      | @ret j w r m hl hm =>
          cases w with
          | pending op => exact absurd hm (by simp [atomic])
          | done r' =>
              have hr : r' = r := (Move.ret.inj hm).1
              subst hr
              have mj := locs j
              rw [hl] at mj
              obtain ⟨op, asks, hD⟩ := mj
              have rel' : ReplayRel (P := P) (x := x) (pre ++ [.respond j r'])
                  ⟨A.obj, Function.update A.loc j (.idle m)⟩ D := by
                refine ⟨obj, fun k => ?_⟩
                by_cases hk : k = j
                · subst hk
                  simp only [Function.update_self]
                  show D.loc k = client P x k (pre ++ [.respond k r'])
                  rw [client_snoc, hD]
                  simp [clientStep]
                · simp only [Function.update_of_ne hk]
                  exact replayLoc_respond_other (Ne.symm hk) r' (locs k)
              have cons' : Consistent P x ((pre ++ [.respond j r']) ++ h') := by
                simpa [List.append_assoc] using cons
              obtain ⟨σ, eff, rel'', counts⟩ := ih cons' rel' rest
              have hist : pre ++ ((some (Event.respond j r')).toList ++ h') =
                  (pre ++ [.respond j r']) ++ h' := by simp
              refine ⟨σ, eff, by rw [hist]; exact rel'', fun i => ?_⟩
              have := counts i
              have flag := doneFlag_update_idle (P := P) hl m i
              rw [show (some (Event.respond j r')).toList ++ h' = [Event.respond j r'] ++ h' from rfl,
                respCount_append, respCount_respond]
              change _ = _ + doneFlag (Function.update A.loc j (.idle m) i) at this
              split_ifs at flag ⊢ <;> omega
      | @rest j m hl =>
          have cons' : Consistent P x (pre ++ h') := by simpa using cons
          obtain ⟨σ, eff, rel'', counts⟩ := ih cons' ⟨obj, locs⟩ rest
          have hist : pre ++ ((none : Option (Event n Y.Op Y.Res)).toList ++ h') = pre ++ h' := by
            simp
          refine ⟨σ, eff, by rw [hist]; exact rel'', fun i => ?_⟩
          rw [show (none : Option (Event n Y.Op Y.Res)).toList ++ h' = h' from rfl]
          exact counts i

end Replay

/-! ## The composed protocol -/

section Compose

variable {X : ObjectType} {Y : DetObject} {n : ℕ} {V : Type}

/-- An operation that always fires and changes nothing, such as a read. -/
def NoOp (X : ObjectType) (a : X.Op) : Prop :=
  (∀ s, ∃ r, X.Fires s a s r) ∧ ∀ s s' r, X.Fires s a s' r → s' = s

variable (P : Protocol Y.toObject n V) (I : Implementation X Y n) (a₀ : X.Op)

/-- What a process of the composed protocol does. -/
def composeAction (i : Fin n) : P.Local × I.Status → Action X.Op V
  | (l, .idle _) => match P.action i l with
    | .decide v => .decide v
    | .invoke _ => .invoke a₀
  | (_, .busy w) => match I.move i w with
    | .call a => .invoke a
    | .ret _ _ => .invoke a₀

/-- Its next local state. -/
def composeNext (i : Fin n) : P.Local × I.Status → X.Res → P.Local × I.Status
  | (l, .idle m), _ => match P.action i l with
    | .decide _ => (l, .idle m)
    | .invoke op => (l, .busy (I.begin i m op))
  | (l, .busy w), ans => match I.move i w with
    | .call _ => (l, .busy (I.next i w ans))
    | .ret r m => (P.next i l r, .idle m)

/-- **The composed protocol**: the protocol over `Y`, each operation on `Y` performed by the
implementation's program over `X`. Starting an operation and returning from one call the no-op
`a₀`. -/
abbrev compose : Protocol X n V where
  Local := P.Local × I.Status
  start i v := (P.start i v, .idle (I.mem₀ i))
  init := I.init
  action := composeAction P I a₀
  next := composeNext P I

/-- The implementation's configuration inside a configuration of the composed protocol. -/
def proj {P : Protocol Y.toObject n V} {I : Implementation X Y n} {a₀ : X.Op}
    (C : (compose P I a₀).Config) : I.Config :=
  ⟨C.obj, fun j => (C.loc j).2⟩

/-- The implementation's choice for a step of process `i`. -/
def qChoice (i : Fin n) : P.Local × I.Status → Choice n Y.Op
  | (l, .idle _) => match P.action i l with
    | .invoke op => .invoke i op
    | .decide _ => .move i
  | (_, .busy _) => .move i

/-- The event a step of process `i` shows. -/
def qEvent (i : Fin n) : P.Local × I.Status → Option (Event n Y.Op Y.Res)
  | (l, .idle _) => match P.action i l with
    | .invoke op => some (.invoke i op)
    | .decide _ => none
  | (_, .busy w) => match I.move i w with
    | .ret r _ => some (.respond i r)
    | .call _ => none

variable {P I a₀}

theorem compose_decision {C : (compose P I a₀).Config} {i : Fin n} {v : V}
    (h : (compose P I a₀).decision C i = some v) :
    ∃ m, (C.loc i).2 = .idle m ∧ P.action i (C.loc i).1 = .decide v := by
  have act := Protocol.decision_eq_some_iff.mp h
  change composeAction P I a₀ i (C.loc i) = _ at act
  rcases hC : C.loc i with ⟨l, st⟩
  rw [hC] at act
  cases st with
  | idle m =>
      cases hP : P.action i l with
      | decide v' =>
          simp only [composeAction, hP] at act
          cases act
          exact ⟨m, rfl, rfl⟩
      | invoke op => simp [composeAction, hP] at act
  | busy w =>
      cases hI : I.move i w with
      | call a => simp [composeAction, hI] at act
      | ret r m => simp [composeAction, hI] at act

theorem compose_decision_of {C : (compose P I a₀).Config} {i : Fin n} {v : V} {m : I.Mem}
    (h2 : (C.loc i).2 = .idle m) (h1 : P.action i (C.loc i).1 = .decide v) :
    (compose P I a₀).decision C i = some v := by
  apply Protocol.decision_eq_some_iff.mpr
  change composeAction P I a₀ i (C.loc i) = _
  rcases hC : C.loc i with ⟨l, st⟩
  rw [hC] at h1 h2
  simp only at h1 h2
  subst h2
  simp only [composeAction, h1]

/-- **A step of the composed protocol is a step of the implementation**, with a call or a return as
its event when the process starts or finishes an operation. -/
theorem compose_step (noop : NoOp X a₀) {C D : (compose P I a₀).Config} {i : Fin n}
    (step : (compose P I a₀).Step C i D) :
    I.Step (proj C) (qChoice P I i (C.loc i)) (qEvent P I i (C.loc i)) (proj D) := by
  cases step with
  | @decided v hd =>
      obtain ⟨m, h2, h1⟩ := compose_decision (Protocol.decision_eq_some_iff.mpr hd)
      have idle : (proj C).loc i = .idle m := h2
      rcases hC : C.loc i with ⟨l, st⟩
      rw [hC] at h1 h2
      simp only at h1 h2
      subst h2
      simp only [qChoice, qEvent, h1]
      exact Step.rest idle
  | @fires op s r hact hf =>
      change composeAction P I a₀ i (C.loc i) = _ at hact
      show I.Step (proj C) _ _ ⟨s, fun j => (Function.update C.loc i
        (composeNext P I i (C.loc i) r) j).2⟩
      have locC : ∀ j, (proj C).loc j = (C.loc j).2 := fun j => rfl
      rcases hC : C.loc i with ⟨l, st⟩
      rw [hC] at hact
      cases st with
      | idle m =>
          cases hP : P.action i l with
          | decide v => simp [composeAction, hP] at hact
          | invoke op' =>
              simp only [composeAction, hP] at hact
              cases hact
              have same := noop.2 _ _ _ hf
              subst same
              simp only [qChoice, qEvent, hP, composeNext]
              have idle : (proj C).loc i = .idle m := by rw [locC, hC]
              convert Step.invoke (I := I) (C := proj C) (i := i) (m := m) op' idle using 1
              refine Implementation.Config.ext rfl (funext fun j => ?_)
              by_cases hj : j = i
              · subst hj; simp
              · simp [Function.update_of_ne hj, proj]
      | busy w =>
          cases hI : I.move i w with
          | call a =>
              simp only [composeAction, hI] at hact
              cases hact
              simp only [qChoice, qEvent, hI, composeNext]
              have busyC : (proj C).loc i = .busy w := by rw [locC, hC]
              convert Step.call (I := I) (C := proj C) (i := i) (w := w) (a := op) (s := s) (r := r)
                busyC hI hf using 1
              refine Implementation.Config.ext rfl (funext fun j => ?_)
              by_cases hj : j = i
              · subst hj; simp
              · simp [Function.update_of_ne hj, proj]
          | ret r' m =>
              simp only [composeAction, hI] at hact
              cases hact
              have same := noop.2 _ _ _ hf
              subst same
              simp only [qChoice, qEvent, hI, composeNext]
              have busyC : (proj C).loc i = .busy w := by rw [locC, hC]
              convert Step.ret (I := I) (C := proj C) (i := i) (w := w) busyC hI using 1
              refine Implementation.Config.ext rfl (funext fun j => ?_)
              by_cases hj : j = i
              · subst hj; simp
              · simp [Function.update_of_ne hj, proj]
  | @waits op hact never =>
      change composeAction P I a₀ i (C.loc i) = _ at hact
      have locC : ∀ j, (proj C).loc j = (C.loc j).2 := fun j => rfl
      rcases hC : C.loc i with ⟨l, st⟩
      rw [hC] at hact
      cases st with
      | idle m =>
          cases hP : P.action i l with
          | decide v => simp [composeAction, hP] at hact
          | invoke op' =>
              simp only [composeAction, hP] at hact
              cases hact
              obtain ⟨r, hr⟩ := noop.1 C.obj
              exact absurd hr (never _ _)
      | busy w =>
          cases hI : I.move i w with
          | call a =>
              simp only [composeAction, hI] at hact
              cases hact
              simp only [qChoice, qEvent, hI]
              have busyC : (proj C).loc i = .busy w := by rw [locC, hC]
              exact Step.wait busyC hI never
          | ret r' m =>
              simp only [composeAction, hI] at hact
              cases hact
              obtain ⟨r, hr⟩ := noop.1 C.obj
              exact absurd hr (never _ _)

variable (P I) in
/-- What the history of the implementation shows inside the composed protocol: each process's
`Y`-part is its client state, and the history is consistent. -/
def QInv (x : Fin n → V) (C : (compose P I a₀).Config) (h : List (Event n Y.Op Y.Res)) : Prop :=
  (∀ j, (C.loc j).1 = client P x j h) ∧ Consistent P x h

theorem qinv_step (noop : NoOp X a₀) {x : Fin n → V} {C D : (compose P I a₀).Config} {i : Fin n}
    {h : List (Event n Y.Op Y.Res)} (qinv : QInv P I x C h) (step : (compose P I a₀).Step C i D) :
    QInv P I x D (h ++ (qEvent P I i (C.loc i)).toList) := by
  obtain ⟨clients, cons⟩ := qinv
  cases step with
  | @decided v hd =>
      obtain ⟨m, h2, h1⟩ := compose_decision (Protocol.decision_eq_some_iff.mpr hd)
      have event : qEvent P I i (C.loc i) = none := by
        rcases hC : C.loc i with ⟨l, st⟩
        rw [hC] at h1 h2; simp only at h1 h2; subst h2; simp [qEvent, h1]
      rw [event, Option.toList_none, List.append_nil]
      exact ⟨clients, cons⟩
  | @fires op s r hact hf =>
      change composeAction P I a₀ i (C.loc i) = _ at hact
      have ci := clients i
      rcases hC : C.loc i with ⟨l, st⟩
      rw [hC] at hact ci
      simp only at ci
      subst ci
      have locD : ∀ j, Function.update C.loc i (composeNext P I i (client P x i h, st) r) j =
          if j = i then composeNext P I i (client P x i h, st) r else C.loc j :=
        fun j => Function.update_apply _ _ _ _
      cases st with
      | idle m =>
          cases hP : P.action i (client P x i h) with
          | decide v => simp [composeAction, hP] at hact
          | invoke op' =>
              have event : qEvent P I i (client P x i h, .idle m) = some (.invoke i op') := by
                simp [qEvent, hP]
              rw [event]
              rw [Option.toList_some]
              refine ⟨fun j => ?_, consistent_snoc cons fun j' op'' he => ?_⟩
              · show (Function.update C.loc i (composeNext P I i (client P x i h, .idle m) r) j).1 = _
                rw [locD, client_snoc]
                by_cases hj : j = i
                · subst hj; simp [composeNext, hP, clientStep]
                · rw [if_neg hj, clients j]; rfl
              · simp only [Event.invoke.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                exact hP
      | busy w =>
          cases hI : I.move i w with
          | call a =>
              have event : qEvent P I i (client P x i h, .busy w) = none := by simp [qEvent, hI]
              rw [event, Option.toList_none, List.append_nil]
              refine ⟨fun j => ?_, cons⟩
              show (Function.update C.loc i (composeNext P I i (client P x i h, .busy w) r) j).1 = _
              rw [locD]
              by_cases hj : j = i
              · subst hj; simp [composeNext, hI]
              · rw [if_neg hj, clients j]
          | ret r' m =>
              have event : qEvent P I i (client P x i h, .busy w) = some (.respond i r') := by
                simp [qEvent, hI]
              rw [event]
              rw [Option.toList_some]
              refine ⟨fun j => ?_, consistent_snoc cons fun j' op'' he => by cases he⟩
              show (Function.update C.loc i (composeNext P I i (client P x i h, .busy w) r) j).1 = _
              rw [locD, client_snoc]
              by_cases hj : j = i
              · subst hj; simp [composeNext, hI, clientStep]
              · rw [if_neg hj, clients j]; simp [clientStep, Ne.symm hj]
  | @waits op hact never =>
      change composeAction P I a₀ i (C.loc i) = _ at hact
      rcases hC : C.loc i with ⟨l, st⟩
      rw [hC] at hact
      cases st with
      | idle m =>
          cases hP : P.action i l with
          | decide v => simp [composeAction, hP] at hact
          | invoke op' =>
              simp only [composeAction, hP] at hact
              cases hact
              obtain ⟨r, hr⟩ := noop.1 C.obj
              exact absurd hr (never _ _)
      | busy w =>
          cases hI : I.move i w with
          | call a =>
              have event : qEvent P I i (l, .busy w) = none := by simp [qEvent, hI]
              rw [event, Option.toList_none, List.append_nil]
              exact ⟨clients, cons⟩
          | ret r' m =>
              simp only [composeAction, hI] at hact
              cases hact
              obtain ⟨r, hr⟩ := noop.1 C.obj
              exact absurd hr (never _ _)

theorem compose_run (noop : NoOp X a₀) {x : Fin n → V} {C D : (compose P I a₀).Config}
    {σ : List (Fin n)} {cs₀ : List (Choice n Y.Op)} {h₀ : List (Event n Y.Op Y.Res)}
    (runI : I.Run I.initial cs₀ h₀ (proj C)) (qinv : QInv P I x C h₀)
    (run : (compose P I a₀).Run C σ D) :
    ∃ cs h, I.Run I.initial cs h (proj D) ∧ QInv P I x D h := by
  induction σ generalizing C cs₀ h₀ with
  | nil => rw [run]; exact ⟨cs₀, h₀, runI, qinv⟩
  | cons i σ ih =>
      obtain ⟨E, step, rest⟩ := run
      exact ih (run_append runI (run_single (compose_step noop step))) (qinv_step noop qinv step) rest

theorem qinv_initial (x : Fin n → V) : QInv P I x ((compose P I a₀).initial x) [] :=
  ⟨fun _ => rfl, consistent_nil⟩

/-- **Every reachable configuration of the composed protocol is mirrored by a reachable
configuration of the protocol over `Y`** in which the processes that decided decided the same. -/
theorem compose_mirror (lin : I.Linearizable P.init) (noop : NoOp X a₀) {x : Fin n → V}
    {C : (compose P I a₀).Config} (reach : (compose P I a₀).Reach x C) :
    ∃ D', P.Reach x D' ∧ ∀ i v, (compose P I a₀).decision C i = some v →
      P.decision D' i = some v := by
  obtain ⟨σ, runQ⟩ := reach
  obtain ⟨cs, h, runI, qinv⟩ := compose_run noop (cs₀ := []) (h₀ := []) (run_nil _)
    (qinv_initial x) runQ
  obtain ⟨acs, A', arun⟩ := lin h ⟨cs, _, runI⟩
  have rel0 : ReplayRel (P := P) (x := x) [] (atomic Y P.init n).initial (P.initial x) :=
    ⟨rfl, fun j => rfl⟩
  obtain ⟨σ', -, rel', -⟩ := replay_atomic (pre := []) (by simpa using qinv.2) rel0 arun
  refine ⟨P.run (P.initial x) σ', Protocol.reach_iff.mpr ⟨σ', rfl⟩, fun i v hv => ?_⟩
  obtain ⟨m, h2, h1⟩ := compose_decision hv
  have busyI := run_isBusy runI i
  have busyA := run_isBusy arun i
  have closed : openAfter i false h = false := by
    have : isBusy ((proj C).loc i) = false := by
      show isBusy (C.loc i).2 = false; rw [h2]; rfl
    rw [this] at busyI; exact busyI.symm
  obtain ⟨u, hu⟩ : ∃ u, A'.loc i = .idle u := by
    have : isBusy (A'.loc i) = false := by rw [busyA]; exact closed
    cases hA : A'.loc i with
    | idle u => exact ⟨u, rfl⟩
    | busy w => rw [hA] at this; cases this
  have loc := rel'.2 i
  rw [hu] at loc
  change (P.run (P.initial x) σ').loc i = client P x i ([] ++ h) at loc
  apply Protocol.decision_eq_some_iff.mpr
  rw [loc, List.nil_append, ← qinv.1 i]
  exact h1

/-- The history shown by the first `m` steps of an execution of the composed protocol. -/
def qHist (σ : ℕ → Fin n) (c : ℕ → (compose P I a₀).Config) : ℕ → List (Event n Y.Op Y.Res)
  | 0 => []
  | m + 1 => qHist σ c m ++ (qEvent P I (σ m) ((c m).loc (σ m))).toList

/-- The implementation's choices for the first `m` steps. -/
def qChoices (σ : ℕ → Fin n) (c : ℕ → (compose P I a₀).Config) : ℕ → List (Choice n Y.Op)
  | 0 => []
  | m + 1 => qChoices σ c m ++ [qChoice P I (σ m) ((c m).loc (σ m))]

theorem qHist_run (noop : NoOp X a₀) {x : Fin n → V} {σ : ℕ → Fin n}
    {c : ℕ → (compose P I a₀).Config} (start : c 0 = (compose P I a₀).initial x)
    (exec : (compose P I a₀).Execution σ c) :
    ∀ m, I.Run I.initial (qChoices σ c m) (qHist σ c m) (proj (c m)) ∧
      QInv P I x (c m) (qHist σ c m) := by
  intro m
  induction m with
  | zero => rw [start]; exact ⟨run_nil _, qinv_initial x⟩
  | succ m ih =>
      obtain ⟨run, qinv⟩ := ih
      exact ⟨run_append run (run_single (compose_step noop (exec m))), qinv_step noop qinv (exec m)⟩

theorem qHist_prefix {σ : ℕ → Fin n} {c : ℕ → (compose P I a₀).Config} {m m' : ℕ} (le : m ≤ m') :
    ∃ seg, qHist σ c m' = qHist σ c m ++ seg := by
  induction m' with
  | zero => obtain rfl : m = 0 := by omega
            exact ⟨[], by simp⟩
  | succ m' ih =>
      rcases Nat.lt_or_ge m (m' + 1) with lt | ge
      · obtain ⟨seg, hseg⟩ := ih (by omega)
        exact ⟨seg ++ _, by rw [qHist, hseg, List.append_assoc]⟩
      · obtain rfl : m = m' + 1 := by omega
        exact ⟨[], by simp⟩

/-- **The composed protocol solves consensus.** -/
theorem compose_solves (S : P.Solves) (lin : I.Linearizable P.init) (wf : I.WaitFree)
    (noop : NoOp X a₀) : (compose P I a₀).Solves := by
  refine ⟨?_, ?_, ?_⟩
  · intro x C reach i j v w hv hw
    obtain ⟨D', reach', mirror⟩ := compose_mirror lin noop reach
    exact S.agreement x D' reach' i j v w (mirror i v hv) (mirror j w hw)
  · intro x C reach i v hv
    obtain ⟨D', reach', mirror⟩ := compose_mirror lin noop reach
    exact S.validity x D' reach' i v (mirror i v hv)
  · intro x σ c start exec i often
    by_contra never
    have undecided : ∀ m, (compose P I a₀).decision (c m) i = none := fun m => by
      cases hm : (compose P I a₀).decision (c m) i with
      | none => rfl
      | some v => exact absurd ⟨m, by rw [hm]; rfl⟩ never
    have runs := qHist_run noop start exec
    -- the implementation's execution inside
    have execI : I.Execution (fun m => qChoice P I (σ m) ((c m).loc (σ m))) (fun m => proj (c m)) :=
      fun m => ⟨_, compose_step noop (exec m)⟩
    have startI : proj (c 0) = I.initial := by rw [start]; rfl
    -- a process's status changes only at its own steps
    have frozen : ∀ t, σ t ≠ i → (c (t + 1)).loc i = (c t).loc i :=
      fun t ht => (exec t).loc_of_ne (Ne.symm ht)
    have frozenFrom : ∀ t d, (∀ d', d' < d → σ (t + d') ≠ i) → (c (t + d)).loc i = (c t).loc i := by
      intro t d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
          intro none'
          rw [← add_assoc, frozen _ (none' d (by omega)), ih (fun d' lt => none' d' (by omega))]
    -- at its next step, an idle process starts an operation
    have busySoon : ∀ m₀, ∃ m₁, m₀ ≤ m₁ ∧ ∃ w, ((c m₁).loc i).2 = .busy w := by
      intro m₀
      obtain ⟨k, hk, hσ⟩ := often m₀
      rcases hst : ((c k).loc i).2 with m | w
      · cases hP : P.action i ((c k).loc i).1 with
        | decide v =>
            exact absurd (compose_decision_of hst hP) (by rw [undecided k]; simp)
        | invoke op =>
            refine ⟨k + 1, by omega, I.begin i m op, ?_⟩
            have step := exec k
            rw [hσ] at step
            have act : (compose P I a₀).action i ((c k).loc i) = .invoke a₀ := by
              show composeAction P I a₀ i ((c k).loc i) = _
              rcases hC : (c k).loc i with ⟨l, st⟩
              rw [hC] at hst hP; simp only at hst hP; subst hst
              simp [composeAction, hP]
            generalize hnext : c (k + 1) = D at step ⊢
            cases step with
            | @decided v hd => rw [act] at hd; cases hd
            | @fires op' s r hact hf =>
                simp only [Function.update_self]
                show (composeNext P I i ((c k).loc i) r).2 = _
                rcases hC : (c k).loc i with ⟨l, st⟩
                rw [hC] at hst hP; simp only at hst hP; subst hst
                simp [composeNext, hP]
            | @waits op' hact never' =>
                rw [act] at hact; cases hact
                obtain ⟨r, hr⟩ := noop.1 (c k).obj
                exact absurd hr (never' _ _)
      · exact ⟨k, hk, w, hst⟩
    -- it is moved infinitely often
    have movesOften : ∀ N, ∃ k, N ≤ k ∧ qChoice P I (σ k) ((c k).loc (σ k)) = .move i := by
      intro N
      obtain ⟨m₁, hm₁, w, hw⟩ := busySoon N
      classical
      have ex : ∃ d, σ (m₁ + d) = i := by
        obtain ⟨k, hk, hσ⟩ := often m₁
        exact ⟨k - m₁, by rw [Nat.add_sub_cancel' hk]; exact hσ⟩
      have hd := Nat.find_spec ex
      have same := frozenFrom m₁ (Nat.find ex) (fun d' lt => Nat.find_min ex lt)
      refine ⟨m₁ + Nat.find ex, by omega, ?_⟩
      rw [hd, same]
      rcases hC : (c m₁).loc i with ⟨l, st⟩
      rw [hC] at hw; simp only at hw; subst hw
      rfl
    -- so it completes more and more operations
    have more : ∀ N, ∃ m, N ≤ respCount i (qHist σ c m) := by
      intro N
      induction N with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ N ih =>
          obtain ⟨m₀, hm₀⟩ := ih
          obtain ⟨m₁, hm₁, w, hw⟩ := busySoon m₀
          obtain ⟨m₂, hm₂, notBusy⟩ := wf _ _ startI execI i m₁ ⟨w, hw⟩ movesOften
          have init : isBusy (I.initial.loc i) = false := rfl
          have open₁ : openAfter i false (qHist σ c m₁) = true := by
            have := run_isBusy (runs m₁).1 i
            rw [init] at this
            rw [← this]; show isBusy ((c m₁).loc i).2 = true; rw [hw]; rfl
          have closed₂ : openAfter i false (qHist σ c m₂) = false := by
            have := run_isBusy (runs m₂).1 i
            rw [init] at this
            rw [← this]
            cases hst : (proj (c m₂)).loc i with
            | idle u => rfl
            | busy w' => exact absurd ⟨w', hst⟩ notBusy
          obtain ⟨seg, hseg⟩ := qHist_prefix (σ := σ) (c := c) hm₂
          rw [hseg, openAfter_append, open₁] at closed₂
          have pos := respCount_pos_of_closed i seg closed₂
          obtain ⟨seg₀, hseg₀⟩ := qHist_prefix (σ := σ) (c := c) hm₁
          refine ⟨m₂, ?_⟩
          rw [hseg, respCount_append, hseg₀, respCount_append]
          omega
    -- but a long enough history replays as an effective run longer than the bound
    obtain ⟨B, hB⟩ := S.bounded x
    obtain ⟨m, hm⟩ := more (B + 1)
    obtain ⟨acs, A', arun⟩ := lin _ ⟨_, _, (runs m).1⟩
    have rel0 : ReplayRel (P := P) (x := x) [] (atomic Y P.init n).initial (P.initial x) :=
      ⟨rfl, fun j => rfl⟩
    obtain ⟨σ', eff, -, counts⟩ := replay_atomic (pre := []) (by simpa using (runs m).2.2) rel0 arun
    have count := counts i
    have flag : doneFlag ((atomic Y P.init n).initial.loc i) = 0 := rfl
    rw [flag, add_zero] at count
    have len := hB σ' eff
    have le := List.count_le_length (a := i) (l := σ')
    omega

end Compose

/-! ## The hierarchy theorem -/

section Hierarchy

variable {X : ObjectType} {Y : DetObject} {n : ℕ} {V : Type} {a₀ : X.Op}

/-- **The hierarchy theorem.** If `X` has an operation that changes nothing, `X` implements `Y`
started at `s₀` for `n` processes, and a protocol over `Y` started at `s₀` solves `n`-process
consensus, then `X` solves `n`-process consensus. -/
theorem solvable_of_implements (noop : NoOp X a₀) {P : Protocol Y.toObject n V} (S : P.Solves)
    (impl : Implements X Y P.init n) : Solvable X n V := by
  obtain ⟨I, lin, wf⟩ := impl
  exact ⟨compose P I a₀, compose_solves S lin wf noop⟩

/-- The same, for an implementation from every state: if `X` implements `Y` and `Y` solves
`n`-process consensus, so does `X`. -/
theorem solvable_of_implements_all (noop : NoOp X a₀) (impl : ∀ s₀, Implements X Y s₀ n)
    (solvable : Solvable Y.toObject n V) : Solvable X n V := by
  obtain ⟨P, S⟩ := solvable
  exact solvable_of_implements noop S (impl P.init)

/-- **An object cannot implement one of a higher consensus number**: if `X` has consensus number
`m`, `Y` has consensus number `k`, and `m < n ≤ k`, then `X` does not implement `Y` for `n`
processes. -/
theorem not_implements_of_consensusNumber (noop : NoOp X a₀) {m k : ℕ∞}
    (hX : HasConsensusNumber X m) (hY : HasConsensusNumber Y.toObject k) (hm : m < n)
    (hk : (n : ℕ∞) ≤ k) : ¬ ∀ s₀, Implements X Y s₀ n := by
  intro impl
  have := (hX n).mp (solvable_of_implements_all noop impl ((hY n).mpr hk))
  exact absurd this (not_le.mpr hm)

end Hierarchy

end Mettapedia.GSLT.Coordination.ConsensusNumbers
