import Mettapedia.Machines.CMemory.PermissionFlow

/-!
# Plans checked in segments

`check` runs a plan from a state. A plan whose spine (its `step`s and the `next` of its branches and
loops) is cut into segments is checked segment after segment: `check_seq` says that checking
`seq a b` is checking `a`, then checking `b` from each normal exit of `a`, with the other exits of `a`
passed through. A long plan can therefore be decided one segment at a time, each from its own start
state, and the results composed by this lemma instead of by one large computation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.PermissionFlow

universe u v

variable {State : Type v} {Action : Type u}

/-- `a` continued by `b` where `a`'s spine ends (`done`). The arms of a branch and the body of a loop
are not the spine: their `done` ends the arm or the iteration, as in `check`. -/
def seq : Plan Action → Plan Action → Plan Action
  | .done, b => b
  | .step action next, b => .step action (seq next b)
  | .ret, _ => .ret
  | .breakLoop, _ => .breakLoop
  | .continueLoop, _ => .continueLoop
  | .branch yes no next, b => .branch yes no (seq next b)
  | .loop body next, b => .loop body (seq next b)

theorem continue_nil (run : State → Option (List (Exit State))) : continueExits run [] = some [] := rfl

theorem continue_append (run : State → Option (List (Exit State))) (xs ys : List (Exit State)) :
    continueExits run (xs ++ ys) =
      (continueExits run xs).bind fun a => (continueExits run ys).bind fun b => some (a ++ b) := by
  induction xs with
  | nil => simp [continueExits]
  | cons x xs ih =>
      simp only [List.cons_append, continueExits, ih, Option.bind_assoc]
      congr 1; funext before
      cases continueExits run xs <;> simp only [Option.bind_none, Option.bind_some]
      cases continueExits run ys <;> simp [List.append_assoc]

/-- An exit that is not normal passes through a continuation unchanged. -/
theorem continue_abrupt_single (run : State → Option (List (Exit State))) {e : Exit State}
    (abrupt : e.kind ≠ .normal) : continueExits run [e] = some [e] := by
  have : (e.kind == .normal) = false := by simpa using abrupt
  simp [continueExits, this]

/-- Exits none of which is normal pass through a continuation unchanged. -/
theorem continue_abrupt_all (run : State → Option (List (Exit State))) {es : List (Exit State)}
    (abrupt : ∀ e ∈ es, e.kind ≠ .normal) : continueExits run es = some es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      have h1 := continue_abrupt_single run (abrupt e (by simp))
      have h2 := ih (fun x mem => abrupt x (by simp [mem]))
      have : (e.kind == .normal) = false := by simpa using abrupt e (by simp)
      simp [continueExits, this, h2]

/-- A normal exit whose continuation was decided: its results precede those of the later exits. -/
theorem continue_normal_eq {run : State → Option (List (Exit State))} {s : State}
    {rest before : List (Exit State)} {after : Option (List (Exit State))}
    (continued : run s = some before) (later : continueExits run rest = after) :
    continueExits run (⟨.normal, s⟩ :: rest) = after.bind fun more => some (before ++ more) := by
  change (run s).bind (fun before => (continueExits run rest).bind
    fun after => some (before ++ after)) = _
  rw [continued, later]
  rfl

/-- A normal exit whose continuation fails fails the whole continuation. -/
theorem continue_normal_none {run : State → Option (List (Exit State))} {s : State}
    {rest : List (Exit State)} (continued : run s = none) :
    continueExits run (⟨.normal, s⟩ :: rest) = none := by
  change (run s).bind (fun before => (continueExits run rest).bind
    fun after => some (before ++ after)) = _
  rw [continued]
  rfl

/-- An exit that is not normal stays in place, before the results of the later exits. -/
theorem continue_abrupt_eq {run : State → Option (List (Exit State))} {e : Exit State}
    {rest : List (Exit State)} {after : Option (List (Exit State))}
    (abrupt : e.kind ≠ .normal) (later : continueExits run rest = after) :
    continueExits run (e :: rest) = after.bind fun more => some (e :: more) := by
  have passed : (e.kind == .normal) = false := by simpa using abrupt
  change (if e.kind == .normal then run e.state else some [e]).bind (fun before =>
    (continueExits run rest).bind fun after => some (before ++ after)) = _
  rw [passed, later]
  rfl

/-- Continuing with `f` then with `g` is continuing with "`f`, then continuing with `g`". -/
theorem continue_continue (f g : State → Option (List (Exit State))) (es : List (Exit State)) :
    continueExits (fun s => (f s).bind (continueExits g)) es =
      (continueExits f es).bind (continueExits g) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [continueExits]
      by_cases normal : (e.kind == .normal) = true
      · simp only [normal, if_true, Option.bind_assoc]
        cases f e.state with
        | none => rfl
        | some before =>
            simp only [Option.bind_some, ih, Option.bind_assoc]
            cases continueExits f es with
            | none =>
                cases continueExits g before <;> rfl
            | some after =>
                simp only [Option.bind_some, continue_append]
      · have abrupt : e.kind ≠ .normal := by simpa using normal
        simp only [normal, Bool.false_eq_true, if_false, Option.bind_some, ih, Option.bind_assoc]
        cases continueExits f es with
        | none => rfl
        | some after =>
            simp only [Option.bind_some]
            rw [show [e] ++ after = [e] ++ after from rfl, continue_append,
              continue_abrupt_single g abrupt]
            simp

variable [BEq State] [LawfulBEq State] {transition : State → Action → Option State}
    {returnAllowed : State → Bool}

/-- `check` of a branch, with its `do` block written as `Option.bind`. -/
theorem check_branch_eq (yes no next : Plan Action) (s : State) :
    check transition returnAllowed (.branch yes no next) s =
      (check transition returnAllowed yes s).bind fun left =>
        (check transition returnAllowed no s).bind fun right =>
          continueExits (check transition returnAllowed next) (left ++ right).eraseDups := rfl

/-- `check` of a loop, with its `do` block written as `Option.bind`. -/
theorem check_loop_eq (body next : Plan Action) (s : State) :
    check transition returnAllowed (.loop body next) s =
      (check transition returnAllowed body s).bind fun iterations =>
        if iterations.all (fun exit => exit.kind == .returned || exit.state == s) then
          (check transition returnAllowed next s).bind fun after =>
            some (iterations.filter (fun exit => exit.kind == .returned) ++ after)
        else none := rfl

/-- Checking `seq a b` is checking `a`, then `b` from each normal exit of `a`. -/
theorem check_seq (a b : Plan Action) (s : State) :
    check transition returnAllowed (seq a b) s =
      (check transition returnAllowed a s).bind (continueExits (check transition returnAllowed b)) := by
  induction a generalizing s with
  | done =>
      simp only [seq, check, Option.bind_some, continueExits]
      cases check transition returnAllowed b s <;> simp
  | step action next ih =>
      simp only [seq, check, Option.bind_assoc, ih]
  | ret =>
      simp only [seq, check]
      split
      · simp [continueExits]
      · rfl
  | breakLoop => simp [seq, check, continueExits]
  | continueLoop => simp [seq, check, continueExits]
  | branch yes no next _ _ ihn =>
      have continued : check transition returnAllowed (seq next b) =
          fun x => (check transition returnAllowed next x).bind
            (continueExits (check transition returnAllowed b)) := funext ihn
      rw [show seq (.branch yes no next) b = .branch yes no (seq next b) from rfl,
        check_branch_eq, check_branch_eq, Option.bind_assoc, continued]
      congr 1; funext left
      rw [Option.bind_assoc]
      congr 1; funext right
      exact continue_continue _ _ _
  | loop body next _ ihn =>
      rw [show seq (.loop body next) b = .loop body (seq next b) from rfl,
        check_loop_eq, check_loop_eq, Option.bind_assoc]
      congr 1; funext iterations
      split
      · rw [ihn s, Option.bind_assoc]
        cases check transition returnAllowed next s with
        | none => rfl
        | some after =>
            simp only [Option.bind_some]
            have abrupt : ∀ e ∈ iterations.filter (fun exit => exit.kind == .returned),
                e.kind ≠ .normal := by
              intro e mem
              have returned := (List.mem_filter.mp mem).2
              simp only [beq_iff_eq] at returned
              simp [returned]
            rw [continue_append, continue_abrupt_all _ abrupt]
            simp
      · rfl

/-! ## Deciding a plan by its cuts

A segment decided from a literal state has literal exits. The lemmas below rewrite the check of a
composed plan into the exits of its first segment, and `continue_normal_eq`, `continue_normal_none`
and `continue_abrupt_eq` carry those exits through the rest. A long plan is then decided by the
separate checks of its segments, each from the state its predecessor reached, and never by one
computation along the whole plan. A composition is built from these equations alone, so checking it
never runs a segment again. -/

/-- The checked exits of `seq a b`, from the exits of `a`. -/
theorem check_seq_of {a b : Plan Action} {s : State} {exits : List (Exit State)}
    (cut : check transition returnAllowed a s = some exits) :
    check transition returnAllowed (seq a b) s =
      continueExits (check transition returnAllowed b) exits := by
  rw [check_seq, cut, Option.bind_some]

/-- A segment that fails fails the whole composition. -/
theorem check_seq_none {a b : Plan Action} {s : State}
    (cut : check transition returnAllowed a s = none) :
    check transition returnAllowed (seq a b) s = none := by
  rw [check_seq, cut, Option.bind_none]

namespace Controls

private def mark (state : List Nat) (event : Nat) : Option (List Nat) := some (state ++ [event])
private def fresh (state : List Nat) (event : Nat) : Option (List Nat) :=
  if event ∈ state then none else some (state ++ [event])
private def split : Plan Nat := .branch (.step 1 .done) (.step 2 .done) .done

-- A cut with two normal exits: the next segment continues from each of them.
example : check mark (fun _ => true) (seq split (.step 3 .ret)) [] =
    some [⟨.returned, [1, 3]⟩, ⟨.returned, [2, 3]⟩] :=
  have first : check mark (fun _ => true) split [] = some [⟨.normal, [1]⟩, ⟨.normal, [2]⟩] := by
    decide
  have left : check mark (fun _ => true) (.step 3 .ret) [1] = some [⟨.returned, [1, 3]⟩] := by
    decide
  have right : check mark (fun _ => true) (.step 3 .ret) [2] = some [⟨.returned, [2, 3]⟩] := by
    decide
  (check_seq_of first).trans (continue_normal_eq left (continue_normal_eq right (continue_nil _)))

-- A return at the cut passes through; the normal exit after it is continued.
example : check mark (fun _ => true) (seq (.branch .ret (.step 1 .done) .done) (.step 3 .ret)) [] =
    some [⟨.returned, []⟩, ⟨.returned, [1, 3]⟩] :=
  have first : check mark (fun _ => true) (.branch .ret (.step 1 .done) .done) [] =
      some [⟨.returned, []⟩, ⟨.normal, [1]⟩] := by decide
  have later : check mark (fun _ => true) (.step 3 .ret) [1] = some [⟨.returned, [1, 3]⟩] := by
    decide
  (check_seq_of first).trans
    (continue_abrupt_eq (by decide) (continue_normal_eq later (continue_nil _)))

-- The next segment refused from one of the two exits refuses the whole plan.
example : check fresh (fun _ => true) (seq split (.step 2 .ret)) [] = none :=
  have first : check fresh (fun _ => true) split [] = some [⟨.normal, [1]⟩, ⟨.normal, [2]⟩] := by
    decide
  have left : check fresh (fun _ => true) (.step 2 .ret) [1] = some [⟨.returned, [1, 2]⟩] := by
    decide
  have right : check fresh (fun _ => true) (.step 2 .ret) [2] = none := by decide
  (check_seq_of first).trans (continue_normal_eq left (continue_normal_none right))

-- A refused first segment refuses the composition, whatever follows.
example : check fresh (fun _ => true) (seq (.step 1 (.step 1 .done)) (.step 3 .ret)) [] = none :=
  check_seq_none (by decide)

end Controls

end Mettapedia.Machines.CMemory.PermissionFlow
