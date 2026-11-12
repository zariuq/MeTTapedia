import Mathlib.Tactic

/-!
# Entry-view and when-reached source reads

Two independent deterministic finite nested-loop algorithms model an incoming
read, one local computation, a right source read, and an answer/caller action.
The entry-view loop retains the initial right rows. The when-reached loop opens
each right reader after its local computation. Once opened, either right reader
retains that call's row list while its caller performs effects.

Their coincidence law requires stability of the logical read region under
both the local computation and the body/caller. Arbitrary effects on the other
state field remain permitted. This is sufficient, not necessary, and concerns
these finite one-result computations/bodies, not arbitrary nondeterminism,
errors, concurrency or current-presence validation of captured read rows.
Logical row stability does not require physical storage/index immutability.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetReadViewCoincidence

variable {Prefix Row Other Value Answer : Type}

structure State (Row Other : Type) where
  rightRows : List Row
  other : Other
  deriving DecidableEq, Repr

abbrev Evaluate (Prefix Row Other Value : Type) :=
  Prefix → State Row Other → Value × State Row Other

abbrev Body (Prefix Row Other Value Answer : Type) :=
  Prefix → Value → Row → State Row Other → Answer × State Row Other

def scanRight (body : Body Prefix Row Other Value Answer) (incoming : Prefix) (value : Value) :
    List Row → State Row Other → List Answer × State Row Other
  | [], world => ([], world)
  | row :: later, world =>
      let answered := body incoming value row world
      let rest := scanRight body incoming value later answered.2
      (answered.1 :: rest.1, rest.2)

def entryLoop (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer) (captured : List Row) :
    List Prefix → State Row Other → List Answer × State Row Other
  | [], world => ([], world)
  | incoming :: later, world =>
      let computed := evaluate incoming world
      let first := scanRight body incoming computed.1 captured computed.2
      let rest := entryLoop evaluate body captured later first.2
      (first.1 ++ rest.1, rest.2)

def reachedLoop (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer) :
    List Prefix → State Row Other → List Answer × State Row Other
  | [], world => ([], world)
  | incoming :: later, world =>
      let computed := evaluate incoming world
      let first := scanRight body incoming computed.1 computed.2.rightRows computed.2
      let rest := reachedLoop evaluate body later first.2
      (first.1 ++ rest.1, rest.2)

def entryView (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer) (prefixes : List Prefix) (world : State Row Other) :
    List Answer × State Row Other := entryLoop evaluate body world.rightRows prefixes world

theorem scan_preserves_right (body : Body Prefix Row Other Value Answer)
    (stable : ∀ incoming value row world, (body incoming value row world).2.rightRows = world.rightRows)
    (incoming : Prefix) (value : Value) (rows : List Row) (world : State Row Other) :
    (scanRight body incoming value rows world).2.rightRows = world.rightRows := by
  induction rows generalizing world with
  | nil => rfl
  | cons row later ih =>
      exact (ih (body incoming value row world).2).trans (stable incoming value row world)

/-- Both local clauses are discharged on actual primitive actions. No final
answer or whole-program equivalence is assumed. Caller writes are included. -/
theorem loops_coincide (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer)
    (evaluateStable : ∀ incoming world, (evaluate incoming world).2.rightRows = world.rightRows)
    (bodyStable : ∀ incoming value row world, (body incoming value row world).2.rightRows = world.rightRows)
    (captured : List Row) (prefixes : List Prefix) (world : State Row Other)
    (sameView : world.rightRows = captured) :
    entryLoop evaluate body captured prefixes world = reachedLoop evaluate body prefixes world := by
  induction prefixes generalizing world with
  | nil => rfl
  | cons incoming later ih =>
      have afterCompute : (evaluate incoming world).2.rightRows = captured :=
        (evaluateStable incoming world).trans sameView
      let first := scanRight body incoming (evaluate incoming world).1 captured (evaluate incoming world).2
      have afterBody : first.2.rightRows = captured :=
        (scan_preserves_right body bodyStable incoming (evaluate incoming world).1 captured
          (evaluate incoming world).2).trans afterCompute
      have following := ih first.2 afterBody
      simpa only [entryLoop, reachedLoop, afterCompute] using
        congrArg (fun rest : List Answer × State Row Other => (first.1 ++ rest.1, rest.2)) following

theorem entry_reached_coincide (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer)
    (evaluateStable : ∀ incoming world, (evaluate incoming world).2.rightRows = world.rightRows)
    (bodyStable : ∀ incoming value row world, (body incoming value row world).2.rightRows = world.rightRows)
    (prefixes : List Prefix) (world : State Row Other) :
    entryView evaluate body prefixes world = reachedLoop evaluate body prefixes world :=
  loops_coincide evaluate body evaluateStable bodyStable world.rightRows prefixes world rfl

/-- A different source rewrite opens the multiplying read before evaluating
the local code, so that code now runs once for each right-row alternative. -/
def afterRight (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer) (incoming : Prefix) :
    List Row → State Row Other → List Answer × State Row Other
  | [], world => ([], world)
  | row :: later, world =>
      let computed := evaluate incoming world
      let answered := body incoming computed.1 row computed.2
      let rest := afterRight evaluate body incoming later answered.2
      (answered.1 :: rest.1, rest.2)

def movedLoop (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer) (captured : List Row) :
    List Prefix → State Row Other → List Answer × State Row Other
  | [], world => ([], world)
  | incoming :: later, world =>
      let first := afterRight evaluate body incoming captured world
      let rest := movedLoop evaluate body captured later first.2
      (first.1 ++ rest.1, rest.2)

def movedEntry (evaluate : Evaluate Prefix Row Other Value)
    (body : Body Prefix Row Other Value Answer) (prefixes : List Prefix) (world : State Row Other) :
    List Answer × State Row Other := movedLoop evaluate body world.rightRows prefixes world

def noop : Evaluate Nat Nat Nat Unit := fun _ world => ((), world)

def callerAdds : Body Nat Nat Nat Unit (Nat × Nat) := fun incoming _ row world =>
  ((incoming, row), ⟨if world.other = 0 then world.rightRows ++ [8] else world.rightRows, world.other + 1⟩)

def changingWorld : State Nat Nat := ⟨[7], 0⟩

example : (entryView noop callerAdds [0, 1] changingWorld).1 = [(0, 7), (1, 7)] ∧
    (entryView noop callerAdds [0, 1] changingWorld).2 = ⟨[7, 8], 2⟩ := by decide

example : (reachedLoop noop callerAdds [0, 1] changingWorld).1 = [(0, 7), (1, 7), (1, 8)] ∧
    (reachedLoop noop callerAdds [0, 1] changingWorld).2 = ⟨[7, 8], 3⟩ := by decide

/-- The local computation writes no source space at all; the caller still
invalidates the claimed unconditional coincidence of entry/reached views. -/
theorem no_local_write_is_insufficient :
    (∀ incoming world, (noop incoming world).2.rightRows = world.rightRows) ∧
      entryView noop callerAdds [0, 1] changingWorld ≠ reachedLoop noop callerAdds [0, 1] changingWorld := by
  constructor
  · intro incoming world; rfl
  · decide

def tick : Evaluate Nat Nat Nat Unit := fun _ world =>
  ((), { world with other := world.other + 1 })

def plainBody : Body Nat Nat Nat Unit (Nat × Nat) := fun incoming _ row world => ((incoming, row), world)
def stableWorld : State Nat Nat := ⟨[10, 20], 0⟩

example : (entryView tick plainBody [0, 1] stableWorld).1 =
    [(0, 10), (0, 20), (1, 10), (1, 20)] ∧
    (entryView tick plainBody [0, 1] stableWorld).2 = ⟨[10, 20], 2⟩ := by decide

example : (movedEntry tick plainBody [0, 1] stableWorld).1 =
    [(0, 10), (0, 20), (1, 10), (1, 20)] ∧
    (movedEntry tick plainBody [0, 1] stableWorld).2 = ⟨[10, 20], 4⟩ := by decide

/-- Source rows stay immutable in both programs, yet moving a multiplying
read before the effect duplicates its executions. -/
theorem frozen_sources_do_not_license_distribution :
    (∀ incoming world, (tick incoming world).2.rightRows = world.rightRows) ∧
      (∀ incoming value row world, (plainBody incoming value row world).2.rightRows = world.rightRows) ∧
      entryView tick plainBody [0, 1] stableWorld ≠ movedEntry tick plainBody [0, 1] stableWorld := by
  refine ⟨?_, ?_, ?_⟩
  · intro incoming world; rfl
  · intro incoming value row world; rfl
  · decide

/-- Nontrivial unrelated effects are allowed by the coincidence hypotheses. -/
example : entryView tick plainBody [0, 1] stableWorld = reachedLoop tick plainBody [0, 1] stableWorld :=
  entry_reached_coincide tick plainBody (fun _ _ => rfl) (fun _ _ _ _ => rfl) _ _

/-- The sufficient region-stability condition is not a necessary condition:
one final caller mutation has no later incoming whose view could distinguish it. -/
example : entryView noop callerAdds [0] changingWorld = reachedLoop noop callerAdds [0] changingWorld := by decide

end Mettapedia.Machines.Cursor.LetReadViewCoincidence
