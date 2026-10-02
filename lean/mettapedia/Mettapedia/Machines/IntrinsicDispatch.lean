import Mathlib.Data.List.Basic

/-! # Partial intrinsic dispatch

A registry entry in another language does not authorize an intrinsic here.
An unavailable intrinsic is distinct from a handled call with no answers.
This small dispatch model specifies that distinction; it does not verify a C
implementation or assume correctness of the intrinsic or host interpreter.
-/
set_option autoImplicit false
namespace Mettapedia.Machines.IntrinsicDispatch

variable {Query Answer : Type}

inductive Evaluates (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer) :
    Query → Answer → Prop
  | native {q answers a} : allowed q = true → native q = some answers →
      a ∈ answers → Evaluates allowed native host q a
  | unowned {q a} : allowed q = false → a ∈ host q →
      Evaluates allowed native host q a
  | unavailable {q a} : native q = none → a ∈ host q →
      Evaluates allowed native host q a

def run (allowed : Query → Bool) (native : Query → Option (List Answer))
    (host : Query → List Answer) (q : Query) : List Answer :=
  if allowed q then (native q).getD (host q) else host q

/-- Whole-answer semantics retains occurrences, including an empty handled
call. Declining an implementation is a separate semantic case. -/
inductive Answers (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer) :
    Query → List Answer → Prop
  | native {q xs} : allowed q = true → native q = some xs →
      Answers allowed native host q xs
  | unowned {q} : allowed q = false → Answers allowed native host q (host q)
  | unavailable {q} : native q = none → Answers allowed native host q (host q)

theorem run_eq_iff (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer)
    (q : Query) (xs : List Answer) :
    run allowed native host q = xs ↔ Answers allowed native host q xs := by
  constructor
  · intro h
    subst xs
    cases ha : allowed q with
    | false => simpa [run, ha] using Answers.unowned (native := native) (host := host) ha
    | true =>
      cases hn : native q with
      | none => simpa [run, ha, hn] using Answers.unavailable (allowed := allowed) (host := host) hn
      | some ys => simpa [run, ha, hn] using Answers.native (host := host) ha hn
  · intro h
    cases h with
    | native ha hn => simp [run, ha, hn]
    | unowned ha => simp [run, ha]
    | unavailable hn => cases ha : allowed q <;> simp [run, ha, hn]

theorem mem_run_iff (allowed : Query → Bool)
    (native : Query → Option (List Answer)) (host : Query → List Answer)
    (q : Query) (a : Answer) :
    a ∈ run allowed native host q ↔ Evaluates allowed native host q a := by
  constructor
  · intro h
    cases ha : allowed q with
    | false => exact .unowned ha (by simpa [run, ha] using h)
    | true =>
      cases hn : native q with
      | none => exact .unavailable hn (by simpa [run, ha, hn] using h)
      | some xs => exact .native ha hn (by simpa [run, ha, hn] using h)
  · intro h
    cases h with
    | native ha hn hm => simpa [run, ha, hn] using hm
    | unowned ha hm => simpa [run, ha] using hm
    | unavailable hn hm => cases ha : allowed q <;> simpa [run, ha, hn] using hm

-- A declined native division may have an ordinary user equation.
example : run (fun _ : Unit => true) (fun _ => none) (fun _ => [5, 5]) () =
    ([5, 5] : List Nat) := rfl

-- A genuine handled failure must not invoke those equations.
example : run (fun _ : Unit => true) (fun _ => some []) (fun _ => [5]) () =
    ([] : List Nat) := rfl

-- Global recognition of a name cannot override this language's ownership.
example : run (fun _ : Unit => false) (fun _ => some [0]) (fun _ => [5]) () ≠
    ([] : List Nat) := by decide

end Mettapedia.Machines.IntrinsicDispatch
