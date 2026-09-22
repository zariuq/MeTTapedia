import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Separation

/-!
# The gate and the distributor

These are the two pieces the reflective encoding of an input prefix is built
from, and between them they are the whole reason that encoding is linear.

## The gate

`gate` holds a continuation as *stored data* rather than as running code: a
synchroniser waits at the trigger subject, the continuation sits inside a
storage combinator, and an opener waits to run it.  `gate_releases` shows that
a message at the trigger releases the continuation in **three steps whatever
the continuation's size**, because what travels is a name.

This is the difference from an elimination without reflection.  Without a way
to store a continuation, "wait, then behave like `S`" has to be implemented by
rewriting `S` itself — splitting at every parallel composition and delaying
every atom — so a constant-factor expansion composes multiplicatively down a
chain of nested prefixes.  The gate pays a constant instead.

## The distributor

`distributor` is a chain of duplicators broadcasting one message from a subject
to several.  `distributor_broadcasts` shows a message at the chain's subject
reaches a message at every delivery subject, one step per duplicator, so its
cost is the number of occurrences rather than anything multiplicative.

Each chain entry names a target and the intermediate subject carrying the
remainder, which is exactly the shape the definition needs; `deliveries` reads
off the subjects reached, and an empty chain delivers at the original subject
with no atoms at all.

## Supporting laws

`Reaches.parRight` lifts reduction under the right of a parallel composition,
which the rules give only on the left, via commutativity.  `broadcast_cons`
and `deliveries_ne_nil` are the bookkeeping the broadcast induction needs.

## References

- N. Yoshida, *Minimality and separation results on asynchronous mobile
  processes*, TCS 274(1–2):231–276, 2002.
- F1R3FLY.io research note, *Name-Free Combinators for the Rho Calculus*,
  draft 3, 2026.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

theorem Reaches.single {p q : Comb} (h : StepMinus Cong p q) : Reaches p q :=
  Reaches.tail (Reaches.refl p) h

/-- Reduction under the left of a parallel composition. -/
theorem Reaches.parLeft {p p' : Comb} (r : Comb) (h : Reaches p p') :
    Reaches (par p r) (par p' r) := by
  induction h with
  | refl => exact Reaches.refl _
  | tail _ step ih => exact Reaches.tail ih (StepMinus.parLeft _ step)
  | congruent hc => exact Reaches.congruent (Cong.parLeft _ hc)
  | trans _ _ ih₁ ih₂ => exact Reaches.trans ih₁ ih₂

/-- Reduction under the right of a parallel composition, via commutativity. -/
theorem Reaches.parRight (p : Comb) {q q' : Comb} (h : Reaches q q') :
    Reaches (par p q) (par p q') := by
  induction h with
  | refl => exact Reaches.refl _
  | tail _ step ih =>
      exact Reaches.tail ih (StepMinus.congruent (Cong.parComm _ _)
        (StepMinus.parLeft _ step) (Cong.parComm _ _))
  | congruent hc => exact Reaches.congruent (Cong.parRight _ hc)
  | trans _ _ ih₁ ih₂ => exact Reaches.trans ih₁ ih₂

/-- Rotation of a three-way parallel composition. -/
theorem par_rotate' (x y z : Comb) : Cong (par (par x y) z) (par (par x z) y) :=
  Cong.trans (Cong.parAssoc x y z)
    (Cong.trans (Cong.parRight x (Cong.parComm y z))
      (Cong.symm (Cong.parAssoc x z y)))

/-- The gate: a synchroniser at the trigger subject, the continuation held as
stored data, and an opener waiting to run it.  The continuation travels as a
name, so the gate is three atoms whatever its size. -/
def gate (trigger store run continuation : Comb) : Comb :=
  par (sy trigger store run)
    (par (qq store continuation) (ev run))

/-- **The gate releases its continuation in three steps, whatever its size.**
This is the mechanism that makes prefix elimination linear: the continuation
is not rewritten into the body, it is stored and released. -/
theorem gate_releases (trigger store run continuation payload : Comb) :
    Reaches (par (gate trigger store run continuation) (mm trigger payload))
      continuation := by
  have first :
      StepMinus Cong (par (gate trigger store run continuation) (mm trigger payload))
        (par (fw store run) (par (qq store continuation) (ev run))) := by
    refine StepMinus.congruent
      (p' := par (par (sy trigger store run) (mm trigger payload))
        (par (qq store continuation) (ev run)))
      (q' := par (fw store run) (par (qq store continuation) (ev run)))
      ?_ ?_ (Cong.refl _)
    · exact par_rotate' (sy trigger store run)
        (par (qq store continuation) (ev run)) (mm trigger payload)
    · exact StepMinus.parLeft _
        (StepMinus.synchronise store run payload (Cong.refl trigger))
  have second :
      StepMinus Cong (par (fw store run) (par (qq store continuation) (ev run)))
        (par (mm run continuation) (ev run)) := by
    refine StepMinus.congruent
      (p' := par (par (fw store run) (qq store continuation)) (ev run))
      (q' := par (mm run continuation) (ev run))
      (Cong.symm (Cong.parAssoc _ _ _)) ?_ (Cong.refl _)
    exact StepMinus.parLeft _
      (StepMinus.release run continuation (Cong.refl store))
  have third :
      StepMinus Cong (par (mm run continuation) (ev run)) continuation := by
    refine StepMinus.congruent
      (p' := par (ev run) (mm run continuation))
      (q' := continuation)
      (Cong.parComm _ _) ?_ (Cong.refl _)
    exact StepMinus.opening continuation (Cong.refl run)
  exact Reaches.tail (Reaches.tail (Reaches.single first) second) third

/-! ## The distributor -/

/-- The distributor: a chain of duplicators broadcasting one message from a
subject to several.  Each entry names a target and the intermediate carrying
the remainder. -/
def distributor (subject : Comb) : List (Comb × Comb) → Comb
  | [] => nil
  | (target, next) :: rest => par (dd subject target next) (distributor next rest)

/-- The subjects a distributor delivers to: each listed target, and finally the
subject the chain ends at. -/
def deliveries (subject : Comb) : List (Comb × Comb) → List Comb
  | [] => [subject]
  | (target, next) :: rest => target :: deliveries next rest

/-- Messages carrying one payload at each of a list of subjects. -/
def broadcast (payload : Comb) : List Comb → Comb
  | [] => nil
  | [s] => mm s payload
  | s :: rest => par (mm s payload) (broadcast payload rest)

theorem broadcast_cons (payload s : Comb) (rest : List Comb) (h : rest ≠ []) :
    broadcast payload (s :: rest) = par (mm s payload) (broadcast payload rest) := by
  cases rest with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem deliveries_ne_nil (subject : Comb) (chain : List (Comb × Comb)) :
    deliveries subject chain ≠ [] := by
  induction chain generalizing subject with
  | nil => simp [deliveries]
  | cons head rest _ => obtain ⟨t, n⟩ := head; simp [deliveries]

/-- **The distributor broadcasts.**  A message at the chain's subject reaches
a message at every delivery subject, in one step per duplicator. -/
theorem distributor_broadcasts (payload : Comb) :
    ∀ (chain : List (Comb × Comb)) (subject : Comb),
      Reaches (par (distributor subject chain) (mm subject payload))
        (broadcast payload (deliveries subject chain)) := by
  intro chain
  induction chain with
  | nil =>
      intro subject
      exact Reaches.congruent (by
        simp only [distributor, deliveries, broadcast]
        exact Cong.trans (Cong.parComm _ _) (Cong.parNil _))
  | cons head rest ih =>
      intro subject
      obtain ⟨target, next⟩ := head
      have stepOne :
          StepMinus Cong
            (par (distributor subject ((target, next) :: rest)) (mm subject payload))
            (par (par (mm target payload) (mm next payload)) (distributor next rest)) := by
        refine StepMinus.congruent
          (p' := par (par (dd subject target next) (mm subject payload))
            (distributor next rest))
          (q' := par (par (mm target payload) (mm next payload))
            (distributor next rest))
          ?_ ?_ (Cong.refl _)
        · simp only [distributor]
          exact par_rotate' (dd subject target next) (distributor next rest)
            (mm subject payload)
        · exact StepMinus.parLeft _
            (StepMinus.duplicate target next payload (Cong.refl subject))
      have rearrange :
          Cong (par (par (mm target payload) (mm next payload)) (distributor next rest))
            (par (mm target payload)
              (par (distributor next rest) (mm next payload))) :=
        Cong.trans (Cong.parAssoc _ _ _)
          (Cong.parRight _ (Cong.parComm _ _))
      have tailReach := ih next
      have lifted :
          Reaches (par (mm target payload)
              (par (distributor next rest) (mm next payload)))
            (par (mm target payload)
              (broadcast payload (deliveries next rest))) :=
        Reaches.parRight _ tailReach
      refine Reaches.trans (Reaches.single stepOne)
        (Reaches.trans (Reaches.congruent rearrange)
          (Reaches.trans lifted (Reaches.congruent ?_)))
      have nonempty := deliveries_ne_nil next rest
      simp only [deliveries]
      rw [broadcast_cons payload target _ nonempty]
      exact Cong.refl _

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.Reaches.parRight
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.gate_releases
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.distributor_broadcasts
