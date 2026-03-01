/-!
# Generic Reflexive-Transitive Closure for Process Calculi

Type-valued reflexive-transitive closure with generic congruence lifters.
Subsumes the duplicated `MultiStep`/`ReducesStar` definitions across
π-calculus, ρ-calculus, and MQ-calculus.

## Key definitions

* `RTClosure R x y` — Type-valued closure of relation `R`
* `RTClosureProp R x y` — Prop-valued closure of relation `R`
* `RTClosure.liftUnary` — lift congruence through unary context (e.g., restriction)
* `RTClosure.liftBinLeft` — lift congruence through left of binary context (e.g., par)
* `RTClosure.liftBinRight` — lift congruence through right of binary context

## Usage

Each process calculus defines its one-step reduction `Reduces` and obtains
multi-step closure + all congruence lifters for free:

```
abbrev MultiStep := RTClosure Reduces
-- par_left := RTClosure.liftBinLeft (fun z h => Reduces.par_left _ _ z h)
-- par_right := RTClosure.liftBinRight (fun z h => Reduces.par_right z _ _ h)
-- nu := RTClosure.liftUnary (fun h => Reduces.res _ _ h)
```

## Note

Named `RTClosure` / `RTClosureProp` to avoid conflict with Mathlib's
`Star` typeclass (star operations on algebraic structures).
-/

universe u

namespace ProcessCalculi

/-- Type-valued reflexive-transitive closure of a relation.

    Used by π-calculus and ρ-calculus where extraction of witnesses is needed. -/
inductive RTClosure {α : Type u} (R : α → α → Type u) : α → α → Type u where
  | refl (x : α) : RTClosure R x x
  | step {x y z : α} : R x y → RTClosure R y z → RTClosure R x z

/-- Prop-valued reflexive-transitive closure of a relation.

    Used by MQ-calculus and any calculus where witness extraction is not needed. -/
inductive RTClosureProp {α : Type u} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : RTClosureProp R x x
  | step {x y z : α} : R x y → RTClosureProp R y z → RTClosureProp R x z

namespace RTClosure

variable {α : Type u} {R : α → α → Type u}

/-- Embed a single step into the closure. -/
def single {x y : α} (h : R x y) : RTClosure R x y :=
  .step h (.refl y)

/-- Transitivity: compose two multi-step sequences. -/
def trans {x y z : α} : RTClosure R x y → RTClosure R y z → RTClosure R x z
  | .refl _, h₂ => h₂
  | .step h rest, h₂ => .step h (trans rest h₂)

/-- Length of a multi-step derivation. -/
def length {x y : α} : RTClosure R x y → Nat
  | .refl _ => 0
  | .step _ rest => 1 + rest.length

/-! ## Generic Congruence Lifters -/

/-- Lift a single-step congruence rule through a unary context.

    Example: if `Reduces p p'` implies `Reduces (nu p) (nu p')`,
    then `RTClosure Reduces p p'` implies `RTClosure Reduces (nu p) (nu p')`. -/
def liftUnary {f : α → α}
    (cong : ∀ {x y : α}, R x y → R (f x) (f y))
    {x y : α} : RTClosure R x y → RTClosure R (f x) (f y)
  | .refl _ => .refl _
  | .step hr rest => .step (cong hr) (liftUnary cong rest)

/-- Lift a single-step congruence rule through the left of a binary context. -/
def liftBinLeft {f : α → α → α}
    (cong : ∀ {x y : α} (z : α), R x y → R (f x z) (f y z))
    {x y : α} (z : α) : RTClosure R x y → RTClosure R (f x z) (f y z)
  | .refl _ => .refl _
  | .step hr rest => .step (cong z hr) (liftBinLeft cong z rest)

/-- Lift a single-step congruence rule through the right of a binary context. -/
def liftBinRight {f : α → α → α}
    (cong : ∀ (z : α) {x y : α}, R x y → R (f z x) (f z y))
    (z : α) {x y : α} : RTClosure R x y → RTClosure R (f z x) (f z y)
  | .refl _ => .refl _
  | .step hr rest => .step (cong z hr) (liftBinRight cong z rest)

/-- Lift congruence on both sides of a binary context. -/
def liftBinBoth {f : α → α → α}
    (congL : ∀ {x y : α} (z : α), R x y → R (f x z) (f y z))
    (congR : ∀ (z : α) {x y : α}, R x y → R (f z x) (f z y))
    {a a' b b' : α} (ha : RTClosure R a a') (hb : RTClosure R b b') :
    RTClosure R (f a b) (f a' b') :=
  (liftBinLeft congL b ha).trans (liftBinRight congR a' hb)

end RTClosure

namespace RTClosureProp

variable {α : Type u} {R : α → α → Prop}

/-- Embed a single step into the Prop-valued closure. -/
theorem single {x y : α} (h : R x y) : RTClosureProp R x y :=
  .step h (.refl y)

/-- Transitivity for Prop-valued closure. -/
theorem trans {x y z : α} : RTClosureProp R x y → RTClosureProp R y z → RTClosureProp R x z
  | .refl _, h₂ => h₂
  | .step h rest, h₂ => .step h (trans rest h₂)

/-! ## Generic Congruence Lifters (Prop-valued) -/

theorem liftUnary {f : α → α}
    (cong : ∀ {x y : α}, R x y → R (f x) (f y))
    {x y : α} : RTClosureProp R x y → RTClosureProp R (f x) (f y)
  | .refl _ => .refl _
  | .step hr rest => .step (cong hr) (liftUnary cong rest)

theorem liftBinLeft {f : α → α → α}
    (cong : ∀ {x y : α} (z : α), R x y → R (f x z) (f y z))
    {x y : α} (z : α) : RTClosureProp R x y → RTClosureProp R (f x z) (f y z)
  | .refl _ => .refl _
  | .step hr rest => .step (cong z hr) (liftBinLeft cong z rest)

theorem liftBinRight {f : α → α → α}
    (cong : ∀ (z : α) {x y : α}, R x y → R (f z x) (f z y))
    (z : α) {x y : α} : RTClosureProp R x y → RTClosureProp R (f z x) (f z y)
  | .refl _ => .refl _
  | .step hr rest => .step (cong z hr) (liftBinRight cong z rest)

theorem liftBinBoth {f : α → α → α}
    (congL : ∀ {x y : α} (z : α), R x y → R (f x z) (f y z))
    (congR : ∀ (z : α) {x y : α}, R x y → R (f z x) (f z y))
    {a a' b b' : α} (ha : RTClosureProp R a a') (hb : RTClosureProp R b b') :
    RTClosureProp R (f a b) (f a' b') :=
  (liftBinLeft congL b ha).trans (liftBinRight congR a' hb)

end RTClosureProp

end ProcessCalculi
