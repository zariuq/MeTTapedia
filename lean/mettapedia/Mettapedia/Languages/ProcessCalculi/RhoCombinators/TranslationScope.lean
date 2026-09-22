/-
# What `translate` covers, and what it does not

This is a correction to my own accounting. §2 has been reported with a size law,
a compositionality law and a simulation step, all proved — and all about a
translation whose scope I had not stated.

## The gap

`translate`'s input clause ends in

```
    fw (slot s (offset + 1)) (slot s (offset + 4))
```

a plain forwarder. It delivers the received name **to a proxy channel**, so the
body reads that name as *data*: dropping it, forwarding it, or placing it inside
a quotation. Those are real occurrence kinds and the clause handles them.

What it does not handle is the received name used as a **communication
subject**. In rho a name is a value, so two processes that received the *same*
name — through *different* binders — can communicate on it. In this translation
each binder allocates its own proxy, so those two processes sit at two different
channels and never meet. `proxies_do_not_meet` is that fact, proved through the
inversion principle: the only listener and the only speaker are at distinct
slots, so there is no matching pair and no step.

`distinct_binders_distinct_proxies` is the underlying arithmetic — two input
clauses at different offsets allocate different proxies.

## What the fix is, and where it already exists

The routers `bl` and `br` are exactly the constructs for this. `br a b` turns an
arriving name into a *sending* subject and `bl a b` into a *listening* one,
rather than forwarding it to a fixed channel. So a complete input clause
dispatches on how the bound name occurs and installs the matching router — which
is the occurrence analysis this lane worked out early and then did not carry into
`translate`.

`Encoding.lean` has the worked clauses. `encodeOutputSubjectInput` uses `br`
precisely where the received name is a sending subject, and
`encodeOutputSubjectInput_reaches` proves it delivers. So the missing piece is
not a new mechanism; it is the dispatch that chooses between `fw`, `bl` and `br`
per occurrence, joined to the fan-out that reaches several occurrences.

## What this does and does not invalidate

**Unaffected.** `storedAtoms_translate_le`, the constant running soup of nested
inputs, the separation against prefix distribution, `translate_fill` and
`translate_fill_congr`, and `comm_simulated`. Each is a theorem about the term
`translate` produces, and each remains true of it. `comm_simulated` in
particular is about an input and an output whose subject is the *same* bound
index, hence the same proxy — the case that does meet.

**Scoped.** Read as a translation of rho, `translate` covers the fragment where
a bound name occurs only as data. Its size law is a size law for that fragment.
The published claim is about a translation with the dispatch, and the dispatch
would add one atom per occurrence — which `fanOut_broadcasts` already prices at
one per use — so the linearity is not in question, but the theorem as stated is
about less than the published one.

Stating this is worth more than closing the bisimulation on an object whose
scope was unrecorded.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.EnvironmentSimulation
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Inertness

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Distinct binders, distinct proxies -/

/-- Two input clauses compiled at different offsets allocate different
proxies. -/
theorem distinct_binders_distinct_proxies (s : Comb) {first second : ℕ}
    (h : first ≠ second) : slot s (first + 4) ≠ slot s (second + 4) :=
  slot_ne (by omega)

/-- And they are distinct up to structural congruence, which is what a
communication needs. -/
theorem distinct_binders_proxies_not_cong (s : Comb) {first second : ℕ}
    (h : first ≠ second) : ¬ Cong (slot s (first + 4)) (slot s (second + 4)) :=
  slot_not_cong (by omega)

/-! ## So two binders' bodies do not meet -/

/-- **A name delivered at one binder's proxy is not received by a process
listening at another binder's proxy.**  In the source both processes hold the
same name and should communicate; in this translation they are at two channels
and there is no step at all.

This is the gap: the translation communicates on the proxy channel a name
*arrived at*, not on the name's own identity. -/
theorem proxies_do_not_meet (s : Comb) {first second : ℕ} (h : first ≠ second)
    (value left right : Comb) :
    ∀ target, ¬ Step Cong
      (par (mm (slot s (first + 4)) value)
        (dd (slot s (second + 4)) left right)) target := by
  refine no_step_of_not_hasMatchingPair ?_
  rintro ⟨listener, hlistener, speaker, hspeaker, heard, hheard, spoken, hspoken,
    hcong⟩
  simp only [components, Multiset.mem_add, Multiset.mem_singleton] at hlistener hspeaker
  rcases hlistener with rfl | rfl
  · simp [listenSubjects] at hheard
  · rcases hspeaker with rfl | rfl
    · simp only [speakSubjects, List.mem_singleton] at hspoken
      simp only [listenSubjects, List.mem_singleton] at hheard
      subst hheard; subst hspoken
      exact distinct_binders_proxies_not_cong s (Ne.symm h) hcong
    · simp [speakSubjects] at hspoken

/-! ## The fragment the translation does cover -/

/-- The bound-name occurrence `translate` installs: a forwarder to the proxy,
which delivers the name as data. -/
theorem translate_inp_delivers_as_data (s : Comb) (proxies : List Comb)
    (subject : SrcName) (body : Src) (offset : ℕ) :
    translate s proxies (Src.inp subject body) offset
      = par (dd (translateName s proxies subject (offset + 5)) (slot s offset)
            (slot s (offset + 1)))
        (par (gate (slot s offset) (slot s (offset + 2)) (slot s (offset + 3))
              (translate s (slot s (offset + 4) :: proxies) body
                (offset + 5 + subject.slotsUsed)))
          (fw (slot s (offset + 1)) (slot s (offset + 4)))) := rfl

/-- **The case that does meet**: an input and an output on the *same* bound
index compile to the same proxy, which is why `comm_simulated` holds. -/
theorem same_index_same_subject (s : Comb) (proxies : List Comb) (index : ℕ)
    (first second : ℕ) :
    translateName s proxies (SrcName.bvar index) first
      = translateName s proxies (SrcName.bvar index) second := rfl

/-- The router that a complete clause would install for a sending occurrence
exists and works: `br` turns an arriving name into a sending subject, which is
what makes communication happen on the name rather than on the channel. -/
theorem sending_router_available (subject target value : Comb) :
    Reaches (par (br subject target) (mm subject value)) (fw target value) :=
  Reaches.single (StepMinus.bindOut target value (Cong.refl subject))

/-- And the listening router likewise. -/
theorem listening_router_available (subject target value : Comb) :
    Reaches (par (bl subject target) (mm subject value)) (fw value target) :=
  Reaches.single (StepMinus.bindIn target value (Cong.refl subject))

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
