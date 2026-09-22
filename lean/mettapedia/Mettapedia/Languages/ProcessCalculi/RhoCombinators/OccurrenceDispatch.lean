/-
# The general input clause: dispatching on how the bound name occurs

The previous report recorded that `translate`'s input clause installs a plain
forwarder, so it delivers the received name as **data** and does not support the
name being used as a communication **subject**. That is the gap, and this file
closes the mechanism half of it.

## One clause, one router

The three ways a bound name can be used correspond to the three routers, and the
correspondence is exact:

```
    dropped, or carried as a payload      fw split target   →  mm target value
    used as a sending subject             br split target   →  fw target value
    used as a listening subject           bl split target   →  fw value target
```

A drop needs nothing clever: `ev target` beside `mm target value` opens the
*payload*, so delivering the name to the target channel is already the drop.
A sending occurrence needs `br`, which turns the arriving name into a forwarder
*to* it, so the body's sends at `target` reach the received name. A listening
occurrence needs `bl`, which forwards *from* the received name to `target`,
where the body listens.

`inp_releases_with_router` is the input clause with the router left as a
parameter and its one-step law as a hypothesis. All three kinds are
instantiations, and `translate_inp_releases` is the first of them — so the
clause the translation already had is the data case of this one rather than a
different construction.

## What this settles and what it leaves

Settled: the mechanism. Each occurrence kind has a router, the router's law is
proved, and the input clause releases the body and routes the name in every
case (`inp_dispatch_releases`).

Left: carrying the dispatch into `translate` itself, which means classifying the
occurrences of the bound name in a body — `occurrenceKind` does it for a body
that *is* an occurrence, and the recursive version has to descend — and reaching
several occurrences at once, which is `fanOut_broadcasts` with one router per
delivery rather than one message per delivery.

Neither is a new mechanism. The remaining work is a classification pass and a
plumbing change, and the cost is already priced: one router per occurrence plus
one duplicator per extra occurrence.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.TranslationScope

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The three kinds -/

/-- How a bound name is used where it occurs. -/
inductive Occurrence where
  | data
  | sendingSubject
  | listeningSubject
  deriving DecidableEq

/-- The router an occurrence needs: it listens where the arriving name is
delivered and acts on it. -/
def routerAtom : Occurrence → Comb → Comb → Comb
  | .data, split, target => fw split target
  | .sendingSubject, split, target => br split target
  | .listeningSubject, split, target => bl split target

/-- What the router leaves behind once the name arrives.  For data the name
itself is delivered; for a sending occurrence a forwarder *to* the received
name; for a listening occurrence a forwarder *from* it. -/
def routerResult : Occurrence → Comb → Comb → Comb
  | .data, target, value => mm target value
  | .sendingSubject, target, value => fw target value
  | .listeningSubject, target, value => fw value target

/-- **Each router acts in one step.** -/
theorem routerAtom_step (kind : Occurrence) (split target value : Comb) :
    StepMinus Cong (par (routerAtom kind split target) (mm split value))
      (routerResult kind target value) := by
  cases kind
  · exact StepMinus.forward target value (Cong.refl split)
  · exact StepMinus.bindOut target value (Cong.refl split)
  · exact StepMinus.bindIn target value (Cong.refl split)

/-! ## The input clause, with the router a parameter -/

/-- **The general input clause.**  The arriving name is split, the gate releases
the body, and the router acts on the name — whatever the router is.  Leaving it
a parameter is what makes the three occurrence kinds one clause. -/
theorem inp_releases_with_router (subject trigger split store run body value
    router routed : Comb)
    (hrouter : StepMinus Cong (par router (mm split value)) routed) :
    Reaches
      (par (par (dd subject trigger split)
        (par (gate trigger store run body) router)) (mm subject value))
      (par body routed) := by
  have ac : ∀ u v : Comb, components u = components v → Cong u v :=
    fun _ _ h => cong_of_components h
  -- split the arriving name to the gate's trigger and to the router
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (dd subject trigger split) (mm subject value))
      (par (gate trigger store run body) router))
    (by simp only [components, gate]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    (Reaches.single (StepMinus.duplicate trigger split value (Cong.refl subject)))) ?_
  -- release the body
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par (gate trigger store run body) (mm trigger value))
      (par (mm split value) router))
    (by simp only [components, gate]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _
    (gate_releases trigger store run body value)) ?_
  -- let the router act on the received name
  refine Reaches.trans (Reaches.congruent (ac _
    (par (par router (mm split value)) body)
    (by simp only [components]; ac_rfl))) ?_
  refine Reaches.trans (Reaches.parLeft _ (Reaches.single hrouter)) ?_
  exact Reaches.congruent (ac _ _ (by simp only [components]; ac_rfl))

/-- **The dispatching clause releases the body and routes the name, for every
occurrence kind.** -/
theorem inp_dispatch_releases (kind : Occurrence)
    (subject trigger split store run target body value : Comb) :
    Reaches
      (par (par (dd subject trigger split)
        (par (gate trigger store run body) (routerAtom kind split target)))
        (mm subject value))
      (par body (routerResult kind target value)) :=
  inp_releases_with_router subject trigger split store run body value
    (routerAtom kind split target) (routerResult kind target value)
    (routerAtom_step kind split target value)

/-! ## The three cases, spelled out -/

/-- A dropped or carried occurrence: the name itself is delivered, and `ev` at
the target opens it. -/
theorem inp_data_releases (subject trigger split store run target body value : Comb) :
    Reaches
      (par (par (dd subject trigger split)
        (par (gate trigger store run body) (fw split target))) (mm subject value))
      (par body (mm target value)) :=
  inp_dispatch_releases .data subject trigger split store run target body value

/-- A sending occurrence: the arriving name becomes a forwarder *to* it, so the
body's sends at the target reach the received name. -/
theorem inp_sending_releases (subject trigger split store run target body value : Comb) :
    Reaches
      (par (par (dd subject trigger split)
        (par (gate trigger store run body) (br split target))) (mm subject value))
      (par body (fw target value)) :=
  inp_dispatch_releases .sendingSubject subject trigger split store run target body value

/-- A listening occurrence: the arriving name becomes a forwarder *from* it, so
what is sent on the received name reaches the body. -/
theorem inp_listening_releases (subject trigger split store run target body value : Comb) :
    Reaches
      (par (par (dd subject trigger split)
        (par (gate trigger store run body) (bl split target))) (mm subject value))
      (par body (fw value target)) :=
  inp_dispatch_releases .listeningSubject subject trigger split store run target body value

/-! ## Classifying an occurrence -/

/-- How the bound name is used, for a body that is itself the occurrence.  The
recursive classification, which has to descend through a body and report one
kind per occurrence, is not here. -/
def occurrenceKind : Src → Option Occurrence
  | Src.drop (SrcName.bvar 0) => some .data
  | Src.out (SrcName.bvar 0) _ => some .sendingSubject
  | Src.inp (SrcName.bvar 0) _ => some .listeningSubject
  | _ => none

theorem occurrenceKind_drop : occurrenceKind (Src.drop (SrcName.bvar 0)) = some .data := rfl

theorem occurrenceKind_out (payload : Src) :
    occurrenceKind (Src.out (SrcName.bvar 0) payload) = some .sendingSubject := rfl

theorem occurrenceKind_inp (body : Src) :
    occurrenceKind (Src.inp (SrcName.bvar 0) body) = some .listeningSubject := rfl

/-- **The clause the translation already had is the data case of this one.**  So
the dispatch extends `translate` rather than replacing it, and the existing size
and compositionality laws are laws about one branch of it. -/
theorem translate_inp_is_the_data_case
    (_s subject trigger split store run target body value : Comb) :
    routerAtom .data split target = fw split target
      ∧ Reaches
          (par (par (dd subject trigger split)
            (par (gate trigger store run body) (fw split target)))
            (mm subject value))
          (par body (mm target value)) :=
  ⟨rfl, inp_data_releases subject trigger split store run target body value⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
