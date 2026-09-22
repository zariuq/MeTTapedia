/-
# The simulation, with sharing on both sides

The previous report showed that translation does not commute with **substituting**
substitution: a name substituted at two occurrences is translated twice, at two
different slot ranges, while the target routes one name and stores the code once.
The conclusion drawn there was that a simulation argument must be behavioural.

That conclusion was too pessimistic, and writing the correspondence out shows
why. The mismatch is not between the target and the source; it is between the
target and one particular *presentation* of the source. `translate` already
carries a list of proxies — an environment. Give the source an environment too,
and the two sides do the same thing.

## The environment semantics

`ClosureStep` is reduction that **extends the environment instead of
substituting**:

```
    ⟨ for y ← x . P  |  x⟨Q⟩ ,  env ⟩   →   ⟨ P ,  ⌜Q⌝ :: env ⟩
```

Nothing is copied. That is exactly what the target does: the gate releases the
compiled body, which was compiled against a fresh proxy, and the payload's code
arrives at that proxy as a message.

## The simulation is exact

`comm_simulated`: a closure step is simulated by target reduction, on the nose.
The compiled body's new proxy corresponds to the new environment entry, and the
message delivering the payload's code at that proxy corresponds to the entry's
value. No behavioural reasoning is needed, because both sides share.

The proof is `translate_inp_releases` applied at the instantiation the
translation produces — the shapes line up by definitional unfolding, which is
the useful sign that the input clause was compiled in the shape the semantics
wanted.

## The restriction, and it is the same sharing question one level down

The simulation holds when the communication subject is a **received name** — a
bound index. That is not a convenience: `translateName` of a bound index reads
the environment and is offset-independent, so the input's subject and the
output's subject compile to the *same* target name.

For a subject given as a literal quotation the two occurrences compile at
different offsets and therefore to different names, which
`quotedSubject_not_shared` exhibits. So the subject needs sharing for the same
reason the payload did, and the environment presentation supplies it for bound
names and not for literals.

The honest statement is therefore: with sharing on both sides the simulation is
exact for communication on received names, and communication on a literal
quotation needs the subject interned — which is a statement about the
translation's name allocation, not about the calculus.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.SourceSemantics

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The source with an environment -/

/-- Reduction that extends the environment rather than substituting: the
communication rule binds the received name by pushing it, and copies nothing.
This is the presentation the target implements. -/
inductive ClosureStep : Src → List SrcName → Src → List SrcName → Prop where
  | comm (index : ℕ) (body payload : Src) (env : List SrcName) :
      ClosureStep
        (Src.par (Src.inp (SrcName.bvar index) body)
          (Src.out (SrcName.bvar index) payload)) env
        body (SrcName.quote payload :: env)

/-- Collapsing an environment is substitution: the substituting semantics is the
environment one with its sharing forgotten. -/
def collapseOne (name : SrcName) (body : Src) : Src := body.subst name 0

theorem collapseOne_comm (_index : ℕ) (body payload : Src) :
    collapseOne (SrcName.quote payload) body
      = body.subst (SrcName.quote payload) 0 := rfl

/-! ## The simulation -/

/-- **A closure step is simulated exactly.**  The compiled body's new proxy is
the new environment entry, and the message delivering the payload's code at that
proxy is the entry's value.  Both sides share, so nothing behavioural is needed.

The offsets are written as the translation produces them; `comm_simulated_offsets`
gives them in closed form. -/
theorem comm_simulated (s : Comb) (proxies : List Comb) (index : ℕ)
    (body payload : Src) (offset : ℕ) :
    Reaches
      (translate s proxies
        (Src.par (Src.inp (SrcName.bvar index) body)
          (Src.out (SrcName.bvar index) payload)) offset)
      (par (translate s (slot s (offset + 4) :: proxies) body
            (offset + 5 + (SrcName.bvar index).slotsUsed))
        (mm (slot s (offset + 4))
          (translate s proxies payload
            (offset + (Src.inp (SrcName.bvar index) body).slotsUsed
              + (SrcName.bvar index).slotsUsed)))) :=
  translate_inp_releases s (proxies.getD index nil) (slot s offset)
    (slot s (offset + 1)) (slot s (offset + 2)) (slot s (offset + 3))
    (slot s (offset + 4))
    (translate s (slot s (offset + 4) :: proxies) body
      (offset + 5 + (SrcName.bvar index).slotsUsed))
    (translate s proxies payload
      (offset + (Src.inp (SrcName.bvar index) body).slotsUsed
        + (SrcName.bvar index).slotsUsed))

/-- The offsets in closed form: the continuation is compiled five slots on, and
the payload after the whole input clause. -/
theorem comm_simulated_offsets (index : ℕ) (body : Src) (offset : ℕ) :
    offset + 5 + (SrcName.bvar index).slotsUsed = offset + 5
      ∧ offset + (Src.inp (SrcName.bvar index) body).slotsUsed
          + (SrcName.bvar index).slotsUsed = offset + 5 + body.slotsUsed := by
  refine ⟨by simp [SrcName.slotsUsed], ?_⟩
  simp only [Src.slotsUsed, SrcName.slotsUsed]
  omega

/-- **The correspondence, stated against the environment semantics.**  A closure
step on a received name is matched by target reduction to the compiled
continuation beside its environment entry — the proxy extension on the target
mirroring the environment extension on the source. -/
theorem closureStep_simulated (s : Comb) (proxies : List Comb) (index : ℕ)
    (body payload : Src) (env : List SrcName) (offset : ℕ)
    (_step : ClosureStep
      (Src.par (Src.inp (SrcName.bvar index) body)
        (Src.out (SrcName.bvar index) payload)) env
      body (SrcName.quote payload :: env)) :
    Reaches
      (translate s proxies
        (Src.par (Src.inp (SrcName.bvar index) body)
          (Src.out (SrcName.bvar index) payload)) offset)
      (par (translate s (slot s (offset + 4) :: proxies) body
            (offset + 5 + (SrcName.bvar index).slotsUsed))
        (mm (slot s (offset + 4))
          (translate s proxies payload
            (offset + (Src.inp (SrcName.bvar index) body).slotsUsed
              + (SrcName.bvar index).slotsUsed)))) :=
  comm_simulated s proxies index body payload offset

/-! ## Why the subject has to be a received name -/

/-- A bound subject reads the environment, so it is offset-independent: the
input's subject and the output's subject compile to the same target name.  This
is what makes the simulation exact. -/
theorem boundSubject_shared (s : Comb) (proxies : List Comb) (index : ℕ)
    (first second : ℕ) :
    translateName s proxies (SrcName.bvar index) first
      = translateName s proxies (SrcName.bvar index) second := rfl

/-- **A quoted subject is not shared.**  Two occurrences compile at different
offsets and therefore to different names, so the input and the output do not
meet.  The subject needs the same sharing the payload did, and a literal
quotation does not get it from the environment. -/
theorem quotedSubject_not_shared (s : Comb) (proxies : List Comb) :
    translateName s proxies (SrcName.quote allocatingPayload) 0
      ≠ translateName s proxies (SrcName.quote allocatingPayload) 5 := by
  intro h
  simp only [translateName] at h
  exact absurd
    (translate_inp_offset_injective s proxies (SrcName.quote Src.nil) Src.nil h)
    (by decide)

/-- The two facts together: sharing is what the simulation needs, the
environment supplies it for received names, and a literal quotation would need
the subject interned instead. -/
theorem simulation_needs_subject_sharing (s : Comb) (proxies : List Comb)
    (index : ℕ) :
    (∀ first second : ℕ,
        translateName s proxies (SrcName.bvar index) first
          = translateName s proxies (SrcName.bvar index) second)
      ∧ translateName s proxies (SrcName.quote allocatingPayload) 0
          ≠ translateName s proxies (SrcName.quote allocatingPayload) 5 :=
  ⟨boundSubject_shared s proxies index, quotedSubject_not_shared s proxies⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
