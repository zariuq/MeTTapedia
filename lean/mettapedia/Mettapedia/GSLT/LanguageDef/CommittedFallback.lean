import Mettapedia.GSLT.LanguageDef.HostCallMachine

/-!
# Ordered queries with committed fallback

This is the operational control of `exact *-> continuation ; fallback`, not
a Boolean approximation to either query. Answers may include logical stores,
occurrence identities and values. The world returned by every poll is retained;
it is distinct from any backtrackable store carried by the cursor or answer.

The source is an inductive small-step relation. It commits on the first exact
answer, retains every remaining exact alternative, and permits fallback only
after normal answerless exhaustion. Suspension and faults are not exhaustion.
The continuation consuming an answer does not control this commitment.

The host supplies the existing `Pull` protocol. `Except` additionally makes
faults explicit. No typing relation, matcher or binding engine is defined here.
The separately implemented marker-based lowering is in `CommittedFallbackNative`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CommittedFallback

open Mettapedia.GSLT.LanguageDef.HostCalls (Pull)

variable {Cursor Answer World Fault : Type}

/-- The two queries and the fallback entry at the original logical checkpoint.
The returned world is not rolled back when that checkpoint is restored. -/
structure Queries (Cursor Answer World Fault : Type) where
  exact : Cursor → World → World × Except Fault (Pull Cursor Answer)
  fallback : Cursor → World → World × Except Fault (Pull Cursor Answer)
  startFallback : World → Cursor

inductive Phase (Cursor Fault : Type) where
  | probing (cursor : Cursor)
  | committed (cursor : Cursor)
  | fallback (cursor : Cursor)
  | done
  | fault (error : Fault)
  deriving DecidableEq, Repr

structure State (Cursor Answer World Fault : Type) where
  phase : Phase Cursor Fault
  world : World
  answers : List Answer
  deriving DecidableEq, Repr

/-- Each clause states one source rule independently of its native encoding. -/
inductive Step (q : Queries Cursor Answer World Fault) :
    State Cursor Answer World Fault → State Cursor Answer World Fault → Prop where
  | probingDone {c w w' as} : q.exact c w = (w', .ok .done) →
      Step q ⟨.probing c, w, as⟩ ⟨.fallback (q.startFallback w'), w', as⟩
  | probingYield {c c' w w' as a} : q.exact c w = (w', .ok (.yield a c')) →
      Step q ⟨.probing c, w, as⟩ ⟨.committed c', w', as ++ [a]⟩
  | probingSuspend {c c' w w' as} : q.exact c w = (w', .ok (.suspend c')) →
      Step q ⟨.probing c, w, as⟩ ⟨.probing c', w', as⟩
  | probingFault {c w w' as e} : q.exact c w = (w', .error e) →
      Step q ⟨.probing c, w, as⟩ ⟨.fault e, w', as⟩
  | committedDone {c w w' as} : q.exact c w = (w', .ok .done) →
      Step q ⟨.committed c, w, as⟩ ⟨.done, w', as⟩
  | committedYield {c c' w w' as a} : q.exact c w = (w', .ok (.yield a c')) →
      Step q ⟨.committed c, w, as⟩ ⟨.committed c', w', as ++ [a]⟩
  | committedSuspend {c c' w w' as} : q.exact c w = (w', .ok (.suspend c')) →
      Step q ⟨.committed c, w, as⟩ ⟨.committed c', w', as⟩
  | committedFault {c w w' as e} : q.exact c w = (w', .error e) →
      Step q ⟨.committed c, w, as⟩ ⟨.fault e, w', as⟩
  | fallbackDone {c w w' as} : q.fallback c w = (w', .ok .done) →
      Step q ⟨.fallback c, w, as⟩ ⟨.done, w', as⟩
  | fallbackYield {c c' w w' as a} : q.fallback c w = (w', .ok (.yield a c')) →
      Step q ⟨.fallback c, w, as⟩ ⟨.fallback c', w', as ++ [a]⟩
  | fallbackSuspend {c c' w w' as} : q.fallback c w = (w', .ok (.suspend c')) →
      Step q ⟨.fallback c, w, as⟩ ⟨.fallback c', w', as⟩
  | fallbackFault {c w w' as e} : q.fallback c w = (w', .error e) →
      Step q ⟨.fallback c, w, as⟩ ⟨.fault e, w', as⟩

/-- A finite execution retains the actual ordered states, not a set of answers. -/
abbrev Reaches (q : Queries Cursor Answer World Fault) := Relation.ReflTransGen (Step q)

def SettledChoice : Phase Cursor Fault → Prop
  | .committed _ | .done | .fault _ => True
  | .probing _ | .fallback _ => False

def IsFallback : Phase Cursor Fault → Prop
  | .fallback _ => True
  | _ => False

theorem settled_not_fallback {phase : Phase Cursor Fault} (h : SettledChoice phase) :
    ¬ IsFallback phase := by
  cases phase <;> simp_all [SettledChoice, IsFallback]

/-- Commitment is monotone, including after exact-query faults or exhaustion. -/
theorem Step.preserves_settled {q : Queries Cursor Answer World Fault}
    {s t : State Cursor Answer World Fault} (h : Step q s t)
    (settled : SettledChoice s.phase) : SettledChoice t.phase := by
  cases h <;> simp_all [SettledChoice]

theorem Reaches.preserves_settled {q : Queries Cursor Answer World Fault}
    {s t : State Cursor Answer World Fault} (h : Reaches q s t)
    (settled : SettledChoice s.phase) : SettledChoice t.phase := by
  induction h with
  | refl => exact settled
  | tail _ step ih => exact step.preserves_settled ih

/-- Once the query has committed, its remaining control cannot enter fallback.
Enclosing answer consumers are not part of this state machine. -/
theorem committed_never_fallback {q : Queries Cursor Answer World Fault}
    {c : Cursor} {w : World} {as : List Answer} {t : State Cursor Answer World Fault}
    (h : Reaches q ⟨.committed c, w, as⟩ t) : ¬ IsFallback t.phase :=
  settled_not_fallback (h.preserves_settled (by simp [SettledChoice]))

/-- A poll either retains the trace or appends precisely the answer it produced. -/
theorem Step.answers_extend {q : Queries Cursor Answer World Fault}
    {s t : State Cursor Answer World Fault} (h : Step q s t) :
    ∃ added : List Answer, t.answers = s.answers ++ added := by
  cases h <;> first | exact ⟨[], (List.append_nil _).symm⟩ | exact ⟨[_], rfl⟩

theorem Reaches.answers_extend {q : Queries Cursor Answer World Fault}
    {s t : State Cursor Answer World Fault} (h : Reaches q s t) :
    ∃ added : List Answer, t.answers = s.answers ++ added := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | tail _ step ih =>
      obtain ⟨before, before_eq⟩ := ih
      obtain ⟨after, after_eq⟩ := step.answers_extend
      exact ⟨before ++ after, by rw [after_eq, before_eq, List.append_assoc]⟩

theorem Step.done_impossible {q : Queries Cursor Answer World Fault}
    {w : World} {as : List Answer} {t : State Cursor Answer World Fault} :
    ¬ Step q ⟨.done, w, as⟩ t := by intro h; cases h

theorem Step.fault_impossible {q : Queries Cursor Answer World Fault}
    {e : Fault} {w : World} {as : List Answer} {t : State Cursor Answer World Fault} :
    ¬ Step q ⟨.fault e, w, as⟩ t := by intro h; cases h

/-- A switch from the probing query has an explicit exhaustion witness. -/
theorem Step.fallback_entry_iff (q : Queries Cursor Answer World Fault)
    (c c' : Cursor) (w w' : World) (as bs : List Answer) :
    Step q ⟨.probing c, w, as⟩ ⟨.fallback c', w', bs⟩ ↔
      q.exact c w = (w', .ok .done) ∧ c' = q.startFallback w' ∧ bs = as := by
  constructor
  · intro h
    cases h with
    | probingDone pulled => exact ⟨pulled, rfl, rfl⟩
  · rintro ⟨pulled, rfl, rfl⟩
    exact .probingDone pulled

theorem suspend_cannot_start_fallback (q : Queries Cursor Answer World Fault)
    {c c' : Cursor} {w w' : World} {as : List Answer}
    (pulled : q.exact c w = (w', .ok (.suspend c'))) :
    ∀ c'' w'' bs, ¬ Step q ⟨.probing c, w, as⟩ ⟨.fallback c'', w'', bs⟩ := by
  intro c'' w'' bs h
  have impossible := (Step.fallback_entry_iff q c c'' w w'' as bs).mp h
  rw [pulled] at impossible
  cases impossible.1

theorem fault_cannot_start_fallback (q : Queries Cursor Answer World Fault)
    {c : Cursor} {w w' : World} {as : List Answer} {e : Fault}
    (pulled : q.exact c w = (w', .error e)) :
    ∀ c'' w'' bs, ¬ Step q ⟨.probing c, w, as⟩ ⟨.fallback c'', w'', bs⟩ := by
  intro c'' w'' bs h
  have impossible := (Step.fallback_entry_iff q c c'' w w'' as bs).mp h
  rw [pulled] at impossible
  cases impossible.1

end Mettapedia.GSLT.LanguageDef.CommittedFallback
