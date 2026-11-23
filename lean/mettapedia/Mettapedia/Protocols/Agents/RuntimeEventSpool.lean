import Mathlib.Tactic

/-!
# Runtime events through a durable spool

Python producers spool each runtime event as a whole file; the native client
takes the files oldest first. Taking one is two steps: the event is handed
to this process's pending input, then its file is removed. The removal is
the durable receipt. A crash empties the process's pending input; the files
stay.

Invariants proved here, over every reachable state:
* no event is lost: each one ever spooled is still waiting or was handed to
  some process;
* one process never holds an event twice: its pending input has no
  duplicates;
* the spool never holds an event twice, and only spooled events are handed.

The counterexample removes the file before handing the event: a crash
between the two steps loses an event that no process ever saw.

This is an abstract contract, not a refinement proof of
`src/runtime_events_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.RuntimeEventSpool

structure State where
  /-- Every event ever spooled. -/
  produced : List ℕ
  /-- Waiting files, oldest first. -/
  spool : List ℕ
  /-- Handed to this process. -/
  pending : List ℕ
  /-- Handed to any process, ever. -/
  delivered : List ℕ
  /-- Handed, its file not yet removed. -/
  inHand : Option ℕ

def initial : State := ⟨[], [], [], [], none⟩

inductive Step : State → State → Prop
  | produce (s : State) (e : ℕ) (fresh : e ∉ s.produced) :
      Step s { s with produced := e :: s.produced, spool := s.spool ++ [e] }
  | hand (s : State) (e : ℕ) (rest : List ℕ) (head : s.spool = e :: rest) (idle : s.inHand = none) :
      Step s { s with pending := s.pending ++ [e], delivered := e :: s.delivered, inHand := some e }
  | remove (s : State) (e : ℕ) (rest : List ℕ) (head : s.spool = e :: rest) (held : s.inHand = some e) :
      Step s { s with spool := rest, inHand := none }
  | crash (s : State) : Step s { s with pending := [], inHand := none }

def Inv (s : State) : Prop :=
  s.spool.Nodup ∧ s.pending.Nodup ∧
  (∀ e ∈ s.spool, e ∈ s.produced) ∧
  (∀ e ∈ s.delivered, e ∈ s.produced) ∧
  (∀ e ∈ s.pending, e ∈ s.delivered) ∧
  (∀ e ∈ s.produced, e ∈ s.spool ∨ e ∈ s.delivered) ∧
  (∀ e ∈ s.pending, e ∈ s.spool → s.inHand = some e) ∧
  (∀ e, s.inHand = some e → e ∈ s.pending ∧ s.spool.head? = some e)

theorem inv_initial : Inv initial := by
  simp [Inv, initial]

theorem inv_step (s t : State) (hs : Inv s) (step : Step s t) : Inv t := by
  obtain ⟨hsn, hpn, hsp, hdp, hpd, hlost, hps, hih⟩ := hs
  cases step with
  | produce e fresh =>
    have hes : e ∉ s.spool := fun h => fresh (hsp e h)
    have hep : e ∉ s.pending := fun h => fresh (hdp e (hpd e h))
    refine ⟨List.nodup_append.2 ⟨hsn, List.nodup_singleton e, ?_⟩, hpn, ?_, ?_, hpd, ?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hes ha
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact List.mem_cons_of_mem _ (hsp x hx)
      · exact List.mem_cons_self
    · intro x hx; exact List.mem_cons_of_mem _ (hdp x hx)
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
      · rcases hlost x hx with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr h
    · intro x hx hxs
      simp only [List.mem_append, List.mem_singleton] at hxs
      rcases hxs with hxs | rfl
      · exact hps x hx hxs
      · exact absurd hx hep
    · intro x hx
      obtain ⟨h1, h2⟩ := hih x hx
      refine ⟨h1, ?_⟩
      cases hsp' : s.spool with
      | nil => simp [hsp'] at h2
      | cons a rest => simpa [hsp'] using h2
  | hand e rest head idle =>
    have hes : e ∈ s.spool := by simp [head]
    have hep : e ∉ s.pending := fun h => by simp [hps e h hes] at idle
    refine ⟨hsn, List.nodup_append.2 ⟨hpn, List.nodup_singleton e, ?_⟩, hsp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hep ha
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hsp x hes
      · exact hdp x hx
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact List.mem_cons_of_mem _ (hpd x hx)
      · exact List.mem_cons_self
    · intro x hx
      rcases hlost x hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · intro x hx hxs
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · simp [hps x hx hxs] at idle
      · rfl
    · intro x hx
      simp only [Option.some.injEq] at hx
      subst hx
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _), by simp [head]⟩
  | remove e rest head held =>
    have hnd : s.spool.Nodup := hsn
    rw [head] at hnd
    have hrest : e ∉ rest := (List.nodup_cons.1 hnd).1
    refine ⟨(List.nodup_cons.1 hnd).2, hpn, ?_, hdp, hpd, ?_, ?_, ?_⟩
    · intro x hx; exact hsp x (by simp [head, hx])
    · intro x hx
      rcases hlost x hx with h | h
      · rw [head] at h
        rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (hpd x (hih x held).1)
        · exact Or.inl h
      · exact Or.inr h
    · intro x hx hxr
      have := hps x hx (by simp [head, hxr])
      rw [held] at this
      simp only [Option.some.injEq] at this
      subst this
      exact absurd hxr hrest
    · intro x hx; simp at hx
  | crash =>
    refine ⟨hsn, List.nodup_nil, hsp, hdp, ?_, hlost, ?_, ?_⟩ <;> simp

/-- Reachable states. -/
inductive Reachable : State → Prop
  | initial : Reachable initial
  | step (s t : State) : Reachable s → Step s t → Reachable t

theorem reachable_inv (s : State) (h : Reachable s) : Inv s := by
  induction h with
  | initial => exact inv_initial
  | step s t _ st ih => exact inv_step s t ih st

theorem no_event_lost (s : State) (h : Reachable s) (e : ℕ) (he : e ∈ s.produced) :
    e ∈ s.spool ∨ e ∈ s.delivered := (reachable_inv s h).2.2.2.2.2.1 e he

theorem handed_once_per_process (s : State) (h : Reachable s) : s.pending.Nodup :=
  (reachable_inv s h).2.1

/-! ## Counterexample: removing the file before handing the event -/

/-- The file is removed first; the event is handed after. -/
inductive StepRemoveFirst : State → State → Prop
  | produce (s : State) (e : ℕ) (fresh : e ∉ s.produced) :
      StepRemoveFirst s { s with produced := e :: s.produced, spool := s.spool ++ [e] }
  | remove (s : State) (e : ℕ) (rest : List ℕ) (head : s.spool = e :: rest) (idle : s.inHand = none) :
      StepRemoveFirst s { s with spool := rest, inHand := some e }
  | hand (s : State) (e : ℕ) (held : s.inHand = some e) :
      StepRemoveFirst s { s with pending := s.pending ++ [e], delivered := e :: s.delivered, inHand := none }
  | crash (s : State) : StepRemoveFirst s { s with pending := [], inHand := none }

/-- Produce event 7, remove its file, crash: no process ever saw it, and it
no longer waits. -/
example :
    let s1 : State := ⟨[7], [7], [], [], none⟩
    let s2 : State := ⟨[7], [], [], [], some 7⟩
    let s3 : State := ⟨[7], [], [], [], none⟩
    StepRemoveFirst initial s1 ∧ StepRemoveFirst s1 s2 ∧ StepRemoveFirst s2 s3 ∧
      7 ∈ s3.produced ∧ 7 ∉ s3.spool ∧ 7 ∉ s3.delivered := by
  refine ⟨StepRemoveFirst.produce initial 7 (by simp [initial]),
          StepRemoveFirst.remove _ 7 [] rfl rfl, StepRemoveFirst.crash _, by simp, by simp, by simp⟩

end Mettapedia.Protocols.Agents.RuntimeEventSpool
