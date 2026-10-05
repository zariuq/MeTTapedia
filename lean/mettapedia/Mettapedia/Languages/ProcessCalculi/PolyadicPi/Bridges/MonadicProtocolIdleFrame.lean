import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolInitialization
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectObservations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles

/-!
# Ordinary occurrences beside offered and pending tuple sessions

The ordinary frame retains its literal source occurrence list. Every head
is an original unary message, listener, or persistent listener of either
arity. Its target head is the actual unary lowering, and its source arity
and persistence remain available for selecting a real source communication.
Guard bodies are retained unchanged and are opaque to active observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.IdleFrame

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ScopedActiveFrontier ActiveMarking ActiveGuardedBodies

inductive Head : {Γ : Ctx sig} → Proc Γ → Prop where
  | output {Γ} (channel datum : Name Γ) : Head (out1 channel datum)
  | input1 {Γ} (channel : Name Γ) {body : Proc (.nm :: Γ)} :
      Guarded body → Head (inp1 channel body)
  | input2 {Γ} (channel : Name Γ) {body : Proc (.nm :: .nm :: Γ)} :
      Guarded body → Head (inp2 channel body)
  | server1 {Γ} (channel : Name Γ) {body : Proc (.nm :: Γ)} :
      Guarded body → Head (rep (inp1 channel body))
  | server2 {Γ} (channel : Name Γ) {body : Proc (.nm :: .nm :: Γ)} :
      Guarded body → Head (rep (inp2 channel body))

theorem head_of_residual {Γ : Ctx sig} {atom : Proc Γ}
    (guarded : GuardedAtom atom) (absent : Initialization.selectOffer atom = none) : Head atom := by
  cases guarded with
  | inp1 channel body => exact .input1 channel body
  | inp2 channel body => exact .input2 channel body
  | out1 channel datum => exact .output channel datum
  | out2 => cases absent
  | server1 channel body => exact .server1 channel body
  | server2 channel body => exact .server2 channel body

theorem entry_heads {Γ : Ctx sig} {process : Proc Γ}
    (entry : Initialization.Entry process) : ∀ atom ∈ entry.residual, Head atom := by
  intro atom member
  obtain ⟨guarded, absent⟩ := entry.heads atom member
  exact head_of_residual guarded absent

theorem Head.guarded {Γ : Ctx sig} {atom : Proc Γ} (head : Head atom) : Guarded atom := by
  cases head with
  | output channel datum => exact .out1 channel datum
  | input1 channel body => exact .inp1 channel body
  | input2 channel body => exact .inp2 channel body
  | server1 channel body => exact .server1 channel body
  | server2 channel body => exact .server2 channel body

theorem Head.rename {Γ Δ : Ctx sig} {atom : Proc Γ}
    (head : Head atom) (environment : Ren sig Γ Δ) : Head (rename environment atom) := by
  cases head with
  | output channel datum => exact .output _ _
  | input1 channel body => exact .input1 _ (body.rename (liftRen environment [.nm]))
  | input2 channel body => exact .input2 _ (body.rename (liftRen environment [.nm, .nm]))
  | server1 channel body => exact .server1 _ (body.rename (liftRen environment [.nm]))
  | server2 channel body => exact .server2 _ (body.rename (liftRen environment [.nm, .nm]))

/-- Lowered ordinary heads introduce no active private scope. The decoder's
callback allocation remains beneath its public input. -/
theorem Head.unused {Γ : Ctx sig} {atom : Proc Γ} (head : Head atom) :
    ScopedOpening.Vacuous (lower atom) := by
  cases head with
  | output => rw [lower_out1]; simp only [out1, ScopedOpening.Vacuous]
  | input1 => rw [lower_inp1]; simp only [inp1, ScopedOpening.Vacuous]
  | input2 => rw [lower_inp2]; simp only [receivePair, inp1, ScopedOpening.Vacuous]
  | server1 => rw [lower_rep, lower_inp1]; simp only [rep, inp1, ScopedOpening.Vacuous]
  | server2 => rw [lower_rep, lower_inp2]; simp only [rep, receivePair, inp1, ScopedOpening.Vacuous]

theorem Head.single {Γ : Ctx sig} {atom : Proc Γ} (head : Head atom) :
    ActiveOriginErasure.SingleBodies (lower atom) := by
  cases head with
  | output => rw [lower_out1]; simp only [out1, ActiveOriginErasure.SingleBodies]
  | input1 => rw [lower_inp1]; simp only [inp1, ActiveOriginErasure.SingleBodies]
  | input2 => rw [lower_inp2]; simp only [receivePair, inp1, ActiveOriginErasure.SingleBodies]
  | server1 =>
      rw [lower_rep, lower_inp1]
      simp only [rep, inp1, ActiveOriginErasure.SingleBodies,
        ActiveOriginErasure.NoActiveRep, ActiveOriginErasure.width, and_self]
  | server2 =>
      rw [lower_rep, lower_inp2]
      simp only [rep, receivePair, inp1, ActiveOriginErasure.SingleBodies,
        ActiveOriginErasure.NoActiveRep, ActiveOriginErasure.width, and_self]

def marks {Label : Type} {Γ : Ctx sig} (labels : Nat → Label) :
    Nat → List (Proc Γ) → ActiveMarking.Tree Label
  | _, [] => .nil
  | index, first :: rest => .par (ActiveSyntaxMarking.mark (labels index) (lower first))
      (marks labels (index + 1) rest)

theorem marks_fits {Label : Type} {Γ : Ctx sig} (labels : Nat → Label)
    (index : Nat) (atoms : List (Proc Γ)) :
    Fits (marks labels index atoms) (parallel (atoms.map lower)) := by
  induction atoms generalizing index with
  | nil => exact .nil
  | cons first rest ih => exact .par (ActiveSyntaxMarking.mark_fits _ _) (ih (index + 1))

theorem parallel_lower {Γ : Ctx sig} (atoms : List (Proc Γ)) :
    parallel (atoms.map lower) = lower (parallel atoms) := by
  induction atoms with
  | nil => exact lower_nil.symm
  | cons first rest ih => simp only [List.map_cons, parallel, lower_par, ih]

theorem unused {Γ : Ctx sig} (atoms : List (Proc Γ))
    (heads : ∀ atom ∈ atoms, Head atom) : ScopedOpening.Vacuous (lower (parallel atoms)) := by
  induction atoms with
  | nil => change ScopedOpening.Vacuous (lower nil); rw [lower_nil]; simp only [nil, ScopedOpening.Vacuous]
  | cons first rest ih =>
      rw [parallel, lower_par]
      simp only [par, ScopedOpening.Vacuous]
      exact ⟨(heads first (List.mem_cons_self)).unused,
        ih (fun atom member => heads atom (List.mem_cons_of_mem _ member))⟩

theorem single {Γ : Ctx sig} (atoms : List (Proc Γ))
    (heads : ∀ atom ∈ atoms, Head atom) : ActiveOriginErasure.SingleBodies (lower (parallel atoms)) := by
  induction atoms with
  | nil => change ActiveOriginErasure.SingleBodies (lower nil); rw [lower_nil]; simp only [nil, ActiveOriginErasure.SingleBodies]
  | cons first rest ih =>
      rw [parallel, lower_par]
      simp only [par, ActiveOriginErasure.SingleBodies]
      exact ⟨(heads first (List.mem_cons_self)).single,
        ih (fun atom member => heads atom (List.mem_cons_of_mem _ member))⟩

/-- The target's unary header retains which actual source prefix produced
it. In particular, a binary decoder is not read back as a unary listener. -/
inductive Reading {Label : Type} {Γ Ω : Ctx sig} (origin : Label)
    (environment : Ren sig Γ Ω) : Proc Γ → Observation Label Ω → Prop where
  | output (channel datum : Name Γ) : Reading origin environment (out1 channel datum)
      (output1 origin channel datum environment)
  | input1 (channel : Name Γ) (body : Proc (.nm :: Γ)) :
      Reading origin environment (inp1 channel body)
        (input1 origin channel (lower body) environment)
  | input2 (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
      Reading origin environment (inp2 channel body)
        (input1 origin channel
          (nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields (lower body)))) environment)
  | server1 (channel : Name Γ) (body : Proc (.nm :: Γ)) :
      Reading origin environment (rep (inp1 channel body))
        (input1 origin channel (lower body) environment)
  | server2 (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
      Reading origin environment (rep (inp2 channel body))
        (input1 origin channel
          (nu (par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields (lower body)))) environment)

theorem observed_head {Label : Type} {Γ Ω : Ctx sig} (origin : Label)
    (binderName : Label → Var Ω .nm) (environment : Ren sig Γ Ω)
    {atom : Proc Γ} (head : Head atom) (observation : Observation Label Ω)
    (member : observation ∈ observe binderName (ActiveSyntaxMarking.mark origin (lower atom))
      (lower atom) environment) : Reading origin environment atom observation := by
  cases head with
  | output channel datum =>
      rw [lower_out1] at member
      simp only [ActiveSyntaxMarking.mark, out1, observe, Set.mem_singleton_iff] at member
      subst observation
      exact .output channel datum
  | input1 channel body =>
      rw [lower_inp1] at member
      simp only [ActiveSyntaxMarking.mark, inp1, observe, Set.mem_singleton_iff] at member
      subst observation
      exact .input1 channel _
  | input2 channel body =>
      rw [lower_inp2] at member
      simp only [receivePair, ActiveSyntaxMarking.mark, inp1, observe, Set.mem_singleton_iff] at member
      subst observation
      exact .input2 channel _
  | server1 channel body =>
      rw [lower_rep, lower_inp1] at member
      simp only [ActiveSyntaxMarking.mark, rep, inp1, observe, Set.mem_singleton_iff] at member
      subst observation
      exact .server1 channel _
  | server2 channel body =>
      rw [lower_rep, lower_inp2] at member
      simp only [receivePair, ActiveSyntaxMarking.mark, rep, inp1, observe, Set.mem_singleton_iff] at member
      subst observation
      exact .server2 channel _

theorem observe_parallel {Label : Type} {Γ Ω : Ctx sig} (labels : Nat → Label)
    (binderName : Label → Var Ω .nm) (environment : Ren sig Γ Ω)
    (index : Nat) (atoms : List (Proc Γ)) (observation : Observation Label Ω) :
    observation ∈ observe binderName (marks labels index atoms)
        (parallel (atoms.map lower)) environment ↔
      ∃ position : Fin atoms.length,
        observation ∈ observe binderName
          (ActiveSyntaxMarking.mark (labels (index + position.val)) (lower atoms[position.val]))
          (lower atoms[position.val]) environment := by
  induction atoms generalizing index with
  | nil =>
      simp only [List.map_nil, marks, parallel, nil, observe, Set.mem_empty_iff_false]
      exact ⟨False.elim, fun ⟨position, _⟩ => Fin.elim0 position⟩
  | cons first rest ih =>
      simp only [List.map_cons, marks, parallel, par, observe, Set.mem_union, ih]
      constructor
      · rintro (member | ⟨position, member⟩)
        · exact ⟨⟨0, Nat.succ_pos _⟩, by simpa only [Nat.add_zero, List.getElem_cons_zero] using member⟩
        · exact ⟨position.succ, by simpa only [Fin.val_succ, List.getElem_cons_succ,
            Nat.add_assoc, Nat.add_comm 1 position.val] using member⟩
      · rintro ⟨position, member⟩
        cases position using Fin.cases with
        | zero => exact Or.inl (by simpa only [Fin.val_zero, Nat.add_zero, List.getElem_cons_zero] using member)
        | succ position =>
            exact Or.inr ⟨position, by simpa only [Fin.val_succ, List.getElem_cons_succ,
              Nat.add_assoc, Nat.add_comm 1 position.val] using member⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.IdleFrame
