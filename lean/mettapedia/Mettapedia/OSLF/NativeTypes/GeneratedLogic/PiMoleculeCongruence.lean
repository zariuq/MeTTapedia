import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeHarmony
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EarlyTransitions

/-!
# Molecules up to congruence

Molecules that differ by a guarded process replaced with a congruent one, by an unused restricted name, or by a
replicated input unfolded once, communicate alike: an internal communication of one is matched by one of the other,
with results denoting congruent processes.

- **Related guarded processes** (`PrimeRel`): equal, or receivers of the same kind on the same channel whose
  continuations are congruent for every received name; related guarded processes are congruent
  (`PrimeRel.congruent`).
- **What a communication leaves** (`result_congruent`): the result of an internal communication denotes the
  molecule's scope over the rest beside what the receiver became.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners

open Mettapedia.Languages.ProcessCalculi.PiCalculus

/-! ## Related guarded processes -/

/-- **Related guarded processes**: equal, or receivers of the same kind on the same channel whose continuations are
congruent for every received name. -/
inductive PrimeRel : Prime → Prime → Prop
  | refl (prime : Prime) : PrimeRel prime prime
  | input {x binder binder' : Name} {body body' : Process}
      (continuations : ∀ payload, Congruent (body.substitute binder payload) (body'.substitute binder' payload)) :
      PrimeRel ⟨.input x binder body, .input _ _ _⟩ ⟨.input x binder' body', .input _ _ _⟩
  | replicate {x binder binder' : Name} {body body' : Process}
      (continuations : ∀ payload, Congruent (body.substitute binder payload) (body'.substitute binder' payload)) :
      PrimeRel ⟨.replicate x binder body, .replicate _ _ _⟩ ⟨.replicate x binder' body', .replicate _ _ _⟩

theorem PrimeRel.symm {first second : Prime} (related : PrimeRel first second) : PrimeRel second first := by
  cases related with
  | refl => exact .refl _
  | input continuations => exact .input fun payload => (continuations payload).symm
  | replicate continuations => exact .replicate fun payload => (continuations payload).symm

/-- A binder renamed to a fresh name is α-conversion, so congruent continuations under every name make congruent
receivers. -/
theorem binder_congruent {binder binder' : Name} {body body' : Process}
    (continuations : ∀ payload, Congruent (body.substitute binder payload) (body'.substitute binder' payload))
    (build : Name → Process → Process)
    (alpha : ∀ {old new : Name} {inner : Process}, new ∉ inner.freeNames → new ≠ old →
      Congruent (build old inner) (build new (inner.substitute old new)))
    (cong : ∀ {name : Name} {first second : Process}, Congruent first second →
      Congruent (build name first) (build name second)) :
    Congruent (build binder body) (build binder' body') := by
  obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ body'.freeNames ∪ {binder, binder'})
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at freshNot
  obtain ⟨⟨notBody, notBody'⟩, notBinder, notBinder'⟩ := freshNot
  exact (alpha notBody notBinder).trans ((cong (continuations fresh)).trans (alpha notBody' notBinder').symm)

/-- **Related guarded processes are congruent.** -/
theorem PrimeRel.congruent {first second : Prime} (related : PrimeRel first second) : Congruent first.1 second.1 := by
  cases related with
  | refl => exact Congruent.refl _
  | @input x binder binder' body body' continuations =>
    exact binder_congruent continuations (fun name inner => .input x name inner)
      (fun notFree different => ⟨.alpha_input _ _ _ _ notFree different⟩) (Congruent.input _ _)
  | @replicate x binder binder' body body' continuations =>
    exact binder_congruent continuations (fun name inner => .replicate x name inner)
      (fun notFree different => ⟨.alpha_replicate _ _ _ _ notFree different⟩) (Congruent.replicate _ _)

/-! ## What a communication leaves -/

/-- A communication's continuation with what the receiver keeps is what the receiver becomes. -/
theorem fires_receive {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
    (fires : Fires receiver sender continuation kept) :
    ∃ (x payload : Name) (keptPrimes : List Prime), sender.1 = .output x payload ∧ ReceivesOn x receiver.1 ∧
      (keptPrimes : Multiset Prime) = kept ∧ (∀ prime ∈ keptPrimes, prime = receiver) ∧
      Congruent (.par continuation (parList (keptPrimes.map Subtype.val))) (receive receiver.1 payload) := by
  cases fires with
  | input x binder payload body =>
    exact ⟨x, payload, [], rfl, Or.inl ⟨binder, body, rfl⟩, rfl, by simp, Congruent.nilRight _⟩
  | replicate x binder payload body =>
    exact ⟨x, payload, [⟨.replicate x binder body, .replicate _ _ _⟩], rfl, Or.inr ⟨binder, body, rfl⟩, rfl, by simp,
      Congruent.par (Congruent.refl _) (Congruent.nilRight _)⟩

/-- **The result of an internal communication** denotes the molecule's scope over the rest beside what the receiver
became. -/
theorem result_congruent {molecule : Molecule} {receiver sender : Prime} {continuation : Process}
    {kept : Multiset Prime} {lifted : Finset Name} {components : Multiset Prime}
    (contained : {receiver, sender} ≤ molecule.body) (fires : Fires receiver sender continuation kept)
    (lifts : Lifts continuation lifted components) (fresh : Disjoint lifted (molecule.scope ∪ molecule.bodyNames))
    {names : List Name} {rest : List Prime} (nodup : names.Nodup) (scopeEq : names.toFinset = molecule.scope)
    (restEq : (rest : Multiset Prime) = molecule.body - {receiver, sender}) {x payload : Name}
    (sends : sender.1 = .output x payload) {process : Process}
    (denotes : Denotes ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩ process) :
    Congruent process (nuList names (.par (parList (rest.map Subtype.val)) (receive receiver.1 payload))) := by
  obtain ⟨x', payload', keptPrimes, sends', _, keptEq, keptIsReceiver, receives⟩ := fires_receive fires
  rw [sends] at sends'
  obtain ⟨rfl, rfl⟩ : x = x' ∧ payload = payload' := by simpa using sends'
  obtain ⟨liftedNames, liftedPrimes, liftedNodup, liftedScope, liftedBody, continuationCongruent⟩ :=
    lifts_congruent lifts
  have receiverMem : receiver ∈ molecule.body := Multiset.subset_of_le contained (by simp)
  have restProcess : ∀ name ∈ (parList (rest.map Subtype.val)).freeNames, name ∈ molecule.bodyNames := by
    intro name inside
    obtain ⟨process, processMem, present⟩ := mem_freeNames_parList.mp inside
    obtain ⟨prime, primeMem, rfl⟩ := List.mem_map.mp processMem
    have : prime ∈ molecule.body := Multiset.mem_of_le (Multiset.sub_le_self _ _) (restEq ▸ Multiset.mem_coe.mpr primeMem)
    exact Molecule.mem_bodyNames.mpr ⟨prime, this, present⟩
  have keptProcess : ∀ name ∈ (parList (keptPrimes.map Subtype.val)).freeNames, name ∈ molecule.bodyNames := by
    intro name inside
    obtain ⟨process, processMem, present⟩ := mem_freeNames_parList.mp inside
    obtain ⟨prime, primeMem, rfl⟩ := List.mem_map.mp processMem
    obtain rfl := keptIsReceiver prime primeMem
    exact Molecule.mem_bodyNames.mpr ⟨_, receiverMem, present⟩
  have outside : Disjoint liftedNames.toFinset
      (Process.par (parList (rest.map Subtype.val)) (parList (keptPrimes.map Subtype.val))).freeNames := by
    refine Finset.disjoint_left.mpr fun name member inside => ?_
    rw [liftedScope] at member
    simp only [Process.freeNames, Finset.mem_union] at inside
    rcases inside with inRest | inKept
    · exact Finset.disjoint_left.mp fresh member (Finset.mem_union_right _ (restProcess name inRest))
    · exact Finset.disjoint_left.mp fresh member (Finset.mem_union_right _ (keptProcess name inKept))
  have explicit : Denotes ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩
      (nuList (names ++ liftedNames) (parList ((rest ++ keptPrimes ++ liftedPrimes).map Subtype.val))) := by
    refine ⟨names ++ liftedNames, rest ++ keptPrimes ++ liftedPrimes, ?_, ?_, ?_, rfl⟩
    · refine List.nodup_append.mpr ⟨nodup, liftedNodup, fun name inside other liftedInside same => ?_⟩
      subst same
      exact Finset.disjoint_left.mp fresh (liftedScope ▸ List.mem_toFinset.mpr liftedInside)
        (Finset.mem_union_left _ (scopeEq ▸ List.mem_toFinset.mpr inside))
    · rw [List.toFinset_append, scopeEq, liftedScope]
    · rw [← Multiset.coe_add, ← Multiset.coe_add, restEq, keptEq, liftedBody]
  refine (denotes_congruent denotes explicit).trans ?_
  rw [nuList_append]
  refine nuList_congruent names ?_
  refine Congruent.symm ((Congruent.par (Congruent.refl _) receives.symm).trans ?_)
  refine (Congruent.par (Congruent.refl _) (Congruent.par continuationCongruent (Congruent.refl _))).trans ?_
  refine (Congruent.par (Congruent.refl _) (Congruent.comm _ _)).trans ((Congruent.assoc _ _ _).symm.trans
    ((Congruent.comm _ _).trans ((nuList_extrude outside).trans (nuList_congruent _ ?_))))
  rw [List.map_append, List.map_append]
  exact (Congruent.comm _ _).trans ((Congruent.par (parList_append _ _).symm (Congruent.refl _)).trans
    (parList_append _ _).symm)

/-! ## Replacing a guarded process -/

theorem receive_congruent {first second : Prime} (related : PrimeRel first second) (payload : Name) :
    Congruent (receive first.1 payload) (receive second.1 payload) := by
  cases related with
  | refl => exact Congruent.refl _
  | input continuations => exact continuations payload
  | replicate continuations =>
    exact Congruent.par (continuations payload) (PrimeRel.congruent (.replicate continuations))

theorem bodyNames_replace {scope : Finset Name} {body : Multiset Prime} {first second : Prime}
    (same : first.1.freeNames = second.1.freeNames) :
    (Molecule.mk scope (body + {first})).bodyNames = (Molecule.mk scope (body + {second})).bodyNames := by
  ext name
  simp only [Molecule.mem_bodyNames, Multiset.mem_add, Multiset.mem_singleton]
  constructor
  · rintro ⟨prime, (inBody | rfl), present⟩
    · exact ⟨prime, Or.inl inBody, present⟩
    · exact ⟨second, Or.inr rfl, same ▸ present⟩
  · rintro ⟨prime, (inBody | rfl), present⟩
    · exact ⟨prime, Or.inl inBody, present⟩
    · exact ⟨first, Or.inr rfl, same.symm ▸ present⟩

/-- Molecules differing by one guarded process replaced with a congruent one denote congruent processes. -/
theorem denotes_replace {scope : Finset Name} {body : Multiset Prime} {first second : Prime}
    (congruent : Congruent first.1 second.1) {process process' : Process}
    (denotes : Denotes ⟨scope, body + {first}⟩ process) (denotes' : Denotes ⟨scope, body + {second}⟩ process') :
    Congruent process process' := by
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := denotes
  have explicit : Denotes ⟨scope, body + {first}⟩ (nuList names (parList ((body.toList ++ [first]).map Subtype.val))) :=
    ⟨names, body.toList ++ [first], nodup, scopeEq,
      by rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_singleton], rfl⟩
  have explicit' : Denotes ⟨scope, body + {second}⟩
      (nuList names (parList ((body.toList ++ [second]).map Subtype.val))) :=
    ⟨names, body.toList ++ [second], nodup, scopeEq,
      by rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_singleton], rfl⟩
  refine (denotes_congruent ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ explicit).trans
    ((nuList_congruent _ (parList_forall₂ ?_)).trans (denotes_congruent explicit' denotes'))
  simp only [List.map_append, List.map_cons, List.map_nil]
  generalize body.toList.map Subtype.val = processes
  induction processes with
  | nil => exact .cons congruent .nil
  | cons head tail holds => exact .cons (Congruent.refl head) holds

theorem pair_le_add_singleton {body : Multiset Prime} {extra receiver sender : Prime}
    (contained : {receiver, sender} ≤ body + {extra}) (notWithin : ¬ {receiver, sender} ≤ body) :
    (receiver = extra ∧ sender ∈ body) ∨ (sender = extra ∧ receiver ∈ body) := by
  rw [Multiset.le_iff_count] at contained
  have notCount : ∃ prime, body.count prime < ({receiver, sender} : Multiset Prime).count prime := by
    by_contra none
    simp only [not_exists, not_lt] at none
    exact notWithin (Multiset.le_iff_count.mpr none)
  obtain ⟨prime, fewer⟩ := notCount
  have bound := contained prime
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Multiset.count_add] at fewer bound
  by_cases isExtra : prime = extra
  · subst isExtra
    by_cases isReceiver : receiver = prime
    · subst isReceiver
      left
      refine ⟨rfl, ?_⟩
      by_cases isSender : sender = receiver
      · subst isSender
        simp at fewer bound
        exact Multiset.one_le_count_iff_mem.mp (by omega)
      · have := contained sender
        simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Multiset.count_add,
          if_neg isSender] at this
        exact Multiset.one_le_count_iff_mem.mp (by simpa using this)
    · right
      have isSender : sender = prime := by
        by_contra different
        simp [Ne.symm isReceiver, Ne.symm different] at fewer
      subst isSender
      refine ⟨rfl, ?_⟩
      have := contained receiver
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, Multiset.count_add,
        if_neg isReceiver] at this
      exact Multiset.one_le_count_iff_mem.mp (by simpa using this)
  · simp [isExtra] at bound
    omega

theorem add_singleton_sub_pair (body : Multiset Prime) (extra sender : Prime) :
    body + {extra} - {extra, sender} = body - {sender} := by
  rw [Multiset.insert_eq_cons, Multiset.sub_cons, Multiset.add_comm, Multiset.singleton_add,
    Multiset.erase_cons_head]

theorem add_singleton_sub_pair' (body : Multiset Prime) (extra receiver : Prime) :
    body + {extra} - {receiver, extra} = body - {receiver} := by
  have swap : ({receiver, extra} : Multiset Prime) = {extra, receiver} := by
    simp only [Multiset.insert_eq_cons]
    exact Multiset.cons_swap _ _ _
  rw [swap, add_singleton_sub_pair]

/-- Internal communications matched, with results denoting congruent processes. -/
def InternalSim (first second : Molecule) : Prop :=
  ∀ result, Internal first result →
    ∃ result', Internal second result' ∧ ∃ process process', Denotes result process ∧ Denotes result' process' ∧
      Congruent process process'

theorem receivesOn_of_primeRel {first second : Prime} (related : PrimeRel first second) {x : Name}
    (receives : ReceivesOn x first.1) : ReceivesOn x second.1 := by
  cases related with
  | refl => exact receives
  | input =>
    rcases receives with ⟨_, _, same⟩ | ⟨_, _, same⟩ <;> simp only [Process.input.injEq, reduceCtorEq] at same
    obtain ⟨rfl, -⟩ := same
    exact Or.inl ⟨_, _, rfl⟩
  | replicate =>
    rcases receives with ⟨_, _, same⟩ | ⟨_, _, same⟩ <;> simp only [Process.replicate.injEq, reduceCtorEq] at same
    obtain ⟨rfl, -⟩ := same
    exact Or.inr ⟨_, _, rfl⟩

theorem eq_of_primeRel_output {first second : Prime} (related : PrimeRel first second) {x payload : Name}
    (sends : first.1 = .output x payload) : second = first := by
  cases related with
  | refl => rfl
  | input => simp at sends
  | replicate => simp at sends

/-- A result denoting by the molecule's scope and rest. -/
theorem result_denotes (scope : Finset Name) (rest : Multiset Prime) :
    ∃ (names : List Name) (restList : List Prime), names.Nodup ∧ names.toFinset = scope ∧
      (restList : Multiset Prime) = rest :=
  ⟨scope.toList, rest.toList, scope.nodup_toList, by simp, by simp⟩

/-- **Replacing a guarded process with a related one** keeps the internal communications. -/
theorem internal_prime {scope : Finset Name} {body : Multiset Prime} {first second : Prime}
    (related : PrimeRel first second) : InternalSim ⟨scope, body + {first}⟩ ⟨scope, body + {second}⟩ := by
  intro result internal
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts fresh =>
  have sameNames : first.1.freeNames = second.1.freeNames := (PrimeRel.congruent related).freeNames_eq
  have bodyNamesEq := bodyNames_replace (scope := scope) (body := body) sameNames
  by_cases within : {receiver, sender} ≤ body
  · refine ⟨⟨scope ∪ lifted, body + {second} - {receiver, sender} + kept + components⟩,
      .comm (within.trans (Multiset.le_add_right _ _)) fires lifts ?_, ?_⟩
    · have := fresh
      simp only at this ⊢
      rwa [← bodyNamesEq]
    · obtain ⟨process, denotes⟩ := denotes_exists ⟨scope ∪ lifted, body + {first} - {receiver, sender} + kept + components⟩
      obtain ⟨process', denotes'⟩ :=
        denotes_exists ⟨scope ∪ lifted, body + {second} - {receiver, sender} + kept + components⟩
      refine ⟨process, process', denotes, denotes', ?_⟩
      have arrange : ∀ extra : Prime, body + {extra} - {receiver, sender} + kept + components =
          (body - {receiver, sender} + kept + components) + {extra} := fun extra => by
        rw [← tsub_add_eq_add_tsub within]
        ac_rfl
      rw [arrange] at denotes denotes'
      exact denotes_replace (PrimeRel.congruent related) denotes denotes'
  · rcases pair_le_add_singleton contained within with ⟨rfl, senderMem⟩ | ⟨rfl, receiverMem⟩
    · obtain ⟨x, payload, keptPrimes, sends, receives, _, _, _⟩ := fires_receive fires
      have receives' := receivesOn_of_primeRel related receives
      obtain ⟨continuation', kept', fires'⟩ := fires_of receives' (show SendsOn x sender.1 from ⟨payload, sends⟩)
      obtain ⟨lifted', components', lifts', fresh'⟩ := lifts_exists _ continuation' le_rfl
        (scope ∪ (Molecule.mk scope (body + {second})).bodyNames)
      have contained' : {second, sender} ≤ body + {second} := by
        rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
        exact add_le_add (Multiset.singleton_le.mpr senderMem) le_rfl
      refine ⟨_, .comm contained' fires' lifts' fresh', ?_⟩
      obtain ⟨names, restList, nodup, scopeEq, restEq⟩ := result_denotes scope (body - {sender})
      obtain ⟨process, denotes⟩ := denotes_exists ⟨scope ∪ lifted, body + {receiver} - {receiver, sender} + kept + components⟩
      obtain ⟨process', denotes'⟩ :=
        denotes_exists ⟨scope ∪ lifted', body + {second} - {second, sender} + kept' + components'⟩
      refine ⟨process, process', denotes, denotes', ?_⟩
      have restFirst : (restList : Multiset Prime) = body + {receiver} - {receiver, sender} := by
        rw [restEq, add_singleton_sub_pair]
      have restSecond : (restList : Multiset Prime) = body + {second} - {second, sender} := by
        rw [restEq, add_singleton_sub_pair]
      have contained1 : {receiver, sender} ≤ (Molecule.mk scope (body + {receiver})).body := contained
      have fresh1 : Disjoint lifted ((Molecule.mk scope (body + {receiver})).scope ∪
          (Molecule.mk scope (body + {receiver})).bodyNames) := fresh
      have scope1 : names.toFinset = (Molecule.mk scope (body + {receiver})).scope := scopeEq
      have rest1 : (restList : Multiset Prime) = (Molecule.mk scope (body + {receiver})).body - {receiver, sender} :=
        restFirst
      have denotes1 : Denotes ⟨(Molecule.mk scope (body + {receiver})).scope ∪ lifted,
          (Molecule.mk scope (body + {receiver})).body - {receiver, sender} + kept + components⟩ process := denotes
      have before : Congruent process (nuList names (.par (parList (restList.map Subtype.val))
          (receive receiver.1 payload))) :=
        result_congruent contained1 fires lifts fresh1 nodup scope1 rest1 sends denotes1
      have contained2 : {second, sender} ≤ (Molecule.mk scope (body + {second})).body := contained'
      have fresh2 : Disjoint lifted' ((Molecule.mk scope (body + {second})).scope ∪
          (Molecule.mk scope (body + {second})).bodyNames) := fresh'
      have scope2 : names.toFinset = (Molecule.mk scope (body + {second})).scope := scopeEq
      have rest2 : (restList : Multiset Prime) = (Molecule.mk scope (body + {second})).body - {second, sender} :=
        restSecond
      have denotes2 : Denotes ⟨(Molecule.mk scope (body + {second})).scope ∪ lifted',
          (Molecule.mk scope (body + {second})).body - {second, sender} + kept' + components'⟩ process' := denotes'
      have after : Congruent process' (nuList names (.par (parList (restList.map Subtype.val))
          (receive second.1 payload))) :=
        result_congruent contained2 fires' lifts' fresh2 nodup scope2 rest2 sends denotes2
      exact before.trans ((nuList_congruent _ (Congruent.par (Congruent.refl _)
        (receive_congruent related payload))).trans after.symm)
    · obtain ⟨x, payload, keptPrimes, sends, _, _, _, _⟩ := fires_receive fires
      obtain rfl := eq_of_primeRel_output related sends
      obtain ⟨process, denotes⟩ := denotes_exists ⟨scope ∪ lifted, body + {second} - {receiver, second} + kept + components⟩
      exact ⟨_, .comm contained fires lifts fresh, process, process, denotes, denotes, Congruent.refl _⟩

/-! ## Unfolding a replicated input -/

/-- The replicated input and its one-shot copy. -/
def server (x binder : Name) (body : Process) : Prime := ⟨.replicate x binder body, .replicate _ _ _⟩
def copy (x binder : Name) (body : Process) : Prime := ⟨.input x binder body, .input _ _ _⟩

/-- A molecule with a replicated input denotes what it denotes with a copy of it beside. -/
theorem denotes_unfold {scope : Finset Name} {body : Multiset Prime} {x binder : Name} {inner : Process}
    {process process' : Process} (denotes : Denotes ⟨scope, body + {server x binder inner}⟩ process)
    (denotes' : Denotes ⟨scope, body + {copy x binder inner, server x binder inner}⟩ process') :
    Congruent process process' := by
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := denotes
  have explicit : Denotes ⟨scope, body + {server x binder inner}⟩
      (nuList names (parList ((body.toList ++ [server x binder inner]).map Subtype.val))) :=
    ⟨names, _, nodup, scopeEq, by rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_singleton], rfl⟩
  have explicit' : Denotes ⟨scope, body + {copy x binder inner, server x binder inner}⟩
      (nuList names (parList ((body.toList ++ [copy x binder inner, server x binder inner]).map Subtype.val))) :=
    ⟨names, _, nodup, scopeEq, by
      rw [← Multiset.coe_add, Multiset.coe_toList]
      rfl, rfl⟩
  refine (denotes_congruent ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ explicit).trans
    ((nuList_congruent _ ?_).trans (denotes_congruent explicit' denotes'))
  simp only [List.map_append, List.map_cons, List.map_nil]
  refine (parList_append _ _).trans ((Congruent.par (Congruent.refl _) ?_).trans (parList_append _ _).symm)
  simp only [parList, server, copy]
  exact (Congruent.nilRight _).trans (Congruent.trans ⟨.replicate_unfold _ _ _⟩
    (Congruent.par (Congruent.refl _) (Congruent.nilRight _).symm))

theorem bodyNames_unfold (scope : Finset Name) (body : Multiset Prime) (x binder : Name) (inner : Process) :
    (Molecule.mk scope (body + {copy x binder inner, server x binder inner})).bodyNames =
      (Molecule.mk scope (body + {server x binder inner})).bodyNames := by
  ext name
  simp only [Molecule.mem_bodyNames, Multiset.mem_add, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton]
  constructor
  · rintro ⟨prime, (inBody | rfl | rfl), present⟩
    · exact ⟨prime, Or.inl inBody, present⟩
    · exact ⟨server x binder inner, Or.inr rfl, by simpa [copy, server, Process.freeNames] using present⟩
    · exact ⟨_, Or.inr rfl, present⟩
  · rintro ⟨prime, (inBody | rfl), present⟩
    · exact ⟨prime, Or.inl inBody, present⟩
    · exact ⟨_, Or.inr (Or.inr rfl), present⟩

theorem unfold_rest {body : Multiset Prime} {x binder : Name} {inner : Process} {sender : Prime}
    (senderMem : sender ∈ body) :
    body + {copy x binder inner, server x binder inner} - {copy x binder inner, sender} =
      body - {sender} + {server x binder inner} := by
  have regroup : body + {copy x binder inner, server x binder inner} =
      body + {server x binder inner} + {copy x binder inner} := by
    simp only [Multiset.insert_eq_cons]
    rw [add_assoc, ← Multiset.singleton_add, add_comm ({server x binder inner} : Multiset Prime)]
  rw [regroup, add_singleton_sub_pair, tsub_add_eq_add_tsub (Multiset.singleton_le.mpr senderMem)]

theorem server_not_sender {sender : Prime} {x binder : Name} {inner : Process} {x' payload : Name}
    (sends : sender.1 = .output x' payload) : sender ≠ server x binder inner := fun same => by
  subst same
  simp [server] at sends

theorem copy_not_sender {sender : Prime} {x binder : Name} {inner : Process} {x' payload : Name}
    (sends : sender.1 = .output x' payload) : sender ≠ copy x binder inner := fun same => by
  subst same
  simp [copy] at sends

/-- **Unfolding a replicated input** keeps the internal communications. -/
theorem internal_unfold {scope : Finset Name} {body : Multiset Prime} {x binder : Name} {inner : Process} :
    InternalSim ⟨scope, body + {server x binder inner}⟩ ⟨scope, body + {copy x binder inner, server x binder inner}⟩ := by
  intro result internal
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts fresh =>
  have namesEq := bodyNames_unfold scope body x binder inner
  have fresh' : Disjoint lifted ((Molecule.mk scope (body + {copy x binder inner, server x binder inner})).scope ∪
      (Molecule.mk scope (body + {copy x binder inner, server x binder inner})).bodyNames) := by
    rw [namesEq]; exact fresh
  obtain ⟨_, _, _, sends, _, _, _, _⟩ := fires_receive fires
  by_cases within : {receiver, sender} ≤ body
  · have contained' : {receiver, sender} ≤ (Molecule.mk scope (body + {copy x binder inner, server x binder inner})).body :=
      within.trans (Multiset.le_add_right _ _)
    refine ⟨_, .comm contained' fires lifts fresh', ?_⟩
    obtain ⟨process, denotes⟩ :=
      denotes_exists ⟨scope ∪ lifted, body + {server x binder inner} - {receiver, sender} + kept + components⟩
    obtain ⟨process', denotes'⟩ := denotes_exists
      ⟨scope ∪ lifted, body + {copy x binder inner, server x binder inner} - {receiver, sender} + kept + components⟩
    refine ⟨process, process', denotes, denotes', ?_⟩
    have arrange : body + {server x binder inner} - {receiver, sender} + kept + components =
        (body - {receiver, sender} + kept + components) + {server x binder inner} := by
      rw [← tsub_add_eq_add_tsub within]; ac_rfl
    have arrange' : body + {copy x binder inner, server x binder inner} - {receiver, sender} + kept + components =
        (body - {receiver, sender} + kept + components) + {copy x binder inner, server x binder inner} := by
      rw [← tsub_add_eq_add_tsub within]; ac_rfl
    rw [arrange] at denotes
    rw [arrange'] at denotes'
    exact denotes_unfold denotes denotes'
  · rcases pair_le_add_singleton contained within with ⟨rfl, senderMem⟩ | ⟨rfl, _⟩
    · cases fires with
      | replicate _ _ payload _ =>
        have contained' : {copy x binder inner, ⟨.output x payload, .output _ _⟩} ≤
            (Molecule.mk scope (body + {copy x binder inner, server x binder inner})).body := by
          have left : ({copy x binder inner, ⟨.output x payload, .output _ _⟩} : Multiset Prime) =
              {copy x binder inner} + {⟨.output x payload, .output _ _⟩} := by
            simp only [Multiset.insert_eq_cons, Multiset.singleton_add]
          have right : body + {copy x binder inner, server x binder inner} =
              {copy x binder inner} + (body + {server x binder inner}) := by
            simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
            ac_rfl
          simp only
          rw [left, right]
          exact add_le_add le_rfl (Multiset.singleton_le.mpr (Multiset.mem_add.mpr (Or.inl senderMem)))
        refine ⟨_, .comm contained' (.input x binder payload inner) lifts fresh', ?_⟩
        obtain ⟨process, denotes⟩ := denotes_exists ⟨scope ∪ lifted, body + {server x binder inner} -
          {server x binder inner, ⟨.output x payload, .output _ _⟩} + {server x binder inner} + components⟩
        refine ⟨process, process, denotes, ?_, Congruent.refl _⟩
        have same : body + {copy x binder inner, server x binder inner} -
            {copy x binder inner, ⟨.output x payload, .output _ _⟩} + 0 + components =
            body + {server x binder inner} - {server x binder inner, ⟨.output x payload, .output _ _⟩} +
              {server x binder inner} + components := by
          rw [unfold_rest senderMem, add_singleton_sub_pair, add_zero]
        simp only at same ⊢
        rw [same]
        exact denotes
    · exact absurd rfl (server_not_sender sends)

theorem server_mem_rest {body kept : Multiset Prime} {receiver sender : Prime} {x binder : Name} {inner : Process}
    {continuation : Process} (fires : Fires receiver sender continuation kept)
    {x' payload : Name} (sends : sender.1 = .output x' payload) :
    server x binder inner ∈ body + {server x binder inner} - {receiver, sender} + kept := by
  by_cases isReceiver : receiver = server x binder inner
  · subst isReceiver
    cases fires with
    | replicate => exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
  · refine Multiset.mem_add.mpr (Or.inl ?_)
    rw [← Multiset.one_le_count_iff_mem, Multiset.count_sub, Multiset.count_add, Multiset.insert_eq_cons,
      Multiset.count_cons, Multiset.count_singleton, Multiset.count_singleton, if_neg (Ne.symm isReceiver),
      if_neg (Ne.symm (server_not_sender sends))]
    simp

/-- **Folding a replicated input's copy back** keeps the internal communications. -/
theorem internal_fold {scope : Finset Name} {body : Multiset Prime} {x binder : Name} {inner : Process} :
    InternalSim ⟨scope, body + {copy x binder inner, server x binder inner}⟩ ⟨scope, body + {server x binder inner}⟩ := by
  intro result internal
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts fresh =>
  have namesEq := bodyNames_unfold scope body x binder inner
  have fresh' : Disjoint lifted ((Molecule.mk scope (body + {server x binder inner})).scope ∪
      (Molecule.mk scope (body + {server x binder inner})).bodyNames) := by
    rw [← namesEq]; exact fresh
  obtain ⟨_, _, _, sends, _, _, _, _⟩ := fires_receive fires
  have regroup : body + {copy x binder inner, server x binder inner} =
      body + {server x binder inner} + {copy x binder inner} := by
    simp only [Multiset.insert_eq_cons]
    rw [add_assoc, ← Multiset.singleton_add, add_comm ({server x binder inner} : Multiset Prime)]
  have contained₀ : {receiver, sender} ≤ body + {server x binder inner} + {copy x binder inner} := by
    rw [← regroup]; exact contained
  by_cases within : {receiver, sender} ≤ body + {server x binder inner}
  · have contained' : {receiver, sender} ≤ (Molecule.mk scope (body + {server x binder inner})).body := within
    refine ⟨_, .comm contained' fires lifts fresh', ?_⟩
    obtain ⟨process, denotes⟩ := denotes_exists
      ⟨scope ∪ lifted, body + {copy x binder inner, server x binder inner} - {receiver, sender} + kept + components⟩
    obtain ⟨process', denotes'⟩ :=
      denotes_exists ⟨scope ∪ lifted, body + {server x binder inner} - {receiver, sender} + kept + components⟩
    refine ⟨process, process', denotes, denotes', ?_⟩
    set rest := body + {server x binder inner} - {receiver, sender} + kept with restDef
    have serverMem : server x binder inner ∈ rest := server_mem_rest fires sends
    have split : rest = rest.erase (server x binder inner) + {server x binder inner} := by
      rw [add_comm, Multiset.singleton_add, Multiset.cons_erase serverMem]
    have forms : body + {copy x binder inner, server x binder inner} - {receiver, sender} + kept + components =
        (rest.erase (server x binder inner) + components) + {copy x binder inner, server x binder inner} := by
      rw [regroup, ← tsub_add_eq_add_tsub within]
      have : body + {server x binder inner} - {receiver, sender} + {copy x binder inner} + kept + components =
          rest + components + {copy x binder inner} := by rw [restDef]; ac_rfl
      rw [this]
      conv_lhs => rw [split]
      simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      ac_rfl
    have forms' : body + {server x binder inner} - {receiver, sender} + kept + components =
        (rest.erase (server x binder inner) + components) + {server x binder inner} := by
      rw [← restDef]
      conv_lhs => rw [split]
      ac_rfl
    rw [forms] at denotes
    rw [forms'] at denotes'
    exact (denotes_unfold denotes' denotes).symm
  · rcases pair_le_add_singleton contained₀ within with ⟨rfl, senderMem⟩ | ⟨rfl, _⟩
    · have senderBody : sender ∈ body := by
        rcases Multiset.mem_add.mp senderMem with inBody | isServer
        · exact inBody
        · exact absurd (Multiset.mem_singleton.mp isServer) (server_not_sender sends)
      cases fires with
      | input _ _ payload _ =>
        have contained' : {server x binder inner, ⟨.output x payload, .output _ _⟩} ≤
            (Molecule.mk scope (body + {server x binder inner})).body := by
          have left : ({server x binder inner, ⟨.output x payload, .output _ _⟩} : Multiset Prime) =
              {⟨.output x payload, .output _ _⟩} + {server x binder inner} := by
            simp only [Multiset.insert_eq_cons, Multiset.singleton_add]
            exact Multiset.cons_swap _ _ _
          simp only
          rw [left]
          exact add_le_add (Multiset.singleton_le.mpr senderBody) le_rfl
        refine ⟨_, .comm contained' (.replicate x binder payload inner) lifts fresh', ?_⟩
        obtain ⟨process, denotes⟩ := denotes_exists ⟨scope ∪ lifted, body + {copy x binder inner, server x binder inner} -
          {copy x binder inner, ⟨.output x payload, .output _ _⟩} + 0 + components⟩
        refine ⟨process, process, denotes, ?_, Congruent.refl _⟩
        have same : body + {server x binder inner} - {server x binder inner, ⟨.output x payload, .output _ _⟩} +
              {server x binder inner} + components =
            body + {copy x binder inner, server x binder inner} -
              {copy x binder inner, ⟨.output x payload, .output _ _⟩} + 0 + components := by
          rw [unfold_rest senderBody, add_singleton_sub_pair, add_zero]
        simp only [server, copy] at same denotes ⊢
        rw [same]
        exact denotes
    · exact absurd rfl (copy_not_sender sends)

/-! ## An unused restricted name -/

/-- **A restriction of an absent name is garbage.** -/
theorem nu_garbage {name : Name} {process : Process} (absent : name ∉ process.freeNames) :
    Congruent (.nu name process) process :=
  (Congruent.nu name (Congruent.nilLeft _).symm).trans (Congruent.trans ⟨.nu_par name .nil process absent⟩
    ((Congruent.par ⟨.nu_nil name⟩ (Congruent.refl _)).trans (Congruent.nilLeft _)))

/-- Molecules differing by an unused restricted name denote congruent processes. -/
theorem denotes_garbage {scope : Finset Name} {body : Multiset Prime} {name : Name} (absent : name ∉ scope)
    (unused : name ∉ (Molecule.mk scope body).bodyNames) {process process' : Process}
    (denotes : Denotes ⟨insert name scope, body⟩ process) (denotes' : Denotes ⟨scope, body⟩ process') :
    Congruent process process' := by
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := denotes'
  have explicit : Denotes ⟨insert name scope, body⟩ (.nu name (nuList names (parList (primes.map Subtype.val)))) :=
    ⟨name :: names, primes, List.nodup_cons.mpr ⟨fun member => absent (by
      have := List.mem_toFinset.mpr member; rw [scopeEq] at this; exact this), nodup⟩,
      by rw [List.toFinset_cons, scopeEq], bodyEq, rfl⟩
  refine (denotes_congruent denotes explicit).trans (nu_garbage ?_)
  rw [freeNames_nuList]
  intro inside
  exact unused (freeNames_parList_primes (molecule := ⟨scope, body⟩) bodyEq (Finset.mem_sdiff.mp inside).1)

/-- **Dropping an unused restricted name** keeps the internal communications. -/
theorem internal_drop {scope : Finset Name} {body : Multiset Prime} {name : Name} (absent : name ∉ scope)
    (unused : name ∉ (Molecule.mk scope body).bodyNames) :
    InternalSim ⟨insert name scope, body⟩ ⟨scope, body⟩ := by
  intro result internal
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts fresh =>
  have notLifted : name ∉ lifted := fun inside =>
    Finset.disjoint_left.mp fresh inside (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
  have fresh' : Disjoint lifted ((Molecule.mk scope body).scope ∪ (Molecule.mk scope body).bodyNames) :=
    fresh.mono_right (Finset.union_subset_union (Finset.subset_insert _ _) le_rfl)
  have contained' : {receiver, sender} ≤ (Molecule.mk scope body).body := contained
  refine ⟨_, .comm contained' fires lifts fresh', ?_⟩
  obtain ⟨process, denotes⟩ := denotes_exists ⟨insert name scope ∪ lifted, body - {receiver, sender} + kept + components⟩
  obtain ⟨process', denotes'⟩ := denotes_exists ⟨scope ∪ lifted, body - {receiver, sender} + kept + components⟩
  refine ⟨process, process', denotes, denotes', ?_⟩
  rw [Finset.insert_union] at denotes
  refine denotes_garbage (fun inside => (Finset.mem_union.mp inside).elim absent notLifted) ?_ denotes denotes'
  intro inside
  rcases Finset.mem_union.mp (bodyNames_after (molecule := ⟨scope, body⟩) contained' fires lifts _ inside) with
    named | liftedName
  · exact unused named
  · exact notLifted liftedName

/-- **Adding an unused restricted name** keeps the internal communications. -/
theorem internal_add {scope : Finset Name} {body : Multiset Prime} {name : Name} (absent : name ∉ scope)
    (unused : name ∉ (Molecule.mk scope body).bodyNames) :
    InternalSim ⟨scope, body⟩ ⟨insert name scope, body⟩ := by
  intro result internal
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts fresh =>
  obtain ⟨lifted', components', lifts', fresh'⟩ := lifts_exists _ continuation le_rfl
    ((Molecule.mk (insert name scope) body).scope ∪ (Molecule.mk (insert name scope) body).bodyNames)
  have contained' : {receiver, sender} ≤ (Molecule.mk (insert name scope) body).body := contained
  refine ⟨_, .comm contained' fires lifts' fresh', ?_⟩
  obtain ⟨x, payload, _, sends, receives, _, _, _⟩ := fires_receive fires
  obtain ⟨names, restList, nodup, scopeEq, restEq⟩ := result_denotes scope (body - {receiver, sender})
  obtain ⟨process, denotes⟩ := denotes_exists ⟨scope ∪ lifted, body - {receiver, sender} + kept + components⟩
  obtain ⟨process', denotes'⟩ :=
    denotes_exists ⟨insert name scope ∪ lifted', body - {receiver, sender} + kept + components'⟩
  refine ⟨process, process', denotes, denotes', ?_⟩
  have nameOut : name ∉ names := fun member => absent (scopeEq ▸ List.mem_toFinset.mpr member)
  have scope1 : names.toFinset = (Molecule.mk scope body).scope := scopeEq
  have scope2 : (name :: names).toFinset = (Molecule.mk (insert name scope) body).scope := by
    rw [List.toFinset_cons, scopeEq]
  have rest1 : (restList : Multiset Prime) = (Molecule.mk scope body).body - {receiver, sender} := restEq
  have rest2 : (restList : Multiset Prime) = (Molecule.mk (insert name scope) body).body - {receiver, sender} := restEq
  have fresh1 : Disjoint lifted ((Molecule.mk scope body).scope ∪ (Molecule.mk scope body).bodyNames) := fresh
  have denotes1 : Denotes ⟨(Molecule.mk scope body).scope ∪ lifted,
      (Molecule.mk scope body).body - {receiver, sender} + kept + components⟩ process := denotes
  have denotes2 : Denotes ⟨(Molecule.mk (insert name scope) body).scope ∪ lifted',
      (Molecule.mk (insert name scope) body).body - {receiver, sender} + kept + components'⟩ process' := denotes'
  have before := result_congruent contained fires lifts fresh1 nodup scope1 rest1 sends denotes1
  have after := result_congruent contained' fires lifts' fresh' (List.nodup_cons.mpr ⟨nameOut, nodup⟩) scope2 rest2
    sends denotes2
  refine before.trans (Congruent.trans ?_ after.symm)
  refine (nu_garbage ?_).symm
  rw [freeNames_nuList]
  intro inside
  obtain ⟨present, _⟩ := Finset.mem_sdiff.mp inside
  simp only [Process.freeNames, Finset.mem_union] at present
  have receiverMem : receiver ∈ body := Multiset.subset_of_le contained (by simp)
  have senderMem : sender ∈ body := Multiset.subset_of_le contained (by simp)
  rcases present with inRest | received
  · obtain ⟨process, processMem, inProcess⟩ := mem_freeNames_parList.mp inRest
    obtain ⟨prime, primeMem, rfl⟩ := List.mem_map.mp processMem
    have : prime ∈ body := Multiset.mem_of_le (Multiset.sub_le_self _ _) (restEq ▸ Multiset.mem_coe.mpr primeMem)
    exact unused (Molecule.mem_bodyNames.mpr ⟨prime, this, inProcess⟩)
  · rcases Finset.mem_insert.mp (freeNames_receive receives payload received) with isPayload | fromReceiver
    · subst isPayload
      exact unused (Molecule.mem_bodyNames.mpr ⟨sender, senderMem, by rw [sends]; simp [Process.freeNames]⟩)
    · exact unused (Molecule.mem_bodyNames.mpr ⟨receiver, receiverMem, fromReceiver⟩)

/-! ## Molecules up to congruence -/

/-- **One step of molecule congruence**: a guarded process replaced with a related one, a replicated input unfolded
once, or an unused restricted name dropped. -/
inductive MolStep : Molecule → Molecule → Prop
  | prime {scope : Finset Name} {body : Multiset Prime} {first second : Prime} :
      PrimeRel first second → MolStep ⟨scope, body + {first}⟩ ⟨scope, body + {second}⟩
  | unfold {scope : Finset Name} {body : Multiset Prime} {x binder : Name} {inner : Process} :
      MolStep ⟨scope, body + {server x binder inner}⟩ ⟨scope, body + {copy x binder inner, server x binder inner}⟩
  | garbage {scope : Finset Name} {body : Multiset Prime} {name : Name} :
      name ∉ scope → name ∉ (Molecule.mk scope body).bodyNames → MolStep ⟨insert name scope, body⟩ ⟨scope, body⟩

/-- **Molecule congruence.** -/
abbrev MolEquiv : Molecule → Molecule → Prop := Relation.EqvGen MolStep

theorem InternalSim.refl (molecule : Molecule) : InternalSim molecule molecule := fun result internal => by
  obtain ⟨process, denotes⟩ := denotes_exists result
  exact ⟨result, internal, process, process, denotes, denotes, Congruent.refl _⟩

theorem InternalSim.trans {first second third : Molecule} (firstSecond : InternalSim first second)
    (secondThird : InternalSim second third) : InternalSim first third := fun result internal => by
  obtain ⟨middle, middleInternal, process, middleProcess, denotes, middleDenotes, congruent⟩ :=
    firstSecond result internal
  obtain ⟨last, lastInternal, middleProcess', lastProcess, middleDenotes', lastDenotes, congruent'⟩ :=
    secondThird middle middleInternal
  exact ⟨last, lastInternal, process, lastProcess, denotes, lastDenotes,
    congruent.trans ((denotes_congruent middleDenotes middleDenotes').trans congruent')⟩

/-- **Congruent molecules communicate alike**, in both directions. -/
theorem internalSim_of_equiv {first second : Molecule} (equivalent : MolEquiv first second) :
    InternalSim first second ∧ InternalSim second first := by
  induction equivalent with
  | rel _ _ step =>
    cases step with
    | prime related => exact ⟨internal_prime related, internal_prime related.symm⟩
    | unfold => exact ⟨internal_unfold, internal_fold⟩
    | garbage absent unused => exact ⟨internal_drop absent unused, internal_add absent unused⟩
  | refl => exact ⟨InternalSim.refl _, InternalSim.refl _⟩
  | symm _ _ _ holds => exact ⟨holds.2, holds.1⟩
  | trans _ _ _ _ _ first second => exact ⟨first.1.trans second.1, second.2.trans first.2⟩

/-- A restricted name inserted into both sides of a step. -/
def insertScope (name : Name) (molecule : Molecule) : Molecule := ⟨insert name molecule.scope, molecule.body⟩

/-- **Molecule congruence survives a restriction.** -/
theorem MolEquiv.insertScope {first second : Molecule} (name : Name) (equivalent : MolEquiv first second) :
    MolEquiv (LeastPartners.insertScope name first) (LeastPartners.insertScope name second) := by
  induction equivalent with
  | rel _ _ step =>
    cases step with
    | prime related => exact .rel _ _ (.prime related)
    | unfold => exact .rel _ _ .unfold
    | @garbage scope body other absent unused =>
      by_cases same : other = name
      · subst same
        simp only [LeastPartners.insertScope, Finset.insert_idem]
        exact .refl _
      · simp only [LeastPartners.insertScope]
        rw [Finset.insert_comm]
        exact .rel _ _ (.garbage (by simp [same, absent]) unused)
  | refl => exact .refl _
  | symm _ _ _ holds => exact .symm _ _ holds
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners
