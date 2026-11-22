import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Barbed

/-!
# Weak barbed bisimilarity and the tensor: not a congruence; the laws of the tensor

## Not a congruence, even on represented states

`weaklyBarbedBisimilar_tensor` assumes that the two states represent the **same** process: the tensor
preserves co-representation. Congruence on represented states would be: two weakly barbed bisimilar
represented states stay so beside a represented state. That fails, with the standard counterexample
of asynchronous calculi:

* `receiver` is `@0(y).0`, `sender` is `@0!(0)`;
* `@0(y).0` and `0` are barbed bisimilar for every set of names (both are stuck and neither shows a
  barb, `receiver_bisimilar_nil`), so their translations are weakly barbed bisimilar
  (`step_bisimilar`);
* beside `@0!(0)`, the first communicates to a process with no barb, and the second keeps its barb on
  `@0` forever: `not_congruence_represented` (all three states represent their processes).

## The laws of the tensor

On the nose the tensor is neither commutative, associative nor unital (`tensor_not_comm`,
`tensor_not_assoc`, `tensor_not_unital`): identities are renamed apart to even and odd numbers. Up to
weak barbed bisimilarity, on represented states, it commutes and associates (`tensor_comm_bisimilar`,
`tensor_assoc_bisimilar`): both sides represent the same process.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (sig G Closed read zeroT)

/-! ## The processes -/

/-- `@0(y).0`. -/
def receiver : RhoProcess := ⟨Source.receiver, Source.receiver_prime.1⟩

/-- `@0!(0)`. -/
def sender : RhoProcess := ⟨CanonicalReactionControls.payload, Source.payload_prime.1⟩

theorem receiver_bag : (fromProcess receiver).1 = {Source.receiver} := by
  rw [fromProcess_primes]
  exact primes_of_isPrime Source.receiver_prime

theorem sender_bag : (fromProcess sender).1 = {CanonicalReactionControls.payload} := by
  rw [fromProcess_primes]
  exact primes_of_isPrime Source.payload_prime

theorem nil_bag : (fromProcess nil).1 = 0 := by
  rw [fromProcess_primes]
  change primes (.apply "PZero" []) = 0
  exact primes_zero

/-! ## Stuck processes and absent barbs, read on canonical bags -/

/-- A process whose bag has no output is stuck. -/
theorem stuck_of_no_output {P : RhoProcess}
    (noOutput : ∀ c q, CanonicalReaction.output c q ∉ (fromProcess P).1) (Q : RhoProcess) :
    ¬ rhoLanguageDefGSLT.Step P Q := by
  intro step
  obtain ⟨rule, residue, source, _⟩ := (CanonicalReaction.publicStep_iff _ _).mp step
  apply noOutput rule.outputChannel rule.payload
  rw [source, CanonicalBag.append_inventory]
  exact Multiset.mem_add.mpr (.inl (by simp [CanonicalReaction.GroundComm.redex]))

/-- A process whose bag has no input is stuck. -/
theorem stuck_of_no_input {P : RhoProcess}
    (noInput : ∀ c b, CanonicalReaction.input c b ∉ (fromProcess P).1) (Q : RhoProcess) :
    ¬ rhoLanguageDefGSLT.Step P Q := by
  intro step
  obtain ⟨rule, residue, source, _⟩ := (CanonicalReaction.publicStep_iff _ _).mp step
  apply noInput rule.inputChannel rule.body
  rw [source, CanonicalBag.append_inventory]
  exact Multiset.mem_add.mpr (.inl (by simp [CanonicalReaction.GroundComm.redex]))

/-- A stuck process reaches only itself. -/
theorem reaches_of_stuck {P Q : RhoProcess} (stuck : ∀ Q, ¬ rhoLanguageDefGSLT.Step P Q)
    (run : Relation.ReflTransGen rhoLanguageDefGSLT.Step P Q) : Q = P := by
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨R, step, _⟩
  · rfl
  · exact (stuck R step).elim

theorem receiver_stuck (Q : RhoProcess) : ¬ rhoLanguageDefGSLT.Step receiver Q :=
  stuck_of_no_output (fun c q member => by
    rw [receiver_bag, Multiset.mem_singleton] at member
    simp [CanonicalReaction.output, Source.receiver, CanonicalReaction.input] at member) Q

theorem receiver_no_barb (c : Pattern) : ¬ Barb receiver c := by
  rintro ⟨q, member⟩
  rw [receiver_bag, Multiset.mem_singleton] at member
  simp [CanonicalReaction.output, Source.receiver, CanonicalReaction.input] at member

theorem nil_no_barb (c : Pattern) : ¬ Barb nil c := by
  rintro ⟨q, member⟩
  rw [nil_bag] at member
  exact Multiset.notMem_zero _ member

/-- **`@0(y).0` and `0` are barbed bisimilar, for every set of names.** -/
theorem receiver_bisimilar_nil (N : G [] .nm → Prop) : SourceBisimilar N receiver nil := by
  refine ⟨fun P Q => (P = receiver ∧ Q = nil) ∨ (P = nil ∧ Q = receiver), ⟨?_, ?_, ?_⟩,
    .inl ⟨rfl, rfl⟩⟩
  · rintro P Q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .inr ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · rintro P Q P' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) step
    · exact (receiver_stuck _ step).elim
    · exact (nil_stuck _ step).elim
  · rintro P Q c _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) barb
    · exact (receiver_no_barb _ barb).elim
    · exact (nil_no_barb _ barb).elim

/-! ## Beside `@0!(0)` -/

/-- The communication of `@0(y).0` with `@0!(0)`, as the calculus's own reaction instance. -/
abbrev receiverSenderComm : CanonicalReaction.GroundComm := Source.afterwards

/-- Its contractum. -/
abbrev receiverSenderAfter : RhoProcess := receiverSenderComm.target CanonicalBag.empty

theorem after_bag : (fromProcess receiverSenderAfter).1 = 0 := by
  rw [receiverSenderComm.target_inventory, CanonicalBag.append_inventory]
  change (fromProcess receiverSenderComm.result).1 + 0 = 0
  rw [add_zero, fromProcess_primes]
  change primes (semanticCommSubst CanonicalReactionControls.zero CanonicalReactionControls.zero) = 0
  rw [show semanticCommSubst CanonicalReactionControls.zero CanonicalReactionControls.zero =
    .apply "PZero" [] by decide]
  exact primes_zero

theorem after_stuck (Q : RhoProcess) : ¬ rhoLanguageDefGSLT.Step receiverSenderAfter Q :=
  stuck_of_no_output (fun c q member => by
    rw [after_bag] at member
    exact Multiset.notMem_zero _ member) Q

theorem after_no_barb (c : Pattern) : ¬ Barb receiverSenderAfter c := by
  rintro ⟨q, member⟩
  rw [after_bag] at member
  exact Multiset.notMem_zero _ member

/-- **`@0(y).0 | @0!(0)` communicates to a process with an empty bag.** -/
theorem receiver_sender_step : rhoLanguageDefGSLT.Step (par receiver sender) receiverSenderAfter := by
  refine (CanonicalReaction.publicStep_iff _ _).mpr ⟨receiverSenderComm, CanonicalBag.empty, ?_,
    receiverSenderComm.target_inventory CanonicalBag.empty⟩
  apply Subtype.ext
  rw [fromProcess_par, receiver_bag, sender_bag, CanonicalBag.append_inventory]
  rfl

theorem nil_sender_bag : (fromProcess (par nil sender)).1 = {CanonicalReactionControls.payload} := by
  rw [fromProcess_par, nil_bag, sender_bag, zero_add]

theorem nil_sender_stuck (Q : RhoProcess) : ¬ rhoLanguageDefGSLT.Step (par nil sender) Q :=
  stuck_of_no_input (fun c b member => by
    rw [nil_sender_bag, Multiset.mem_singleton] at member
    simp [CanonicalReaction.output, CanonicalReactionControls.payload, CanonicalReaction.input]
      at member) Q

/-- `@0!(0)` beside `0` shows its barb on `@0`. -/
theorem nil_sender_barb : Barb (par nil sender) (canonicalize (read ByInstantiation.nameZero)) := by
  refine ⟨CanonicalReactionControls.zero, ?_⟩
  rw [nil_sender_bag, Multiset.mem_singleton]
  rfl

theorem nameZero_closed : Closed ByInstantiation.nameZero := by decide

/-- **Beside `@0!(0)`, they are not barbed bisimilar** once `@0` is observable. -/
theorem not_bisimilar_beside_sender (N : G [] .nm → Prop) (observed : N ByInstantiation.nameZero) :
    ¬ SourceBisimilar N (par receiver sender) (par nil sender) := by
  rintro ⟨R, bisimulation, related⟩
  obtain ⟨Q', run, related'⟩ := bisimulation.step related receiver_sender_step
  rw [reaches_of_stuck nil_sender_stuck run] at related'
  obtain ⟨T, run', barb⟩ :=
    bisimulation.barb ByInstantiation.nameZero observed (bisimulation.symm related') nil_sender_barb
  rw [reaches_of_stuck after_stuck run'] at barb
  exact after_no_barb _ barb

/-! ## The same on the step -/

/-- Weak barbed bisimilarity is barbed bisimilarity over all closed names. -/
theorem weaklyBarbedBisimilar_iff_stepBisimilar (s t : ByInstantiation.State) :
    WeaklyBarbedBisimilar s t ↔ StepBisimilar (fun c => Closed c) s t := by
  constructor
  · rintro ⟨R, ⟨symm, moves, barbs⟩, related⟩
    exact ⟨R, ⟨symm, moves, fun c closed rel b => barbs c closed rel b⟩, related⟩
  · rintro ⟨R, ⟨symm, moves, barb⟩, related⟩
    exact ⟨R, ⟨symm, moves, fun c closed rel b => barb c closed rel b⟩, related⟩

/-- The translations of `@0(y).0` and `0` are weakly barbed bisimilar. -/
theorem step_bisimilar : WeaklyBarbedBisimilar (encode receiver) (encode nil) :=
  (weaklyBarbedBisimilar_iff_stepBisimilar _ _).mpr
    ((fully_abstract (fun _ closed => closed) receiver nil).mp (receiver_bisimilar_nil _))

/-- **Weak barbed bisimilarity is not a congruence for the tensor on represented states**: the
translations of `@0(y).0` and `0` are weakly barbed bisimilar, and beside the translation of `@0!(0)`
they are not. -/
theorem not_congruence_represented :
    ByInstantiation.Represents (encode receiver) receiver ∧
      ByInstantiation.Represents (encode nil) nil ∧
      ByInstantiation.Represents (encode sender) sender ∧
      WeaklyBarbedBisimilar (encode receiver) (encode nil) ∧
      ¬ WeaklyBarbedBisimilar (tensor (encode receiver) (encode sender))
        (tensor (encode nil) (encode sender)) := by
  refine ⟨encode_represents _, encode_represents _, encode_represents _, step_bisimilar, ?_⟩
  rw [← encode_par, ← encode_par, weaklyBarbedBisimilar_iff_stepBisimilar,
    ← fully_abstract (fun _ closed => closed)]
  exact not_bisimilar_beside_sender _ nameZero_closed

/-- The hypothesis of `weaklyBarbedBisimilar_tensor` fails here: the two states represent processes
with different bags. -/
theorem not_same_process : (fromProcess receiver).1 ≠ (fromProcess nil).1 := by
  rw [receiver_bag, nil_bag]
  exact Multiset.singleton_ne_zero _

/-! ## The laws of the tensor -/

/-- A state with one row, `0`. -/
abbrev oneRow : ByInstantiation.State := single zeroT

/-- **Not commutative on the nose.** -/
theorem tensor_not_comm : tensor oneRow emptyState ≠ tensor emptyState oneRow := by
  intro same
  have inside : (1 : ℕ) ∈ (tensor emptyState oneRow).present :=
    mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)
  rw [← same, mem_tensor] at inside
  rcases inside with ⟨k, _, odd⟩ | ⟨k, member, _⟩
  · omega
  · exact absurd member (Finset.notMem_empty k)

/-- **Not unital on the nose.** -/
theorem tensor_not_unital : tensor emptyState oneRow ≠ oneRow := by
  intro same
  have inside : (1 : ℕ) ∈ (tensor emptyState oneRow).present :=
    mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)
  rw [same] at inside
  exact absurd (Finset.mem_singleton.mp inside) (by decide)

/-- **Not associative on the nose.** -/
theorem tensor_not_assoc :
    tensor (tensor emptyState oneRow) emptyState ≠ tensor emptyState (tensor oneRow emptyState) := by
  intro same
  have inside : (2 : ℕ) ∈ (tensor (tensor emptyState oneRow) emptyState).present :=
    mem_tensor.mpr (.inl ⟨1, mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩), rfl⟩)
  rw [same, mem_tensor] at inside
  rcases inside with ⟨k, member, _⟩ | ⟨k, _, odd⟩
  · exact absurd member (Finset.notMem_empty k)
  · omega

/-- **Up to weak barbed bisimilarity, on represented states, the tensor commutes.** -/
theorem tensor_comm_bisimilar {s t : ByInstantiation.State} {P Q : RhoProcess}
    (onS : ByInstantiation.Represents s P) (onT : ByInstantiation.Represents t Q) :
    WeaklyBarbedBisimilar (tensor s t) (tensor t s) := by
  obtain ⟨left, onS⟩ := onS
  obtain ⟨right, onT⟩ := onT
  exact weaklyBarbedBisimilar_of_represents (P := par P Q)
    ⟨_, tensor_represents onS onT (fromProcess_par P Q)⟩
    ⟨_, tensor_represents onT onS (by rw [fromProcess_par, add_comm])⟩

/-- **Up to weak barbed bisimilarity, on represented states, the tensor is associative.** -/
theorem tensor_assoc_bisimilar {s t u : ByInstantiation.State} {P Q R : RhoProcess}
    (onS : ByInstantiation.Represents s P) (onT : ByInstantiation.Represents t Q)
    (onU : ByInstantiation.Represents u R) :
    WeaklyBarbedBisimilar (tensor (tensor s t) u) (tensor s (tensor t u)) := by
  obtain ⟨vs, onS⟩ := onS
  obtain ⟨vt, onT⟩ := onT
  obtain ⟨vu, onU⟩ := onU
  exact weaklyBarbedBisimilar_of_represents (P := par (par P Q) R)
    ⟨_, tensor_represents (tensor_represents onS onT (fromProcess_par P Q)) onU
      (fromProcess_par _ R)⟩
    ⟨_, tensor_represents onS (tensor_represents onT onU (fromProcess_par Q R))
      (by rw [fromProcess_par, fromProcess_par, fromProcess_par, add_assoc])⟩

/-- **Up to weak barbed bisimilarity, on represented states, the empty state is a unit**: both sides
represent the same process. -/
theorem tensor_unit_bisimilar {s : ByInstantiation.State} {P : RhoProcess}
    (onS : ByInstantiation.Represents s P) : WeaklyBarbedBisimilar (tensor emptyState s) s := by
  obtain ⟨value, onS⟩ := onS
  exact weaklyBarbedBisimilar_of_represents (P := P)
    ⟨_, tensor_represents (empty_represents (P := nil) primes_zero) onS
      (by rw [nil_bag, zero_add])⟩
    ⟨_, onS⟩

#print axioms receiver_bisimilar_nil
#print axioms receiver_sender_step
#print axioms not_bisimilar_beside_sender
#print axioms weaklyBarbedBisimilar_iff_stepBisimilar
#print axioms step_bisimilar
#print axioms not_congruence_represented
#print axioms not_same_process
#print axioms tensor_not_comm
#print axioms tensor_not_unital
#print axioms tensor_not_assoc
#print axioms tensor_comm_bisimilar
#print axioms tensor_assoc_bisimilar
#print axioms tensor_unit_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
