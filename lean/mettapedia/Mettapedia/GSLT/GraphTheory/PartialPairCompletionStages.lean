import Mettapedia.GSLT.GraphTheory.PartialPairCompletionStep
import Mathlib.Data.Nat.Basic
import Mathlib.Order.DirectedInverseSystem

/-!
# Canonical-completion stages and coherent inclusions

These stages iterate the actual partial-pair successor of
Bucciarelli–Salibra §2.3 Definition 4. Their embeddings preserve complete
finite supports and every already-defined code. Undefined old inputs become
defined, so reflection concerns outputs in the embedded old carrier, not
unconditional reflection of definedness. The stage tower is a directed
system; the total limit coding and graph model are not constructed here.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStages

open Mettapedia.GSLT.Core

def stage (pair : PartialPair) : Nat → PartialPair
  | 0 => pair
  | n + 1 => CompletionStep.successor (stage pair n)

def inclusion (pair : PartialPair) {n m : Nat} (h : n ≤ m) :
    (stage pair n).Carrier ↪ (stage pair m).Carrier where
  toFun := Nat.leRecOn (C := fun k => (stage pair k).Carrier) h
    (fun {_} token => Sum.inl token)
  inj' := Nat.leRecOn_injective (C := fun k => (stage pair k).Carrier)
    h (fun {_} token => Sum.inl token)
    (fun _ => Sum.inl_injective)

theorem inclusion_self (pair : PartialPair) (n : Nat) :
    inclusion pair (Nat.le_refl n) = Function.Embedding.refl _ := by
  ext token
  exact Nat.leRecOn_self (C := fun k => (stage pair k).Carrier)
    (next := fun {_} token => Sum.inl token) token

theorem inclusion_succ (pair : PartialPair) {n m : Nat} (h : n ≤ m) :
    inclusion pair (Nat.le_succ_of_le h) =
      (inclusion pair h).trans Function.Embedding.inl := by
  ext token
  exact Nat.leRecOn_succ (C := fun k => (stage pair k).Carrier)
    (next := fun {_} token => Sum.inl token) h token

theorem inclusion_next (pair : PartialPair) (n : Nat) :
    inclusion pair (Nat.le_succ n) = Function.Embedding.inl := by
  ext token
  exact Nat.leRecOn_succ' (C := fun k => (stage pair k).Carrier)
    (next := fun {_} token => Sum.inl token) token

theorem inclusion_trans (pair : PartialPair) {n m k : Nat}
    (h : n ≤ m) (h' : m ≤ k) :
    inclusion pair (h.trans h') = (inclusion pair h).trans (inclusion pair h') := by
  ext token
  exact Nat.leRecOn_trans (C := fun k => (stage pair k).Carrier)
    (next := fun {_} token => Sum.inl token) h h' token

theorem inclusion_trans_apply (pair : PartialPair) {n m k : Nat}
    (h : n ≤ m) (h' : m ≤ k) (token : (stage pair n).Carrier) :
    inclusion pair h' (inclusion pair h token) = inclusion pair (h.trans h') token := by
  rw [inclusion_trans pair h h']
  rfl

/-- Existing generic directed-limit infrastructure applies to these actual maps. -/
instance (pair : PartialPair) :
    DirectedSystem (fun n => (stage pair n).Carrier)
      (fun {_ _} h => inclusion pair h) where
  map_self := by intro n token; rw [inclusion_self]; rfl
  map_map := by intro k m n h h' token; exact inclusion_trans_apply pair h h' token

theorem support_self (pair : PartialPair) (n : Nat)
    (support : Finset (stage pair n).Carrier) :
    support.map (inclusion pair (Nat.le_refl n)) = support := by
  rw [inclusion_self, Finset.map_refl]

theorem support_trans (pair : PartialPair) {n m k : Nat} (h : n ≤ m) (h' : m ≤ k)
    (support : Finset (stage pair n).Carrier) :
    (support.map (inclusion pair h)).map (inclusion pair h') =
      support.map (inclusion pair (h.trans h')) := by
  rw [Finset.map_map, inclusion_trans pair h h']

/-- Every old token occurs in the later full support exactly when it did before. -/
theorem mem_support_iff (pair : PartialPair) {n m : Nat} (h : n ≤ m)
    (support : Finset (stage pair n).Carrier) (token : (stage pair n).Carrier) :
    inclusion pair h token ∈ support.map (inclusion pair h) ↔ token ∈ support := by
  exact Finset.mem_map' _

theorem support_card (pair : PartialPair) {n m : Nat} (h : n ≤ m)
    (support : Finset (stage pair n).Carrier) :
    (support.map (inclusion pair h)).card = support.card := Finset.card_map _

theorem support_injective (pair : PartialPair) {n m : Nat} (h : n ≤ m) :
    Function.Injective (Finset.map (inclusion pair h)) := Finset.map_injective _

theorem full_input_injective (pair : PartialPair) {n m : Nat} (h : n ≤ m) :
    Function.Injective (fun input : Finset (stage pair n).Carrier × (stage pair n).Carrier =>
      (input.1.map (inclusion pair h), inclusion pair h input.2)) := by
  intro first second hInputs
  apply Prod.ext
  · exact support_injective pair h (congrArg Prod.fst hInputs)
  · exact (inclusion pair h).injective (congrArg Prod.snd hInputs)

/-- Filling does not invent a new code equal to a preserved old output. -/
theorem successor_code_old_output_iff (pair : PartialPair)
    (support : Finset pair.Carrier) (output token : pair.Carrier) :
    (CompletionStep.successor pair).coding.code
        (support.map Function.Embedding.inl, Sum.inl output) = some (Sum.inl token) ↔
      pair.coding.code (support, output) = some token := by
  change CompletionStep.code pair (support.map Function.Embedding.inl, Sum.inl output) =
    some (Sum.inl token) ↔ _
  rw [CompletionStep.code_old]
  cases h : pair.coding.code (support, output) with
  | none =>
      rw [CompletionStep.oldCode_of_missing pair _ h]
      simp only [Option.some.injEq, Sum.inr_ne_inl, reduceCtorEq]
  | some value =>
      rw [CompletionStep.oldCode_of_defined pair _ value h]
      simp only [Option.some.injEq, Sum.inl.injEq]

/-- Defined codes and their full inputs are preserved and reflected across
arbitrary ordered stages, provided the compared output is an old token. -/
theorem code_old_output_iff (pair : PartialPair) {n m : Nat} (h : n ≤ m)
    (support : Finset (stage pair n).Carrier) (output token : (stage pair n).Carrier) :
    (stage pair m).coding.code
        (support.map (inclusion pair h), inclusion pair h output) =
          some (inclusion pair h token) ↔
      (stage pair n).coding.code (support, output) = some token := by
  induction h with
  | refl => rw [inclusion_self, Finset.map_refl]; rfl
  | @step m h ih =>
      rw [inclusion_succ pair h]
      change CompletionStep.code (stage pair m)
        (support.map ((inclusion pair h).trans Function.Embedding.inl),
          Sum.inl (inclusion pair h output)) = some (Sum.inl (inclusion pair h token)) ↔ _
      rw [← Finset.map_map]
      exact (successor_code_old_output_iff (stage pair m) _ _ _).trans ih

/-- All finite inputs at one stage become defined at its successor. -/
theorem input_defined_next (pair : PartialPair) (n : Nat)
    (support : Finset (stage pair n).Carrier) (output : (stage pair n).Carrier) :
    ∃ token, (stage pair (n + 1)).coding.code
      (support.map (inclusion pair (Nat.le_succ n)),
        inclusion pair (Nat.le_succ n) output) = some token := by
  rw [inclusion_next]
  exact ⟨CompletionStep.oldCode (stage pair n) (support, output),
    CompletionStep.code_old (stage pair n) support output⟩

/-- An input already available at stage n is defined at every later stage m>n. -/
theorem input_defined_later (pair : PartialPair) {n m : Nat} (h : n < m)
    (support : Finset (stage pair n).Carrier) (output : (stage pair n).Carrier) :
    ∃ token, (stage pair m).coding.code
      (support.map (inclusion pair (Nat.le_of_lt h)),
        inclusion pair (Nat.le_of_lt h) output) = some token := by
  obtain ⟨token, hToken⟩ := input_defined_next pair n support output
  have hNext : n + 1 ≤ m := h
  have hPreserved := (code_old_output_iff pair hNext
    (support.map (inclusion pair (Nat.le_succ n)))
    (inclusion pair (Nat.le_succ n) output) token).mpr hToken
  rw [support_trans, inclusion_trans_apply] at hPreserved
  exact ⟨inclusion pair hNext token, hPreserved⟩

/-- Finitely many stage indices have a common later stage; every source
support retains its cardinality and complete membership there. -/
theorem finite_family_common_stage (pair : PartialPair) {ι : Type*}
    (indices : Finset ι) (stageIndex : ι → Nat)
    (supports : ∀ i, Finset (stage pair (stageIndex i)).Carrier) :
    ∃ m, ∀ i ∈ indices, ∃ h : stageIndex i ≤ m,
      (supports i |>.map (inclusion pair h)).card = (supports i).card ∧
      ∀ token, inclusion pair h token ∈ (supports i).map (inclusion pair h) ↔
        token ∈ supports i := by
  refine ⟨indices.sup stageIndex, ?_⟩
  intro i hMember
  have h : stageIndex i ≤ indices.sup stageIndex := Finset.le_sup hMember
  exact ⟨h, support_card pair h _, mem_support_iff pair h _⟩

/-- Finitely many full inputs drawn from different stages become defined in
one common later stage, with each original support still injectively embedded. -/
theorem finite_inputs_defined_common_stage (pair : PartialPair) {ι : Type*}
    (indices : Finset ι) (stageIndex : ι → Nat)
    (inputs : ∀ i, Finset (stage pair (stageIndex i)).Carrier ×
      (stage pair (stageIndex i)).Carrier) :
    ∃ m, ∀ i ∈ indices, ∃ h : stageIndex i < m, ∃ token,
      (stage pair m).coding.code
          ((inputs i).1.map (inclusion pair (Nat.le_of_lt h)),
            inclusion pair (Nat.le_of_lt h) (inputs i).2) = some token ∧
        ((inputs i).1.map (inclusion pair (Nat.le_of_lt h))).card = (inputs i).1.card := by
  refine ⟨indices.sup stageIndex + 1, ?_⟩
  intro i hMember
  have h : stageIndex i < indices.sup stageIndex + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup hMember)
  obtain ⟨token, hToken⟩ := input_defined_later pair h (inputs i).1 (inputs i).2
  exact ⟨h, token, hToken, support_card pair _ _⟩

end Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStages
