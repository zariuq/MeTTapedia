import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
import Mathlib.Data.List.NodupEquivFin

/-!
# Occurrence embeddings for proof-relevant step oracles

An oracle returns a list of individual firing results. An extension may add
results before an old firing, changing its ordinal even when its endpoint and
evidence survive. An occurrence embedding retains a strictly ordered map of
positions together with the relation satisfied by the selected results. It
does not identify equal entries or presume an identity-on-history inclusion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

universe u v w

/-- A selected occurrence in `before` is sent to a distinct, ordered
occurrence in `after`; the two selected values satisfy `Related`. -/
structure Embedding {A : Type u} {B : Type v}
    (Related : A → B → Prop) (before : List A) (after : List B) where
  position : Fin before.length ↪o Fin after.length
  relates : ∀ i, Related (before.get i) (after.get (position i))

/-- Every oracle result has its original occurrence in the same list. -/
def Embedding.refl {A : Type u} (values : List A) :
    Embedding Eq values values where
  position := OrderEmbedding.ofMapLEIff id (by intro a b; rfl)
  relates := by intro i; rfl

/-- Composing refinements composes their position maps and their relations
without discarding the intermediate selected result. -/
def Embedding.comp {A : Type u} {B : Type v} {C : Type w}
    {R : A → B → Prop} {S : B → C → Prop}
    {before : List A} {middle : List B} {after : List C}
    (first : Embedding R before middle)
    (second : Embedding S middle after) :
    Embedding (fun a c => ∃ b, R a b ∧ S b c) before after where
  position := first.position.trans second.position
  relates := by
    intro i
    exact ⟨middle.get (first.position i), first.relates i,
      second.relates (first.position i)⟩

/-- A transitive value relation supports successive occurrence-preserving
oracle extensions. -/
def Embedding.trans {A : Type u} {R : A → A → Prop}
    {before middle after : List A}
    (transitive : ∀ a b c, R a b → R b c → R a c)
    (first : Embedding R before middle)
    (second : Embedding R middle after) : Embedding R before after where
  position := first.position.trans second.position
  relates := by
    intro i
    exact transitive _ _ _ (first.relates i)
      (second.relates (first.position i))

/-- Inserting a prefix preserves every old result, shifting its ordinal by
the prefix length. The witness distinguishes duplicate values by position. -/
def Embedding.afterPrefix {A : Type u} (inserted values : List A) :
    Embedding Eq values (inserted ++ values) where
  position := OrderEmbedding.ofMapLEIff
    (fun i => (⟨inserted.length + i.val, by simp⟩ :
      Fin (inserted ++ values).length)) (by
        intro i j
        change (inserted.length + i.val ≤ inserted.length + j.val) ↔
          (i.val ≤ j.val)
        omega)
  relates := by
    intro i
    change values[i.val] = (inserted ++ values)[inserted.length + i.val]
    simp

/-- The prefix map sends each old occurrence to the corresponding shifted
ordinal, even when a newly inserted value equals it. -/
theorem Embedding.afterPrefix_position {A : Type u}
    (inserted values : List A) (i : Fin values.length) :
    ((Embedding.afterPrefix inserted values).position i).val =
      inserted.length + i.val := rfl

/-- For unchanged values, occurrence embeddings are exactly sublist
witnesses. In particular, this comparison keeps duplicate occurrences. -/
theorem exists_eq_iff_sublist {A : Type u} {before after : List A} :
    Nonempty (Embedding Eq before after) ↔ List.Sublist before after := by
  constructor
  · rintro ⟨embedding⟩
    exact List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      ⟨embedding.position, embedding.relates⟩
  · intro sublist
    obtain ⟨position, relates⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp sublist
    exact ⟨⟨position, relates⟩⟩

/-- A located old oracle result has a related result at its specifically
mapped new ordinal. Membership alone would lose this occurrence identity. -/
theorem Embedding.zipIdx_transport {A : Type u} {B : Type v}
    {R : A → B → Prop} {before : List A} {after : List B}
    (embedding : Embedding R before after)
    {value : A} {ordinal : Nat}
    (selected : (value, ordinal) ∈ before.zipIdx) :
    ∃ (bound : ordinal < before.length) (newValue : B),
      (newValue, (embedding.position ⟨ordinal, bound⟩).val) ∈
        after.zipIdx ∧ R value newValue := by
  obtain ⟨bound, valueEq⟩ := List.mem_zipIdx' selected
  let oldPosition : Fin before.length := ⟨ordinal, bound⟩
  let newPosition := embedding.position oldPosition
  refine ⟨bound, after.get newPosition, ?_, ?_⟩
  · have newBound : newPosition.val < after.zipIdx.length := by
      simpa only [List.length_zipIdx] using newPosition.isLt
    have newEntry : after.zipIdx[newPosition.val] ∈ after.zipIdx :=
      List.getElem_mem newBound
    simpa [List.getElem_zipIdx, newPosition] using newEntry
  · simpa [oldPosition, valueEq] using embedding.relates oldPosition

/-- A scoped step premise transports across the occurrence embedding at its
actual instantiated source. The completed contextual assignment is unchanged;
the new ordinal is exactly the embedding's selected position. This applies
beneath any number of local binders. -/
theorem stepResults_transport_at {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat)
    (source target instantiated : Pattern)
    (assignment completed : Assignment)
    (oldOrdinal : Nat) (oldEvidence : OldEvidence)
    (instantiates :
      instantiateAt? rule spec ambient (.premise index 0 0) [] localDepth
        assignment source = some instantiated)
    (oracleEmbedding :
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle (localDepth + ambient) instantiated)
        (newOracle (localDepth + ambient) instantiated))
    (executed :
      ((.step index oldOrdinal oldEvidence), completed) ∈
        stepResults oldOracle rule spec ambient index localDepth
          source target assignment) :
    ∃ (oldBound : oldOrdinal <
        (oldOracle (localDepth + ambient) instantiated).length)
      (newEvidence : NewEvidence),
      ((.step index
        (oracleEmbedding.position ⟨oldOrdinal, oldBound⟩).val
          newEvidence), completed) ∈
        stepResults newOracle rule spec ambient index localDepth
          source target assignment ∧
      relatedEvidence oldEvidence newEvidence := by
  by_cases hscope : instantiated.isWellScopedAt
      (localDepth + ambient) = true
  · simp only [stepResults, instantiates, hscope, ite_true] at executed ⊢
    obtain ⟨⟨⟨oldValue, candidate⟩, selectedOrdinal⟩,
        oracleSelected, admitted⟩ := List.mem_flatMap.mp executed
    by_cases candidateScope : candidate.isWellScopedAt
        (localDepth + ambient) = true
    · simp only [candidateScope, ite_true, List.mem_map] at admitted
      obtain ⟨newAssignment, matched, equalResult⟩ := admitted
      cases equalResult
      have selected := oracleEmbedding.zipIdx_transport oracleSelected
      obtain ⟨oldBound, ⟨newValue, newCandidate⟩,
        newSelected, ⟨candidateEq, evidenceRelated⟩⟩ := selected
      cases candidateEq
      refine ⟨oldBound, newValue, ?_, ?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨((newValue, candidate),
          (oracleEmbedding.position ⟨oldOrdinal, oldBound⟩).val),
            newSelected, ?_⟩
        simp only [candidateScope, ite_true, List.mem_map]
        exact ⟨completed, matched, rfl⟩
      · exact evidenceRelated
    · simp [candidateScope] at admitted
  · simp [stepResults, instantiates, hscope] at executed

/-- A family of oracle occurrence embeddings gives the scoped step-premise
transport at every instantiated source and every local binder depth. -/
theorem stepResults_transport {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat)
    (source target : Pattern) (assignment completed : Assignment)
    (oldOrdinal : Nat) (oldEvidence : OldEvidence)
    (executed :
      ((.step index oldOrdinal oldEvidence), completed) ∈
        stepResults oldOracle rule spec ambient index localDepth
          source target assignment) :
    ∃ instantiated,
      instantiateAt? rule spec ambient (.premise index 0 0) [] localDepth
        assignment source = some instantiated ∧
      ∃ (oldBound : oldOrdinal <
          (oldOracle (localDepth + ambient) instantiated).length)
        (newEvidence : NewEvidence),
        ((.step index
          ((oracleEmbedding (localDepth + ambient) instantiated).position
            ⟨oldOrdinal, oldBound⟩).val newEvidence), completed) ∈
          stepResults newOracle rule spec ambient index localDepth
            source target assignment ∧
        relatedEvidence oldEvidence newEvidence := by
  cases hinst : instantiateAt? rule spec ambient (.premise index 0 0)
      [] localDepth assignment source with
  | none =>
      simp [stepResults, hinst] at executed
  | some instantiated =>
      obtain ⟨oldBound, newEvidence, selected, related⟩ :=
        stepResults_transport_at relatedEvidence oldOracle newOracle
          rule spec ambient index localDepth source target instantiated
          assignment completed oldOrdinal oldEvidence hinst
          (oracleEmbedding _ _) executed
      exact ⟨instantiated, rfl, oldBound, newEvidence,
        selected, related⟩

#print axioms Embedding.refl
#print axioms Embedding.comp
#print axioms Embedding.trans
#print axioms Embedding.afterPrefix
#print axioms Embedding.afterPrefix_position
#print axioms exists_eq_iff_sublist
#print axioms Embedding.zipIdx_transport
#print axioms stepResults_transport_at
#print axioms stepResults_transport

end Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding
