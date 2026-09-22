import Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual

/-!
# Strict truth-code decoding in the trace contextual model

The semantic proof fibre of a predicate is a separated canonical singleton.
Uniform trace products decode implication and universal quantification by
literal equality of set codes, over arbitrary contextual set families.
Consequently arbitrary dependent families over these codes can consume the
same witness using equality transport. No native identity or proof-erasure
rule is added, and a full native syntax interpretation is a separate result.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding

open ZFSetDependentProducts ZFSetTraceProducts
open ZFSetContextualInterpretation (SetFamily Section Extension totalFamily totalFamily_at
  extensionSubstitution)
open ZFSetTraceContextual (piFamily piDecode)

universe u v

noncomputable def truthCode (P : Prop) : ZFSet.{u} := ZFSet.sep (fun _ => P) {∅}

theorem mem_truthCode (P : Prop) (x : ZFSet.{u}) :
    x ∈ truthCode P ↔ x = ∅ ∧ P := by
  simp only [truthCode, ZFSet.mem_sep, ZFSet.mem_singleton]

theorem truthCode_subset (P : Prop) : truthCode.{u} P ⊆ ({∅} : ZFSet.{u}) :=
  ZFSet.sep_subset

theorem trace_forall_code (a : ZFSet.{u}) (P : Elements a → Prop) :
    tracePiSet a (totalFamily a (fun x => truthCode (P x))) =
      truthCode (∀ x : Elements a, P x) := by
  have fibres : ∀ x ∈ a, totalFamily a (fun x => truthCode (P x)) x ⊆ ({∅} : ZFSet.{u}) := by
    intro x hx
    rw [totalFamily_at a _ ⟨x, hx⟩]
    exact truthCode_subset _
  apply ZFSet.ext
  intro t
  rw [mem_tracePiSet_subterminal_iff fibres, mem_truthCode]
  constructor
  · rintro ⟨zero, all⟩
    refine ⟨zero, fun x => ?_⟩
    have member := all x.1 x.2
    rw [totalFamily_at, mem_truthCode] at member
    exact member.2
  · rintro ⟨zero, all⟩
    refine ⟨zero, fun x hx => ?_⟩
    rw [totalFamily_at a _ ⟨x, hx⟩, mem_truthCode]
    exact ⟨rfl, all ⟨x, hx⟩⟩

noncomputable def truthFamily {Γ : Type (u + 1)} (P : Γ → Prop) : SetFamily Γ :=
  fun γ => truthCode (P γ)

theorem forall_decoder {Γ : Type (u + 1)} (a : SetFamily Γ)
    (P : Extension a → Prop) :
    truthFamily (fun γ => ∀ x : Elements (a γ), P ⟨γ, x⟩) =
      piFamily a (truthFamily P) := by
  funext γ
  exact (trace_forall_code (a γ) (fun x => P ⟨γ, x⟩)).symm

theorem implication_decoder {Γ : Type (u + 1)} (P Q : Γ → Prop) :
    truthFamily (fun γ => P γ → Q γ) =
      piFamily (truthFamily P) (truthFamily (fun pair => Q pair.1)) := by
  rw [← forall_decoder]
  funext γ
  apply congrArg truthCode
  apply propext
  constructor
  · intro implication x
    exact implication ((mem_truthCode _ x.1).mp x.2).2
  · intro function premise
    exact function ⟨∅, (mem_truthCode _ ∅).mpr ⟨rfl, premise⟩⟩

theorem truthFamily_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ) (P : Γ → Prop) :
    truthFamily P ∘ θ = truthFamily (P ∘ θ) := rfl

theorem forall_decoder_reindex {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    (a : SetFamily Γ) (P : Extension a → Prop) :
    (truthFamily (fun γ => ∀ x : Elements (a γ), P ⟨γ, x⟩)) ∘ θ =
      piFamily (a ∘ θ) (truthFamily (P ∘ extensionSubstitution θ a)) := by
  rw [forall_decoder]
  rfl

/-- Unlike an unstructured carrier bijection, this proved code equality
can be used under every set-valued dependent family of codes. -/
theorem dependent_family_agreement {Γ : Type (u + 1)} (a : SetFamily Γ)
    (P : Extension a → Prop) (F : Γ → ZFSet.{u} → ZFSet.{u}) :
    (fun γ => F γ (truthCode (∀ x : Elements (a γ), P ⟨γ, x⟩))) =
      fun γ => F γ (piFamily a (truthFamily P) γ) := by
  funext γ
  exact congrArg (F γ) (congrFun (forall_decoder a P) γ)

noncomputable def dependentConsumer {Γ : Type (u + 1)} (a : SetFamily Γ)
    (P : Extension a → Prop) (F : Γ → ZFSet.{u} → ZFSet.{u})
    (witness : (γ : Γ) → Elements (F γ (truthCode (∀ x : Elements (a γ), P ⟨γ, x⟩)))) :
    (γ : Γ) → Elements (F γ (piFamily a (truthFamily P) γ)) :=
  fun γ => ⟨(witness γ).1, (congrFun (dependent_family_agreement a P F) γ) ▸ (witness γ).2⟩

theorem dependentConsumer_value {Γ : Type (u + 1)} (a : SetFamily Γ)
    (P : Extension a → Prop) (F : Γ → ZFSet.{u} → ZFSet.{u})
    (witness : (γ : Γ) → Elements (F γ (truthCode (∀ x : Elements (a γ), P ⟨γ, x⟩))))
    (γ : Γ) : (dependentConsumer a P F witness γ).1 = (witness γ).1 := rfl

theorem dependentConsumer_reindex {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    (a : SetFamily Γ) (P : Extension a → Prop) (F : Γ → ZFSet.{u} → ZFSet.{u})
    (witness : (γ : Γ) → Elements (F γ (truthCode (∀ x : Elements (a γ), P ⟨γ, x⟩)))) :
    (fun δ => dependentConsumer a P F witness (θ δ)) =
      dependentConsumer (a ∘ θ) (P ∘ extensionSubstitution θ a)
        (fun δ => F (θ δ)) (fun δ => witness (θ δ)) := by
  funext δ
  rfl

/-- The trace product itself, not a redefined proof-code alias, equals the
original canonical true code. -/
theorem true_implication_literal :
    tracePiSet (truthCode.{u} True) (fun _ => truthCode True) = truthCode True := by
  rw [tracePiSet_eq_truth (fun _ _ => truthCode_subset True)]
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_sep, ZFSet.mem_singleton, mem_truthCode, and_true, implies_true]

theorem false_consequent_rejected :
    tracePiSet (truthCode.{u} True) (fun _ => truthCode False) = ∅ :=
  tracePiSet_empty_of_empty_fibre
    ⟨∅, (mem_truthCode True ∅).mpr ⟨rfl, trivial⟩⟩ (by
      apply ZFSet.ext
      intro x
      simp only [mem_truthCode, and_false, ZFSet.notMem_empty])

#print axioms trace_forall_code
#print axioms forall_decoder
#print axioms implication_decoder
#print axioms forall_decoder_reindex
#print axioms dependent_family_agreement
#print axioms dependentConsumer_value
#print axioms dependentConsumer_reindex
#print axioms true_implication_literal
#print axioms false_consequent_rejected

end Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
