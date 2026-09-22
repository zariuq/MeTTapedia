import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTermInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding

/-!
# Literal trace decoding of original HOL proof families

The formulas here are original typed HOL source expressions, interpreted by
the independently recursive trace interpreter. Their implication and universal
proof fibres are literally the contextual trace-product codes. The generic
trace-decoder laws are instantiated, not duplicated. Original retained proof
trees cross the existing same-model proof-family bridge and can be applied
using actual trace application. This does not assert all-native DTT soundness.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceProofDecoding

open ZFSetHOLTraceTypeInterpretation ZFSetHOLTraceTermInterpretation
open ZFSetDependentProducts ZFSetUniverseClosure ZFSetUniverseInterpretation
open ZFSetHOLTypeInterpretation (holds holds_truth)
open ZFSetContextualInterpretation (SetFamily Extension extensionSubstitution)

universe u

noncomputable def truthFibre (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation Γ) : ZFSet.{u + 1} :=
  ZFSetTraceProofDecoding.truthCode (holds (interpret (universeConstants h) φ ρ))

noncomputable def truthFamily (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) : SetFamily (Valuation.{u} Γ) := truthFibre h φ

theorem mem_truthFibre (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation Γ) (x : ZFSet.{u + 1}) :
    x ∈ truthFibre h φ ρ ↔ x = ∅ ∧ holds (interpret (universeConstants h) φ ρ) :=
  ZFSetTraceProofDecoding.mem_truthCode _ x

theorem formula_graph_agreement (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    interpret (universeConstants h) φ ρ =
      ZFSetHOLTermInterpretation.interpret (ZFSetHOLTermInterpretation.universeConstants h)
        φ (graphValuation ρ) :=
  (graphEquiv_prop _).symm.trans
    (graph_interpret (universeConstants h) (ZFSetHOLTermInterpretation.universeConstants h)
      (graph_universeConstants h) φ ρ)

theorem truthFibre_graph (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    truthFibre h φ ρ = ZFSetHOLProofInterpretation.truthFibre h φ (graphValuation ρ) := by
  unfold truthFibre ZFSetTraceProofDecoding.truthCode ZFSetHOLProofInterpretation.truthFibre
  rw [formula_graph_agreement]

theorem truthFibre_substitution (h : CofinalInaccessibles.{u}) {Γ Δ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) :
    truthFibre h (HOL.subst θ φ) ρ =
      truthFibre h φ (substValuation (universeConstants h) θ ρ) := by
  unfold truthFibre
  rw [universe_substitution]

/-! ## Source formulas instantiate the literal contextual decoder -/

@[reducible] noncomputable def quantifierDomain (Γ : Ctx Unit) (A : Ty Unit) :
    SetFamily (Valuation.{u} Γ) :=
  fun _ => typeCode A

noncomputable def quantifierBody (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ)) :
    SetFamily (Extension (quantifierDomain.{u} Γ A)) :=
  fun pair => truthFibre h φ (extend pair.1 pair.2)

theorem source_implication_decoder (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p q : Formula UniverseSymbol Γ) :
    truthFamily h (.imp p q) =
      ZFSetTraceContextual.piFamily (truthFamily h p) (fun pair => truthFibre h q pair.1) := by
  funext ρ
  have generic := congrFun (ZFSetTraceProofDecoding.implication_decoder
      (fun ρ : Valuation Γ => holds (interpret (universeConstants h) p ρ))
      (fun ρ : Valuation Γ => holds (interpret (universeConstants h) q ρ))) ρ
  have source : truthFibre h (.imp p q) ρ = ZFSetTraceProofDecoding.truthCode
      (holds (interpret (universeConstants h) p ρ) →
        holds (interpret (universeConstants h) q ρ)) := by
    unfold truthFibre
    apply congrArg ZFSetTraceProofDecoding.truthCode
    exact propext (holds_truth _)
  exact source.trans generic

theorem source_forall_decoder (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ)) :
    truthFamily h (.all φ) =
      ZFSetTraceContextual.piFamily (quantifierDomain Γ A) (quantifierBody h φ) := by
  funext ρ
  have generic := congrFun (ZFSetTraceProofDecoding.forall_decoder (quantifierDomain Γ A)
    (fun pair => holds (interpret (universeConstants h) φ (extend pair.1 pair.2)))) ρ
  have source : truthFibre h (.all φ) ρ = ZFSetTraceProofDecoding.truthCode
      (∀ x : Value A, holds (interpret (universeConstants h) φ (extend ρ x))) := by
    unfold truthFibre
    apply congrArg ZFSetTraceProofDecoding.truthCode
    exact propext (holds_truth _)
  exact source.trans generic

theorem quantifierBody_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) :
    quantifierBody h (HOL.subst (Subst.lift θ) φ) =
      quantifierBody h φ ∘ extensionSubstitution (substValuation (universeConstants h) θ)
        (quantifierDomain Γ A) := by
  funext pair
  exact (truthFibre_substitution h φ (Subst.lift θ) (extend pair.1 pair.2)).trans
    (congrArg (fun ρ : Valuation (A :: Γ) => truthFibre h φ ρ)
      (universe_substValuation_lift h θ pair.1 pair.2))

theorem source_forall_decoder_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) :
    truthFamily h (HOL.subst θ (.all φ)) =
      ZFSetTraceContextual.piFamily (quantifierDomain Δ A)
        (quantifierBody h φ ∘ extensionSubstitution (substValuation (universeConstants h) θ)
          (quantifierDomain Γ A)) := by
  change truthFamily h (.all (HOL.subst (Subst.lift θ) φ)) = _
  exact (source_forall_decoder h (HOL.subst (Subst.lift θ) φ)).trans
    (congrArg (ZFSetTraceContextual.piFamily (quantifierDomain Δ A))
      (quantifierBody_substitution h φ θ))

theorem source_implication_decoder_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} (p q : Formula UniverseSymbol Γ) (θ : Subst UniverseSymbol Γ Δ) :
    truthFamily h (HOL.subst θ (.imp p q)) =
      ZFSetTraceContextual.piFamily
        (truthFamily h p ∘ substValuation (universeConstants h) θ)
        (fun pair => truthFibre h q (substValuation (universeConstants h) θ pair.1)) := by
  funext ρ
  exact (truthFibre_substitution h (.imp p q) θ ρ).trans
    (congrFun (source_implication_decoder h p q) (substValuation (universeConstants h) θ ρ))

/-- Code equality remains valid inside arbitrary code-indexed families. -/
theorem source_dependent_family_agreement (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (F : Valuation Γ → ZFSet.{u + 1} → ZFSet.{u + 1}) (ρ : Valuation Γ) :
    F ρ (truthFibre h (.all φ) ρ) =
      F ρ (ZFSetTraceContextual.piFamily (quantifierDomain Γ A) (quantifierBody h φ) ρ) :=
  congrArg (F ρ) (congrFun (source_forall_decoder h φ) ρ)

/-! ## Retained original proofs, now consumed by actual trace application -/

abbrev CodedSatisfied (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (hypotheses : List (Formula UniverseSymbol Γ)) :=
  {ρ : Valuation.{u} Γ // ∀ φ ∈ hypotheses, holds (interpret (universeConstants h) φ ρ)}

noncomputable def graphSatisfied (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula UniverseSymbol Γ)} (ρ : CodedSatisfied h hypotheses) :
    ZFSetHOLProofInterpretation.CodedSatisfied h hypotheses :=
  ⟨graphValuation ρ.1, fun φ member => (formula_graph_agreement h φ ρ.1) ▸ ρ.2 φ member⟩

noncomputable def proofValue (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula UniverseSymbol Γ)} {φ : Formula UniverseSymbol Γ}
    (proof : ProofSyntax UniverseSymbol hypotheses φ) (ρ : CodedSatisfied h hypotheses) :
    Elements (truthFibre h φ ρ.1) :=
  let value := ZFSetHOLProofInterpretation.proofValue h proof (graphSatisfied h ρ)
  ⟨value.1, (truthFibre_graph h φ ρ.1).symm ▸ value.2⟩

noncomputable def universalProof (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all φ)) (ρ : CodedSatisfied h hypotheses) :
    Elements (ZFSetTraceContextual.piFamily (quantifierDomain Γ A) (quantifierBody h φ) ρ.1) :=
  ⟨(proofValue h proof ρ).1,
    (congrFun (source_forall_decoder h φ) ρ.1) ▸ (proofValue h proof ρ).2⟩

noncomputable def universalProofApp (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all φ)) (ρ : CodedSatisfied h hypotheses)
    (x : Value A) : Elements (truthFibre h φ (extend ρ.1 x)) :=
  ZFSetTraceContextual.piDecode (quantifierDomain Γ A) (quantifierBody h φ) ρ.1
    (universalProof h proof ρ) x

theorem universalProofApp_trace (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all φ)) (ρ : CodedSatisfied h hypotheses)
    (x : Value A) : (universalProofApp h proof ρ x).1 =
      ZFSetTraceProducts.traceApp (proofValue h proof ρ).1 x.1 :=
  ZFSetTraceContextual.piDecode_value (quantifierDomain Γ A) (quantifierBody h φ) ρ.1 _ x

def noHypotheses (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit} (ρ : Valuation Γ) :
    CodedSatisfied h ([] : List (Formula UniverseSymbol Γ)) :=
  ⟨ρ, fun _ member => False.elim (List.not_mem_nil member)⟩

noncomputable def higherOrderEtaApplication (h : CofinalInaccessibles.{u}) :
    Elements (truthFibre h
      (.eq (.lam (.app (.var (.vs .vz)) (.var .vz)))
        (.var .vz : UniverseExpr [ZFSetHenkinInterpretation.mapping] ZFSetHenkinInterpretation.mapping))
      (extend emptyValuation (universeConstants h (.core .power)))) :=
  universalProofApp h ZFSetHOLProofInterpretation.functionEtaProof
    (noHypotheses h emptyValuation) (universeConstants h (.core .power))

theorem false_source_fibre (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit} (ρ : Valuation Γ) :
    truthFibre h (.imp .top .bot) ρ = ∅ := by
  apply ZFSet.ext
  intro x
  simp only [mem_truthFibre, interpret, holds_truth, true_implies, and_false, ZFSet.notMem_empty]

theorem false_source_has_no_proof (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (ProofSyntax UniverseSymbol ([] : List (ClosedFormula UniverseSymbol))
      (.imp .top .bot)) := by
  rintro ⟨proof⟩
  have value := proofValue h proof (noHypotheses h emptyValuation)
  have claimed := ((mem_truthFibre h (.imp .top .bot) emptyValuation value.1).mp value.2).2
  simp only [interpret, holds_truth, true_implies] at claimed

#print axioms truthFibre_graph
#print axioms source_implication_decoder
#print axioms source_forall_decoder
#print axioms truthFibre_substitution
#print axioms quantifierBody_substitution
#print axioms source_forall_decoder_substitution
#print axioms source_implication_decoder_substitution
#print axioms source_dependent_family_agreement
#print axioms proofValue
#print axioms universalProofApp
#print axioms universalProofApp_trace
#print axioms higherOrderEtaApplication
#print axioms false_source_fibre
#print axioms false_source_has_no_proof

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceProofDecoding
