import Mettapedia.Logic.HOL.Embedding.ZFSetContextualIdentity
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceProofDecoding

/-!
# Original HOL equality proofs consumed by contextual identity

The truth fibre of an original HOL equality formula is literally the
set-coded contextual identity fibre of its interpreted endpoints.  A retained
HOL proof therefore supplies an actual identity section, which the full
dependent `J` operation can consume without rebuilding a second proof.

The bridge concerns the extensional trace/set interpretation.  A commuting
theorem for compiled native proof terms is a further, typed interpretation
result.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceIdentityBridge

open ZFSetDependentProducts (Elements)
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetUniverseInterpretation (UniverseSymbol UniverseExpr)
open ZFSetHOLTraceTypeInterpretation (typeCode)
open ZFSetHOLTypeInterpretation (truth truth_false_ne_truth_true)
open ZFSetHOLTraceTermInterpretation (Valuation interpret universeConstants emptyValuation)
open ZFSetHOLTraceProofDecoding (CodedSatisfied truthFibre proofValue noHypotheses)
open ZFSetContextualInterpretation (SetFamily Section Extension codedCwf)
open ZFSetContextualIdentity

universe u

variable (h : CofinalInaccessibles.{u})
variable {Γ : Ctx Unit} {hypotheses : List (Formula UniverseSymbol Γ)}

@[reducible] noncomputable def sourceTypeFamily (A : Ty Unit) :
    SetFamily.{u + 1} (CodedSatisfied h hypotheses) := fun _ => typeCode.{u} A

noncomputable def sourceTermSection {A : Ty Unit} (term : UniverseExpr Γ A) :
    Section (sourceTypeFamily h (hypotheses := hypotheses) A) :=
  fun ρ => interpret (universeConstants h) term ρ.1

/-- The two constructions produce equal `ZFSet` codes, not merely equivalent
membership types. -/
theorem source_equality_fibre {A : Ty Unit} (left right : UniverseExpr Γ A)
    (ρ : CodedSatisfied h hypotheses) :
    truthFibre h (.eq left right) ρ.1 =
      identityFamily (sourceTypeFamily h (hypotheses := hypotheses) A)
        (sourceTermSection h left) (sourceTermSection h right) ρ := by
  unfold truthFibre identityFamily sourceTermSection
  apply congrArg ZFSetTraceProofDecoding.truthCode
  exact propext (ZFSetHOLTypeInterpretation.holds_truth _)

noncomputable def sourceIdentityWitness {A : Ty Unit}
    {left right : UniverseExpr Γ A}
    (proof : ProofSyntax UniverseSymbol hypotheses (.eq left right))
    (ρ : CodedSatisfied h hypotheses) :
    Elements
      (identityFamily (sourceTypeFamily h (hypotheses := hypotheses) A)
        (sourceTermSection h left) (sourceTermSection h right) ρ) :=
  ⟨(proofValue h proof ρ).1,
    (source_equality_fibre h left right ρ) ▸ (proofValue h proof ρ).2⟩

noncomputable def sourceIdentitySection {A : Ty Unit}
    {left right : UniverseExpr Γ A}
    (proof : ProofSyntax UniverseSymbol hypotheses (.eq left right)) :
    Section
      (identityFamily (sourceTypeFamily h (hypotheses := hypotheses) A)
        (sourceTermSection h left) (sourceTermSection h right)) :=
  sourceIdentityWitness h proof

theorem source_identity_reflects_terms {A : Ty Unit}
    {left right : UniverseExpr Γ A}
    (proof : ProofSyntax UniverseSymbol hypotheses (.eq left right)) :
    sourceTermSection h (hypotheses := hypotheses) left =
      sourceTermSection h (hypotheses := hypotheses) right :=
  inhabited_identity_reflects_endpoints _ _ _ (sourceIdentitySection h proof)

noncomputable def sourceIdentityPoint {A : Ty Unit}
    {left right : UniverseExpr Γ A}
    (proof : ProofSyntax UniverseSymbol hypotheses (.eq left right))
    (ρ : CodedSatisfied h hypotheses) :
    formation.identityContext (sourceTypeFamily h (hypotheses := hypotheses) A) :=
  ⟨⟨⟨ρ, sourceTermSection h left ρ⟩, sourceTermSection h right ρ⟩,
    sourceIdentityWitness h proof ρ⟩

/-- An arbitrary dependent set-valued motive consumes the retained original
HOL proof through the actual contextual `J` operation. -/
noncomputable def consumeSourceEquality {A : Ty Unit}
    {left right : UniverseExpr Γ A}
    (proof : ProofSyntax UniverseSymbol hypotheses (.eq left right))
    (motive : SetFamily
      (formation.identityContext (sourceTypeFamily h (hypotheses := hypotheses) A)))
    (base : Section
      (codedCwf.tySub motive
        (elimination.reflexivitySubstitution
          (sourceTypeFamily h (hypotheses := hypotheses) A))))
    (ρ : CodedSatisfied h hypotheses) :
    Elements (motive (sourceIdentityPoint h proof ρ)) :=
  elimination.j motive base (sourceIdentityPoint h proof ρ)

noncomputable def endpointSingletonMotive {A : Ty Unit} :
    SetFamily
      (formation.identityContext (sourceTypeFamily h (hypotheses := hypotheses) A)) :=
  fun point => {(point.1.1.2).1}

noncomputable def endpointSingletonBase {A : Ty Unit} :
    Section
      (codedCwf.tySub (endpointSingletonMotive h (hypotheses := hypotheses) (A := A))
        (elimination.reflexivitySubstitution
          (sourceTypeFamily h (hypotheses := hypotheses) A))) :=
  fun point => ⟨point.2.1, ZFSet.mem_singleton.mpr rfl⟩

/-- A concrete dependent consumer returns an element of the singleton indexed
by the proof's left endpoint.  The output is constrained by the motive, rather
than being postulated to equal the source value. -/
noncomputable def consumeEndpoint {A : Ty Unit}
    {left right : UniverseExpr Γ A}
    (proof : ProofSyntax UniverseSymbol hypotheses (.eq left right))
    (ρ : CodedSatisfied h hypotheses) :
    Elements
      (endpointSingletonMotive h (hypotheses := hypotheses)
        (sourceIdentityPoint h proof ρ)) :=
  consumeSourceEquality h proof (endpointSingletonMotive h) (endpointSingletonBase h) ρ

theorem consumeEndpoint_value {A : Ty Unit}
    {left right : UniverseExpr Γ A}
    (proof : ProofSyntax UniverseSymbol hypotheses (.eq left right))
    (ρ : CodedSatisfied h hypotheses) :
    (consumeEndpoint h proof ρ).1 = (sourceTermSection h left ρ).1 :=
  ZFSet.mem_singleton.mp (consumeEndpoint h proof ρ).2

/-! ## A false source equality cannot cross the bridge -/

def falseEquality : ClosedFormula UniverseSymbol := .eq .top .bot

theorem false_equality_has_no_source_proof (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty
      (ProofSyntax UniverseSymbol ([] : List (ClosedFormula UniverseSymbol)) falseEquality) := by
  rintro ⟨proof⟩
  have equalSections := source_identity_reflects_terms h proof
  have equalValues := congrFun equalSections (noHypotheses h emptyValuation)
  apply truth_false_ne_truth_true
  simpa only [sourceTermSection, ZFSetHOLTraceTermInterpretation.interpret] using equalValues.symm

#print axioms source_equality_fibre
#print axioms sourceIdentityWitness
#print axioms source_identity_reflects_terms
#print axioms consumeSourceEquality
#print axioms consumeEndpoint_value
#print axioms false_equality_has_no_source_proof

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceIdentityBridge
