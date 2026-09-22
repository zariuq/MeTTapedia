import Mettapedia.Logic.HOL.Embedding.ZFSetContextualIdentity
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListProofConsumption
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTermInterpretation

/-!
# The retained map-fusion proof consumed by contextual identity

The original intrinsically typed HOL proof tree is interpreted in the actual
uniform-list model, encoded in the trace proof fibre, and applied three times
through literal trace products.  Its final equality fibre is the same set as
the contextual identity fibre of the two interpreted list terms.  Full
dependent `J` can therefore consume that retained source proof.

This construction neither rebuilds map fusion semantically nor identifies a
compiled native proof term with the source proof.  Native attachment requires
an additional typed proof-term interpretation and commuting theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceProofBridge

open UniformListInduction UniformListMapFusion
open ZFSetDependentProducts
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open ZFSetHOLTypeInterpretation (holds holds_truth)
open ZFSetContextualInterpretation (SetFamily Section Extension codedCwf)
open ZFSetContextualIdentity
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation

universe u

theorem formula_agreement {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    (φ : Formula Symbol Γ) (ρ : Valuation a Γ) :
    holds (interpret φ ρ) ↔
      ((ZFSetUniformListModel.model a).denote φ (decodeValuation ρ)).down :=
  iff_of_eq (congrArg ULift.down (term_agreement φ ρ))

noncomputable def decodeContext {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    (ρ : Valuation a Γ) : AdmissibleContext (ZFSetUniformListModel.model a) Γ :=
  ⟨decodeValuation ρ, fun _ => trivial⟩

abbrev CodedSatisfied (a : ZFSet.{u}) {Γ : Ctx BaseSort}
    (hypotheses : List (Formula Symbol Γ)) :=
  {ρ : Valuation a Γ // ∀ φ ∈ hypotheses, holds (interpret φ ρ)}

noncomputable def decodeSatisfied {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    {hypotheses : List (Formula Symbol Γ)} (ρ : CodedSatisfied a hypotheses) :
    SatisfiedContext (ZFSetUniformListModel.model a) hypotheses :=
  ⟨decodeContext ρ.1, fun φ member => (formula_agreement φ ρ.1).mp (ρ.2 φ member)⟩

noncomputable def truthFibre {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    (φ : Formula Symbol Γ) (ρ : Valuation a Γ) : ZFSet.{u} :=
  ZFSetTraceProofDecoding.truthCode (holds (interpret φ ρ))

theorem mem_truthFibre {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    (φ : Formula Symbol Γ) (ρ : Valuation a Γ) (x : ZFSet.{u}) :
    x ∈ truthFibre φ ρ ↔ x = ∅ ∧ holds (interpret φ ρ) :=
  ZFSetTraceProofDecoding.mem_truthCode _ x

/-- The retained source proof tree supplies the witness.  The semantic
soundness theorem is used only to establish membership in its trace fibre. -/
noncomputable def proofValue {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    {hypotheses : List (Formula Symbol Γ)} {φ : Formula Symbol Γ}
    (proof : ProofSyntax Symbol hypotheses φ) (ρ : CodedSatisfied a hypotheses) :
    Elements (truthFibre φ ρ.1) :=
  ⟨∅, (mem_truthFibre φ ρ.1 ∅).mpr ⟨rfl, (formula_agreement φ ρ.1).mpr
    (proofSection (ZFSetUniformListModel.model a) (ZFSetUniformListModel.respects a)
      proof (decodeSatisfied ρ)).down.down⟩⟩

@[reducible] noncomputable def quantifierDomain (a : ZFSet.{u})
    (Γ : Ctx BaseSort) (A : Ty BaseSort) : SetFamily (Valuation a Γ) :=
  fun _ => typeCode a A

noncomputable def quantifierBody {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    {A : Ty BaseSort} (φ : Formula Symbol (A :: Γ)) :
    SetFamily (Extension (quantifierDomain a Γ A)) :=
  fun pair => truthFibre φ (extend pair.1 pair.2)

theorem source_forall_decoder {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    {A : Ty BaseSort} (φ : Formula Symbol (A :: Γ)) :
    (fun ρ => truthFibre (.all φ) ρ) =
      ZFSetTraceContextual.piFamily (quantifierDomain a Γ A) (quantifierBody φ) := by
  funext ρ
  have generic := congrFun
    (ZFSetTraceProofDecoding.forall_decoder (quantifierDomain a Γ A)
      (fun pair => holds (interpret φ (extend pair.1 pair.2)))) ρ
  have source : truthFibre (.all φ) ρ = ZFSetTraceProofDecoding.truthCode
      (∀ x : Value a A, holds (interpret φ (extend ρ x))) := by
    unfold truthFibre
    apply congrArg ZFSetTraceProofDecoding.truthCode
    exact propext (holds_truth _)
  exact source.trans generic

noncomputable def universalValueApp {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    {A : Ty BaseSort} {φ : Formula Symbol (A :: Γ)} (ρ : Valuation a Γ)
    (value : Elements (truthFibre (.all φ) ρ)) (x : Value a A) :
    Elements (truthFibre φ (extend ρ x)) :=
  let function : Elements
      (ZFSetTraceContextual.piFamily (quantifierDomain a Γ A) (quantifierBody φ) ρ) :=
    ⟨value.1, (congrFun (source_forall_decoder φ) ρ) ▸ value.2⟩
  ZFSetTraceContextual.piDecode (quantifierDomain a Γ A) (quantifierBody φ) ρ function x

noncomputable def codedTheory (a : ZFSet.{u}) :
    CodedSatisfied a (theory (Γ := [])) :=
  ⟨(show Valuation a [] from emptyValuation), by
    intro φ member
    apply (formula_agreement φ (show Valuation a [] from emptyValuation)).mpr
    refine Eq.mp ?_ (ZFSetUniformListModel.theory_valid a φ member)
    unfold HenkinModel.models PreModel.models
    apply congrArg ULift.down
    apply congrArg (PreModel.denote (ZFSetUniformListModel.model a).toPreModel φ)
    funext A boundVar
    nomatch boundVar⟩

abbrev fusionBody : Formula Symbol [sequence, mapping, mapping] :=
  fuses (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)

noncomputable def fusionValuation {a : ZFSet.{u}} (f g : Value a mapping)
    (xs : Value a sequence) : Valuation a [sequence, mapping, mapping]
  | _, .vz => xs
  | _, .vs .vz => g
  | _, .vs (.vs .vz) => f

/-- Three source universal eliminations are trace applications of the one
retained `mapFusionProof`, in source binder order `f`, `g`, `xs`. -/
noncomputable def fusionProofValue {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (truthFibre fusionBody (fusionValuation f g xs)) := by
  let root := proofValue (a := a) mapFusionProof (codedTheory a)
  let atF := universalValueApp emptyValuation root f
  let atG := universalValueApp (extend emptyValuation f) atF g
  let atXs := universalValueApp (extend (extend emptyValuation f) g) atG xs
  exact atXs

@[reducible] noncomputable def sequenceFamily (a : ZFSet.{u}) : SetFamily PUnit :=
  fun _ => typeCode a sequence

noncomputable def beforeSection {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) : Section (sequenceFamily a) :=
  fun _ => interpret
    (map (.var (.vs (.vs .vz))) (map (.var (.vs .vz)) (.var .vz)))
    (fusionValuation f g xs)

noncomputable def afterSection {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) : Section (sequenceFamily a) :=
  fun _ => interpret
    (map (compose (.var (.vs (.vs .vz))) (.var (.vs .vz))) (.var .vz))
    (fusionValuation f g xs)

/-- The final source proof fibre and dependent identity fibre are literally
the same set code. -/
theorem fusion_fibre_identity {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    truthFibre fusionBody (fusionValuation f g xs) =
      identityFamily (sequenceFamily a) (beforeSection f g xs)
        (afterSection f g xs) PUnit.unit := by
  unfold truthFibre identityFamily fusionBody beforeSection afterSection
  apply congrArg ZFSetTraceProofDecoding.truthCode
  exact propext (holds_truth _)

noncomputable def fusionIdentityWitness {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (identityFamily (sequenceFamily a) (beforeSection f g xs)
      (afterSection f g xs) PUnit.unit) :=
  ⟨(fusionProofValue f g xs).1,
    fusion_fibre_identity f g xs ▸ (fusionProofValue f g xs).2⟩

noncomputable def fusionIdentityPoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    formation.identityContext (sequenceFamily a) :=
  ⟨⟨⟨PUnit.unit, beforeSection f g xs PUnit.unit⟩,
      afterSection f g xs PUnit.unit⟩, fusionIdentityWitness f g xs⟩

/-- An arbitrary dependent set-valued motive consumes the source map-fusion
proof through the actual contextual `J` operation. -/
noncomputable def consumeFusionEquality {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence)
    (motive : SetFamily (formation.identityContext (sequenceFamily a)))
    (base : Section (codedCwf.tySub motive
      (elimination.reflexivitySubstitution (sequenceFamily a)))) :
    Elements (motive (fusionIdentityPoint f g xs)) :=
  elimination.j motive base (fusionIdentityPoint f g xs)

noncomputable def endpointMotive {a : ZFSet.{u}} :
    SetFamily (formation.identityContext (sequenceFamily a)) :=
  fun point => {point.1.1.2.1}

noncomputable def endpointBase {a : ZFSet.{u}} :
    Section (codedCwf.tySub endpointMotive
      (elimination.reflexivitySubstitution (sequenceFamily a))) :=
  fun point => ⟨point.2.1, ZFSet.mem_singleton.mpr rfl⟩

noncomputable def consumedEndpoint {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    Elements (endpointMotive (fusionIdentityPoint f g xs)) :=
  consumeFusionEquality f g xs endpointMotive endpointBase

theorem endpointMotive_value {a : ZFSet.{u}}
    {point : formation.identityContext (sequenceFamily a)}
    (value : Elements (endpointMotive point)) :
    value.1 = point.1.1.2.1 :=
  ZFSet.mem_singleton.mp value.2

/-- The reversed-composition sentence has no inhabitant in the same trace
proof interpretation.  This is inherited from its concrete two-element
countermodel, rather than from failure of proof search. -/
theorem wrongFusion_trace_uninhabited :
    ¬ Nonempty (Elements (truthFibre
      (UniformListMapFusion.Controls.wrongFusion (Γ := []))
      (emptyValuation : Valuation
        ZFSetUniformListProofConsumption.Controls.two []))) := by
  rintro ⟨value⟩
  have encodedHolds := (mem_truthFibre
    (UniformListMapFusion.Controls.wrongFusion (Γ := []))
    (emptyValuation : Valuation
      ZFSetUniformListProofConsumption.Controls.two []) value.1).mp value.2
  have semantic := (formula_agreement
    (UniformListMapFusion.Controls.wrongFusion (Γ := []))
    (emptyValuation : Valuation
      ZFSetUniformListProofConsumption.Controls.two [])).mp encodedHolds.2
  apply ZFSetUniformListProofConsumption.Controls.wrongFusion_invalid
  unfold HenkinModel.models PreModel.models
  refine Eq.mp ?_ semantic
  apply congrArg ULift.down
  apply congrArg (PreModel.denote
    (ZFSetUniformListModel.model
      ZFSetUniformListProofConsumption.Controls.two).toPreModel
    (UniformListMapFusion.Controls.wrongFusion (Γ := [])))
  funext A boundVar
  nomatch boundVar

#print axioms formula_agreement
#print axioms proofValue
#print axioms source_forall_decoder
#print axioms universalValueApp
#print axioms codedTheory
#print axioms fusionProofValue
#print axioms fusion_fibre_identity
#print axioms fusionIdentityWitness
#print axioms consumeFusionEquality
#print axioms endpointMotive_value
#print axioms wrongFusion_trace_uninhabited

end Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceProofBridge
