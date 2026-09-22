import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientIdentityFrames
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityGeometry
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientBasedContextRepresentation

/-!
# Coverage of admitted native identity motives on the shared quotient

The native declaration telescope determines the required input domain.
Identity formation, reflexivity and the canonical based-context section
are actual quotient operations. No total elimination function, added
universe rule, K/UIP principle or reduced constant-motive scope is supplied.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientMotiveCoverage

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment FormationSensitiveContextual
open SharedJudgmentQuotientInterpretation SharedJudgmentTypeInterpretation
open Mettapedia.TypeTheory
open ContextualBasedIdentityOperations (basedContext baseProjection rightEndpoint witnessType)

variable {assembly : Assembly}

@[reducible] noncomputable def frames (assembly : Assembly) :
    FrameOperations (QuotientCwf.cwf assembly.rules) where
  identity := QuotientIdentity.formation assembly.rules
  reflexivity := QuotientIdentity.reflexivity assembly.rules
  reflSection := QuotientIdentityGeometry.reflSection

/-- The native telescope carries all four actual parameters. Its typed
substitution is not replaced by an assumed J result. -/
def nativeInput {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    QuotientIdentity.Based.Admitted (context source) where
  type := type
  left := left
  motive := motive
  method := method
  typed := parameters.2

/-- The source parameters construct all raw frame data. The canonical
section comparison is derived from actual typed substitutions, not supplied
as an additional admission premise. -/
noncomputable def nativeFrame {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    JFrame (data assembly) (frames assembly) source type left motive method where
  contextFormation := (nativeInput source parameters).basedContext.formed
  semanticType := QType.mk (nativeInput source parameters).element
  semanticLeft := TermFibre.mk (nativeInput source parameters).leftTerm
  motive := QuotientCwf.tySub (QType.mk (nativeInput source parameters).motiveType)
    (nativeInput source parameters).presentation.hom
  base := TermFibre.compare
    (QuotientIdentityGeometry.admitted_motive_reflexivity (nativeInput source parameters)).symm
    (nativeInput source parameters).base
  comparison := ⟨(nativeInput source parameters).presentation.inv,
    (nativeInput source parameters).presentation.hom⟩
  reflexivityMap := QuotientCwf.project (nativeInput source parameters).reflSection

private theorem type_inverse {Head : Type} {rules : Rules Head}
    {source target : QuotientCwf.QContext rules} (iso : source ≅ target)
    (family : QuotientCwf.Ty target) :
    QuotientCwf.tySub (QuotientCwf.tySub family iso.hom) iso.inv = family := by
  rw [← QuotientCwf.tySub_comp, iso.inv_hom_id, QuotientCwf.tySub_id]

/-- All frame clauses are attached to the same submitted native tuple:
the actual variable meanings fix the comparison and the actual method
fixes the reflexivity fibre. -/
theorem native_frame_meaning {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    JFrameMeaning (data assembly) (frames assembly) (nativeFrame source parameters) := by
  let input := nativeInput source parameters
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact QuotientInterpretation.type_meaning (context source) input.element
  · exact QuotientInterpretation.term_meaning (context source) input.leftTerm
  · exact ⟨input.presentation.hom_inv_id, input.presentation.inv_hom_id⟩
  · exact QuotientBasedContextRepresentation.admitted_projection_meaning input
  · exact QuotientBasedContextRepresentation.admitted_right_meaning input
  · exact QuotientBasedContextRepresentation.admitted_witness_meaning input
  · exact ⟨input.reflSection.typed, rfl⟩
  · exact QuotientIdentityGeometry.admitted_comparison input
  · exact ⟨input.motiveType, rfl,
      (type_inverse input.presentation (QType.mk input.motiveType)).symm⟩
  · exact ⟨input.methodType, rfl,
      (QuotientIdentityGeometry.admitted_motive_reflexivity input).symm⟩
  · exact ⟨input.methodType, rfl, input.nativeMethod, rfl,
      (QuotientIdentityGeometry.admitted_motive_reflexivity input).symm, rfl⟩

/-- The quantifier is the complete authored native telescope, over every
formed source context; no constant-motive or closed-context restriction. -/
theorem based_motive_coverage :
    BasedMotiveCoverage (data assembly) (frames assembly) := by
  intro n source type left motive method parameters
  exact ⟨nativeFrame source parameters, native_frame_meaning source parameters⟩

/-- An independently supplied qualified frame is the constructed frame;
this uniqueness concerns one fixed request, not arbitrary identity proofs. -/
theorem native_frame_unique {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method)
    {frame : JFrame (data assembly) (frames assembly) source type left motive method}
    (meaning : JFrameMeaning (data assembly) (frames assembly) frame) :
    frame = nativeFrame source parameters :=
  SharedJudgmentQuotientIdentityFrames.frame_unique meaning (native_frame_meaning source parameters)

/-- This constructor is defined on every submitted native parameter tuple.
Its domain is explicit; it is not a total operation on all ambient families. -/
noncomputable def nativeJ {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    QuotientCwf.Tm _ (nativeFrame source parameters).motive :=
  (nativeInput source parameters).chosenJ

private theorem term_inverse {Head : Type} {rules : Rules Head}
    {source target : QuotientCwf.QContext rules} (iso : source ≅ target)
    {type : QuotientCwf.Ty target} (value : QuotientCwf.Tm target type) :
    (QuotientCwf.tmSub (QuotientCwf.tmSub value iso.hom) iso.inv).val = value.val := by
  change QuotientCwf.totalSub (QuotientCwf.totalSub value.val iso.hom) iso.inv = value.val
  rw [← QuotientCwf.totalSub_comp, iso.inv_hom_id, QuotientCwf.totalSub_id]

/-- The actual submitted J term, including its retained endpoint and path
variables, has its native motive meaning through the same frame. -/
theorem native_j_meaning {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    (data assembly).term (nativeFrame source parameters).context
      (FormationSensitiveBasedIdentity.genericTerm type left motive method)
      (FormationSensitiveBasedIdentity.motiveBody motive)
      (QuotientCwf.tySub (nativeFrame source parameters).motive
        (nativeFrame source parameters).comparison.forward)
      (QuotientCwf.tmSub (nativeJ source parameters)
        (nativeFrame source parameters).comparison.forward) := by
  let input := nativeInput source parameters
  exact ⟨input.motiveType, rfl, input.nativeJ, rfl,
    (type_inverse input.presentation (QType.mk input.motiveType)).symm,
    (term_inverse input.presentation input.j).symm⟩

/-- Reflexivity returns the actual method in its original dependent fibre.
No separate equality policy or assumption about the desired result is used. -/
theorem native_j_beta {n : Nat}
    (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    QuotientCwf.tmSub (nativeJ source parameters)
      ((frames assembly).reflSection (nativeFrame source parameters).semanticLeft) =
      (nativeFrame source parameters).base :=
  Subtype.ext (QuotientIdentityGeometry.admitted_beta_value (nativeInput source parameters))

theorem based_boundary :
    AdmittedBasedBoundary (data assembly) (frames assembly) := by
  intro n source type left motive method frame _ _
  exact ⟨QuotientIdentityGeometry.endpoint frame.semanticLeft,
    QuotientIdentityGeometry.witness frame.semanticLeft⟩

namespace Controls

/-- Even when all four parameters are variables, the complete declared
telescope has exactly one frame with the required independent meanings. -/
theorem variable_frame (assembly : Assembly) :
    ∃! frame : JFrame (data assembly) (frames assembly)
        (SharedJudgmentTypeInterpretation.Controls.sourceContext assembly)
        (.var 3) (.var 2) (.var 1) (.var 0),
      JFrameMeaning (data assembly) (frames assembly) frame := by
  let source := SharedJudgmentTypeInterpretation.Controls.sourceContext assembly
  have parameters := SharedJudgmentTypeInterpretation.Controls.parameters assembly
  exact ⟨nativeFrame source parameters, native_frame_meaning source parameters,
    fun _ meaning => native_frame_unique parameters meaning⟩

/-- The mixed HOL/list/wire input has a path-dependent motive and actual
projected endpoint. The same shared interpretation receives its full frame. -/
theorem mixed_frame (wire : NativeWireData.Wire) :
    ∃! frame : JFrame (data common) (frames common)
        (SharedJudgmentInterpretation.Context.nil)
        (QuotientIdentity.Controls.mixedInput wire).type
        (QuotientIdentity.Controls.mixedInput wire).left
        (QuotientIdentity.Controls.mixedInput wire).motive
        (QuotientIdentity.Controls.mixedInput wire).method,
      JFrameMeaning (data common) (frames common) frame := by
  have parameters := (QuotientIdentity.Controls.mixedInput wire).parameters
  exact ⟨nativeFrame .nil parameters, native_frame_meaning .nil parameters,
    fun _ meaning => native_frame_unique parameters meaning⟩

/-- A qualified frame cannot conflate the endpoint with its retained path.
This is a negative control on the actual native conversion, not a new policy. -/
theorem endpoint_is_not_path
    (opacity : OpaqueRelatorExtension.Opacity assembly.declarations)
    {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    let frame := nativeFrame source parameters
    (QuotientCwf.tmSub (rightEndpoint (frames assembly).identity frame.semanticLeft)
      frame.comparison.forward).val ≠
    (QuotientCwf.tmSub
      (QuotientCwf.vz (witnessType (frames assembly).identity frame.semanticLeft))
      frame.comparison.forward).val :=
  QuotientBasedContextRepresentation.admitted_right_ne_witness opacity
    (nativeInput source parameters)

end Controls

#print axioms native_frame_meaning
#print axioms based_motive_coverage
#print axioms native_frame_unique
#print axioms native_j_meaning
#print axioms native_j_beta
#print axioms based_boundary
#print axioms Controls.variable_frame
#print axioms Controls.mixed_frame
#print axioms Controls.endpoint_is_not_path

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientMotiveCoverage
