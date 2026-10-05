import Mettapedia.GSLT.Logic.ObservedGeneratedModel

/-!
# Source material transport of interpreted observed families

Every interpreted family has an actual graph dictionary and restriction
maps on observed contexts. Pulling that data back along the authored source
readout constructs a raw graph family, material member transport and its
observation-fibre law. Its natural sections give compatible source sections
with the same complete material values.

These constructions apply directly to decoded generated codes. They do not
choose a formation derivation or infer arbitrary raw-family admissibility
from predicate support.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedGeneratedFamilyDescent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualObservedFamilyEnclosure
open ContextualGeneratedUniverse
open ObservedGeneratedModel
open PowerClassPresheafDescent

universe u
variable {C : Type u} [Category.{u} C]
variable (profile : ContextualSystem C) (worlds : ArgumentCoding Cᵒᵖ)
variable (domain : MaterialFamily (ObservedGeneratedModel.context profile worlds))

def rawGraphs (point : profile.sourceFace.Elements) : AccessiblePointedGraph.{u} :=
  (domain.model (observedPoint profile worlds point)).graph

def rawArrow {X Y : Cᵒᵖ} (step : X ⟶ Y) (source : profile.sourceFace.obj X) :
    observedPoint profile worlds ⟨X, source⟩ ⟶
      observedPoint profile worlds ⟨Y, profile.sourceFace.map step source⟩ :=
  (classElements profile.sourceFace profile.classFace profile.observation).map
    (CategoryOfElements.homMk ⟨X, source⟩ ⟨Y, profile.sourceFace.map step source⟩ step rfl)

def rawMap {X Y : Cᵒᵖ} (step : X ⟶ Y) (source : profile.sourceFace.obj X)
    (member : El (· ∈ ·) (HSet.mk (rawGraphs profile worlds domain ⟨X, source⟩))) :
    El (· ∈ ·) (HSet.mk (rawGraphs profile worlds domain ⟨Y, profile.sourceFace.map step source⟩)) :=
  let moved := domain.memberRestriction (rawArrow profile worlds step source) ⟨member.1, member.2⟩;
  ⟨moved.1, moved.2⟩

theorem rawMap_value {X Y : Cᵒᵖ} (step : X ⟶ Y) (source : profile.sourceFace.obj X)
    (member : El (· ∈ ·) (HSet.mk (rawGraphs profile worlds domain ⟨X, source⟩))) :
    (rawMap profile worlds domain step source member).1 =
      (domain.model (observedPoint profile worlds ⟨Y, profile.sourceFace.map step source⟩)).value
        (domain.family.map (rawArrow profile worlds step source)
          ((domain.model (observedPoint profile worlds ⟨X, source⟩)).decode ⟨member.1, member.2⟩)) := rfl

private theorem arrow_heq {P : Cᵒᵖ ⥤ Type u}
    {first first' second second' : P.Elements} (sources : first = first') (targets : second = second')
    (left : first ⟶ second) (right : first' ⟶ second') (arrows : HEq left.1 right.1) : HEq left right := by
  cases sources
  cases targets
  exact heq_of_eq (Subtype.ext (eq_of_heq arrows))

private theorem familyMap_heq {D : Type u} [Category.{u} D] (family : D ⥤ Type u)
    {first first' second second' : D} (sources : first = first') (targets : second = second')
    (left : first ⟶ second) (right : first' ⟶ second') (arrows : HEq left right)
    (member : family.obj first) (member' : family.obj first') (members : HEq member member') :
    HEq (family.map left member) (family.map right member') := by
  cases sources
  cases targets
  cases eq_of_heq arrows
  cases eq_of_heq members
  rfl

private theorem modelValue_heq {first second : (ObservedGeneratedModel.context profile worlds).base.Elements}
    (points : first = second) (left : domain.family.obj first) (right : domain.family.obj second)
    (values : HEq left right) : (domain.model first).value left = (domain.model second).value right := by
  cases points
  cases eq_of_heq values
  rfl

private theorem decode_heq {first second : (ObservedGeneratedModel.context profile worlds).base.Elements}
    (points : first = second)
    (left : {value : HSet.{u} // value ∈ (domain.model first).carrier})
    (right : {value : HSet.{u} // value ∈ (domain.model second).carrier})
    (values : left.1 = right.1) : HEq ((domain.model first).decode left) ((domain.model second).decode right) := by
  cases points
  exact heq_of_eq (congrArg (domain.model first).decode (Subtype.ext values))

theorem rawGraphs_invariant (X : Cᵒᵖ) :
    PowerClassFamilyDescent.FamilyInvariant (profile.observation.app X)
      (fun value => rawGraphs profile worlds domain ⟨X, value⟩) := by
  intro left right same
  have points := (observedPoint_eq_iff profile worlds X left right).mpr
    ((profile.observation_eq_iff X left right).mp same)
  exact congrArg (fun point => (domain.model point).carrier) points

theorem rawMap_id_value (X : Cᵒᵖ) (source : profile.sourceFace.obj X)
    (member : El (· ∈ ·) (HSet.mk (rawGraphs profile worlds domain ⟨X, source⟩))) :
    (rawMap profile worlds domain (𝟙 X) source member).1 = member.1 := by
  let point := observedPoint profile worlds ⟨X, source⟩
  have targets : observedPoint profile worlds ⟨X, profile.sourceFace.map (𝟙 X) source⟩ = point :=
    congrArg (observedPoint profile worlds) (Sigma.ext rfl (heq_of_eq (profile.sourceFace.map_id_apply X source)))
  have arrows := arrow_heq rfl targets (rawArrow profile worlds (𝟙 X) source) (𝟙 point) (heq_of_eq rfl)
  have mapped := familyMap_heq domain.family rfl targets _ _ arrows
    ((domain.model point).decode ⟨member.1, member.2⟩) _ (heq_of_eq rfl)
  exact (rawMap_value profile worlds domain _ _ _).trans
    ((modelValue_heq profile worlds domain targets _ _ mapped).trans
      ((congrArg (domain.model point).value (domain.family.map_id_apply point _)).trans
        ((domain.model point).value_decode ⟨member.1, member.2⟩)))

theorem rawMap_comp_value {X Y Z : Cᵒᵖ} (first : X ⟶ Y) (second : Y ⟶ Z)
    (source : profile.sourceFace.obj X)
    (member : El (· ∈ ·) (HSet.mk (rawGraphs profile worlds domain ⟨X, source⟩))) :
    (rawMap profile worlds domain (first ≫ second) source member).1 =
      (rawMap profile worlds domain second (profile.sourceFace.map first source)
        (rawMap profile worlds domain first source member)).1 := by
  let atSource := observedPoint profile worlds ⟨X, source⟩
  let atMiddle := observedPoint profile worlds ⟨Y, profile.sourceFace.map first source⟩
  let atEnd := observedPoint profile worlds ⟨Z, profile.sourceFace.map second (profile.sourceFace.map first source)⟩
  have targets : observedPoint profile worlds ⟨Z, profile.sourceFace.map (first ≫ second) source⟩ = atEnd :=
    congrArg (observedPoint profile worlds) (Sigma.ext rfl (heq_of_eq (profile.sourceFace.map_comp_apply first second source)))
  have arrows := arrow_heq rfl targets (rawArrow profile worlds (first ≫ second) source)
    (rawArrow profile worlds first source ≫ rawArrow profile worlds second (profile.sourceFace.map first source)) (heq_of_eq rfl)
  let decoded := (domain.model atSource).decode ⟨member.1, member.2⟩
  have mapped := familyMap_heq domain.family rfl targets _ _ arrows decoded decoded (heq_of_eq rfl)
  have decodedMiddle : (domain.model atMiddle).decode
      ⟨(rawMap profile worlds domain first source member).1,
        (rawMap profile worlds domain first source member).2⟩ =
      domain.family.map (rawArrow profile worlds first source) decoded :=
    (domain.model atMiddle).decode.apply_symm_apply _
  exact (rawMap_value profile worlds domain _ _ _).trans
    ((modelValue_heq profile worlds domain targets _ _ mapped).trans
      ((congrArg (domain.model atEnd).value
        (domain.family.map_comp_apply (rawArrow profile worlds first source)
          (rawArrow profile worlds second (profile.sourceFace.map first source)) decoded)).trans
        ((congrArg (fun value => (domain.model atEnd).value
          (domain.family.map (rawArrow profile worlds second (profile.sourceFace.map first source)) value))
          decodedMiddle.symm).trans (rawMap_value profile worlds domain _ _ _).symm)))

theorem rawMap_compatible {X Y : Cᵒᵖ} (step : X ⟶ Y) :
    PowerClassPresheafDescent.MapCompatible (profile.observation.app X)
      (fun value => rawGraphs profile worlds domain ⟨X, value⟩) (profile.sourceFace.map step)
      (fun value => rawGraphs profile worlds domain ⟨Y, value⟩) (rawMap profile worlds domain step) := by
  intro left right related first second same
  have sourceEq := (observedPoint_eq_iff profile worlds X left right).mpr
    ((profile.observation_eq_iff X left right).mp related)
  have targetEq := (observedPoint_eq_iff profile worlds Y _ _).mpr
    (profile.bisim_restrict step ((profile.observation_eq_iff X left right).mp related))
  have arrows := arrow_heq sourceEq targetEq (rawArrow profile worlds step left)
    (rawArrow profile worlds step right) (heq_of_eq rfl)
  have decoded := decode_heq profile worlds domain sourceEq ⟨first.1, first.2⟩ ⟨second.1, second.2⟩ same
  have mapped := familyMap_heq domain.family sourceEq targetEq _ _ arrows _ _ decoded
  exact (rawMap_value profile worlds domain _ _ _).trans
    ((modelValue_heq profile worlds domain targetEq _ _ mapped).trans
      (rawMap_value profile worlds domain _ _ _).symm)

/-- Material source transport is constructed from interpreted family maps;
its admissibility laws follow from the exact observed kernel. -/
def rawTransport : MaterialTransport profile.sourceFace profile.classFace profile.observation
    (rawGraphs profile worlds domain) where
  invariant := rawGraphs_invariant profile worlds domain
  map := rawMap profile worlds domain
  map_id_value := rawMap_id_value profile worlds domain
  map_comp_value := rawMap_comp_value profile worlds domain
  compatible := rawMap_compatible profile worlds domain

def rawSection (term : domain.family.sections) : RawSection profile.sourceFace (rawGraphs profile worlds domain) :=
  fun point => ⟨(domain.model (observedPoint profile worlds point)).value
    (term.val (observedPoint profile worlds point)), (domain.model (observedPoint profile worlds point)).value_mem _⟩

theorem rawSection_compatible (term : domain.family.sections) :
    ContextualCompatible profile.sourceFace profile.classFace profile.observation (rawGraphs profile worlds domain)
      (rawTransport profile worlds domain) (rawSection profile worlds domain term) := by
  constructor
  · intro X left right same
    have points := (observedPoint_eq_iff profile worlds X left right).mpr
      ((profile.observation_eq_iff X left right).mp same)
    exact modelValue_heq profile worlds domain points _ _
      (PowerClassPresheafBaseChange.Cat.dependentValue_heq term.val points)
  · intro X Y step source
    exact (rawMap_value profile worlds domain step source (rawSection profile worlds domain term ⟨X, source⟩)).trans
      ((congrArg (fun value =>
        (domain.model (observedPoint profile worlds ⟨Y, profile.sourceFace.map step source⟩)).value
          (domain.family.map (rawArrow profile worlds step source) value))
        ((domain.model (observedPoint profile worlds ⟨X, source⟩)).decode_value _)).trans
          (congrArg (domain.model (observedPoint profile worlds ⟨Y, profile.sourceFace.map step source⟩)).value
            (term.property (rawArrow profile worlds step source))))

theorem rawSection_injective : Function.Injective (rawSection profile worlds domain) := by
  intro left right same
  apply Subtype.ext
  funext point
  obtain ⟨source, sourceEq⟩ := PowerClassFamilyDescent.classOf_surjective (profile.observation.app point.1) point.2
  have points : observedPoint profile worlds ⟨point.1, source⟩ = point := Sigma.ext rfl (heq_of_eq sourceEq)
  have values := congrArg (fun term => (term ⟨point.1, source⟩).1) same
  have terms := (domain.model (observedPoint profile worlds ⟨point.1, source⟩)).value_injective values
  exact eq_of_heq ((PowerClassPresheafBaseChange.Cat.dependentValue_heq left.val points).symm.trans
    ((heq_of_eq terms).trans (PowerClassPresheafBaseChange.Cat.dependentValue_heq right.val points)))

def reinterpret : MaterialFamily (ObservedGeneratedModel.context profile worlds) :=
  ObservedGeneratedModel.input profile worlds (rawGraphs profile worlds domain) (rawTransport profile worlds domain)

theorem reinterpret_carrier (point : (ObservedGeneratedModel.context profile worlds).base.Elements) :
    ((reinterpret profile worlds domain).model point).carrier = (domain.model point).carrier := by
  obtain ⟨source, sourceEq⟩ := PowerClassFamilyDescent.classOf_surjective (profile.observation.app point.1) point.2
  have points : observedPoint profile worlds ⟨point.1, source⟩ = point := Sigma.ext rfl (heq_of_eq sourceEq)
  exact (congrArg (fun point => ((reinterpret profile worlds domain).model point).carrier) points).symm.trans
    ((input_source_carrier profile worlds (rawGraphs profile worlds domain)
      (rawTransport profile worlds domain) ⟨point.1, source⟩).trans
      (congrArg (fun point => (domain.model point).carrier) points))

private def sameCarrierEquiv {first second : HSet.{u}} (same : first = second) :
    {value : HSet.{u} // value ∈ first} ≃ {value : HSet.{u} // value ∈ second} := by
  cases same
  exact Equiv.refl _

private theorem sameCarrierEquiv_value {first second : HSet.{u}} (same : first = second)
    (member : {value : HSet.{u} // value ∈ first}) : (sameCarrierEquiv same member).1 = member.1 := by
  cases same
  rfl

def fibreEquiv (point : (ObservedGeneratedModel.context profile worlds).base.Elements) :
    (reinterpret profile worlds domain).family.obj point ≃ domain.family.obj point :=
  (((reinterpret profile worlds domain).model point).decode.symm.trans
    (sameCarrierEquiv (reinterpret_carrier profile worlds domain point))).trans (domain.model point).decode

theorem fibreEquiv_value (point : (ObservedGeneratedModel.context profile worlds).base.Elements)
    (member : (reinterpret profile worlds domain).family.obj point) :
    (domain.model point).value (fibreEquiv profile worlds domain point member) =
      ((reinterpret profile worlds domain).model point).value member :=
  ((domain.model point).value_decode _).trans (sameCarrierEquiv_value _ _)

theorem fibreEquiv_natural {first second : (ObservedGeneratedModel.context profile worlds).base.Elements}
    (step : first ⟶ second) (member : (reinterpret profile worlds domain).family.obj first) :
    fibreEquiv profile worlds domain second ((reinterpret profile worlds domain).family.map step member) =
      domain.family.map step (fibreEquiv profile worlds domain first member) := by
  apply (domain.model second).value_injective
  obtain ⟨source, sourceEq⟩ := PowerClassFamilyDescent.classOf_surjective (profile.observation.app first.1) first.2
  let atSource : PowerClassPresheafDescent.ClassSources first.2 := ⟨source, by rw [← sourceEq]; rfl⟩
  let selected := PowerClassPresheafDescent.memberAt (profile.observation.app first.1)
    (fun candidate => rawGraphs profile worlds domain ⟨first.1, candidate⟩)
    ((rawTransport profile worlds domain).invariant first.1) first.2
    (contextualMemberEquiv profile.sourceFace profile.classFace profile.observation
      (rawGraphs profile worlds domain) first member) atSource
  have firstPoint : observedPoint profile worlds ⟨first.1, source⟩ = first := Sigma.ext rfl (heq_of_eq sourceEq)
  have secondClass : PowerClassFamilyDescent.classOf (profile.observation.app second.1)
      (profile.sourceFace.map step.1 source) = second.2 :=
    (classFace_map_class profile.sourceFace profile.classFace profile.observation step.1 source).symm.trans
      ((congrArg ((ObservedGeneratedModel.context profile worlds).base.map step.1) sourceEq).trans step.2)
  have secondPoint : observedPoint profile worlds ⟨second.1, profile.sourceFace.map step.1 source⟩ = second :=
    Sigma.ext rfl (heq_of_eq secondClass)
  have arrows := arrow_heq firstPoint secondPoint (rawArrow profile worlds step.1 source) step (heq_of_eq rfl)
  have selectedValue : selected.1 = (domain.model first).value (fibreEquiv profile worlds domain first member) :=
    (PowerClassPresheafDescent.memberAt_value _ _ _ _ _ _).trans
      ((input_value profile worlds (rawGraphs profile worlds domain) (rawTransport profile worlds domain) first member).symm.trans
        (fibreEquiv_value profile worlds domain first member).symm)
  have decoded := (decode_heq profile worlds domain firstPoint ⟨selected.1, selected.2⟩
    ((domain.model first).decode.symm (fibreEquiv profile worlds domain first member)) selectedValue).trans
      (heq_of_eq ((domain.model first).decode.apply_symm_apply _))
  have mapped := familyMap_heq domain.family firstPoint secondPoint _ _ arrows _ _ decoded
  exact (fibreEquiv_value profile worlds domain second _).trans
    ((input_value profile worlds (rawGraphs profile worlds domain) (rawTransport profile worlds domain) second _).trans
      ((contextualMemberMap_value profile.sourceFace profile.classFace profile.observation
        (rawGraphs profile worlds domain) (rawTransport profile worlds domain) step member atSource).trans
        ((rawMap_value profile worlds domain step.1 source selected).trans
          (modelValue_heq profile worlds domain secondPoint _ _ mapped))))

def reinterpretSectionEquiv : (reinterpret profile worlds domain).family.sections ≃ domain.family.sections where
  toFun term := ⟨fun point => fibreEquiv profile worlds domain point (term.val point), by
    intro first second step
    exact (fibreEquiv_natural profile worlds domain step (term.val first)).symm.trans
      (congrArg (fibreEquiv profile worlds domain second) (term.property step))⟩
  invFun term := ⟨fun point => (fibreEquiv profile worlds domain point).symm (term.val point), by
    intro first second step
    apply (fibreEquiv profile worlds domain second).injective
    exact (fibreEquiv_natural profile worlds domain step _).trans
      ((congrArg (domain.family.map step) ((fibreEquiv profile worlds domain first).apply_symm_apply _)).trans
        ((term.property step).trans ((fibreEquiv profile worlds domain second).apply_symm_apply _).symm))⟩
  left_inv term := Subtype.ext (funext fun point => (fibreEquiv profile worlds domain point).symm_apply_apply (term.val point))
  right_inv term := Subtype.ext (funext fun point => (fibreEquiv profile worlds domain point).apply_symm_apply (term.val point))

/-- Every compatible source material section is recovered as a genuine
section of the original interpreted family, with its restriction maps. -/
def compatibleSectionEquiv : domain.family.sections ≃
    {term : RawSection profile.sourceFace (rawGraphs profile worlds domain) //
      ContextualCompatible profile.sourceFace profile.classFace profile.observation (rawGraphs profile worlds domain)
        (rawTransport profile worlds domain) term} :=
  (reinterpretSectionEquiv profile worlds domain).symm.trans
    (sourceSectionEquiv profile worlds (rawGraphs profile worlds domain) (rawTransport profile worlds domain))

theorem compatibleSectionEquiv_value (term : domain.family.sections) (source : profile.sourceFace.Elements) :
    ((compatibleSectionEquiv profile worlds domain term).val source).1 =
      (rawSection profile worlds domain term source).1 := by
  have preserved := fibreEquiv_value profile worlds domain (observedPoint profile worlds source)
    ((fibreEquiv profile worlds domain (observedPoint profile worlds source)).symm
      (term.val (observedPoint profile worlds source)))
  rw [Equiv.apply_symm_apply] at preserved
  exact (sourceSectionEquiv_value profile worlds (rawGraphs profile worlds domain) (rawTransport profile worlds domain)
    ((reinterpretSectionEquiv profile worlds domain).symm term) source).symm.trans preserved.symm

variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (body : MaterialFamily domain.extension)

/-- The row of an abstracted function uses the arbitrary dependent body's
actual fibre decoder at the complete future argument index. -/
theorem pi_lambda_row (term : body.family.sections)
    (point : (ObservedGeneratedModel.context profile worlds).base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments domain.family point) :
    LabelledDependentProducts.evalValue (domain.futureCoding arrows point) (domain.futureOutputs body point)
      (((domain.pi body arrows).model point).value ((PowerClassPresheafProducts.piLambda term).val point)) argument =
        (body.model ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩).value
          (term.val ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩) :=
  (domain.pi_evaluation body arrows point _ argument).trans
    (congrArg (body.model ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩).value
      (PowerClassPresheafProducts.piLambda_value term point argument.1.1 argument.1.2 argument.2))

/-- Application after abstraction preserves the arbitrary dependent result
value at the actual observed source, including its selected argument. -/
theorem pi_application_source_beta (term : body.family.sections) (argument : domain.family.sections)
    (source : profile.sourceFace.Elements) :
    ((body.reindex (PowerClassPresheafProducts.sectionMap domain.family argument)).model
      (observedPoint profile worlds source)).value
      ((PowerClassPresheafProducts.piApply (PowerClassPresheafProducts.piLambda term) argument).val
        (observedPoint profile worlds source)) =
      (body.model ⟨source.1, ⟨(observedPoint profile worlds source).2,
        argument.val (observedPoint profile worlds source)⟩⟩).value
        (term.val ⟨source.1, ⟨(observedPoint profile worlds source).2,
          argument.val (observedPoint profile worlds source)⟩⟩) :=
  congrArg (fun chosen => ((body.reindex (PowerClassPresheafProducts.sectionMap domain.family argument)).model
    (observedPoint profile worlds source)).value (chosen.val (observedPoint profile worlds source)))
      (PowerClassPresheafProducts.pi_beta term argument)

theorem sigma_source_coordinates (source : profile.sourceFace.Elements)
    (pair : (domain.sigma body).family.obj (observedPoint profile worlds source)) :
    HSet.fst (((domain.sigma body).model (observedPoint profile worlds source)).value pair) =
      (domain.model (observedPoint profile worlds source)).value pair.1 ∧
    HSet.snd (((domain.sigma body).model (observedPoint profile worlds source)).value pair) =
      (body.model ⟨source.1, ⟨(observedPoint profile worlds source).2, pair.1⟩⟩).value pair.2 :=
  ⟨domain.sigma_first body _ pair, domain.sigma_second body _ pair⟩

theorem pi_substitution_decoder {other : LabelledContext C}
    (change : NatTrans other.base (ObservedGeneratedModel.context profile worlds).base)
    (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ (((domain.pi body arrows).reindex change).model point).carrier}) :
    ((domain.piUnder body arrows change).model point).decode
      (domain.piUnderMember body arrows change point member) =
        domain.piComparison body arrows change point
          ((((domain.pi body arrows).reindex change).model point).decode member) :=
  domain.piUnder_decoder body arrows change point member

theorem pi_source_section_compatible (term : (domain.pi body arrows).family.sections) :
    ContextualCompatible profile.sourceFace profile.classFace profile.observation
      (rawGraphs profile worlds (domain.pi body arrows))
      (rawTransport profile worlds (domain.pi body arrows))
      (rawSection profile worlds (domain.pi body arrows) term) :=
  rawSection_compatible profile worlds (domain.pi body arrows) term

theorem sigma_source_section_compatible (term : (domain.sigma body).family.sections) :
    ContextualCompatible profile.sourceFace profile.classFace profile.observation
      (rawGraphs profile worlds (domain.sigma body))
      (rawTransport profile worlds (domain.sigma body))
      (rawSection profile worlds (domain.sigma body) term) :=
  rawSection_compatible profile worlds (domain.sigma body) term

theorem w_source_section_compatible (term : (domain.w body arrows).family.sections) :
    ContextualCompatible profile.sourceFace profile.classFace profile.observation
      (rawGraphs profile worlds (domain.w body arrows))
      (rawTransport profile worlds (domain.w body arrows))
      (rawSection profile worlds (domain.w body arrows) term) :=
  rawSection_compatible profile worlds (domain.w body arrows) term

variable (graphs : profile.sourceFace.Elements → AccessiblePointedGraph.{u})
variable (transport : MaterialTransport profile.sourceFace profile.classFace profile.observation graphs)

theorem dependent_formation_enclosed
    (first : Generation (ObservedGeneratedModel.Seeds profile worlds)
      (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows domain)
    (second : Generation (ObservedGeneratedModel.Seeds profile worlds)
      (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows body)
    (point : (ObservedGeneratedModel.context profile worlds).base.Elements) :
    HSet.lift ((domain.pi body arrows).model point).carrier ∈
        enclosure (ObservedGeneratedModel.Seeds profile worlds)
          (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows
          (ObservedGeneratedModel.context profile worlds) point ∧
    HSet.lift ((domain.sigma body).model point).carrier ∈
        enclosure (ObservedGeneratedModel.Seeds profile worlds)
          (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows
          (ObservedGeneratedModel.context profile worlds) point ∧
    HSet.lift ((domain.w body arrows).model point).carrier ∈
        enclosure (ObservedGeneratedModel.Seeds profile worlds)
          (ObservedGeneratedModel.seedModel profile worlds graphs transport) arrows
          (ObservedGeneratedModel.context profile worlds) point :=
  ⟨generated_mem_enclosure _ _ _ (.pi first second) point,
    generated_mem_enclosure _ _ _ (.sigma first second) point,
    generated_mem_enclosure _ _ _ (.w first second) point⟩

def codeTransport (code : ObservedGeneratedModel.Code profile worlds arrows graphs transport
    (ObservedGeneratedModel.context profile worlds)) :
    MaterialTransport profile.sourceFace profile.classFace profile.observation
      (rawGraphs profile worlds (decodeCode profile worlds arrows graphs transport code)) :=
  rawTransport profile worlds (decodeCode profile worlds arrows graphs transport code)

theorem codeSection_compatible
    (code : ObservedGeneratedModel.Code profile worlds arrows graphs transport (ObservedGeneratedModel.context profile worlds))
    (term : (decodeCode profile worlds arrows graphs transport code).family.sections) :
    ContextualCompatible profile.sourceFace profile.classFace profile.observation
      (rawGraphs profile worlds (decodeCode profile worlds arrows graphs transport code))
      (codeTransport profile worlds arrows graphs transport code)
      (rawSection profile worlds (decodeCode profile worlds arrows graphs transport code) term) :=
  rawSection_compatible profile worlds (decodeCode profile worlds arrows graphs transport code) term

end Mettapedia.GSLT.ObservedGeneratedFamilyDescent
