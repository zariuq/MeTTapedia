import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingSteps
import Mettapedia.Languages.ProcessCalculi.Ambient.CommEquivalences
import Mettapedia.Languages.ProcessCalculi.Ambient.FullObjects
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Extensions

/-!
# The laws of ambients with paths, by shape

Every instance of a law of the calculus with paths and communication, and every law of its bag, relates terms of a
shape, one way or the other (`comm_generator_shape`): a shape of the core's laws, or of the laws of paths
(`CommShape`). The laws are plain (`comm_plain`): none has premises, and a raw one instantiates its other side
plainly, so the reference relation's equation steps are the static theory's.

The shapes read through object terms (`commShapes`), so a chain of laws between object processes passes through
object processes only (`comm_objectChain`). A shape's source is no variable, no abstraction and no capability, so no
law applies inside a name or a capability term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (Bindings matchPattern applyBindings isMatchCorrectAux isMatchCorrectListAux)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (matchPattern_sound matchRel_correct)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (notDeeper notDeeperList captureSitesOf)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator EquationInstanceAt readsRaw readsRaw_of_none)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext HoleType ObjectChain ObjectShapes ProcEquiv PlainLaws
  closeTails closeTailsList substFree substFreeList derived_mono objectChain_mono final_of_premises_nil)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbShape ambient_instance_shape ambient_derived_shape
  ambient_premises_nil ambient_raw_notDeeper ambientRepBlock ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (procType cap_apply_inv shape_not_cap)

/-! ## The shapes -/

/-- **The shapes of the laws with paths**: those of the core's laws and those of the laws of paths. -/
inductive CommShape : Pattern → Pattern → Prop where
  | core {source target : Pattern} (shape : AmbShape source target) : CommShape source target
  | path {source target : Pattern} (shape : PathShape source target) : CommShape source target

/-- The laws of paths, one by one. -/
theorem pathLaw_cases {equation : Equation} (listed : equation ∈ pathLaws) :
    equation = pathEps ∨ equation = pathDot ∨ ∃ cap fused,
      (cap, fused) ∈ [("CapIn", "AIn"), ("CapOut", "AOut"), ("CapOpen", "AOpen")] ∧ equation = capPrefix cap fused := by
  simp only [pathLaws, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨_, _, by simp, rfl⟩)
  · exact .inr (.inr ⟨_, _, by simp, rfl⟩)
  · exact .inr (.inr ⟨_, _, by simp, rfl⟩)

/-- **A law of paths read from left to right relates a shape.** -/
theorem path_forward {equation : Equation} (listed : equation ∈ pathLaws) {bindings : Bindings}
    {source target : Pattern} (matched : bindings ∈ matchPattern equation.left source)
    (applied : applyBindings bindings equation.right = target) : PathShape source target := by
  have related := matchPattern_sound matched
  rcases pathLaw_cases listed with rfl | rfl | ⟨cap, fused, capListed, rfl⟩
  · have rebuilt := matchRel_correct related (by decide)
    subst rebuilt applied
    simp only [pathEps, applyBindings, List.map_cons, List.map_nil]
    exact .eps _
  · have rebuilt := matchRel_correct related (by decide)
    subst rebuilt applied
    simp only [pathDot, applyBindings, List.map_cons, List.map_nil]
    exact .dot _ _ _
  · have rebuilt := matchRel_correct related (by simp [capPrefix, Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect,
      isMatchCorrectAux, isMatchCorrectListAux])
    subst rebuilt applied
    simp only [capPrefix, applyBindings, List.map_cons, List.map_nil]
    exact .capPrefix capListed _ _

/-- **A law of paths read from right to left relates a shape, reversed.** -/
theorem path_reverse {equation : Equation} (listed : equation ∈ pathLaws) {bindings : Bindings}
    {source target : Pattern} (matched : bindings ∈ matchPattern equation.right source)
    (applied : applyBindings bindings equation.left = target) : PathShape target source := by
  have related := matchPattern_sound matched
  rcases pathLaw_cases listed with rfl | rfl | ⟨cap, fused, capListed, rfl⟩
  · have rebuilt := matchRel_correct related (by decide)
    subst rebuilt applied
    simp only [pathEps, applyBindings, List.map_cons, List.map_nil]
    exact .eps _
  · have rebuilt := matchRel_correct related (by decide)
    subst rebuilt applied
    simp only [pathDot, applyBindings, List.map_cons, List.map_nil]
    exact .dot _ _ _
  · have rebuilt := matchRel_correct related (by simp [capPrefix, Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect,
      isMatchCorrectAux, isMatchCorrectListAux])
    subst rebuilt applied
    simp only [capPrefix, applyBindings, List.map_cons, List.map_nil]
    exact .capPrefix capListed _ _

/-! ## The laws -/

/-- The calculus with paths and its core have one grammar. -/
theorem comm_terms_core : ambientCommCalc.terms ⊆ ambientCoreCalc.terms := fun _ member => member

theorem core_terms_comm : ambientCoreCalc.terms ⊆ ambientCommCalc.terms := fun _ member => member

/-- The laws of the core and the laws of paths. -/
theorem comm_laws_cases {equation : Equation} (member : equation ∈ ambientCommCalc.equations) :
    equation ∈ ambientCoreCalc.equations ∨ equation ∈ pathLaws :=
  List.mem_append.mp member

/-- Every law has no premise. -/
theorem comm_premises_nil {equation : Equation} (member : equation ∈ ambientCommCalc.equations) :
    equation.premises = [] := by
  rcases comm_laws_cases member with core | path
  · exact ambient_premises_nil core
  · rcases pathLaw_cases path with rfl | rfl | ⟨cap, fused, -, rfl⟩ <;> rfl

/-- **The laws of ambients with paths are plain**: none has premises, and a raw one instantiates its other side
plainly. -/
theorem comm_plain : PlainLaws ambientCommCalc where
  premises _ member := comm_premises_nil member
  aligned equation member raw := by
    rcases comm_laws_cases member with core | path
    · exact ambient_raw_notDeeper core raw
    · rcases pathLaw_cases path with rfl | rfl | ⟨cap, fused, -, rfl⟩ <;>
        constructor <;> simp [pathEps, pathDot, capPrefix, notDeeper, notDeeperList, captureSitesOf,
          Mettapedia.OSLF.MeTTaIL.Match.captureDepth, Mettapedia.OSLF.MeTTaIL.Match.captureDepthList]

theorem premises_transfer {base : BasePremiseEvaluator} {first second : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premises : List Premise} (none : premises = [])
    (holds : PremisesAt base first fuel initial premises final) : PremisesAt base second fuel initial premises final := by
  subst none
  cases holds
  exact .nil _

/-- **Every instance of a law with paths has a shape**, one way or the other. -/
theorem comm_instance_shape {base : BasePremiseEvaluator} {fuel : Nat} {source target : Pattern}
    (equationInstance : EquationInstanceAt base ambientCommCalc fuel source target) :
    CommShape source target ∨ CommShape target source := by
  cases equationInstance with
  | forward member raw matched premises applied =>
      rcases comm_laws_cases member with core | path
      · rcases ambient_instance_shape (.forward core raw matched
          (premises_transfer (ambient_premises_nil core) premises) applied) with shape | shape
        · exact .inl (.core shape)
        · exact .inr (.core shape)
      · rw [final_of_premises_nil (comm_premises_nil member) premises] at applied
        exact .inl (.path (path_forward path matched applied))
  | reverse member raw matched premises applied =>
      rcases comm_laws_cases member with core | path
      · rcases ambient_instance_shape (.reverse core raw matched
          (premises_transfer (ambient_premises_nil core) premises) applied) with shape | shape
        · exact .inl (.core shape)
        · exact .inr (.core shape)
      · rw [final_of_premises_nil (comm_premises_nil member) premises] at applied
        exact .inr (.path (path_reverse path matched applied))
  | declared member notRaw declared =>
      rcases comm_laws_cases member with core | path
      · obtain ⟨spec, captured, final, oriented, admitted, sourceScoped, matched, premisesHold, reduced,
          targetScoped⟩ := declared
        rcases ambient_instance_shape (.declared core notRaw ⟨spec, captured, final, oriented, admitted, sourceScoped,
          matched, premises_transfer (ambient_premises_nil core) premisesHold, reduced, targetScoped⟩) with
          shape | shape
        · exact .inl (.core shape)
        · exact .inr (.core shape)
      · rcases pathLaw_cases path with rfl | rfl | ⟨cap, fused, -, rfl⟩ <;>
          exact absurd (readsRaw_of_none rfl) (by rw [notRaw]; decide)

/-- **Every generator of the static theory with paths has a shape**, one way or the other. -/
theorem comm_generator_shape {base : BasePremiseEvaluator} {source target : Pattern}
    (generator : EquationGenerator base ambientCommCalc source target) :
    CommShape source target ∨ CommShape target source := by
  rcases generator with ⟨_, equationInstance⟩ | derived
  · exact comm_instance_shape equationInstance
  · exact .inl (.core (.law (ambient_derived_shape
      (derived_mono comm_terms_core derived))))

/-! ## Shapes through object terms -/

/-- **A shape's source is no variable.** -/
theorem CommShape.notVariable {source target : Pattern} (shape : CommShape source target) :
    (∀ index, source ≠ .bvar index) ∧ ∀ name, source ≠ .fvar name := by
  cases shape with
  | core shape => exact shape.notVariable
  | path shape => cases shape <;> exact ⟨by simp, by simp⟩

/-- **A shape's source is no abstraction.** -/
theorem CommShape.notLambda {source target : Pattern} (shape : CommShape source target) :
    ∀ binder body, source ≠ .lambda binder body := by
  cases shape with
  | core shape => exact shape.notLambda.1
  | path shape => cases shape <;> simp

/-- **A shape's source is no capability.** -/
theorem CommShape.notCap {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : CommShape source target) : ¬ HasType ambientCoreCalc free bound source capType := by
  cases shape with
  | core shape => exact shape_not_cap shape
  | path shape =>
      intro typed
      cases shape <;> rcases cap_apply_inv typed with ⟨listed, -⟩ | ⟨labelIs, -⟩ | ⟨labelIs, -⟩ <;> simp_all

/-- **A shape keeps pending substitutions.** -/
theorem CommShape.sameSubst {source target : Pattern} (shape : CommShape source target) :
    substFree source = substFree target := by
  cases shape with
  | core shape => exact shape.sameSubst
  | path shape => cases shape <;> simp [substFree, substFreeList, Bool.and_assoc]

/-- **A shape keeps its shape with its tails closed.** -/
theorem CommShape.closeTailed {source target : Pattern} (shape : CommShape source target) :
    CommShape (closeTails source) (closeTails target) := by
  cases shape with
  | core shape => exact .core shape.closeTailed
  | path shape =>
      induction shape with
      | eps process => simpa [closeTails, closeTailsList] using CommShape.path (.eps (closeTails process))
      | dot first rest process =>
          simpa [closeTails, closeTailsList] using
            CommShape.path (.dot (closeTails first) (closeTails rest) (closeTails process))
      | capPrefix listed name process =>
          simpa [closeTails, closeTailsList] using
            CommShape.path (.capPrefix listed (closeTails name) (closeTails process))

/-- **A shape between typed object terms at a hole is a chain through object terms.** -/
theorem CommShape.objectChain {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {type : TypeExpr} (hole : HoleType ambientCommCalc ambientRepBlock.toBlock type) {source target : Pattern}
    (shape : CommShape source target) (sourceTyped : HasType ambientCommCalc free bound source type)
    (targetTyped : HasType ambientCommCalc free bound target type) (sourceObject : isObjectPattern source = true)
    (targetObject : isObjectPattern target = true) :
    ObjectChain ambientCommCalc free bound type source target := by
  cases shape with
  | core shape =>
      exact objectChain_mono core_terms_comm (fun _ member => List.mem_append_left _ member)
        (fun _ member => ambient_premises_nil member)
        (Mettapedia.Languages.ProcessCalculi.Ambient.Full.AmbShape.objectChain context hole shape
          (sourceTyped.of_terms_subset comm_terms_core) (targetTyped.of_terms_subset comm_terms_core)
          sourceObject targetObject)
  | path shape => exact ObjectChain.ofInstance shape.instance sourceTyped targetTyped sourceObject targetObject

/-- **The shapes of the laws with paths read through object terms.** -/
theorem commShapes : ObjectShapes ambientCommCalc ambientRepBlock CommShape where
  generator generator := comm_generator_shape generator
  sameSubst shape := shape.sameSubst
  notLambda shape := .inl shape.notLambda
  closeTailed shape := shape.closeTailed
  chain context hole shape := shape.objectChain context hole

/-- **A chain of laws with paths between object processes passes through object processes only.** -/
theorem comm_objectChain {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} (equivalent : ProcEquiv ambientCommCalc ambientBlock free bound first second)
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true) :
    ObjectChain ambientCommCalc free bound procType first second :=
  commShapes.objectChain_of_objects context equivalent firstObject secondObject

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
