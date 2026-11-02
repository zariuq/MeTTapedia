import Mettapedia.Logic.HOL.ConstructorShapeDataGuard
import Mettapedia.Logic.HOL.ConstructorDataPredicateProgramsControls

/-!
# Complete shape elimination with a proper row-condition implication

Two constructor occurrences share Boolean field types but retain distinct
tags. The first source row requires its first field and the negation of its
second field; the target retains the first requirement. The second row is
forbidden. The retained bridge acts on the original beta-wrapped payload.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorShapeDataGuardControls

open FiniteConstructorEncoding FiniteConstructorEncoding.Controls
open CurriedPredicates IndexedConstructorGuards

variable {Γ Ξ : Ctx Empty}

abbrev first := ConstructorDataPredicates.ProgramControls.first
abbrev second := ConstructorDataPredicates.ProgramControls.second
abbrev originalPayload := ConstructorDataPredicates.ProgramControls.payload

def targetConditions : ConstructorDataPredicates.Conditions Constants Γ signature
  | ⟨0, _⟩ => .lam (.lam (.var (.vs .vz)))
  | ⟨1, _⟩ => .lam (.lam .bot)

def notSecond : Term Constants Γ (handlerType [.prop, .prop]) :=
  .lam (.lam (.not (.var .vz)))

def sourceConditions : ConstructorDataPredicates.Conditions Constants Γ signature
  | ⟨0, _⟩ => conjoin [.prop, .prop] (targetConditions first) notSecond
  | ⟨1, _⟩ => .lam (.lam .bot)

def inventory : ConstructorPrograms Constants Γ where
  fields := signature
  number := .prop
  index := .prop
  numeral := fun number => if number = 0 then .top else .bot
  allowed := sourceConditions
  result
    | ⟨0, _⟩ => .lam (.lam .top)
    | ⟨1, _⟩ => .lam (.lam .top)

def rowImplication (premises : List (Formula Constants Γ)) :
    ConstructorPrograms.RowImplication premises inventory targetConditions := by
  intro Ξ images assumptions _transport occurrence arguments allowed
  rcases occurrence with ⟨occurrence, bound⟩
  match occurrence with
  | 0 =>
      have current : ProofSyntax Constants assumptions
          (applyArguments [.prop, .prop]
            (conjoin [.prop, .prop] (HOL.subst images (targetConditions first))
              (HOL.subst images notSecond)) arguments) :=
        .castIndices rfl
          (congrArg (fun predicate => applyArguments [.prop, .prop] predicate arguments)
            (conjoin_subst images [.prop, .prop] (targetConditions first) notSecond)) allowed
      exact .andEL (.impE (.eqPropEL
        (conjoin_beta [.prop, .prop] (HOL.subst images (targetConditions first))
          (HOL.subst images notSecond) arguments)) current)
  | 1 => exact allowed

theorem rowImplication_free (premises : List (Formula Constants Γ)) :
    ConstructorPrograms.RowImplication.Free (rowImplication premises) := by
  intro Ξ images assumptions transport occurrence arguments allowed allowedFree
  rcases occurrence with ⟨occurrence, bound⟩
  match occurrence with
  | 0 =>
      unfold rowImplication
      exact ⟨conjoin_beta_free _ _ _ _,
        (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr allowedFree⟩
  | 1 => exact allowedFree

def notSecondEquation : ProofSyntax Constants []
    (.eq (applyArguments [.prop, .prop] notSecond fields) (.not .bot)) :=
  .eqTrans (.eqApp .bot (.beta .top (.lam (.not (.var .vz)))))
    (.beta .bot (.not (.var .vz)))

def notSecondProof : ProofSyntax Constants []
    (applyArguments [.prop, .prop] notSecond fields) :=
  .impE (.eqPropER notSecondEquation) (.notI (.hyp 0))

def sourceAllowed : ProofSyntax Constants []
    (applyArguments [.prop, .prop] (sourceConditions first) fields) :=
  conjoin_intro [.prop, .prop] fields
    ConstructorDataPredicates.ProgramControls.fieldProof notSecondProof

theorem notSecondProof_free : notSecondProof.FunctionExtensionalityFree := by
  trivial

theorem sourceAllowed_free : sourceAllowed.FunctionExtensionalityFree :=
  conjoin_intro_free _ _ _ _ ConstructorDataPredicates.ProgramControls.fieldProof_free
    notSecondProof_free

def sourceShape : ProofSyntax Constants []
    (.app (.app inventory.shapeProgram .top) originalPayload) :=
  .impE (.eqPropER (inventory.shapeProgram_beta .top originalPayload))
    (ConstructorDataPredicates.introduceAt (inventory.shapeCondition .top) originalPayload
      first fields
      (conjoin_intro [.prop, .prop] fields sourceAllowed
        (constant_intro [.prop, .prop] fields (.eqRefl .top)))
      ConstructorDataPredicates.ProgramControls.payloadEquation)

theorem sourceShape_free : sourceShape.FunctionExtensionalityFree := by
  unfold sourceShape
  refine ⟨inventory.shapeProgram_beta_free _ _, ?_⟩
  apply ConstructorDataPredicates.introduceAt_free
  · exact conjoin_intro_free _ _ _ _ sourceAllowed_free
      (constant_intro_free _ _ _ True.intro)
  · exact ConstructorDataPredicates.ProgramControls.payloadEquation_free

def transported : ProofSyntax Constants []
    (ConstructorDataPredicates.guard signature targetConditions originalPayload) :=
  ConstructorPrograms.shapeDataGuard inventory targetConditions (rowImplication [])
    .top originalPayload sourceShape

theorem transported_free : transported.FunctionExtensionalityFree :=
  ConstructorPrograms.shapeDataGuard_free inventory targetConditions (rowImplication [])
    (rowImplication_free []) .top originalPayload sourceShape sourceShape_free

theorem transported_holds :
    (model.denote (ConstructorDataPredicates.guard signature targetConditions originalPayload) values).down := by
  apply Soundness.extDerivation_sound transported.erase
    (model.functionsRespectEqv_of_fullDomains ConstructorDataPredicates.ProgramControls.full)
    (fun _ => ConstructorDataPredicates.ProgramControls.full _ _)
  intro formula member
  cases member

def shape (tag : ClosedFormula Constants)
    (payload : ClosedTerm Constants (payloadType signature)) : ClosedFormula Constants :=
  .app (.app inventory.shapeProgram tag) payload

theorem shape_on_encoded (tag : ClosedFormula Constants) (occurrence : Fin signature.length)
    (arguments : Arguments Constants [] (signature.get occurrence)) :
    (model.denote (shape tag (encode signature occurrence arguments)) values).down ↔
      inventory.dataAllowed model values ⟨occurrence, denoteArguments model _ arguments values⟩ ∧
        model.denote tag values = model.denote (inventory.numeral occurrence.val) values := by
  refine (inventory.shapeProgram_denote model ConstructorDataPredicates.ProgramControls.full values
    (model.denote tag values) (model.denote (encode signature occurrence arguments) values)).trans ?_
  constructor
  · rintro ⟨data, allowed, same⟩
    have identified := TypeTheory.FiniteConstructorEncoding.encode_injective _ _
      ((encode_denote model signature occurrence arguments values).symm.trans same)
    subst data
    exact allowed
  · intro allowed
    exact ⟨_, allowed, encode_denote model signature occurrence arguments values⟩

theorem changed_first_refused :
    ¬ (model.denote (shape .top (encode signature first changedFields)) values).down := by
  intro present
  have allowed := ((shape_on_encoded .top first changedFields).mp present).1
  exact ((conjoin_holds model [.prop, .prop] (targetConditions first) notSecond values
    (denoteArguments model _ changedFields values)).mp allowed).1

theorem forbidden_occurrence_refused :
    ¬ (model.denote (shape .bot (encode signature second fields)) values).down := by
  intro present
  exact ((shape_on_encoded .bot second fields).mp present).1

theorem wrong_tag_refused : ¬ (model.denote (shape .bot originalPayload) values).down := by
  intro present
  have wrong := ((shape_on_encoded .bot first fields).mp present).2
  exact (congrArg ULift.down wrong).mpr True.intro

theorem unused_shape_refused : ¬ (model.denote (shape .top unused) values).down := by
  intro present
  obtain ⟨data, _, same⟩ :=
    (inventory.shapeProgram_denote model ConstructorDataPredicates.ProgramControls.full values _ _).mp present
  exact unused_refused ⟨data, same.symm⟩

def bothTrue : Arguments Constants [] [.prop, .prop] := (.top, .top, PUnit.unit)

theorem target_does_not_require_second_negation :
    (model.denote (ConstructorDataPredicates.guard signature targetConditions
      (encode signature first bothTrue)) values).down := by
  apply (ConstructorDataPredicates.guard_on_encoded model
    ConstructorDataPredicates.ProgramControls.full signature targetConditions first bothTrue values).mpr
  trivial

theorem source_still_requires_second_negation :
    ¬ (model.denote (shape .top (encode signature first bothTrue)) values).down := by
  intro present
  have allowed := ((shape_on_encoded .top first bothTrue).mp present).1
  exact ((conjoin_holds model [.prop, .prop] (targetConditions first) notSecond values
    (denoteArguments model _ bothTrue values)).mp allowed).2 True.intro

#print axioms rowImplication
#print axioms rowImplication_free
#print axioms sourceShape
#print axioms sourceShape_free
#print axioms transported
#print axioms transported_free
#print axioms transported_holds
#print axioms changed_first_refused
#print axioms forbidden_occurrence_refused
#print axioms wrong_tag_refused
#print axioms unused_shape_refused
#print axioms target_does_not_require_second_negation
#print axioms source_still_requires_second_negation

end Mettapedia.Logic.HOL.ConstructorShapeDataGuardControls
