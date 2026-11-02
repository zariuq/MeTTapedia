import Mettapedia.Logic.HOL.ConstructorPositionReadback
import Mettapedia.Logic.HOL.ConstructorActiveProgramProofs

/-!
# Original scoped position witnesses from encoded activity

Activity at an encoded constructor payload recovers its original field guard
and an existential child-index relation at that same slot. The converse uses
the same existential, without choosing a global index or assuming uniqueness.
Both directions retain proof programs and their function-extensionality-free
fragment witnesses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {constructors : ConstructorPrograms Const Γ} (positions : PositionPrograms constructors)
    {assumptions : List (Formula Const Γ)}

def originalActivityWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) : Formula Const Γ :=
  .and (applyArguments _ (constructors.allowed occurrence) arguments)
    (.ex (applyArguments _ (.app (weaken (.app (positions.graph occurrence) slot)) (.var .vz))
      (weakenArguments constructors.index _ arguments)))

def activityConditionReadback (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot)) :
    ProofSyntax Const assumptions (applyArguments _ (positions.activeCondition slot occurrence) arguments) :=
  ConstructorDataPredicates.readOnEncoded constructors.fields (positions.activeCondition slot) occurrence arguments
    (.impE (.eqPropEL (positions.activeProgram_beta _ slot)) present)

theorem activityConditionReadback_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot))
    (free : present.FunctionExtensionalityFree) :
    (positions.activityConditionReadback occurrence arguments slot present).FunctionExtensionalityFree :=
  ConstructorDataPredicates.readOnEncoded_free _ _ _ _ _ ⟨positions.activeProgram_beta_free _ _,free⟩

def certifiedActivityConditionReadback (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot))
    (free : present.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const assumptions (applyArguments _ (positions.activeCondition slot occurrence) arguments) //
      proof.FunctionExtensionalityFree } :=
  ⟨positions.activityConditionReadback occurrence arguments slot present,
    positions.activityConditionReadback_free occurrence arguments slot present free⟩

def activityConditionIntroduce (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence)) (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions (applyArguments _ (positions.activeCondition slot occurrence) arguments)) :
    ProofSyntax Const assumptions (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot) :=
  .impE (.eqPropER (positions.activeProgram_beta _ slot))
    (ConstructorDataPredicates.introduce constructors.fields (positions.activeCondition slot) occurrence arguments present)

theorem activityConditionIntroduce_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence)) (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions (applyArguments _ (positions.activeCondition slot occurrence) arguments))
    (free : present.FunctionExtensionalityFree) :
    (positions.activityConditionIntroduce occurrence arguments slot present).FunctionExtensionalityFree :=
  ⟨positions.activeProgram_beta_free _ _,ConstructorDataPredicates.introduce_free _ _ _ _ _ free⟩

def certifiedActivityConditionIntroduce (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence)) (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions (applyArguments _ (positions.activeCondition slot occurrence) arguments))
    (free : present.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const assumptions (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot) //
      proof.FunctionExtensionalityFree } :=
  ⟨positions.activityConditionIntroduce occurrence arguments slot present,
    positions.activityConditionIntroduce_free occurrence arguments slot present free⟩

def activityGuardReadback (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions
      (positions.activeGuard (encode constructors.fields occurrence arguments) slot)) :
    ProofSyntax Const assumptions (positions.originalActivityWitness occurrence arguments slot) := by
  let fields := ProofSyntax.impE (ProofSyntax.eqPropEL
    (conjoin_beta _ (constructors.allowed occurrence) (existsValue _ (.app (positions.graph occurrence) slot)) arguments))
    (ConstructorDataPredicates.readOnEncoded constructors.fields (positions.activeCondition slot) occurrence arguments present)
  exact .andI (.andEL fields)
    (.impE (.eqPropEL (existsValue_beta _ (.app (positions.graph occurrence) slot) arguments)) (.andER fields))

theorem activityGuardReadback_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions
      (positions.activeGuard (encode constructors.fields occurrence arguments) slot))
    (free : present.FunctionExtensionalityFree) :
    (positions.activityGuardReadback occurrence arguments slot present).FunctionExtensionalityFree := by
  unfold activityGuardReadback
  have fieldsFree := And.intro (conjoin_beta_free (assumptions := assumptions) _ (constructors.allowed occurrence)
    (existsValue _ (.app (positions.graph occurrence) slot)) arguments)
    (ConstructorDataPredicates.readOnEncoded_free _ _ _ _ present free)
  exact ⟨fieldsFree,⟨existsValue_beta_free _ _ _,fieldsFree⟩⟩

def activityGuardFromWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (witness : ProofSyntax Const assumptions (positions.originalActivityWitness occurrence arguments slot)) :
    ProofSyntax Const assumptions (positions.activeGuard (encode constructors.fields occurrence arguments) slot) :=
  ConstructorDataPredicates.introduce constructors.fields (positions.activeCondition slot) occurrence arguments
    (conjoin_intro _ arguments (.andEL witness)
      (.impE (.eqPropER (existsValue_beta _ (.app (positions.graph occurrence) slot) arguments)) (.andER witness)))

theorem activityGuardFromWitness_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (witness : ProofSyntax Const assumptions (positions.originalActivityWitness occurrence arguments slot))
    (free : witness.FunctionExtensionalityFree) :
    (positions.activityGuardFromWitness occurrence arguments slot witness).FunctionExtensionalityFree :=
  ConstructorDataPredicates.introduce_free _ _ _ _ _
    (conjoin_intro_free _ _ _ _ free ⟨existsValue_beta_free _ _ _,free⟩)

def activityProgramReadback (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot)) :
    ProofSyntax Const assumptions (positions.originalActivityWitness occurrence arguments slot) :=
  positions.activityGuardReadback occurrence arguments slot
    (.impE (.eqPropEL (positions.activeProgram_beta _ slot)) present)

theorem activityProgramReadback_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot))
    (free : present.FunctionExtensionalityFree) :
    (positions.activityProgramReadback occurrence arguments slot present).FunctionExtensionalityFree :=
  positions.activityGuardReadback_free _ _ _ _ ⟨positions.activeProgram_beta_free _ _,free⟩

def activityProgramFromWitness (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (witness : ProofSyntax Const assumptions (positions.originalActivityWitness occurrence arguments slot)) :
    ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot) :=
  .impE (.eqPropER (positions.activeProgram_beta _ slot))
    (positions.activityGuardFromWitness occurrence arguments slot witness)

theorem activityProgramFromWitness_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number)
    (witness : ProofSyntax Const assumptions (positions.originalActivityWitness occurrence arguments slot))
    (free : witness.FunctionExtensionalityFree) :
    (positions.activityProgramFromWitness occurrence arguments slot witness).FunctionExtensionalityFree :=
  ⟨positions.activeProgram_beta_free _ _,positions.activityGuardFromWitness_free _ _ _ _ free⟩

theorem activityProgram_iff_original (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (slot : Term Const Γ constructors.number) :
    Nonempty (ProofSyntax Const assumptions
      (.app (.app positions.activeProgram (encode constructors.fields occurrence arguments)) slot)) ↔
    Nonempty (ProofSyntax Const assumptions (positions.originalActivityWitness occurrence arguments slot)) :=
  ⟨fun ⟨proof⟩ => ⟨positions.activityProgramReadback occurrence arguments slot proof⟩,
    fun ⟨proof⟩ => ⟨positions.activityProgramFromWitness occurrence arguments slot proof⟩⟩

#print axioms activityProgramReadback_free
#print axioms activityProgram_iff_original
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
