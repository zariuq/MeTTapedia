import Mettapedia.Logic.HOL.ConstructorActivityReadback
import Mettapedia.Logic.HOL.OrderedPositionConversion
import Mettapedia.Logic.HOL.OrderedConstructorChildExistence

/-!
# Scoped activity witnesses for ordered position plans

An active position retains an existential index in the original field graph.
Its beta equation exposes the ordered plan under that same binder. Supplied
count/label equations transport this witness to another plan; no index is
selected globally and no source field guard is discarded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))
    {Δ : List (Formula Const Γ)}

def activeAt (plan : Plan Const Γ number index) (slot : Term Const Γ number) : Formula Const Γ :=
  .ex (compileAt zero successor plan (Subst.ofRename Rename.weaken) (weaken slot) (.var .vz))

def fieldActivity (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (arguments : Arguments Const Γ fields) (slot : Term Const Γ number) : Formula Const Γ :=
  .ex (applyArguments fields (.app (weaken (.app (fieldGraph zero successor fields plan) slot)) (.var .vz))
    (weakenArguments index fields arguments))

def activeAt_intro (plan : Plan Const Γ number index) (slot : Term Const Γ number) (target : Term Const Γ index)
    (related : ProofSyntax Const Δ (compileAt zero successor plan Subst.id slot target)) :
    ProofSyntax Const Δ (activeAt zero successor plan slot) := by
  apply ProofSyntax.exI target
  apply ProofSyntax.castIndices rfl ?_ related
  simp only [instantiate,compileAt_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]
  rfl

theorem activeAt_intro_free (plan : Plan Const Γ number index) (slot : Term Const Γ number) (target : Term Const Γ index)
    (related : ProofSyntax Const Δ (compileAt zero successor plan Subst.id slot target)) (free : related.FunctionExtensionalityFree) :
    (activeAt_intro zero successor plan slot target related).FunctionExtensionalityFree := by
  unfold activeAt_intro
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem weakenArguments_as_substitution (fields : List (Ty Base)) (arguments : Arguments Const Γ fields) :
    weakenArguments index fields arguments = substituteArguments (Subst.ofRename (Rename.weaken (σ := index))) fields arguments := by
  induction fields with
  | nil => cases arguments; rfl
  | cons type rest previous =>
      exact congrArg₂ Prod.mk (subst_ofRename Rename.weaken arguments.1).symm (previous arguments.2)

def fieldActivityEquation (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (arguments : Arguments Const Γ fields) (slot : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (fieldActivity zero successor fields plan arguments slot)
      (activeAt zero successor (fieldTerms fields plan Subst.id arguments) slot)) := by
  apply ContextualTrinity.exCongr
  let images : Subst Const Γ (index :: Γ) := Subst.ofRename Rename.weaken
  let source := fieldTerms fields plan Subst.id arguments
  let raised := substituteArguments images fields arguments
  let targetPlan := fieldTerms fields (substitute images plan) Subst.id raised
  have natural : substitute images source = targetPlan := by
    dsimp only [source,targetPlan,raised]
    rw [fieldTerms_subst,fieldTerms_substitute]
    simp only [HOL.subst,subst_id,Subst.id]
  apply ProofSyntax.castIndices rfl ?_
    (fieldGraph_beta zero successor fields (substitute images plan) (weaken slot) (.var .vz) raised)
  apply congrArg₂ Term.eq
  · rw [← fieldGraph_substitute]
    simp only [images,subst_ofRename]
    rw [weakenArguments_as_substitution]
    rfl
  · change compileAt zero successor targetPlan Subst.id (weaken slot) (.var .vz) =
      compileAt zero successor source images (weaken slot) (.var .vz)
    rw [← natural,compileAt_substitute]
    simp only [subst_id]

theorem fieldActivityEquation_free (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (arguments : Arguments Const Γ fields) (slot : Term Const Γ number) :
    (fieldActivityEquation (Δ := Δ) zero successor fields plan arguments slot).FunctionExtensionalityFree := by
  unfold fieldActivityEquation
  apply (ContextualTrinity.exCongr_free _).mpr
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact fieldGraph_beta_free _ _ _ _ _ _ _

def activeAtEquation {left right : Plan Const Γ number index} (equations : PlanEquations Δ left right)
    (slot : Term Const Γ number) : ProofSyntax Const Δ (.eq (activeAt zero successor left slot) (activeAt zero successor right slot)) := by
  apply ContextualTrinity.exCongr
  apply ProofSyntax.castIndices ?_ rfl
    (compileAt_congr zero successor equations (Subst.ofRename (Rename.weaken (σ := index))) (weaken slot) (.var .vz))
  apply List.map_congr_left
  intro formula _
  exact subst_ofRename Rename.weaken formula

theorem activeAtEquation_free {left right : Plan Const Γ number index} (equations : PlanEquations Δ left right)
    (slot : Term Const Γ number) (free : equations.Free) :
    (activeAtEquation zero successor equations slot).FunctionExtensionalityFree := by
  unfold activeAtEquation
  apply (ContextualTrinity.exCongr_free _).mpr
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact compileAt_congr_free _ _ equations free _ _ _

#print axioms fieldActivityEquation_free
#print axioms activeAtEquation_free
end Mettapedia.Logic.HOL.OrderedPositionPrograms

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number) (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {Δ : List (Formula Const Γ)}

def conditionToCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (applyArguments _
      ((ofSegments constructors zero successor plans).activeCondition slot occurrence) arguments)) :
    ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)) := by
  let fields := ProofSyntax.impE (.eqPropEL (conjoin_beta _ (constructors.allowed occurrence)
    (existsValue _ (.app (fieldGraph zero successor _ (plans occurrence)) slot)) arguments)) present
  let fieldWitness := ProofSyntax.impE (.eqPropEL (existsValue_beta _
    (.app (fieldGraph zero successor _ (plans occurrence)) slot) arguments)) (.andER fields)
  let conversion := ProofSyntax.eqTrans (fieldActivityEquation zero successor _ (plans occurrence) arguments slot)
    (activeAtEquation zero successor equations slot)
  exact .andI (.andEL fields) (.impE (.eqPropEL conversion) fieldWitness)

theorem conditionToCanonical_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (applyArguments _
      ((ofSegments constructors zero successor plans).activeCondition slot occurrence) arguments))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    (conditionToCanonical constructors zero successor plans occurrence arguments canonical equations slot present).FunctionExtensionalityFree := by
  unfold conditionToCanonical
  have fieldsFree := And.intro (conjoin_beta_free (assumptions := Δ) _ (constructors.allowed occurrence)
    (existsValue _ (.app (fieldGraph zero successor _ (plans occurrence)) slot)) arguments) presentFree
  exact ⟨fieldsFree,⟨⟨fieldActivityEquation_free _ _ _ _ _ _,activeAtEquation_free _ _ equations slot equationsFree⟩,
    ⟨existsValue_beta_free _ _ _,fieldsFree⟩⟩⟩

def certifiedConditionToCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (applyArguments _
      ((ofSegments constructors zero successor plans).activeCondition slot occurrence) arguments))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)) // proof.FunctionExtensionalityFree } :=
  ⟨conditionToCanonical constructors zero successor plans occurrence arguments canonical equations slot present,
    conditionToCanonical_free constructors zero successor plans occurrence arguments canonical equations slot present equationsFree presentFree⟩

def canonicalToCondition (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot))) :
    ProofSyntax Const Δ (applyArguments _
      ((ofSegments constructors zero successor plans).activeCondition slot occurrence) arguments) := by
  let conversion := ProofSyntax.eqTrans (fieldActivityEquation zero successor _ (plans occurrence) arguments slot)
    (activeAtEquation zero successor equations slot)
  let fieldWitness := ProofSyntax.impE (.eqPropER conversion) (.andER present)
  exact conjoin_intro _ arguments (.andEL present)
    (.impE (.eqPropER (existsValue_beta _ (.app (fieldGraph zero successor _ (plans occurrence)) slot) arguments)) fieldWitness)

theorem canonicalToCondition_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    (canonicalToCondition constructors zero successor plans occurrence arguments canonical equations slot present).FunctionExtensionalityFree := by
  unfold canonicalToCondition
  apply conjoin_intro_free
  · exact presentFree
  · exact ⟨existsValue_beta_free _ _ _,⟨⟨fieldActivityEquation_free _ _ _ _ _ _,
      activeAtEquation_free _ _ equations slot equationsFree⟩,presentFree⟩⟩

def certifiedCanonicalToCondition (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (applyArguments _
      ((ofSegments constructors zero successor plans).activeCondition slot occurrence) arguments) // proof.FunctionExtensionalityFree } :=
  ⟨canonicalToCondition constructors zero successor plans occurrence arguments canonical equations slot present,
    canonicalToCondition_free constructors zero successor plans occurrence arguments canonical equations slot present equationsFree presentFree⟩

def activityToCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ
      (.app (.app (ofSegments constructors zero successor plans).activeProgram
        (encode constructors.fields occurrence arguments)) slot)) :
    ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)) := by
  let original := (ofSegments constructors zero successor plans).activityProgramReadback occurrence arguments slot present
  let conversion := ProofSyntax.eqTrans (fieldActivityEquation zero successor _ (plans occurrence) arguments slot)
    (activeAtEquation zero successor equations slot)
  exact .andI (.andEL original) (.impE (.eqPropEL conversion) (.andER original))

theorem activityToCanonical_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ
      (.app (.app (ofSegments constructors zero successor plans).activeProgram
        (encode constructors.fields occurrence arguments)) slot))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    (activityToCanonical constructors zero successor plans occurrence arguments canonical equations slot present).FunctionExtensionalityFree := by
  unfold activityToCanonical
  have readbackFree := (ofSegments constructors zero successor plans).activityProgramReadback_free occurrence arguments slot present presentFree
  exact ⟨readbackFree,⟨⟨fieldActivityEquation_free _ _ _ _ _ _,activeAtEquation_free _ _ equations slot equationsFree⟩,readbackFree⟩⟩

def activityFromCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot))) :
    ProofSyntax Const Δ (.app (.app (ofSegments constructors zero successor plans).activeProgram
      (encode constructors.fields occurrence arguments)) slot) := by
  let conversion := ProofSyntax.eqTrans (fieldActivityEquation zero successor _ (plans occurrence) arguments slot)
    (activeAtEquation zero successor equations slot)
  exact (ofSegments constructors zero successor plans).activityProgramFromWitness occurrence arguments slot
    (.andI (.andEL present) (.impE (.eqPropER conversion) (.andER present)))

theorem activityFromCanonical_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    (activityFromCanonical constructors zero successor plans occurrence arguments canonical equations slot present).FunctionExtensionalityFree := by
  unfold activityFromCanonical
  apply activityProgramFromWitness_free
  exact ⟨presentFree,⟨⟨fieldActivityEquation_free _ _ _ _ _ _,activeAtEquation_free _ _ equations slot equationsFree⟩,presentFree⟩⟩

#print axioms activityToCanonical_free
#print axioms activityFromCanonical_free

def certifiedActivityToCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (.app (.app (ofSegments constructors zero successor plans).activeProgram
      (encode constructors.fields occurrence arguments)) slot))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)) // proof.FunctionExtensionalityFree } :=
  ⟨activityToCanonical constructors zero successor plans occurrence arguments canonical equations slot present,
    activityToCanonical_free constructors zero successor plans occurrence arguments canonical equations slot present equationsFree presentFree⟩

def certifiedActivityFromCanonical (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number)
    (present : ProofSyntax Const Δ (.and (applyArguments _ (constructors.allowed occurrence) arguments)
      (activeAt zero successor canonical slot)))
    (equationsFree : equations.Free) (presentFree : present.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (.app (.app (ofSegments constructors zero successor plans).activeProgram
      (encode constructors.fields occurrence arguments)) slot) // proof.FunctionExtensionalityFree } :=
  ⟨activityFromCanonical constructors zero successor plans occurrence arguments canonical equations slot present,
    activityFromCanonical_free constructors zero successor plans occurrence arguments canonical equations slot present equationsFree presentFree⟩

def activityCanonicalEquation (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number) :
    ProofSyntax Const Δ (.eq
      (.app (.app (ofSegments constructors zero successor plans).activeProgram
        (encode constructors.fields occurrence arguments)) slot)
      (.and (applyArguments _ (constructors.allowed occurrence) arguments) (activeAt zero successor canonical slot))) :=
  .eqPropI (.impI (activityToCanonical constructors zero successor plans occurrence arguments canonical
    (equations.prepend _) slot (.hyp 0)))
    (.impI (activityFromCanonical constructors zero successor plans occurrence arguments canonical
      (equations.prepend _) slot (.hyp 0)))

theorem activityCanonicalEquation_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number) (free : equations.Free) :
    (activityCanonicalEquation constructors zero successor plans occurrence arguments canonical equations slot).FunctionExtensionalityFree :=
  ⟨activityToCanonical_free _ _ _ _ _ _ _ _ _ _ (equations.prepend_free _ free) trivial,
    activityFromCanonical_free _ _ _ _ _ _ _ _ _ _ (equations.prepend_free _ free) trivial⟩

def certifiedActivityCanonicalEquation (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (canonical : Plan Const Γ constructors.number constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments) canonical)
    (slot : Term Const Γ constructors.number) (free : equations.Free) :
    { proof : ProofSyntax Const Δ (.eq
      (.app (.app (ofSegments constructors zero successor plans).activeProgram
        (encode constructors.fields occurrence arguments)) slot)
      (.and (applyArguments _ (constructors.allowed occurrence) arguments) (activeAt zero successor canonical slot))) //
      proof.FunctionExtensionalityFree } :=
  ⟨activityCanonicalEquation constructors zero successor plans occurrence arguments canonical equations slot,
    activityCanonicalEquation_free constructors zero successor plans occurrence arguments canonical equations slot free⟩

#print axioms certifiedActivityCanonicalEquation
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
