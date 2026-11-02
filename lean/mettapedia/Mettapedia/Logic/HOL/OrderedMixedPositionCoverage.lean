import Mettapedia.Logic.HOL.MixedPositionCoverage
import Mettapedia.Logic.HOL.OrderedPositionFunctionality
import Mettapedia.Logic.HOL.OrderedPositionConversion
import Mettapedia.Logic.HOL.ConstructorActiveProgramProofs
import Mettapedia.Logic.HOL.ConstructorPositionSubstitution
import Mettapedia.Logic.HOL.OrderedConstructorChildExistence

/-!
# Coverage supplied by the actual ordered-position compiler

The three segments are a leading child, a length-indexed vector segment and
a trailing child. Their index labels may differ. Source field telescopes and
allowed-field predicates remain explicit in the original constructor guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
open SuccessorOrder FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))
    {Δ : List (Formula Const Γ)}

def mixedPlan (length : Term Const Γ number) (firstIndex vectorIndex lastIndex : Term Const Γ index) :
    Plan Const Γ number index :=
  [(.app (weakenCtx Γ successor) (weakenCtx Γ zero),firstIndex),
    (length,vectorIndex),(.app (weakenCtx Γ successor) (weakenCtx Γ zero),lastIndex)]

theorem mixedPlan_substitute (images : Subst Const Γ Ξ) (length : Term Const Γ number)
    (firstIndex vectorIndex lastIndex : Term Const Γ index) :
    substitute images (mixedPlan zero successor length firstIndex vectorIndex lastIndex) =
      mixedPlan zero successor (HOL.subst images length) (HOL.subst images firstIndex)
        (HOL.subst images vectorIndex) (HOL.subst images lastIndex) := by
  simp only [mixedPlan,substitute,List.map_cons,List.map_nil,HOL.subst,subst_weakenCtx]

def mixedFirst (length : Term Const Γ number) (firstIndex vectorIndex lastIndex : Term Const Γ index) :
    ProofSyntax Const Δ (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id (weakenCtx Γ zero) firstIndex) := by
  apply compileAt_here
  · apply ProofSyntax.castIndices rfl ?_ (lessNext successor (weakenCtx Γ zero))
    simp only [subst_id]
  · apply ProofSyntax.castIndices rfl ?_ (.eqRefl firstIndex)
    simp only [subst_id]

theorem mixedFirst_free (length : Term Const Γ number) (firstIndex vectorIndex lastIndex : Term Const Γ index) :
    (mixedFirst (Δ := Δ) zero successor length firstIndex vectorIndex lastIndex).FunctionExtensionalityFree := by
  unfold mixedFirst
  apply compileAt_here_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact lessNext_free _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

def onePlus (position : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) (weakenCtx Γ zero))) position) (.app (weakenCtx Γ successor) position)) :=
  sumSuccLeft successor zero (weakenCtx Γ zero) position position (sumZeroLeft successor zero position principle)

theorem onePlus_free (position : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) : (onePlus zero successor position principle).FunctionExtensionalityFree :=
  sumSuccLeft_free _ _ _ _ _ _ (sumZeroLeft_free _ _ _ principle free)

def mixedInterior (length : Term Const Γ number) (firstIndex vectorIndex lastIndex : Term Const Γ index)
    (position : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) position) length)) :
    ProofSyntax Const Δ (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id (.app (weakenCtx Γ successor) position) vectorIndex) := by
  apply compileAt_later (offset := position)
  · apply ProofSyntax.castIndices rfl ?_ (onePlus zero successor position principle)
    simp only [subst_id]
  · apply compileAt_here
    · apply ProofSyntax.castIndices rfl ?_ bounded
      simp only [subst_id]
    · apply ProofSyntax.castIndices rfl ?_ (.eqRefl vectorIndex)
      simp only [subst_id]

theorem mixedInterior_free (length : Term Const Γ number) (firstIndex vectorIndex lastIndex : Term Const Γ index)
    (position : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) position) length))
    (principleFree : principle.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (mixedInterior zero successor length firstIndex vectorIndex lastIndex position principle bounded).FunctionExtensionalityFree := by
  unfold mixedInterior
  apply compileAt_later_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact onePlus_free zero successor position principle principleFree
  · apply compileAt_here_free
    · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr boundedFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial

def mixedLast (length : Term Const Γ number) (firstIndex vectorIndex lastIndex : Term Const Γ index)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id (.app (weakenCtx Γ successor) length) lastIndex) := by
  apply compileAt_later (offset := length)
  · apply ProofSyntax.castIndices rfl ?_ (onePlus zero successor length principle)
    simp only [subst_id]
  · apply compileAt_later (offset := weakenCtx Γ zero)
    · apply ProofSyntax.castIndices rfl ?_ (sumZero successor zero length)
      simp only [subst_id]
    · apply compileAt_here
      · apply ProofSyntax.castIndices rfl ?_ (lessNext successor (weakenCtx Γ zero))
        simp only [subst_id]
      · apply ProofSyntax.castIndices rfl ?_ (.eqRefl lastIndex)
        simp only [subst_id]

theorem mixedLast_free (length : Term Const Γ number) (firstIndex vectorIndex lastIndex : Term Const Γ index)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) :
    (mixedLast zero successor length firstIndex vectorIndex lastIndex principle).FunctionExtensionalityFree := by
  unfold mixedLast
  apply compileAt_later_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact onePlus_free zero successor length principle free
  · apply compileAt_later_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact sumZero_free _ _ _
    · apply compileAt_here_free
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact lessNext_free _ _
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial

#print axioms mixedInterior_free
#print axioms mixedLast_free
end Mettapedia.Logic.HOL.OrderedPositionPrograms

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number)
    (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {Δ : List (Formula Const Γ)}

theorem fieldTerms_map (images : Subst Const Γ Ξ) (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields constructors.number constructors.index) (arguments : Arguments Const Γ fields) :
    fieldTerms fields (substitute images plan) Subst.id (substituteArguments images fields arguments) =
      substitute images (fieldTerms fields plan Subst.id arguments) := by
  rw [fieldTerms_substitute]
  have same := fieldTerms_subst fields plan Subst.id images arguments
  simpa only [HOL.subst_id,HOL.subst,Subst.id] using same.symm

def sourceActive (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence)) : Term Const Γ (constructors.number ⇒ .prop) :=
  .app (ofSegments constructors zero successor plans).activeProgram (encode constructors.fields occurrence arguments)

theorem sourceActive_subst (images : Subst Const Γ Ξ) (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence)) :
    HOL.subst images (sourceActive constructors zero successor plans occurrence arguments) =
      sourceActive (constructors.subst images) zero successor (fun occurrence => substitute images (plans occurrence))
        occurrence (substituteArguments images _ arguments) := by
  simp only [sourceActive,HOL.subst,activeProgram_subst,ofSegments_subst,encode_subst]
  rfl

def activeFromPlanEquations (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (slot : Term Const Γ constructors.number) (target : Term Const Γ constructors.index)
    (related : ProofSyntax Const Δ (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id slot target)) :
    ProofSyntax Const Δ (.app (sourceActive constructors zero successor plans occurrence arguments) slot) :=
  (ofSegments constructors zero successor plans).activeFromOriginal occurrence arguments slot target allowed
    (.impE (.eqPropER (fieldGraph_beta zero successor _ (plans occurrence) slot target arguments))
      (.impE (.eqPropER (compileAt_planEquation zero successor equations slot target)) related))

theorem activeFromPlanEquations_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (slot : Term Const Γ constructors.number) (target : Term Const Γ constructors.index)
    (related : ProofSyntax Const Δ (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id slot target)) (equationsFree : equations.Free) (allowedFree : allowed.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    (activeFromPlanEquations constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
      equations allowed slot target related).FunctionExtensionalityFree := by
  unfold activeFromPlanEquations
  apply activeFromOriginal_free
  · exact allowedFree
  · exact ⟨fieldGraph_beta_free _ _ _ _ _ _ _,
      ⟨compileAt_planEquation_free zero successor equations slot target equationsFree,relatedFree⟩⟩

def originalMixedCoverage (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    MixedCoverage successor zero (sourceActive constructors zero successor plans occurrence arguments) length Δ where
  first := activeFromPlanEquations constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
    equations allowed (weakenCtx Γ zero) firstIndex (mixedFirst zero successor length firstIndex vectorIndex lastIndex)
  last := activeFromPlanEquations constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
    equations allowed (.app (weakenCtx Γ successor) length) lastIndex (mixedLast zero successor length firstIndex vectorIndex lastIndex principle)
  interior := by
    refine .allI (.impI ?_)
    let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
    let inventory := constructors.subst images
    let localPlans := fun occurrence => substitute images (plans occurrence)
    let fields := substituteArguments images _ arguments
    let premise : Formula Const (constructors.number :: Γ) :=
      .app (.app (weakenCtx _ (less successor)) (.var .vz)) (weaken length)
    let assumptions := premise :: weakenHyps Δ
    have contexts : Δ.map (HOL.subst images) = weakenHyps (σ := constructors.number) Δ := by
      apply List.map_congr_left
      intro formula _
      exact subst_ofRename Rename.weaken formula
    have mappedEquations : PlanEquations (weakenHyps (σ := constructors.number) Δ)
        (fieldTerms _ (localPlans occurrence) Subst.id fields)
        (mixedPlan zero successor (HOL.subst images length) (HOL.subst images firstIndex)
          (HOL.subst images vectorIndex) (HOL.subst images lastIndex)) :=
      PlanEquations.cast contexts (fieldTerms_map constructors images _ (plans occurrence) arguments).symm
        (mixedPlan_substitute zero successor images length firstIndex vectorIndex lastIndex) (equations.subst images)
    have currentAllowed : ProofSyntax Const assumptions (applyArguments _ (inventory.allowed occurrence) fields) := by
      apply ProofSyntax.castIndices ?_ ?_ ((allowed.subst images).prepend premise)
      · change premise :: Δ.map (HOL.subst images) = premise :: Δ.map weaken
        apply congrArg (List.cons premise)
        apply List.map_congr_left
        intro formula _
        exact subst_ofRename Rename.weaken formula
      · exact applyArguments_subst images _ (constructors.allowed occurrence) arguments
    have currentPrinciple := (inductionRename successor zero principle (Rename.weaken (σ := constructors.number))).prepend premise
    have bounded : ProofSyntax Const assumptions
        (.app (.app (weakenCtx _ (less successor)) (.var .vz)) (HOL.subst images length)) := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := assumptions) 0)
      change premise = _
      simp only [premise,images,subst_ofRename,weaken]
    have related := mixedInterior zero successor (HOL.subst images length) (HOL.subst images firstIndex)
      (HOL.subst images vectorIndex) (HOL.subst images lastIndex) (.var .vz) currentPrinciple bounded
    apply ProofSyntax.castIndices rfl ?_
      (activeFromPlanEquations inventory zero successor localPlans occurrence fields (HOL.subst images length)
        (HOL.subst images firstIndex) (HOL.subst images vectorIndex) (HOL.subst images lastIndex)
        (mappedEquations.prepend premise) currentAllowed (.app (weakenCtx _ successor) (.var .vz)) (HOL.subst images vectorIndex) related)
    change Term.app (sourceActive inventory zero successor localPlans occurrence fields) _ =
      Term.app (weaken (sourceActive constructors zero successor plans occurrence arguments)) _
    apply congrArg (fun predicate => Term.app predicate (.app (weakenCtx _ successor) (.var .vz)))
    exact (sourceActive_subst constructors zero successor plans images occurrence arguments).symm.trans
      (subst_ofRename Rename.weaken _)

theorem originalMixedCoverage_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (equationsFree : equations.Free) (allowedFree : allowed.FunctionExtensionalityFree) (principleFree : principle.FunctionExtensionalityFree) :
    (originalMixedCoverage constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
      equations allowed principle).Free := by
  unfold MixedCoverage.Free originalMixedCoverage
  refine ⟨?_,?_,?_⟩
  · exact activeFromPlanEquations_free constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
      equations allowed _ _ _ equationsFree allowedFree (mixedFirst_free _ _ _ _ _ _)
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply activeFromPlanEquations_free
    · apply PlanEquations.prepend_free
      apply PlanEquations.cast_free
      exact equations.subst_free _ equationsFree
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_subst] using allowedFree
    · apply mixedInterior_free
      · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using
          inductionRename_free successor zero principle (Rename.weaken (σ := constructors.number)) principleFree
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial
  · exact activeFromPlanEquations_free constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
      equations allowed _ _ _ equationsFree allowedFree
      (mixedLast_free _ _ _ _ _ _ principle principleFree)

def inactiveOriginalAddress (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (slot : Term Const Γ constructors.number)
    (inactive : ProofSyntax Const Δ (.not (.app (sourceActive constructors zero successor plans occurrence arguments) slot))) :
    ProofSyntax Const Δ (paddingAddress successor zero length slot) :=
  inactiveAddress successor zero (sourceActive constructors zero successor plans occurrence arguments) length slot
    (originalMixedCoverage constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
      equations allowed principle) principle separate inactive

theorem inactiveOriginalAddress_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (slot : Term Const Γ constructors.number)
    (inactive : ProofSyntax Const Δ (.not (.app (sourceActive constructors zero successor plans occurrence arguments) slot)))
    (equationsFree : equations.Free) (allowedFree : allowed.FunctionExtensionalityFree) (principleFree : principle.FunctionExtensionalityFree)
    (separateFree : separate.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (inactiveOriginalAddress constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
      equations allowed principle separate slot inactive).FunctionExtensionalityFree :=
  inactiveAddress_free _ _ _ _ _ _ principle separate inactive
    (originalMixedCoverage_free constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex
      equations allowed principle equationsFree allowedFree principleFree) principleFree separateFree inactiveFree

#print axioms originalMixedCoverage_free
#print axioms inactiveOriginalAddress_free
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
