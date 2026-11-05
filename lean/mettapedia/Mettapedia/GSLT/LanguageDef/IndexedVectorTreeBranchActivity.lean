import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecovery
import Mettapedia.Logic.HOL.OrderedPositionActivityReadback
import Mettapedia.Logic.HOL.OrderedPositionChildIntroduction
import Mettapedia.Logic.HOL.OrderedPositionFunctionality
import Mettapedia.Logic.HOL.IndexedContainerFieldProofs
import Mettapedia.Logic.HOL.IndexedContainerIndexPrograms

/-!
# The complete parsed branch has one ordered Vector segment

The generated branch plan retains the original arity field and the separate
shape field. Its sole count computes to the arity, and its index computes to
the original unindexed result. Actual encoded-payload activity is equivalent
to the original field guard together with a bounded slot; no additional
position witness or whole-plan correctness assumption is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchActivity
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding CurriedPredicates IndexedConstructorGuards OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {N A E : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
  (tags : Nat → Term Const Γ N) {Δ : List (Formula Const Γ)}

def inventory := IndexedVectorTreeStoredFieldGuards.inventory given source numbers zero one tags
def plans : (i : Fin (inventory given source numbers zero one tags).fields.length) →
    FieldPlan Const Γ ((inventory given source numbers zero one tags).fields.get i) N .prop :=
  IndexedContainerPositionTerms.FieldGuards.plans
    (reading := IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one)
    IndexedVectorTreeStoredFieldGuards.codes Subst.id
def positions := IndexedVectorTreeStoredConstructorRecovery.positions given source numbers zero one successor tags
def occurrence : Fin (inventory given source numbers zero one tags).fields.length := ⟨1, by change 1 < 2; decide⟩
def arguments (n q : Term Const Γ N) :
    Arguments Const Γ ((inventory given source numbers zero one tags).fields.get (occurrence given source numbers zero one tags)) :=
  (n,q,PUnit.unit)
def payload (n q : Term Const Γ N) := encode (inventory given source numbers zero one tags).fields
  (occurrence given source numbers zero one tags) (arguments given source numbers zero one tags n q)
def allowed (n q : Term Const Γ N) : Formula Const Γ :=
  applyArguments _ ((inventory given source numbers zero one tags).allowed (occurrence given source numbers zero one tags))
    (arguments given source numbers zero one tags n q)
def activity (n q : Term Const Γ N) (slot : Term Const Γ N) : Formula Const Γ :=
  .app (.app (positions given source numbers zero one successor tags).activeProgram
    (payload given source numbers zero one tags n q)) slot
def rawPlan (n q : Term Const Γ N) :=
  fieldTerms _ (plans given source numbers zero one tags (occurrence given source numbers zero one tags))
    Subst.id (arguments given source numbers zero one tags n q)

theorem rawPlan_length (n q : Term Const Γ N) : (rawPlan given source numbers zero one tags n q).length = 1 := rfl

def countAt (n q : Term Const Γ N) : Term Const Γ N :=
  ((rawPlan given source numbers zero one tags n q).get ⟨0, by rw [rawPlan_length]; decide⟩).1
def labelAt (n q : Term Const Γ N) : Term Const Γ .prop :=
  ((rawPlan given source numbers zero one tags n q).get ⟨0, by rw [rawPlan_length]; decide⟩).2
def countBody : Term Const (N :: N :: Γ) N := .app (.lam (.var (.vs (.vs .vz)))) (.var .vz)

def countProof (n q : Term Const Γ N) : ProofSyntax Const Δ (.eq (countAt given source numbers zero one tags n q) n) := by
  have first : ProofSyntax Const Δ (.eq (countAt given source numbers zero one tags n q)
      (.app (.lam (weaken n)) q)) := by
    apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2 countBody n q)
    apply congrArg₂ Term.eq
    · rfl
    · simp only [countBody,instantiate,HOL.subst,Subst.lift,Subst.single]
      apply congrArg (fun body : Term Const (N :: Γ) N => Term.app (.lam body) q)
      simp only [HOL.subst_rename,Subst.lift,Subst.single,HOL.rename,Rename.weaken]
      exact subst_ofRename Rename.weaken n
  have second : ProofSyntax Const Δ (.eq (.app (.lam (weaken n)) q) n) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta q (weaken n))
    simp only [instantiate_weaken]
  exact .eqTrans first second

theorem countProof_free (n q : Term Const Γ N) :
    (countProof given source numbers zero one tags (Δ := Δ) n q).FunctionExtensionalityFree := by
  unfold countProof
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact CurriedGuardProgramProofs.beta2_free _ _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

def labelProof (n q : Term Const Γ N) :
    ProofSyntax Const Δ (.eq (labelAt given source numbers zero one tags n q) .top) :=
  IndexedContainerPositionTerms.Reading.ignoreFields_beta [N,N] .top (n,q,PUnit.unit)

theorem labelProof_free (n q : Term Const Γ N) :
    (labelProof given source numbers zero one tags (Δ := Δ) n q).FunctionExtensionalityFree :=
  IndexedContainerPositionTerms.Reading.ignoreFields_beta_free _ _ _

def planEquations (n q : Term Const Γ N) :
    PlanEquations Δ (rawPlan given source numbers zero one tags n q) [(n,.top)] :=
  .cons (countProof given source numbers zero one tags n q) (labelProof given source numbers zero one tags n q) .nil

theorem planEquations_free (n q : Term Const Γ N) :
    (planEquations given source numbers zero one tags (Δ := Δ) n q).Free :=
  ⟨countProof_free _ _ _ _ _ _ _ _,labelProof_free _ _ _ _ _ _ _ _,True.intro⟩

private def singletonBound {index : Ty Base} (n slot : Term Const Γ N) (label requested : Term Const Γ index)
    (present : ProofSyntax Const Δ (compileAt zero successor [(n,label)] Subst.id slot requested)) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n) := by
  let first := Term.and (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n) (.eq requested label)
  let later := Term.ex (.and (.app (.app (.app (weakenCtx _ (SuccessorOrder.sum zero successor)) (weaken n))
    (.var .vz)) (weaken slot)) .bot)
  have normalized : ProofSyntax Const Δ (.or first later) :=
    .castIndices rfl (by simp only [first,later,compileAt,subst_id]) present
  exact .orE normalized (.andEL (.hyp 0)) (.exE (.hyp 0) (.botE (.andER (.hyp 0))))

private theorem singletonBound_free {index : Ty Base} (n slot : Term Const Γ N) (label requested : Term Const Γ index)
    (present : ProofSyntax Const Δ (compileAt zero successor [(n,label)] Subst.id slot requested))
    (free : present.FunctionExtensionalityFree) :
    (singletonBound zero successor n slot label requested present).FunctionExtensionalityFree := by
  unfold singletonBound
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free,True.intro,True.intro,True.intro⟩

private def singletonActiveBound {index : Ty Base} (n slot : Term Const Γ N) (label : Term Const Γ index)
    (present : ProofSyntax Const Δ (activeAt zero successor [(n,label)] slot)) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n) := by
  apply ProofSyntax.exE present
  let body := compileAt zero successor [(n,label)] (Subst.ofRename Rename.weaken) (weaken slot) (.var .vz)
  have related : ProofSyntax Const (body :: weakenHyps Δ)
      (compileAt zero successor [(weaken n,weaken label)] Subst.id (weaken slot) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := body :: weakenHyps Δ) 0)
    change body = compileAt zero successor [(weaken n,weaken label)] Subst.id (weaken slot) (.var .vz)
    simpa only [body,substitute,List.map_cons,List.map_nil,subst_id,subst_ofRename,weaken] using
      (compileAt_substitute zero successor [(n,label)] (Subst.ofRename Rename.weaken) Subst.id
        (weaken slot) (.var .vz)).symm
  apply ProofSyntax.castIndices rfl ?_ (singletonBound zero successor (weaken n) (weaken slot) (weaken label) (.var .vz) related)
  simp only [weaken,HOL.rename,rename_weakenCtx]

private theorem singletonActiveBound_free {index : Ty Base} (n slot : Term Const Γ N) (label : Term Const Γ index)
    (present : ProofSyntax Const Δ (activeAt zero successor [(n,label)] slot))
    (free : present.FunctionExtensionalityFree) :
    (singletonActiveBound zero successor n slot label present).FunctionExtensionalityFree := by
  unfold singletonActiveBound
  refine ⟨free,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply singletonBound_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

private def singletonRelated {index : Ty Base} (n slot : Term Const Γ N) (label : Term Const Γ index)
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n)) :
    ProofSyntax Const Δ (compileAt zero successor [(n,label)] Subst.id slot label) :=
  compileAt_here zero successor (n,label) [] Subst.id slot label
    (.castIndices rfl (by simp only [subst_id]) bounded)
    (.castIndices rfl (by simp only [subst_id]) (.eqRefl label))

private theorem singletonRelated_free {index : Ty Base} (n slot : Term Const Γ N) (label : Term Const Γ index)
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n))
    (free : bounded.FunctionExtensionalityFree) :
    (singletonRelated zero successor n slot label bounded).FunctionExtensionalityFree := by
  apply compileAt_here_free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def activityReadback (n q slot : Term Const Γ N)
    (present : ProofSyntax Const Δ (activity given source numbers zero one successor tags n q slot)) :
    ProofSyntax Const Δ (.and (allowed given source numbers zero one tags n q)
      (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n)) :=
  let canonical := PositionPrograms.activityToCanonical (inventory given source numbers zero one tags) zero successor
    (plans given source numbers zero one tags) (occurrence given source numbers zero one tags)
    (arguments given source numbers zero one tags n q) [(n,.top)]
    (planEquations given source numbers zero one tags n q) slot present
  .andI (.andEL canonical) (singletonActiveBound zero successor n slot .top (.andER canonical))

theorem activityReadback_free (n q slot : Term Const Γ N)
    (present : ProofSyntax Const Δ (activity given source numbers zero one successor tags n q slot))
    (free : present.FunctionExtensionalityFree) :
    (activityReadback given source numbers zero one successor tags n q slot present).FunctionExtensionalityFree := by
  have canonicalFree := PositionPrograms.activityToCanonical_free (inventory given source numbers zero one tags) zero successor
    (plans given source numbers zero one tags) (occurrence given source numbers zero one tags)
    (arguments given source numbers zero one tags n q) [(n,.top)]
    (planEquations given source numbers zero one tags n q) slot present
    (planEquations_free _ _ _ _ _ _ _ _) free
  exact ⟨canonicalFree,singletonActiveBound_free zero successor n slot .top _ canonicalFree⟩

def childGuardFromBound (n q slot : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (allowed given source numbers zero one tags n q))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n)) :
    ProofSyntax Const Δ ((positions given source numbers zero one successor tags).childGuard
      (payload given source numbers zero one tags n q) slot .top) :=
  PositionPrograms.childFromCanonical (inventory given source numbers zero one tags) zero successor
    (plans given source numbers zero one tags) (occurrence given source numbers zero one tags)
    (arguments given source numbers zero one tags n q) [(n,.top)]
    (planEquations given source numbers zero one tags n q) slot .top admitted
    (singletonRelated zero successor n slot .top bounded)

theorem childGuardFromBound_free (n q slot : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (allowed given source numbers zero one tags n q))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n))
    (admittedFree : admitted.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (childGuardFromBound given source numbers zero one successor tags n q slot admitted bounded).FunctionExtensionalityFree := by
  apply PositionPrograms.childFromCanonical_free
  · exact planEquations_free _ _ _ _ _ _ _ _
  · exact admittedFree
  · exact singletonRelated_free zero successor n slot .top bounded boundedFree

def activityFromBound (n q slot : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (allowed given source numbers zero one tags n q))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n)) :
    ProofSyntax Const Δ (activity given source numbers zero one successor tags n q slot) :=
  PositionPrograms.activityFromCanonical (inventory given source numbers zero one tags) zero successor
    (plans given source numbers zero one tags) (occurrence given source numbers zero one tags)
    (arguments given source numbers zero one tags n q) [(n,.top)]
    (planEquations given source numbers zero one tags n q) slot
    (.andI admitted (activeAt_intro zero successor [(n,.top)] slot .top
      (singletonRelated zero successor n slot .top bounded)))

theorem activityFromBound_free (n q slot : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (allowed given source numbers zero one tags n q))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n))
    (admittedFree : admitted.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (activityFromBound given source numbers zero one successor tags n q slot admitted bounded).FunctionExtensionalityFree :=
  PositionPrograms.activityFromCanonical_free _ _ _ _ _ _ _ _ _ _
    (planEquations_free _ _ _ _ _ _ _ _)
    ⟨admittedFree,activeAt_intro_free _ _ _ _ _ _ (singletonRelated_free zero successor n slot .top bounded boundedFree)⟩

def inactiveBound (n q slot : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (allowed given source numbers zero one tags n q))
    (inactive : ProofSyntax Const Δ (.not (activity given source numbers zero one successor tags n q slot))) :
    ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less successor)) slot) n)) :=
  .notI (.notE (inactive.prepend _) (activityFromBound given source numbers zero one successor tags n q slot
    (admitted.prepend _) (.hyp 0)))

theorem inactiveBound_free (n q slot : Term Const Γ N)
    (admitted : ProofSyntax Const Δ (allowed given source numbers zero one tags n q))
    (inactive : ProofSyntax Const Δ (.not (activity given source numbers zero one successor tags n q slot)))
    (admittedFree : admitted.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (inactiveBound given source numbers zero one successor tags n q slot admitted inactive).FunctionExtensionalityFree :=
  ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr inactiveFree,
    activityFromBound_free _ _ _ _ _ _ _ _ _ _ _ _
      ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr admittedFree) True.intro⟩

#print axioms planEquations
#print axioms activityReadback_free
#print axioms childGuardFromBound_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchActivity
