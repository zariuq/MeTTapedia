import Mettapedia.Logic.HOL.OrderedMixedPositionCoverage

/-!
# Reusable transfer from a canonical position plan to original activity

The source guard and retained count/label equations establish one universally
quantified transfer theorem. Arithmetic region proofs can then be supplied
independently without duplicating the source constructor encoding in them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    (constructors : ConstructorPrograms Const Γ)
    (zero : ClosedTerm Const constructors.number) (successor : ClosedTerm Const (constructors.number ⇒ constructors.number))
    (plans : (occurrence : Fin constructors.fields.length) →
      FieldPlan Const Γ (constructors.fields.get occurrence) constructors.number constructors.index)
    {Δ : List (Formula Const Γ)}

def canonicalTransfer (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index) :
    Formula Const Γ :=
  .all (.imp (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
    (Subst.ofRename Rename.weaken) (.var .vz) (weaken target))
    (.app (weaken (sourceActive constructors zero successor plans occurrence arguments)) (.var .vz)))

def canonicalTransferAt (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (slot : Term Const Γ constructors.number)
    (transfer : ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments
      length firstIndex vectorIndex lastIndex target)) :
    ProofSyntax Const Δ (.imp (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id slot target) (.app (sourceActive constructors zero successor plans occurrence arguments) slot)) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE slot transfer)
  simp only [instantiate,HOL.subst,compileAt_subst,Subst.single,
    PredicateFixedPoint.subst_single_weaken]
  rfl

theorem canonicalTransferAt_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (slot : Term Const Γ constructors.number)
    (transfer : ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments
      length firstIndex vectorIndex lastIndex target)) (free : transfer.FunctionExtensionalityFree) :
    (canonicalTransferAt constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target slot transfer).FunctionExtensionalityFree := by
  unfold canonicalTransferAt
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def canonicalInterior (length : Term Const Γ constructors.number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index) : Formula Const Γ :=
  .all (.imp (.app (.app (weakenCtx _ (SuccessorOrder.less successor)) (.var .vz)) (weaken length))
    (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      (Subst.ofRename Rename.weaken) (.app (weakenCtx _ successor) (.var .vz)) (weaken target)))

def transferInterior (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (transfer : ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments
      length firstIndex vectorIndex lastIndex target))
    (region : ProofSyntax Const Δ (canonicalInterior constructors zero successor length firstIndex vectorIndex lastIndex target)) :
    ProofSyntax Const Δ (SuccessorOrder.interiorCoverage successor
      (sourceActive constructors zero successor plans occurrence arguments) length) := by
  refine .allI (.impI ?_)
  let bound : Formula Const (constructors.number :: Γ) :=
    .app (.app (weakenCtx _ (SuccessorOrder.less successor)) (.var .vz)) (weaken length)
  let raisedTransfer := (transfer.rename (Rename.weaken (σ := constructors.number))).prepend bound
  let raisedRegion := (region.rename (Rename.weaken (σ := constructors.number))).prepend bound
  let step : Term Const (constructors.number :: Γ) constructors.number := .app (weakenCtx _ successor) (.var .vz)
  have cancel {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (Subst.single step) (rename (Rename.lift (Rename.weaken (σ := constructors.number)))
        (weaken (σ := constructors.number) term)) = weaken term := by
    change HOL.subst (Subst.single step) (rename (Rename.lift Rename.weaken) (rename Rename.weaken term)) = _
    rw [rename_lift_weaken]
    exact instantiate_weaken step (weaken term)
  have currentTransfer : ProofSyntax Const (bound :: weakenHyps Δ)
      (.imp (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
        (Subst.ofRename Rename.weaken) step (weaken target))
        (.app (weaken (sourceActive constructors zero successor plans occurrence arguments)) step)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE step raisedTransfer)
    simp only [rename,instantiate,HOL.subst,compileAt_rename,compileAt_subst,
      cancel,Rename.lift,Subst.single,Subst.ofRename,Rename.weaken]
    rfl
  have currentRegion := ContextualTrinity.instantiateFresh raisedRegion
  exact .impE currentTransfer (.impE currentRegion (.hyp 0))

theorem transferInterior_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (transfer : ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments
      length firstIndex vectorIndex lastIndex target))
    (region : ProofSyntax Const Δ (canonicalInterior constructors zero successor length firstIndex vectorIndex lastIndex target))
    (transferFree : transfer.FunctionExtensionalityFree) (regionFree : region.FunctionExtensionalityFree) :
    (transferInterior constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target
      transfer region).FunctionExtensionalityFree := by
  unfold transferInterior
  simp only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices,
    ContextualTrinity.instantiateFresh_free,ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename,
    transferFree,regionFree,and_self]

def proveCanonicalTransfer (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments)) :
    ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments length
      firstIndex vectorIndex lastIndex target) := by
  refine .allI (.impI ?_)
  let images : Subst Const Γ (constructors.number :: Γ) := Subst.ofRename Rename.weaken
  let inventory := constructors.subst images
  let localPlans := fun occurrence => substitute images (plans occurrence)
  let fields := substituteArguments images _ arguments
  let premise := compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
    images (.var .vz) (weaken target)
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
    apply ProofSyntax.castIndices (congrArg (List.cons premise) contexts) ?_ ((allowed.subst images).prepend premise)
    exact applyArguments_subst images _ (constructors.allowed occurrence) arguments
  have related : ProofSyntax Const assumptions
      (compileAt zero successor (mixedPlan zero successor (HOL.subst images length) (HOL.subst images firstIndex)
        (HOL.subst images vectorIndex) (HOL.subst images lastIndex)) Subst.id (.var .vz) (HOL.subst images target)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := assumptions) 0)
    change premise = _
    rw [← mixedPlan_substitute zero successor images]
    simp only [compileAt_substitute,HOL.subst_id]
    dsimp only [premise,images]
    rw [subst_ofRename]
    rfl
  apply ProofSyntax.castIndices rfl ?_
    (activeFromPlanEquations inventory zero successor localPlans occurrence fields (HOL.subst images length)
      (HOL.subst images firstIndex) (HOL.subst images vectorIndex) (HOL.subst images lastIndex)
      (mappedEquations.prepend premise) currentAllowed (.var .vz) (HOL.subst images target) related)
  apply congrArg (fun predicate => Term.app predicate (.var .vz))
  exact (sourceActive_subst constructors zero successor plans images occurrence arguments).symm.trans
    (subst_ofRename Rename.weaken _)

theorem proveCanonicalTransfer_free (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (equationsFree : equations.Free) (allowedFree : allowed.FunctionExtensionalityFree) :
    (proveCanonicalTransfer constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target
      equations allowed).FunctionExtensionalityFree := by
  unfold proveCanonicalTransfer
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply activeFromPlanEquations_free
  · apply PlanEquations.prepend_free
    apply PlanEquations.cast_free
    exact equations.subst_free _ equationsFree
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_subst] using allowedFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

/-- Retain the proof and its fragment witness before specializing a large
constructor encoding. The computational proof is unchanged. -/
def certifiedCanonicalTransfer (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (equations : PlanEquations Δ (fieldTerms _ (plans occurrence) Subst.id arguments)
      (mixedPlan zero successor length firstIndex vectorIndex lastIndex))
    (allowed : ProofSyntax Const Δ (applyArguments _ (constructors.allowed occurrence) arguments))
    (equationsFree : equations.Free) (allowedFree : allowed.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments
      length firstIndex vectorIndex lastIndex target) // proof.FunctionExtensionalityFree } :=
  ⟨proveCanonicalTransfer constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target
    equations allowed, proveCanonicalTransfer_free constructors zero successor plans occurrence arguments length
    firstIndex vectorIndex lastIndex target equations allowed equationsFree allowedFree⟩

def certifiedCanonicalTransferAt (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (slot : Term Const Γ constructors.number)
    (transfer : ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments
      length firstIndex vectorIndex lastIndex target)) (free : transfer.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (.imp (compileAt zero successor (mixedPlan zero successor length firstIndex vectorIndex lastIndex)
      Subst.id slot target) (.app (sourceActive constructors zero successor plans occurrence arguments) slot)) //
      proof.FunctionExtensionalityFree } :=
  ⟨canonicalTransferAt constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target slot transfer,
    canonicalTransferAt_free constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target slot transfer free⟩

def certifiedTransferInterior (occurrence : Fin constructors.fields.length)
    (arguments : Arguments Const Γ (constructors.fields.get occurrence))
    (length : Term Const Γ constructors.number) (firstIndex vectorIndex lastIndex target : Term Const Γ constructors.index)
    (transfer : ProofSyntax Const Δ (canonicalTransfer constructors zero successor plans occurrence arguments
      length firstIndex vectorIndex lastIndex target))
    (region : ProofSyntax Const Δ (canonicalInterior constructors zero successor length firstIndex vectorIndex lastIndex target))
    (transferFree : transfer.FunctionExtensionalityFree) (regionFree : region.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (SuccessorOrder.interiorCoverage successor
      (sourceActive constructors zero successor plans occurrence arguments) length) // proof.FunctionExtensionalityFree } :=
  ⟨transferInterior constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target transfer region,
    transferInterior_free constructors zero successor plans occurrence arguments length firstIndex vectorIndex lastIndex target
      transfer region transferFree regionFree⟩

#print axioms proveCanonicalTransfer_free
#print axioms certifiedTransferInterior
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
