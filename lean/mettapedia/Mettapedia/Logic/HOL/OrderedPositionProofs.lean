import Mettapedia.Logic.HOL.OrderedPositionPrograms
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs

/-!
# Retained index consequences of ordered position programs

The query computes to its authored ordered relation. When every segment's
child-index program is proved equal to the same requested index, any answer
has that index. This consequence needs no arithmetic axioms: both lookup
branches retain their index equation, including under residual-slot binders.
Heterogeneous plans require additional position-sensitive comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms

open IndexedConstructorGuards.ConstructorPrograms (beneathTwo)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base}
    {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))

def graph_beta {assumptions : List (Formula Const Γ)}
    (plan : Plan Const Γ number index) (slot : Term Const Γ number) (target : Term Const Γ index) :
    ProofSyntax Const assumptions (.eq (.app (.app (graph zero successor plan) slot) target)
      (compileAt zero successor plan Subst.id slot target)) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2
    (compileAt zero successor plan beneathTwo (.var (.vs .vz)) (.var .vz)) slot target)
  apply congrArg₂ Term.eq
  · rfl
  · simp only [instantiate, compileAt_subst, HOL.subst, Subst.lift, Subst.single]
    have slotSame : HOL.subst (Subst.single target) (HOL.rename Rename.weaken slot) = slot :=
      PredicateFixedPoint.subst_single_weaken target slot
    rw [slotSame]
    apply congrArg (fun images : Subst Const Γ Γ => compileAt zero successor plan images slot target)
    funext type entry
    rfl

theorem graph_beta_free {assumptions : List (Formula Const Γ)}
    (plan : Plan Const Γ number index) (slot : Term Const Γ number) (target : Term Const Γ index) :
    (graph_beta zero successor (assumptions := assumptions) plan slot target).FunctionExtensionalityFree := by
  unfold graph_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

private theorem subst_raised {type bound : Ty Base} (images : Subst Const Γ Δ) (term : Term Const Γ type) :
    HOL.subst (fun entry => weaken (σ := bound) (images entry)) term = weaken (HOL.subst images term) := by
  change HOL.subst (fun entry => weaken (σ := bound) (images entry)) term =
    HOL.rename Rename.weaken (HOL.subst images term)
  rw [← subst_ofRename, HOL.subst_comp]
  apply HOL.subst_ext
  intro result entry
  exact (subst_ofRename Rename.weaken (images entry)).symm

def compileAt_result (plan : Plan Const Γ number index) :
    {Δ : Ctx Base} → (images : Subst Const Γ Δ) →
    (slot : Term Const Δ number) → (target expected : Term Const Δ index) →
    {assumptions : List (Formula Const Δ)} →
    (∀ occurrence : Fin plan.length, ProofSyntax Const assumptions (.eq (HOL.subst images (plan.get occurrence).2) expected)) →
    ProofSyntax Const assumptions (compileAt zero successor plan images slot target) →
    ProofSyntax Const assumptions (.eq target expected) := by
  induction plan with
  | nil =>
      intro Δ images slot target expected assumptions aligned present
      exact .botE present
  | cons segment rest previous =>
      intro Δ images slot target expected assumptions aligned present
      let first := Term.and
        (.app (.app (weakenCtx _ (SuccessorOrder.less successor)) slot) (HOL.subst images segment.1))
        (.eq target (HOL.subst images segment.2))
      let body := Term.and
        (.app (.app (.app (weakenCtx _ (SuccessorOrder.sum zero successor))
          (weaken (HOL.subst images segment.1))) (.var .vz)) (weaken slot))
        (compileAt zero successor rest (fun entry => weaken (images entry)) (.var .vz) (weaken target))
      apply ProofSyntax.orE present
      · exact .eqTrans (.andER (.hyp 0)) ((aligned ⟨0, Nat.zero_lt_succ rest.length⟩).prepend first)
      · apply ProofSyntax.exE (ProofSyntax.hyp 0)
        let localAssumptions := body :: weakenHyps (Term.ex body :: assumptions)
        apply previous (fun entry => weaken (images entry)) (.var .vz) (weaken target) (weaken expected)
        · intro remaining
          apply ProofSyntax.castIndices rfl ?_
            (((ProofSyntax.rename Rename.weaken (aligned remaining.succ)).prepend
              (weaken (Term.ex body))).prepend body)
          exact congrArg (fun term => Term.eq term (weaken expected)) (subst_raised images (rest.get remaining).2).symm
        · exact .andER (ProofSyntax.hyp (Δ := localAssumptions) 0)

theorem compileAt_result_free (plan : Plan Const Γ number index) :
    ∀ {Δ : Ctx Base} (images : Subst Const Γ Δ)
      (slot : Term Const Δ number) (target expected : Term Const Δ index)
      {assumptions : List (Formula Const Δ)}
      (aligned : ∀ occurrence : Fin plan.length, ProofSyntax Const assumptions (.eq (HOL.subst images (plan.get occurrence).2) expected))
      (present : ProofSyntax Const assumptions (compileAt zero successor plan images slot target)),
      (∀ occurrence, (aligned occurrence).FunctionExtensionalityFree) →
      present.FunctionExtensionalityFree →
      (compileAt_result zero successor plan images slot target expected aligned present).FunctionExtensionalityFree := by
  induction plan with
  | nil => intro Δ images slot target expected assumptions aligned present alignedFree presentFree; exact presentFree
  | cons segment rest previous =>
      intro Δ images slot target expected assumptions aligned present alignedFree presentFree
      unfold compileAt_result
      refine ⟨presentFree, ?_, ?_⟩
      · exact ⟨trivial, (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (alignedFree ⟨0, Nat.zero_lt_succ rest.length⟩)⟩
      · refine ⟨trivial, ?_⟩
        apply previous
        · intro remaining
          apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
          apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
          exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr (alignedFree remaining.succ)
        · trivial

#print axioms graph_beta_free
#print axioms compileAt_result_free

open FiniteConstructorEncoding CurriedPredicates

theorem fieldTerms_subst {Ξ : Ctx Base} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index)
    (images : Subst Const Γ Δ) (later : Subst Const Δ Ξ) (arguments : Arguments Const Δ fields) :
    substitute later (fieldTerms fields plan images arguments) =
      fieldTerms fields plan (fun entry => HOL.subst later (images entry)) (substituteArguments later fields arguments) := by
  simp only [substitute, fieldTerms, List.map_map]
  apply List.map_congr_left
  intro segment _
  change (HOL.subst later (applyFields fields (HOL.subst images segment.1) arguments),
      HOL.subst later (applyFields fields (HOL.subst images segment.2) arguments)) = _
  simp only [applyFields_subst, HOL.subst_comp]
  rfl

def fieldBody (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index) :
    ArgumentBody Const (index :: number :: Γ) fields := fun images arguments =>
  compileAt zero successor
    (fieldTerms fields plan (fun entry => images (.vs (.vs entry))) arguments)
    Subst.id (images (.vs .vz)) (images .vz)

theorem fieldBody_natural (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index) :
    NaturalBody (@fieldBody Base Const Γ number index zero successor fields plan) := by
  intro earlierContext laterContext earlier later arguments
  simp only [fieldBody, compileAt_subst]
  rw [← fieldTerms_subst fields plan (fun entry => earlier (.vs (.vs entry))) later arguments]
  rw [compileAt_substitute]
  simp only [HOL.subst_id, Subst.id, HOL.subst]

def fieldInstanceBody (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (slot : Term Const Γ number) (target : Term Const Γ index) : ArgumentBody Const Γ fields :=
  fun images arguments => compileAt zero successor (fieldTerms fields plan images arguments)
    Subst.id (HOL.subst images slot) (HOL.subst images target)

theorem fieldInstanceBody_natural (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (slot : Term Const Γ number) (target : Term Const Γ index) :
    NaturalBody (@fieldInstanceBody Base Const Γ number index zero successor fields plan slot target) := by
  intro earlierContext laterContext earlier later arguments
  simp only [fieldInstanceBody, compileAt_subst, HOL.subst_comp]
  rw [← fieldTerms_subst fields plan earlier later arguments]
  rw [compileAt_substitute]
  simp only [HOL.subst_id, Subst.id, HOL.subst]
  rfl

theorem fieldGraph_instantiate (fields : List (Ty Base)) (plan : FieldPlan Const Γ fields number index)
    (slot : Term Const Γ number) (target : Term Const Γ index) :
    instantiate target (HOL.subst (Subst.lift (Subst.single slot))
      (abstractArguments fields (@fieldBody Base Const Γ number index zero successor fields plan))) =
      abstractArguments fields (@fieldInstanceBody Base Const Γ number index zero successor fields plan slot target) := by
  simp only [instantiate, HOL.subst_comp]
  rw [abstractArguments_subst _ _ _ (fieldBody_natural zero successor fields plan)]
  apply congrArg (abstractArguments fields)
  funext laterContext later arguments
  simp only [fieldBody, fieldInstanceBody, Subst.comp, HOL.subst, Subst.lift, Subst.single]
  have cancel : HOL.subst (Subst.single target) (HOL.rename Rename.weaken slot) = slot :=
    PredicateFixedPoint.subst_single_weaken target slot
  rw [cancel]
  simp only [HOL.rename, Rename.weaken, HOL.subst, Subst.single]

def fieldGraph_beta {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (slot : Term Const Γ number) (target : Term Const Γ index)
    (arguments : Arguments Const Γ fields) :
    ProofSyntax Const assumptions
      (.eq (applyArguments fields (.app (.app (fieldGraph zero successor fields plan) slot) target) arguments)
        (compileAt zero successor (fieldTerms fields plan Subst.id arguments) Subst.id slot target)) := by
  have head : ProofSyntax Const assumptions
      (.eq (.app (.app (fieldGraph zero successor fields plan) slot) target)
        (abstractArguments fields (@fieldInstanceBody Base Const Γ number index zero successor fields plan slot target))) :=
    ProofSyntax.castIndices rfl
    (congrArg (fun term => Term.eq (.app (.app (fieldGraph zero successor fields plan) slot) target) term)
      (fieldGraph_instantiate zero successor fields plan slot target))
    (CurriedGuardProgramProofs.beta2
      (abstractArguments fields (@fieldBody Base Const Γ number index zero successor fields plan)) slot target)
  apply ProofSyntax.eqTrans (applyArguments_congr fields _ _ arguments head)
  apply ProofSyntax.castIndices rfl ?_ (abstractArguments_beta fields
    (@fieldInstanceBody Base Const Γ number index zero successor fields plan slot target)
    (fieldInstanceBody_natural zero successor fields plan slot target) arguments)
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun entry => .var entry) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [fieldInstanceBody, identityTerm]
  rfl

theorem fieldGraph_beta_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (slot : Term Const Γ number) (target : Term Const Γ index)
    (arguments : Arguments Const Γ fields) :
    (fieldGraph_beta zero successor (assumptions := assumptions) fields plan slot target arguments).FunctionExtensionalityFree := by
  unfold fieldGraph_beta
  constructor
  · apply applyArguments_congr_free
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact CurriedGuardProgramProofs.beta2_free _ _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact abstractArguments_beta_free _ _ _ _

#print axioms fieldBody_natural
#print axioms fieldGraph_beta_free

def fieldGraph_result {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (slot : Term Const Γ number)
    (target expected : Term Const Γ index) (arguments : Arguments Const Γ fields)
    (aligned : ∀ occurrence : Fin plan.length,
      ProofSyntax Const assumptions (.eq (applyFields fields (plan.get occurrence).2 arguments) expected))
    (present : ProofSyntax Const assumptions
      (applyArguments fields (.app (.app (fieldGraph zero successor fields plan) slot) target) arguments)) :
    ProofSyntax Const assumptions (.eq target expected) := by
  apply compileAt_result zero successor (fieldTerms fields plan Subst.id arguments) Subst.id slot target expected
  · intro occurrence
    let sourceOccurrence : Fin plan.length :=
      ⟨occurrence.val, by simpa only [fieldTerms, List.length_map] using occurrence.isLt⟩
    apply ProofSyntax.castIndices rfl ?_ (aligned sourceOccurrence)
    simp only [fieldTerms, List.get_eq_getElem, List.getElem_map, HOL.subst_id, sourceOccurrence]
  · exact .impE (.eqPropEL (fieldGraph_beta zero successor fields plan slot target arguments)) present

theorem fieldGraph_result_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (slot : Term Const Γ number)
    (target expected : Term Const Γ index) (arguments : Arguments Const Γ fields)
    (aligned : ∀ occurrence : Fin plan.length,
      ProofSyntax Const assumptions (.eq (applyFields fields (plan.get occurrence).2 arguments) expected))
    (present : ProofSyntax Const assumptions
      (applyArguments fields (.app (.app (fieldGraph zero successor fields plan) slot) target) arguments))
    (alignedFree : ∀ occurrence, (aligned occurrence).FunctionExtensionalityFree)
    (presentFree : present.FunctionExtensionalityFree) :
    (fieldGraph_result zero successor fields plan slot target expected arguments aligned present).FunctionExtensionalityFree := by
  unfold fieldGraph_result
  apply compileAt_result_free
  · intro occurrence
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact alignedFree _
  · exact ⟨fieldGraph_beta_free zero successor fields plan slot target arguments, presentFree⟩

#print axioms fieldGraph_result_free

theorem fieldTerms_substitute {Ξ : Ctx Base} (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (earlier : Subst Const Γ Δ)
    (later : Subst Const Δ Ξ) (arguments : Arguments Const Ξ fields) :
    fieldTerms fields (substitute earlier plan) later arguments =
      fieldTerms fields plan (fun entry => HOL.subst later (earlier entry)) arguments := by
  simp only [fieldTerms, substitute, List.map_map]
  apply List.map_congr_left
  intro segment _
  change (applyFields fields (HOL.subst later (HOL.subst earlier segment.1)) arguments,
    applyFields fields (HOL.subst later (HOL.subst earlier segment.2)) arguments) = _
  simp only [HOL.subst_comp]
  rfl

theorem fieldGraph_substitute (fields : List (Ty Base))
    (plan : FieldPlan Const Γ fields number index) (images : Subst Const Γ Δ) :
    HOL.subst images (fieldGraph zero successor fields plan) =
      fieldGraph zero successor fields (substitute images plan) := by
  change Term.lam (.lam (HOL.subst (Subst.lift (Subst.lift images))
      (abstractArguments fields (@fieldBody Base Const Γ number index zero successor fields plan)))) =
    Term.lam (.lam (abstractArguments fields
      (@fieldBody Base Const Δ number index zero successor fields (substitute images plan))))
  rw [abstractArguments_subst _ _ _ (fieldBody_natural zero successor fields plan)]
  apply congrArg Term.lam
  apply congrArg Term.lam
  apply congrArg (abstractArguments fields)
  funext laterContext later arguments
  simp only [fieldBody, fieldTerms_substitute, Subst.lift, HOL.subst]
  apply congrArg (fun data => compileAt zero successor data Subst.id (later (.vs .vz)) (later .vz))
  apply congrArg (fun mapping : Subst Const Γ laterContext => fieldTerms fields plan mapping arguments)
  funext type entry
  rw [HOL.rename_comp]
  exact HOL.subst_rename later (fun index => .vs (.vs index)) (images entry)

#print axioms fieldGraph_substitute

end Mettapedia.Logic.HOL.OrderedPositionPrograms
