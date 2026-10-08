import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# Guarded predicates at a selected rewrite position

The projection from complete rule instances to focus-variable assignments
binds every rely input. Universal quantification retains the conditional
postcondition; image along the actual focus map produces the modality.
The pullback square states that the rule-instance context is the complete
rely context for that focus, including any shared parameters.

The elimination conclusion is an image predicate retaining a complete rule
instance and its postcondition. It does not choose a data witness from an
erased existential predicate. Supplied instances are read separately by
the operational consumer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.PositionedRewritePredicateLogic

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v p

variable {C : Type u} [Category.{v} C]
variable (doctrine : PredicateDoctrine.FirstOrder.{u,v,p} C)
variable {instances assignments assay carrier : C}
variable (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)

/-- All rely inputs satisfy the independently supplied condition. -/
def introPredicate (condition : doctrine.Fiber instances) : doctrine.Fiber assignments :=
  doctrine.forallAlong forget condition

/-- The actual focus image retains a possible complete assignment. -/
def modality (condition : doctrine.Fiber instances) : doctrine.Fiber carrier :=
  doctrine.existsAlong focus (introPredicate doctrine forget condition)

theorem introduction_iff (condition : doctrine.Fiber instances)
    (premise : doctrine.Fiber assignments) :
    doctrine.reindex forget premise ≤ condition ↔
      premise ≤ introPredicate doctrine forget condition :=
  doctrine.forall_adj forget premise condition

theorem introduction (condition : doctrine.Fiber instances)
    (premise : doctrine.Fiber assignments)
    (admitted : doctrine.reindex forget premise ≤ condition) :
    doctrine.existsAlong focus premise ≤ modality doctrine forget focus condition :=
  doctrine.exists_mono focus ((introduction_iff doctrine forget condition premise).mp admitted)

theorem supplied_focus (condition : doctrine.Fiber instances) :
    introPredicate doctrine forget condition ≤
      doctrine.reindex focus (modality doctrine forget focus condition) :=
  (doctrine.exists_adj focus).le_u_l _

theorem modality_mono : Monotone (modality doctrine forget focus) :=
  (doctrine.exists_mono focus).comp (doctrine.forall_mono forget)

variable (instantiate : instances ⟶ assay) (hole : assay ⟶ carrier)

def conditional (relies : doctrine.Fiber assay) (postcondition : doctrine.Fiber instances) :
    doctrine.Fiber instances := doctrine.reindex instantiate relies ⇨ postcondition

theorem guarded_introduction_iff (relies : doctrine.Fiber assay)
    (postcondition : doctrine.Fiber instances) (premise : doctrine.Fiber assignments) :
    doctrine.reindex forget premise ⊓ doctrine.reindex instantiate relies ≤ postcondition ↔
      premise ≤ introPredicate doctrine forget (conditional doctrine instantiate relies postcondition) := by
  rw [← le_himp_iff]
  exact introduction_iff doctrine forget _ premise

/-- Frobenius and the actual square reconstruct the complete guarded instance.
The result retains its postcondition; it is not equality conversion. -/
theorem guarded_elimination
    (square : IsPullback forget instantiate focus hole)
    (relies : doctrine.Fiber assay) (postcondition : doctrine.Fiber instances) :
    doctrine.reindex hole
        (modality doctrine forget focus (conditional doctrine instantiate relies postcondition)) ⊓ relies ≤
      doctrine.existsAlong instantiate postcondition := by
  rw [modality, doctrine.exists_baseChange forget instantiate focus hole square,
    ← doctrine.frobenius instantiate]
  apply doctrine.exists_mono instantiate
  exact (inf_le_inf_right _
    ((doctrine.forall_adj forget).l_u_le
      (conditional doctrine instantiate relies postcondition))).trans himp_inf_le

theorem supplied_condition {context : C}
    (assignment : context ⟶ assignments) (assayMap : context ⟶ assay)
    (instanceMap : context ⟶ instances)
    (assignmentRead : instanceMap ≫ forget = assignment)
    (assayRead : instanceMap ≫ instantiate = assayMap)
    (relies : doctrine.Fiber assay) (postcondition : doctrine.Fiber instances)
    (intro : doctrine.reindex assignment
      (introPredicate doctrine forget (conditional doctrine instantiate relies postcondition)) = ⊤)
    (rely : doctrine.reindex assayMap relies = ⊤) :
    doctrine.reindex instanceMap postcondition = ⊤ := by
  have admitted := doctrine.reindex_mono instanceMap
    ((doctrine.forall_adj forget).l_u_le (conditional doctrine instantiate relies postcondition))
  change doctrine.reindex assignment (doctrine.forallAlong forget
    (conditional doctrine instantiate relies postcondition)) = ⊤ at intro
  rw [← doctrine.reindex_comp, assignmentRead, intro, conditional,
    doctrine.reindex_himp, ← doctrine.reindex_comp, assayRead, rely] at admitted
  apply eq_top_iff.mpr
  simpa only [top_inf_eq] using (le_himp_iff.mp admitted)

variable {laterInstances laterAssignments laterCarrier : C}

/-- Arbitrary future contexts act through both genuine base-change squares. -/
theorem modality_baseChange
    (instanceMap : laterInstances ⟶ instances)
    (assignmentMap : laterAssignments ⟶ assignments)
    (carrierMap : laterCarrier ⟶ carrier)
    (laterForget : laterInstances ⟶ laterAssignments)
    (laterFocus : laterAssignments ⟶ laterCarrier)
    (instanceSquare : IsPullback instanceMap laterForget forget assignmentMap)
    (focusSquare : IsPullback assignmentMap laterFocus focus carrierMap)
    (condition : doctrine.Fiber instances) :
    doctrine.reindex carrierMap (modality doctrine forget focus condition) =
      modality doctrine laterForget laterFocus (doctrine.reindex instanceMap condition) := by
  rw [modality, doctrine.exists_baseChange assignmentMap laterFocus focus carrierMap focusSquare,
    introPredicate, doctrine.forall_baseChange instanceMap laterForget forget assignmentMap instanceSquare]
  rfl

end Mettapedia.CategoryTheory.PositionedRewritePredicateLogic
