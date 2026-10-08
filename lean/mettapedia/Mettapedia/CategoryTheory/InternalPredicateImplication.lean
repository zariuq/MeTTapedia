import Mettapedia.CategoryTheory.InternalConjunctiveObject

/-!
# Finite local diagrams for predicate implication

Implication is an actual arrow on two independent predicate inputs. One
monotonicity diagram on the ordered-consequent equalizer and two generic
unit/counit diagrams derive the meet/implication adjunction in every context.
The antecedent remains fixed during monotonicity and is retained by all
substitution maps. No all-context implication law is an input field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateImplication

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open InternalConjunctiveObject

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [HasEqualizers C]
variable (original : Operations C) (originalLaws : original.Laws)

def orderedPairs : C := equalizer original.conjunction
  (fst original.proposition original.proposition)

def orderInclusion : orderedPairs original ⟶ original.proposition ⊗ original.proposition :=
  equalizer.ι _ _

def smaller : orderedPairs original ⟶ original.proposition := orderInclusion original ≫ fst _ _
def larger : orderedPairs original ⟶ original.proposition := orderInclusion original ≫ snd _ _

def orderFactor {context : C} (first second : original.Fiber context)
    (ordered : original.meet second first = first) : context ⟶ orderedPairs original :=
  equalizer.lift (lift first second)
    (((original.meet_comm originalLaws first second).trans ordered).trans (lift_fst first second).symm)

@[reassoc (attr := simp)] theorem orderFactor_smaller {context : C}
    (first second : original.Fiber context) (ordered : original.meet second first = first) :
    orderFactor original originalLaws first second ordered ≫ smaller original = first := by
  simp only [orderFactor, smaller, orderInclusion, ← Category.assoc, equalizer.lift_ι]
  exact lift_fst first second

@[reassoc (attr := simp)] theorem orderFactor_larger {context : C}
    (first second : original.Fiber context) (ordered : original.meet second first = first) :
    orderFactor original originalLaws first second ordered ≫ larger original = second := by
  simp only [orderFactor, larger, orderInclusion, ← Category.assoc, equalizer.lift_ι]
  exact lift_snd first second

omit [HasEqualizers C] in
def applyOperation (operation : original.proposition ⊗ original.proposition ⟶ original.proposition)
    {context : C} (antecedent consequent : original.Fiber context) : original.Fiber context :=
  lift antecedent consequent ≫ operation

omit [HasEqualizers C] in
theorem apply_substitution
    (operation : original.proposition ⊗ original.proposition ⟶ original.proposition)
    {first second : C} (incoming : first ⟶ second) (antecedent consequent : original.Fiber second) :
    incoming ≫ applyOperation original operation antecedent consequent =
      applyOperation original operation (incoming ≫ antecedent) (incoming ≫ consequent) :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun arrow => arrow ≫ operation) (comp_lift incoming antecedent consequent))

def monotonicityScope : C := original.proposition ⊗ orderedPairs original

def antecedent : monotonicityScope original ⟶ original.proposition := fst _ _
def smallerConsequent : monotonicityScope original ⟶ original.proposition := snd _ _ ≫ smaller original
def largerConsequent : monotonicityScope original ⟶ original.proposition := snd _ _ ≫ larger original

structure Qualification where
  operation : original.proposition ⊗ original.proposition ⟶ original.proposition
  monotonicity : original.meet
      (applyOperation original operation (antecedent original) (largerConsequent original))
      (applyOperation original operation (antecedent original) (smallerConsequent original)) =
        applyOperation original operation (antecedent original) (smallerConsequent original)
  unit : original.meet
      (applyOperation original operation (fst _ _) (original.meet (fst _ _) (snd _ _)))
      (snd original.proposition original.proposition) = snd _ _
  counit : original.meet (snd original.proposition original.proposition)
      (original.meet (fst _ _) (applyOperation original operation (fst _ _) (snd _ _))) =
        original.meet (fst _ _) (applyOperation original operation (fst _ _) (snd _ _))

namespace Qualification

variable (qualified : Qualification original)

def implies {context : C} (first second : original.Fiber context) : original.Fiber context :=
  applyOperation original qualified.operation first second

theorem implies_substitution {first second : C} (incoming : first ⟶ second)
    (antecedent consequent : original.Fiber second) :
    incoming ≫ qualified.implies original antecedent consequent =
      qualified.implies original (incoming ≫ antecedent) (incoming ≫ consequent) :=
  apply_substitution original qualified.operation incoming antecedent consequent

theorem monotone_at {context : C} (fixed : context ⟶ original.proposition) :
    letI : SemilatticeInf (context ⟶ original.proposition) := original.semilattice originalLaws context
    Monotone (α := context ⟶ original.proposition) (β := context ⟶ original.proposition)
      (fun consequent : context ⟶ original.proposition =>
      (qualified.implies original fixed consequent : context ⟶ original.proposition)) := by
  intro first second ordered
  change original.meet second first = first at ordered
  change original.meet (qualified.implies original fixed second)
    (qualified.implies original fixed first) = qualified.implies original fixed first
  let pairs := orderFactor original originalLaws first second ordered
  let scopeMap := lift fixed pairs
  have natural := original.reindex_meet scopeMap
    (applyOperation original qualified.operation (antecedent original) (largerConsequent original))
    (applyOperation original qualified.operation (antecedent original) (smallerConsequent original))
  have complete := natural.symm.trans (congrArg (fun arrow => scopeMap ≫ arrow) qualified.monotonicity)
  simp only [Operations.reindex, apply_substitution] at complete
  have fixedRead : scopeMap ≫ antecedent original = fixed := lift_fst fixed pairs
  have firstRead : scopeMap ≫ smallerConsequent original = first := by
    change lift fixed pairs ≫ snd _ _ ≫ smaller original = first
    rw [lift_snd_assoc]
    exact orderFactor_smaller original originalLaws first second ordered
  have secondRead : scopeMap ≫ largerConsequent original = second := by
    change lift fixed pairs ≫ snd _ _ ≫ larger original = second
    rw [lift_snd_assoc]
    exact orderFactor_larger original originalLaws first second ordered
  rw [fixedRead, firstRead, secondRead] at complete
  exact complete

theorem unit_at {context : C} (first second : original.Fiber context) :
    original.meet (qualified.implies original first (original.meet first second)) second = second := by
  let incoming := lift first second
  have natural := original.reindex_meet incoming
    (applyOperation original qualified.operation (fst _ _) (original.meet (fst _ _) (snd _ _)))
    (snd _ _)
  have complete := natural.symm.trans (congrArg (fun arrow => incoming ≫ arrow) qualified.unit)
  have meetRead : incoming ≫ original.meet (fst _ _) (snd _ _) = original.meet first second := by
    have reading := original.reindex_meet incoming (fst _ _) (snd _ _)
    simpa only [Operations.reindex, incoming, lift_fst, lift_snd] using reading
  simp only [Operations.reindex, apply_substitution] at complete
  rw [meetRead] at complete
  simpa only [incoming, lift_fst, lift_snd, implies] using complete

theorem counit_at {context : C} (first second : original.Fiber context) :
    original.meet second (original.meet first (qualified.implies original first second)) =
      original.meet first (qualified.implies original first second) := by
  let incoming := lift first second
  have natural := original.reindex_meet incoming (snd _ _)
    (original.meet (fst _ _) (applyOperation original qualified.operation (fst _ _) (snd _ _)))
  have complete := natural.symm.trans (congrArg (fun arrow => incoming ≫ arrow) qualified.counit)
  have meetRead : incoming ≫ original.meet (fst _ _)
      (applyOperation original qualified.operation (fst _ _) (snd _ _)) =
        original.meet first (qualified.implies original first second) := by
    have reading := original.reindex_meet incoming (fst _ _)
      (applyOperation original qualified.operation (fst _ _) (snd _ _))
    simpa only [Operations.reindex, apply_substitution, incoming, lift_fst, lift_snd, implies] using reading
  simp only [Operations.reindex] at complete
  rw [meetRead] at complete
  simpa only [incoming, lift_snd] using complete

theorem adjunction {context : C} (fixed : context ⟶ original.proposition) :
    letI : SemilatticeInf (context ⟶ original.proposition) := original.semilattice originalLaws context
    GaloisConnection (α := context ⟶ original.proposition) (β := context ⟶ original.proposition)
      (fun predicate : context ⟶ original.proposition =>
        (original.meet fixed predicate : context ⟶ original.proposition))
      (fun predicate : context ⟶ original.proposition =>
        (qualified.implies original fixed predicate : context ⟶ original.proposition)) := by
  let : SemilatticeInf (context ⟶ original.proposition) := original.semilattice originalLaws context
  intro first second
  constructor
  · intro ordered
    have preserved := monotone_at original originalLaws qualified fixed ordered
    have bound : first ≤ qualified.implies original fixed (original.meet fixed first) :=
      unit_at original qualified fixed first
    exact bound.trans preserved
  · intro ordered
    have preserved := inf_le_inf_left fixed ordered
    have bound : @LE.le (context ⟶ original.proposition) inferInstance
        (original.meet fixed (qualified.implies original fixed second)) second :=
      counit_at original qualified fixed second
    exact preserved.trans bound

end Qualification

end Mettapedia.CategoryTheory.InternalPredicateImplication
