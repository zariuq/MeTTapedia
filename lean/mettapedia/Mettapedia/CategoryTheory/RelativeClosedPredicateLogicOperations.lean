import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicDiagrams
import Mettapedia.CategoryTheory.InternalPredicateImplication

/-!
# The generated predicate object earns its local implication laws

The four authored conjunctive declarations yield the actual predicate
semilattice. The implication declarations yield the finite local interface.
The ordered-consequent object remains its authored raw presentation; its
comparison to the chosen equalizer transports the complete local diagram.
Neither literal equality of raw objects nor a source classifier is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C : Type k} [Category.{k} C]

abbrev inclusion := equationInclusion (C := C)

def operations : InternalConjunctiveObject.Operations (Object (lawfulSignature (C := C))) where
  proposition := inclusion.object omega
  truth := inclusion.functor.map (classOf truthRaw)
  conjunction := inclusion.functor.map (classOf conjunctionRaw)

private theorem lift_pairing {names : Symbols.{k}}
    {presentation : Signature (C := C) (symbols := names)}
    {context left right : Object presentation} (first : context ⟶ left) (second : context ⟶ right) :
    lift first second = pairing first second := by
  apply product_joint_cancel
  · exact (lift_fst first second).trans (pairing_first first second).symm
  · exact (lift_snd first second).trans (pairing_second first second).symm

private theorem toUnit_terminal {names : Symbols.{k}}
    {presentation : Signature (C := C) (symbols := names)} (context : Object presentation) :
    toUnit context = toTerminal context := toTerminal_unique _

theorem laws : (operations (C := C)).Laws where
  commutativity := by
    change lift (snd operations.proposition operations.proposition)
      (fst operations.proposition operations.proposition) ≫ operations.conjunction = operations.conjunction
    rw [lift_pairing]
    exact declared_law (Law.commutativity (C := C))
  associativity := by
    unfold InternalConjunctiveObject.Operations.associateLeft
      InternalConjunctiveObject.Operations.associateRight
    simp only [lift_pairing]
    exact declared_law (Law.associativity (C := C))
  idempotence := by
    change lift (𝟙 operations.proposition) (𝟙 operations.proposition) ≫ operations.conjunction =
      𝟙 operations.proposition
    rw [lift_pairing]
    exact declared_law (Law.idempotence (C := C))
  truthUnit := by
    change lift (𝟙 operations.proposition) (toUnit operations.proposition ≫ operations.truth) ≫
      operations.conjunction = 𝟙 operations.proposition
    rw [lift_pairing, toUnit_terminal]
    exact declared_law (Law.truthUnit (C := C))

def implicationOperation : (operations (C := C)).proposition ⊗ operations.proposition ⟶ operations.proposition :=
  inclusion.functor.map (classOf implicationRaw)

def orderedComparison : inclusion.object orderedPredicates ≅
    InternalPredicateImplication.orderedPairs (operations (C := C)) :=
  (PresentedEqualizer.isLimit (inclusion.rawArrow conjunctionRaw)
    (inclusion.rawArrow (RawHom.first omega omega))).conePointUniqueUpToIso
      (limit.isLimit (parallelPair operations.conjunction
        (fst operations.proposition operations.proposition)))

theorem orderedComparison_inclusion :
    (orderedComparison (C := C)).inv ≫ inclusion.functor.map
      (classOf (RawHom.inclusion conjunctionRaw (RawHom.first omega omega))) =
      equalizer.ι operations.conjunction (fst operations.proposition operations.proposition) :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (PresentedEqualizer.isLimit (inclusion.rawArrow conjunctionRaw)
      (inclusion.rawArrow (RawHom.first omega omega))) (limit.isLimit _) WalkingParallelPair.zero

theorem orderedComparison_smaller :
    (orderedComparison (C := C)).inv ≫ inclusion.functor.map (classOf smallerRaw) =
      InternalPredicateImplication.smaller operations := by
  change orderedComparison.inv ≫ inclusion.functor.map
      (classOf (RawHom.inclusion conjunctionRaw (RawHom.first omega omega))) ≫
      first operations.proposition operations.proposition =
    equalizer.ι operations.conjunction (fst operations.proposition operations.proposition) ≫
      first operations.proposition operations.proposition
  rw [← Category.assoc, orderedComparison_inclusion]

theorem orderedComparison_larger :
    (orderedComparison (C := C)).inv ≫ inclusion.functor.map (classOf largerRaw) =
      InternalPredicateImplication.larger operations := by
  change orderedComparison.inv ≫ inclusion.functor.map
      (classOf (RawHom.inclusion conjunctionRaw (RawHom.first omega omega))) ≫
      second operations.proposition operations.proposition =
    equalizer.ι operations.conjunction (fst operations.proposition operations.proposition) ≫
      second operations.proposition operations.proposition
  rw [← Category.assoc, orderedComparison_inclusion]

private theorem implication_authored_monotonicity :
    operations.meet
      (InternalPredicateImplication.applyOperation operations implicationOperation
        (fst operations.proposition (inclusion.object orderedPredicates))
        (snd operations.proposition (inclusion.object orderedPredicates) ≫
          inclusion.functor.map (classOf (largerRaw (C := C)))))
      (InternalPredicateImplication.applyOperation operations implicationOperation
        (fst operations.proposition (inclusion.object orderedPredicates))
        (snd operations.proposition (inclusion.object orderedPredicates) ≫
          inclusion.functor.map (classOf (smallerRaw (C := C))))) =
      InternalPredicateImplication.applyOperation operations implicationOperation
        (fst operations.proposition (inclusion.object orderedPredicates))
        (snd operations.proposition (inclusion.object orderedPredicates) ≫
          inclusion.functor.map (classOf (smallerRaw (C := C)))) := by
  unfold InternalConjunctiveObject.Operations.meet InternalPredicateImplication.applyOperation
  simp only [lift_pairing]
  exact declared_law (Law.implicationMonotonicity (C := C))

def implicationQualification : InternalPredicateImplication.Qualification (operations (C := C)) where
  operation := implicationOperation
  monotonicity := by
    let incoming : InternalPredicateImplication.monotonicityScope (operations (C := C)) ⟶
        product operations.proposition (inclusion.object orderedPredicates) :=
      lift (fst _ _) (snd _ _ ≫ (orderedComparison (C := C)).inv)
    let fixed := fst (operations (C := C)).proposition
      ((inclusion (C := C)).object orderedPredicates)
    let first := snd (operations (C := C)).proposition
      ((inclusion (C := C)).object orderedPredicates) ≫
      inclusion.functor.map (classOf smallerRaw)
    let second := snd (operations (C := C)).proposition
      ((inclusion (C := C)).object orderedPredicates) ≫
      inclusion.functor.map (classOf largerRaw)
    have natural := operations.reindex_meet incoming
      (InternalPredicateImplication.applyOperation operations implicationOperation fixed second)
      (InternalPredicateImplication.applyOperation operations implicationOperation fixed first)
    have localRead : operations.meet
        (InternalPredicateImplication.applyOperation operations implicationOperation fixed second)
        (InternalPredicateImplication.applyOperation operations implicationOperation fixed first) =
        InternalPredicateImplication.applyOperation operations implicationOperation fixed first :=
      implication_authored_monotonicity (C := C)
    have complete := natural.symm.trans
      (congrArg (fun arrow => incoming ≫ arrow) localRead)
    have fixedRead : incoming ≫ fixed = InternalPredicateImplication.antecedent operations :=
      lift_fst _ _
    have firstRead : incoming ≫ first = InternalPredicateImplication.smallerConsequent operations := by
      change lift (fst _ _) (snd _ _ ≫ orderedComparison.inv) ≫ snd _ _ ≫
        inclusion.functor.map (classOf smallerRaw) = _
      rw [lift_snd_assoc, Category.assoc, orderedComparison_smaller]
      rfl
    have secondRead : incoming ≫ second = InternalPredicateImplication.largerConsequent operations := by
      change lift (fst _ _) (snd _ _ ≫ orderedComparison.inv) ≫ snd _ _ ≫
        inclusion.functor.map (classOf largerRaw) = _
      rw [lift_snd_assoc, Category.assoc, orderedComparison_larger]
      rfl
    simpa only [InternalConjunctiveObject.Operations.reindex,
      InternalPredicateImplication.apply_substitution, fixedRead, firstRead, secondRead] using complete
  unit := by
    unfold InternalConjunctiveObject.Operations.meet InternalPredicateImplication.applyOperation
    simp only [lift_pairing]
    exact declared_law (Law.implicationUnit (C := C))
  counit := by
    unfold InternalConjunctiveObject.Operations.meet InternalPredicateImplication.applyOperation
    simp only [lift_pairing]
    exact declared_law (Law.implicationCounit (C := C))

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.SourceOperations
