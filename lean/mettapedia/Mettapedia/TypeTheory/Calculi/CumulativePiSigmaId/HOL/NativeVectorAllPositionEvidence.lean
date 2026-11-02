import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistence
import Mettapedia.Logic.HOL.IndexedVectorPredicateLifting

/-!
# Actual All existence from evidence at every vector position

The position premise quantifies only actual lookup positions of the supplied
open vector. Relational lifting derives the witnessed vector predicate, which
feeds the existing All producer. The original source child-array correspondence
is a separate obligation; primitive computation laws enter only production.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.PositionEvidence
open Mettapedia.Logic
open HOL.FiniteConstructorEncoding HOL.CurriedPredicates
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {evidence : HOL.Ty Base}
    (original : NativeVectorComputationRows.Operations Base Const)
    {Γ Ξ : HOL.Ctx Base}

abbrev signature := NativeVectorComputationRows.GuardedFamily.algebra original
abbrev Fields := [original.number, original.element]

def body (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector) :
    ArgumentBody Const Γ (Fields original) := fun images fields =>
  .imp (HOL.IndexedVectorPositions.lookup (signature original) (HOL.subst images index) (HOL.subst images vector)
    fields.1 fields.2.1) (existsValue [] (.app (HOL.subst images predicate) fields.2.1))

theorem body_natural (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector) :
    NaturalBody (body original predicate index vector) := by
  intro Δ Ω earlier later fields
  simp only [body, HOL.subst, HOL.IndexedVectorPositions.lookup_subst, existsValue_subst,
    HOL.subst_comp, substituteArguments]
  rfl

def condition (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector) : HOL.Formula Const Γ :=
  forallArguments (Fields original) (body original predicate index vector)

@[simp] theorem condition_subst (images : HOL.Subst Const Γ Ξ)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector) :
    HOL.subst images (condition original predicate index vector) =
      condition original (HOL.subst images predicate) (HOL.subst images index) (HOL.subst images vector) := by
  unfold condition
  rw [forallArguments_subst _ _ _ (body_natural original predicate index vector)]
  apply congrArg (forallArguments (Fields original))
  funext laterContext later fields
  simp only [body, HOL.subst_comp]
  rfl

variable {Δ : List (HOL.Formula Const Γ)}

def atPosition (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (position : HOL.Term Const Γ original.number) (element : HOL.Term Const Γ original.element)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector)) :
    HOL.ProofSyntax Const Δ (.imp (HOL.IndexedVectorPositions.lookup (signature original) index vector position element)
      (existsValue [] (.app predicate element))) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (forallArguments_elim _ _ (body_natural original predicate index vector) (position, element, PUnit.unit) given)
  simp only [body, HOL.subst_id]

theorem atPosition_free (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (position : HOL.Term Const Γ original.number) (element : HOL.Term Const Γ original.element)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector))
    (free : given.FunctionExtensionalityFree) :
    (atPosition original predicate index vector position element given).FunctionExtensionalityFree := by
  unfold atPosition
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_elim_free _ _ _ _ given free

def guardedPoint (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (position : HOL.Term Const Γ original.number) (element : HOL.Term Const Γ original.element)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector)) :
    HOL.ProofSyntax Const Δ (.imp (HOL.IndexedVectorPositions.lookup (signature original) index vector position element)
      (.imp (.app A element) (.app (Existence.lifted original A predicate) element))) := by
  let found := HOL.IndexedVectorPositions.lookup (signature original) index vector position element
  let guard := HOL.Term.app A element
  let hypotheses := guard :: found :: Δ
  refine .impI (.impI ?_)
  exact .impE (.eqPropER (Existence.lifted_apply original A predicate element))
    (.andI (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩)
      (.impE (atPosition original predicate index vector position element ((given.prepend found).prepend guard))
        (.hyp (Δ := hypotheses) ⟨1, by simp [hypotheses]⟩)))

theorem guardedPoint_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (position : HOL.Term Const Γ original.number) (element : HOL.Term Const Γ original.element)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector))
    (free : given.FunctionExtensionalityFree) :
    (guardedPoint original A predicate index vector position element given).FunctionExtensionalityFree := by
  unfold guardedPoint
  refine ⟨Existence.lifted_apply_free original A predicate element, True.intro, ?_, True.intro⟩
  apply atPosition_free
  simpa only [HOL.ProofSyntax.prepend, HOL.ProofSyntax.functionExtensionalityFree_mono] using free

def liftingBranch (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector)) :
    ArgumentProof Δ (Fields original)
      (HOL.IndexedVectorPredicateLifting.pointBody (signature original) A (Existence.lifted original A predicate) index vector) := by
  intro Ξ images fields
  have mapped : HOL.ProofSyntax Const (Δ.map (HOL.subst images))
      (condition original (HOL.subst images predicate) (HOL.subst images index) (HOL.subst images vector)) :=
    HOL.ProofSyntax.castIndices rfl (condition_subst original images predicate index vector) (given.subst images)
  apply HOL.ProofSyntax.castIndices rfl ?_
    (guardedPoint original (HOL.subst images A) (HOL.subst images predicate)
      (HOL.subst images index) (HOL.subst images vector) fields.1 fields.2.1 mapped)
  simp only [HOL.IndexedVectorPredicateLifting.pointBody, Existence.subst_lifted]

theorem liftingBranch_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector))
    (free : given.FunctionExtensionalityFree) (images : HOL.Subst Const Γ Ξ)
    (fields : Arguments Const Ξ (Fields original)) :
    (liftingBranch original A predicate index vector given images fields).FunctionExtensionalityFree := by
  unfold liftingBranch
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply guardedPoint_free
  simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices, HOL.ProofSyntax.functionExtensionalityFree_subst] using free

def liftingCondition (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector)) :
    HOL.ProofSyntax Const Δ (HOL.IndexedVectorPredicateLifting.condition (signature original)
      A (Existence.lifted original A predicate) index vector) :=
  forallArguments_intro _ _ (liftingBranch original A predicate index vector given)

theorem liftingCondition_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector)) (free : given.FunctionExtensionalityFree) :
    (liftingCondition original A predicate index vector given).FunctionExtensionalityFree :=
  forallArguments_intro_free _ _ _ (liftingBranch_free original A predicate index vector given free)

def liftedMember (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (member : HOL.ProofSyntax Const Δ ((signature original).member A index vector))
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector)) :
    HOL.ProofSyntax Const Δ ((signature original).member (Existence.lifted original A predicate) index vector) :=
  HOL.IndexedVectorPredicateLifting.relationalLift (signature original) A (Existence.lifted original A predicate)
    index vector member (liftingCondition original A predicate index vector given)

theorem liftedMember_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (member : HOL.ProofSyntax Const Δ ((signature original).member A index vector))
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector))
    (memberFree : member.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree) :
    (liftedMember original A predicate index vector member given).FunctionExtensionalityFree :=
  HOL.IndexedVectorPredicateLifting.relationalLift_free (signature original) A (Existence.lifted original A predicate)
    index vector member (liftingCondition original A predicate index vector given) memberFree
    (liftingCondition_free original A predicate index vector given givenFree)

def produce (pairs : HOL.PredicateSigma.Operations Const evidence) (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ evidence ⇒ .prop)))
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (premises : Existence.ComputationPremises original selection Δ)
    (member : HOL.ProofSyntax Const Δ ((signature original).member A index vector))
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector)) :
    HOL.ProofSyntax Const Δ (Existence.query original pairs witness selection A predicate index vector) :=
  let lifted := (signature original).member (Existence.lifted original A predicate) index vector
  .impE (.impI (Existence.produce original pairs witness selection A predicate index vector
    (premises.prepend lifted) (.hyp 0)))
    (liftedMember original A predicate index vector member given)

theorem produce_free (pairs : HOL.PredicateSigma.Operations Const evidence) (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ evidence ⇒ .prop)))
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (vector : HOL.Term Const Γ original.vector)
    (premises : Existence.ComputationPremises original selection Δ)
    (member : HOL.ProofSyntax Const Δ ((signature original).member A index vector))
    (given : HOL.ProofSyntax Const Δ (condition original predicate index vector))
    (premisesFree : premises.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree) :
    (produce original pairs witness selection A predicate index vector premises member given).FunctionExtensionalityFree := by
  unfold produce
  constructor
  · apply Existence.produce_free
    · exact premises.prepend_free _ premisesFree
    · trivial
  · exact liftedMember_free original A predicate index vector member given memberFree givenFree

#print axioms liftedMember_free
#print axioms produce_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.PositionEvidence
