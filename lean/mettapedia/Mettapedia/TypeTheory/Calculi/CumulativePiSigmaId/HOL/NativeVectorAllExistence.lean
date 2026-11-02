import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllNaturality
import Mettapedia.Logic.HOL.PredicateSigmaExistence

/-!
# Constructing actual All witnesses from witnessed vector elements

Induction takes place over the object-level least vector predicate, so the
index and vector may remain neutral. The four computation laws stay explicit.
Relating source child slots to this lifted membership is a separate premise
bridge; it is not supplied by the existence construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Existence
open Mettapedia.Logic
open HOL.CurriedPredicates
open Reading
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {evidence : HOL.Ty Base}
    (original : NativeVectorComputationRows.Operations Base Const)
    (pairs : HOL.PredicateSigma.Operations Const evidence) (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ evidence ⇒ .prop)))
    {Γ Ξ : HOL.Ctx Base}

def lifted (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.Term Const Γ original.elementPredicate :=
  .lam (.and (.app (HOL.weaken A) (.var .vz))
    (existsValue [] (.app (HOL.weaken predicate) (.var .vz))))

@[simp] theorem subst_lifted (images : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.subst images (lifted original A predicate) =
      lifted original (HOL.subst images A) (HOL.subst images predicate) := by
  simp only [lifted, HOL.subst, existsValue_subst, HOL.subst_weaken, HOL.Subst.lift]

@[simp] theorem rename_lifted (rho : HOL.Rename Base Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.rename rho (lifted original A predicate) =
      lifted original (HOL.rename rho A) (HOL.rename rho predicate) := by
  simpa only [HOL.subst_ofRename] using subst_lifted original (HOL.Subst.ofRename rho) A predicate

def query (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) : HOL.Formula Const Γ :=
  existsValue [] (allCode original pairs witness selection A predicate index value)

@[simp] theorem subst_query (images : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    HOL.subst images (query original pairs witness selection A predicate index value) =
      query original pairs witness selection (HOL.subst images A) (HOL.subst images predicate)
        (HOL.subst images index) (HOL.subst images value) := by
  simp only [query, existsValue_subst, subst_allCode]

@[simp] theorem rename_query (rho : HOL.Rename Base Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    HOL.rename rho (query original pairs witness selection A predicate index value) =
      query original pairs witness selection (HOL.rename rho A) (HOL.rename rho predicate)
        (HOL.rename rho index) (HOL.rename rho value) := by
  simpa only [HOL.subst_ofRename] using subst_query original pairs witness selection
    (HOL.Subst.ofRename rho) A predicate index value

def atIndex (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) : HOL.Term Const Γ (original.vector ⇒ .prop) :=
  .lam (query original pairs witness selection (HOL.weaken A) (HOL.weaken predicate) (HOL.weaken index) (.var .vz))

@[simp] theorem subst_atIndex (images : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) :
    HOL.subst images (atIndex original pairs witness selection A predicate index) =
      atIndex original pairs witness selection (HOL.subst images A) (HOL.subst images predicate)
        (HOL.subst images index) := by
  simp only [atIndex, HOL.subst, subst_query, HOL.subst_weaken, HOL.Subst.lift]

def property (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.Term Const Γ (original.number ⇒ original.vector ⇒ .prop) :=
  .lam (atIndex original pairs witness selection (HOL.weaken A) (HOL.weaken predicate) (.var .vz))

@[simp] theorem subst_property (images : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.subst images (property original pairs witness selection A predicate) =
      property original pairs witness selection (HOL.subst images A) (HOL.subst images predicate) := by
  simp only [property, HOL.subst, subst_atIndex, HOL.subst_weaken, HOL.Subst.lift]

@[simp] theorem rename_property (rho : HOL.Rename Base Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.rename rho (property original pairs witness selection A predicate) =
      property original pairs witness selection (HOL.rename rho A) (HOL.rename rho predicate) := by
  simpa only [HOL.subst_ofRename] using subst_property original pairs witness selection
    (HOL.Subst.ofRename rho) A predicate

variable {Δ : List (HOL.Formula Const Γ)}

def lifted_apply (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (value : HOL.Term Const Γ original.element) :
    HOL.ProofSyntax Const Δ (.eq (.app (lifted original A predicate) value)
      (.and (.app A value) (existsValue [] (.app predicate value)))) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (.beta value (.and (.app (HOL.weaken A) (.var .vz))
      (existsValue [] (.app (HOL.weaken predicate) (.var .vz)))))
  simp only [lifted, HOL.instantiate, HOL.subst, existsValue_subst,
    HOL.PredicateFixedPoint.subst_single_weaken, HOL.Subst.single]

def atIndex_apply (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    HOL.ProofSyntax Const Δ (.eq (.app (atIndex original pairs witness selection A predicate index) value)
      (query original pairs witness selection A predicate index value)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (.beta value (query original pairs witness selection (HOL.weaken A) (HOL.weaken predicate)
      (HOL.weaken index) (.var .vz)))
  simp only [atIndex, HOL.instantiate, subst_query,
    HOL.PredicateFixedPoint.subst_single_weaken, HOL.subst, HOL.Subst.single]

def property_apply (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    HOL.ProofSyntax Const Δ (.eq
      (HOL.PredicatePair.holds (property original pairs witness selection A predicate) index value)
      (query original pairs witness selection A predicate index value)) := by
  have first : HOL.ProofSyntax Const Δ (.eq
      (.app (property original pairs witness selection A predicate) index)
      (atIndex original pairs witness selection A predicate index)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta index (atIndex original pairs witness selection (HOL.weaken A) (HOL.weaken predicate) (.var .vz)))
    simp only [property, HOL.instantiate, subst_atIndex,
      HOL.PredicateFixedPoint.subst_single_weaken, HOL.subst, HOL.Subst.single]
  exact .eqTrans (.eqApp value first) (atIndex_apply original pairs witness selection A predicate index value)

theorem lifted_apply_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (value : HOL.Term Const Γ original.element) :
    (lifted_apply (Δ := Δ) original A predicate value).FunctionExtensionalityFree := by
  simp [lifted_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem property_apply_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    (property_apply (Δ := Δ) original pairs witness selection A predicate index value).FunctionExtensionalityFree := by
  simp [property_apply, atIndex_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

variable (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))

def nil_query : HOL.ProofSyntax Const Δ
    (query original pairs witness selection A predicate (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.nil)) := by
  let code := allCode original pairs witness selection A predicate (HOL.weakenCtx Γ original.zero)
    (.app (HOL.weakenCtx Γ (operations original selection).nilCode) A)
  let point : HOL.Term Const Γ evidence := .app (HOL.weakenCtx Γ
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralProfile.reflexivityCode
      witness original.number)) (HOL.weakenCtx Γ original.zero)
  have present := existsValue_intro [] code PUnit.unit point
    (Evidence.nil_value original pairs witness selection A predicate choice recursion)
  have equal := arguments_equal original pairs witness selection (assumptions := Δ) A predicate
    (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.zero) _ _ (.eqRefl _)
    (NativeVectorComputationRows.GuardedFamily.nil_apply (operations original selection) A)
  exact .impE (.eqPropEL (existsValue_nil_congr _ _ equal)) present

def cons_query (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw)
    (headExists : HOL.ProofSyntax Const Δ (existsValue [] (.app predicate head)))
    (tailExists : HOL.ProofSyntax Const Δ (query original pairs witness selection A predicate index tail)) :
    HOL.ProofSyntax Const Δ (query original pairs witness selection A predicate
      (.app (HOL.weakenCtx Γ original.successor) index)
      ((NativeVectorComputationRows.GuardedFamily.algebra original).consValue index head tail)) := by
  have packed := HOL.PredicateSigma.independent_exists pairs (.app predicate head)
    (allCode original pairs witness selection A predicate index tail) headExists tailExists
  have computation := Computation.cons_guard original pairs witness selection A predicate index head tail
    choice recursion headLaw tailLaw
  have coded := HOL.ProofSyntax.impE (.eqPropER (existsValue_nil_congr _ _ computation)) packed
  have equal := arguments_equal original pairs witness selection (assumptions := Δ) A predicate
    (.app (HOL.weakenCtx Γ original.successor) index) (.app (HOL.weakenCtx Γ original.successor) index)
    _ _ (.eqRefl _)
    ((operations original selection).cons_apply A index head tail)
  exact .impE (.eqPropEL (existsValue_nil_congr _ _ equal)) coded

theorem nil_query_free (choiceFree : choice.FunctionExtensionalityFree)
    (recursionFree : recursion.FunctionExtensionalityFree) :
    (nil_query original pairs witness selection A predicate choice recursion).FunctionExtensionalityFree := by
  simp only [nil_query, HOL.ProofSyntax.FunctionExtensionalityFree, existsValue_nil_congr_free,
    arguments_equal_free, existsValue_intro_free, Evidence.nil_value_free,
    NativeVectorComputationRows.GuardedFamily.nil_apply, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    choiceFree, recursionFree, and_self]

theorem cons_query_free (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw)
    (headExists : HOL.ProofSyntax Const Δ (existsValue [] (.app predicate head)))
    (tailExists : HOL.ProofSyntax Const Δ (query original pairs witness selection A predicate index tail))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headLawFree : headLaw.FunctionExtensionalityFree) (tailLawFree : tailLaw.FunctionExtensionalityFree)
    (headFree : headExists.FunctionExtensionalityFree) (tailFree : tailExists.FunctionExtensionalityFree) :
    (cons_query original pairs witness selection A predicate choice recursion index head tail headLaw tailLaw
      headExists tailExists).FunctionExtensionalityFree := by
  simp only [cons_query, HOL.ProofSyntax.FunctionExtensionalityFree, existsValue_nil_congr_free,
    arguments_equal_free, HOL.PredicateSigma.independent_exists_free, Computation.cons_guard_free,
    NativeVectorComputationRows.Operations.cons_apply, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    choiceFree, recursionFree, headLawFree, tailLawFree, headFree, tailFree, and_self]

structure ComputationPremises (assumptions : List (HOL.Formula Const Γ)) where
  choice : HOL.ProofSyntax Const assumptions (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection))
  recursion : HOL.ProofSyntax Const assumptions (HOL.NaturalRecursionProofs.statement
    (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor) (original.vector ⇒ evidence ⇒ .prop))
  head : HOL.ProofSyntax Const assumptions (operations original selection).headLaw
  tail : HOL.ProofSyntax Const assumptions (operations original selection).tailLaw

namespace ComputationPremises
variable {original selection}

def rename (premises : ComputationPremises original selection Δ) (rho : HOL.Rename Base Γ Ξ) :
    ComputationPremises original selection (Δ.map (HOL.rename rho)) where
  choice := HOL.ProofSyntax.castIndices rfl (rename_choiceLaw original selection rho) (premises.choice.rename rho)
  recursion := HOL.ProofSyntax.castIndices rfl (rename_recursionLaw original selection rho) (premises.recursion.rename rho)
  head := HOL.ProofSyntax.castIndices rfl (rename_headLaw original selection rho) (premises.head.rename rho)
  tail := HOL.ProofSyntax.castIndices rfl (rename_tailLaw original selection rho) (premises.tail.rename rho)

def weaken (premises : ComputationPremises original selection Δ) (type : HOL.Ty Base) :
    ComputationPremises original selection (HOL.weakenHyps (σ := type) Δ) :=
  premises.rename HOL.Rename.weaken

def prepend (premises : ComputationPremises original selection Δ) (formula : HOL.Formula Const Γ) :
    ComputationPremises original selection (formula :: Δ) where
  choice := premises.choice.prepend formula
  recursion := premises.recursion.prepend formula
  head := premises.head.prepend formula
  tail := premises.tail.prepend formula

def FunctionExtensionalityFree (premises : ComputationPremises original selection Δ) : Prop :=
  premises.choice.FunctionExtensionalityFree ∧ premises.recursion.FunctionExtensionalityFree ∧
    premises.head.FunctionExtensionalityFree ∧ premises.tail.FunctionExtensionalityFree

theorem rename_free (premises : ComputationPremises original selection Δ) (rho : HOL.Rename Base Γ Ξ)
    (free : premises.FunctionExtensionalityFree) : (premises.rename rho).FunctionExtensionalityFree := by
  simpa only [FunctionExtensionalityFree, rename, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    HOL.ProofSyntax.functionExtensionalityFree_rename] using free

theorem weaken_free (premises : ComputationPremises original selection Δ) (type : HOL.Ty Base)
    (free : premises.FunctionExtensionalityFree) : (premises.weaken type).FunctionExtensionalityFree :=
  premises.rename_free HOL.Rename.weaken free

theorem prepend_free (premises : ComputationPremises original selection Δ) (formula : HOL.Formula Const Γ)
    (free : premises.FunctionExtensionalityFree) : (premises.prepend formula).FunctionExtensionalityFree := by
  simpa only [FunctionExtensionalityFree, prepend, HOL.ProofSyntax.prepend,
    HOL.ProofSyntax.functionExtensionalityFree_mono] using free
end ComputationPremises

def step_point (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector) (premises : ComputationPremises original selection Δ) :
    HOL.ProofSyntax Const Δ ((NativeVectorComputationRows.GuardedFamily.algebra original).stepBody
      (lifted original A predicate) (property original pairs witness selection A predicate) index head tail) := by
  let elements := lifted original A predicate
  let motive := property original pairs witness selection A predicate
  let a : HOL.Formula Const Γ := .app elements head
  let b := (NativeVectorComputationRows.GuardedFamily.algebra original).member elements index tail
  let c := HOL.PredicatePair.holds motive index tail
  refine .impI (.impI (.impI ?_))
  let current := ((premises.prepend a).prepend b).prepend c
  have headExists : HOL.ProofSyntax Const (c :: b :: a :: Δ) (existsValue [] (.app predicate head)) :=
    .andER (.impE (.eqPropEL (lifted_apply original A predicate head)) (.hyp 2))
  have tailExists : HOL.ProofSyntax Const (c :: b :: a :: Δ)
      (query original pairs witness selection A predicate index tail) :=
    .impE (.eqPropEL (property_apply original pairs witness selection A predicate index tail)) (.hyp 0)
  exact .impE (.eqPropER (property_apply original pairs witness selection A predicate
      (.app (HOL.weakenCtx Γ original.successor) index)
      ((NativeVectorComputationRows.GuardedFamily.algebra original).consValue index head tail)))
    (cons_query original pairs witness selection A predicate current.choice current.recursion index head tail
      current.head current.tail headExists tailExists)

theorem step_point_free (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector) (premises : ComputationPremises original selection Δ)
    (free : premises.FunctionExtensionalityFree) :
    (step_point original pairs witness selection A predicate index head tail premises).FunctionExtensionalityFree := by
  have a := premises.prepend_free (.app (lifted original A predicate) head) free
  have b := (premises.prepend _).prepend_free
    ((NativeVectorComputationRows.GuardedFamily.algebra original).member (lifted original A predicate) index tail) a
  have c := ((premises.prepend _).prepend _).prepend_free
    (HOL.PredicatePair.holds (property original pairs witness selection A predicate) index tail) b
  simp only [step_point, HOL.ProofSyntax.FunctionExtensionalityFree, property_apply_free,
    true_and]
  apply cons_query_free
  · exact c.1
  · exact c.2.1
  · exact c.2.2.1
  · exact c.2.2.2
  · exact ⟨lifted_apply_free original A predicate head, True.intro⟩
  · exact ⟨property_apply_free original pairs witness selection A predicate index tail, True.intro⟩

def step_condition (premises : ComputationPremises original selection Δ) :
    HOL.ProofSyntax Const Δ ((NativeVectorComputationRows.GuardedFamily.algebra original).stepCondition
      (lifted original A predicate) (property original pairs witness selection A predicate)) := by
  refine .allI (.allI (.allI ?_))
  let a := HOL.weaken (σ := original.vector) (HOL.weaken (σ := original.element) (HOL.weaken (σ := original.number) A))
  let p := HOL.weaken (σ := original.vector) (HOL.weaken (σ := original.element) (HOL.weaken (σ := original.number) predicate))
  let current := ((premises.weaken original.number).weaken original.element).weaken original.vector
  apply HOL.ProofSyntax.castIndices rfl ?_
    (step_point original pairs witness selection a p (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz) current)
  simp only [HOL.weaken, rename_lifted, rename_property, a, p]

theorem step_condition_free (premises : ComputationPremises original selection Δ)
    (free : premises.FunctionExtensionalityFree) :
    (step_condition original pairs witness selection A predicate premises).FunctionExtensionalityFree := by
  simp only [step_condition, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.functionExtensionalityFree_castIndices]
  exact step_point_free original pairs witness selection _ _ _ _ _ _
    (((premises.weaken_free original.number free) |> fun h =>
      (premises.weaken original.number).weaken_free original.element h) |> fun h =>
      ((premises.weaken original.number).weaken original.element).weaken_free original.vector h)

def produce (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector)
    (premises : ComputationPremises original selection Δ)
    (member : HOL.ProofSyntax Const Δ ((NativeVectorComputationRows.GuardedFamily.algebra original).member
      (lifted original A predicate) index value)) :
    HOL.ProofSyntax Const Δ (query original pairs witness selection A predicate index value) :=
  .impE (.eqPropEL (property_apply original pairs witness selection A predicate index value))
    ((NativeVectorComputationRows.GuardedFamily.algebra original).inductionProof
      (lifted original A predicate) (property original pairs witness selection A predicate) index value
      (.impE (.eqPropER (property_apply original pairs witness selection A predicate
        (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.nil)))
        (nil_query original pairs witness selection A predicate premises.choice premises.recursion))
      (step_condition original pairs witness selection A predicate premises) member)

theorem produce_free (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector)
    (premises : ComputationPremises original selection Δ)
    (member : HOL.ProofSyntax Const Δ ((NativeVectorComputationRows.GuardedFamily.algebra original).member
      (lifted original A predicate) index value))
    (premisesFree : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (produce original pairs witness selection A predicate index value premises member).FunctionExtensionalityFree := by
  simp only [produce, HOL.ProofSyntax.FunctionExtensionalityFree, property_apply_free, true_and]
  apply HOL.IndexedVectorPredicate.Signature.inductionProof_free
  · exact ⟨property_apply_free original pairs witness selection A predicate _ _,
      nil_query_free original pairs witness selection A predicate premises.choice premises.recursion
        premisesFree.1 premisesFree.2.1⟩
  · exact step_condition_free original pairs witness selection A predicate premises premisesFree
  · exact memberFree

#print axioms produce
#print axioms produce_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Existence
