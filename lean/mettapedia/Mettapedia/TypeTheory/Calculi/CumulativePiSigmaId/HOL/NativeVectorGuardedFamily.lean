import Mettapedia.Logic.HOL.IndexedVectorPredicate
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorEncodedConstructor
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateContexts

/-!
# The constructed indexed guard in the original Vec reading

The guard uses the same zero, successor, nil and cons terms as the received
computation rows. Open element predicates and length indices remain arguments.
Adding the family and instantiated universe heads preserves all readings of
the earlier computation-only lexical table.

This does not interpret every universe-valued term or establish a typing
fundamental theorem for the complete source calculus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.GuardedFamily
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

def algebra (operations : Operations Base Const) : HOL.IndexedVectorPredicate.Signature Const where
  number := operations.number
  element := operations.element
  vector := operations.vector
  zero := operations.zero
  successor := operations.successor
  nil := operations.nil
  cons := operations.cons

variable (operations : Operations Base Const) {Γ Ξ : HOL.Ctx Base}

def familyAt (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number) :
    HOL.Term Const Γ (operations.vector ⇒ .prop) :=
  .lam ((algebra operations).member (HOL.weaken elements) (HOL.weaken index) (.var .vz))

def familyFor (elements : HOL.Term Const Γ operations.elementPredicate) :
    HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ .prop) :=
  .lam (familyAt operations (HOL.weaken elements) (.var .vz))

def familyCode : HOL.Term Const Γ (operations.elementPredicate ⇒ operations.number ⇒ operations.vector ⇒ .prop) :=
  .lam (familyFor operations (.var .vz))

@[simp] theorem subst_familyAt (substitution : HOL.Subst Const Γ Ξ)
    (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number) :
    HOL.subst substitution (familyAt operations elements index) =
      familyAt operations (HOL.subst substitution elements) (HOL.subst substitution index) := by
  simp [familyAt, algebra, HOL.subst, HOL.IndexedVectorPredicate.Signature.subst_member, HOL.subst_weaken, HOL.Subst.lift]

@[simp] theorem subst_familyFor (substitution : HOL.Subst Const Γ Ξ)
    (elements : HOL.Term Const Γ operations.elementPredicate) :
    HOL.subst substitution (familyFor operations elements) = familyFor operations (HOL.subst substitution elements) := by
  simp [familyFor, HOL.subst, subst_familyAt, HOL.subst_weaken, HOL.Subst.lift]

@[simp] theorem subst_familyCode (substitution : HOL.Subst Const Γ Ξ) :
    HOL.subst substitution (familyCode operations (Γ := Γ)) = familyCode operations (Γ := Ξ) := by
  simp [familyCode, HOL.subst, subst_familyFor, HOL.Subst.lift]

theorem weaken_familyCode : HOL.weakenCtx Γ (familyCode operations (Γ := [])) = familyCode operations (Γ := Γ) := by
  let empty : HOL.Subst Const [] Γ := fun index => nomatch index
  exact (HOL.subst_weakenCtx empty _).symm.trans (subst_familyCode operations empty)

variable {Δ : List (HOL.Formula Const Γ)}

def familyAt_apply (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number)
    (value : HOL.Term Const Γ operations.vector) :
    HOL.ProofSyntax Const Δ (.eq (.app (familyAt operations elements index) value)
      ((algebra operations).member elements index value)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (.beta value ((algebra operations).member (HOL.weaken elements) (HOL.weaken index) (.var .vz)))
  simp [familyAt, algebra, HOL.instantiate, HOL.IndexedVectorPredicate.Signature.subst_member, HOL.subst, HOL.Subst.single]

def familyFor_apply (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number) :
    HOL.ProofSyntax Const Δ (.eq (.app (familyFor operations elements) index) (familyAt operations elements index)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (.beta index (familyAt operations (HOL.weaken elements) (.var .vz)))
  simp [HOL.instantiate, subst_familyAt, HOL.subst, HOL.Subst.single]
  rfl

def family_apply (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number)
    (value : HOL.Term Const Γ operations.vector) :
    HOL.ProofSyntax Const Δ (.eq (.app (.app (.app (familyCode operations) elements) index) value)
      ((algebra operations).member elements index value)) := by
  have first : HOL.ProofSyntax Const Δ (.eq (.app (familyCode operations) elements) (familyFor operations elements)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta elements (familyFor operations (.var .vz)))
    simp [HOL.instantiate, subst_familyFor, HOL.subst, HOL.Subst.single]
    rfl
  exact .eqTrans (.eqApp value (.eqApp index first))
    (.eqTrans (.eqApp value (familyFor_apply operations elements index)) (familyAt_apply operations elements index value))

theorem family_apply_free (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number)
    (value : HOL.Term Const Γ operations.vector) :
    (family_apply (Δ := Δ) operations elements index value).FunctionExtensionalityFree := by
  simp [family_apply, familyFor_apply, familyAt_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

def membership (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number)
    (value : HOL.Term Const Γ operations.vector) : HOL.Formula Const Γ :=
  .app (.app (.app (familyCode operations) elements) index) value

def nil_apply (elements : HOL.Term Const Γ operations.elementPredicate) :
    HOL.ProofSyntax Const Δ (.eq (.app (HOL.weakenCtx Γ operations.nilCode) elements) (HOL.weakenCtx Γ operations.nil)) := by
  have code : HOL.weakenCtx Γ operations.nilCode = .lam (HOL.weaken (HOL.weakenCtx Γ operations.nil)) := by
    let empty : HOL.Subst Const [] Γ := fun index => nomatch index
    calc
      _ = HOL.subst empty operations.nilCode := (HOL.subst_weakenCtx empty _).symm
      _ = _ := by
        simp only [Operations.nilCode, HOL.subst, HOL.subst_weaken]
        exact congrArg HOL.Term.lam (congrArg HOL.weaken (HOL.subst_weakenCtx empty operations.nil))
  apply HOL.ProofSyntax.castIndices rfl ?_ (.beta elements (HOL.weaken (HOL.weakenCtx Γ operations.nil)))
  simp [code, HOL.instantiate_weaken]

def nil_member (elements : HOL.Term Const Γ operations.elementPredicate) :
    HOL.ProofSyntax Const Δ (membership operations elements (HOL.weakenCtx Γ operations.zero)
      (.app (HOL.weakenCtx Γ operations.nilCode) elements)) := by
  have raw : HOL.ProofSyntax Const Δ (membership operations elements (HOL.weakenCtx Γ operations.zero)
      (HOL.weakenCtx Γ operations.nil)) :=
    .impE (.eqPropER (family_apply operations elements (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.nil)))
      ((algebra operations).nil_member elements)
  exact .impE (.eqPropER (.eqAppArg (.app (.app (familyCode operations) elements) (HOL.weakenCtx Γ operations.zero))
    (nil_apply operations elements))) raw

def cons_member (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number)
    (head : HOL.Term Const Γ operations.element) (tail : HOL.Term Const Γ operations.vector)
    (headMember : HOL.ProofSyntax Const Δ (.app elements head))
    (tailMember : HOL.ProofSyntax Const Δ (membership operations elements index tail)) :
    HOL.ProofSyntax Const Δ (membership operations elements (.app (HOL.weakenCtx Γ operations.successor) index)
      (.app (.app (.app (.app (HOL.weakenCtx Γ operations.consCode) elements) index) head) tail)) := by
  have recursive := HOL.ProofSyntax.impE (.eqPropEL (family_apply operations elements index tail)) tailMember
  have constructed := (algebra operations).cons_member elements index head tail headMember recursive
  have raw : HOL.ProofSyntax Const Δ (membership operations elements (.app (HOL.weakenCtx Γ operations.successor) index)
      ((algebra operations).consValue index head tail)) :=
    .impE (.eqPropER (family_apply operations elements (.app (HOL.weakenCtx Γ operations.successor) index)
      ((algebra operations).consValue index head tail))) constructed
  exact .impE (.eqPropER (.eqAppArg
    (.app (.app (familyCode operations) elements) (.app (HOL.weakenCtx Γ operations.successor) index))
    (operations.cons_apply elements index head tail))) raw

theorem nil_member_free (elements : HOL.Term Const Γ operations.elementPredicate) :
    (nil_member (Δ := Δ) operations elements).FunctionExtensionalityFree := by
  simp [nil_member, nil_apply, HOL.ProofSyntax.FunctionExtensionalityFree, family_apply_free,
    HOL.IndexedVectorPredicate.Signature.nil_member_free]

theorem cons_member_free (elements : HOL.Term Const Γ operations.elementPredicate) (index : HOL.Term Const Γ operations.number)
    (head : HOL.Term Const Γ operations.element) (tail : HOL.Term Const Γ operations.vector)
    (headMember : HOL.ProofSyntax Const Δ (.app elements head))
    (tailMember : HOL.ProofSyntax Const Δ (membership operations elements index tail))
    (headFree : headMember.FunctionExtensionalityFree) (tailFree : tailMember.FunctionExtensionalityFree) :
    (cons_member operations elements index head tail headMember tailMember).FunctionExtensionalityFree := by
  simp [cons_member, Operations.cons_apply, HOL.ProofSyntax.FunctionExtensionalityFree, family_apply_free,
    HOL.IndexedVectorPredicate.Signature.cons_member_free, headFree, tailFree]

def elementHead := RussellTarski.substLevelsHead Programs.levels (.sort elementLevel)
def motiveHead := RussellTarski.substLevelsHead Programs.levels (.sort motiveLevel)

def lexical : AnnotatedPredicateReading.LexicalReading Tower.Head Base Const where
  constCode? name := if name = vecName then some ⟨_, familyCode operations⟩ else operations.lexicalReading.constCode? name
  headCode? head := if head = elementHead then
    some ⟨_, HOL.PredicateProducts.full operations.elementPredicate⟩
    else if head = motiveHead then
      some ⟨_, HOL.PredicateProducts.full (operations.result ⇒ .prop)⟩
    else none

theorem extends_computation : AnnotatedPredicateReading.LexicalMap operations.lexicalReading (lexical operations) (fun head => head) := by
  constructor
  · intro name type code found
    have distinct : name ≠ vecName := by
      intro same
      subst name
      simp [Operations.lexicalReading, vecName, natName, zeroName, succName, vnilName, vconsName, vecEliminateName] at found
    simpa only [lexical, if_neg distinct] using found
  · intro head type code found
    cases found
  · intro operator result code found
    cases found

theorem family_reads : AnnotatedPredicateReading.Reads (lexical operations) (Γ := Γ) (.const vecName)
    (familyCode operations) := by
  rw [← weaken_familyCode]
  exact .constant (by simp [lexical])

theorem original_rows_read (row : Row) :
    AnnotatedPredicateReading.Reads (lexical operations) (Γ := row.parameters operations)
      (liftTm (row.rawLeft operations)) (row.leftCode operations) ∧
    AnnotatedPredicateReading.Reads (lexical operations) (Γ := row.parameters operations)
      (liftTm (row.rawRight operations)) (row.rightCode operations) := by
  constructor
  · simpa only [CTm.mapHead_id] using (row.left_reads operations).mapLexical (extends_computation operations)
  · simpa only [CTm.mapHead_id] using (row.right_reads operations).mapLexical (extends_computation operations)

#print axioms subst_familyCode
#print axioms family_apply_free
#print axioms extends_computation
#print axioms original_rows_read
#print axioms nil_member_free
#print axioms cons_member_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.GuardedFamily
