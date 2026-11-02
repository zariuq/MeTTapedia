import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateStructuralProofs

/-!
# Packing and recovering evidence for the actual All computation

The nil witness is the actual reflexivity combinator applied to zero. The
cons witness packs head and recursive evidence. Decoding retains reconstruction
and recovers both guards, using the same open tail and predecessor index.
Recursor and pair-projection premises remain separate retained proof inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Evidence

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Reading
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Computation
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {evidence : HOL.Ty Base}
    (original : NativeVectorComputationRows.Operations Base Const)
    (pairs : HOL.PredicateSigma.Operations Const evidence) (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ (evidence ⇒ .prop))))
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}

theorem fullCode_eq (type : HOL.Ty Base) :
    fullCode (Const := Const) (Γ := Γ) type = HOL.PredicateProducts.full type := by
  let images : HOL.Subst Const [] Γ := fun index => nomatch index
  exact (HOL.subst_weakenCtx images (HOL.PredicateProducts.full type)).symm.trans
    (HOL.PredicateProducts.subst_full images type)

def full_member {type : HOL.Ty Base} (value : HOL.Term Const Γ type) :
    HOL.ProofSyntax Const Δ (.app (fullCode type) value) :=
  HOL.ProofSyntax.castIndices rfl (congrArg (fun predicate => HOL.Term.app predicate value) (fullCode_eq type)).symm
    (.impE (.eqPropER (.beta value .top)) .topI)

theorem full_member_free {type : HOL.Ty Base} (value : HOL.Term Const Γ type) :
    (full_member (Δ := Δ) value).FunctionExtensionalityFree := by
  simp [full_member, HOL.ProofSyntax.FunctionExtensionalityFree]

variable (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))

def nil_value : HOL.ProofSyntax Const Δ (.app
    (allCode original pairs witness selection A predicate (HOL.weakenCtx Γ original.zero)
      (.app (HOL.weakenCtx Γ (operations original selection).nilCode) A))
    (.app (HOL.weakenCtx Γ (StructuralProfile.reflexivityCode witness original.number))
      (HOL.weakenCtx Γ original.zero))) :=
  .impE (.eqPropER (.eqAppArg _ (StructuralProfile.reflexivity_apply witness (HOL.weakenCtx Γ original.zero))))
    (.impE (.eqPropER (.eqApp (HOL.weakenCtx Γ witness)
      (nil_guard original pairs witness selection A predicate choice recursion)))
      (StructuralProfile.identity_introduce witness (fullCode original.number) _ _
        (full_member _) (full_member _) (.eqRefl _)))

theorem nil_value_free (choiceFree : choice.FunctionExtensionalityFree)
    (recursionFree : recursion.FunctionExtensionalityFree) :
    (nil_value original pairs witness selection A predicate choice recursion).FunctionExtensionalityFree := by
  simp [nil_value, HOL.ProofSyntax.FunctionExtensionalityFree, StructuralProfile.reflexivity_apply_free,
    nil_guard_free, StructuralProfile.identity_introduce_free, full_member_free, choiceFree, recursionFree]

def nil_decode (point : HOL.Term Const Γ evidence)
    (member : HOL.ProofSyntax Const Δ (.app
      (allCode original pairs witness selection A predicate (HOL.weakenCtx Γ original.zero)
        (.app (HOL.weakenCtx Γ (operations original selection).nilCode) A)) point)) :
    HOL.ProofSyntax Const Δ (.eq point (HOL.weakenCtx Γ witness)) :=
  .andEL (.andER (.andER (StructuralProfile.identity_eliminate witness (fullCode original.number) _ _ point
    (.impE (.eqPropEL (.eqApp point (nil_guard original pairs witness selection A predicate choice recursion))) member))))

def family_beta (recursive : HOL.Term Const Γ (evidence ⇒ .prop))
    (headEvidence tailEvidence : HOL.Term Const Γ evidence) :
    HOL.ProofSyntax Const Δ (.eq
      (HOL.PredicateSigma.familyAt (.lam (HOL.weaken recursive)) headEvidence tailEvidence)
      (.app recursive tailEvidence)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (.eqApp tailEvidence (.beta headEvidence (HOL.weaken recursive)))
  simp only [HOL.PredicateSigma.familyAt, HOL.instantiate_weaken]

theorem family_beta_free (recursive : HOL.Term Const Γ (evidence ⇒ .prop))
    (headEvidence tailEvidence : HOL.Term Const Γ evidence) :
    (family_beta (Δ := Δ) recursive headEvidence tailEvidence).FunctionExtensionalityFree := by
  simp [family_beta, HOL.ProofSyntax.FunctionExtensionalityFree]

variable (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw)

def cons_value (headEvidence tailEvidence : HOL.Term Const Γ evidence)
    (headMember : HOL.ProofSyntax Const Δ (.app (.app predicate head) headEvidence))
    (tailMember : HOL.ProofSyntax Const Δ
      (.app (allCode original pairs witness selection A predicate index tail) tailEvidence)) :
    HOL.ProofSyntax Const Δ (.app
      (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
        (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail))
      (HOL.PredicateSigma.pair pairs headEvidence tailEvidence)) :=
  .impE (.eqPropER (.eqApp (HOL.PredicateSigma.pair pairs headEvidence tailEvidence)
    (cons_guard original pairs witness selection A predicate index head tail choice recursion headLaw tailLaw)))
    (HOL.PredicateSigma.introduce pairs (.app predicate head)
      (.lam (HOL.weaken (allCode original pairs witness selection A predicate index tail)))
      headEvidence tailEvidence headMember
      (.impE (.eqPropER (family_beta _ headEvidence tailEvidence)) tailMember))

def decoded (point : HOL.Term Const Γ evidence) : HOL.Formula Const Γ :=
  .and (.eq (HOL.PredicateSigma.pair pairs (HOL.PredicateSigma.first pairs point)
      (HOL.PredicateSigma.second pairs point)) point)
    (.and (.app (.app predicate head) (HOL.PredicateSigma.first pairs point))
      (.app (allCode original pairs witness selection A predicate index tail) (HOL.PredicateSigma.second pairs point)))

def cons_decode (point : HOL.Term Const Γ evidence)
    (firstLaw : HOL.ProofSyntax Const Δ (HOL.weakenCtx Γ (HOL.PredicateSigma.firstLaw pairs)))
    (secondLaw : HOL.ProofSyntax Const Δ (HOL.weakenCtx Γ (HOL.PredicateSigma.secondLaw pairs)))
    (member : HOL.ProofSyntax Const Δ (.app
      (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
        (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail)) point)) :
    HOL.ProofSyntax Const Δ (decoded original pairs witness selection A predicate index head tail point) := by
  let found := HOL.PredicateSigma.projection pairs (.app predicate head)
    (.lam (HOL.weaken (allCode original pairs witness selection A predicate index tail))) point firstLaw secondLaw
    (.impE (.eqPropEL (.eqApp point
      (cons_guard original pairs witness selection A predicate index head tail choice recursion headLaw tailLaw))) member)
  exact .andI (.andEL found) (.andI (.andEL (.andER found))
    (.impE (.eqPropEL (family_beta _ (HOL.PredicateSigma.first pairs point) (HOL.PredicateSigma.second pairs point)))
      (.andER (.andER found))))

theorem cons_value_free (headEvidence tailEvidence : HOL.Term Const Γ evidence)
    (headMember : HOL.ProofSyntax Const Δ (.app (.app predicate head) headEvidence))
    (tailMember : HOL.ProofSyntax Const Δ
      (.app (allCode original pairs witness selection A predicate index tail) tailEvidence))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headLawFree : headLaw.FunctionExtensionalityFree) (tailLawFree : tailLaw.FunctionExtensionalityFree)
    (headFree : headMember.FunctionExtensionalityFree) (tailFree : tailMember.FunctionExtensionalityFree) :
    (cons_value original pairs witness selection A predicate choice recursion index head tail headLaw tailLaw
      headEvidence tailEvidence headMember tailMember).FunctionExtensionalityFree := by
  simp [cons_value, HOL.ProofSyntax.FunctionExtensionalityFree, cons_guard_free,
    HOL.PredicateSigma.introduce_free, family_beta_free, choiceFree, recursionFree, headLawFree, tailLawFree, headFree, tailFree]

theorem cons_decode_free (point : HOL.Term Const Γ evidence)
    (firstLaw : HOL.ProofSyntax Const Δ (HOL.weakenCtx Γ (HOL.PredicateSigma.firstLaw pairs)))
    (secondLaw : HOL.ProofSyntax Const Δ (HOL.weakenCtx Γ (HOL.PredicateSigma.secondLaw pairs)))
    (member : HOL.ProofSyntax Const Δ (.app
      (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
        (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail)) point))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headLawFree : headLaw.FunctionExtensionalityFree) (tailLawFree : tailLaw.FunctionExtensionalityFree)
    (firstFree : firstLaw.FunctionExtensionalityFree) (secondFree : secondLaw.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (cons_decode original pairs witness selection A predicate choice recursion index head tail headLaw tailLaw
      point firstLaw secondLaw member).FunctionExtensionalityFree := by
  simp [cons_decode, HOL.ProofSyntax.FunctionExtensionalityFree, HOL.PredicateSigma.projection_free,
    cons_guard_free, family_beta_free, choiceFree, recursionFree, headLawFree, tailLawFree, firstFree, secondFree, memberFree]

theorem nil_source_value_reads [DecidableEq Base]
    (elementLevel resultLevel : Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) :
    Reads (lexical original pairs witness selection elementLevel resultLevel)
      (Γ := Γ) (.refl (.const NativeNaturalVectorFamilies.zeroName))
      (.app (HOL.weakenCtx Γ (StructuralProfile.reflexivityCode witness original.number))
        (HOL.weakenCtx Γ original.zero)) :=
  .reflexivity rfl (zero_reads original pairs witness selection elementLevel resultLevel)

#print axioms nil_value
#print axioms cons_value
#print axioms cons_decode

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Evidence
