import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSCorrespondence

/-!
# Finite GSOS rules modulo their independently authored firing denotation

The equivalence relation compares successful clauses with complete selected
premise assignments. Equality of their constructed natural laws is proved
equivalent to that relation. With finite action carriers the actual law
reconstruction supplies both inverse laws of the quotient equivalence.
Authored clause identifiers and firing receipts are outside this quotient.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

/-- Compare independently supplied clauses and their complete matching inputs. -/
def Equivalent (first second : Presentation S Actions) : Prop :=
  ∀ (X : S.Families) sort (operator : S.Operator sort) arguments action target,
    (∃ rule ∈ first sort operator action,
      ∃ input : Input rule.pattern X, Matches rule.pattern arguments input ∧ rule.output input = target) ↔
    ∃ rule ∈ second sort operator action,
      ∃ input : Input rule.pattern X, Matches rule.pattern arguments input ∧ rule.output input = target

theorem equivalent_iff_law_equal (first second : Presentation S Actions) :
    Equivalent first second ↔ Presentation.toLaw first = Presentation.toLaw second := by
  constructor
  · intro equivalent
    apply NatTrans.ext
    funext X base sort
    apply ConcreteCategory.hom_ext
    intro layer
    cases base
    rcases layer with ⟨operator, arguments⟩
    funext action
    apply Finset.ext
    intro target
    exact (Presentation.toLaw_denotes first X sort operator arguments action target).trans
      ((equivalent X sort operator arguments action target).trans
        (Presentation.toLaw_denotes second X sort operator arguments action target).symm)
  · intro same X sort operator arguments action target
    exact ((Presentation.toLaw_denotes first X sort operator arguments action target).symm.trans
      (by rw [same])).trans (Presentation.toLaw_denotes second X sort operator arguments action target)

def presentationSetoid (S : Signature.{u}) (Actions : S.Srt → Type u) :
    Setoid (Presentation S Actions) where
  r := Equivalent
  iseqv := ⟨fun _ _ _ _ _ _ _ => Iff.rfl,
    fun held X sort operator arguments action target => (held X sort operator arguments action target).symm,
    fun first second X sort operator arguments action target =>
      (first X sort operator arguments action target).trans (second X sort operator arguments action target)⟩

abbrev RuleQuotient (S : Signature.{u}) (Actions : S.Srt → Type u) :=
  Quotient (presentationSetoid S Actions)

def quotientLaw : RuleQuotient S Actions → Law S Actions :=
  Quotient.lift Presentation.toLaw (fun _ _ held => (equivalent_iff_law_equal _ _).mp held)

@[simp]
theorem quotientLaw_mk (presentation : Presentation S Actions) :
    quotientLaw (Quotient.mk (presentationSetoid S Actions) presentation) =
      Presentation.toLaw presentation := rfl

/-- Reconstructing finite clauses retains their complete denotation while
allowing redundant clause syntax and origin identifiers to be forgotten. -/
theorem presentation_roundtrip [∀ sort, Finite (Actions sort)] (presentation : Presentation S Actions) :
    Equivalent (Reconstruction.fromLaw (Presentation.toLaw presentation)) presentation :=
  (equivalent_iff_law_equal _ _).mpr (Reconstruction.law_roundtrip _)

def lawQuotient [∀ sort, Finite (Actions sort)] (law : Law S Actions) : RuleQuotient S Actions :=
  Quotient.mk _ (Reconstruction.fromLaw law)

theorem quotientLaw_lawQuotient [∀ sort, Finite (Actions sort)] (law : Law S Actions) :
    quotientLaw (lawQuotient law) = law := Reconstruction.law_roundtrip law

theorem lawQuotient_quotientLaw [∀ sort, Finite (Actions sort)] (rules : RuleQuotient S Actions) :
    lawQuotient (quotientLaw rules) = rules := by
  induction rules using Quotient.inductionOn with
  | _ presentation =>
      exact Quotient.sound (presentation_roundtrip presentation)

/-- Actual natural finite-per-action laws are classified by the independent
finite GSOS premise/target format under the stated finite-action boundary. -/
def ruleLawEquiv [∀ sort, Finite (Actions sort)] : RuleQuotient S Actions ≃ Law S Actions where
  toFun := quotientLaw
  invFun := lawQuotient
  left_inv := lawQuotient_quotientLaw
  right_inv := quotientLaw_lawQuotient

end Mettapedia.OSLF.FiniteBranching.Premises
