import Mettapedia.Logic.HOL.SuccessorOrderTransforms
import Mettapedia.Logic.HOL.FiniteConstructorEncodingControls

/-!
# Positive successor-closure computations and premise separation

The Boolean examples are countermodels to dropping arithmetic premises,
not representations of natural numbers. All displayed object proofs retain
their inferences; semantic soundness is used only to refute impossible proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder.Controls

open FiniteConstructorEncoding.Controls

def identitySuccessor : ClosedTerm Constants (.prop ⇒ .prop) := .lam (.var .vz)
def constantSuccessor : ClosedTerm Constants (.prop ⇒ .prop) := .lam .top

def collapsedZeroSelfLess : ProofSyntax Constants []
    (.app (.app (less identitySuccessor) .top) .top) :=
  .impE (.eqPropEL (.eqAppArg (.app (less identitySuccessor) .top) (.beta .top (.var .vz))))
    (lessNext identitySuccessor .top)

theorem collapsedZeroSelfLess_free : collapsedZeroSelfLess.FunctionExtensionalityFree := by
  exact ⟨trivial, lessNext_free _ _⟩

private theorem constantSuccessor_weaken (context : Ctx Empty) :
    weakenCtx context constantSuccessor = (.lam (.top : Formula Constants (.prop :: context))) := by
  induction context with
  | nil => rfl
  | cons type context ih =>
    simp only [weakenCtx_cons, ih, weaken, HOL.rename]

def constantSuccessorTrue {Γ : Ctx Empty} {assumptions : List (Formula Constants Γ)}
    (point : Term Constants Γ .prop) :
    ProofSyntax Constants assumptions (.app (weakenCtx Γ constantSuccessor) point) := by
  apply ProofSyntax.impE (.eqPropER ?_) .topI
  apply ProofSyntax.castIndices rfl ?_ (.beta point .top)
  rw [constantSuccessor_weaken]
  rfl

theorem constantSuccessorTrue_free {Γ : Ctx Empty} {assumptions : List (Formula Constants Γ)}
    (point : Term Constants Γ .prop) :
    (constantSuccessorTrue (assumptions := assumptions) point).FunctionExtensionalityFree := by
  unfold constantSuccessorTrue
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · trivial

def identityAtSuccessor {Γ : Ctx Empty} {assumptions : List (Formula Constants Γ)}
    (point : Term Constants Γ .prop) :
    ProofSyntax Constants assumptions
      (.app (.lam (.var .vz)) (.app (weakenCtx Γ constantSuccessor) point)) :=
  .impE (.eqPropER (.beta (.app (weakenCtx Γ constantSuccessor) point) (.var .vz)))
    (constantSuccessorTrue point)

theorem identityAtSuccessor_free {Γ : Ctx Empty} {assumptions : List (Formula Constants Γ)}
    (point : Term Constants Γ .prop) :
    (identityAtSuccessor (assumptions := assumptions) point).FunctionExtensionalityFree := by
  exact ⟨trivial, constantSuccessorTrue_free _⟩

def constantNotBelowFalse : ProofSyntax Constants []
    (.not (.app (.app (less constantSuccessor) .top) .bot)) := by
  apply ProofSyntax.notI
  let predicate : ClosedTerm Constants (.prop ⇒ .prop) := .lam (.var .vz)
  have closed : ProofSyntax Constants
      [.app (.app (less constantSuccessor) .top) .bot] (successorClosed constantSuccessor predicate) :=
    .allI (.impI (identityAtSuccessor (.var .vz)))
  have atFalse := lessEliminate constantSuccessor .top .bot predicate (.hyp 0)
    (identityAtSuccessor .top) closed
  exact .impE (.eqPropEL (.beta .bot (.var .vz))) atFalse

theorem constantNotBelowFalse_free : constantNotBelowFalse.FunctionExtensionalityFree := by
  unfold constantNotBelowFalse
  constructor
  · trivial
  · apply lessEliminate_free
    · trivial
    · exact identityAtSuccessor_free _
    · exact identityAtSuccessor_free _

def equalSuccessorsLess : ProofSyntax Constants []
    (.app (.app (less constantSuccessor) (.app constantSuccessor .top))
      (.app constantSuccessor .bot)) := by
  have closedSelf : ProofSyntax Constants [] (.app (.app (less constantSuccessor) .top) .top) :=
    .impE (.eqPropEL (.eqAppArg (.app (less constantSuccessor) .top) (.beta .top .top)))
      (lessNext constantSuccessor .top)
  have heads : ProofSyntax Constants [] (.eq
      (.app (.app (less constantSuccessor) (.app constantSuccessor .top)) (.app constantSuccessor .bot))
      (.app (.app (less constantSuccessor) .top) .top)) :=
    .eqTrans (.eqApp (.app constantSuccessor .bot) (.eqAppArg (less constantSuccessor) (.beta .top .top)))
      (.eqAppArg (.app (less constantSuccessor) .top) (.beta .bot .top))
  exact .impE (.eqPropER heads) closedSelf

theorem equalSuccessorsLess_free : equalSuccessorsLess.FunctionExtensionalityFree := by
  unfold equalSuccessorsLess
  exact ⟨⟨trivial, trivial⟩, trivial, lessNext_free _ _⟩

private theorem noClosedFalse : ¬ Nonempty (ProofSyntax Constants (Γ := []) [] .bot) := by
  rintro ⟨proof⟩
  have impossible := Soundness.extTheorem_sound proof.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact impossible

theorem separation_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Constants [] (NaturalNumeralProofs.separation (.top : ClosedFormula Constants) identitySuccessor)) := by
  rintro ⟨separate⟩
  exact noClosedFalse ⟨lessZeroRefute identitySuccessor .top .top separate collapsedZeroSelfLess⟩

theorem injectivity_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Constants [] (NaturalNumeralProofs.injectivity constantSuccessor)) := by
  rintro ⟨injective⟩
  exact noClosedFalse ⟨.notE constantNotBelowFalse
    (lessSuccessorCancel constantSuccessor .top .bot injective equalSuccessorsLess)⟩

def closedSum : ProofSyntax Constants []
    (.app (.app (.app (sum .bot constantSuccessor) .bot) (.app constantSuccessor .bot))
      (.app constantSuccessor .bot)) :=
  sumStep constantSuccessor .bot .bot .bot .bot (sumZero constantSuccessor .bot .bot)

def closedSumReflection : ProofSyntax Constants []
    (.eq (.app constantSuccessor .bot) (.app constantSuccessor .bot)) :=
  sumZeroReflect constantSuccessor .bot (.app constantSuccessor .bot) (.app constantSuccessor .bot) closedSum

theorem closedSumReflection_free : closedSumReflection.FunctionExtensionalityFree := by
  apply sumZeroReflect_free
  apply sumStep_free
  exact sumZero_free _ _ _

def closedSumPredecessor : ProofSyntax Constants []
    (predecessorSum constantSuccessor .bot .bot .bot (.app constantSuccessor .bot)) :=
  sumLeftSuccessor constantSuccessor .bot .bot .bot (.app constantSuccessor .bot)
    (sumZero constantSuccessor .bot (.app constantSuccessor .bot))

theorem closedSumPredecessor_free : closedSumPredecessor.FunctionExtensionalityFree := by
  apply sumLeftSuccessor_free
  exact sumZero_free _ _ _

#print axioms collapsedZeroSelfLess_free
#print axioms constantNotBelowFalse_free
#print axioms equalSuccessorsLess_free
#print axioms separation_cannot_be_dropped
#print axioms injectivity_cannot_be_dropped
#print axioms closedSumReflection_free
#print axioms closedSumPredecessor_free

end Mettapedia.Logic.HOL.SuccessorOrder.Controls
