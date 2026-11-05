import Mettapedia.Logic.HOL.SetComprehensionProofs
import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Retained membership transport and empty-set reasoning

These programs keep equality transport, subset specialization and the
weakening of closed set-law proofs explicit. They add no set axiom.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetMembershipProofs
open SetComprehensionProofs
open Mettapedia.Logic.HOL.Embedding
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
variable {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}

def valueCongr {first second : Term Const Γ ZFSetHenkinInterpretation.set}
    (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (equal : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (member core first bound) (member core second bound)) :=
  .eqApp bound (.eqAppArg (.const (core .member)) equal)

def boundCongr (point : Term Const Γ ZFSetHenkinInterpretation.set)
    {first second : Term Const Γ ZFSetHenkinInterpretation.set}
    (equal : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (member core point first) (member core point second)) :=
  .eqAppArg (.app (.const (core .member)) point) equal

def transportValue {first second : Term Const Γ ZFSetHenkinInterpretation.set}
    (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (equal : ProofSyntax Const Δ (.eq first second))
    (proof : ProofSyntax Const Δ (member core first bound)) :
    ProofSyntax Const Δ (member core second bound) :=
  .impE (.eqPropEL (valueCongr core bound equal)) proof

def transportBound (point : Term Const Γ ZFSetHenkinInterpretation.set)
    {first second : Term Const Γ ZFSetHenkinInterpretation.set}
    (equal : ProofSyntax Const Δ (.eq first second))
    (proof : ProofSyntax Const Δ (member core point first)) :
    ProofSyntax Const Δ (member core point second) :=
  .impE (.eqPropEL (boundCongr core point equal)) proof

def weakenLaw {added : Ty Unit} (law : ClosedFormula ZFSetHenkinInterpretation.Symbol)
    (proof : ProofSyntax Const Δ (lawAt core law)) :
    ProofSyntax Const (weakenHyps (σ := added) Δ) (lawAt (Γ := added :: Γ) core law) := by
  apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof proof)
  simp only [lawAt_eq_weakenCtx, weaken, HOL.rename_weakenCtx]

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (weaken term) = term := instantiate_weaken point term

def subsetElim (left right point : Term Const Γ ZFSetHenkinInterpretation.set)
    (inclusion : ProofSyntax Const Δ (included core left right))
    (member : ProofSyntax Const Δ (SetComprehensionProofs.member core point left)) :
    ProofSyntax Const Δ (SetComprehensionProofs.member core point right) := by
  have implication : ProofSyntax Const Δ (.imp
      (SetComprehensionProofs.member core point left)
      (SetComprehensionProofs.member core point right)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE point inclusion)
    simp only [instantiate, SetComprehensionProofs.member, HOL.subst,
      Subst.single, substituteWeak]
  exact .impE implication member

def emptyElim (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.emptyLaw)) :
    ProofSyntax Const Δ (.not (member core point (.const (core .empty)))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE point law)
  rfl

def emptyInPower (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (emptyLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.emptyLaw))
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw)) :
    ProofSyntax Const Δ (member core (.const (core .empty)) (power core bound)) := by
  apply ProofSyntax.impE (.andER (powerset core bound (.const (core .empty)) powerLaw))
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.botE
  exact .notE ((emptyElim core (.var .vz) (weakenLaw core _ emptyLaw)).prepend _) (.hyp 0)

def selfInPower (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw)) :
    ProofSyntax Const Δ (member core bound (power core bound)) :=
  .impE (.andER (powerset core bound bound powerLaw)) (.allI (.impI (.hyp 0)))

def emptyNePower (emptyLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.emptyLaw))
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw)) :
    ProofSyntax Const Δ (.not (.eq (.const (core .empty)) (power core (.const (core .empty))))) :=
  .notI (.notE ((emptyElim core (.const (core .empty)) emptyLaw).prepend _)
    (transportBound core (.const (core .empty)) (.eqSymm (.hyp 0))
      ((emptyInPowerEmpty core powerLaw).prepend _)))

theorem valueCongr_free {first second : Term Const Γ ZFSetHenkinInterpretation.set}
    (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (equal : ProofSyntax Const Δ (.eq first second)) :
    (valueCongr core bound equal).FunctionExtensionalityFree ↔ equal.FunctionExtensionalityFree := Iff.rfl

theorem transportValue_free {first second : Term Const Γ ZFSetHenkinInterpretation.set}
    (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (equal : ProofSyntax Const Δ (.eq first second))
    (proof : ProofSyntax Const Δ (member core first bound))
    (equalFree : equal.FunctionExtensionalityFree) (proofFree : proof.FunctionExtensionalityFree) :
    (transportValue core bound equal proof).FunctionExtensionalityFree := ⟨equalFree, proofFree⟩

theorem weakenLaw_free {added : Ty Unit} (law : ClosedFormula ZFSetHenkinInterpretation.Symbol)
    (proof : ProofSyntax Const Δ (lawAt core law)) (free : proof.FunctionExtensionalityFree) :
    (weakenLaw (added := added) core law proof).FunctionExtensionalityFree := by
  simpa [weakenLaw, PredicateFixedPoint.weakenProof] using free

theorem transportBound_free (point : Term Const Γ ZFSetHenkinInterpretation.set)
    {first second : Term Const Γ ZFSetHenkinInterpretation.set}
    (equal : ProofSyntax Const Δ (.eq first second))
    (proof : ProofSyntax Const Δ (member core point first))
    (equalFree : equal.FunctionExtensionalityFree) (proofFree : proof.FunctionExtensionalityFree) :
    (transportBound core point equal proof).FunctionExtensionalityFree := ⟨equalFree, proofFree⟩

theorem emptyElim_free (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.emptyLaw)) :
    (emptyElim core point law).FunctionExtensionalityFree ↔ law.FunctionExtensionalityFree := by
  simp [emptyElim, ProofSyntax.FunctionExtensionalityFree]

theorem emptyInPower_free (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (emptyLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.emptyLaw))
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (emptyFree : emptyLaw.FunctionExtensionalityFree) (powerFree : powerLaw.FunctionExtensionalityFree) :
    (emptyInPower core bound emptyLaw powerLaw).FunctionExtensionalityFree := by
  simp [emptyInPower, ProofSyntax.FunctionExtensionalityFree, powerset_free, emptyElim_free,
    weakenLaw_free, ProofSyntax.prepend, emptyFree, powerFree]

theorem selfInPower_free (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (powerFree : powerLaw.FunctionExtensionalityFree) :
    (selfInPower core bound powerLaw).FunctionExtensionalityFree := by
  simp [selfInPower, ProofSyntax.FunctionExtensionalityFree, powerset_free, powerFree]

theorem replacement_free (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (function : Term Const Γ ZFSetHenkinInterpretation.mapping)
    (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.replacementLaw)) :
    (replacement core bound function point law).FunctionExtensionalityFree ↔ law.FunctionExtensionalityFree := by
  simp [replacement, ProofSyntax.FunctionExtensionalityFree]

theorem imageIntro_free (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (function : Term Const Γ ZFSetHenkinInterpretation.mapping)
    (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.replacementLaw))
    (inBound : ProofSyntax Const Δ (member core point bound))
    (lawFree : law.FunctionExtensionalityFree) (boundFree : inBound.FunctionExtensionalityFree) :
    (imageIntro core bound function point law inBound).FunctionExtensionalityFree := by
  simp [imageIntro, ProofSyntax.FunctionExtensionalityFree, replacement_free, lawFree, boundFree]

theorem emptyNePower_free (emptyLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.emptyLaw))
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (emptyFree : emptyLaw.FunctionExtensionalityFree) (powerFree : powerLaw.FunctionExtensionalityFree) :
    (emptyNePower core emptyLaw powerLaw).FunctionExtensionalityFree := by
  simp [emptyNePower, ProofSyntax.FunctionExtensionalityFree, emptyElim_free,
    transportBound, boundCongr, ProofSyntax.prepend, emptyInPowerEmpty_free, emptyFree, powerFree]

end Mettapedia.Logic.HOL.SetMembershipProofs
