import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ProofRelevantSubstitutionCoherence
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticJudgmentalPi

/-!
# Substitution coherence for retained structural computation

The canonical retained lift of a proposition-valued root computation is
functorial under simultaneous substitution.  This follows from the syntax
substitution laws together with proof irrelevance in each lifted root fibre.

The result is intentionally generic in the hosted presentation.  Richer
authored receipt types are not silently covered by this theorem: they must
supply their own `SubstitutionCoherent` capability when their proof data has
observable structure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace SyntacticJudgmentalPi

open Declaration
open ProofRelevantStructuralComputation
open Mettapedia.TypeTheory.JudgmentalEquality

/-- Lifted proofs in propositionally equal fibres are heterogeneously equal.
This is the precise proof-irrelevant step used by the canonical retained
root; it is not available for arbitrary informative receipt types. -/
private theorem plift_heq_of_prop_eq {left right : Prop}
    (fibreEquality : left = right) (first : PLift left)
    (second : PLift right) : HEq first second := by
  cases fibreEquality
  exact heq_of_eq (Subsingleton.elim _ _)

/-- The canonical proof-retaining lift of any proposition-valued root relation
has coherent identity and composite substitution actions. -/
def RetainedRoot.ofRulesSubstitutionCoherent
    {Head : Type} (rules : Rules Head) :
    (RetainedRoot.ofRules rules).computation.SubstitutionCoherent where
  substitute_ids := by
    intro n left right evidence
    change HEq (PLift.up _) evidence
    exact plift_heq_of_prop_eq (by simp) _ _
  substitute_comp := by
    intro n m k later earlier left right evidence
    change HEq (PLift.up _) (PLift.up _)
    exact plift_heq_of_prop_eq (by simp only [subst_comp]) _ _

/-! ## Structural receipts inherit root coherence -/

namespace StructuralStepReceipt

private theorem liftSub_comp_function
    {Head : Type} {n m k : Nat}
    (later : Sub Head m k) (earlier : Sub Head n m) :
    (fun index => subst (liftSub later) (liftSub earlier index)) =
      liftSub (fun index => subst later (earlier index)) :=
  funext (liftSub_comp_apply later earlier)

private theorem betaPi_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {body body' : Tm Head (n + 1)}
    {argument argument' : Tm Head n}
    (bodyEquality : HEq body body')
    (argumentEquality : HEq argument argument') :
    HEq
      (StructuralStepReceipt.betaPi
        (computation := computation) (headEq := headEq) body argument)
      (StructuralStepReceipt.betaPi
        (computation := computation) (headEq := headEq) body' argument') := by
  cases eq_of_heq bodyEquality
  cases eq_of_heq argumentEquality
  rfl

private theorem betaSigmaFst_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {first second first' second' : Tm Head n}
    (firstEquality : HEq first first')
    (secondEquality : HEq second second') :
    HEq
      (StructuralStepReceipt.betaSigmaFst
        (computation := computation) (headEq := headEq) first second)
      (StructuralStepReceipt.betaSigmaFst
        (computation := computation) (headEq := headEq) first' second') := by
  cases eq_of_heq firstEquality
  cases eq_of_heq secondEquality
  rfl

private theorem betaSigmaSnd_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {first second first' second' : Tm Head n}
    (firstEquality : HEq first first')
    (secondEquality : HEq second second') :
    HEq
      (StructuralStepReceipt.betaSigmaSnd
        (computation := computation) (headEq := headEq) first second)
      (StructuralStepReceipt.betaSigmaSnd
        (computation := computation) (headEq := headEq) first' second') := by
  cases eq_of_heq firstEquality
  cases eq_of_heq secondEquality
  rfl

private theorem root_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {left right left' right' : Tm Head n}
    {evidence : computation.Evidence left right}
    {evidence' : computation.Evidence left' right'}
    (leftEquality : HEq left left') (rightEquality : HEq right right')
    (evidenceEquality : HEq evidence evidence') :
    HEq
      (StructuralStepReceipt.root (headEq := headEq) evidence)
      (StructuralStepReceipt.root (headEq := headEq) evidence') := by
  cases eq_of_heq leftEquality
  cases eq_of_heq rightEquality
  cases eq_of_heq evidenceEquality
  rfl

private theorem congLam_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {body body' nextBody nextBody' : Tm Head (n + 1)}
    {receipt : StructuralStepReceipt computation headEq body body'}
    {nextReceipt : StructuralStepReceipt computation headEq nextBody nextBody'}
    (bodyEquality : HEq body nextBody)
    (bodyPrimeEquality : HEq body' nextBody')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congLam receipt)
      (StructuralStepReceipt.congLam nextReceipt) := by
  cases eq_of_heq bodyEquality
  cases eq_of_heq bodyPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congPiDom_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {domain domain' nextDomain nextDomain' : Tm Head n}
    {codomain nextCodomain : Tm Head (n + 1)}
    {receipt : StructuralStepReceipt computation headEq domain domain'}
    {nextReceipt : StructuralStepReceipt computation headEq
      nextDomain nextDomain'}
    (domainEquality : HEq domain nextDomain)
    (domainPrimeEquality : HEq domain' nextDomain')
    (codomainEquality : HEq codomain nextCodomain)
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congPiDom
      (codomain := codomain) receipt)
      (StructuralStepReceipt.congPiDom
        (codomain := nextCodomain) nextReceipt) := by
  cases eq_of_heq domainEquality
  cases eq_of_heq domainPrimeEquality
  cases eq_of_heq codomainEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congPiCod_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {domain nextDomain : Tm Head n}
    {codomain codomain' nextCodomain nextCodomain' : Tm Head (n + 1)}
    {receipt : StructuralStepReceipt computation headEq codomain codomain'}
    {nextReceipt : StructuralStepReceipt computation headEq
      nextCodomain nextCodomain'}
    (domainEquality : HEq domain nextDomain)
    (codomainEquality : HEq codomain nextCodomain)
    (codomainPrimeEquality : HEq codomain' nextCodomain')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congPiCod
      (domain := domain) receipt)
      (StructuralStepReceipt.congPiCod
        (domain := nextDomain) nextReceipt) := by
  cases eq_of_heq domainEquality
  cases eq_of_heq codomainEquality
  cases eq_of_heq codomainPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congSigmaDom_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {domain domain' nextDomain nextDomain' : Tm Head n}
    {codomain nextCodomain : Tm Head (n + 1)}
    {receipt : StructuralStepReceipt computation headEq domain domain'}
    {nextReceipt : StructuralStepReceipt computation headEq
      nextDomain nextDomain'}
    (domainEquality : HEq domain nextDomain)
    (domainPrimeEquality : HEq domain' nextDomain')
    (codomainEquality : HEq codomain nextCodomain)
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congSigmaDom
      (codomain := codomain) receipt)
      (StructuralStepReceipt.congSigmaDom
        (codomain := nextCodomain) nextReceipt) := by
  cases eq_of_heq domainEquality
  cases eq_of_heq domainPrimeEquality
  cases eq_of_heq codomainEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congSigmaCod_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {domain nextDomain : Tm Head n}
    {codomain codomain' nextCodomain nextCodomain' : Tm Head (n + 1)}
    {receipt : StructuralStepReceipt computation headEq codomain codomain'}
    {nextReceipt : StructuralStepReceipt computation headEq
      nextCodomain nextCodomain'}
    (domainEquality : HEq domain nextDomain)
    (codomainEquality : HEq codomain nextCodomain)
    (codomainPrimeEquality : HEq codomain' nextCodomain')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congSigmaCod
      (domain := domain) receipt)
      (StructuralStepReceipt.congSigmaCod
        (domain := nextDomain) nextReceipt) := by
  cases eq_of_heq domainEquality
  cases eq_of_heq codomainEquality
  cases eq_of_heq codomainPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congIdTy_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {type type' nextType nextType' left right nextLeft nextRight : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq type type'}
    {nextReceipt : StructuralStepReceipt computation headEq nextType nextType'}
    (typeEquality : HEq type nextType)
    (typePrimeEquality : HEq type' nextType')
    (leftEquality : HEq left nextLeft) (rightEquality : HEq right nextRight)
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congIdTy
      (left := left) (right := right) receipt)
      (StructuralStepReceipt.congIdTy
        (left := nextLeft) (right := nextRight) nextReceipt) := by
  cases eq_of_heq typeEquality
  cases eq_of_heq typePrimeEquality
  cases eq_of_heq leftEquality
  cases eq_of_heq rightEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congIdLeft_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {type nextType left left' nextLeft nextLeft' right nextRight : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq left left'}
    {nextReceipt : StructuralStepReceipt computation headEq nextLeft nextLeft'}
    (typeEquality : HEq type nextType)
    (leftEquality : HEq left nextLeft)
    (leftPrimeEquality : HEq left' nextLeft')
    (rightEquality : HEq right nextRight)
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congIdLeft
      (type := type) (right := right) receipt)
      (StructuralStepReceipt.congIdLeft
        (type := nextType) (right := nextRight) nextReceipt) := by
  cases eq_of_heq typeEquality
  cases eq_of_heq leftEquality
  cases eq_of_heq leftPrimeEquality
  cases eq_of_heq rightEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congIdRight_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {type nextType left nextLeft right right' nextRight nextRight' : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq right right'}
    {nextReceipt : StructuralStepReceipt computation headEq nextRight nextRight'}
    (typeEquality : HEq type nextType) (leftEquality : HEq left nextLeft)
    (rightEquality : HEq right nextRight)
    (rightPrimeEquality : HEq right' nextRight')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congIdRight
      (type := type) (left := left) receipt)
      (StructuralStepReceipt.congIdRight
        (type := nextType) (left := nextLeft) nextReceipt) := by
  cases eq_of_heq typeEquality
  cases eq_of_heq leftEquality
  cases eq_of_heq rightEquality
  cases eq_of_heq rightPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congAppFun_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {function function' nextFunction nextFunction' argument nextArgument : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq function function'}
    {nextReceipt : StructuralStepReceipt computation headEq
      nextFunction nextFunction'}
    (functionEquality : HEq function nextFunction)
    (functionPrimeEquality : HEq function' nextFunction')
    (argumentEquality : HEq argument nextArgument)
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congAppFun
      (argument := argument) receipt)
      (StructuralStepReceipt.congAppFun
        (argument := nextArgument) nextReceipt) := by
  cases eq_of_heq functionEquality
  cases eq_of_heq functionPrimeEquality
  cases eq_of_heq argumentEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congAppArg_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {function nextFunction argument argument' nextArgument nextArgument' : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq argument argument'}
    {nextReceipt : StructuralStepReceipt computation headEq
      nextArgument nextArgument'}
    (functionEquality : HEq function nextFunction)
    (argumentEquality : HEq argument nextArgument)
    (argumentPrimeEquality : HEq argument' nextArgument')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congAppArg
      (function := function) receipt)
      (StructuralStepReceipt.congAppArg
        (function := nextFunction) nextReceipt) := by
  cases eq_of_heq functionEquality
  cases eq_of_heq argumentEquality
  cases eq_of_heq argumentPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congPairFst_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {first first' nextFirst nextFirst' second nextSecond : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq first first'}
    {nextReceipt : StructuralStepReceipt computation headEq nextFirst nextFirst'}
    (firstEquality : HEq first nextFirst)
    (firstPrimeEquality : HEq first' nextFirst')
    (secondEquality : HEq second nextSecond)
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congPairFst
      (second := second) receipt)
      (StructuralStepReceipt.congPairFst
        (second := nextSecond) nextReceipt) := by
  cases eq_of_heq firstEquality
  cases eq_of_heq firstPrimeEquality
  cases eq_of_heq secondEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congPairSnd_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {first nextFirst second second' nextSecond nextSecond' : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq second second'}
    {nextReceipt : StructuralStepReceipt computation headEq nextSecond nextSecond'}
    (firstEquality : HEq first nextFirst)
    (secondEquality : HEq second nextSecond)
    (secondPrimeEquality : HEq second' nextSecond')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congPairSnd
      (first := first) receipt)
      (StructuralStepReceipt.congPairSnd
        (first := nextFirst) nextReceipt) := by
  cases eq_of_heq firstEquality
  cases eq_of_heq secondEquality
  cases eq_of_heq secondPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congFst_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {pair pair' nextPair nextPair' : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq pair pair'}
    {nextReceipt : StructuralStepReceipt computation headEq nextPair nextPair'}
    (pairEquality : HEq pair nextPair)
    (pairPrimeEquality : HEq pair' nextPair')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congFst receipt)
      (StructuralStepReceipt.congFst nextReceipt) := by
  cases eq_of_heq pairEquality
  cases eq_of_heq pairPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congSnd_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {pair pair' nextPair nextPair' : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq pair pair'}
    {nextReceipt : StructuralStepReceipt computation headEq nextPair nextPair'}
    (pairEquality : HEq pair nextPair)
    (pairPrimeEquality : HEq pair' nextPair')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congSnd receipt)
      (StructuralStepReceipt.congSnd nextReceipt) := by
  cases eq_of_heq pairEquality
  cases eq_of_heq pairPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem congRefl_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {term term' nextTerm nextTerm' : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq term term'}
    {nextReceipt : StructuralStepReceipt computation headEq nextTerm nextTerm'}
    (termEquality : HEq term nextTerm)
    (termPrimeEquality : HEq term' nextTerm')
    (receiptEquality : HEq receipt nextReceipt) :
    HEq (StructuralStepReceipt.congRefl receipt)
      (StructuralStepReceipt.congRefl nextReceipt) := by
  cases eq_of_heq termEquality
  cases eq_of_heq termPrimeEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem substitute_heq_of_eq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n m : Nat}
    {left right : Tm Head n}
    (receipt : StructuralStepReceipt computation headEq left right)
    {first second : Sub Head n m} (equality : first = second) :
    HEq (receipt.substitute first) (receipt.substitute second) := by
  cases equality
  rfl

/-- The beta receipt produced by substitution is the canonical beta receipt,
up to the endpoint transport required by `subst_inst0`. -/
private theorem betaPi_substitute_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n m : Nat}
    (body : Tm Head (n + 1)) (argument : Tm Head n)
    (substitution : Sub Head n m) :
    HEq
      ((StructuralStepReceipt.betaPi
        (computation := computation) (headEq := headEq)
        body argument).substitute substitution)
      (StructuralStepReceipt.betaPi
        (computation := computation) (headEq := headEq)
        (subst (liftSub substitution) body) (subst substitution argument)) := by
  unfold StructuralStepReceipt.substitute
  exact cast_heq _ _

private theorem substitute_congr_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n m : Nat}
    {left right left' right' : Tm Head n}
    (leftEquality : left = left') (rightEquality : right = right')
    {receipt : StructuralStepReceipt computation headEq left right}
    {receipt' : StructuralStepReceipt computation headEq left' right'}
    (receiptEquality : HEq receipt receipt')
    (substitution : Sub Head n m) :
    HEq (receipt.substitute substitution)
      (receipt'.substitute substitution) := by
  cases leftEquality
  cases rightEquality
  cases eq_of_heq receiptEquality
  rfl

/-- Reindex a structural receipt along equality of both raw endpoints. -/
def cast
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {left right left' right' : Tm Head n}
    (leftEquality : left = left') (rightEquality : right = right') :
    StructuralStepReceipt computation headEq left right →
      StructuralStepReceipt computation headEq left' right' := by
  cases leftEquality
  cases rightEquality
  exact _root_.id

@[simp] theorem cast_rfl
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {left right : Tm Head n}
    (receipt : StructuralStepReceipt computation headEq left right) :
    cast rfl rfl receipt = receipt :=
  rfl

/-- Identity substitution preserves the complete structural step of the
canonical retained lift, including its exact congruence constructor. -/
theorem ofRules_substitute_ids_heq
    {Head : Type} (rules : Rules Head)
    {headEq : Head → Head → Prop} {n : Nat} {left right : Tm Head n}
    (receipt : StructuralStepReceipt
      (RetainedRoot.ofRules rules).computation headEq left right) :
    HEq (receipt.substitute (ids : Sub Head n n)) receipt := by
  induction receipt <;>
    simp_all [StructuralStepReceipt.substitute] <;>
    congr <;>
    try simp_all only [liftSub_ids, subst_ids]
  all_goals
    first
    | rw [liftSub_ids]
      assumption
    | exact (RetainedRoot.ofRulesSubstitutionCoherent rules).substitute_ids _

/-- Sequential substitution preserves the complete structural step of the
canonical retained lift exactly as one composite substitution does. -/
theorem ofRules_substitute_comp_heq
    {Head : Type} (rules : Rules Head)
    {headEq : Head → Head → Prop} {n m k : Nat}
    (later : Sub Head m k) (earlier : Sub Head n m)
    {left right : Tm Head n}
    (receipt : StructuralStepReceipt
      (RetainedRoot.ofRules rules).computation headEq left right) :
    HEq
      ((receipt.substitute earlier).substitute later)
      (receipt.substitute (fun index => subst later (earlier index))) := by
  induction receipt generalizing m k with
  | betaPi body argument =>
      have liftedEquality := liftSub_comp_function later earlier
      have bodyEquality :
          subst (liftSub later) (subst (liftSub earlier) body) =
            subst (liftSub (fun index => subst later (earlier index))) body :=
        (subst_comp (liftSub later) (liftSub earlier) body).trans
          (congrArg (fun substitution => subst substitution body) liftedEquality)
      have argumentEquality := subst_comp later earlier argument
      have firstBoundary := betaPi_substitute_heq
        (computation := (RetainedRoot.ofRules rules).computation)
        (headEq := headEq) body argument earlier
      have firstBoundaryUnderLater := substitute_congr_heq
        (by rfl) (subst_inst0 earlier argument body)
        firstBoundary later
      have secondBoundary := betaPi_substitute_heq
        (computation := (RetainedRoot.ofRules rules).computation)
        (headEq := headEq) (subst (liftSub earlier) body)
        (subst earlier argument) later
      have canonicalComposition :=
        betaPi_heq
          (computation := (RetainedRoot.ofRules rules).computation)
          (headEq := headEq) (heq_of_eq bodyEquality)
          (heq_of_eq argumentEquality)
      have compositeBoundary := betaPi_substitute_heq
        (computation := (RetainedRoot.ofRules rules).computation)
        (headEq := headEq) body argument
        (fun index => subst later (earlier index))
      exact firstBoundaryUnderLater.trans
        (secondBoundary.trans
          (canonicalComposition.trans compositeBoundary.symm))
  | betaSigmaFst first second =>
      have firstEquality := subst_comp later earlier first
      have secondEquality := subst_comp later earlier second
      simpa only [StructuralStepReceipt.substitute, Presentation.subst] using
        betaSigmaFst_heq (heq_of_eq firstEquality) (heq_of_eq secondEquality)
  | betaSigmaSnd first second =>
      have firstEquality := subst_comp later earlier first
      have secondEquality := subst_comp later earlier second
      simpa only [StructuralStepReceipt.substitute, Presentation.subst] using
        betaSigmaSnd_heq (heq_of_eq firstEquality) (heq_of_eq secondEquality)
  | head equality => rfl
  | root evidence =>
      exact root_heq
        (heq_of_eq (subst_comp later earlier _))
        (heq_of_eq (subst_comp later earlier _))
        ((RetainedRoot.ofRulesSubstitutionCoherent rules).substitute_comp
          later earlier evidence)
  | congPiDom nested ih =>
      rename_i domain domain' codomain
      have nestedEquality := ih later earlier
      have liftedEquality := liftSub_comp_function later earlier
      have codomainEquality :=
        (subst_comp (liftSub later) (liftSub earlier) codomain).trans
          (congrArg (fun substitution => subst substitution codomain)
            liftedEquality)
      exact congPiDom_heq
        (heq_of_eq (subst_comp later earlier domain))
        (heq_of_eq (subst_comp later earlier domain'))
        (heq_of_eq codomainEquality) nestedEquality
  | congPiCod nested ih =>
      rename_i domain codomain codomain'
      have liftedEquality := liftSub_comp_function later earlier
      have nestedEquality := HEq.trans
        (ih (liftSub later) (liftSub earlier))
        (substitute_heq_of_eq nested liftedEquality)
      have codomainEquality :=
        (subst_comp (liftSub later) (liftSub earlier) codomain).trans
          (congrArg (fun substitution => subst substitution codomain)
            liftedEquality)
      have codomainPrimeEquality :=
        (subst_comp (liftSub later) (liftSub earlier) codomain').trans
          (congrArg (fun substitution => subst substitution codomain')
            liftedEquality)
      exact congPiCod_heq
        (heq_of_eq (subst_comp later earlier domain))
        (heq_of_eq codomainEquality) (heq_of_eq codomainPrimeEquality)
        nestedEquality
  | congSigmaDom nested ih =>
      rename_i domain domain' codomain
      have nestedEquality := ih later earlier
      have liftedEquality := liftSub_comp_function later earlier
      have codomainEquality :=
        (subst_comp (liftSub later) (liftSub earlier) codomain).trans
          (congrArg (fun substitution => subst substitution codomain)
            liftedEquality)
      exact congSigmaDom_heq
        (heq_of_eq (subst_comp later earlier domain))
        (heq_of_eq (subst_comp later earlier domain'))
        (heq_of_eq codomainEquality) nestedEquality
  | congSigmaCod nested ih =>
      rename_i domain codomain codomain'
      have liftedEquality := liftSub_comp_function later earlier
      have nestedEquality := HEq.trans
        (ih (liftSub later) (liftSub earlier))
        (substitute_heq_of_eq nested liftedEquality)
      have codomainEquality :=
        (subst_comp (liftSub later) (liftSub earlier) codomain).trans
          (congrArg (fun substitution => subst substitution codomain)
            liftedEquality)
      have codomainPrimeEquality :=
        (subst_comp (liftSub later) (liftSub earlier) codomain').trans
          (congrArg (fun substitution => subst substitution codomain')
            liftedEquality)
      exact congSigmaCod_heq
        (heq_of_eq (subst_comp later earlier domain))
        (heq_of_eq codomainEquality) (heq_of_eq codomainPrimeEquality)
        nestedEquality
  | congIdTy nested ih =>
      rename_i type type' leftTerm rightTerm
      have nestedEquality := ih later earlier
      exact congIdTy_heq
        (heq_of_eq (subst_comp later earlier type))
        (heq_of_eq (subst_comp later earlier type'))
        (heq_of_eq (subst_comp later earlier leftTerm))
        (heq_of_eq (subst_comp later earlier rightTerm)) nestedEquality
  | congIdLeft nested ih =>
      rename_i type leftTerm leftTerm' rightTerm
      have nestedEquality := ih later earlier
      exact congIdLeft_heq
        (heq_of_eq (subst_comp later earlier type))
        (heq_of_eq (subst_comp later earlier leftTerm))
        (heq_of_eq (subst_comp later earlier leftTerm'))
        (heq_of_eq (subst_comp later earlier rightTerm)) nestedEquality
  | congIdRight nested ih =>
      rename_i type leftTerm rightTerm rightTerm'
      have nestedEquality := ih later earlier
      exact congIdRight_heq
        (heq_of_eq (subst_comp later earlier type))
        (heq_of_eq (subst_comp later earlier leftTerm))
        (heq_of_eq (subst_comp later earlier rightTerm))
        (heq_of_eq (subst_comp later earlier rightTerm')) nestedEquality
  | congLam nested ih =>
      rename_i body body'
      have liftedEquality := liftSub_comp_function later earlier
      have nestedEquality := HEq.trans
        (ih (liftSub later) (liftSub earlier))
        (substitute_heq_of_eq nested liftedEquality)
      have bodyEquality :=
        (subst_comp (liftSub later) (liftSub earlier) body).trans
          (congrArg (fun substitution => subst substitution body) liftedEquality)
      have bodyPrimeEquality :=
        (subst_comp (liftSub later) (liftSub earlier) body').trans
          (congrArg (fun substitution => subst substitution body') liftedEquality)
      exact congLam_heq (heq_of_eq bodyEquality)
        (heq_of_eq bodyPrimeEquality) nestedEquality
  | congAppFun nested ih =>
      rename_i function function' argument
      have nestedEquality := ih later earlier
      exact congAppFun_heq
        (heq_of_eq (subst_comp later earlier function))
        (heq_of_eq (subst_comp later earlier function'))
        (heq_of_eq (subst_comp later earlier argument)) nestedEquality
  | congAppArg nested ih =>
      rename_i function argument argument'
      have nestedEquality := ih later earlier
      exact congAppArg_heq
        (heq_of_eq (subst_comp later earlier function))
        (heq_of_eq (subst_comp later earlier argument))
        (heq_of_eq (subst_comp later earlier argument')) nestedEquality
  | congPairFst nested ih =>
      rename_i first first' second
      have nestedEquality := ih later earlier
      exact congPairFst_heq
        (heq_of_eq (subst_comp later earlier first))
        (heq_of_eq (subst_comp later earlier first'))
        (heq_of_eq (subst_comp later earlier second)) nestedEquality
  | congPairSnd nested ih =>
      rename_i first second second'
      have nestedEquality := ih later earlier
      exact congPairSnd_heq
        (heq_of_eq (subst_comp later earlier first))
        (heq_of_eq (subst_comp later earlier second))
        (heq_of_eq (subst_comp later earlier second')) nestedEquality
  | congFst nested ih =>
      rename_i pair pair'
      exact congFst_heq
        (heq_of_eq (subst_comp later earlier pair))
        (heq_of_eq (subst_comp later earlier pair')) (ih later earlier)
  | congSnd nested ih =>
      rename_i pair pair'
      exact congSnd_heq
        (heq_of_eq (subst_comp later earlier pair))
        (heq_of_eq (subst_comp later earlier pair')) (ih later earlier)
  | congRefl nested ih =>
      rename_i term term'
      exact congRefl_heq
        (heq_of_eq (subst_comp later earlier term))
        (heq_of_eq (subst_comp later earlier term')) (ih later earlier)

end StructuralStepReceipt

/-! ## Complete conversion paths inherit the same coherence -/

namespace StructuralConversionReceipt

private theorem step_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {left right left' right' : Tm Head n}
    {receipt : StructuralStepReceipt computation headEq left right}
    {receipt' : StructuralStepReceipt computation headEq left' right'}
    (leftEquality : HEq left left') (rightEquality : HEq right right')
    (receiptEquality : HEq receipt receipt') :
    HEq
      ((.step receipt : StructuralConversionReceipt computation headEq left right))
      ((.step receipt' : StructuralConversionReceipt
        computation headEq left' right')) := by
  cases eq_of_heq leftEquality
  cases eq_of_heq rightEquality
  cases eq_of_heq receiptEquality
  rfl

private theorem refl_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {state state' : Tm Head n} (stateEquality : HEq state state') :
    HEq
      (ConversionEvidence.refl
        (computation := rawStructuralComputation computation headEq n)
        (index := ()) state)
      (ConversionEvidence.refl
        (computation := rawStructuralComputation computation headEq n)
        (index := ()) state') := by
  cases eq_of_heq stateEquality
  rfl

private theorem symm_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {left right left' right' : Tm Head n}
    {conversion : StructuralConversionReceipt computation headEq left right}
    {conversion' : StructuralConversionReceipt computation headEq left' right'}
    (leftEquality : HEq left left') (rightEquality : HEq right right')
    (conversionEquality : HEq conversion conversion') :
    HEq
      ((.symm conversion : StructuralConversionReceipt
        computation headEq right left))
      ((.symm conversion' : StructuralConversionReceipt
        computation headEq right' left')) := by
  cases eq_of_heq leftEquality
  cases eq_of_heq rightEquality
  cases eq_of_heq conversionEquality
  rfl

private theorem trans_heq
    {Head : Type} {computation : ProofRelevantRootComputation Head}
    {headEq : Head → Head → Prop} {n : Nat}
    {left middle right left' middle' right' : Tm Head n}
    {first : StructuralConversionReceipt computation headEq left middle}
    {second : StructuralConversionReceipt computation headEq middle right}
    {first' : StructuralConversionReceipt computation headEq left' middle'}
    {second' : StructuralConversionReceipt computation headEq middle' right'}
    (leftEquality : HEq left left') (middleEquality : HEq middle middle')
    (rightEquality : HEq right right')
    (firstEquality : HEq first first') (secondEquality : HEq second second') :
    HEq
      ((.trans first second : StructuralConversionReceipt
        computation headEq left right))
      ((.trans first' second' : StructuralConversionReceipt
        computation headEq left' right')) := by
  cases eq_of_heq leftEquality
  cases eq_of_heq middleEquality
  cases eq_of_heq rightEquality
  cases eq_of_heq firstEquality
  cases eq_of_heq secondEquality
  rfl

/-- Identity substitution preserves the complete conversion tree, including
every intermediate term and every retained structural step receipt. -/
theorem ofRules_substitute_ids_heq
    {Head : Type} (rules : Rules Head)
    {headEq : Head → Head → Prop} {n : Nat} {left right : Tm Head n}
    (conversion : StructuralConversionReceipt
      (RetainedRoot.ofRules rules).computation headEq left right) :
    HEq (conversion.substitute (ids : Sub Head n n)) conversion := by
  exact @ConversionEvidence.rec
    (Index := Unit)
    (computation := rawStructuralComputation
      (RetainedRoot.ofRules rules).computation headEq n)
    (index := ())
    (motive := fun source target current =>
      HEq (StructuralConversionReceipt.substitute current
        (ids : Sub Head n n)) current)
    (fun {source target} receipt => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        step_heq (heq_of_eq (subst_ids source))
          (heq_of_eq (subst_ids target))
          (StructuralStepReceipt.ofRules_substitute_ids_heq rules receipt))
    (fun state => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        refl_heq
          (computation := (RetainedRoot.ofRules rules).computation)
          (headEq := headEq) (heq_of_eq (subst_ids state)))
    (fun {source target} _current ih => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        symm_heq (heq_of_eq (subst_ids source))
          (heq_of_eq (subst_ids target)) ih)
    (fun {source middle target} _first _second ihFirst ihSecond => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        trans_heq (heq_of_eq (subst_ids source))
          (heq_of_eq (subst_ids middle)) (heq_of_eq (subst_ids target))
          ihFirst ihSecond)
    left right conversion

/-- Sequential substitution of a complete conversion path is identical to
one composite substitution, without flattening or re-associating its path. -/
theorem ofRules_substitute_comp_heq
    {Head : Type} (rules : Rules Head)
    {headEq : Head → Head → Prop} {n m k : Nat}
    (later : Sub Head m k) (earlier : Sub Head n m)
    {left right : Tm Head n}
    (conversion : StructuralConversionReceipt
      (RetainedRoot.ofRules rules).computation headEq left right) :
    HEq
      ((conversion.substitute earlier).substitute later)
      (conversion.substitute (fun index => subst later (earlier index))) := by
  exact @ConversionEvidence.rec
    (Index := Unit)
    (computation := rawStructuralComputation
      (RetainedRoot.ofRules rules).computation headEq n)
    (index := ())
    (motive := fun source target current =>
      HEq
        ((StructuralConversionReceipt.substitute current earlier).substitute
          later)
        (StructuralConversionReceipt.substitute current
          (fun index => subst later (earlier index))))
    (fun {source target} receipt => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        step_heq (heq_of_eq (subst_comp later earlier source))
          (heq_of_eq (subst_comp later earlier target))
          (StructuralStepReceipt.ofRules_substitute_comp_heq
            rules later earlier receipt))
    (fun state => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        refl_heq
          (computation := (RetainedRoot.ofRules rules).computation)
          (headEq := headEq) (heq_of_eq (subst_comp later earlier state)))
    (fun {source target} _current ih => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        symm_heq (heq_of_eq (subst_comp later earlier source))
          (heq_of_eq (subst_comp later earlier target)) ih)
    (fun {source middle target} _first _second ihFirst ihSecond => by
      simpa only [StructuralConversionReceipt.substitute,
        ProofRelevantStructuralComputation.StructuralConversionReceipt.mapCompatible] using
        trans_heq (heq_of_eq (subst_comp later earlier source))
          (heq_of_eq (subst_comp later earlier middle))
          (heq_of_eq (subst_comp later earlier target)) ihFirst ihSecond)
    left right conversion

end StructuralConversionReceipt

/-! ## Axiom audit -/

#print axioms RetainedRoot.ofRulesSubstitutionCoherent
#print axioms StructuralStepReceipt.ofRules_substitute_ids_heq
#print axioms StructuralStepReceipt.ofRules_substitute_comp_heq
#print axioms StructuralConversionReceipt.ofRules_substitute_ids_heq
#print axioms StructuralConversionReceipt.ofRules_substitute_comp_heq

end SyntacticJudgmentalPi
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
