import Mettapedia.Logic.HOL.SetMembershipProofs
import Mettapedia.Logic.HOL.PairingReconstruction
import Mettapedia.Logic.HOL.SelectionProofs

/-!
# Pairing from set operations and an explicit selection law

The construction follows the decided-index route of
`Mettapedia.SetTheory.Profiles.Pairing`: separate the double powerset of the
empty set to indices at which membership of the empty set is decided, then
take a functional image. The image function uses the supplied set selector.
No pairing law or excluded-middle law is an input. Relational replacement
has a separate construction without a selection operator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetPairingProofs
open SetComprehensionProofs SetMembershipProofs ContextualTrinity
open Mettapedia.Logic.HOL.Embedding
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
abbrev object := ZFSetHenkinInterpretation.set
variable (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

def condition (point : Term Const Γ object) : Formula Const Γ :=
  member core (.const (core .empty)) point

def index : Term Const Γ object :=
  separate core (power core (power core (.const (core .empty))))
    (.lam (.or (condition core (.var .vz)) (.not (condition core (.var .vz)))))

def choose (question : Formula Const Γ) (left right : Term Const Γ object) : Term Const Γ object :=
  SelectionProofs.selected (weakenCtx Γ epsilon)
    (.or (.and (weaken question) (.eq (.var .vz) (weaken left)))
      (.and (.not (weaken question)) (.eq (.var .vz) (weaken right))))

def send (left right : Term Const Γ object) : Term Const Γ (object ⇒ object) :=
  .lam (choose epsilon (condition core (.var .vz)) (weaken left) (weaken right))

def unordered (left right : Term Const Γ object) : Term Const Γ object :=
  image core (index core) (send core epsilon left right)

structure Laws (assumptions : List (Formula Const Γ)) where
  empty : ProofSyntax Const assumptions (lawAt core ZFSetHenkinInterpretation.emptyLaw)
  power : ProofSyntax Const assumptions (lawAt core ZFSetHenkinInterpretation.powerLaw)
  separation : ProofSyntax Const assumptions (lawAt core ZFSetHenkinInterpretation.separationLaw)
  replacement : ProofSyntax Const assumptions (lawAt core ZFSetHenkinInterpretation.replacementLaw)
  selection : ProofSyntax Const assumptions (SelectionProofs.principle (weakenCtx Γ epsilon))

def Laws.prepend {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (formula : Formula Const Γ) :
    Laws core epsilon (formula :: Δ) where
  empty := laws.empty.prepend formula
  power := laws.power.prepend formula
  separation := laws.separation.prepend formula
  replacement := laws.replacement.prepend formula
  selection := laws.selection.prepend formula

private theorem substitutePrinciple (substitution : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection object)) :
    HOL.subst substitution (SelectionProofs.principle selection) =
      SelectionProofs.principle (HOL.subst substitution selection) := by
  simp only [SelectionProofs.principle, HOL.subst, SelectionProofs.subst_instanceFormula,
    HOL.subst_weaken, Subst.lift]

def Laws.weaken {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (added : Ty Unit) :
    Laws core epsilon (weakenHyps (σ := added) Δ) where
  empty := weakenLaw core _ laws.empty
  power := weakenLaw core _ laws.power
  separation := weakenLaw core _ laws.separation
  replacement := weakenLaw core _ laws.replacement
  selection := by
    apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof laws.selection)
    simpa only [HOL.subst_ofRename, HOL.weaken, HOL.rename_weakenCtx] using
      substitutePrinciple (Subst.ofRename (Rename.weaken (σ := added))) (weakenCtx Γ epsilon)

@[simp] theorem subst_condition (substitution : Subst Const Γ Ξ) (point : Term Const Γ object) :
    HOL.subst substitution (condition core point) = condition core (HOL.subst substitution point) := rfl

@[simp] theorem subst_index (substitution : Subst Const Γ Ξ) :
    HOL.subst substitution (index (Γ := Γ) core) = index (Γ := Ξ) core := rfl

@[simp] theorem subst_choose (substitution : Subst Const Γ Ξ)
    (question : Formula Const Γ) (left right : Term Const Γ object) :
    HOL.subst substitution (choose epsilon question left right) =
      choose epsilon (HOL.subst substitution question) (HOL.subst substitution left)
        (HOL.subst substitution right) := by
  simp [choose, SelectionProofs.selected, HOL.subst, HOL.subst_weakenCtx, HOL.subst_weaken, Subst.lift]

@[simp] theorem subst_send (substitution : Subst Const Γ Ξ) (left right : Term Const Γ object) :
    HOL.subst substitution (send core epsilon left right) =
      send core epsilon (HOL.subst substitution left) (HOL.subst substitution right) := by
  simp [send, HOL.subst, HOL.subst_weaken, Subst.lift]

@[simp] theorem subst_unordered (substitution : Subst Const Γ Ξ) (left right : Term Const Γ object) :
    HOL.subst substitution (unordered core epsilon left right) =
      unordered core epsilon (HOL.subst substitution left) (HOL.subst substitution right) := by
  simp [unordered, image, HOL.subst]

theorem rename_unordered (rho : Rename Unit Γ Ξ) (left right : Term Const Γ object) :
    HOL.rename rho (unordered core epsilon left right) =
      unordered core epsilon (HOL.rename rho left) (HOL.rename rho right) := by
  simpa only [HOL.subst_ofRename] using subst_unordered core epsilon (Subst.ofRename rho) left right

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (weaken term) = term := instantiate_weaken point term

def sendBeta (left right point : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (.app (send core epsilon left right) point)
      (choose epsilon (condition core point) left right)) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta point
    (choose epsilon (condition core (.var .vz)) (weaken left) (weaken right)))
  simp only [send, instantiate, subst_choose, subst_condition, HOL.subst, Subst.single, substituteWeak]

def chooseSpec (question : Formula Const Γ) (left right : Term Const Γ object)
    (law : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (decided : ProofSyntax Const Δ (.or question (.not question))) :
    ProofSyntax Const Δ (.or
      (.and question (.eq (choose epsilon question left right) left))
      (.and (.not question) (.eq (choose epsilon question left right) right))) := by
  let body : Formula Const (object :: Γ) :=
    .or (.and (weaken question) (.eq (.var .vz) (weaken left)))
      (.and (.not (weaken question)) (.eq (.var .vz) (weaken right)))
  have witness : ProofSyntax Const Δ (.ex body) := by
    refine .orE decided ?_ ?_
    · apply ProofSyntax.exI left
      apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.orIL
        (ψ := .and (.not question) (.eq left right)) (.andI (.hyp 0) (.eqRefl left)))
      simp only [body, instantiate, HOL.subst, Subst.single, substituteWeak]
      rfl
    · apply ProofSyntax.exI right
      apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.orIR
        (φ := .and question (.eq right left)) (.andI (.hyp 0) (.eqRefl right)))
      simp only [body, instantiate, HOL.subst, Subst.single, substituteWeak]
      rfl
  apply ProofSyntax.castIndices rfl ?_
    (SelectionProofs.specification (weakenCtx Γ epsilon) body law witness)
  simp only [body, instantiate, HOL.subst, Subst.single, substituteWeak]
  rfl

def chooseLeft (question : Formula Const Γ) (left right : Term Const Γ object)
    (law : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (positive : ProofSyntax Const Δ question) :
    ProofSyntax Const Δ (.eq (choose epsilon question left right) left) := by
  refine .orE (chooseSpec epsilon question left right law (.orIL positive)) ?_ ?_
  · exact .andER (.hyp 0)
  · exact .botE (.notE (.andEL (.hyp 0)) (positive.prepend _))

def chooseRight (question : Formula Const Γ) (left right : Term Const Γ object)
    (law : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (negative : ProofSyntax Const Δ (.not question)) :
    ProofSyntax Const Δ (.eq (choose epsilon question left right) right) := by
  refine .orE (chooseSpec epsilon question left right law (.orIR negative)) ?_ ?_
  · exact .botE (.notE (negative.prepend _) (.andEL (.hyp 0)))
  · exact .andER (.hyp 0)

def indexDecided (point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (member : ProofSyntax Const Δ (SetComprehensionProofs.member core point (index core))) :
    ProofSyntax Const Δ (.or (condition core point) (.not (condition core point))) := by
  apply ProofSyntax.castIndices rfl ?_
    (separationProperty core _ point
      (.or (condition core (.var .vz)) (.not (condition core (.var .vz)))) laws.separation member)
  rfl

def emptyInIndex (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (member core (.const (core .empty)) (index core)) := by
  apply separationIntro core _ _
    (.or (condition core (.var .vz)) (.not (condition core (.var .vz)))) laws.separation
    (emptyInPower core _ laws.empty laws.power)
  exact .orIR (emptyElim core _ laws.empty)

def powerEmptyInIndex (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (member core (power core (.const (core .empty))) (index core)) := by
  apply separationIntro core _ _
    (.or (condition core (.var .vz)) (.not (condition core (.var .vz)))) laws.separation
    (selfInPower core _ laws.power)
  exact .orIL (emptyInPowerEmpty core laws.power)

@[simp] theorem weaken_index {added : Ty Unit} :
    HOL.weaken (σ := added) (index (Γ := Γ) core) = index (Γ := added :: Γ) core := rfl

@[simp] theorem weaken_send {added : Ty Unit} (left right : Term Const Γ object) :
    HOL.weaken (σ := added) (send core epsilon left right) =
      send core epsilon (HOL.weaken left) (HOL.weaken right) := by
  simpa only [HOL.subst_ofRename, HOL.weaken] using
    subst_send core epsilon (Subst.ofRename (Rename.weaken (σ := added))) left right

@[simp] theorem weaken_unordered {added : Ty Unit} (left right : Term Const Γ object) :
    HOL.weaken (σ := added) (unordered core epsilon left right) =
      unordered core epsilon (HOL.weaken left) (HOL.weaken right) := by
  simpa only [HOL.subst_ofRename, HOL.weaken] using
    subst_unordered core epsilon (Subst.ofRename (Rename.weaken (σ := added))) left right

def leftMem (left right : Term Const Γ object) (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (member core left (unordered core epsilon left right)) := by
  let point : Term Const Γ object := power core (.const (core .empty))
  have equal : ProofSyntax Const Δ (.eq (.app (send core epsilon left right) point) left) :=
    .eqTrans (sendBeta core epsilon left right point)
      (chooseLeft epsilon (condition core point) left right laws.selection
        (emptyInPowerEmpty core laws.power))
  exact transportValue core _ equal
    (imageIntro core (index core) (send core epsilon left right) point laws.replacement
      (powerEmptyInIndex core epsilon laws))

def rightMem (left right : Term Const Γ object) (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (member core right (unordered core epsilon left right)) := by
  let point : Term Const Γ object := .const (core .empty)
  have equal : ProofSyntax Const Δ (.eq (.app (send core epsilon left right) point) right) :=
    .eqTrans (sendBeta core epsilon left right point)
      (chooseRight epsilon (condition core point) left right laws.selection
        (emptyElim core point laws.empty))
  exact transportValue core _ equal
    (imageIntro core (index core) (send core epsilon left right) point laws.replacement
      (emptyInIndex core epsilon laws))

/-- A member of the functional image must be one of the two supplied values.
The image witness has its own object binder and local assumption. -/
def unorderedElim (left right point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core point (unordered core epsilon left right))) :
    ProofSyntax Const Δ (.or (.eq point left) (.eq point right)) := by
  have imageWitness := ProofSyntax.impE
    (.andEL (replacement core (index core) (send core epsilon left right) point laws.replacement)) admitted
  refine ProofSyntax.exE imageWitness ?_
  let body : Formula Const (object :: Γ) :=
    .and (member core (.var .vz) (HOL.weaken (index core)))
      (.eq (.app (HOL.weaken (send core epsilon left right)) (.var .vz)) (HOL.weaken point))
  let assumptions := body :: weakenHyps (σ := object) Δ
  let raised := (laws.weaken object).prepend body
  have witness : ProofSyntax Const assumptions body := .hyp 0
  have inIndex : ProofSyntax Const assumptions (member core (.var .vz) (index core)) :=
    ProofSyntax.castIndices rfl (by rw [weaken_index]) (.andEL witness)
  have decided := indexDecided core epsilon (.var .vz) raised inIndex
  have spec := chooseSpec epsilon (condition core (.var .vz))
    (HOL.weaken left) (HOL.weaken right) raised.selection decided
  have value : ProofSyntax Const assumptions
      (.eq (choose epsilon (condition core (.var .vz)) (HOL.weaken left) (HOL.weaken right))
        (HOL.weaken point)) := by
    apply ProofSyntax.eqTrans (ProofSyntax.eqSymm
      (sendBeta core epsilon (HOL.weaken left) (HOL.weaken right) (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (.andER witness)
    simp only [weaken_send]
  change ProofSyntax Const assumptions
    (.or (.eq (HOL.weaken point) (HOL.weaken left)) (.eq (HOL.weaken point) (HOL.weaken right)))
  refine .orE spec ?_ ?_
  · exact .orIL (.eqTrans ((ProofSyntax.eqSymm value).prepend _) (.andER (.hyp 0)))
  · exact .orIR (.eqTrans ((ProofSyntax.eqSymm value).prepend _) (.andER (.hyp 0)))

def unorderedIntro (left right point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (selected : ProofSyntax Const Δ (.or (.eq point left) (.eq point right))) :
    ProofSyntax Const Δ (member core point (unordered core epsilon left right)) := by
  refine .orE selected ?_ ?_
  · exact transportValue core _ (.eqSymm (.hyp 0)) ((leftMem core epsilon left right laws).prepend _)
  · exact transportValue core _ (.eqSymm (.hyp 0)) ((rightMem core epsilon left right laws).prepend _)

def membership (left right point : Term Const Γ object) (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (.and
      (.imp (member core point (unordered core epsilon left right)) (.or (.eq point left) (.eq point right)))
      (.imp (.or (.eq point left) (.eq point right)) (member core point (unordered core epsilon left right)))) :=
  .andI (.impI (unorderedElim core epsilon left right point (laws.prepend _) (.hyp 0)))
    (.impI (unorderedIntro core epsilon left right point (laws.prepend _) (.hyp 0)))

/-- Proof-producing membership rules at the same ordered hypothesis context.
The elimination field is a retained implication, so it weakens without
reconstructing its original theory proof. -/
structure MembershipRules (assumptions : List (Formula Const Γ)) where
  left : ∀ left right, ProofSyntax Const assumptions (member core left (unordered core epsilon left right))
  right : ∀ left right, ProofSyntax Const assumptions (member core right (unordered core epsilon left right))
  elimination : ∀ left right point, ProofSyntax Const assumptions
    (.imp (member core point (unordered core epsilon left right)) (.or (.eq point left) (.eq point right)))

def MembershipRules.prepend {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (rules : MembershipRules core epsilon Δ) (formula : Formula Const Γ) :
    MembershipRules core epsilon (formula :: Δ) where
  left left right := (rules.left left right).prepend formula
  right left right := (rules.right left right).prepend formula
  elimination left right point := (rules.elimination left right point).prepend formula

def MembershipRules.leftMem (left right : Term Const Γ object) (rules : MembershipRules core epsilon Δ) :=
  rules.left left right

def MembershipRules.rightMem (left right : Term Const Γ object) (rules : MembershipRules core epsilon Δ) :=
  rules.right left right

def MembershipRules.elim (left right point : Term Const Γ object) (rules : MembershipRules core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core point (unordered core epsilon left right))) :
    ProofSyntax Const Δ (.or (.eq point left) (.eq point right)) :=
  .impE (rules.elimination left right point) admitted

def Laws.membershipRules {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) : MembershipRules core epsilon Δ where
  left left right := leftMem core epsilon left right laws
  right left right := rightMem core epsilon left right laws
  elimination left right point := .impI (unorderedElim core epsilon left right point (laws.prepend _) (.hyp 0))

def ordered (left right : Term Const Γ object) : Term Const Γ object :=
  unordered core epsilon (unordered core epsilon left left) (unordered core epsilon left right)

@[simp] theorem subst_ordered (substitution : Subst Const Γ Ξ) (left right : Term Const Γ object) :
    HOL.subst substitution (ordered core epsilon left right) =
      ordered core epsilon (HOL.subst substitution left) (HOL.subst substitution right) := by
  simp only [ordered, subst_unordered]

def orderedCongrFirst {left left' : Term Const Γ object} (right : Term Const Γ object)
    (equal : ProofSyntax Const Δ (.eq left left')) :
    ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon left' right)) := by
  apply ProofSyntax.castIndices rfl ?_
    (holeCongr (ordered core epsilon (.var .vz) (HOL.weaken right)) equal)
  simp only [instantiate, subst_ordered, HOL.subst, Subst.single, substituteWeak]

/-- Fixing one member makes unordered pairing injective in the other.
Only the already derived membership programs are used. -/
def reconstructionOperations : PairingReconstruction.Operations Const Γ object where
  member := member core
  pair := unordered core epsilon
  transportBound point equal admitted := SetMembershipProofs.transportBound core point equal admitted
  orderedCongrFirst right equal := SetPairingProofs.orderedCongrFirst core epsilon right equal

def MembershipRules.reconstruction {core : Core Const}
    {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (rules : MembershipRules core epsilon Δ) :
    PairingReconstruction.Rules (reconstructionOperations core epsilon) Δ where
  left := rules.left
  right := rules.right
  elimination := rules.elimination

def MembershipRules.anchoredInjective (anchor left right : Term Const Γ object) (rules : MembershipRules core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (unordered core epsilon anchor left) (unordered core epsilon anchor right))) :
    ProofSyntax Const Δ (.eq left right) :=
  PairingReconstruction.anchoredInjective (reconstructionOperations core epsilon) anchor left right rules.reconstruction equal

def anchoredInjective (anchor left right : Term Const Γ object) (laws : Laws core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (unordered core epsilon anchor left) (unordered core epsilon anchor right))) :
    ProofSyntax Const Δ (.eq left right) :=
  MembershipRules.anchoredInjective core epsilon anchor left right laws.membershipRules equal

def MembershipRules.firstCoordinate (left right first second : Term Const Γ object) (rules : MembershipRules core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second))) :
    ProofSyntax Const Δ (.eq left first) :=
  PairingReconstruction.firstCoordinate (reconstructionOperations core epsilon) left right first second rules.reconstruction equal

def firstCoordinate (left right first second : Term Const Γ object) (laws : Laws core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second))) :
    ProofSyntax Const Δ (.eq left first) :=
  MembershipRules.firstCoordinate core epsilon left right first second laws.membershipRules equal

/-- Both fields of the actual Kuratowski construction are recovered from
equality. No injectivity premise for the constructed pair is assumed. -/
def MembershipRules.orderedInjective (left right first second : Term Const Γ object) (rules : MembershipRules core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second))) :
    ProofSyntax Const Δ (.and (.eq left first) (.eq right second)) :=
  PairingReconstruction.orderedInjective (reconstructionOperations core epsilon) left right first second rules.reconstruction equal

def orderedInjective (left right first second : Term Const Γ object) (laws : Laws core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second))) :
    ProofSyntax Const Δ (.and (.eq left first) (.eq right second)) :=
  MembershipRules.orderedInjective core epsilon left right first second laws.membershipRules equal

structure MembershipRules.Free {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (rules : MembershipRules core epsilon Δ) : Prop where
  left : ∀ left right, (rules.left left right).FunctionExtensionalityFree
  right : ∀ left right, (rules.right left right).FunctionExtensionalityFree
  elimination : ∀ left right point, (rules.elimination left right point).FunctionExtensionalityFree

theorem MembershipRules.prepend_free {core : Core Const}
    {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (rules : MembershipRules core epsilon Δ) (formula : Formula Const Γ) (free : rules.Free) :
    (rules.prepend formula).Free where
  left left right := by simpa [MembershipRules.prepend, ProofSyntax.prepend] using free.left left right
  right left right := by simpa [MembershipRules.prepend, ProofSyntax.prepend] using free.right left right
  elimination left right point := by
    simpa [MembershipRules.prepend, ProofSyntax.prepend] using free.elimination left right point

structure Laws.Free {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) : Prop where
  empty : laws.empty.FunctionExtensionalityFree
  power : laws.power.FunctionExtensionalityFree
  separation : laws.separation.FunctionExtensionalityFree
  replacement : laws.replacement.FunctionExtensionalityFree
  selection : laws.selection.FunctionExtensionalityFree

theorem Laws.prepend_free {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (formula : Formula Const Γ) (free : laws.Free) :
    (laws.prepend formula).Free where
  empty := by simpa [Laws.prepend, ProofSyntax.prepend] using free.empty
  power := by simpa [Laws.prepend, ProofSyntax.prepend] using free.power
  separation := by simpa [Laws.prepend, ProofSyntax.prepend] using free.separation
  replacement := by simpa [Laws.prepend, ProofSyntax.prepend] using free.replacement
  selection := by simpa [Laws.prepend, ProofSyntax.prepend] using free.selection

theorem Laws.weaken_free {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (added : Ty Unit) (free : laws.Free) :
    (laws.weaken added).Free where
  empty := weakenLaw_free (added := added) core _ laws.empty free.empty
  power := weakenLaw_free (added := added) core _ laws.power free.power
  separation := weakenLaw_free (added := added) core _ laws.separation free.separation
  replacement := weakenLaw_free (added := added) core _ laws.replacement free.replacement
  selection := by simpa [Laws.weaken, PredicateFixedPoint.weakenProof] using free.selection

theorem sendBeta_free (left right point : Term Const Γ object) :
    (sendBeta (Δ := Δ) core epsilon left right point).FunctionExtensionalityFree := by
  simp [sendBeta, ProofSyntax.FunctionExtensionalityFree]

theorem chooseSpec_free (question : Formula Const Γ) (left right : Term Const Γ object)
    (law : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (decided : ProofSyntax Const Δ (.or question (.not question)))
    (lawFree : law.FunctionExtensionalityFree) (decidedFree : decided.FunctionExtensionalityFree) :
    (chooseSpec epsilon question left right law decided).FunctionExtensionalityFree := by
  simp only [chooseSpec, ProofSyntax.functionExtensionalityFree_castIndices]
  apply SelectionProofs.specification_free
  · exact lawFree
  · simp [ProofSyntax.FunctionExtensionalityFree, decidedFree]

theorem chooseLeft_free (question : Formula Const Γ) (left right : Term Const Γ object)
    (law : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (positive : ProofSyntax Const Δ question)
    (lawFree : law.FunctionExtensionalityFree) (proofFree : positive.FunctionExtensionalityFree) :
    (chooseLeft epsilon question left right law positive).FunctionExtensionalityFree := by
  simp [chooseLeft, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
    chooseSpec_free, lawFree, proofFree]

theorem chooseRight_free (question : Formula Const Γ) (left right : Term Const Γ object)
    (law : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (negative : ProofSyntax Const Δ (.not question))
    (lawFree : law.FunctionExtensionalityFree) (proofFree : negative.FunctionExtensionalityFree) :
    (chooseRight epsilon question left right law negative).FunctionExtensionalityFree := by
  simp [chooseRight, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
    chooseSpec_free, lawFree, proofFree]

theorem indexDecided_free (point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core point (index core)))
    (lawsFree : laws.Free) (proofFree : admitted.FunctionExtensionalityFree) :
    (indexDecided core epsilon point laws admitted).FunctionExtensionalityFree := by
  simp [indexDecided, separationProperty, ProofSyntax.FunctionExtensionalityFree,
    separation_free, lawsFree.separation, proofFree]

theorem emptyInIndex_free (laws : Laws core epsilon Δ) (free : laws.Free) :
    (emptyInIndex core epsilon laws).FunctionExtensionalityFree := by
  apply separationIntro_free
  · exact free.separation
  · exact emptyInPower_free core _ laws.empty laws.power free.empty free.power
  · simp [ProofSyntax.FunctionExtensionalityFree, emptyElim_free, free.empty]

theorem powerEmptyInIndex_free (laws : Laws core epsilon Δ) (free : laws.Free) :
    (powerEmptyInIndex core epsilon laws).FunctionExtensionalityFree := by
  apply separationIntro_free
  · exact free.separation
  · exact selfInPower_free core _ laws.power free.power
  · simp [ProofSyntax.FunctionExtensionalityFree, emptyInPowerEmpty_free, free.power]

theorem leftMem_free (left right : Term Const Γ object) (laws : Laws core epsilon Δ) (free : laws.Free) :
    (leftMem core epsilon left right laws).FunctionExtensionalityFree := by
  apply transportValue_free
  · exact ⟨sendBeta_free core epsilon left right _,
      chooseLeft_free epsilon _ left right laws.selection _ free.selection
        (emptyInPowerEmpty_free core laws.power free.power)⟩
  · exact imageIntro_free core _ _ _ laws.replacement _ free.replacement
      (powerEmptyInIndex_free core epsilon laws free)

theorem rightMem_free (left right : Term Const Γ object) (laws : Laws core epsilon Δ) (free : laws.Free) :
    (rightMem core epsilon left right laws).FunctionExtensionalityFree := by
  apply transportValue_free
  · exact ⟨sendBeta_free core epsilon left right _,
      chooseRight_free epsilon _ left right laws.selection _ free.selection
        ((emptyElim_free core _ laws.empty).mpr free.empty)⟩
  · exact imageIntro_free core _ _ _ laws.replacement _ free.replacement
      (emptyInIndex_free core epsilon laws free)

theorem unorderedElim_free (left right point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core point (unordered core epsilon left right)))
    (lawsFree : laws.Free) (proofFree : admitted.FunctionExtensionalityFree) :
    (unorderedElim core epsilon left right point laws admitted).FunctionExtensionalityFree := by
  let body : Formula Const (object :: Γ) :=
    .and (member core (.var .vz) (HOL.weaken (index core)))
      (.eq (.app (HOL.weaken (send core epsilon left right)) (.var .vz)) (HOL.weaken point))
  have raisedFree := Laws.prepend_free (laws.weaken object) body (laws.weaken_free object lawsFree)
  simp only [unorderedElim, id_eq, ProofSyntax.FunctionExtensionalityFree,
    ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
    ProofSyntax.functionExtensionalityFree_castIndices, replacement_free, sendBeta_free,
    proofFree, lawsFree.replacement, and_self, true_and, and_true]
  apply chooseSpec_free
  · exact raisedFree.selection
  · apply indexDecided_free
    · exact raisedFree
    · simp [ProofSyntax.FunctionExtensionalityFree]

theorem unorderedIntro_free (left right point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (selected : ProofSyntax Const Δ (.or (.eq point left) (.eq point right)))
    (lawsFree : laws.Free) (proofFree : selected.FunctionExtensionalityFree) :
    (unorderedIntro core epsilon left right point laws selected).FunctionExtensionalityFree := by
  simp [unorderedIntro, transportValue, valueCongr, ProofSyntax.FunctionExtensionalityFree,
    ProofSyntax.prepend, leftMem_free, rightMem_free, lawsFree, proofFree]

theorem membership_free (left right point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (free : laws.Free) : (membership core epsilon left right point laws).FunctionExtensionalityFree := by
  simp only [membership, ProofSyntax.FunctionExtensionalityFree]
  exact ⟨unorderedElim_free core epsilon left right point _ _ (laws.prepend_free _ free) trivial,
    unorderedIntro_free core epsilon left right point _ _ (laws.prepend_free _ free) trivial⟩

theorem orderedCongrFirst_free {left left' : Term Const Γ object} (right : Term Const Γ object)
    (equal : ProofSyntax Const Δ (.eq left left')) (free : equal.FunctionExtensionalityFree) :
    (orderedCongrFirst core epsilon right equal).FunctionExtensionalityFree := by
  simp [orderedCongrFirst, holeCongr, ProofSyntax.FunctionExtensionalityFree, free]

theorem Laws.membershipRules_free {core : Core Const}
    {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (free : laws.Free) : laws.membershipRules.Free where
  left left right := leftMem_free core epsilon left right laws free
  right left right := rightMem_free core epsilon left right laws free
  elimination left right point :=
    unorderedElim_free core epsilon left right point (laws.prepend _) (.hyp 0)
      (laws.prepend_free _ free) trivial

theorem reconstructionOperations_free : (reconstructionOperations (Γ := Γ) core epsilon).Free where
  transportBound _ _ _ first second := ⟨first,second⟩
  orderedCongrFirst right equal free := orderedCongrFirst_free core epsilon right equal free

theorem MembershipRules.reconstruction_free {core : Core Const}
    {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (rules : MembershipRules core epsilon Δ) (free : rules.Free) : rules.reconstruction.Free where
  left := free.left
  right := free.right
  elimination := free.elimination

theorem MembershipRules.anchoredInjective_free (anchor left right : Term Const Γ object)
    (rules : MembershipRules core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (unordered core epsilon anchor left) (unordered core epsilon anchor right)))
    (rulesFree : rules.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (MembershipRules.anchoredInjective core epsilon anchor left right rules equal).FunctionExtensionalityFree :=
  PairingReconstruction.anchoredInjective_free (reconstructionOperations core epsilon) anchor left right
    rules.reconstruction equal (reconstructionOperations_free core epsilon)
    (rules.reconstruction_free rulesFree) proofFree

theorem MembershipRules.firstCoordinate_free (left right first second : Term Const Γ object)
    (rules : MembershipRules core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second)))
    (rulesFree : rules.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (MembershipRules.firstCoordinate core epsilon left right first second rules equal).FunctionExtensionalityFree :=
  PairingReconstruction.firstCoordinate_free (reconstructionOperations core epsilon) left right first second
    rules.reconstruction equal (reconstructionOperations_free core epsilon)
    (rules.reconstruction_free rulesFree) proofFree

theorem MembershipRules.orderedInjective_free (left right first second : Term Const Γ object)
    (rules : MembershipRules core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second)))
    (rulesFree : rules.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (MembershipRules.orderedInjective core epsilon left right first second rules equal).FunctionExtensionalityFree :=
  PairingReconstruction.orderedInjective_free (reconstructionOperations core epsilon) left right first second
    rules.reconstruction equal (reconstructionOperations_free core epsilon)
    (rules.reconstruction_free rulesFree) proofFree

theorem anchoredInjective_free (anchor left right : Term Const Γ object) (laws : Laws core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (unordered core epsilon anchor left) (unordered core epsilon anchor right)))
    (lawsFree : laws.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (anchoredInjective core epsilon anchor left right laws equal).FunctionExtensionalityFree :=
  MembershipRules.anchoredInjective_free core epsilon anchor left right laws.membershipRules equal
    (laws.membershipRules_free lawsFree) proofFree

theorem firstCoordinate_free (left right first second : Term Const Γ object) (laws : Laws core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second)))
    (lawsFree : laws.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (firstCoordinate core epsilon left right first second laws equal).FunctionExtensionalityFree :=
  MembershipRules.firstCoordinate_free core epsilon left right first second laws.membershipRules equal
    (laws.membershipRules_free lawsFree) proofFree

theorem orderedInjective_free (left right first second : Term Const Γ object) (laws : Laws core epsilon Δ)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) (ordered core epsilon first second)))
    (lawsFree : laws.Free) (proofFree : equal.FunctionExtensionalityFree) :
    (orderedInjective core epsilon left right first second laws equal).FunctionExtensionalityFree :=
  MembershipRules.orderedInjective_free core epsilon left right first second laws.membershipRules equal
    (laws.membershipRules_free lawsFree) proofFree

def orderedApartSecond (left right first second : Term Const Γ object) (laws : Laws core epsilon Δ)
    (apart : ProofSyntax Const Δ (.not (.eq right second))) :
    ProofSyntax Const Δ (.not (.eq (ordered core epsilon left right) (ordered core epsilon first second))) :=
  .notI (.notE (apart.prepend _)
    (.andER (orderedInjective core epsilon left right first second (laws.prepend _) (.hyp 0))))

theorem orderedApartSecond_free (left right first second : Term Const Γ object) (laws : Laws core epsilon Δ)
    (apart : ProofSyntax Const Δ (.not (.eq right second)))
    (lawsFree : laws.Free) (apartFree : apart.FunctionExtensionalityFree) :
    (orderedApartSecond core epsilon left right first second laws apart).FunctionExtensionalityFree := by
  exact ⟨by simpa [ProofSyntax.prepend] using apartFree,
    orderedInjective_free core epsilon left right first second _ _ (laws.prepend_free _ lawsFree) trivial⟩

def operator : ClosedTerm Const (object ⇒ object ⇒ object) :=
  .lam (.lam (ordered core epsilon (.var (.vs .vz)) (.var .vz)))

theorem rename_ordered (rho : Rename Unit Γ Ξ) (left right : Term Const Γ object) :
    HOL.rename rho (ordered core epsilon left right) =
      ordered core epsilon (HOL.rename rho left) (HOL.rename rho right) := by
  simpa only [HOL.subst_ofRename] using subst_ordered core epsilon (Subst.ofRename rho) left right

theorem operatorForm (context : Ctx Unit) :
    HOL.weakenCtx context (operator core epsilon) =
      .lam (.lam (ordered core epsilon (.var (.vs .vz)) (.var .vz))) := by
  induction context with
  | nil => rfl
  | cons type context ih =>
    rw [HOL.weakenCtx_cons, ih]
    simp only [HOL.weaken, HOL.rename, rename_ordered, Rename.lift]

/-- The ordinary closed operator can fill a compiler's pair-operation slot.
Its application reduces to the proved construction by two retained beta steps. -/
def operatorBeta (left right : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (.app (.app (weakenCtx Γ (operator core epsilon)) left) right)
      (ordered core epsilon left right)) := by
  have first : ProofSyntax Const Δ (.eq
      (.app (.app (weakenCtx Γ (operator core epsilon)) left) right)
      (.app (.lam (ordered core epsilon (HOL.weaken left) (.var .vz))) right)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.eqApp right (ProofSyntax.beta left
      (.lam (ordered core epsilon (.var (.vs .vz)) (.var .vz)))))
    simp only [operatorForm, instantiate, HOL.subst, subst_ordered, Subst.lift, Subst.single, HOL.weaken]
  have second : ProofSyntax Const Δ (.eq
      (.app (.lam (ordered core epsilon (HOL.weaken left) (.var .vz))) right)
      (ordered core epsilon left right)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta right
      (ordered core epsilon (HOL.weaken left) (.var .vz)))
    simp only [instantiate, subst_ordered, HOL.subst, Subst.single, substituteWeak]
  exact .eqTrans first second

theorem operatorBeta_free (left right : Term Const Γ object) :
    (operatorBeta (Δ := Δ) core epsilon left right).FunctionExtensionalityFree := by
  simp [operatorBeta, ProofSyntax.FunctionExtensionalityFree]

end Mettapedia.Logic.HOL.SetPairingProofs
