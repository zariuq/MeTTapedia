import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.FinitaryRuleSystem.Tree
import Mathlib.Algebra.BigOperators.Fin

/-!
# Inspectable syntax for the extensional HOL derivation calculus

Every constructor of `ExtDerivation` has a Type-valued counterpart, indexed
by the exact source context, ordered assumptions and conclusion. Hypotheses
name occurrences in that assumption list; two equal formulas at different
positions remain different proof choices. Binder and equality rules retain
their original typed terms and context changes.

Erasure establishes the unchanged proposition-valued calculus. Conversely,
every derivation has some syntax. This converse eliminates into `Nonempty`,
not into a chosen proof tree: proposition-valued admission cannot recover
which proof was supplied. Structural observations reuse the generic finite
derivation-tree carrier and its node count, without adding a replay checker.
They are observations, not a serialization or an injective code for all rule
parameters. The full indexed syntax retains those parameters separately.

The controls distinguish ordinary and detoured proofs of the same implication,
and separate duplicate assumption occurrences. Their erased intrinsic
admissions coincide, so no decoder from that coarse admission recovers both.
This supplies proof data, not a raw-byte trust boundary or a selected kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u}

/-- All 29 rules of the existing extensional calculus, with retained proof
syntax rather than proposition-valued premises. -/
inductive ProofSyntax (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Type (max u v) where
  | hyp {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (occurrence : Fin Δ.length) :
      ProofSyntax Const Δ (Δ.get occurrence)
  | topI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      ProofSyntax Const Δ .top
  | botE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      ProofSyntax Const Δ .bot → ProofSyntax Const Δ φ
  | andI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} :
      ProofSyntax Const Δ φ → ProofSyntax Const Δ ψ → ProofSyntax Const Δ (.and φ ψ)
  | andEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} :
      ProofSyntax Const Δ (.and φ ψ) → ProofSyntax Const Δ φ
  | andER {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} :
      ProofSyntax Const Δ (.and φ ψ) → ProofSyntax Const Δ ψ
  | orIL {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} :
      ProofSyntax Const Δ φ → ProofSyntax Const Δ (.or φ ψ)
  | orIR {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} :
      ProofSyntax Const Δ ψ → ProofSyntax Const Δ (.or φ ψ)
  | orE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ χ : Formula Const Γ} :
      ProofSyntax Const Δ (.or φ ψ) → ProofSyntax Const (φ :: Δ) χ →
      ProofSyntax Const (ψ :: Δ) χ → ProofSyntax Const Δ χ
  | impI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} :
      ProofSyntax Const (φ :: Δ) ψ → ProofSyntax Const Δ (.imp φ ψ)
  | impE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} :
      ProofSyntax Const Δ (.imp φ ψ) → ProofSyntax Const Δ φ → ProofSyntax Const Δ ψ
  | notI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      ProofSyntax Const (φ :: Δ) .bot → ProofSyntax Const Δ (.not φ)
  | notE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      ProofSyntax Const Δ (.not φ) → ProofSyntax Const Δ φ → ProofSyntax Const Δ .bot
  | allI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
      ProofSyntax Const (weakenHyps (Base := Base) (σ := σ) Δ) φ →
      ProofSyntax Const Δ (.all φ)
  | allE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} (t : Term Const Γ σ) :
      ProofSyntax Const Δ (.all φ) → ProofSyntax Const Δ (instantiate (Base := Base) t φ)
  | exI {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} (t : Term Const Γ σ) :
      ProofSyntax Const Δ (instantiate (Base := Base) t φ) → ProofSyntax Const Δ (.ex φ)
  | exE {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {ψ : Formula Const Γ} :
      ProofSyntax Const Δ (.ex φ) →
      ProofSyntax Const (φ :: weakenHyps (Base := Base) (σ := σ) Δ)
        (weaken (Base := Base) (σ := σ) ψ) → ProofSyntax Const Δ ψ
  | eqRefl {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {τ : Ty Base} (t : Term Const Γ τ) :
      ProofSyntax Const Δ (.eq t t)
  | eqSymm {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u : Term Const Γ τ} :
      ProofSyntax Const Δ (.eq t u) → ProofSyntax Const Δ (.eq u t)
  | eqTrans {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {τ : Ty Base} {t u v : Term Const Γ τ} :
      ProofSyntax Const Δ (.eq t u) → ProofSyntax Const Δ (.eq u v) →
      ProofSyntax Const Δ (.eq t v)
  | eqPropI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {p q : Formula Const Γ} :
      ProofSyntax Const Δ (.imp p q) → ProofSyntax Const Δ (.imp q p) →
      ProofSyntax Const Δ (.eq p q)
  | eqPropEL {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {p q : Formula Const Γ} :
      ProofSyntax Const Δ (.eq p q) → ProofSyntax Const Δ (.imp p q)
  | eqPropER {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {p q : Formula Const Γ} :
      ProofSyntax Const Δ (.eq p q) → ProofSyntax Const Δ (.imp q p)
  | eqApp {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} (t : Term Const Γ σ) :
      ProofSyntax Const Δ (.eq f g) → ProofSyntax Const Δ (.eq (.app f t) (.app g t))
  | eqAppArg {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) {t u : Term Const Γ σ} :
      ProofSyntax Const Δ (.eq t u) → ProofSyntax Const Δ (.eq (.app f t) (.app f u))
  | eqLam {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {t u : Term Const (σ :: Γ) τ} :
      ProofSyntax Const (weakenHyps (Base := Base) (σ := σ) Δ) (.eq t u) →
      ProofSyntax Const Δ (.eq (.lam t) (.lam u))
  | funExt {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} {f g : Term Const Γ (σ ⇒ τ)} :
      ProofSyntax Const Δ
        (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
          (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))) →
      ProofSyntax Const Δ (.eq f g)
  | beta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (t : Term Const Γ σ) (body : Term Const (σ :: Γ) τ) :
      ProofSyntax Const Δ (.eq (.app (.lam body) t) (instantiate (Base := Base) t body))
  | eta {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ τ : Ty Base} (f : Term Const Γ (σ ⇒ τ)) :
      ProofSyntax Const Δ (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f)

namespace ProofSyntax

variable {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

/-- Structural erasure establishes the original judgment at exactly the
syntax's indices. It neither changes the calculus nor checks raw bytes. -/
theorem erase {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ProofSyntax Const Δ φ → ExtDerivation Const Δ φ
  | .hyp occurrence => .hyp (List.get_mem _ occurrence)
  | .topI => .topI
  | .botE proof => .botE proof.erase
  | .andI left right => .andI left.erase right.erase
  | .andEL proof => .andEL proof.erase
  | .andER proof => .andER proof.erase
  | .orIL proof => .orIL proof.erase
  | .orIR proof => .orIR proof.erase
  | .orE cases left right => .orE cases.erase left.erase right.erase
  | .impI proof => .impI proof.erase
  | .impE function argument => .impE function.erase argument.erase
  | .notI proof => .notI proof.erase
  | .notE negative positive => .notE negative.erase positive.erase
  | .allI proof => .allI proof.erase
  | .allE term proof => .allE term proof.erase
  | .exI term proof => .exI term proof.erase
  | .exE existsProof body => .exE existsProof.erase body.erase
  | .eqRefl term => .eqRefl term
  | .eqSymm proof => .eqSymm proof.erase
  | .eqTrans left right => .eqTrans left.erase right.erase
  | .eqPropI forward backward => .eqPropI forward.erase backward.erase
  | .eqPropEL proof => .eqPropEL proof.erase
  | .eqPropER proof => .eqPropER proof.erase
  | .eqApp term proof => .eqApp term proof.erase
  | .eqAppArg function proof => .eqAppArg function proof.erase
  | .eqLam proof => .eqLam proof.erase
  | .funExt proof => .funExt proof.erase
  | .beta term body => .beta term body
  | .eta function => .eta function

/-- Existence of syntax is proved by Prop-to-Prop induction. No canonical
proof tree, hypothesis occurrence or proof-search procedure is extracted. -/
theorem nonempty_of_derivation (derivation : ExtDerivation Const Δ φ) :
    Nonempty (ProofSyntax Const Δ φ) := by
  induction derivation with
  | hyp member =>
      obtain ⟨occurrence, equal⟩ := List.mem_iff_get.mp member
      cases equal
      exact ⟨.hyp occurrence⟩
  | topI => exact ⟨.topI⟩
  | botE _ ih => rcases ih with ⟨proof⟩; exact ⟨.botE proof⟩
  | andI _ _ ihLeft ihRight =>
      rcases ihLeft with ⟨left⟩; rcases ihRight with ⟨right⟩; exact ⟨.andI left right⟩
  | andEL _ ih => rcases ih with ⟨proof⟩; exact ⟨.andEL proof⟩
  | andER _ ih => rcases ih with ⟨proof⟩; exact ⟨.andER proof⟩
  | orIL _ ih => rcases ih with ⟨proof⟩; exact ⟨.orIL proof⟩
  | orIR _ ih => rcases ih with ⟨proof⟩; exact ⟨.orIR proof⟩
  | orE _ _ _ ihCases ihLeft ihRight =>
      rcases ihCases with ⟨cases⟩; rcases ihLeft with ⟨left⟩; rcases ihRight with ⟨right⟩
      exact ⟨.orE cases left right⟩
  | impI _ ih => rcases ih with ⟨proof⟩; exact ⟨.impI proof⟩
  | impE _ _ ihFunction ihArgument =>
      rcases ihFunction with ⟨function⟩; rcases ihArgument with ⟨argument⟩
      exact ⟨.impE function argument⟩
  | notI _ ih => rcases ih with ⟨proof⟩; exact ⟨.notI proof⟩
  | notE _ _ ihNegative ihPositive =>
      rcases ihNegative with ⟨negative⟩; rcases ihPositive with ⟨positive⟩
      exact ⟨.notE negative positive⟩
  | allI _ ih => rcases ih with ⟨proof⟩; exact ⟨.allI proof⟩
  | allE term _ ih => rcases ih with ⟨proof⟩; exact ⟨.allE term proof⟩
  | exI term _ ih => rcases ih with ⟨proof⟩; exact ⟨.exI term proof⟩
  | exE _ _ ihExists ihBody =>
      rcases ihExists with ⟨existsProof⟩; rcases ihBody with ⟨body⟩
      exact ⟨.exE existsProof body⟩
  | eqRefl term => exact ⟨.eqRefl term⟩
  | eqSymm _ ih => rcases ih with ⟨proof⟩; exact ⟨.eqSymm proof⟩
  | eqTrans _ _ ihLeft ihRight =>
      rcases ihLeft with ⟨left⟩; rcases ihRight with ⟨right⟩; exact ⟨.eqTrans left right⟩
  | eqPropI _ _ ihForward ihBackward =>
      rcases ihForward with ⟨forward⟩; rcases ihBackward with ⟨backward⟩
      exact ⟨.eqPropI forward backward⟩
  | eqPropEL _ ih => rcases ih with ⟨proof⟩; exact ⟨.eqPropEL proof⟩
  | eqPropER _ ih => rcases ih with ⟨proof⟩; exact ⟨.eqPropER proof⟩
  | eqApp term _ ih => rcases ih with ⟨proof⟩; exact ⟨.eqApp term proof⟩
  | eqAppArg function _ ih => rcases ih with ⟨proof⟩; exact ⟨.eqAppArg function proof⟩
  | eqLam _ ih => rcases ih with ⟨proof⟩; exact ⟨.eqLam proof⟩
  | funExt _ ih => rcases ih with ⟨proof⟩; exact ⟨.funExt proof⟩
  | beta term body => exact ⟨.beta term body⟩
  | eta function => exact ⟨.eta function⟩

theorem nonempty_iff : Nonempty (ProofSyntax Const Δ φ) ↔ ExtDerivation Const Δ φ :=
  ⟨fun ⟨proof⟩ => proof.erase, nonempty_of_derivation⟩

/-! ## Structural observations with every node's full sequent -/

structure Sequent (Const : Ty Base → Type v) where
  context : Ctx Base
  assumptions : List (Formula Const context)
  conclusion : Formula Const context

inductive RuleTag where
  | hyp | topI | botE | andI | andEL | andER | orIL | orIR | orE | impI | impE
  | notI | notE | allI | allE | exI | exE | eqRefl | eqSymm | eqTrans
  | eqPropI | eqPropEL | eqPropER | eqApp | eqAppArg | eqLam | funExt | beta | eta
  deriving DecidableEq, Repr

structure RuleObservation where
  rule : RuleTag
  hypothesisOccurrence : Option Nat := none
  deriving DecidableEq, Repr

abbrev Tree (Const : Ty Base → Type v) :=
  Mettapedia.Logic.Derivation (Sequent Const) RuleObservation

private def observationNode (sequent : Sequent Const) (rule : RuleObservation)
    (children : List (Tree Const)) : Tree Const :=
  .node sequent rule children.length children.get

@[simp] theorem observationNode_nodeCount (sequent : Sequent Const) (rule : RuleObservation)
    (children : List (Tree Const)) :
    (observationNode sequent rule children).nodeCount =
      1 + ∑ i : Fin children.length, (children.get i).nodeCount := rfl

/-- An ordered structural tree. It retains each node's exact sequent and
each local hypothesis position, while omitting some rule-instance terms. -/
def observe {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) : Tree Const :=
  let sequent : Sequent Const := ⟨Γ, Δ, φ⟩
  match proof with
  | .hyp occurrence => observationNode sequent ⟨.hyp, some occurrence.val⟩ []
  | .topI => observationNode sequent ⟨.topI, none⟩ []
  | .botE proof => observationNode sequent ⟨.botE, none⟩ [proof.observe]
  | .andI left right => observationNode sequent ⟨.andI, none⟩ [left.observe, right.observe]
  | .andEL proof => observationNode sequent ⟨.andEL, none⟩ [proof.observe]
  | .andER proof => observationNode sequent ⟨.andER, none⟩ [proof.observe]
  | .orIL proof => observationNode sequent ⟨.orIL, none⟩ [proof.observe]
  | .orIR proof => observationNode sequent ⟨.orIR, none⟩ [proof.observe]
  | .orE cases left right => observationNode sequent ⟨.orE, none⟩ [cases.observe, left.observe, right.observe]
  | .impI proof => observationNode sequent ⟨.impI, none⟩ [proof.observe]
  | .impE function argument => observationNode sequent ⟨.impE, none⟩ [function.observe, argument.observe]
  | .notI proof => observationNode sequent ⟨.notI, none⟩ [proof.observe]
  | .notE negative positive => observationNode sequent ⟨.notE, none⟩ [negative.observe, positive.observe]
  | .allI proof => observationNode sequent ⟨.allI, none⟩ [proof.observe]
  | .allE _ proof => observationNode sequent ⟨.allE, none⟩ [proof.observe]
  | .exI _ proof => observationNode sequent ⟨.exI, none⟩ [proof.observe]
  | .exE existsProof body => observationNode sequent ⟨.exE, none⟩ [existsProof.observe, body.observe]
  | .eqRefl _ => observationNode sequent ⟨.eqRefl, none⟩ []
  | .eqSymm proof => observationNode sequent ⟨.eqSymm, none⟩ [proof.observe]
  | .eqTrans left right => observationNode sequent ⟨.eqTrans, none⟩ [left.observe, right.observe]
  | .eqPropI forward backward => observationNode sequent ⟨.eqPropI, none⟩ [forward.observe, backward.observe]
  | .eqPropEL proof => observationNode sequent ⟨.eqPropEL, none⟩ [proof.observe]
  | .eqPropER proof => observationNode sequent ⟨.eqPropER, none⟩ [proof.observe]
  | .eqApp _ proof => observationNode sequent ⟨.eqApp, none⟩ [proof.observe]
  | .eqAppArg _ proof => observationNode sequent ⟨.eqAppArg, none⟩ [proof.observe]
  | .eqLam proof => observationNode sequent ⟨.eqLam, none⟩ [proof.observe]
  | .funExt proof => observationNode sequent ⟨.funExt, none⟩ [proof.observe]
  | .beta _ _ => observationNode sequent ⟨.beta, none⟩ []
  | .eta _ => observationNode sequent ⟨.eta, none⟩ []

theorem observe_conclusion (proof : ProofSyntax Const Δ φ) :
    proof.observe.concl = ⟨Γ, Δ, φ⟩ := by
  cases proof <;> rfl

def nodeCount (proof : ProofSyntax Const Δ φ) : Nat := proof.observe.nodeCount

theorem nodeCount_pos (proof : ProofSyntax Const Δ φ) : 0 < proof.nodeCount :=
  proof.observe.nodeCount_pos

def rootObservation (proof : ProofSyntax Const Δ φ) : RuleObservation :=
  match proof.observe with
  | .node _ rule _ _ => rule

/-! ## Erased admission cannot identify a supplied proof tree -/

/-- The existing intrinsic admission shape: exact assumptions/conclusion
together with a proposition-valued derivation. -/
def intrinsicAdmission (proof : ProofSyntax Const Δ φ) :
    { claim : List (Formula Const Γ) × Formula Const Γ //
      ExtDerivation Const claim.1 claim.2 } :=
  ⟨(Δ, φ), proof.erase⟩

theorem erased_eq (first second : ProofSyntax Const Δ φ) : first.erase = second.erase :=
  Subsingleton.elim _ _

theorem intrinsicAdmission_eq (first second : ProofSyntax Const Δ φ) :
    first.intrinsicAdmission = second.intrinsicAdmission := Subtype.ext rfl

/-- Even a noncomputable proposed decoder cannot recover two distinguished
trees from their common intrinsic admission. -/
theorem no_common_decoder (first second : ProofSyntax Const Δ φ) (different : first ≠ second) :
    ¬ ∃ decode :
      { claim : List (Formula Const Γ) × Formula Const Γ //
        ExtDerivation Const claim.1 claim.2 } → ProofSyntax Const Δ φ,
      decode first.intrinsicAdmission = first ∧ decode second.intrinsicAdmission = second := by
  rintro ⟨decode, recoversFirst, recoversSecond⟩
  apply different
  exact recoversFirst.symm.trans
    ((congrArg decode (intrinsicAdmission_eq first second)).trans recoversSecond)

namespace Controls

variable (φ : Formula Const Γ)

def direct : ProofSyntax Const [] (.imp φ φ) := .impI (.hyp ⟨0, by simp⟩)

def detour : ProofSyntax Const [] (.imp φ φ) :=
  .impI (.andEL (.andI (.hyp ⟨0, by simp⟩) (.hyp ⟨0, by simp⟩)))

theorem counts : (direct φ).nodeCount = 2 ∧ (detour φ).nodeCount = 5 := by
  constructor
  · simp [nodeCount, direct, observe, observationNode]
  · simp [nodeCount, detour, observe, observationNode, Fin.sum_univ_succ]

theorem distinct_trees : direct φ ≠ detour φ := by
  intro same
  have equal := congrArg nodeCount same
  rw [(counts φ).1, (counts φ).2] at equal
  omega

theorem different_observations : (direct φ).observe ≠ (detour φ).observe := by
  intro same
  have equal := congrArg Mettapedia.Logic.Derivation.nodeCount same
  change (direct φ).nodeCount = (detour φ).nodeCount at equal
  rw [(counts φ).1, (counts φ).2] at equal
  omega

theorem same_intrinsic_admission : (direct φ).intrinsicAdmission = (detour φ).intrinsicAdmission :=
  intrinsicAdmission_eq _ _

theorem no_decoder :
    ¬ ∃ decode :
      { claim : List (Formula Const Γ) × Formula Const Γ //
        ExtDerivation Const claim.1 claim.2 } → ProofSyntax Const [] (.imp φ φ),
      decode (direct φ).intrinsicAdmission = direct φ ∧
        decode (detour φ).intrinsicAdmission = detour φ :=
  no_common_decoder _ _ (distinct_trees φ)

def firstOccurrence : ProofSyntax Const [φ, φ] φ := .hyp ⟨0, by simp⟩
def secondOccurrence : ProofSyntax Const [φ, φ] φ := .hyp ⟨1, by simp⟩

theorem occurrence_observations :
    (firstOccurrence φ).rootObservation = ⟨.hyp, some 0⟩ ∧
    (secondOccurrence φ).rootObservation = ⟨.hyp, some 1⟩ := ⟨rfl, rfl⟩

theorem duplicate_occurrences_distinct : firstOccurrence φ ≠ secondOccurrence φ := by
  intro same
  have equal := congrArg rootObservation same
  rw [(occurrence_observations φ).1, (occurrence_observations φ).2] at equal
  cases equal

/-- The object binder and its typed variable are present in the proof data. -/
def binderReflexivity (σ : Ty Base) :
    ProofSyntax Const (Γ := Γ) [] (.all (.eq (.var (.vz : Var (σ :: Γ) σ)) (.var .vz))) :=
  .allI (.eqRefl (.var .vz))

theorem binder_erasure (σ : Ty Base) :
    ExtDerivation Const (Γ := Γ) [] (.all (.eq (.var (.vz : Var (σ :: Γ) σ)) (.var .vz))) :=
  (binderReflexivity (Const := Const) (Γ := Γ) σ).erase

end Controls

end ProofSyntax
end Mettapedia.Logic.HOL
