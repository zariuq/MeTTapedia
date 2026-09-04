import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Languages.Megalodon.ImplicationalKernel

/-!
# Independent semantics for the Megalodon implicational kernel

The implicational fragment already has two operational presentations: an
intrinsic proof-term checker and an authored CertificateGSLT compiler.  This
module adds a third, independently stated face: valuation semantics in `Prop`.

The NIK theory family below deliberately separates:

* `Scope`: existence of an intrinsic proof accepted by `infer`;
* `Meaning`: validity under every valuation satisfying the context;
* `checker`: executable replay of one submitted intrinsic proof.

Thus exact checker authority is proved only for the declared proof scope, and
scope soundness is separately proved into semantic meaning.  No completeness
claim for the valuation semantics, full Megalodon, or HOTG is made here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.Megalodon.ImplicationalKernel
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## A meaning independent of proof syntax -/

/-- An interpretation assigns a proposition to every atomic formula. -/
abbrev Valuation := Nat → Prop

/-- Ordinary implicational valuation semantics. -/
def Holds (valuation : Valuation) : Formula → Prop
  | .atom index => valuation index
  | .imp domain codomain => Holds valuation domain → Holds valuation codomain

/-- Every assumption in a context is true under the valuation. -/
def ContextHolds (valuation : Valuation) (context : List Formula) : Prop :=
  ∀ formula ∈ context, Holds valuation formula

/-- Semantic consequence for the authored context and conclusion. -/
def Entails (context : List Formula) (formula : Formula) : Prop :=
  ∀ valuation, ContextHolds valuation context → Holds valuation formula

/-- Intrinsic theoremhood is the image of the independently defined inference
function, not the semantic predicate itself. -/
def Derivable (context : List Formula) (formula : Formula) : Prop :=
  ∃ proof, infer context proof = some formula

private theorem contextHolds_cons
    {valuation : Valuation} {head : Formula} {tail : List Formula}
    (headHolds : Holds valuation head)
    (tailHolds : ContextHolds valuation tail) :
    ContextHolds valuation (head :: tail) := by
  intro formula member
  rcases List.mem_cons.mp member with equal | member
  · subst formula
    exact headHolds
  · exact tailHolds formula member

/-- The intrinsic Megalodon fragment is sound for the independently authored
valuation semantics. -/
theorem infer_sound
    {context : List Formula} {proof : Proof} {formula : Formula}
    (inferred : infer context proof = some formula) :
    Entails context formula := by
  induction proof generalizing context formula with
  | hyp index =>
      intro valuation contextHolds
      simp only [infer] at inferred
      exact contextHolds formula (List.mem_of_getElem? inferred)
  | app function argument functionIH argumentIH =>
      simp only [infer] at inferred
      cases hfunction : infer context function with
      | none => simp [hfunction] at inferred
      | some functionType =>
          cases functionType with
          | atom atomIndex => simp [hfunction] at inferred
          | imp domain codomain =>
              cases hargument : infer context argument with
              | none => simp [hfunction, hargument] at inferred
              | some actual =>
                  by_cases equal : actual = domain
                  · subst actual
                    simp [hfunction, hargument] at inferred
                    subst formula
                    intro valuation contextHolds
                    exact functionIH hfunction valuation contextHolds
                      (argumentIH hargument valuation contextHolds)
                  · simp [hfunction, hargument, equal] at inferred
  | lam domain body bodyIH =>
      simp only [infer] at inferred
      cases hbody : infer (domain :: context) body with
      | none => simp [hbody] at inferred
      | some codomain =>
          simp [hbody] at inferred
          subst formula
          intro valuation contextHolds domainHolds
          exact bodyIH hbody valuation
            (contextHolds_cons domainHolds contextHolds)

/-- Intrinsic theoremhood projects into semantic consequence. -/
theorem derivable_sound
    {context : List Formula} {formula : Formula}
    (derivable : Derivable context formula) : Entails context formula := by
  obtain ⟨proof, inferred⟩ := derivable
  exact infer_sound inferred

/-! ## Source-level semantics for arbitrary rule payloads -/

/-- The raw implication constructor used by the authored calculus. -/
def rawImp (domain codomain : Pattern) : Pattern :=
  implicationPattern domain codomain

/-- The raw empty-context constructor used by the authored calculus. -/
def rawContextNil : Pattern :=
  .apply "MCtxNil" []

/-- The raw context-extension constructor used by the authored calculus. -/
def rawContextCons (formula context : Pattern) : Pattern :=
  contextConsPattern formula context

/-- The raw proof judgment used by the authored calculus. -/
def rawProves (context formula : Pattern) : Pattern :=
  judgmentPattern context formula

/-- Interpret every pattern not headed by binary `MImp` as an atomic
proposition.  This deliberately gives malformed or guest-extended payloads a
meaning instead of assuming that every rule argument decodes to `Formula`. -/
def RawFormulaHolds (atomic : Pattern → Prop) : Pattern → Prop
  | _pattern@(.apply "MImp" [domain, codomain]) =>
      RawFormulaHolds atomic domain → RawFormulaHolds atomic codomain
  | pattern => atomic pattern
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp
  all_goals omega

/-- Interpret explicit context constructors structurally and every other
context pattern through an independently supplied base-context predicate. -/
def RawContextHolds (atomic : Pattern → Prop)
    (baseContext : Pattern → Prop) : Pattern → Prop
  | .apply "MCtxNil" [] => True
  | .apply "MCtxCons" [formula, context] =>
      RawFormulaHolds atomic formula ∧
        RawContextHolds atomic baseContext context
  | pattern => baseContext pattern
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp
  all_goals omega

/-- Raw semantic consequence, polymorphic in atomic and opaque-context
interpretations. -/
def RawEntails (context formula : Pattern) : Prop :=
  ∀ atomic baseContext,
    RawContextHolds atomic baseContext context →
      RawFormulaHolds atomic formula

/-- Only well-shaped proof judgments make semantic demands.  This is the
source-level interpretation consumed by generic derivation induction. -/
def RawJudgmentMeaning : Pattern → Prop
  | .apply "MProves" [context, formula] => RawEntails context formula
  | _ => True

@[simp] theorem rawFormulaHolds_imp
    (atomic : Pattern → Prop) (domain codomain : Pattern) :
    RawFormulaHolds atomic (rawImp domain codomain) ↔
      (RawFormulaHolds atomic domain → RawFormulaHolds atomic codomain) := by
  simp [RawFormulaHolds, rawImp, implicationPattern]

@[simp] theorem rawContextHolds_nil
    (atomic baseContext : Pattern → Prop) :
    RawContextHolds atomic baseContext rawContextNil := by
  simp [RawContextHolds, rawContextNil]

@[simp] theorem rawContextHolds_cons
    (atomic baseContext : Pattern → Prop) (formula context : Pattern) :
    RawContextHolds atomic baseContext (rawContextCons formula context) ↔
      (RawFormulaHolds atomic formula ∧
        RawContextHolds atomic baseContext context) := by
  simp [RawContextHolds, rawContextCons, contextConsPattern]

@[simp] theorem rawJudgmentMeaning_proves
    (context formula : Pattern) :
    RawJudgmentMeaning (rawProves context formula) ↔
      RawEntails context formula := by
  rfl

/-- Hypothesis-zero is semantically valid for arbitrary raw payloads. -/
theorem raw_hypothesis_zero_sound (context formula : Pattern) :
    RawJudgmentMeaning (rawProves (rawContextCons formula context) formula) := by
  intro atomic baseContext contextHolds
  exact (rawContextHolds_cons atomic baseContext formula context).mp
    contextHolds |>.1

/-- Weakening is semantically valid for arbitrary raw payloads. -/
theorem raw_weakening_sound (context formula head : Pattern)
    (premise : RawJudgmentMeaning (rawProves context formula)) :
    RawJudgmentMeaning
      (rawProves (rawContextCons head context) formula) := by
  intro atomic baseContext contextHolds
  exact premise atomic baseContext
    ((rawContextHolds_cons atomic baseContext head context).mp
      contextHolds).2

/-- Implication introduction is semantically valid for arbitrary raw
payloads. -/
theorem raw_implication_introduction_sound
    (context domain codomain : Pattern)
    (premise : RawJudgmentMeaning
      (rawProves (rawContextCons domain context) codomain)) :
    RawJudgmentMeaning (rawProves context (rawImp domain codomain)) := by
  intro atomic baseContext contextHolds
  rw [rawFormulaHolds_imp]
  intro domainHolds
  exact premise atomic baseContext
    ((rawContextHolds_cons atomic baseContext domain context).mpr
      ⟨domainHolds, contextHolds⟩)

/-- Implication elimination is semantically valid for arbitrary raw
payloads. -/
theorem raw_implication_elimination_sound
    (context domain codomain : Pattern)
    (functionPremise : RawJudgmentMeaning
      (rawProves context (rawImp domain codomain)))
    (argumentPremise : RawJudgmentMeaning (rawProves context domain)) :
    RawJudgmentMeaning (rawProves context codomain) := by
  intro atomic baseContext contextHolds
  exact (rawFormulaHolds_imp atomic domain codomain).mp
    (functionPremise atomic baseContext contextHolds)
    (argumentPremise atomic baseContext contextHolds)

/-- Every local application admitted by the authored Megalodon GSLT preserves
the raw semantic interpretation, including arbitrary ground rule payloads. -/
theorem authoredRuleApplication_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (premisesMeaning : ∀ premise ∈ premises,
      RawJudgmentMeaning premise) :
    RawJudgmentMeaning conclusion := by
  cases ruleApplication_shape application with
  | hypothesisZero context formula =>
      exact raw_hypothesis_zero_sound context formula
  | weakening context formula head =>
      apply raw_weakening_sound context formula head
      exact premisesMeaning (rawProves context formula) (by simp [rawProves])
  | implicationIntroduction context domain codomain =>
      apply raw_implication_introduction_sound context domain codomain
      exact premisesMeaning
        (rawProves (rawContextCons domain context) codomain)
        (by simp [rawProves, rawContextCons])
  | implicationElimination context domain codomain =>
      apply raw_implication_elimination_sound context domain codomain
      · exact premisesMeaning
          (rawProves context (rawImp domain codomain))
          (by simp [rawProves, rawImp])
      · exact premisesMeaning (rawProves context domain)
          (by simp [rawProves])

/-- Every arbitrary raw article accepted by the authored GSLT checker has the
source-level meaning induced by its rule table. -/
theorem acceptedRawArticle_meaning
    {goal : Pattern} {article : RawProof}
    (accepted : checkRaw validated goal article = true) :
    RawJudgmentMeaning goal := by
  obtain ⟨derivation⟩ := checkRaw_soundness accepted
  exact Derivation.sound_of_ruleApplications RawJudgmentMeaning
    authoredRuleApplication_sound derivation

/-! ### Agreement with the intrinsic encoding -/

/-- Decode the unary natural-number patterns used by the intrinsic encoder. -/
def decodeNat : Pattern → Option Nat
  | .apply "MZero" [] => some 0
  | .apply "MSucc" [inner] => (decodeNat inner).map Nat.succ
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp
  all_goals omega

@[simp] theorem decodeNat_encodeNat (index : Nat) :
    decodeNat (encodeNat index) = some index := by
  induction index with
  | zero => simp [encodeNat, decodeNat]
  | succ index indexIH => simp [encodeNat, decodeNat, indexIH]

/-- Interpret precisely encoded atomic formulas through an intrinsic
valuation; every other non-implication raw pattern is false in this particular
model. -/
def EncodedAtomic (valuation : Valuation) : Pattern → Prop
  | .apply "MAtom" [number] =>
      ∃ index, decodeNat number = some index ∧ valuation index
  | _ => False

/-- Raw formula interpretation agrees with intrinsic formula semantics on the
canonical encoding. -/
theorem rawFormulaHolds_encodeFormula
    (valuation : Valuation) (formula : Formula) :
    RawFormulaHolds (EncodedAtomic valuation) (encodeFormula formula) ↔
      Holds valuation formula := by
  induction formula with
  | atom index =>
      simp [RawFormulaHolds, EncodedAtomic, encodeFormula, Holds,
        decodeNat_encodeNat]
  | imp domain codomain domainIH codomainIH =>
      simp [RawFormulaHolds, encodeFormula, Holds,
        domainIH, codomainIH]

private theorem contextHolds_cons_iff
    (valuation : Valuation) (formula : Formula) (context : List Formula) :
    ContextHolds valuation (formula :: context) ↔
      Holds valuation formula ∧ ContextHolds valuation context := by
  constructor
  · intro contextHolds
    constructor
    · exact contextHolds formula (by simp)
    · intro member memberInContext
      exact contextHolds member (by simp [memberInContext])
  · rintro ⟨formulaHolds, contextHolds⟩ member membership
    rcases List.mem_cons.mp membership with equal | memberInContext
    · subst member
      exact formulaHolds
    · exact contextHolds member memberInContext

/-- Raw context interpretation agrees with intrinsic context semantics on the
canonical encoding. -/
theorem rawContextHolds_encodeContext
    (valuation : Valuation) (context : List Formula) :
    RawContextHolds (EncodedAtomic valuation) (fun _ => False)
        (encodeContext context) ↔
      ContextHolds valuation context := by
  induction context with
  | nil => simp [RawContextHolds, encodeContext, ContextHolds]
  | cons formula context contextIH =>
      rw [contextHolds_cons_iff]
      simp [RawContextHolds, encodeContext,
        rawFormulaHolds_encodeFormula, contextIH]

/-- Source-level raw meaning specializes to the independently authored
intrinsic valuation meaning at every canonical endpoint. -/
theorem rawMeaning_encoded_implies_entails
    {context : List Formula} {formula : Formula}
    (rawMeaning : RawJudgmentMeaning
      (rawProves (encodeContext context) (encodeFormula formula))) :
    Entails context formula := by
  have rawEntails :
      RawEntails (encodeContext context) (encodeFormula formula) :=
    (rawJudgmentMeaning_proves _ _).mp rawMeaning
  intro valuation contextHolds
  have rawContext :
      RawContextHolds (EncodedAtomic valuation) (fun _ => False)
        (encodeContext context) :=
    (rawContextHolds_encodeContext valuation context).mpr contextHolds
  have rawFormula :=
    rawEntails (EncodedAtomic valuation) (fun _ => False) rawContext
  exact (rawFormulaHolds_encodeFormula valuation formula).mp rawFormula

/-- Semantic no-invention for arbitrary externally authored raw articles at a
canonical intrinsic endpoint. -/
theorem checkedRawArticle_entails
    {context : List Formula} {formula : Formula} {article : RawProof}
    (accepted : checkRaw validated
      (rawProves (encodeContext context) (encodeFormula formula)) article = true) :
    Entails context formula :=
  rawMeaning_encoded_implies_entails (acceptedRawArticle_meaning accepted)

/-! ## Exact executable scope authority -/

/-- A profile-local theorem query. -/
structure Claim where
  context : List Formula
  formula : Formula
deriving DecidableEq, Repr

/-- Replay one intrinsic proof against one explicit claim. -/
def checker : Checker Claim Proof where
  check claim proof := decide (infer claim.context proof = some claim.formula)

/-- The executable checker is exact for intrinsic theoremhood. -/
theorem checker_authority :
    checker.Authority (fun claim => Derivable claim.context claim.formula) where
  sound := by
    intro claim proof accepted
    exact ⟨proof, of_decide_eq_true accepted⟩
  complete := by
    intro claim derivable
    obtain ⟨proof, inferred⟩ := derivable
    exact ⟨proof, by simp [checker, inferred]⟩

/-- One independently meaningful theory profile for the fragment. -/
def theory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := id
  Claim := fun _ => Claim
  Scope := fun _ claim => Derivable claim.context claim.formula
  Meaning := fun _ claim => Entails claim.context claim.formula
  scope_sound := by
    intro _ claim derivable
    exact derivable_sound derivable

/-- Proof-carrying NIK authority for the fragment's intrinsic theorem scope. -/
def contract : AuthorityContract theory where
  Certificate := fun _ => Proof
  checker := fun _ => checker
  scopeAuthority := fun _ => checker_authority

/-- The corresponding ordinary NIK authority family. -/
def family : AuthorityFamily Unit :=
  contract.toAuthorityFamily

/-- Accepted intrinsic evidence has independent semantic meaning, via the
authority projection rather than by identifying checking with truth. -/
theorem accepted_implies_meaning
    (claim : Claim) (proof : Proof)
    (accepted : (family.checker ()).check claim proof = true) :
    theory.Meaning () claim :=
  (family.projection ()).sound claim proof accepted

/-! ## The authored GSLT compiler inherits the same semantics -/

/-- Compilation cannot change the proposition synthesized by the independent
intrinsic inference function. -/
theorem compile_implies_infer
    {context : List Formula} {proof : Proof} {formula : Formula}
    {article : Mettapedia.GSLT.LanguageDef.InferenceChecker.RawProof}
    (compiled : compile context proof = some (formula, article)) :
    infer context proof = some formula := by
  induction proof generalizing context formula article with
  | hyp index =>
      induction context generalizing index formula article with
      | nil => simp [compile] at compiled
      | cons head tail tailIH =>
          cases index with
          | zero =>
              simp [compile, infer] at compiled ⊢
              exact compiled.1.symm ▸ rfl
          | succ index =>
              simp only [compile] at compiled
              cases hrecursive : compile tail (.hyp index) with
              | none => simp [hrecursive] at compiled
              | some result =>
                  rcases result with ⟨resultFormula, resultArticle⟩
                  simp [hrecursive] at compiled
                  rcases compiled with ⟨rfl, rfl⟩
                  simp only [infer]
                  exact tailIH index hrecursive
  | app function argument functionIH argumentIH =>
      simp only [compile] at compiled
      cases hfunction : compile context function with
      | none => simp [hfunction] at compiled
      | some functionResult =>
          rcases functionResult with ⟨functionType, functionArticle⟩
          cases functionType with
          | atom atomIndex => simp [hfunction] at compiled
          | imp domain codomain =>
              cases hargument : compile context argument with
              | none => simp [hfunction, hargument] at compiled
              | some argumentResult =>
                  rcases argumentResult with ⟨actual, argumentArticle⟩
                  by_cases equal : actual = domain
                  · subst actual
                    simp [hfunction, hargument] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    simp [infer, functionIH hfunction, argumentIH hargument]
                  · simp [hfunction, hargument, equal] at compiled
  | lam domain body bodyIH =>
      simp only [compile] at compiled
      cases hbody : compile (domain :: context) body with
      | none => simp [hbody] at compiled
      | some result =>
          rcases result with ⟨codomain, child⟩
          simp [hbody] at compiled
          rcases compiled with ⟨rfl, rfl⟩
          simp [infer, bodyIH hbody]

/-- Every successfully inferred intrinsic proof has a compiler-emitted
authored-GSLT article at exactly the inferred proposition. -/
theorem infer_implies_exists_compile
    {context : List Formula} {proof : Proof} {formula : Formula}
    (inferred : infer context proof = some formula) :
    ∃ article, compile context proof = some (formula, article) := by
  induction proof generalizing context formula with
  | hyp index =>
      induction context generalizing index formula with
      | nil => simp [infer] at inferred
      | cons head tail tailIH =>
          cases index with
          | zero =>
              simp [infer] at inferred
              subst formula
              simp [compile]
          | succ index =>
              simp only [infer] at inferred
              obtain ⟨child, compiled⟩ := tailIH index inferred
              simp [compile, compiled]
  | app function argument functionIH argumentIH =>
      simp only [infer] at inferred
      cases hfunction : infer context function with
      | none => simp [hfunction] at inferred
      | some functionType =>
          cases functionType with
          | atom atomIndex => simp [hfunction] at inferred
          | imp domain codomain =>
              cases hargument : infer context argument with
              | none => simp [hfunction, hargument] at inferred
              | some actual =>
                  by_cases equal : actual = domain
                  · subst actual
                    simp [hfunction, hargument] at inferred
                    subst formula
                    obtain ⟨functionArticle, functionCompiled⟩ :=
                      functionIH hfunction
                    obtain ⟨argumentArticle, argumentCompiled⟩ :=
                      argumentIH hargument
                    simp [compile, functionCompiled, argumentCompiled]
                  · simp [hfunction, hargument, equal] at inferred
  | lam domain body bodyIH =>
      simp only [infer] at inferred
      cases hbody : infer (domain :: context) body with
      | none => simp [hbody] at inferred
      | some codomain =>
          simp [hbody] at inferred
          subst formula
          obtain ⟨child, compiled⟩ := bodyIH hbody
          simp [compile, compiled]

/-- Compiler inhabitation and intrinsic inference agree exactly at every
proposition, while the article remains an explicit retained witness. -/
theorem exists_compile_iff_infer
    {context : List Formula} {proof : Proof} {formula : Formula} :
    (∃ article, compile context proof = some (formula, article)) ↔
      infer context proof = some formula := by
  constructor
  · rintro ⟨article, compiled⟩
    exact compile_implies_infer compiled
  · exact infer_implies_exists_compile

/-- A compiler-emitted article is accepted by the authored GSLT checker and
its endpoint is valid under every valuation satisfying the source context. -/
def encodedJudgment (context : List Formula) (formula : Formula) :
    Pattern :=
  rawProves (encodeContext context) (encodeFormula formula)

/-- Replay an arbitrary authored GSLT article at a canonical intrinsic claim. -/
def authoredChecker : Checker Claim RawProof where
  check claim article :=
    checkRaw validated (encodedJudgment claim.context claim.formula) article

/-- The exact accepted image of the authored raw checker.  It is kept distinct
from both intrinsic theorem scope and external semantic meaning. -/
def AuthoredCertified (claim : Claim) : Prop :=
  ∃ article, authoredChecker.check claim article = true

/-- As for every checker, replay is exact for its explicitly named accepted
image. -/
theorem authoredChecker_authority :
    authoredChecker.Authority AuthoredCertified where
  sound := by
    intro claim article accepted
    exact ⟨article, accepted⟩
  complete := by
    intro claim certified
    exact certified

/-- Every intrinsic theorem has a compiler-produced certificate in the larger
authored raw-certificate scope. -/
theorem intrinsicScope_to_authoredCertified
    {claim : Claim}
    (intrinsic : Derivable claim.context claim.formula) :
    AuthoredCertified claim := by
  obtain ⟨proof, inferred⟩ := intrinsic
  obtain ⟨article, compiled⟩ := infer_implies_exists_compile inferred
  exact ⟨article, compile_checked compiled⟩

/-- Every raw certificate in the authored scope projects to independent
semantic meaning, including certificates not produced by `compile`. -/
theorem authoredCertified_to_meaning
    {claim : Claim} (certified : AuthoredCertified claim) :
    Entails claim.context claim.formula := by
  obtain ⟨article, accepted⟩ := certified
  exact checkedRawArticle_entails accepted

/-- The authored checker therefore occupies an honest middle layer:
intrinsic theoremhood is included in raw certificate acceptance, which is
included in semantic validity. -/
theorem intrinsic_authored_semantic_sandwich (claim : Claim) :
    (Derivable claim.context claim.formula → AuthoredCertified claim) ∧
      (AuthoredCertified claim → Entails claim.context claim.formula) :=
  ⟨intrinsicScope_to_authoredCertified, authoredCertified_to_meaning⟩

/-- NIK-compatible authority projection for arbitrary authored certificates.
Its exact scope is explicitly `AuthoredCertified`, not silently identified with
the intrinsic scope of `contract`. -/
def authoredProjection :
    authoredChecker.AuthorityProjection AuthoredCertified
      (fun claim => Entails claim.context claim.formula) where
  authority := authoredChecker_authority
  project := fun _ certified => authoredCertified_to_meaning certified

theorem compiled_article_checked_and_meaning
    {context : List Formula} {proof : Proof} {formula : Formula}
    {article : Mettapedia.GSLT.LanguageDef.InferenceChecker.RawProof}
    (compiled : compile context proof = some (formula, article)) :
    Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw validated
        (encodedJudgment context formula) article = true ∧
      Entails context formula := by
  have accepted := compile_checked compiled
  exact ⟨accepted, checkedRawArticle_entails accepted⟩

/-! ## Positive and negative controls -/

private def atomZero : Formula := .atom 0

def identityClaim : Claim where
  context := []
  formula := .imp atomZero atomZero

def identityProof : Proof :=
  .lam atomZero (.hyp 0)

/-- Positive control: implication identity is accepted. -/
theorem identity_accepted :
    (family.checker ()).check identityClaim identityProof = true := by
  decide

/-- Positive control: the accepted identity claim has independently stated
semantic meaning. -/
theorem identity_meaning : theory.Meaning () identityClaim :=
  accepted_implies_meaning identityClaim identityProof identity_accepted

/-- Positive raw-article control: the independently exposed authored article
is accepted through the arbitrary-certificate checker. -/
theorem identity_raw_article_accepted :
    authoredChecker.check identityClaim
      ImplicationalKernel.identityArticle = true := by
  change checkRaw validated ImplicationalKernel.identityGoal
    ImplicationalKernel.identityArticle = true
  exact ImplicationalKernel.identity_accepted

def wrongAuthoredClaim : Claim where
  context := []
  formula := .imp atomZero (.imp atomZero atomZero)

/-- Negative raw-article control: an accepted identity article cannot be
replayed at a different exact endpoint. -/
theorem identity_raw_article_rejected_at_wrong_claim :
    authoredChecker.check wrongAuthoredClaim
      ImplicationalKernel.identityArticle = false := by
  change checkRaw validated ImplicationalKernel.wrongExactGoal
    ImplicationalKernel.identityArticle = false
  exact ImplicationalKernel.wrong_exact_rejected

def bareAtomClaim : Claim where
  context := []
  formula := atomZero

/-- Countermodel control: an unconstrained atom is not semantically valid. -/
theorem bareAtom_not_meaning : ¬ theory.Meaning () bareAtomClaim := by
  intro meaningful
  have falseAtom : Holds (fun _ => False) atomZero :=
    meaningful (fun _ => False) (by simp [ContextHolds, bareAtomClaim])
  exact falseAtom

/-- Consequently the sound intrinsic kernel cannot derive the bare atom. -/
theorem bareAtom_not_in_scope : ¬ theory.Scope () bareAtomClaim := by
  intro inScope
  exact bareAtom_not_meaning (theory.scope_sound () bareAtomClaim inScope)

/-- Negative replay control: a hypothesis certificate cannot invent an
assumption in the empty context. -/
theorem bareAtom_hyp_rejected :
    (family.checker ()).check bareAtomClaim (.hyp 0) = false := by
  decide

#print axioms infer_sound
#print axioms checker_authority
#print axioms ImplicationalKernel.ruleApplication_shape
#print axioms exists_compile_iff_infer
#print axioms acceptedRawArticle_meaning
#print axioms checkedRawArticle_entails
#print axioms intrinsic_authored_semantic_sandwich
#print axioms compiled_article_checked_and_meaning
#print axioms bareAtom_not_meaning

end Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority
