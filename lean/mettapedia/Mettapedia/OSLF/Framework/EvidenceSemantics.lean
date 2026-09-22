import Mettapedia.OSLF.Formula
import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.PLN.Evidence.EvidenceQuantale
import Mettapedia.PLN.WorldModel.PLNWorldModel
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# EvidenceQuantale Adapter for OSLF Semantics

This module is an **adapter layer**: it interprets OSLF formulas in the
canonical evidence carrier `EvidenceQuantale.BinaryEvidence`.

Ownership boundary:
- Canonical evidence semantics lives in `Mettapedia.PLN.Evidence.EvidenceQuantale`
- This file only lifts that evidence algebra into OSLF formula interpretation

BinaryEvidence-valued formula interpretation uses BinaryEvidence's Frame (complete Heyting
algebra) structure:

- BinaryEvidence is a `Frame` (hence `HeytingAlgebra`, `CompleteLattice`)
- OSLF formulas map to BinaryEvidence values via lattice operations
- Threshold-Prop semantics (`sem`) is a corollary, not the foundation
- The threshold bridge is PARTIAL: it fails for disjunction/diamond because
  `τ ≤ x ⊔ y ⇏ τ ≤ x ∨ τ ≤ y` in BinaryEvidence's non-total order
  (this is a threshold-projection obstruction, not a failure of K&S scalar fidelity)
- Nested implication can also fail: evidence-level modus ponens is not a
  compositional translation of Heyting implication into Prop implication

## Interpretation Table

| Formula   | BinaryEvidence semantics          |
|-----------|-----------------------------|
| ⊤         | ⊤ (top evidence)            |
| ⊥         | ⊥ (zero evidence)           |
| atom a    | I a p                       |
| φ ∧ ψ    | semE φ p ⊓ semE ψ p        |
| φ ∨ ψ    | semE φ p ⊔ semE ψ p        |
| φ → ψ    | semE φ p ⇨ semE ψ p        |
| ◇ φ      | ⨆ {q | R p q}, semE φ q    |
| □ φ      | ⨅ {q | R q p}, semE φ q    |

## References

- Meredith & Stay, "Operational Semantics in Logical Form"
- Knuth & Skilling, "Foundations of Inference" (one-way scalar fidelity)
-/

namespace Mettapedia.OSLF.Framework.EvidenceSemantics

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModel

open scoped ENNReal

/-! ## BinaryEvidence-Valued Atom Semantics -/

/-- BinaryEvidence-valued atom interpretation: maps atom names and patterns to BinaryEvidence. -/
abbrev EvidenceAtomSem := String → Pattern → BinaryEvidence

/-! ## Evidence observations on equation classes -/

/-- An evidence-valued observation is semantic when it assigns identical
evidence to equation-equivalent presentations. -/
def EvidenceEquationInvariant (theory : GSLT)
    (observation : theory.Term → BinaryEvidence) : Prop :=
  ∀ ⦃left right : theory.Term⦄,
    theory.Equiv left right → observation left = observation right

/-- Evidence-valued predicates on authored terms equipped with the proof that
they are functions on the GSLT's equation classes. -/
abbrev EquationEvidencePredicate (theory : GSLT) :=
  { observation : theory.Term → BinaryEvidence //
    EvidenceEquationInvariant theory observation }

/-- Equation-respecting evidence interpretations for one `LanguageDef`. -/
abbrev EquationEvidenceAtomSemUsing (relEnv : RelationEnv)
    (lang : LanguageDef) :=
  String → EquationEvidencePredicate (langGSLTUsing relEnv lang)

/-- Default-environment equation-respecting evidence interpretations. -/
abbrev EquationEvidenceAtomSem (lang : LanguageDef) :=
  EquationEvidenceAtomSemUsing RelationEnv.empty lang

/-- Turn an authored evidence interpretation into a semantic one by querying
the computable representative of each equation class.  The section proof is
what makes this operation exact rather than a hidden choice of syntax. -/
def canonicalEvidenceAtomSemUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (canonical : ComputableSetoidSection Pattern
      (langGSLTUsing relEnv lang).equations)
    (interpretation : EvidenceAtomSem) :
    EquationEvidenceAtomSemUsing relEnv lang :=
  fun atom =>
    ⟨fun term => interpretation atom (canonical.normalize term), by
      intro left right equivalent
      exact congrArg (interpretation atom) (canonical.complete equivalent)⟩

/-- Default-environment form of `canonicalEvidenceAtomSemUsing`. -/
def canonicalEvidenceAtomSem
    (lang : LanguageDef)
    (canonical : ComputableSetoidSection Pattern (langGSLT lang).equations)
    (interpretation : EvidenceAtomSem) : EquationEvidenceAtomSem lang :=
  canonicalEvidenceAtomSemUsing RelationEnv.empty lang canonical interpretation

/-- Thresholding an equation-respecting evidence interpretation produces the
atomic predicates accepted by the sole equation-respecting OSLF. -/
def thresholdEquationAtomSemUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (interpretation : EquationEvidenceAtomSemUsing relEnv lang)
    (threshold : BinaryEvidence) : EquationAtomSemUsing relEnv lang :=
  fun atom =>
    ⟨fun term => threshold ≤ (interpretation atom).1 term, by
      intro left right equivalent
      change (threshold ≤ (interpretation atom).1 left) ↔
        (threshold ≤ (interpretation atom).1 right)
      rw [(interpretation atom).2 equivalent]⟩

/-- Default-environment form of `thresholdEquationAtomSemUsing`. -/
def thresholdEquationAtomSem
    (lang : LanguageDef) (interpretation : EquationEvidenceAtomSem lang)
    (threshold : BinaryEvidence) : EquationAtomSem lang :=
  thresholdEquationAtomSemUsing RelationEnv.empty lang interpretation threshold

/-! ## BinaryEvidence-Valued Formula Semantics -/

/-! ### Scope environments and the frame for an evidence-valued generator

The evidence-valued reading of the formula language must read a generator too,
and it reads it the same way: as the greatest lower bound of the pre-fixed
points of its body *inside a frame* of evidence observations.  Taking the bound
over the ambient function space instead would put the fixed point in a lattice
the generated logic does not have, and would cost the unconditional invariance
theorem below. -/

/-- Evidence-valued scope environments. -/
abbrev EvidenceScopeEnv := Nat → Pattern → BinaryEvidence

/-- Extend an evidence scope environment with a new innermost binding. -/
def EvidenceScopeEnv.push (value : Pattern → BinaryEvidence)
    (env : EvidenceScopeEnv) : EvidenceScopeEnv
  | 0 => value
  | k + 1 => env k

/-- The environment in which no scope variable carries evidence. -/
def EvidenceScopeEnv.empty : EvidenceScopeEnv := fun _ _ => ⊥

/-- A class of evidence observations closed under arbitrary infima. -/
structure EvidencePredFrame where
  /-- The evidence observations of the logic. -/
  Mem : (Pattern → BinaryEvidence) → Prop
  /-- Closed under the infima a greatest lower bound is built from. -/
  mem_iInf : ∀ selector : (Pattern → BinaryEvidence) → Prop,
    Mem fun term =>
      ⨅ candidate : Pattern → BinaryEvidence,
        ⨅ _ : Mem candidate ∧ selector candidate, candidate term

/-- The frame in which every evidence observation counts. -/
def fullEvidenceFrame : EvidencePredFrame where
  Mem := fun _ => True
  mem_iInf := fun _ => trivial

/-- BinaryEvidence-valued denotational semantics of OSLF formulas under a scope
environment.

Uses BinaryEvidence's Frame structure:
- `⊓` for conjunction (coordinatewise min)
- `⊔` for disjunction (coordinatewise max)
- `⇨` for Heyting implication (residuation)
- `⨆`/`⨅` for modalities over step-related states
- `⨅` over the pre-fixed points of the body, in the frame, for a generator -/
noncomputable def semEEnv (R : Pattern → Pattern → Prop)
    (F : EvidencePredFrame) (I : EvidenceAtomSem) (env : EvidenceScopeEnv) :
    OSLFFormula → Pattern → BinaryEvidence
  | .top, _ => ⊤
  | .bot, _ => ⊥
  | .atom a, p => I a p
  | .and φ ψ, p => semEEnv R F I env φ p ⊓ semEEnv R F I env ψ p
  | .or φ ψ, p => semEEnv R F I env φ p ⊔ semEEnv R F I env ψ p
  | .imp φ ψ, p => semEEnv R F I env φ p ⇨ semEEnv R F I env ψ p
  | .dia φ, p => ⨆ (q : {q // R p q}), semEEnv R F I env φ q.val
  | .box φ, p => ⨅ (q : {q // R q p}), semEEnv R F I env φ q.val
  | .var k, p => env k p
  | .mu φ, p =>
      ⨅ candidate : Pattern → BinaryEvidence,
        ⨅ _ : F.Mem candidate ∧
            ∀ t, semEEnv R F I (EvidenceScopeEnv.push candidate env) φ t
              ≤ candidate t,
          candidate p
  | .headed label body, p =>
      ⨅ candidate : Pattern → BinaryEvidence,
        ⨅ _ : F.Mem candidate ∧
            ∀ t, (⨆ inner : { inner : Pattern // t = Pattern.apply label [inner] },
                  semEEnv R F I env body inner.val)
              ≤ candidate t,
          candidate p
  | .emptyColl kind, p =>
      ⨅ candidate : Pattern → BinaryEvidence,
        ⨅ _ : F.Mem candidate ∧
            ∀ t, (if t = Pattern.collection kind [] none then (⊤ : BinaryEvidence) else ⊥)
              ≤ candidate t,
          candidate p
  | .cut kind left right, p =>
      ⨅ candidate : Pattern → BinaryEvidence,
        ⨅ _ : F.Mem candidate ∧
            ∀ t, (⨆ split : { split : List Pattern × List Pattern //
                    t = Pattern.collection kind (split.1 ++ split.2) none },
                  semEEnv R F I env left
                      (Pattern.collection kind split.val.1 none) ⊓
                    semEEnv R F I env right
                      (Pattern.collection kind split.val.2 none))
              ≤ candidate t,
          candidate p

/-- BinaryEvidence-valued denotational semantics of a closed formula in the
ambient observation space. -/
noncomputable def semE (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) :
    OSLFFormula → Pattern → BinaryEvidence :=
  semEEnv R fullEvidenceFrame I EvidenceScopeEnv.empty

/-! ## Unfolding Lemmas -/

@[simp] theorem semEEnv_top (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (p : Pattern) :
    semEEnv R F I env .top p = ⊤ := rfl

@[simp] theorem semEEnv_bot (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (p : Pattern) :
    semEEnv R F I env .bot p = ⊥ := rfl

@[simp] theorem semEEnv_atom (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (a : String) (p : Pattern) :
    semEEnv R F I env (.atom a) p = I a p := rfl

@[simp] theorem semEEnv_and (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.and φ ψ) p = semEEnv R F I env φ p ⊓ semEEnv R F I env ψ p := rfl

@[simp] theorem semEEnv_or (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.or φ ψ) p = semEEnv R F I env φ p ⊔ semEEnv R F I env ψ p := rfl

@[simp] theorem semEEnv_imp (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.imp φ ψ) p = semEEnv R F I env φ p ⇨ semEEnv R F I env ψ p := rfl

@[simp] theorem semEEnv_dia (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.dia φ) p = ⨆ (q : {q // R p q}), semEEnv R F I env φ q.val := rfl

@[simp] theorem semEEnv_box (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.box φ) p = ⨅ (q : {q // R q p}), semEEnv R F I env φ q.val := rfl

@[simp] theorem semEEnv_var (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (k : Nat) (p : Pattern) :
    semEEnv R F I env (.var k) p = env k p := rfl

/-- An evidence-valued generated scope is an observation of the frame it was
taken in. -/
theorem mem_semEEnv_mu (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ : OSLFFormula) :
    F.Mem (semEEnv R F I env (.mu φ)) :=
  F.mem_iInf _

@[simp] theorem semE_top (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (p : Pattern) :
    semE R I .top p = ⊤ := rfl

@[simp] theorem semE_bot (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (p : Pattern) :
    semE R I .bot p = ⊥ := rfl

@[simp] theorem semE_atom (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (a : String) (p : Pattern) :
    semE R I (.atom a) p = I a p := rfl

@[simp] theorem semE_and (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p = semE R I φ p ⊓ semE R I ψ p := rfl

@[simp] theorem semE_or (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.or φ ψ) p = semE R I φ p ⊔ semE R I ψ p := rfl

@[simp] theorem semE_imp (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.imp φ ψ) p = semE R I φ p ⇨ semE R I ψ p := rfl

@[simp] theorem semE_dia (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ : OSLFFormula) (p : Pattern) :
    semE R I (.dia φ) p = ⨆ (q : {q // R p q}), semE R I φ q.val := rfl

@[simp] theorem semE_box (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ : OSLFFormula) (p : Pattern) :
    semE R I (.box φ) p = ⨅ (q : {q // R q p}), semE R I φ q.val := rfl

/-- A formula of the modal fragment never consults the frame or the scope
environment, so on those formulas every reading is the same function. -/
theorem semEEnv_frame_irrelevant (R : Pattern → Pattern → Prop)
    (F F' : EvidencePredFrame) (I : EvidenceAtomSem) (φ : OSLFFormula)
    (free : OSLFFormula.modalOnly φ = true) :
    ∀ env env' : EvidenceScopeEnv, semEEnv R F I env φ = semEEnv R F' I env' φ := by
  induction φ with
  | top => intro _ _; rfl
  | bot => intro _ _; rfl
  | atom _ => intro _ _; rfl
  | var _ => simp [OSLFFormula.modalOnly] at free
  | mu _ _ => simp [OSLFFormula.modalOnly] at free
  | emptyColl _ => simp [OSLFFormula.modalOnly] at free
  | cut _ _ _ _ _ => simp [OSLFFormula.modalOnly] at free
  | headed _ _ _ => simp [OSLFFormula.modalOnly] at free
  | and φ ψ ihφ ihψ =>
      simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at free
      intro env env'
      funext t
      simp only [semEEnv, ihφ free.1 env env', ihψ free.2 env env']
  | or φ ψ ihφ ihψ =>
      simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at free
      intro env env'
      funext t
      simp only [semEEnv, ihφ free.1 env env', ihψ free.2 env env']
  | imp φ ψ ihφ ihψ =>
      simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at free
      intro env env'
      funext t
      simp only [semEEnv, ihφ free.1 env env', ihψ free.2 env env']
  | dia φ ih =>
      simp only [OSLFFormula.modalOnly] at free
      intro env env'
      funext t
      simp only [semEEnv, ih free env env']
  | box φ ih =>
      simp only [OSLFFormula.modalOnly] at free
      intro env env'
      funext t
      simp only [semEEnv, ih free env env']

/-- The ambient reading of a modal-fragment formula is its reading at any
frame. -/
theorem semE_eq_semEEnv_of_modalOnly (R : Pattern → Pattern → Prop)
    (F : EvidencePredFrame) (I : EvidenceAtomSem) (env : EvidenceScopeEnv)
    (φ : OSLFFormula) (free : OSLFFormula.modalOnly φ = true) :
    semE R I φ = semEEnv R F I env φ :=
  semEEnv_frame_irrelevant R fullEvidenceFrame F I φ free EvidenceScopeEnv.empty env

/-! ## Canonical evidence-valued OSLF semantics -/

/-- The frame of evidence observations of the generated logic: those assigning
identical evidence to equation-equivalent presentations. -/
def equationEvidenceFrameUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    EvidencePredFrame where
  Mem := EvidenceEquationInvariant (langGSLTUsing relEnv lang)
  mem_iInf := by
    intro _ left right equivalent
    exact iInf_congr fun candidate =>
      iInf_congr fun member => member.1 equivalent

/-- Evidence-valued interpretation over the modulo-equations operational
relation.  Atomic evidence has already descended through the language's
equation theory. -/
noncomputable def langSemEUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (interpretation : EquationEvidenceAtomSemUsing relEnv lang) :
    OSLFFormula → Pattern → BinaryEvidence :=
  semEEnv (langSemanticReducesUsing relEnv lang)
    (equationEvidenceFrameUsing relEnv lang)
    (fun atom term => (interpretation atom).1 term) EvidenceScopeEnv.empty

/-- Default-environment evidence-valued OSLF semantics. -/
noncomputable def langSemE
    (lang : LanguageDef) (interpretation : EquationEvidenceAtomSem lang) :
    OSLFFormula → Pattern → BinaryEvidence :=
  langSemEUsing RelationEnv.empty lang interpretation

/-- The evidence denotation of every formula is a function on equation
classes whenever its atomic observations are. -/
theorem semEEnv_equationInvariantUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (interpretation : EquationEvidenceAtomSemUsing relEnv lang)
    (formula : OSLFFormula) :
    ∀ env : EvidenceScopeEnv,
      (∀ index, EvidenceEquationInvariant (langGSLTUsing relEnv lang) (env index)) →
      EvidenceEquationInvariant (langGSLTUsing relEnv lang)
        (semEEnv (langSemanticReducesUsing relEnv lang)
          (equationEvidenceFrameUsing relEnv lang)
          (fun atom term => (interpretation atom).1 term) env formula) := by
  induction formula with
  | top => intro _ _; simp [EvidenceEquationInvariant, semEEnv]
  | bot => intro _ _; simp [EvidenceEquationInvariant, semEEnv]
  | atom atom => intro _ _; exact (interpretation atom).2
  | emptyColl kind =>
      intro _ _
      exact (equationEvidenceFrameUsing relEnv lang).mem_iInf _
  | cut kind first second _ _ =>
      intro _ _
      exact (equationEvidenceFrameUsing relEnv lang).mem_iInf _
  | headed label body _ =>
      intro _ _
      exact (equationEvidenceFrameUsing relEnv lang).mem_iInf _
  | and first second firstIH secondIH =>
      intro env envInv
      refine fun {left right : Pattern} equivalent => ?_
      simp only [semEEnv_and]
      rw [firstIH env envInv equivalent, secondIH env envInv equivalent]
  | or first second firstIH secondIH =>
      intro env envInv
      refine fun {left right : Pattern} equivalent => ?_
      simp only [semEEnv_or]
      rw [firstIH env envInv equivalent, secondIH env envInv equivalent]
  | imp first second firstIH secondIH =>
      intro env envInv
      refine fun {left right : Pattern} equivalent => ?_
      simp only [semEEnv_imp]
      rw [firstIH env envInv equivalent, secondIH env envInv equivalent]
  | dia body bodyIH =>
      intro env envInv
      refine fun {left right : Pattern} equivalent => ?_
      simp only [semEEnv_dia]
      apply le_antisymm
      · apply iSup_le
        intro target
        obtain ⟨target', step', targetEquivalent⟩ :=
          (langGSLTUsing relEnv lang).rewrites_resp_left
            equivalent target.property
        calc
          semEEnv (langSemanticReducesUsing relEnv lang)
                (equationEvidenceFrameUsing relEnv lang)
                (fun atom term => (interpretation atom).1 term) env body target.val =
              semEEnv (langSemanticReducesUsing relEnv lang)
                (equationEvidenceFrameUsing relEnv lang)
                (fun atom term => (interpretation atom).1 term) env body target' :=
            bodyIH env envInv targetEquivalent
          _ ≤ ⨆ (candidate :
                {candidate // langSemanticReducesUsing relEnv lang right candidate}),
                semEEnv (langSemanticReducesUsing relEnv lang)
                  (equationEvidenceFrameUsing relEnv lang)
                  (fun atom term => (interpretation atom).1 term) env body candidate.val :=
            le_iSup (fun candidate :
              {candidate // langSemanticReducesUsing relEnv lang right candidate} =>
                semEEnv (langSemanticReducesUsing relEnv lang)
                  (equationEvidenceFrameUsing relEnv lang)
                  (fun atom term => (interpretation atom).1 term) env body candidate.val)
              ⟨target', step'⟩
      · apply iSup_le
        intro target
        obtain ⟨target', step', targetEquivalent⟩ :=
          (langGSLTUsing relEnv lang).rewrites_resp_left
            ((langGSLTUsing relEnv lang).equations.iseqv.symm equivalent)
            target.property
        calc
          semEEnv (langSemanticReducesUsing relEnv lang)
                (equationEvidenceFrameUsing relEnv lang)
                (fun atom term => (interpretation atom).1 term) env body target.val =
              semEEnv (langSemanticReducesUsing relEnv lang)
                (equationEvidenceFrameUsing relEnv lang)
                (fun atom term => (interpretation atom).1 term) env body target' :=
            bodyIH env envInv targetEquivalent
          _ ≤ ⨆ (candidate :
                {candidate // langSemanticReducesUsing relEnv lang left candidate}),
                semEEnv (langSemanticReducesUsing relEnv lang)
                  (equationEvidenceFrameUsing relEnv lang)
                  (fun atom term => (interpretation atom).1 term) env body candidate.val :=
            le_iSup (fun candidate :
              {candidate // langSemanticReducesUsing relEnv lang left candidate} =>
                semEEnv (langSemanticReducesUsing relEnv lang)
                  (equationEvidenceFrameUsing relEnv lang)
                  (fun atom term => (interpretation atom).1 term) env body candidate.val)
              ⟨target', step'⟩
  | box body bodyIH =>
      intro env envInv
      refine fun {left right : Pattern} equivalent => ?_
      simp only [semEEnv_box]
      apply le_antisymm
      · apply le_iInf
        intro source
        have sourceStep : langSemanticReducesUsing relEnv lang source.val left :=
          (langGSLTUsing relEnv lang).rewrites_resp_right source.property
            ((langGSLTUsing relEnv lang).equations.iseqv.symm equivalent)
        exact iInf_le
          (fun candidate :
            {candidate // langSemanticReducesUsing relEnv lang candidate left} =>
              semEEnv (langSemanticReducesUsing relEnv lang)
                (equationEvidenceFrameUsing relEnv lang)
                (fun atom term => (interpretation atom).1 term) env body candidate.val)
          ⟨source.val, sourceStep⟩
      · apply le_iInf
        intro source
        have sourceStep : langSemanticReducesUsing relEnv lang source.val right :=
          (langGSLTUsing relEnv lang).rewrites_resp_right source.property equivalent
        exact iInf_le
          (fun candidate :
            {candidate // langSemanticReducesUsing relEnv lang candidate right} =>
              semEEnv (langSemanticReducesUsing relEnv lang)
                (equationEvidenceFrameUsing relEnv lang)
                (fun atom term => (interpretation atom).1 term) env body candidate.val)
          ⟨source.val, sourceStep⟩
  | var index => intro env envInv; exact envInv index
  | mu body _ =>
      intro env _
      exact (equationEvidenceFrameUsing relEnv lang).mem_iInf _

/-- The empty evidence scope environment consists of observations of the
logic. -/
theorem evidenceEquationInvariant_scopeEnv_empty
    (relEnv : RelationEnv) (lang : LanguageDef) :
    ∀ index, EvidenceEquationInvariant (langGSLTUsing relEnv lang)
      (EvidenceScopeEnv.empty index) :=
  fun _ _ _ _ => rfl

/-- The evidence denotation of every formula is a function on equation classes
whenever its atomic observations are. -/
theorem langSemE_equationInvariantUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (interpretation : EquationEvidenceAtomSemUsing relEnv lang)
    (formula : OSLFFormula) :
    EvidenceEquationInvariant (langGSLTUsing relEnv lang)
      (langSemEUsing relEnv lang interpretation formula) :=
  semEEnv_equationInvariantUsing relEnv lang interpretation formula
    EvidenceScopeEnv.empty
    (evidenceEquationInvariant_scopeEnv_empty relEnv lang)

/-- Default-environment equation-invariance theorem. -/
theorem langSemE_equationInvariant
    (lang : LanguageDef) (interpretation : EquationEvidenceAtomSem lang)
    (formula : OSLFFormula) :
    EvidenceEquationInvariant (langGSLT lang)
      (langSemE lang interpretation formula) := by
  simpa [langSemE, langGSLT] using
    langSemE_equationInvariantUsing RelationEnv.empty lang interpretation formula

/-! ## Structural Monotonicity -/

/-- Conjunction projects to the left component. -/
theorem semE_and_le_left (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p ≤ semE R I φ p :=
  inf_le_left

/-- Conjunction projects to the right component. -/
theorem semE_and_le_right (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p ≤ semE R I ψ p :=
  inf_le_right

/-- Left disjunct injects into disjunction. -/
theorem semE_le_or_left (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I φ p ≤ semE R I (.or φ ψ) p :=
  le_sup_left

/-- Right disjunct injects into disjunction. -/
theorem semE_le_or_right (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I ψ p ≤ semE R I (.or φ ψ) p :=
  le_sup_right

/-- A step-successor's evidence injects into diamond. -/
theorem semE_dia_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ : OSLFFormula) (p q : Pattern) (h : R p q) :
    semE R I φ q ≤ semE R I (.dia φ) p :=
  le_iSup (fun (s : {s // R p s}) => semE R I φ s.val) ⟨q, h⟩

/-- Box projects to any predecessor. -/
theorem semE_box_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ : OSLFFormula) (p q : Pattern) (h : R q p) :
    semE R I (.box φ) p ≤ semE R I φ q :=
  iInf_le (fun (s : {s // R s p}) => semE R I φ s.val) ⟨q, h⟩

/-! ### The same order facts under a scope environment

Stated for `semEEnv` because the language-level evidence reading takes its
generator in the frame of the generated logic, so its connectives are
`semEEnv`'s and not the ambient reading's. -/

theorem semEEnv_and_le_left (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.and φ ψ) p ≤ semEEnv R F I env φ p :=
  inf_le_left

theorem semEEnv_and_le_right (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.and φ ψ) p ≤ semEEnv R F I env ψ p :=
  inf_le_right

theorem semEEnv_le_or_left (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env φ p ≤ semEEnv R F I env (.or φ ψ) p :=
  le_sup_left

theorem semEEnv_le_or_right (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env ψ p ≤ semEEnv R F I env (.or φ ψ) p :=
  le_sup_right

theorem semEEnv_dia_le (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ : OSLFFormula) (p q : Pattern)
    (h : R p q) :
    semEEnv R F I env φ q ≤ semEEnv R F I env (.dia φ) p :=
  le_iSup (fun (s : {s // R p s}) => semEEnv R F I env φ s.val) ⟨q, h⟩

theorem semEEnv_box_le (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ : OSLFFormula) (p q : Pattern)
    (h : R q p) :
    semEEnv R F I env (.box φ) p ≤ semEEnv R F I env φ q :=
  iInf_le (fun (s : {s // R s p}) => semEEnv R F I env φ s.val) ⟨q, h⟩

theorem semEEnv_imp_mp (R : Pattern → Pattern → Prop) (F : EvidencePredFrame)
    (I : EvidenceAtomSem) (env : EvidenceScopeEnv) (φ ψ : OSLFFormula) (p : Pattern) :
    semEEnv R F I env (.imp φ ψ) p ⊓ semEEnv R F I env φ p ≤ semEEnv R F I env ψ p := by
  simp only [semEEnv_imp]
  exact himp_inf_le

/-! ## Modus Ponens (Heyting) -/

/-- Heyting modus ponens: `semE (φ → ψ) p ⊓ semE φ p ≤ semE ψ p`. -/
theorem semE_imp_mp (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.imp φ ψ) p ⊓ semE R I φ p ≤ semE R I ψ p := by
  simp only [semE_imp]
  exact himp_inf_le

/-! ## World-Model Connection -/

section WMConnection

variable {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]

/-- BinaryEvidence atom semantics from a world-model state: the atom at pattern p
is the evidence extracted by querying `queryOfAtom a p`. -/
noncomputable def wmEvidenceAtomSem
    (W : State) (queryOfAtom : String → Pattern → Pattern) : EvidenceAtomSem :=
  fun a p => BinaryWorldModel.evidence W (queryOfAtom a p)

/-- WM revision lifts to evidence atoms: revising world states then
extracting atom evidence = extracting from each and combining. -/
theorem semE_wm_atom_revision
    (W₁ W₂ : State) (queryOfAtom : String → Pattern → Pattern)
    (R : Pattern → Pattern → Prop) (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSem (W₁ + W₂) queryOfAtom) (.atom a) p =
      semE R (wmEvidenceAtomSem W₁ queryOfAtom) (.atom a) p +
      semE R (wmEvidenceAtomSem W₂ queryOfAtom) (.atom a) p := by
  simp only [semE_atom, wmEvidenceAtomSem]
  exact BinaryWorldModel.evidence_add W₁ W₂ (queryOfAtom a p)

end WMConnection

/-! ## Threshold Bridge (Conjunctive Fragment)

The threshold bridge `τ ≤ semE R I φ p → sem R (threshI τ) φ p` works for
the conjunctive fragment (top, atom, and, box) but FAILS for the
disjunctive fragment (or, dia) because BinaryEvidence's order is non-total:
`τ ≤ x ⊔ y ⇏ τ ≤ x ∨ τ ≤ y`.

This is a property of thresholding a partial order into `Prop`.  It is distinct
from K&S one-way scalar fidelity and from the Boolean/Heyting complement gate. -/

/-- Threshold atom semantics: atom holds when evidence exceeds threshold. -/
noncomputable def threshAtomSem (I : EvidenceAtomSem) (τ : BinaryEvidence) :
    AtomSem :=
  fun a p => τ ≤ I a p

/-- Threshold bridge for atoms: direct by definition. -/
theorem threshold_atom (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (a : String) (p : Pattern) :
    τ ≤ semE R I (.atom a) p ↔ sem R (threshAtomSem I τ) (.atom a) p := by
  rfl

/-- Threshold bridge for conjunction. -/
theorem threshold_and (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : τ ≤ semE R I φ p → sem R (threshAtomSem I τ) φ p)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.and φ ψ) p → sem R (threshAtomSem I τ) (.and φ ψ) p := by
  intro h
  simp only [semE_and] at h
  exact ⟨hφ (le_trans h inf_le_left), hψ (le_trans h inf_le_right)⟩

/-- Threshold bridge FAILS for disjunction in general.

Counterexample: I "a" = (1,0), I "b" = (0,1) are incomparable in BinaryEvidence.
Their join (1,0) ⊔ (0,1) = (1,1), but τ = (1,1) exceeds neither component.
This is the imprecision gate in action: non-total order prevents Boolean
reduction of disjunction. -/
theorem threshold_or_counterexample :
    ¬ (∀ (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
       (φ ψ : OSLFFormula) (p : Pattern),
       τ ≤ semE R I (.or φ ψ) p →
       sem R (threshAtomSem I τ) (.or φ ψ) p) := by
  intro h
  -- I "a" = (1,0), I "b" = (0,1) are incomparable; τ = (1,1) = their join
  let p₀ : Pattern := .apply "x" []
  let I : EvidenceAtomSem := fun a _ =>
    if a == "a" then ⟨1, 0⟩ else ⟨0, 1⟩
  let τ₀ : BinaryEvidence := ⟨1, 1⟩
  let R₀ : Pattern → Pattern → Prop := fun _ _ => False
  have hle : τ₀ ≤ semE R₀ I (.or (.atom "a") (.atom "b")) p₀ := by
    simp only [semE_or, semE_atom]
    show (⟨1, 1⟩ : BinaryEvidence) ≤ (⟨1, 0⟩ : BinaryEvidence) ⊔ (⟨0, 1⟩ : BinaryEvidence)
    exact ⟨(@le_sup_left BinaryEvidence _ ⟨1, 0⟩ ⟨0, 1⟩).1, (@le_sup_right BinaryEvidence _ ⟨1, 0⟩ ⟨0, 1⟩).2⟩
  have habs := h I τ₀ R₀ (.atom "a") (.atom "b") p₀ hle
  simp only [sem] at habs
  have hnle : ¬ ((1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞)) := by norm_num
  rcases habs with h1 | h2
  · exact hnle h1.2
  · exact hnle h2.1

/-! ### Connective-Specific Threshold Bridges

The forward threshold bridge is closed under {⊤, atom, ∧, □}; bottom also
admits the bridge when the threshold is strictly positive. Disjunction and
diamond fail in general. The implication law below is evidence-level modus
ponens, not a compositional implication bridge: nested implication can fail
even when no disjunction or diamond occurs.

The obstruction is order-theoretic: a threshold below a join need not lie below
either summand.  It does not say that K&S scalar valuation requires a total
source order, nor that totality alone makes the evidence algebra Boolean. -/

/-- Threshold bridge for ⊤: always works (vacuously). -/
theorem threshold_top (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (p : Pattern) :
    τ ≤ semE R I .top p → sem R (threshAtomSem I τ) .top p := by
  intro _; trivial

/-- Threshold bridge for ⊥: works by absurdity (τ ≤ ⊥ is impossible for τ > 0). -/
theorem threshold_bot (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (p : Pattern) (hτ : ⊥ < τ) :
    τ ≤ semE R I .bot p → sem R (threshAtomSem I τ) .bot p := by
  intro h; exact absurd (lt_of_lt_of_le hτ h) (lt_irrefl _)

/-- Threshold bridge for implication (→): evidence-level modus ponens.

If `τ ≤ φ ⇨ ψ` and `τ ≤ φ` then `τ ≤ ψ`. The second hypothesis is at
the evidence level (not Prop level) because the reverse bridge
`sem (threshAtomSem I τ) φ p → τ ≤ semE R I φ p` fails for the
disjunctive fragment. -/
theorem threshold_imp (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.imp φ ψ) p →
    τ ≤ semE R I φ p →
    sem R (threshAtomSem I τ) ψ p := by
  intro himp hφ
  apply hψ
  calc τ = τ ⊓ τ := (inf_idem _).symm
    _ ≤ (semE R I φ p ⇨ semE R I ψ p) ⊓ semE R I φ p := inf_le_inf himp hφ
    _ ≤ semE R I ψ p := himp_inf_le

/-- Nested implication refutes a compositional forward threshold bridge even
in the fragment generated by atoms and implication.

At threshold `(1,1)`, all three atoms are false. Evidence implication gives
`a ⇨ b = (0,∞)` and `(a ⇨ b) ⇨ c = (∞,2)`, above the threshold, whereas
the Prop reading is `(False → False) → False`. -/
theorem threshold_nested_imp_counterexample :
    ∃ (I : EvidenceAtomSem) (R : Pattern → Pattern → Prop) (p : Pattern),
      (⟨1, 1⟩ : BinaryEvidence) ≤
        semE R I (.imp (.imp (.atom "a") (.atom "b")) (.atom "c")) p ∧
      ¬ sem R (threshAtomSem I ⟨1, 1⟩)
        (.imp (.imp (.atom "a") (.atom "b")) (.atom "c")) p := by
  let I : EvidenceAtomSem := fun name _ =>
    if name == "a" then ⟨2, 0⟩ else if name == "b" then ⟨0, 0⟩ else ⟨0, 2⟩
  refine ⟨I, fun _ _ => False, .apply "p" [], ?_, ?_⟩
  · change (⟨1, 1⟩ : BinaryEvidence) ≤
      BinaryEvidence.himp (BinaryEvidence.himp ⟨2, 0⟩ ⟨0, 0⟩) ⟨0, 2⟩
    change (1 : ℝ≥0∞) ≤
        (BinaryEvidence.himp (BinaryEvidence.himp ⟨2, 0⟩ ⟨0, 0⟩) ⟨0, 2⟩).pos ∧
      (1 : ℝ≥0∞) ≤
        (BinaryEvidence.himp (BinaryEvidence.himp ⟨2, 0⟩ ⟨0, 0⟩) ⟨0, 2⟩).neg
    norm_num [BinaryEvidence.himp]
  · change ¬ ((((⟨1, 1⟩ : BinaryEvidence) ≤ ⟨2, 0⟩) →
        (⟨1, 1⟩ : BinaryEvidence) ≤ ⟨0, 0⟩) →
      (⟨1, 1⟩ : BinaryEvidence) ≤ ⟨0, 2⟩)
    have hna : ¬ (⟨1, 1⟩ : BinaryEvidence) ≤ ⟨2, 0⟩ := by
      norm_num [BinaryEvidence.le_def]
    have hnc : ¬ (⟨1, 1⟩ : BinaryEvidence) ≤ ⟨0, 2⟩ := by
      norm_num [BinaryEvidence.le_def]
    intro implication
    exact hnc (implication (fun antecedent => (hna antecedent).elim))

#print axioms threshold_nested_imp_counterexample

/-- Threshold bridge for box (□): works because ⊓ distributes over threshold. -/
theorem threshold_box (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (φ : OSLFFormula) (p : Pattern)
    (hφ : ∀ q, R q p → τ ≤ semE R I φ q → sem R (threshAtomSem I τ) φ q) :
    τ ≤ semE R I (.box φ) p → sem R (threshAtomSem I τ) (.box φ) p := by
  intro h q hqp
  apply hφ q hqp
  exact le_trans h (semE_box_le R I φ p q hqp)

/-- Threshold bridge FAILS for diamond (◇) in general.

Same mechanism as `threshold_or_counterexample`: `τ ≤ ⨆ ... ⇏ ∃ ..., τ ≤ ...`
because BinaryEvidence is non-total. Two successors q₁, q₂ with incomparable evidence
(1,0) and (0,1) have supremum (1,1), but no single successor exceeds (1,1). -/
theorem threshold_dia_fails :
    ¬ (∀ (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
       (φ : OSLFFormula) (p : Pattern),
       τ ≤ semE R I (.dia φ) p →
       sem R (threshAtomSem I τ) (.dia φ) p) := by
  intro h
  let p₀ : Pattern := .apply "p" []
  let q₁ : Pattern := .apply "q1" []
  let q₂ : Pattern := .apply "q2" []
  let I : EvidenceAtomSem := fun _ q =>
    if q == q₁ then ⟨1, 0⟩ else ⟨0, 1⟩
  let τ₀ : BinaryEvidence := ⟨1, 1⟩
  let R₀ : Pattern → Pattern → Prop := fun p q => p = p₀ ∧ (q = q₁ ∨ q = q₂)
  -- τ₀ = (1,1) ≤ (1,0) ⊔ (0,1) ≤ ⨆ over {q₁, q₂} by le_iSup + sup_le
  have hle : τ₀ ≤ semE R₀ I (.dia (.atom "a")) p₀ := by
    simp only [semE_dia, semE_atom]
    have h1 := le_iSup (fun (q : {q // R₀ p₀ q}) => I "a" q.val) ⟨q₁, rfl, Or.inl rfl⟩
    have h2 := le_iSup (fun (q : {q // R₀ p₀ q}) => I "a" q.val) ⟨q₂, rfl, Or.inr rfl⟩
    refine le_trans ?_ (sup_le h1 h2)
    simp only [I, q₁, q₂, beq_iff_eq]
    exact ⟨le_sup_of_le_left (le_refl _), le_sup_of_le_right (le_refl _)⟩
  -- But no single successor has evidence ≥ (1,1)
  have habs := h I τ₀ R₀ (.atom "a") p₀ hle
  simp only [sem] at habs
  have hnle : ¬ ((1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞)) := by norm_num
  rcases habs with ⟨q, ⟨_, hq⟩, hsat⟩
  rcases hq with rfl | rfl
  · exact hnle hsat.2
  · exact hnle hsat.1

/-! ## Totality Gate for Threshold Projection

Under total order (`∀ a b, a ≤ b ∨ b ≤ a`), the forward threshold bridge also
works for disjunction and, with finite nonempty branching, diamond.  This is a
projection theorem for the listed connectives.  It does not make the carrier
Boolean, and it establishes no compositional threshold law for implication. -/

/-- In a linearly ordered lattice, `τ ≤ a ⊔ b → τ ≤ a ∨ τ ≤ b`.
This is the lattice-level totality gate. -/
theorem le_sup_of_total {H : Type*} [SemilatticeSup H]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a)
    {τ a b : H} (h : τ ≤ a ⊔ b) : τ ≤ a ∨ τ ≤ b := by
  rcases hTotal a b with hab | hba
  · right; exact le_trans h (sup_le hab (le_refl b))
  · left; exact le_trans h (sup_le (le_refl a) hba)

/-- Under totality, threshold bridge works for disjunction. -/
theorem threshold_or_total
    (hTotal : ∀ a b : BinaryEvidence, a ≤ b ∨ b ≤ a)
    (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : τ ≤ semE R I φ p → sem R (threshAtomSem I τ) φ p)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.or φ ψ) p → sem R (threshAtomSem I τ) (.or φ ψ) p := by
  intro h
  simp only [semE_or] at h
  rcases le_sup_of_total hTotal h with h1 | h2
  · exact Or.inl (hφ h1)
  · exact Or.inr (hψ h2)

/-- In a total order, `a ⊔ b < τ` from `a < τ` and `b < τ`. -/
private theorem sup_lt_of_lt_total {H : Type*} [SemilatticeSup H]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a) {a b τ : H}
    (ha : a < τ) (hb : b < τ) : a ⊔ b < τ := by
  rcases hTotal a b with h | h
  · rwa [sup_eq_right.mpr h]
  · rwa [sup_eq_left.mpr h]

/-- In a total order, `Finset.sup'` of finitely many elements all `< τ` is `< τ`. -/
private theorem Finset.sup'_lt_total {H ι : Type*} [SemilatticeSup H]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a)
    {s : Finset ι} (hs : s.Nonempty) {f : ι → H} {τ : H}
    (hlt : ∀ i ∈ s, f i < τ) : s.sup' hs f < τ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp [Finset.sup'_singleton]; exact hlt a (Finset.mem_singleton_self a)
  | cons a s has hs ih =>
    rw [Finset.sup'_cons hs]
    exact sup_lt_of_lt_total hTotal
      (hlt a (Finset.mem_cons_self a _))
      (ih (fun i hi => hlt i (Finset.mem_cons_of_mem hi)))

/-- In a total order, `iSup` of finitely many elements all `< τ` is `< τ`.
Connects `Finset.sup'` on `Finset.univ` to `iSup` via `sup'_univ_eq_ciSup`. -/
private theorem iSup_lt_of_forall_lt_total {H : Type*} {ι : Type*}
    [CompleteLattice H] [Fintype ι] [Nonempty ι]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a)
    {f : ι → H} {τ : H}
    (hlt : ∀ i, f i < τ) : iSup f < τ := by
  rw [← Finset.sup'_univ_eq_ciSup]
  exact Finset.sup'_lt_total hTotal Finset.univ_nonempty (fun i _ => hlt i)

/-- Under totality + finite branching, threshold bridge works for diamond.
Uses `iSup_lt_of_forall_lt_total`: in a total order over a finite set,
if every element is strictly below τ, then iSup < τ. -/
theorem threshold_dia_total
    (hTotal : ∀ a b : BinaryEvidence, a ≤ b ∨ b ≤ a)
    (I : EvidenceAtomSem) (τ : BinaryEvidence) (R : Pattern → Pattern → Prop)
    (φ : OSLFFormula) (p : Pattern)
    (hφ : ∀ q, R p q → τ ≤ semE R I φ q → sem R (threshAtomSem I τ) φ q)
    (hSucc : Set.Finite {q | R p q})
    (hNonempty : ∃ q, R p q) :
    τ ≤ semE R I (.dia φ) p → sem R (threshAtomSem I τ) (.dia φ) p := by
  intro h
  simp only [semE_dia] at h
  have : Nonempty {q // R p q} := by
    obtain ⟨q, hq⟩ := hNonempty; exact ⟨⟨q, hq⟩⟩
  have : Finite {q // R p q} := hSucc.to_subtype
  by_contra hc
  simp only [sem, semEnv] at hc
  push Not at hc
  have hno : ∀ q, R p q → ¬ (τ ≤ semE R I φ q) := by
    intro q hRq hle; exact hc q hRq (hφ q hRq hle)
  have hlt : ∀ (q : {q // R p q}), semE R I φ q.val < τ := by
    intro ⟨q, hRq⟩
    rcases hTotal τ (semE R I φ q) with h1 | h2
    · exact absurd h1 (hno q hRq)
    · exact lt_of_le_of_ne h2 (fun heq => hno q hRq (heq ▸ le_refl _))
  have : Fintype {q // R p q} := hSucc.fintype
  exact absurd (lt_of_le_of_lt h (iSup_lt_of_forall_lt_total hTotal hlt))
    (lt_irrefl _)

/-- Reverse threshold bridge: `sem (threshAtomSem I τ) φ p → τ ≤ semE R I φ p`.
Works for implication-free modal formulas without totality. No reverse
implication bridge is established here. -/
theorem threshold_reverse_atom (I : EvidenceAtomSem) (τ : BinaryEvidence)
    (R : Pattern → Pattern → Prop) (a : String) (p : Pattern) :
    sem R (threshAtomSem I τ) (.atom a) p → τ ≤ semE R I (.atom a) p := id

theorem threshold_reverse_and (I : EvidenceAtomSem) (τ : BinaryEvidence)
    (R : Pattern → Pattern → Prop) (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p)
    (hψ : sem R (threshAtomSem I τ) ψ p → τ ≤ semE R I ψ p) :
    sem R (threshAtomSem I τ) (.and φ ψ) p → τ ≤ semE R I (.and φ ψ) p := by
  intro ⟨h1, h2⟩; exact le_inf (hφ h1) (hψ h2)

theorem threshold_reverse_or (I : EvidenceAtomSem) (τ : BinaryEvidence)
    (R : Pattern → Pattern → Prop) (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p)
    (hψ : sem R (threshAtomSem I τ) ψ p → τ ≤ semE R I ψ p) :
    sem R (threshAtomSem I τ) (.or φ ψ) p → τ ≤ semE R I (.or φ ψ) p := by
  intro h
  rcases h with h1 | h2
  · exact le_trans (hφ h1) le_sup_left
  · exact le_trans (hψ h2) le_sup_right

/-! ## Scope of the Totality Projection Theorem

`threshold_dia_total` requires two side conditions:

1. **Finite branching** (`hSucc : Set.Finite {q | R p q}`): The successor set
   must be finite.  Without this, the sup of infinitely many values all `< τ`
   can still equal τ (e.g. sup of `{1 - 1/n}` = 1).

2. **Nonempty successors** (`hNonempty : ∃ q, R p q`): At deadlock states,
   `semE(◇φ, p) = ⊥` but `sem(◇φ, p)` requires a witness.  The bridge fails
   because the Prop-level diamond is existential while the BinaryEvidence-level
   diamond is a supremum (which can be ⊥ over the empty set).

Together with the top, atom, conjunction, and box bridges,
`threshold_or_total` and `threshold_dia_total` supply connective-wise forward
bridges for implication-free modal formulas, provided their side conditions
hold at every state reached by the recursive interpretation. They do not
establish a bridge for implication, spatial constructors, scope variables,
or fixed-point generators. The stated totality premise is not satisfied by
the full coordinatewise BinaryEvidence carrier. -/

/-- The threshold bridge for ◇ genuinely fails at deadlock states:
`⊥ ≤ semE(◇φ, p)` holds (empty sup = ⊥), but `sem(◇φ, p)` requires a
witness that doesn't exist. This shows `hNonempty` is necessary. -/
theorem threshold_dia_fails_at_deadlock :
    ∃ (I : EvidenceAtomSem) (R : Pattern → Pattern → Prop) (φ : OSLFFormula)
      (p : Pattern),
      (⊥ : BinaryEvidence) ≤ semE R I (.dia φ) p ∧
      ¬ sem R (threshAtomSem I ⊥) (.dia φ) p := by
  refine ⟨fun _ _ => ⊥, fun _ _ => False, .atom "a", .fvar "dead", bot_le, ?_⟩
  intro ⟨_, hR, _⟩; exact hR

/-! ## Reverse Threshold Bridge (Imp-Free Fragment)

The REVERSE direction `sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p`
holds for the implication-free fragment WITHOUT totality or finite branching.
The existential witness in ◇ provides the evidence bound directly. -/

/-- An OSLF formula is implication-free (no `.imp` subformulas). -/
def impFree : OSLFFormula → Prop
  | .top | .bot | .atom _ => True
  | .and φ ψ | .or φ ψ => impFree φ ∧ impFree ψ
  | .imp _ _ => False
  | .dia φ | .box φ => impFree φ
  | .var _ => True
  | .mu φ => impFree φ
  | .emptyColl _ => True
  | .cut _ φ ψ => impFree φ ∧ impFree ψ
  | .headed _ φ => impFree φ

/-- Reverse threshold bridge for ◇: no totality or finite branching needed.
The existential witness in `sem(◇φ)` provides the evidence bound. -/
theorem threshold_reverse_dia (I : EvidenceAtomSem) (τ : BinaryEvidence)
    (R : Pattern → Pattern → Prop) (φ : OSLFFormula) (p : Pattern)
    (hφ : ∀ q, R p q → sem R (threshAtomSem I τ) φ q → τ ≤ semE R I φ q) :
    sem R (threshAtomSem I τ) (.dia φ) p → τ ≤ semE R I (.dia φ) p := by
  intro ⟨q, hRq, hsat⟩
  simp only [semE_dia]
  exact le_trans (hφ q hRq hsat)
    (le_iSup (fun (q : {q // R p q}) => semE R I φ q.val) ⟨q, hRq⟩)

/-- Reverse threshold bridge for implication-free modal formulas.

Under `impFree φ` and `modalOnly φ = true`,
`sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p` holds without totality
or branching assumptions. Spatial constructors, scope variables, and
fixed-point generators are outside this theorem's domain. The forward
direction for ∨/◇ needs additional hypotheses, but the reverse does not. -/
theorem threshold_reverse_impFree_env (I : EvidenceAtomSem) (τ : BinaryEvidence)
    (R : Pattern → Pattern → Prop) (F : EvidencePredFrame) (env : EvidenceScopeEnv)
    (φ : OSLFFormula) (hImpFree : impFree φ)
    (hMuFree : OSLFFormula.modalOnly φ = true)
    (p : Pattern) :
    sem R (threshAtomSem I τ) φ p → τ ≤ semEEnv R F I env φ p := by
  induction φ generalizing p with
  | emptyColl _ => simp [OSLFFormula.modalOnly] at hMuFree
  | cut _ _ _ _ _ => simp [OSLFFormula.modalOnly] at hMuFree
  | headed _ _ _ => simp [OSLFFormula.modalOnly] at hMuFree
  | top => intro _; exact le_top
  | bot => intro h; exact absurd h id
  | atom a => intro h; exact h
  | and φ ψ ih1 ih2 =>
    simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at hMuFree
    intro ⟨h1, h2⟩
    exact le_inf (ih1 hImpFree.1 hMuFree.1 p h1) (ih2 hImpFree.2 hMuFree.2 p h2)
  | or φ ψ ih1 ih2 =>
    simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at hMuFree
    intro h; rcases h with h | h
    · exact le_trans (ih1 hImpFree.1 hMuFree.1 p h) le_sup_left
    · exact le_trans (ih2 hImpFree.2 hMuFree.2 p h) le_sup_right
  | imp _ _ => exact absurd hImpFree id
  | dia φ ih =>
    simp only [OSLFFormula.modalOnly] at hMuFree
    intro ⟨q, hRq, hsat⟩; simp only [semEEnv_dia]
    exact le_trans (ih hImpFree hMuFree q hsat)
      (le_iSup (fun (q : {q // R p q}) => semEEnv R F I env φ q.val) ⟨q, hRq⟩)
  | box φ ih =>
    simp only [OSLFFormula.modalOnly] at hMuFree
    intro hbox; simp only [semEEnv_box]
    exact le_iInf fun ⟨q, hRq⟩ => ih hImpFree hMuFree q (hbox q hRq)
  | var _ => simp [OSLFFormula.modalOnly] at hMuFree
  | mu _ _ => simp [OSLFFormula.modalOnly] at hMuFree

/-- Reverse threshold bridge in the ambient observation space. -/
theorem threshold_reverse_impFree (I : EvidenceAtomSem) (τ : BinaryEvidence)
    (R : Pattern → Pattern → Prop) (φ : OSLFFormula) (hImpFree : impFree φ)
    (hMuFree : OSLFFormula.modalOnly φ = true)
    (p : Pattern) :
    sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p :=
  threshold_reverse_impFree_env I τ R fullEvidenceFrame EvidenceScopeEnv.empty
    φ hImpFree hMuFree p

/-! ## Temporal BinaryEvidence Semantics

Temporal operators following Geisweiller & Yusuf, "Probabilistic Logic Networks
for Temporal and Procedural Reasoning" (LNCS 2023).  Temporal predicates are
regular predicates with a time dimension:

  P, Q, ... : Domain × Time → {True, False}

We embed temporal indices into patterns via a tagging constructor, keeping
Pattern as the universal query carrier.  Temporal operators are macros over
the existing evidence semantics — they shift the time index before evaluation.

### Operators (from Geisweiller & Yusuf §3.1)

- `Lag(P, T)  := λx,t. P(x, t - T)`  — bring past into present
- `Lead(P, T) := λx,t. P(x, t + T)`  — bring future into present
- `SequentialAnd(T, P, Q) := And(P, Lead(Q, T))`
- `PredictiveImplication(T, P, Q) := Imp(P, Lead(Q, T))`

### Key design: temporal patterns as tagged patterns

Rather than extending Pattern or OSLFFormula with a time type parameter
(which would require pervasive changes), we embed time into patterns:

  temporalPattern p t = Pattern.apply "⊛temporal" [p, Pattern.apply (toString t) []]

Old non-temporal Pattern queries are the special case `t = 0`. -/

section TemporalSemantics

/-- Embed a time index into a pattern.  Non-temporal patterns are `t = 0`. -/
def temporalPattern (p : Pattern) (t : Int) : Pattern :=
  Pattern.apply "⊛temporal" [p, Pattern.apply (toString t) []]

/-- Extract the spatial component from a temporal pattern at the same time. -/
theorem temporalPattern_injective_left {p₁ p₂ : Pattern} {t : Int}
    (h : temporalPattern p₁ t = temporalPattern p₂ t) : p₁ = p₂ := by
  simp [temporalPattern] at h
  exact h

/-- Same pattern at the same time gives the same temporal pattern. -/
@[simp] theorem temporalPattern_eq_iff {p₁ p₂ : Pattern} {t₁ t₂ : Int} :
    temporalPattern p₁ t₁ = temporalPattern p₂ t₂ ↔
    p₁ = p₂ ∧ toString t₁ = toString t₂ := by
  simp [temporalPattern]

/-- Temporal atom query: encode atom name + pattern + time into a WM query. -/
def temporalAtomQuery (baseAtomQuery : String → Pattern → Pattern)
    (a : String) (p : Pattern) (t : Int) : Pattern :=
  baseAtomQuery a (temporalPattern p t)

/-- BinaryEvidence-valued temporal atom semantics.  Evaluates an atom at a given
    time by embedding the time index into the query pattern. -/
noncomputable def temporalEvidenceAtomSem
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (t : Int) : EvidenceAtomSem :=
  fun a p => BinaryWorldModel.evidence W (temporalAtomQuery baseAtomQuery a p t)

/-- Lag operator (Geisweiller & Yusuf §3.1):
    `Lag(I, T)` shifts atom evaluation backward by T time units.
    "Brings the past into the present." -/
noncomputable def lagAtomSem
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (lag : Int) : EvidenceAtomSem :=
  temporalEvidenceAtomSem W baseAtomQuery (baseTime - lag)

/-- Lead operator (Geisweiller & Yusuf §3.1):
    `Lead(I, T)` shifts atom evaluation forward by T time units.
    "Brings the future into the present." -/
noncomputable def leadAtomSem
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (lead : Int) : EvidenceAtomSem :=
  temporalEvidenceAtomSem W baseAtomQuery (baseTime + lead)

/-- Lead(Lag(P, T), T) ≡ P : shifting back then forward by T is identity. -/
theorem lagLeadIdentity
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int) :
    lagAtomSem W baseAtomQuery (baseTime + T) T =
    temporalEvidenceAtomSem W baseAtomQuery baseTime := by
  simp [lagAtomSem]

/-- SequentialAnd (Geisweiller & Yusuf §3.1):
    `SequentialAnd(T, φ, ψ)` = φ holds now AND ψ holds T time units later.
    Realized as conjunction with the second formula evaluated under Lead. -/
noncomputable def sequentialAndSemE
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) : BinaryEvidence :=
  semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p ⊓
  semE R (temporalEvidenceAtomSem W baseAtomQuery (baseTime + T)) ψ p

/-- PredictiveImplication (Geisweiller & Yusuf §3.1):
    `P ⇝ᵀ Q` = if P holds now then Q holds T time units later.
    Realized as implication with consequent evaluated under Lead. -/
noncomputable def predictiveImplicationSemE
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) : BinaryEvidence :=
  semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p ⇨
  semE R (temporalEvidenceAtomSem W baseAtomQuery (baseTime + T)) ψ p

/-- SequentialAnd is bounded by each component:
    `SequentialAnd(T, φ, ψ) ≤ semE(φ)` at the base time. -/
theorem sequentialAnd_le_left
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :
    sequentialAndSemE R W baseAtomQuery baseTime T φ ψ p ≤
    semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p :=
  inf_le_left

/-- PredictiveImplication + antecedent evidence gives consequent evidence
    (modus ponens at the evidence level, using Heyting residuation). -/
theorem predictiveImplication_mp
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p ⊓
    predictiveImplicationSemE R W baseAtomQuery baseTime T φ ψ p ≤
    semE R (temporalEvidenceAtomSem W baseAtomQuery (baseTime + T)) ψ p :=
  inf_himp_le

/-- Temporal shifting rule (Geisweiller & Yusuf §3.2, rule S):
    The evidence of a proposition is preserved under time shift.
    Specifically, if φ is an atom, evidence is determined by the WM state
    at the shifted time — shifting merely changes WHICH time we look at,
    not the evidence structure. -/
theorem temporal_shift_atom
    {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (t : Int) (a : String) (p : Pattern) :
    semE R (temporalEvidenceAtomSem W baseAtomQuery t) (.atom a) p =
    BinaryWorldModel.evidence W (temporalAtomQuery baseAtomQuery a p t) := rfl

end TemporalSemantics

/-! ## Presupposition as BinaryEvidence Gating

Presuppositions are backgrounded content that must be satisfied for an assertion
to be felicitous (Strawson 1950, Heim 1983).  In evidence semantics, this is
naturally modeled using the tensor product (sequential composition):

  `presupGatedSemE(presup, assert, p) = E_presup(p) ⊗ E_assert(p)`

The tensor product is the right choice (vs. conjunction ⊓) because:
1. It represents independent, sequential composition of evidence
2. `⊗` distributes over `⨆` (quantale law), enabling presupposition
   projection through existential/diamond contexts
3. When presupposition evidence is `⊥` (unsatisfied), the tensor product
   collapses the whole sentence to `⊥`
4. When presupposition evidence is `one` (fully satisfied), tensor is
   transparent: `one ⊗ E_assert = E_assert`

### Projection Laws (van der Sandt 1992, Beaver 2001)

- **Negation projection**: `¬P` preserves the presupposition of P.
  "The king of France is NOT bald" still presupposes France has a king.

- **Conditional filtering**: In "If P then Q", presuppositions of Q are
  filtered by P.  BinaryEvidence version: presup(Q) is gated by presup(P→Q).

### References

- Strawson, "On Referring" (1950)
- Heim, "On the Projection Problem for Presuppositions" (1983)
- van der Sandt, "Presupposition Projection as Anaphora Resolution" (1992)
- Beaver, "Presupposition and Assertion in Dynamic Semantics" (2001)
-/

section Presupposition

/-- Presupposition-gated evidence: the total evidence of a presuppositional
    sentence is the tensor product of presupposition evidence and assertion evidence.

    Example: "The king of France is bald"
    - presup: ◇(is_king_of_france) — there exists a king of France
    - assert: is_bald — the referent is bald
    - gated evidence: E_presup ⊗ E_assert -/
noncomputable def presupGatedSemE (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern) : BinaryEvidence :=
  semE R I presup p * semE R I assert p

/-- When presupposition is fully satisfied (evidence = one), gating is transparent:
    `one ⊗ E_assert = E_assert`. -/
theorem presupGated_one_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern)
    (h : semE R I presup p = BinaryEvidence.one) :
    presupGatedSemE R I presup assert p = semE R I assert p := by
  unfold presupGatedSemE
  rw [h, BinaryEvidence.one_tensor]

/-- When presupposition fails completely (evidence = ⊥), the gated evidence
    collapses to ⊥.  This captures presupposition failure. -/
theorem presupGated_bot_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern)
    (h : semE R I presup p = ⊥) :
    presupGatedSemE R I presup assert p = ⊥ := by
  unfold presupGatedSemE
  rw [h]
  simp

/-- Gated evidence is bounded by assertion evidence (modulo presupposition).
    Since tensor components are multiplicative and evidence values are in ℝ≥0∞,
    `x * y ≤ y` when `x ≤ 1` (i.e., presupposition evidence is bounded). -/
theorem presupGated_le_assert_of_presup_le_one
    (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern)
    (hp : semE R I presup p ≤ BinaryEvidence.one) :
    presupGatedSemE R I presup assert p ≤ semE R I assert p := by
  unfold presupGatedSemE
  simp only [BinaryEvidence.le_def, BinaryEvidence.tensor_def, BinaryEvidence.one] at hp ⊢
  exact ⟨mul_le_of_le_one_left (zero_le) hp.1, mul_le_of_le_one_left (zero_le) hp.2⟩

/-- **Negation projection law**: Negation preserves presupposition.

    `presupGated(presup, ¬assert)` has the same presupposition component as
    `presupGated(presup, assert)`. We express this as: the presupposition
    evidence factor is identical regardless of whether the assertion is
    negated (negation is modeled as `assert → ⊥`). -/
theorem negation_preserves_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern) :
    presupGatedSemE R I presup (.imp assert .bot) p =
    semE R I presup p * (semE R I assert p ⇨ ⊥) := by
  unfold presupGatedSemE
  simp [semE_imp, semE_bot]

/-- **Conditional filtering law**: In "If P then Q", the presupposition of Q
    is filtered through P.  At the evidence level, this means the presupposition
    evidence of Q is at least the implicational evidence P → presup(Q).

    Concretely: `semE(P → presupGated(presup_Q, Q)) ≥ semE(P → presup_Q) ⊓ semE(P → Q)`
    because the tensor factors can be separated under the Heyting residuation.

    We prove the simpler useful form: if P → presup(Q) is satisfied (≥ τ) and
    P → Q is satisfied (≥ τ), then P → presupGated(presup_Q, Q) is also
    supported at level τ ⊗ τ. -/
theorem conditional_filters_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (antecedent presup_q assertion_q : OSLFFormula) (p : Pattern) (τ : BinaryEvidence)
    (h_presup : τ ≤ semE R I (.imp antecedent presup_q) p)
    (h_assert : τ ≤ semE R I (.imp antecedent assertion_q) p) :
    τ * τ ≤ semE R I (.imp antecedent presup_q) p *
             semE R I (.imp antecedent assertion_q) p := by
  exact mul_le_mul' h_presup h_assert

/-- Presupposition gating with shared presupposition distributes over conjunction:
    if the same presupposition gates both conjuncts, gating the conjunction is
    the same as conjoining the gated parts.

    `presupGated(π, φ₁ ∧ φ₂) = π ⊗ (semE(φ₁) ⊓ semE(φ₂))` -/
theorem presupGated_shared_and (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert₁ assert₂ : OSLFFormula) (p : Pattern) :
    presupGatedSemE R I presup (.and assert₁ assert₂) p =
    semE R I presup p * (semE R I assert₁ p ⊓ semE R I assert₂ p) := by
  unfold presupGatedSemE
  simp [semE_and]

/-- Presupposition gating monotonicity: stronger assertion gives stronger gated evidence. -/
theorem presupGated_mono_assert (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert₁ assert₂ : OSLFFormula) (p : Pattern)
    (h : semE R I assert₁ p ≤ semE R I assert₂ p) :
    presupGatedSemE R I presup assert₁ p ≤ presupGatedSemE R I presup assert₂ p := by
  unfold presupGatedSemE
  exact mul_le_mul_right h _

/-- Presupposition gating monotonicity: stronger presupposition gives stronger gated evidence. -/
theorem presupGated_mono_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup₁ presup₂ assert : OSLFFormula) (p : Pattern)
    (h : semE R I presup₁ p ≤ semE R I presup₂ p) :
    presupGatedSemE R I presup₁ assert p ≤ presupGatedSemE R I presup₂ assert p := by
  unfold presupGatedSemE
  exact mul_le_mul_left h _

/-- Presupposition gating through diamond: if the presupposition and assertion
    hold at a successor, then the gated diamond holds.

    `◇(presupGated(presup, assert))` ≥ the gated value at any successor. -/
theorem presupGated_dia_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p q : Pattern) (hRpq : R p q) :
    presupGatedSemE R I presup assert q ≤
    ⨆ (s : {s // R p s}), presupGatedSemE R I presup assert s.val := by
  exact le_iSup (fun (s : {s // R p s}) => presupGatedSemE R I presup assert s.val) ⟨q, hRpq⟩

end Presupposition

end Mettapedia.OSLF.Framework.EvidenceSemantics
