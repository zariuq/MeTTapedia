import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
import Mathlib.Data.List.Enum

open Mettapedia.OSLF.Framework

/-!
# Executable canonical successor coverage for the authored rho language

The input is the original `rhoCalc`, with its original COMM and ParCong
declarations, reflective substitution, QuoteDrop equation, and parallel
algebra. No permissive contextual companion is substituted for that language.

The admitted carrier is exactly its closed, well-sorted, quote-sealed process
family. Canonicalization is proved complete for the authored equations. The
finite matcher runs COMM on that representative; the canonical step theorem
accounts for every original ParCong derivation modulo those equations.

Matching alternatives keep their order and are never deduplicated when their
targets agree. Equation conversions are administration, rather than additional
primitive communication events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRuleUsing)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement

/-- Computable admission of precisely the original closed process family. -/
def admit (source : Pattern) : Bool :=
  checkOpenPatternWellSorted rhoCalc FreeTypeContext.empty [] (.base "Proc") source &&
    binderSafeAt "NQuote" 0 source

theorem admit_exact (source : Pattern) :
    admit source = true ↔ RhoClosedTermWellSorted rhoProc source := by
  rw [← closed_process_wellSorted_iff]
  simp only [admit, Bool.and_eq_true, checkOpenPatternWellSorted_eq_true_iff]
  constructor
  · rintro ⟨⟨typed, canonical, object, safe⟩, sealed⟩
    exact ⟨⟨typed, ground_of_closed_sorting (sort := rhoProc) typed object safe, canonical, object, safe⟩,
      (rho_scopeSafe_iff source).mpr sealed⟩
  · rintro ⟨⟨typed, _, canonical, object, safe⟩, sealed⟩
    exact ⟨⟨typed, canonical, object, safe⟩, (rho_scopeSafe_iff source).mp sealed⟩

def admittedProcess (source : Pattern) (accepted : admit source = true) : RhoProcess :=
  ⟨source, (admit_exact source).mp accepted⟩

/-- Exact original matched alternatives, on the canonical representative. -/
def alternatives (source : Pattern) : List Bindings :=
  matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite (canonicalize source)

/-- A finite original-COMM origin. Its index distinguishes equal alternatives. -/
structure Receipt where
  declarationIndex : Nat
  alternativeIndex : Nat
  bindings : Bindings
  rawTarget : Pattern
  target : Pattern
  deriving DecidableEq, Repr

def receipt (alternative : Bindings × Nat) : Receipt :=
  let raw := applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite alternative.1
  ⟨0, alternative.2, alternative.1, raw, canonicalize raw⟩

def receipts (source : Pattern) : List Receipt :=
  (alternatives source).zipIdx.map receipt

/-- Original declaration identities remain in the input semantic language. -/
theorem original_declarations :
    rhoCalc.rewrites = [rhoCommRewrite, rhoParCongRewrite] := rfl

theorem receipt_alternatives {source : Pattern} {item : Receipt}
    (listed : item ∈ receipts source) :
    item.declarationIndex = 0 ∧ item.bindings ∈ alternatives source ∧
      item.rawTarget = applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite item.bindings ∧
      item.target = canonicalize item.rawTarget := by
  obtain ⟨⟨bindings, index⟩, member, rfl⟩ := List.mem_map.mp listed
  have matched : bindings ∈ alternatives source := List.fst_mem_of_mem_zipIdx member
  exact ⟨rfl, matched, rfl, rfl⟩

theorem matched_receipt {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ alternatives source) :
    ∃ item ∈ receipts source, item.bindings = bindings := by
  obtain ⟨index, bound, equality⟩ := List.mem_iff_getElem.mp matched
  refine ⟨receipt (bindings, index), List.mem_map.mpr ?_, rfl⟩
  refine ⟨(bindings, index), ?_, rfl⟩
  rw [← equality]
  apply (List.mem_zipIdx_iff_getElem?).mpr
  simp only [List.getElem?_eq_getElem bound, equality]

theorem receipt_primitive {source : Pattern} {item : Receipt}
    (listed : item ∈ receipts source) :
    RhoStepAt 1 (canonicalize source) item.rawTarget := by
  obtain ⟨_, matched, raw, _⟩ := receipt_alternatives listed
  refine StepAt.rule (rule := rhoCommRewrite) (initialBindings := item.bindings)
    (finalBindings := item.bindings) (by simp [rhoCalc]) matched (PremisesAt.nil _) ?_
  exact raw.symm

theorem receipt_target_admitted {source : RhoProcess} {item : Receipt}
    (listed : item ∈ receipts source.1) :
    admit item.target = true := by
  let raw := source.canonicalize.stepTarget ⟨1, receipt_primitive listed⟩
  have closed : RhoClosedTermWellSorted rhoProc item.target := by
    rw [(receipt_alternatives listed).2.2.2]
    exact raw.canonicalize.2
  exact (admit_exact item.target).mpr closed

def receiptProcess (source : RhoProcess) (item : Receipt)
    (listed : item ∈ receipts source.1) : RhoProcess :=
  admittedProcess item.target (receipt_target_admitted listed)

theorem receipt_sound {source : RhoProcess} {item : Receipt}
    (listed : item ∈ receipts source.1) :
    rhoLanguageDefGSLT.Step source (receiptProcess source item listed) := by
  let raw := source.canonicalize.stepTarget ⟨1, receipt_primitive listed⟩
  refine ⟨source.canonicalize, raw, ?_, ?_, ?_⟩
  · change canonicalize source.1 = canonicalize (canonicalize source.1)
    exact (canonicalize_idempotent source.1).symm
  · exact ⟨1, receipt_primitive listed⟩
  · change canonicalize item.rawTarget = canonicalize item.target
    rw [(receipt_alternatives listed).2.2.2, canonicalize_idempotent]

/-- Every original modulo-equations successor has a listed canonical receipt. -/
theorem receipt_complete {source target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step source target) :
    ∃ item ∈ receipts source.1, item.target = canonicalize target.1 := by
  obtain ⟨redex, contractum, sourceEquivalent, primitive, targetEquivalent⟩ := step
  have closed := (rhoClosedTermWellSorted_process_iff redex.1).mp redex.2
  obtain ⟨rawTarget, canonicalStep, canonicalTarget⟩ :=
    canonicalStep_complete_of_rhoStep closed.1 primitive
  have canonicalStep' : RhoStepAt 1 (canonicalize source.1) rawTarget := by
    change canonicalize source.1 = canonicalize redex.1 at sourceEquivalent
    rw [sourceEquivalent]
    exact canonicalStep
  obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv canonicalStep'
  obtain ⟨item, listed, bindingsEq⟩ := matched_receipt matched
  refine ⟨item, listed, ?_⟩
  rw [(receipt_alternatives listed).2.2.2, (receipt_alternatives listed).2.2.1,
    bindingsEq, applied, canonicalTarget]
  exact targetEquivalent

/-- A complete comparison to the independently derived generic rho GSLT. -/
theorem original_successors_exact (source target : rhoReflectiveGSLT.Term) :
    rhoReflectiveGSLT.Step source target ↔
      ∃ item ∈ receipts source.1, item.target = canonicalize target.1 := by
  rw [presentedRhoStep_iff]
  constructor
  · exact receipt_complete
  · rintro ⟨item, listed, targetEq⟩
    have listed' : item ∈ receipts (presentedRhoProcessEquiv source).1 := listed
    have sound := receipt_sound listed'
    refine rhoProcessRewrites_resp_right sound ?_
    change canonicalize item.target = canonicalize target.1
    rw [targetEq, canonicalize_idempotent]

/-- Budget counts retained matched occurrences, including equal targets. -/
def frontier (budget : Nat) (source : Pattern) : List Receipt :=
  (receipts source).take budget

def pending (budget : Nat) (source : Pattern) : List Receipt :=
  (receipts source).drop budget

def closed (budget : Nat) (source : Pattern) : Bool :=
  decide ((receipts source).length ≤ budget)

def completionBudget (source : Pattern) : Nat := (receipts source).length

theorem complete_at (source : Pattern) :
    closed (completionBudget source) source = true := by
  simp [closed, completionBudget]

theorem complete_frontier {budget : Nat} {source : Pattern}
    (complete : closed budget source = true) : frontier budget source = receipts source := by
  exact List.take_of_length_le (of_decide_eq_true complete)

theorem frontier_sound {source : RhoProcess} {budget : Nat} {item : Receipt}
    (listed : item ∈ frontier budget source.1) :
    ∃ target : RhoProcess, target.1 = item.target ∧ rhoLanguageDefGSLT.Step source target := by
  have allListed : item ∈ receipts source.1 := List.mem_of_mem_take listed
  exact ⟨receiptProcess source item allListed, rfl, receipt_sound allListed⟩

theorem frontier_complete {source target : RhoProcess} {budget : Nat}
    (complete : closed budget source.1 = true) (step : rhoLanguageDefGSLT.Step source target) :
    ∃ item ∈ frontier budget source.1, item.target = canonicalize target.1 := by
  rw [complete_frontier complete]
  exact receipt_complete step

theorem frontier_partition (budget : Nat) (source : Pattern) :
    frontier budget source ++ pending budget source = receipts source := by
  exact List.take_append_drop budget (receipts source)

theorem exact_resume (first more : Nat) (source : Pattern) :
    frontier (first + more) source =
      frontier first source ++ (pending first source).take more := by
  exact List.take_add

theorem certified_empty_absence {source : RhoProcess} {budget : Nat}
    (complete : closed budget source.1 = true) (empty : frontier budget source.1 = []) :
    ∀ target : RhoProcess, ¬ rhoLanguageDefGSLT.Step source target := by
  intro target step
  obtain ⟨item, listed, _⟩ := frontier_complete complete step
  rw [empty] at listed
  exact List.not_mem_nil listed

/-- A retained receipt in the exact generic authored-language carrier. -/
abbrev OriginalReceipt (source : rhoReflectiveGSLT.Term) :=
  { item : Receipt // item ∈ receipts source.1 }

def originalFrontier (budget : Nat) (source : rhoReflectiveGSLT.Term) :
    List (OriginalReceipt source) :=
  (frontier budget source.1).attach.map fun item =>
    ⟨item.1, List.mem_of_mem_take item.2⟩

def originalTarget (source : rhoReflectiveGSLT.Term) (item : OriginalReceipt source) :
    rhoReflectiveGSLT.Term :=
  presentedRhoProcessEquiv.symm (receiptProcess (presentedRhoProcessEquiv source) item.1 item.2)

@[simp]
theorem originalTarget_pattern (source : rhoReflectiveGSLT.Term) (item : OriginalReceipt source) :
    (originalTarget source item).1 = item.1.target := rfl

theorem originalTarget_sound (source : rhoReflectiveGSLT.Term) (item : OriginalReceipt source) :
    rhoReflectiveGSLT.Step source (originalTarget source item) := by
  apply presentedRhoStep_complete
  simpa only [originalTarget, presentedRhoProcessEquiv_apply_symm] using receipt_sound item.2

theorem originalFrontier_mem {budget : Nat} {source : rhoReflectiveGSLT.Term}
    (item : OriginalReceipt source) :
    item ∈ originalFrontier budget source ↔ item.1 ∈ frontier budget source.1 := by
  constructor
  · intro listed
    obtain ⟨candidate, listed, same⟩ := List.mem_map.mp listed
    have equal : candidate.1 = item.1 := congrArg Subtype.val same
    rw [← equal]
    exact candidate.2
  · intro listed
    refine List.mem_map.mpr ⟨⟨item.1, listed⟩, ?_, ?_⟩
    · exact List.mem_attach _ _
    · rfl

theorem originalFrontier_stable (source : rhoReflectiveGSLT.Term) (budget : Nat)
    (enough : completionBudget source.1 ≤ budget) :
    originalFrontier budget source = originalFrontier (completionBudget source.1) source := by
  apply (List.map_inj_right (fun left right same => Subtype.ext same)).mp
  simp only [originalFrontier, List.map_map, Function.comp_def]
  change (frontier budget source.1).attach.map Subtype.val =
    (frontier (completionBudget source.1) source.1).attach.map Subtype.val
  rw [List.attach_map_subtype_val, List.attach_map_subtype_val]
  rw [complete_frontier (decide_eq_true enough), complete_frontier (complete_at source.1)]

theorem closed_stable (source : Pattern) (budget : Nat)
    (enough : completionBudget source ≤ budget) :
    closed budget source = closed (completionBudget source) source := by
  rw [complete_at]
  exact decide_eq_true enough

theorem originalFrontier_coverage {budget : Nat} {source target : rhoReflectiveGSLT.Term}
    (complete : closed budget source.1 = true) (step : rhoReflectiveGSLT.Step source target) :
    ∃ item ∈ originalFrontier budget source,
      rhoReflectiveGSLT.Equiv (originalTarget source item) target := by
  obtain ⟨item, listed, equal⟩ := (original_successors_exact source target).mp step
  let owned : OriginalReceipt source := ⟨item, listed⟩
  refine ⟨owned, (originalFrontier_mem owned).mpr ?_, ?_⟩
  · rw [complete_frontier complete]
    exact listed
  · apply presentedRhoEquations_complete
    change canonicalize item.target = canonicalize target.1
    rw [equal, canonicalize_idempotent]

/-- Equation comparison against the original presentation, not a smaller plan. -/
theorem original_equations_exact (left right : rhoReflectiveGSLT.Term) :
    rhoReflectiveGSLT.Equiv left right ↔ canonicalize left.1 = canonicalize right.1 := by
  exact presentedRhoEquations_iff left right

theorem originalTarget_admitted (source : rhoReflectiveGSLT.Term) (item : OriginalReceipt source) :
    admit (originalTarget source item).1 = true :=
  receipt_target_admitted (source := presentedRhoProcessEquiv source) item.2

/-- Finite targets for a raw-pattern caller after successful source admission. -/
def targets (budget : Nat) (source : Pattern) : List Pattern :=
  (frontier budget source).map Receipt.target

theorem targets_admitted {source : Pattern} {budget : Nat}
    (accepted : admit source = true) {target : Pattern}
    (listed : target ∈ targets budget source) : admit target = true := by
  obtain ⟨item, receiptListed, rfl⟩ := List.mem_map.mp listed
  exact receipt_target_admitted (source := admittedProcess source accepted)
    (List.mem_of_mem_take receiptListed)

#print axioms admit_exact
#print axioms receipt_sound
#print axioms receipt_complete
#print axioms original_successors_exact
#print axioms originalFrontier_coverage
#print axioms original_equations_exact
#print axioms exact_resume

end Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical
