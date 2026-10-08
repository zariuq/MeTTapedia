import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement

/-!
# The full closed COMM family on canonical bags

The reaction family is authored independently from the executable matcher:
an input and an output with equal canonical names produce the semantic
capture-avoiding substitution result. An arbitrary bag is retained as the
parallel residue. Its contextual reaction relation is exactly the public
equation-saturated closed rho step. Free drop remains inert in this profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement

def input (channel body : Pattern) : Pattern :=
  .apply "PInput" [channel, .lambda none body]

def output (channel payload : Pattern) : Pattern :=
  .apply "POutput" [channel, payload]

/-- Every closed canonical COMM instance, with its actual name equation. -/
structure GroundComm where
  inputChannel : Pattern
  outputChannel : Pattern
  body : Pattern
  payload : Pattern
  inputPrime : IsPrime (input inputChannel body)
  outputPrime : IsPrime (output outputChannel payload)
  channels : canonicalize inputChannel = canonicalize outputChannel

namespace GroundComm

theorem body_typed (rule : GroundComm) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] rule.body :=
  (rho_input_wellSorted_inv
    ((rhoClosedTermWellSorted_process_iff _).mp rule.inputPrime.1).1).2.2

theorem body_safe (rule : GroundComm) :
    binderSafeAt "NQuote" 1 rule.body = true :=
  (binderSafe_of_input
    ((rhoClosedTermWellSorted_process_iff _).mp rule.inputPrime.1).2).2

theorem payload_typed (rule : GroundComm) :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] rule.payload :=
  (rho_output_wellSorted_inv
    ((rhoClosedTermWellSorted_process_iff _).mp rule.outputPrime.1).1).2

theorem payload_safe (rule : GroundComm) :
    binderSafeAt "NQuote" 0 rule.payload = true := by
  have safe := ((rhoClosedTermWellSorted_process_iff _).mp rule.outputPrime.1).2
  change binderSafeAt "NQuote" 0 (output rule.outputChannel rule.payload) = true at safe
  have components : binderSafeAt "NQuote" 0 rule.outputChannel = true ∧
      binderSafeAt "NQuote" 0 rule.payload = true := by
    simpa [output, binderSafeAt, binderSafeListAt] using safe
  exact components.2

/-- The result is computed from the supplied body and payload, not by execution. -/
def result (rule : GroundComm) : RhoProcess :=
  ⟨semanticCommSubst rule.body rule.payload,
    (rhoClosedTermWellSorted_process_iff _).mpr
      (semanticCommSubst_preserves rule.body_typed rule.body_safe
        rule.payload_typed rule.payload_safe)⟩

def redex (rule : GroundComm) : Bag :=
  ⟨([input rule.inputChannel rule.body, output rule.outputChannel rule.payload] :
      List Pattern), fun pattern membership => by
    simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact rule.inputPrime
    · exact rule.outputPrime⟩

def reactum (rule : GroundComm) : Bag := fromProcess rule.result

theorem source_primes (rule : GroundComm) (residue : Bag) :
    ∀ pattern ∈ input rule.inputChannel rule.body ::
      output rule.outputChannel rule.payload :: ordered residue.1, IsPrime pattern := by
  intro pattern membership
  simp only [List.mem_cons] at membership
  rcases membership with rfl | rfl | membership
  · exact rule.inputPrime
  · exact rule.outputPrime
  · exact ordered_prime residue membership

def source (rule : GroundComm) (residue : Bag) : RhoProcess :=
  ofList (input rule.inputChannel rule.body ::
    output rule.outputChannel rule.payload :: ordered residue.1)
    (fun _ membership => (rule.source_primes residue _ membership).1)

def target (rule : GroundComm) (residue : Bag) : RhoProcess :=
  ofList (rule.result.1 :: ordered residue.1) (fun pattern membership => by
    rcases List.mem_cons.mp membership with rfl | membership
    · exact rule.result.2
    · exact (ordered_prime residue membership).1)

theorem source_inventory (rule : GroundComm) (residue : Bag) :
    fromProcess (rule.source residue) = append rule.redex residue := by
  apply Subtype.ext
  unfold source
  rw [fromProcess_ofList_primes _ (rule.source_primes residue)]
  change (([input rule.inputChannel rule.body, output rule.outputChannel rule.payload] ++
    ordered residue.1 : List Pattern) : Multiset Pattern) = _
  rw [← Multiset.coe_add, ordered_multiset]
  rfl

theorem target_inventory (rule : GroundComm) (residue : Bag) :
    fromProcess (rule.target residue) = append rule.reactum residue := by
  apply Subtype.ext
  unfold target
  rw [fromProcess_cons_primes rule.result _ _
    (fun _ membership => ordered_prime residue membership), ordered_multiset]
  rfl

/-- The independent instance agrees with the actual compiled COMM matcher. -/
theorem step (rule : GroundComm) (residue : Bag) :
    RhoStep (rule.source residue).1 (rule.target residue).1 := by
  have actual := rhoStepAt_one_comm
    (inputIndex := 0) (outputIndex := 0)
    (elements := input rule.inputChannel rule.body ::
      output rule.outputChannel rule.payload :: ordered residue.1)
    (by simp) (by simp) rfl rfl
    (rhoCanonicalEquivalent_iff _ _ |>.mpr rule.channels)
  rw [apply_commBindingsAt rule.body_typed rule.payload_typed] at actual
  exact ⟨1, by simpa [source, target, result, ofList] using actual⟩

end GroundComm

/-- Contextual reaction of the independently formed whole COMM family. -/
def Reaction (source target : Bag) : Prop :=
  ∃ rule : GroundComm, ∃ residue : Bag,
    source = append rule.redex residue ∧ target = append rule.reactum residue

/-- Adding an actual parallel residue preserves the same reaction instance. -/
theorem reaction_frame {source target : Bag} (reaction : Reaction source target)
    (frame : Bag) : Reaction (append source frame) (append target frame) := by
  obtain ⟨rule, residue, rfl, rfl⟩ := reaction
  exact ⟨rule, append residue frame, append_assoc _ _ _, append_assoc _ _ _⟩

theorem reaction_public {source target : Bag} (reaction : Reaction source target) :
    rhoLanguageDefGSLT.Step (toProcess source) (toProcess target) := by
  obtain ⟨rule, residue, rfl, rfl⟩ := reaction
  refine ⟨rule.source residue, rule.target residue, ?_, rule.step residue, ?_⟩
  · apply (fromProcess_eq_iff _ _).mp
    rw [fromProcess_toProcess, rule.source_inventory]
  · apply (fromProcess_eq_iff _ _).mp
    rw [rule.target_inventory, fromProcess_toProcess]

/-- Every actual public step selects an instance of the independent family.
Canonical completeness exposes COMM rather than treating a successful step
as its own reaction certificate. -/
theorem public_reaction {source target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step source target) :
    Reaction (fromProcess source) (fromProcess target) := by
  obtain ⟨redex, contractum, sourceEquation, reduces, targetEquation⟩ := step
  have closed := (rhoClosedTermWellSorted_process_iff redex.1).mp redex.2
  obtain ⟨target', canonicalStep, canonicalTarget⟩ :=
    canonicalStep_complete_of_rhoStep closed.1 closed.2 reduces
  change canonicalize source.1 = canonicalize redex.1 at sourceEquation
  rw [← sourceEquation] at canonicalStep
  obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv canonicalStep
  obtain ⟨elements, rest, i, iBound, j, jBound, inputChannel, body, binder,
    outputChannel, payload, sourceShape, inputShape, outputShape, channels,
    bindingsShape⟩ := rhoComm_match_shape matched
  have sourceClosed := (rhoClosedTermWellSorted_process_iff source.1).mp source.2
  have sourceTyped := canonicalize_procWellSorted [] sourceClosed.1
  rw [sourceShape] at sourceTyped
  obtain ⟨rfl, _⟩ := rho_parallel_wellSorted_inv sourceTyped
  have actualContents := contents_of_canonical_bag source sourceShape
  have allPrime : ∀ pattern ∈ elements, IsPrime pattern := by
    intro pattern membership
    exact contents_prime source (by rw [actualContents]; exact membership)
  have inputPrime := allPrime elements[i] (List.getElem_mem iBound)
  have outputPrime := allPrime (elements.eraseIdx i)[j]
    (List.mem_of_mem_eraseIdx (List.getElem_mem jBound))
  rw [inputShape] at inputPrime
  rw [outputShape] at outputPrime
  obtain ⟨rfl, _, _⟩ := rho_input_wellSorted_inv
    ((rhoClosedTermWellSorted_process_iff _).mp inputPrime.1).1
  let rule : GroundComm :=
    ⟨inputChannel, outputChannel, body, payload, inputPrime, outputPrime,
      (rhoCanonicalEquivalent_iff _ _).mp channels⟩
  let tail := (elements.eraseIdx i).eraseIdx j
  have tailPrimes : ∀ pattern ∈ tail, IsPrime pattern := by
    intro pattern membership
    exact allPrime pattern (mem_of_mem_eraseIdx_eraseIdx membership)
  let residue : Bag := ⟨(tail : Multiset Pattern), fun _ membership =>
    tailPrimes _ (by simpa using membership)⟩
  have permutation : List.Perm elements
      (input rule.inputChannel rule.body ::
        output rule.outputChannel rule.payload :: tail) := by
    have perm : List.Perm elements
        (elements[i] :: (elements.eraseIdx i)[j] :: tail) :=
      ((List.getElem_cons_eraseIdx_perm jBound).cons _ |>.trans
        (List.getElem_cons_eraseIdx_perm iBound)).symm
    simpa [rule, input, output, inputShape, outputShape] using perm
  have targetShape : target' =
      .collection .hashBag (rule.result.1 :: tail) none := by
    rw [← applied, bindingsShape]
    exact apply_commBindingsAt rule.body_typed rule.payload_typed elements i j inputChannel
  let targetPresentation : RhoProcess :=
    ofList (rule.result.1 :: tail) (fun pattern membership => by
      rcases List.mem_cons.mp membership with rfl | membership
      · exact rule.result.2
      · exact (tailPrimes pattern membership).1)
  refine ⟨rule, residue, ?_, ?_⟩
  · apply Subtype.ext
    change (contents source : Multiset Pattern) =
      ([input rule.inputChannel rule.body, output rule.outputChannel rule.payload] :
        List Pattern) + (tail : Multiset Pattern)
    rw [actualContents, Multiset.coe_add]
    exact Multiset.coe_eq_coe.mpr permutation
  · have equivalent : rhoProcessEquations.r target targetPresentation := by
      change canonicalize target.1 =
        canonicalize (.collection .hashBag (rule.result.1 :: tail) none)
      rw [← targetShape, canonicalTarget]
      exact targetEquation.symm
    have equality := (fromProcess_eq_iff _ _).mpr equivalent
    rw [equality]
    apply Subtype.ext
    rw [fromProcess_cons_primes rule.result tail _ tailPrimes]
    rfl

/-- Public saturated closed steps and canonical bag reactions coincide. -/
theorem publicStep_iff (source target : RhoProcess) :
    rhoLanguageDefGSLT.Step source target ↔
      Reaction (fromProcess source) (fromProcess target) := by
  constructor
  · exact public_reaction
  · intro reaction
    obtain ⟨redex, contractum, sourceEquation, reduces, targetEquation⟩ :=
      reaction_public reaction
    rw [toProcess_fromProcess] at sourceEquation targetEquation
    refine ⟨redex, contractum, ?_, reduces, ?_⟩
    · change canonicalize source.1 = canonicalize redex.1
      change canonicalize (canonicalize source.1) = canonicalize redex.1 at sourceEquation
      rwa [canonicalize_idempotent] at sourceEquation
    · change canonicalize contractum.1 = canonicalize target.1
      change canonicalize contractum.1 = canonicalize (canonicalize target.1) at targetEquation
      rwa [canonicalize_idempotent] at targetEquation

theorem reaction_iff_publicStep (source target : Bag) :
    Reaction source target ↔ rhoLanguageDefGSLT.Step (toProcess source) (toProcess target) := by
  rw [publicStep_iff, fromProcess_toProcess, fromProcess_toProcess]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
