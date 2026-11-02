import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingTheoremApplication

/-!
# Native MM0 theorem-step controls

The non-occurrence example is exercised through the actual guarded rewriting step, not
through the earlier proof interpreter. A repeated hypothesis is also read
from a single retained occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.TheoremControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def imp (left right : Preterm) : Preterm := .app (.app (.term 0) left) right
def all (bound body : Preterm) : Preterm := .app (.app (.term 1) bound) body

def signature : TermSignature
  | 0 => some ⟨[.regular 0 ∅, .regular 0 ∅], 0, ∅⟩
  | 1 => some ⟨[.bound 1, .regular 0 {0}], 0, ∅⟩
  | _ => none

def sorts : SortSignature := fun _ => some {}
def independentContext : Context := [.bound 1, .regular 0 ∅]
def dependentContext : Context := [.bound 1, .regular 0 {0}]
def arguments : List Preterm := [.var 0, .var 1]
def goal : Preterm := imp (.var 1) (all (.var 0) (.var 1))
def nf : TheoremDecl := ⟨[.bound 1, .regular 0 ∅], [], goal⟩

theorem independentContext_formed : Context.WellFormed sorts independentContext := by
  apply (Context.check_iff _ _).mp
  decide

theorem nf_instance : nf.Instantiates signature independentContext arguments ⟨[], goal⟩ := by
  apply (TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp
  decide

theorem nf_accepted :
    Step ContextualPatterns.layer (theoremRule signature independentContext "apply-nf" nf)
      {requestValue "apply-nf" (arguments.map (encode independentContext))}
      {proofValue independentContext goal} := by
  simpa using theoremRule_complete independentContext_formed "apply-nf" nf nf_instance 0 (by simp)

theorem nf_arguments_refused :
    admitArguments signature nf.arguments dependentContext (expressionAssignment dependentContext arguments) = none := by
  unfold admitArguments
  rw [show nf.arguments.length = arguments.length from rfl, readArguments_encoded]
  change (if checkAdmissibleNative [] signature nf.arguments dependentContext arguments = true
    then some arguments else none) = none
  rw [checkAdmissibleNative_eq canonical_nil]
  decide

theorem dependent_arguments_scoped :
    ∀ argument ∈ arguments, Term.supportedAt dependentContext.length (encode dependentContext argument) = true := by
  intro argument member
  rcases (show argument = .var 0 ∨ argument = .var 1 from by simpa [arguments] using member) with rfl | rfl
  · decide
  · simp [MM0ContextualSupport.encode, encodeVariable, dependentContext, dependencyFields,
      Term.supportedAt, Term.Fields.supportedAt]

/-- The forbidden dependency prevents every firing from this request. -/
theorem nf_refused (after : Multiset Tm) :
    ¬Step ContextualPatterns.layer (theoremRule signature dependentContext "apply-nf" nf)
      {requestValue "apply-nf" (arguments.map (encode dependentContext))} after := by
  rintro ⟨assignment, frame, taken, kept, made, binds, ⟨selected, takes, takenSame⟩,
    _, before, checks, _, _⟩
  cases takes with
  | cons head tail =>
    cases tail
    rename_i selectedRequest
    have requestMember : selectedRequest ∈ ({requestValue "apply-nf" (arguments.map (encode dependentContext))} : Multiset Tm) := by
      rw [before, ← takenSame]
      simp
    have requestSame : selectedRequest = requestValue "apply-nf" (arguments.map (encode dependentContext)) := by
      simpa using requestMember
    subst selectedRequest
    have left : ContextualPatterns.layer.Step (fun _ => none)
        (theoremRequest dependentContext.length nf.arguments.length "apply-nf")
        (requestValue "apply-nf" (arguments.map (encode dependentContext))) assignment := by
      refine ⟨?_, ?_, head⟩
      · intro _ _ impossible
        cases impossible
      · intro index absent
        apply binds index
        simpa [theoremRule, requestRule, nf] using absent
    have right : ContextualPatterns.layer.Step (fun _ => none)
        (theoremRequest dependentContext.length nf.arguments.length "apply-nf")
        (requestValue "apply-nf" (arguments.map (encode dependentContext)))
        (expressionAssignment dependentContext arguments) := by
      refine ⟨?_, ?_, ?_⟩
      · intro _ _ impossible
        cases impossible
      · intro index absent
        exact theoremRule_binds signature dependentContext "apply-nf" nf arguments rfl index (by
          simpa [theoremRule, requestRule, nf] using absent)
      · exact (ContextualPatterns.solves_iff _ _ _).mpr
          (theoremRequest_instantiation dependentContext arguments dependent_arguments_scoped "apply-nf")
    have same := ContextualPatterns.solution_unique (judgmentPattern_input _ _ _) left right
    subst assignment
    have impossible := checks
      ⟨theoremRequest dependentContext.length nf.arguments.length "apply-nf", fun assignment _ =>
        (admitArguments signature nf.arguments dependentContext assignment).isSome = true⟩
      (by simp [theoremRule, requestRule])
    change (admitArguments signature nf.arguments dependentContext
      (expressionAssignment dependentContext arguments)).isSome = true at impossible
    rw [nf_arguments_refused] at impossible
    cases impossible

def repeated : TheoremDecl := ⟨[.regular 0 ∅], [.var 0, .var 0], .var 0⟩

theorem repeated_instance : repeated.Instantiates signature independentContext [.var 1]
    ⟨[.var 1, .var 1], .var 1⟩ := by
  apply (TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp
  decide

theorem repeated_hypotheses_share_one_occurrence :
    Step ContextualPatterns.layer (theoremRule signature independentContext "apply-repeat" repeated)
      ({requestValue "apply-repeat" [encode independentContext (.var 1)]} + {proofValue independentContext (.var 1)})
      ({proofValue independentContext (.var 1)} + {proofValue independentContext (.var 1)}) := by
  apply theoremRule_complete independentContext_formed "apply-repeat" repeated repeated_instance
  intro expression member
  have same : expression = .var 1 := by simpa using member
  simp [same]

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.TheoremControls
