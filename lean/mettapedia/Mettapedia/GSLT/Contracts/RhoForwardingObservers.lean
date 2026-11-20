import Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
import Mettapedia.GSLT.Contracts.PaperRhoOrderedSearch
import Mettapedia.GSLT.Contracts.PaperRhoParallel

/-!
# Forwarding and its observers

Substitution transports equivalent payloads directly in the locally
nameless source. There is no encoding, decoding, or normalization of
the body in that proof. Normalizing a payload once can therefore
serve all receivers that observe the paper's equation classes. The
converse holds for an unrestricted choice of closed continuation:
one continuation simply runs the received code.

Binder display metadata and the identity of unresolved free variables
are different. The paper embedding already has canonical binder
metadata, so a second alpha-erasure pass on its output is redundant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.ForwardingObservers

open Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses (NormalForms)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open OrderedSearch (structuralEquations)
open PatternBoundary (encodeProcess encodeName)

private theorem bindName_payload {p q : Process} (equivalent : Congruence p q)
    (depth : Nat) (name : Name) :
    NameEquivalence (bindName p depth name) (bindName q depth name) := by
  unfold bindName
  split
  · exact .quote equivalent
  · exact .refl _

/-- Congruent payloads remain congruent after substitution into any
body, including when the received code is activated by a drop. -/
theorem substitute_payload_congruent {p q : Process} (equivalent : Congruence p q)
    (body : Process) (depth : Nat) :
    Congruence (substitute p depth body) (substitute q depth body) := by
  cases body with
  | zero => exact .refl _
  | par a b =>
      exact .par (substitute_payload_congruent equivalent a depth)
        (substitute_payload_congruent equivalent b depth)
  | send n tail =>
      exact .send (bindName_payload equivalent depth n)
        (substitute_payload_congruent equivalent tail depth)
  | receive n tail =>
      exact .receive (bindName_payload equivalent depth n)
        (substitute_payload_congruent equivalent tail (depth + 1))
  | drop n =>
      unfold substitute
      by_cases selected : binderIndex n = some depth
      · simpa only [if_pos selected] using equivalent
      · simp only [if_neg selected]
        exact .refl _
termination_by structural body

theorem reuse_payload_at_quotient {p q : Process} (equivalent : Congruence p q)
    {Answer : Type*} (read : Quotient structuralEquations → Answer)
    (body : Process) (depth : Nat) :
    read (Quotient.mk _ (substitute p depth body)) =
      read (Quotient.mk _ (substitute q depth body)) :=
  congrArg read (Quotient.sound (s := structuralEquations)
    (substitute_payload_congruent equivalent body depth))

def ClosedObserver {Answer : Type*} (read : Process → Answer) : Prop :=
  ∀ {p q}, ScopedProcess 0 p → ScopedProcess 0 q → Congruence p q → read p = read q

/-- An exact criterion for using a canonical payload for all closed
receivers. Normalizing the payload neither changes the output in a
class observer nor supplies an observer that was missing. -/
theorem prepare_payload_once_iff {Answer : Type*} (forms : NormalForms structuralEquations)
    (read : Process → Answer) :
    (∀ payload, ScopedProcess 0 payload → ∀ body, ScopedProcess 1 body →
      read (substitute (forms.normal payload) 0 body) = read (substitute payload 0 body)) ↔
      ClosedObserver read := by
  constructor
  · intro safe p q pClosed qClosed equivalent
    have activates : ScopedProcess 1 (.drop (.bound 0)) := .drop (.bound (by decide))
    have first : read (forms.normal p) = read p := safe p pClosed _ activates
    have second : read (forms.normal q) = read q := safe q qClosed _ activates
    exact first.symm.trans ((congrArg read (forms.same equivalent)).trans second)
  · intro invariant p pClosed body bodyScoped
    have normalizedClosed : ScopedProcess 0 (forms.normal p) :=
      ((Congruence.scoped_iff (forms.sound p)) 0).mpr pClosed
    exact invariant ((substitute_fits _ _ _).lowers_scope bodyScoped normalizedClosed)
      ((substitute_fits _ _ _).lowers_scope bodyScoped pClosed)
      (substitute_payload_congruent (forms.sound p) body 0)

mutual
  theorem encodedName_has_no_binder_metadata (n : Name) :
      (encodeName n).hasCanonicalBinderMetadata = true := by
    cases n with
    | bound _ => rfl
    | quote code =>
        simp [encodeName, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
          encodedProcess_has_no_binder_metadata code]
  termination_by structural n

  theorem encodedProcess_has_no_binder_metadata (p : Process) :
      (encodeProcess p).hasCanonicalBinderMetadata = true := by
    cases p with
    | zero => rfl
    | par a b =>
        simp [encodeProcess, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
          encodedProcess_has_no_binder_metadata a, encodedProcess_has_no_binder_metadata b]
    | send n tail =>
        simp [encodeProcess, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
          encodedName_has_no_binder_metadata n, encodedProcess_has_no_binder_metadata tail]
    | receive n tail =>
        simp [encodeProcess, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
          encodedName_has_no_binder_metadata n, encodedProcess_has_no_binder_metadata tail]
    | drop n =>
        simp [encodeProcess, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
          encodedName_has_no_binder_metadata n]
  termination_by structural p
end

theorem encodedProcess_skips_alpha_erasure (p : Process) :
    (encodeProcess p).eraseBinderMetadata = encodeProcess p :=
  Pattern.eraseBinderMetadata_eq_self_of_canonical (encodedProcess_has_no_binder_metadata p)

namespace Controls

open Separation (base)

private def forwardingBody : Process := .send (.bound 0) .zero
private def payload : Process := .drop base
private def anotherSpelling : Process := .par payload .zero

theorem paper_forwarding_agrees_literal_print_can_differ :
    Congruence (substitute payload 0 forwardingBody) (substitute anotherSpelling 0 forwardingBody) ∧
      ¬ ProcEq (substitute payload 0 forwardingBody) (substitute anotherSpelling 0 forwardingBody) := by
  refine ⟨substitute_payload_congruent (.symm (.unit _)) _ _, ?_⟩
  exact ParallelControls.forwarding_observes_payload_representative.2.2.2

theorem raw_output_is_not_a_closed_class_observer :
    ¬ ClosedObserver (id : Process → Process) := by
  intro invariant
  have p : ScopedProcess 0 payload := .drop (.literal .zero)
  have q : ScopedProcess 0 anotherSpelling := .par p .zero
  have wrong : payload = anotherSpelling := invariant p q (.symm (.unit _))
  cases wrong

theorem resolved_binding_and_unresolved_spelling_are_distinct :
    Pattern.AlphaEquiv (.lambda (some "x") (.bvar 0)) (.lambda (some "y") (.bvar 0)) ∧
      ¬ Pattern.AlphaEquiv (.lambda (some "x") (.fvar "x")) (.lambda (some "y") (.fvar "y")) := by
  simp [Pattern.AlphaEquiv, Pattern.eraseBinderMetadata]

end Controls

#print axioms substitute_payload_congruent
#print axioms prepare_payload_once_iff
#print axioms encodedProcess_skips_alpha_erasure
#print axioms Controls.paper_forwarding_agrees_literal_print_can_differ
#print axioms Controls.raw_output_is_not_a_closed_class_observer
#print axioms Controls.resolved_binding_and_unresolved_spelling_are_distinct

end Mettapedia.GSLT.Contracts.PaperRho.ForwardingObservers
