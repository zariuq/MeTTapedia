import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeCapture
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads

/-!
# The typing packet determines actual scoped inference

Filtering unrelated rows preserves the complete subtype traversal, including
fresh-name supplies and unfinished results. Annotation reads additionally
require stable outer row shapes: an opaque root or head must not become a
declaration when observed. The executable gate admits unrelated mutable data
inside an ordinary non-typing row, rather than requiring every stored atom
to be immutable.

These are source representation laws. Native opaque-header classification,
index coverage and compressed dependency tokens require their own codecs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSourceProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypingScopeCapture NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView observe observeList)

/-- Only opaque values that could replace a whole row or its three-field
head are excluded by this shape test. Fields of unrelated data stay free. -/
def rowShapeKnown : Atom → Bool
  | .grounded (.custom _ _) => false
  | .expression [.grounded (.custom _ _), _, _] => false
  | _ => true

theorem potential_wrong_arity (children : List Atom) (different : children.length ≠ 3) :
    potentialTypingRow (.expression children) = false := by
  unfold potentialTypingRow
  split <;> simp_all

theorem observeList_length (external : ExternalView) (atoms : List Atom) :
    (observeList external atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp only [observeList, List.length_cons, ih]

theorem potential_observe (external : ExternalView) (row : Atom)
    (known : rowShapeKnown row = true) :
    potentialTypingRow (observe external row) = potentialTypingRow row := by
  cases row with
  | symbol _ | var _ => rfl
  | grounded value => cases value <;> simp_all [rowShapeKnown, observe, potentialTypingRow]
  | expression children =>
      by_cases length : children.length = 3
      · obtain ⟨head, first, second, rfl⟩ := List.length_eq_three.mp length
        cases head with
        | symbol _ | var _ | expression _ => rfl
        | grounded value =>
            cases value <;> simp_all [rowShapeKnown, observe, observeList, potentialTypingRow]
      · rw [observe, potential_wrong_arity children length,
          potential_wrong_arity _ (by simpa only [observeList_length] using length)]

theorem capture_observed (external : ExternalView) (rows : List Atom)
    (shapes : rows.all rowShapeKnown = true)
    (safe : TypeDependencyAdmission.resourceFreeList (capture rows) = true) :
    capture (observeList external rows) = capture rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have shape := Bool.and_eq_true_iff.mp shapes
      have classified := potential_observe external row shape.1
      cases relevant : potentialTypingRow row with
      | false =>
          have tailSafe : TypeDependencyAdmission.resourceFreeList (capture rows) = true := by
            simpa [capture, relevant] using safe
          simpa only [observeList, capture, List.filter_cons, classified, relevant,
            Bool.false_eq_true, if_false] using ih shape.2 tailSafe
      | true =>
          have both : TypeDependencyAdmission.resourceFree row = true ∧
              TypeDependencyAdmission.resourceFreeList (capture rows) = true := by
            simpa [capture, relevant, TypeDependencyAdmission.resourceFreeList] using safe
          have unchanged := TypeDependencyAdmission.observe_resourceFree external row both.1
          simp only [observeList, capture, List.filter_cons, classified, relevant, if_true]
          rw [unchanged]
          exact congrArg (row :: ·) (ih shape.2 both.2)

def readyRows (rows : List Atom) : Bool := rows.all rowShapeKnown && freshScan rows

theorem ready_safe (rows : List Atom) (ready : readyRows rows = true) :
    TypeDependencyAdmission.resourceFreeList (capture rows) = true :=
  freshScan_capture_resourceFree rows (Bool.and_eq_true_iff.mp ready).2

theorem ready_observed (external : ExternalView) (rows : List Atom)
    (ready : readyRows rows = true) : capture (observeList external rows) = capture rows :=
  capture_observed external rows (Bool.and_eq_true_iff.mp ready).1 (ready_safe rows ready)

/-- The raw annotation reader, not an assumed inference oracle. -/
theorem annotation_packet (external : ExternalView) (rows : List Atom)
    (ready : readyRows rows = true) (subject : Atom) :
    getAnnotatedTypes (TypeDependencyAdmission.observedSpace external rows) subject =
      getAnnotatedTypes ⟨capture rows⟩ subject := by
  change getAnnotatedTypes ⟨observeList external rows⟩ subject = _
  rw [← annotations_capture subject (observeList external rows), ready_observed external rows ready]

theorem possible_is_potential (row : Atom) (possible : ScopedSubtypeReads.possibleRow row = true) :
    potentialTypingRow row = true := by
  unfold ScopedSubtypeReads.possibleRow at possible
  split at possible
  · rfl
  · rfl
  · simp [potentialTypingRow]
  · contradiction

/-- Every omitted row is skipped before allocation by the actual row walker. -/
theorem subtype_rows_capture (external : ExternalView) (input : Atom) (resultName : String)
    (rows : List Atom) : ∀ supply,
    ScopedSubtypeReads.rows external input resultName (capture rows) supply =
      ScopedSubtypeReads.rows external input resultName rows supply := by
  induction rows with
  | nil => intro supply; rfl
  | cons row rows ih =>
      intro supply
      simp only [capture] at ih
      cases relevant : potentialTypingRow row with
      | false =>
          have skipped : ScopedSubtypeReads.possibleRow row = false := by
            cases possible : ScopedSubtypeReads.possibleRow row with
            | false => rfl
            | true => have yes := possible_is_potential row possible; simp_all
          simpa only [capture, List.filter_cons, relevant, Bool.false_eq_true, if_false,
            ScopedSubtypeReads.rows, skipped] using ih supply
      | true =>
          simp only [capture, List.filter_cons, relevant, if_true, ScopedSubtypeReads.rows]
          split
          · rw [ih]
          · exact ih supply

theorem subtype_query_capture (external : ExternalView) (rows : List Atom) (base : String)
    (input : Atom) (supply : Supply) :
    ScopedSubtypeReads.query external (capture rows) base input supply =
      ScopedSubtypeReads.query external rows base input supply := by
  unfold ScopedSubtypeReads.query
  rw [subtype_rows_capture]

theorem discoveries_capture (external : ExternalView) (rows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State)
    (frontier : List (SubtypeClosureRounds.Entry × Nat)) : ∀ supply,
    ScopedSubtypeReads.discoveries external (capture rows) base alpha before frontier supply =
      ScopedSubtypeReads.discoveries external rows base alpha before frontier supply := by
  induction frontier with
  | nil => intro supply; rfl
  | cons pair rest ih =>
      intro supply
      simp only [ScopedSubtypeReads.discoveries]
      split
      · exact ih supply
      · rw [subtype_query_capture, ih]

theorem subtype_round_capture (external : ExternalView) (rows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (before : SubtypeClosureRounds.State) (supply : Supply) :
    ScopedSubtypeReads.round external (capture rows) base alpha before supply =
      ScopedSubtypeReads.round external rows base alpha before supply := by
  unfold ScopedSubtypeReads.round
  rw [discoveries_capture]

theorem subtype_run_capture (external : ExternalView) (rows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (budget : Nat) : ∀ before supply,
    ScopedSubtypeReads.run external (capture rows) base alpha budget before supply =
      ScopedSubtypeReads.run external rows base alpha budget before supply := by
  induction budget with
  | zero => intro before supply; rfl
  | succ budget ih =>
      intro before supply
      simp only [ScopedSubtypeReads.run, subtype_round_capture]
      split
      · rfl
      · exact ih _ _

theorem subtype_complete_capture (external : ExternalView) (rows : List Atom) (base : String)
    (alpha : Atom → Atom → Bool) (budget : Nat) (seeds : List Atom) (supply : Supply) :
    ScopedSubtypeReads.completeTypes external (capture rows) base alpha budget seeds supply =
      ScopedSubtypeReads.completeTypes external rows base alpha budget seeds supply := by
  unfold ScopedSubtypeReads.completeTypes
  rw [subtype_run_capture]

def project (source : Source) : Source :=
  { source with rows := capture source.rows, intrinsicRows := capture source.intrinsicRows }

def ready (source : Source) : Bool := readyRows source.rows && readyRows source.intrinsicRows

theorem project_safe (source : Source) (accepted : ready source = true) :
    NativeTypeSourcePorts.Safe (project source) :=
  ⟨ready_safe source.rows (Bool.and_eq_true_iff.mp accepted).1,
    ready_safe source.intrinsicRows (Bool.and_eq_true_iff.mp accepted).2⟩

theorem raw_declarations_project (source : Source) (external : ExternalView)
    (accepted : ready source = true) (subject : Atom) :
    rawDeclarations (project source) external subject = rawDeclarations source external subject := by
  have both := Bool.and_eq_true_iff.mp accepted
  have own : getAnnotatedTypes (TypeDependencyAdmission.observedSpace external (capture source.rows)) subject =
      getAnnotatedTypes (TypeDependencyAdmission.observedSpace external source.rows) subject := by
    calc
      _ = getAnnotatedTypes ⟨capture source.rows⟩ subject := by
        simp only [TypeDependencyAdmission.observedSpace,
          TypeDependencyAdmission.observeList_resourceFree external _ (ready_safe source.rows both.1)]
      _ = _ := (annotation_packet external source.rows both.1 subject).symm
  have intrinsic : getAnnotatedTypes
        (TypeDependencyAdmission.observedSpace external (capture source.intrinsicRows)) subject =
      getAnnotatedTypes (TypeDependencyAdmission.observedSpace external source.intrinsicRows) subject := by
    calc
      _ = getAnnotatedTypes ⟨capture source.intrinsicRows⟩ subject := by
        simp only [TypeDependencyAdmission.observedSpace,
          TypeDependencyAdmission.observeList_resourceFree external _ (ready_safe source.intrinsicRows both.2)]
      _ = _ := (annotation_packet external source.intrinsicRows both.2 subject).symm
  cases subject <;> simp only [rawDeclarations, project, own, intrinsic]

theorem primitive_project (source : Source) (external : ExternalView)
    (accepted : ready source = true) (supply : Supply) (key : Primitive) :
    NativeTypeScopedReads.primitive (project source) external supply key =
      NativeTypeScopedReads.primitive source external supply key := by
  cases key with
  | annotations atom => simp only [NativeTypeScopedReads.primitive, raw_declarations_project source external accepted]
  | closure seeds =>
      simp only [NativeTypeScopedReads.primitive, project, subtype_complete_capture]
  | intrinsic atom =>
      cases atom with
      | expression _ | symbol _ | var _ => rfl
      | grounded value => cases value <;> rfl
  | kind _ | classify _ _ => rfl

theorem evaluate_project (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (accepted : ready source = true) (depth : Nat) :
    ∀ call supply,
    NativeTypeScopedReads.evaluate ops (project source) external depth call supply =
      NativeTypeScopedReads.evaluate ops source external depth call supply := by
  induction depth with
  | zero => intro call supply; rfl
  | succ depth ih =>
      intro call supply
      have services : (fun (current : Supply) (key : Question) => match key with
          | .inl key => NativeTypeScopedReads.primitive (project source) external current key
          | .inr child => NativeTypeScopedReads.evaluate ops (project source) external depth child current) =
          (fun (current : Supply) (key : Question) => match key with
          | .inl key => NativeTypeScopedReads.primitive source external current key
          | .inr child => NativeTypeScopedReads.evaluate ops source external depth child current) := by
        funext current key
        cases key with
        | inl primitive => exact primitive_project source external accepted current primitive
        | inr child => exact ih child current
      exact congrArg (fun service : Supply → Question → Option Reply × Supply =>
        let result := QueryState.run service (ReadOnlyQueryDemand.demand (body ops call)) supply
        let answer := NativeTypeRecursiveDriver.completed result.answer
        (answer, NativeTypeScopedReads.retain result.state answer)) services

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSourceProjection
