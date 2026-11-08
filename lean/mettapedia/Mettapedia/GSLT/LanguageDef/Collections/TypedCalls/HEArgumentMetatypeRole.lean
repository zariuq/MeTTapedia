import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeMatcher
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeDemand
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission

/-!
# The metatype cut belongs to argument admission, not global typing

The HE argument role tests the authored formal against the syntactic kind
before consulting inferred candidates. A successful kind cut keeps exactly
one unchanged caller frame and demands no inference of the held subject.
The native driver applies its current substitution first; their coincidence
below is established for the closed symbolic formals used by range.

An observer-level encoding into the historical query-based argument checker
requires an independently justified query/match. A cut is never itself a
`TypeOf` fact or evidence that the inferred service returned the formal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEArgumentMetatypeRole

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type
open Mettapedia.Machines.ReadOnlyQuery

abbrev KindCut := ArgumentKindCut

theorem native_cut {formal kind : Atom} (cut : KindCut formal kind) :
    TypeScopeMatcher.metaCheckAtom formal kind = some true := by
  cases cut <;> rfl

/-- One source-role step. The inferred arm reuses the existing ordered
argument checker and its actual caller-frame refinements. -/
abbrev Admission := KindArgumentAdmissionRel

theorem cut_keeps_exact_frame {space inferred policy expression subject formal position before frames errors kind}
    (kindOf : MetaTypeRel subject kind) (cut : KindCut formal kind)
    (admitted : Admission space inferred policy expression subject formal position before frames errors) :
    frames = [before] ∧ errors = [] := by
  cases admitted with
  | kind => exact ⟨rfl, rfl⟩
  | inferred noCut _ => exact (noCut kind kindOf cut).elim

theorem singleton_inferred {space inferred policy expression subject formal position before after actual}
    (noCut : ∀ kind, MetaTypeRel subject kind → ¬KindCut formal kind)
    (queried : inferred before.bindings subject formal [actual])
    (renewed : Frame.TypeRenewRel policy formal actual before after) :
    Admission space inferred policy expression subject formal position before [after] [] := by
  apply KindArgumentAdmissionRel.inferred noCut
  simpa [checkedFrames, checkedFailures] using
    ArgumentChecksRel.cons (expression := expression) (position := position) queried
      (List.Forall₂.cons (TypeCheckRel.accepted renewed) List.Forall₂.nil) ArgumentChecksRel.nil

/-- This is only equality of the accepted frame/error observation. The
query premise is independent evidence, never manufactured by the kind cut. -/
theorem historical_observer_encoding {space inferred policy expression subject formal position before kind actual}
    (kindOf : MetaTypeRel subject kind) (cut : KindCut formal kind)
    (queried : inferred before.bindings subject formal [actual])
    (matched : policy.matching.Rel formal actual before.bindings before.bindings) :
    Admission space inferred policy expression subject formal position before [before] [] ∧
      ArgumentChecksRel space inferred policy expression subject formal position [before] [before] [] := by
  refine ⟨.kind kindOf cut, ?_⟩
  simpa [checkedFrames, checkedFailures] using
    ArgumentChecksRel.cons (expression := expression) (position := position) queried
      (List.Forall₂.cons (TypeCheckRel.accepted (Frame.TypeRenewRel.unchanged matched)) List.Forall₂.nil) ArgumentChecksRel.nil

theorem symbolic_formal_keeps_its_meaning (policy : Policy) (frame : Frame)
    (state : TypeScopeMatcher.State) (name : String) :
    (frame.read policy (Entry.Value.ofAtom (.symbol name))).erase = .symbol name ∧
      substA state (.symbol name) = .symbol name := by
  simp [Frame.read, Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.erase, substA]

theorem native_closed_cut (external : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) (state : TypeScopeMatcher.State)
    {formal kind : Atom} (cut : KindCut formal kind) :
    (TypeScopeMatcher.ops external normalize subtypes).metaCheck
      ((TypeScopeMatcher.ops external normalize subtypes).apply state formal) kind = some true := by
  cases cut <;> rfl

/-- The existing native argument plan reads precisely the kind and then
returns the same state. No inferred/tuple view or body execution is demanded. -/
theorem single_cut_trace (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (store : NativeTypeDemand.Question Atom → NativeTypeDemand.ViewReply Atom Atom)
    (state : TypeScopeMatcher.State) (subject formal kind : Atom)
    (kindReply : store (.kind subject) = .kind kind)
    (cut : ops.metaCheck (ops.apply state formal) kind = some true) :
    run store (NativeTypeDemand.argsPlan ops [formal] [subject] state) =
      ⟨.ok (some state), [(.kind subject, .kind kind)]⟩ := by
  simp [NativeTypeDemand.argsPlan, run, kindReply, cut]

def onlyKinds : NativeTypeDemand.Question Atom → Option (NativeTypeDemand.ViewReply Atom Atom)
  | .kind subject => some (.kind (getMetaType subject))
  | _ => none

theorem partial_cut_trace (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (state : TypeScopeMatcher.State) (subject formal : Atom)
    (cut : ops.metaCheck (ops.apply state formal) (getMetaType subject) = some true) :
    run onlyKinds (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeDemand.argsPlan ops [formal] [subject] state)) =
      ⟨some (.ok (some state)), [(.kind subject, some (.kind (getMetaType subject)))]⟩ := by
  simp [NativeTypeDemand.argsPlan, Mettapedia.Machines.ReadOnlyQueryDemand.demand, run, onlyKinds, cut]

namespace Controls

def unsupported : Atom := .grounded (.custom "Unsupported" "opaque")

theorem held_unsupported_needs_no_inference (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom) (state : TypeScopeMatcher.State) :
    (run onlyKinds (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeDemand.argsPlan (TypeScopeMatcher.ops external normalize subtypes) [Atom.atomType] [unsupported] state))).answer =
        some (.ok (some state)) ∧ onlyKinds (.inferred unsupported) = none := by
  rw [partial_cut_trace _ _ _ _ (native_closed_cut external normalize subtypes state (.atom _))]
  exact ⟨rfl, rfl⟩

/-- Eager inference changes a successful held-argument admission into a
decline at the unavailable read. This is not an empty typing reply. -/
theorem eager_inference_refused (external : RetainedTypePayloads.ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom) (state : TypeScopeMatcher.State) :
    run onlyKinds (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeDemand.typesRead (.inferred unsupported) (fun _ =>
        NativeTypeDemand.argsPlan (TypeScopeMatcher.ops external normalize subtypes) [Atom.atomType] [unsupported] state))) =
      ⟨none, [(.inferred unsupported, none)]⟩ := by
  simp [NativeTypeDemand.typesRead, Mettapedia.Machines.ReadOnlyQueryDemand.demand, run, onlyKinds]

theorem actual_unsupported_reader_declines (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : NativeTypeSourcePorts.Source) (world : RetainedTypePayloads.ExternalView)
    (depth : Nat) (supply : TypeReadSupply.Supply) :
    NativeTypeScopedReads.evaluate ops source world depth (.infer true unsupported) supply = (none, supply) := by
  cases depth with
  | zero => rfl
  | succ depth =>
      simp [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, unsupported,
        NativeTypeCallGraph.typesRead, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
        Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive,
        NativeTypeScopedReads.retain, NativeTypeRecursiveDriver.completed]

theorem kind_cut_is_not_global_typing :
    KindCut Atom.atomType Atom.groundedType ∧
      ¬TypeOfRel Space.empty (.grounded (.int 7)) Atom.atomType := by
  refine ⟨.atom _, ?_⟩
  rintro ⟨types, queried, member⟩
  have intrinsic : StorageTypesRel Space.empty (.grounded (.int 7)) [.symbol "Number"] :=
    .groundedKnown (.int 7) (by decide)
  have same := queried.unique intrinsic
  rw [same] at member
  simp [Atom.atomType] at member

def assignedAtom : TypeScopeMatcher.State := fun name => if name = "t" then Atom.atomType else .var name

/-- The closed-formal law cannot be silently extended to arbitrary
schematic formals whose substituted value happens to be a metatype. -/
theorem substituted_formal_cut_is_a_distinct_policy :
    TypeScopeMatcher.metaCheckAtom (substA assignedAtom (.var "t")) Atom.groundedType = some true ∧
      ¬KindCut (.var "t") Atom.groundedType := by
  constructor
  · simp [substA, assignedAtom, TypeScopeMatcher.metaCheckAtom]
  · intro cut
    cases cut

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEArgumentMetatypeRole
