import Mettapedia.OSLF.Framework.RhoScopeOperationalFutures
import Mettapedia.OSLF.Syntax.RhoScopedNativeAbsenceControls

/-!
# Productive original scope atoms and their fresh-context grades

The two atomic premises are actual original communications. Their generated
scope has minimum depth zero, and its transported certificate retains two
ordered occurrences after fresh-variable extension. An empty original rule
profile supplies no atoms and cannot fabricate a generated scope certificate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopeOperationalFutureControls

open Mettapedia.OSLF.Binding _root_.CategoryTheory
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoScopedParallelEvents
open RhoScopedNativeAbsence RhoScopedNativeAbsenceControls RhoScopedParallelReactiveControls
open SyntacticRetractionContexts RhoScopeOperationalFutures
open RhoEquationGeneratedScope RhoGeneratedScopeStrata RhoGeneratedScopeMinimum
open RhoScopeMinimumReceipts RhoGeneratedScopeSubstitution

local instance enabledDecision (admitted : SourceRule → Prop) (context : Ctx sig) :
    DecidablePred (Enabled (context := context) admitted) := Classical.decPred _

def productiveName : Name [] := quote (join commRoot.source commRoot.source)

def productiveCertificate : Certificate (Enabled core) (Enabled core) productiveName :=
  .atoms commRoot.source commRoot.source supplied_communication_enabled supplied_communication_enabled

theorem productive_minimum_zero :
    minimumDepth? (Enabled core) (Enabled core) productiveName = some 0 :=
  (minimum_zero_iff_atomic_pair _ _ _).mpr
    ⟨commRoot.source, commRoot.source, supplied_communication_enabled,
      supplied_communication_enabled, rfl⟩

def freshName : world (S := sig) [Srt.nm] ⟶ world (S := sig) [] :=
  fresh (S := sig) [] Srt.nm (quoteRaw null)

def freshSubstitution : Sub sig [] [Srt.nm] := freshName.val

def futureCertificate : Certificate (Enabled core) (Enabled core)
    (bindQ freshSubstitution productiveName) :=
  transportRaw core core freshSubstitution productiveCertificate

theorem future_actual_scope_admitted :
    generated (Enabled core) (Enabled core) (bindQ freshSubstitution productiveName) :=
  certificate_sound futureCertificate

theorem productive_and_future_minimum_zero :
    minimumDepth? (Enabled core) (Enabled core) productiveName = some 0 ∧
    minimumDepth? (Enabled core) (Enabled core) (bindQ freshSubstitution productiveName) = some 0 := by
  refine ⟨productive_minimum_zero, (minimum_zero_iff_bounded _ _ _).mpr ?_⟩
  refine ⟨futureCertificate, ?_⟩
  exact Nat.le_of_eq (transportRaw_depth core core freshSubstitution productiveCertificate)

theorem supplied_two_occurrences_retained : futureCertificate.atomicOrigins =
    [.inl (bindQ freshSubstitution commRoot.source), .inr (bindQ freshSubstitution commRoot.source)] := by
  simp only [futureCertificate, transportRaw, productiveCertificate, transport,
    Certificate.atomicOrigins, raw_substitution]

theorem no_event_in_empty_profile {context : Ctx sig} (process : Process context) :
    ¬ Enabled (fun _ => False) process := by
  rintro ⟨result, step⟩
  obtain ⟨root, _surrounding, _source, _target⟩ := (step_iff_root_surrounding _ _).mp step
  exact root.1.property

theorem no_scope_from_unavailable_atoms {context : Ctx sig} (name : Name context) :
    ¬ generated (Enabled (fun _ => False)) (Enabled core) name :=
  no_left_atoms_excludes_scope (fun process member => no_event_in_empty_profile process member) name

end Mettapedia.OSLF.Framework.RhoScopeOperationalFutureControls
