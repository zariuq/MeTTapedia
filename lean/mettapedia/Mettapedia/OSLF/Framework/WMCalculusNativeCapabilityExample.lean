import Mettapedia.OSLF.Framework.WMCalculusNativeCapability
import Mettapedia.OSLF.Framework.WMCalculusNativeContextExample

/-!
# A proper supported-query family

One lawful Boolean WM reading supports its query only in the true state.
The supported dependent answer graph has a real inhabitant, but the false
request has none and its Sigma-image is a proper native predicate. This
separates partial capability from silently answering unsupported requests.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusNativeContextExample

/-- A query is available exactly in the true Boolean state. -/
def truthCapability : WMCapability booleanReading where
  supports := fun state _ => state = true
  respectsAgree := by
    intro first second query agree
    have equal := agree ()
    change first = second at equal
    subst second
    exact Iff.rfl

private abbrev wmLanguage :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

private def stage : Opposite (ConstructorObj wmLanguage) :=
  Opposite.op (ConstructorObj.mk ⟨"State", by decide⟩)

/-- A supported request has exactly its extracted answer. -/
theorem supported_true_answer :
    ((true, ()), true) ∈ (supportedGraph truthCapability).obj stage := by
  exact ⟨rfl, rfl⟩

/-- An unsupported request cannot enter the answer graph even with a
candidate evidence value. -/
theorem unsupported_false_answer (value : Bool) :
    ((false, ()), value) ∉ (supportedGraph truthCapability).obj stage := by
  intro member
  cases member.1

/-- The supported-query Sigma-image is proper; total extraction remains a
separate fact about the underlying WM reading. -/
theorem truthSupport_not_top : supportPredicate truthCapability ≠ ⊤ :=
  supportPredicate_ne_top_of_unsupported truthCapability stage false ()
    (by simp [truthCapability])

end Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample
