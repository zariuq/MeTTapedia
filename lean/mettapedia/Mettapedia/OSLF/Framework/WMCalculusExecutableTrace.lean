import Mettapedia.OSLF.Framework.WMCalculusExecutableOccurrence

/-!
# Finite executable occurrence traces for the WM calculus

Each event retains the fuel, authored rule index, rule name, and local
alternative index returned by the premise-aware interpreter. A trace also
retains intermediate typed terms. Erasure is exact on support against both
the typed WM contextual relation and the authored LanguageDef relation, but
is not an isomorphism of proof-relevant execution records.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusExecutableTrace

open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace
open Mettapedia.OSLF.Framework.WMCalculusExecutableOccurrence
open Mettapedia.OSLF.Framework.LangMorphism

/-- A numbered result of the actual premise-aware interpreter, indexed by
typed WM endpoints. -/
structure ExecutableWMEvent {s : WMSort} (source target : WMTerm s) where
  fuel : Nat
  occurrence : RewriteOccurrence
  admitted : occurrence ∈ encodedOccurrences fuel source
  endpoint : occurrence.target =
    Mettapedia.OSLF.Framework.WMCalculusEncoding.encodeWM target

/-- Executable and typed constructor-position events have the same support.
The theorem does not choose a canonical correspondence of their identities. -/
theorem executableEvent_support_iff {s : WMSort}
    (source target : WMTerm s) :
    Nonempty (ExecutableWMEvent source target) ↔
      Nonempty (WMContextEvent source target) := by
  constructor
  · rintro ⟨event⟩
    exact (contextEvent_executable_iff source target).mpr
      ⟨event.fuel, event.occurrence, event.admitted, event.endpoint⟩
  · rintro ⟨event⟩
    obtain ⟨fuel, occurrence, admitted, endpoint⟩ :=
      (contextEvent_executable_iff source target).mp ⟨event⟩
    exact ⟨⟨fuel, occurrence, admitted, endpoint⟩⟩

/-- Forget executable metadata to the existing contextual step proposition. -/
theorem ExecutableWMEvent.erase {s : WMSort} {source target : WMTerm s}
    (event : ExecutableWMEvent source target) : WMContextStep source target :=
  contextEvent_support_iff.mp
    ((executableEvent_support_iff source target).mp ⟨event⟩)

/-- A finite sequence of actual engine occurrences; unlike a proposition of
reachability, it retains each numbered event and its intermediate endpoints. -/
inductive ExecutableWMTrace : {s : WMSort} → WMTerm s → WMTerm s → Type where
  | refl {s : WMSort} {term : WMTerm s} : ExecutableWMTrace term term
  | tail {s : WMSort} {source middle target : WMTerm s} :
      ExecutableWMTrace source middle → ExecutableWMEvent middle target →
        ExecutableWMTrace source target

/-- Number of engine occurrences in the execution record. -/
def ExecutableWMTrace.length {s : WMSort} {source target : WMTerm s} :
    ExecutableWMTrace source target → Nat
  | .refl => 0
  | .tail earlier _ => earlier.length + 1

/-- Forget the machine occurrence record but keep contextual reachability. -/
theorem ExecutableWMTrace.erase {s : WMSort} {source target : WMTerm s} :
    ExecutableWMTrace source target → WMContextStepStar source target
  | .refl => .refl
  | .tail earlier event => .tail earlier.erase event.erase

/-- Engine occurrence traces exist exactly for typed WM contextual
reachability. The reverse implication is a support claim, not an executable
choice of one event record from a proposition. -/
theorem executableTrace_support_iff {s : WMSort}
    (source target : WMTerm s) :
    Nonempty (ExecutableWMTrace source target) ↔
      WMContextStepStar source target := by
  constructor
  · rintro ⟨trace⟩
    exact trace.erase
  · intro steps
    induction steps with
    | refl => exact ⟨.refl⟩
    | tail _ last earlier =>
        obtain ⟨trace⟩ := earlier
        obtain ⟨event⟩ :=
          (executableEvent_support_iff _ _).mpr
            (contextEvent_support_iff.mpr last)
        exact ⟨.tail trace event⟩

/-- The numbered executable traces and the constructor-position traces
admit exactly the same endpoints, although their evidence types are not
identified. -/
theorem executableTrace_typedTrace_support_iff {s : WMSort}
    (source target : WMTerm s) :
    Nonempty (ExecutableWMTrace source target) ↔
      Nonempty (WMTrace source target) :=
  (executableTrace_support_iff source target).trans
    (trace_support_iff).symm

/-- Engine occurrence traces have exactly the support of the authored
contextual WM LanguageDef on encoded typed endpoints. -/
theorem executableTrace_authored_iff {s : WMSort}
    (source target : WMTerm s) :
    Nonempty (ExecutableWMTrace source target) ↔
      LangReducesStar
        (Mettapedia.OSLF.Framework.WMCalculusContextClosure.wmExtVertexLanguageDefWithCong
          Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal)
        (Mettapedia.OSLF.Framework.WMCalculusEncoding.encodeWM source)
        (Mettapedia.OSLF.Framework.WMCalculusEncoding.encodeWM target) :=
  (executableTrace_support_iff source target).trans
    (wmContextStepStar_iff source target)

end Mettapedia.OSLF.Framework.WMCalculusExecutableTrace
