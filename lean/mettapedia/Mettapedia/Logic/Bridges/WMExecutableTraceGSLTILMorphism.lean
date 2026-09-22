import Mettapedia.Logic.Bridges.WMExecutableTraceGSLTIL
import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism

/-!
# Backend maps preserve the same executable WM history

A capability-preserving world-model interpretation changes the semantic
request and answer but keeps the authored syntax and every indexed machine
occurrence fixed. Erasing the trace commutes with backend transport. This is
forward only: a target backend may support additional requests.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMExecutableTraceGSLTILMorphism

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory
open Mettapedia.Logic.Bridges.WMNativeCapabilityComputation
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism
open Mettapedia.Logic.Bridges.WMNativeExecutionTraceGSLTIL
open Mettapedia.Logic.Bridges.WMExecutableTraceGSLTIL

variable {source target : LawfulCapability} (hom : source ⟶ target)

/-- Transport a checked answer through a capability backend arrow while
retaining the exact finite machine trace and reduced term request. -/
def mapExecutableEvidence
    (terms : TermRequest) (answer : source.model.Evidence) :
    (executableCapabilityChain source.capability).evidence terms answer →
      (executableCapabilityChain target.capability).evidence terms
        (hom.readingMap.mapEvidence answer)
  | ⟨reduced, trace, receipt⟩ =>
      ⟨reduced, trace,
        mapTermCapabilityEvidence hom reduced answer receipt⟩

/-- Backend interpretation preserves existence of every exact checked
answer route, with its evidence value mapped through the reading morphism. -/
theorem executable_support_forward
    (terms : TermRequest) (answer : source.model.Evidence) :
    Nonempty ((executableCapabilityChain source.capability).evidence
      terms answer) →
      Nonempty ((executableCapabilityChain target.capability).evidence
        terms (hom.readingMap.mapEvidence answer)) := by
  rintro ⟨witness⟩
  exact ⟨mapExecutableEvidence hom terms answer witness⟩

/-- Trace erasure and backend transport form a commuting square. The
extensional receipt fibre is subsingleton, whereas the full trace fibre is
not: this does not identify distinct executions. -/
theorem forgetExecutable_map
    (terms : TermRequest) (answer : source.model.Evidence)
    (witness : (executableCapabilityChain source.capability).evidence
      terms answer) :
    forgetExecutable target.model.laws target.capability terms
        (hom.readingMap.mapEvidence answer)
        (mapExecutableEvidence hom terms answer witness) =
      mapTermCapabilityEvidence hom terms answer
        (forgetExecutable source.model.laws source.capability
          terms answer witness) := by
  exact (chainEvidence_subsingleton target.capability terms
    (hom.readingMap.mapEvidence answer)).allEq _ _

end Mettapedia.Logic.Bridges.WMExecutableTraceGSLTILMorphism
