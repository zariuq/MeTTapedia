import Mettapedia.OSLF.Framework.PremiseAwareOccurrence
import Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace

/-!
# Executable occurrences of authored WM contextual steps

The typed WM event relation and the premise-aware OSLF engine have exactly
the same one-step support on encoded terms. The executable occurrence carries
its rule and local alternative indices at a chosen fuel; the typed event
carries its constructor position and root-rule identity. Existence is proved
both ways, but there is no asserted bijection between those evidence types.
The older no-premise `rewriteOccurrences` adapter misses a genuine nested
revision step, so it cannot be substituted for this premise-aware adapter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusExecutableOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace

/-- The authored contextual WM language, including exactly the congruence
rules used by the typed contextual-reduction adequacy theorem. -/
abbrev contextualWMLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong
    Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal

/-- Executable occurrences at a fixed contextual fuel and typed WM source. -/
def encodedOccurrences {s : WMSort} (fuel : Nat) (source : WMTerm s) :
    List RewriteOccurrence :=
  rewriteAtOccurrences (engineBasePremises RelationEnv.empty)
    contextualWMLanguage fuel (encodeWM source)

/-- Typed constructor-position events exist exactly when the premise-aware
engine admits some numbered occurrence at finite fuel. This does not recover
an engine occurrence's internal recursive-premise proof tree. -/
theorem contextEvent_executable_iff {s : WMSort}
    (source target : WMTerm s) :
    Nonempty (WMContextEvent source target) ↔
      ∃ fuel, ∃ occurrence ∈ encodedOccurrences fuel source,
        occurrence.target = encodeWM target := by
  rw [contextEvent_support_iff, wmContextStep_iff]
  rw [langSemanticReduces_iff_langReduces_of_equation_free
    minimalVertexWithCong_isEquationFree]
  exact (occurrence_support_iff_langReduces contextualWMLanguage
    (encodeWM source) (encodeWM target)).symm

private def nestedSource : WMTerm .state :=
  .revise (.state "a") (.revise (.state "b") (.state "c"))

private def nestedTarget : WMTerm .state :=
  .revise (.state "a") (.revise (.state "c") (.state "b"))

/-- The inner right-child revision commutes without changing the outer
revision's left child. -/
def nestedEvent : WMContextEvent nestedSource nestedTarget :=
  .revise_right (.state "a")
    (.root (.revision_comm (.state "b") (.state "c")))

/-- The premise-aware executable engine admits that nested event. -/
theorem nested_executable :
    ∃ fuel, ∃ occurrence ∈ encodedOccurrences fuel nestedSource,
      occurrence.target = encodeWM nestedTarget :=
  (contextEvent_executable_iff nestedSource nestedTarget).mp ⟨nestedEvent⟩

/-- The older no-premise top-level helper does not perform the inner
commutation at this source. -/
theorem nested_not_topLevel :
    encodeWM nestedTarget ∉
      rewriteStep contextualWMLanguage (encodeWM nestedSource) := by
  decide +kernel

/-- Consequently no occurrence in the old no-premise adapter witnesses the
genuine nested step, despite the premise-aware occurrence above. -/
theorem nested_not_oldOccurrence :
    ¬ ∃ occurrence ∈
      rewriteOccurrences contextualWMLanguage (encodeWM nestedSource),
        occurrence.target = encodeWM nestedTarget := by
  intro old
  exact nested_not_topLevel
    ((target_mem_rewriteStep_iff contextualWMLanguage
      (encodeWM nestedSource) (encodeWM nestedTarget)).2 old)

end Mettapedia.OSLF.Framework.WMCalculusExecutableOccurrence
