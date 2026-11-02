import Mettapedia.Languages.HOLLight.CachedSourceProfileTransport
import Mettapedia.Languages.HOLLight.CachedSourceExpansionControls

/-!
# Source-profile composition and refusal controls

Two admitted definitions supply a source equation. The profile first unfolds
truth and then reverses the equation by retained symmetry. A second retained
symmetry composes through the same profile interface. Exact syntax checks
refuse missing definitions, insufficient depth and derived-connective aliases.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CachedSourceProfileTransportControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL CachedSourceDefinitionTable CachedSourceProfileTransport
open StandardTheoryInterpretation

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def bindings : List Binding := [⟨⟨.prop, Interpretation.Symbols.truth⟩, Raw.truth⟩]

def reversed : ClosedFormula Symbol :=
  .eq HOLLightBooleanDefinitions.conjunction (.const Interpretation.Symbols.conjunction)

def symmetry : Profile where
  source := CachedSourceExpansionControls.source
  unfolded := CachedSourceExpansionControls.target
  target := reversed
  native := reversed
  conversion := .eqSymm (.hyp ⟨0, by decide⟩)
  conversionFree := by simp only [ProofSyntax.FunctionExtensionalityFree]
  nativeImage := rfl

def twice : Profile := symmetry.post CachedSourceExpansionControls.target
  CachedSourceExpansionControls.target (.eqSymm (.hyp ⟨0, by decide⟩))
    (by simp only [ProofSyntax.FunctionExtensionalityFree]) rfl

theorem conversion_changes_source : symmetry.target ≠ symmetry.source := by
  intro same
  cases same

theorem symmetry_matching : (symmetry.matching? bindings 1).isSome = true := by decide +kernel
theorem twice_matching : (twice.matching? bindings 1).isSome = true := by decide +kernel
theorem missing_definition_refused : (symmetry.matching? [] 1).isNone = true := by decide +kernel
theorem insufficient_depth_refused : (symmetry.matching? bindings 0).isNone = true := by decide +kernel

theorem primitive_alias_refused :
    (sameReadable? (.bot : ClosedFormula Symbol) HOLLightBooleanDefinitions.falsity).isNone = true := by
  decide +kernel

theorem wrong_source_refused :
    (CachedSourceExpansion.read? CachedSourceExpansionControls.before 1 symmetry.target).isNone = true := by
  decide +kernel

theorem wrong_roots_refused :
    (symmetry.install? bindings 1 CachedSourceExpansionControls.before [0, 1] ("profile-symmetry", 0)).isNone = true := by
  decide +kernel

theorem original_reads :
    (CachedSourceExpansion.readAll? CachedSourceExpansionControls.before
      (symmetry.source :: theory bindings) [1, 0]).isSome = true := by decide +kernel

def sources : CachedSourceExpansion.Sources CachedSourceExpansionControls.before
    (symmetry.source :: theory bindings) :=
  (CachedSourceExpansion.readAll? CachedSourceExpansionControls.before
    (symmetry.source :: theory bindings) [1, 0]).get original_reads

theorem sources_read : CachedSourceExpansion.readAll? CachedSourceExpansionControls.before
    (symmetry.source :: theory bindings) [1, 0] = some sources :=
  (Option.some_get original_reads).symm

theorem dependencies_empty : CachedHypothesisList.dependencies (sources.entries.map Prod.snd) = ∅ := by
  decide +kernel

theorem checked_symmetry : ∃ after root fact,
    symmetry.install? bindings 1 CachedSourceExpansionControls.before [1, 0]
      ("profile-symmetry", 0) = some (after, root) ∧
    GraphExpansion.BuildChecked emptyAxiomPolicy CachedSourceExpansionControls.received.cache.toList after ∧
    after.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ ∧
    fact.sequent.concl = CachedSourceExpansion.encode reversed ∧ fact.axioms = ∅ := by
  let matched := (symmetry.matching? bindings 1).get symmetry_matching
  have matchRead : symmetry.matching? bindings 1 = some matched := (Option.some_get symmetry_matching).symm
  obtain ⟨after, root, fact, installed, checked, found, closed, conclusion, axioms, _⟩ :=
    symmetry.install_checked bindings 1 matched.down matchRead [1, 0] sources sources_read
      CachedSourceExpansionControls.before_checked ("profile-symmetry", 0)
  exact ⟨after, root, fact, installed, checked, found, closed, conclusion,
    axioms.trans dependencies_empty⟩

theorem checked_composition : ∃ after root fact,
    twice.install? bindings 1 CachedSourceExpansionControls.before [1, 0]
      ("profile-double-symmetry", 0) = some (after, root) ∧
    GraphExpansion.BuildChecked emptyAxiomPolicy CachedSourceExpansionControls.received.cache.toList after ∧
    after.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ ∧
    fact.sequent.concl = CachedSourceExpansion.encode CachedSourceExpansionControls.target ∧ fact.axioms = ∅ := by
  let matched := (twice.matching? bindings 1).get twice_matching
  have matchRead : twice.matching? bindings 1 = some matched := (Option.some_get twice_matching).symm
  obtain ⟨after, root, fact, installed, checked, found, closed, conclusion, axioms, _⟩ :=
    twice.install_checked bindings 1 matched.down matchRead [1, 0] sources sources_read
      CachedSourceExpansionControls.before_checked ("profile-double-symmetry", 0)
  exact ⟨after, root, fact, installed, checked, found, closed, conclusion,
    axioms.trans dependencies_empty⟩

#print axioms conversion_changes_source
#print axioms primitive_alias_refused
#print axioms wrong_roots_refused
#print axioms checked_symmetry
#print axioms checked_composition

end Mettapedia.Languages.HOLLight.CachedSourceProfileTransportControls
