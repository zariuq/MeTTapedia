import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
import Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurfaceProperties

/-!
# Structural origin laws for compiled compressed presentations

The two derived direct handlers in every successful presentation transform
are members of the emitted rule inventory because they are produced by the
strict positional compiler selected by that transform.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface

theorem transformCompressedVerifierPresentation?_direct_rules_mem
    {sourceRules sourceStaticRows : List Atom}
    {output : CompiledPresentation}
    (built : transformCompressedVerifierPresentation?
      sourceRules sourceStaticRows = some output) :
    output.selected.artifact.directProofRule ∈ output.targetRules ∧
      output.selected.artifact.directOpaqueRule ∈ output.targetRules := by
  rw [transformCompressedVerifierPresentation?] at built
  obtain ⟨selected, selectedBuilt, built⟩ :=
    Option.bind_eq_some_iff.mp built
  dsimp only at built
  split at built
  · simp at built
  · split at built
    · simp at built
    · split at built
      · simp at built
      · obtain ⟨retainedRows, _rowsBuilt, built⟩ :=
          Option.bind_eq_some_iff.mp built
        cases built
        exact buildSelectedStrict?_direct_rules_mem
          compressedSpeculativeLookupProfile
          compressedSpeculativeLookupSelection sourceRules selected
          selectedBuilt

#print axioms transformCompressedVerifierPresentation?_direct_rules_mem

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
