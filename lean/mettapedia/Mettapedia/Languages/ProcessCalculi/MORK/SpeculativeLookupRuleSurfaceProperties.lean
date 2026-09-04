import Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface

/-!
# Structural properties of speculative lookup compilation

Successful positional compilation appends both derived direct handlers to
the target inventory.  These laws expose that origin without reducing a
caller-specific finite presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem buildSelected?_direct_rules_mem
    (profile : Profile) (selection : Selection) (sourceRules : List Atom)
    (artifact : SelectedArtifact)
    (built : buildSelected? profile selection sourceRules = some artifact) :
    artifact.artifact.directProofRule ∈ artifact.artifact.targetRules ∧
      artifact.artifact.directOpaqueRule ∈ artifact.artifact.targetRules := by
  unfold buildSelected? at built
  obtain ⟨sourceTerminalRule, _terminalExact, built⟩ :=
    Option.bind_eq_some_iff.mp built
  obtain ⟨sourceProofRule, _proofExact, built⟩ :=
    Option.bind_eq_some_iff.mp built
  obtain ⟨sourceOpaqueRule, _opaqueExact, built⟩ :=
    Option.bind_eq_some_iff.mp built
  obtain ⟨directRules, _directExact, built⟩ :=
    Option.bind_eq_some_iff.mp built
  rcases directRules with
    ⟨directProofRule, directOpaqueRule, targetTerminalRule⟩
  obtain ⟨retainedRules, _retainedExact, built⟩ :=
    Option.bind_eq_some_iff.mp built
  cases built
  simp

theorem buildSelectedStrict?_direct_rules_mem
    (profile : Profile) (selection : Selection) (sourceRules : List Atom)
    (artifact : SelectedArtifact)
    (built : buildSelectedStrict? profile selection sourceRules =
      some artifact) :
    artifact.artifact.directProofRule ∈ artifact.artifact.targetRules ∧
      artifact.artifact.directOpaqueRule ∈ artifact.artifact.targetRules := by
  unfold buildSelectedStrict? at built
  split at built
  · obtain ⟨candidate, candidateBuilt, built⟩ :=
      Option.bind_eq_some_iff.mp built
    split at built
    · cases built
      exact buildSelected?_direct_rules_mem profile selection sourceRules
        artifact candidateBuilt
    · simp at built
  · simp at built

#print axioms buildSelected?_direct_rules_mem
#print axioms buildSelectedStrict?_direct_rules_mem

end Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface
