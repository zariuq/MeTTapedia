import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.OSLFBridge_handcrafted

/-!
# Agreement: Handcrafted Bridge = DSL-Authored Semantic Kernel

Proves that the handcrafted rewrite rules in `OSLFBridge_handcrafted.lean`
(manual record constructors) are identical to the DSL-authored rules in
`SemanticKernelDSL.lean` (via `languageDef!` macro), as re-exported through
`OSLFBridge.lean`.

This file exists separately because importing both bridges in one file
requires the `languageDef!` macro syntax from the DSL import chain, which
clashes with some of the handcrafted bridge's syntax patterns. By proving
agreement here, we avoid modifying the handcrafted bridge while still
verifying semantic identity.
-/

namespace Mettapedia.Languages.GF.GFKernelAgreement

/-- Handcrafted UseN elimination = DSL-authored UseN elimination. -/
theorem useNElim_agreement :
    OSLFBridge.useNElimRewrite = GFCoreOSLFBridge.useNElimRewrite := rfl

/-- Handcrafted PositA elimination = DSL-authored PositA elimination. -/
theorem positAElim_agreement :
    OSLFBridge.positAElimRewrite = GFCoreOSLFBridge.positAElimRewrite := rfl

/-- Handcrafted UseN identity equation = DSL-authored UseN identity equation. -/
theorem useNIdentity_agreement :
    OSLFBridge.useNIdentityEquation = GFCoreOSLFBridge.useNIdentityEquation := rfl

/-- Handcrafted active-passive rewrite = DSL-authored active-passive rewrite. -/
theorem activePassive_agreement :
    OSLFBridge.activePassiveRewrite = GFCoreOSLFBridge.activePassiveRewrite := rfl

/-- Handcrafted present tense rewrite = DSL-authored present tense rewrite. -/
theorem presentTense_agreement :
    OSLFBridge.presentTenseRewrite = GFCoreOSLFBridge.presentTenseRewrite := rfl

/-- Handcrafted past tense rewrite = DSL-authored past tense rewrite. -/
theorem pastTense_agreement :
    OSLFBridge.pastTenseRewrite = GFCoreOSLFBridge.pastTenseRewrite := rfl

/-- Handcrafted future tense rewrite = DSL-authored future tense rewrite. -/
theorem futureTense_agreement :
    OSLFBridge.futureTenseRewrite = GFCoreOSLFBridge.futureTenseRewrite := rfl

end Mettapedia.Languages.GF.GFKernelAgreement
