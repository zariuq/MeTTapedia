import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularNormalization
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularSubjectReduction
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularBidirectional
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularBidirectionalCompleteness
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularPatternElaboration
import Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature
import Mettapedia.Languages.MeTTa.Prime.InternalDataTransport
import Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax
import Mettapedia.Languages.MeTTa.Prime.InternalAdmission
import Mettapedia.Languages.MeTTa.Prime.SelfInstance

/-!
# Prime regular-kernel build boundary

This module declares nothing.  It is a focused build boundary that collects
the exact regular normalizer and bidirectional checker (the `IntrinsicPure`
`Regular*` development), strict Pattern elaboration, internal
language-operation transport, revision-scoped admission, and the level-raised
Prime self-instance, so that they can be elaborated together.

It is not the MeTTa Native type theory: that is
`Languages/MeTTa/TypeTheory/StagedReflective/Presentation.lean`.  The regular checker
collected here is the intrinsic Pure fragment (a pure type system with sorts
`u0 : u1`, Π, Σ, and Id), which embeds into the native presentation exactly
on its image and is implemented by the CeTTa Prime regular kernel.

Quantitative scheduling, evidence weights, and cost semantics are deliberately
outside this boundary.
-/
