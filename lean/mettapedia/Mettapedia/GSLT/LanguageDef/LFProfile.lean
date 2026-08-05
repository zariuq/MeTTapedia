import Mettapedia.GSLT.LanguageDef.LF.Profiles
import Mettapedia.GSLT.LanguageDef.LF.DTTBenchDemand
import Mettapedia.GSLT.LanguageDef.LF.Canonical
import Mettapedia.GSLT.LanguageDef.LF.ProfileChecker
import Mettapedia.GSLT.LanguageDef.LF.BetaEtaConversion
import Mettapedia.GSLT.LanguageDef.LF.ConversionProfileChecker
import Mettapedia.GSLT.LanguageDef.LF.RootedBetaEtaConversion
import Mettapedia.GSLT.LanguageDef.LF.RootedBetaEtaCorrespondence
import Mettapedia.GSLT.LanguageDef.LF.ContextualBetaEtaClosure
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderContextualConversion
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderContextualCorrespondence
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderOperationalCorrespondence
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderCertifiedNormalization
import Mettapedia.GSLT.LanguageDef.LF.RootedBetaEtaAdequacyBoundary
import Mettapedia.GSLT.LanguageDef.LF.PureCorrespondence
import Mettapedia.GSLT.LanguageDef.LF.DTTBenchConversionReplay
import Mettapedia.GSLT.LanguageDef.LF.DTTBenchProofCarryingConversionReplay

/-!
# Profile-parametric LF theory

This umbrella exposes the source-extracted basic/indexed PTS lattice, the
frozen DTTBench statement-demand theorem, eta-long canonical forms with
hereditary substitution, and the profile-parametric reference checker.

The profile checker is paired with a rooted beta-eta reduction declaration.
Conversion-dependent source terms must still pass both profile typing and the
generic common-reduct certificate checker.  The runtime LF carrier is connected
to that root by proved lift, substitution, freshness, and scope
correspondences.  The universe-free Pure trace carrier is connected to LF by a
total embedding that commutes with beta-eta normalization and conversion.  A
hash-bound calibration fixture rechecks all 31 frozen DTTBench candidates with
the generic indexed conversion checker.  The original rooted proof
presentation has an explicit adequacy boundary: direct beta and eta are
proof-carrying, but its binder-wrapped congruence premise cannot certify
non-reflexive reduction under a product.  An independent contextual-closure
theorem identifies the complete semantic certificate language as finite paths
of root beta/delta/eta steps under explicit one-hole contexts.  For the
empty-signature profile, a validated first-order presentation now serializes
explicit contexts, lifting, substitution, unused-variable elimination, and
beta-eta steps into the source-neutral checker; it accepts a beta step beneath
a product body and rejects captured eta and a fabricated endpoint.  Runtime
natural numbers, Unicode names, terms, and one-hole contexts have total
injective encodings into that presentation, and a recursively generated
context-fill certificate is accepted for every runtime context and inserted
term.  Proof-producing compilers for natural-number order and addition,
de Bruijn lifting, capture-avoiding substitution, successful unbinding, and
arbitrarily contextual beta and eta contractions are accepted universally by
the same generic checker.  Captured eta, changed lift targets, and changed
beta targets are rejected.  Finite chronological certificates compose through
an explicitly checked transitivity rule, while a reversed chain is rejected
before proof emission.  The derived MeTTa source is admitted by the
source-indexed generic checker, and the live conversion bridge reconstructs
both conversion goals from the raw and normalized `KWCheck` terms before the
normalized candidate reaches the indexed LF kernel.  Closed contextual beta,
closed eta, and a two-step beta path pass that boundary; changed intermediate,
reversed, missing-child, unknown-rule, captured-eta, malformed, and external
proof-byte mutations fail.  Producing proof paths for the full raw dependent
corpus is now uniform rather than hand-authored: a leftmost beta/eta producer
emits accepted one-step certificates, proves every bounded path chronological,
rejects fuel exhaustion as completion, and supports both independent
term/type normalization and common-normal-form conversion.  All 31 known raw
DTTBench term/type pairs produce completed proof paths at fuel 512.  Separate
negative fixtures establish that normalization does not imply typing, while
malformed and binder-captured candidates remain rejected by the indexed
checker.  Live serialization of the full calibration corpus and validation on
an independent unopened family remain open.
-/
