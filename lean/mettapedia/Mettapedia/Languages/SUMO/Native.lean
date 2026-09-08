import Mettapedia.Languages.SUMO.Native.NIKAuthority
import Mettapedia.Languages.SUMO.Native.DomainGuardElaboration
import Mettapedia.Languages.SUMO.Native.SignatureSemantics
import Mettapedia.Languages.SUMO.Native.SignatureInference
import Mettapedia.Languages.SUMO.Native.SourceTheory

/-!
# Native SUMO logical core

This umbrella exports intrinsically scoped SUO-KIF syntax, capture-avoiding
renaming and substitution, general unityped world semantics, a classical
natural-deduction calculus, its model-soundness theorem, and the executable
proof-producing checker.  Exact-spine bounded universals give row-domain
restrictions a native meaning without imposing a finite arity, while denoted
operator-domain judgments handle variable and computed operators directly.
The umbrella also exports the native proof-search GSLT and its two-way adequacy
theorem with the calculus, together with exact closed and contextual NIK
authority fibres.
Source-signature inference additionally derives declared argument-domain facts
from true ground relation applications under an explicit domain-respecting
model law, while retaining the original ontology context in its NIK claim.
-/
