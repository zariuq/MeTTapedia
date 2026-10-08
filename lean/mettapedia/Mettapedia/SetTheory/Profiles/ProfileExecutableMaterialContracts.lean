import Mettapedia.SetTheory.Profiles.ProfileMaterialContracts
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFiniteBoolean
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFiniteMatching
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFoundationPresentations
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutObservedPresentations
import Mettapedia.SetTheory.Profiles.ProfileFiniteScottCollapse
import Mettapedia.SetTheory.Profiles.ProfileFiniteScottCoherence
import Mettapedia.SetTheory.Profiles.ProfileFiniteScottEvaluation
import Mettapedia.SetTheory.Profiles.ProfileNativeProofSerialization

/-!
# Material derivations and qualified finite observations

The source calculus has profile-indexed adopted declarations and retained
proofs. Its compilation retains object-variable indices, hypothesis
occurrences, conclusions and declaration authority. Typed recovery is exact
for the retained HOL target proof tree, rather than an inverse to the
first-order compiler. An encoded proof is interpreted only in the context
under which it was checked.

Finite presentations retain their authored successor rows. The Aczel
readout identifies roots exactly at bisimilarity and preserves membership.
The raw-unfolding readout instead identifies isomorphic rooted path trees.
The canonical finite Scott readout repeatedly quotients the raw-unfolding
classes, removes repeated quotient edges and compares the resulting graph
again. Its final graph, projection, identity kernel and member image are
constructed. Closed successor-fibre embeddings give coherent comparisons
with independently canonical roots, invariant under disjoint padding.
Checked stable stages evaluate that same observer, including the first
authored member representatives, without normalizing unchanged quotient tails.
Transport to another material carrier requires a canonical
decoration of that final graph; an arbitrary decoration is insufficient.

The Foundation readout is restricted to accessible roots. It preserves
material equality and membership on that domain and refuses cyclic roots;
it does not totalize the operation by discarding non-well-founded members.
The observed readout also retains declared results or faults, scope and
origins. A material quotient does not identify authored receipts: a
dependent consumer needs the proved family and term descent contracts.

The generic solver and proof recovery theorems are kernel statements.
Native parser, compiler, resource reporting and execution agreement are
separately qualified implementation boundaries. Finite execution does not
establish a complete set-theory universe or select a native foundation.
-/
