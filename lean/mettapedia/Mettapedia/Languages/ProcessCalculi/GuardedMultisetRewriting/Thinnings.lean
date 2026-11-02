import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Thin
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Rename
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.CTerm
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Store
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Build
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Operations
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Patterns
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Matching
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Names
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedSteps
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Calculus

/-!
# The guarded rewriting calculus on thinnings: the core term layer

Terms are binding trees (`SignatureIndexedABT.Term`), stored as **co-de-Bruijn** DAGs: every
node records exactly which variables of its scope it uses, and every edge carries a **thinning**
(an order-preserving embedding, as a bit vector) placing the child's variables among the parent's.

* `Thinnings.Thin`: thinnings and their category laws; union (the coproduct of two subscopes),
  pullback, and the edge of the smart constructor.
* `Thinnings.Rename`: thinnings act on trees (a functor); shifts are thinnings; relevance; a trimmed
  thinning and a relevant tree are determined by the tree they give; opening an unused variable
  only erases it.
* `Thinnings.CTerm`: co-de-Bruijn terms, relevance, smart constructors, encoding and decoding, and
  the canonicity invariant (encoding and decoding are inverse bijections).
* `Thinnings.Store`, `Thinnings.Build`: a hash-consed store of thinned nodes; **pointer equality is
  tree equality**; one node per code, so a term and any renaming of it are one node and a closed
  subterm is one node wherever it occurs; making a node interns one node.
* `Thinnings.Operations`: weakening (any thinning, under any binders) touches no store; viewing
  allocates nothing; opening a binder with a shifted value, exiting at once where the variable is
  unused.
* `Thinnings.Patterns`, `Thinnings.Matching`: gather patterns and the tree matcher; matching on
  references (a pure read of the store) and instantiating in the store compute the tree answers.
* `Thinnings.Names`: alpha-equivalent named terms are one reference.
* `Thinnings.SharedSteps`: **running on thinned shared DAGs is running on trees**.
* `Thinnings.Calculus`: the calculus with this term layer: processes, LCF and Need cells on the
  store.
-/
