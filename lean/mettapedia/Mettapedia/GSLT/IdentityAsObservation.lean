import Mettapedia.TypeTheory.Calculi.BooleanSTLC.Syntax
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.Evaluation
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.ObservationalEquality
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.ProofRelevance
import Mettapedia.TypeTheory.Calculi.BooleanSTLC.WitnessIdentity
import Mettapedia.TypeTheory.OneToOneCorrespondence
import Mettapedia.GSLT.Logic.EliminatorObservers
import Mettapedia.GSLT.Logic.QuotientObservers

/-!
# Identity as observation

* `BooleanSTLC.Syntax`, `BooleanSTLC.Evaluation`: a simply typed calculus with
  booleans, propositions, products and functions; renaming, substitution, codes,
  and evaluation in the standard model.
* `BooleanSTLC.ObservationalEquality`: observational equality by recursion on
  type formers, with the pointwise and the logical function clause; the
  fundamental lemma, the coincidence of the two clauses, and the context lemma.
* `BooleanSTLC.ProofRelevance`: proof-relevant propositions; proofs in the
  observational fragment are irrelevant; propositional extensionality as
  equivalence of proof types holds exactly when proofs are unique; an inspectable
  disjunction breaks it.
* `BooleanSTLC.WitnessIdentity`: identifications as witnesses; the groupoid of
  witnesses at the types of the calculus lies in the h-set fragment, while the
  identity of types (equivalences of observational types) satisfies the groupoid
  laws without UIP and is a stage of a groupoid-valued presheaf, not of a plain
  one.
* `OneToOneCorrespondence`: one-to-one correspondences compared with
  equivalences.
* `Logic.EliminatorObservers`: the saturated relative equivalence of the
  eliminator observers is observational equality; the context lemma in the
  observer lattice; too few observers and code observers as controls; a
  step-counting presentation as a control; the stages of the observer presheaf.
* `Logic.QuotientObservers`: quotients as bubbles whose admissible observers
  respect the relation; proof irrelevance and propositional extensionality as
  quotients.
-/
