import Mettapedia.Logic.Propositions.LogicalForm
import Mettapedia.Logic.Propositions.TwoDimensional
import Mettapedia.Logic.Propositions.Views
import Mettapedia.Logic.Propositions.Comparison
import Mettapedia.Logic.Propositions.Scrutability
import Mettapedia.Logic.Propositions.ScenarioSpaces
import Mettapedia.Logic.Propositions.Totality
import Mettapedia.Logic.Propositions.InformationStates
import Mettapedia.Logic.Propositions.EvidenceStates
import Mettapedia.Logic.Propositions.ObserverViews
import Mettapedia.Logic.Propositions.Verification
import Mettapedia.Logic.Propositions.Examples.MorningStar
import Mettapedia.Logic.Propositions.Examples.Julius

/-!
# What a sentence expresses: views of propositions

The four views of propositions surveyed by Chalmers (*Constructing the World*,
2012, ch. 2 §2), the enriched propositions of his own account, the maps between
them, and what each view does to the thesis that all truths are scrutable from
a base.

* `LogicalForm`: the shape shared by sentences and structured propositions,
  with the leaf type a parameter; replacing leaves and reading a form.
* `TwoDimensional`: interpretations over scenarios and worlds; the primary and
  the secondary intension; being a priori and being necessary.
* `Views`: Fregean, Russellian and enriched propositions, the proposition a
  sentence expresses on each, and the commuting diagram from sentences through
  enriched propositions to the two intensions.
* `Comparison`: which features of sentences factor through which view, by the
  factorization criterion of `Mettapedia.GSLT.Core.NonFactorization` and the
  two liftings of `Mettapedia.GSLT.Scope.PredicateDescent`; the order of the views (the enriched view is the meet of the
  Fregean and the Russellian one); being a priori lives on the Fregean leg and
  being necessary on the Russellian leg; the outcomes Chalmers reports for each
  view.
* `Scrutability`: a priori scrutability as semantic consequence over scenarios;
  its agreement with propositional scrutability on the Fregean view and under
  guises; scrutability bases as descriptions that pin the actual scenario down.
* `ScenarioSpaces`: what is a priori and how finely senses are individuated
  depend monotonically on which scenarios are open.
* `Totality`: what a base of positive truths settles without a that's-all
  truth (what holds in every extension of the actual scenario), and the
  that's-all truth as the condition under which it settles everything.
* `InformationStates`: sets of open scenarios as a world model; scrutability
  is what the state of the base settles.
* `EvidenceStates`: bags of observed scenarios as a PLN world model; evidence
  is a function of the sense of a sentence, and a state settles a sentence
  exactly when there is no evidence against it.
* `ObserverViews`: sameness of sense as the equality of the bubble of
  sense-respecting observers.
* `Verification`: a second axis, how much of a proposition's verification is
  kept: the code (data), the type of proofs, the truth value; each strictly
  coarser than the one before.
* `Examples.MorningStar`: Frege's puzzle; a necessary a posteriori truth; the
  negative control for the Russellian and the possible-worlds leg.
* `Examples.Julius`: Evans's contingent a priori; the negative control for the
  Fregean leg.
-/
