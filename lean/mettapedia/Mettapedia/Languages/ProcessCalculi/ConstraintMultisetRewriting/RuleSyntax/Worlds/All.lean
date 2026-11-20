import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Local
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Bag
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Sharing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Confinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Algebra
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Product
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Events
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Pairs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Arrows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Embedding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Merging
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Interaction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Rows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Tree
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.TreeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Spatial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Freshness

/-!
# Knowledge located at worlds: candidate states and their laws

Candidate states of the step in which knowledge is located. The original single-firing construction
is recovered by the explicit local family `events X O E`. None replaces `RuleSyntax.State`.

## A bag of worlds and a space of closed rows

* `Local`: supplied local event families, with program monotonicity and refusal at inconsistent
  knowledge as separate properties; the original events satisfy both.
* `Bag`: the state, its moves (a supplied local event in one world; a copy; a publication of a row with
  its knowledge; a merge of two worlds), side by side and the one-world cases. Persistence uses
  program monotonicity; confinement of an inconsistent world uses refusal there.
* `Sharing`: what a closed row carries (the joint information of a shared premise), when it can be
  fired, that a row published from a dead world is fired by no one, and the order of a publication
  and a firing.
* `Confinement`: for the original events, confinement along runs: dead worlds and the rows they publish
  are no neighbours.
* `Algebra`: the merge distributes over side by side, through a copy.
* `Product`: without publication and merge, side by side is a product.
* `Events`, `Pairs`, `Arrows`: the same statements for the tree's comparison of systems that counts
  events, and as functional bisimulations: the one-world case, and two worlds as the interleaving
  product of their steps.
* `Embedding`: the states of worlds with one program (`Hosting.Alternatives.Worlds`) are bags.
* `Merging`: at the twin-binder frames, the composition of the calculus of systems is the merge; what
  side by side and the merge do to the two switching witnesses; the calculus of systems under the
  tensor has no uniform translation into the calculus of worlds side by side.
* `Controls`, `Interaction`: on first-order atoms, the two notions of a shared row, what a none query
  check reads, the joint information of a used premise, and where worlds interact.

## Located rows, and worlds as a tree

* `Rows`: a positive firing does not read the rows it does not select.
* `Tree`, `TreeControls`: worlds as a tree with knowledge and rows inherited downward; the candidate
  with a store at each location (`Hosting.Alternatives.Located`) is the tree of depth one; what is
  inherited and what is not.
* `Spatial`: the stores of a tree of worlds as a spatial constraint system.

## Freshness

* `Freshness`: what a state mentions decides an admission only through the freshness of the opening.
-/
