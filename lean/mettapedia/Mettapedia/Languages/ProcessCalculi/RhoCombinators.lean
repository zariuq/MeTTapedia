import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Admissibility
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Basic
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Blowup
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.CollapsedConstructor
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Compositionality
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.CongruenceScope
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.CostNotSaturated
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Encoding
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.EncodingLinearity
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.EnvironmentSimulation
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.FanOut
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.FreshReads
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Gate
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Inertness
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.MetavariableRouting
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.MeTTaFragment
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.MinimalLabel
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NameGrowth
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NormalForm
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.ObservationBoundary
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Occupancy
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.OccurrenceClassification
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.OccurrenceDispatch
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.ReactiveSystem
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RedexDecomposition
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RuleSkeleton
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Seeds
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Separation
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.SkeletonExtraction
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.SoupInstance
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.SourceCongruence
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.SourceSemantics
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Sufficiency
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Termination
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Translation
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.TranslationScope

/-!
# Process Calculi: the rho combinators

Language-focused facade for the name-free combinator calculus, so the lane is a
single build target rather than a set of modules reachable only by name.

## Summary

A concurrent calculus with no binders: every name is a quotation, the source
calculus's input prefix is replaced by routing atoms, and the operations that
build a name are atoms too.  The interest is that a calculus without binders
still has to say what its names are, and the answer constrains which
sub-calculi are closed under their own reduction.

## What is here

- `Basic.lean` — the thirteen atom shapes, structural congruence, reduction,
  and the two name lemmas: no constructor-free step invents a name, and a
  constructor step provably does.
- `NormalForm.lean` — the multiset of top-level components is a complete
  invariant of structural congruence, so congruence questions become multiset
  questions.
- `Occupancy.lean` — a sub-calculus is a set of admitted shapes; occupancy is
  decidable in one traversal, and is preserved by reduction exactly when the
  admitted set is closed under what its own rules build.
- `Termination.lean` — without the opener, reduction length is bounded by a
  weight on the top-level atoms.  The unweighted count of non-message atoms
  does not bound it, and the three rules that defeat it are exhibited.
- `Translation.lean`, `Encoding.lean`, `FanOut.lean`, `FreshReads.lean` — the
  compiler from the source calculus, and the routing it needs.
- `Blowup.lean`, `NameGrowth.lean` — how large a name gets.
- `ReactiveSystem.lean`, `MinimalLabel.lean`, `RedexDecomposition.lean` — the
  labelled transitions, and the fact that a least label exists and is
  determined.
- `Separation.lean`, `Sufficiency.lean`, `Admissibility.lean` — what the
  calculus can and cannot do, and which presentations admit a name-free target.
-/
