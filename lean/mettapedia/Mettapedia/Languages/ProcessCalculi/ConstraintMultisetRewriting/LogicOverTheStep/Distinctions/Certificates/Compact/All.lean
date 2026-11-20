import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Lumping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Quotient
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Work
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Abstraction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.StepClasses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.UpTo
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Scaling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Supported
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.SupportedControls

/-!
# Compact certificates: certify on classes

A prefixpoint certificate of a chain has a kernel on all pairs of states and checks a coupling for
every action and pair, so its checker does on the order of `|A| · n⁴` products whatever the chain's
structure. When many states lump into few classes, the same bound is certified on the classes.

* **The law** (`Lumping`): coupling bounds compose by gluing, and a lumping is a coupling bound of
  cost zero on its graph; so a coupling bound of the quotient pulls back to one of the chain
  (`couplingBound_pullback`, `couplingBound_lift`, every discount `0 ≤ c`), and the metric is invariant
  under lumping (`bisimulationMetric_lump`, `0 < c ≤ 1`).
* **The certificate and its checker** (`Quotient`): a class map, a chain on the classes, and a
  prefixpoint certificate of it; the checker checks the lumping with sums and equalities only, then
  runs the prefixpoint checker on the quotient (`classCheck`, `classCheck_sound`). With the quotient's
  dual certificate the distance is exact (`classCheck_exact_of_dual`); on a closed region of the
  transform step it bounds the region's behavioural metric (`classCheck_sound_region`).
* **Counted work and size** (`Work`): the lumping check costs no product (`lumpWork_eq`); every
  accepted prefixpoint certificate costs at least `|A| · n(n-1)(n²+1)` products
  (`prefixpointWork_lower`).
* **For every chain** (`Scaling`): checking any certificate on `k` classes costs at most a bound
  quadratic in `n` (`classWork_all_le`); when four times it is below the incumbent's quartic lower
  bound, the class certificate is four times cheaper (`four_times_cheaper_of_large`); with one action,
  one observation and four classes, from nine states on (`four_classes_from_nine`).
* **The family** (`Family`): `m + 1` copies of the leak chain's four states. For every `m` the classes
  lump onto the leak chain and the metric is exact at the classes; every incumbent certificate proving
  as much lists at least `(m + 1)(2m + 1)` couplings (attained at `m = 1`); for every `m ≥ 1` the
  certificate on classes is at least four times smaller and its checker at least four times cheaper
  (`four_times_smaller`, `four_times_cheaper`); at `m = 0` it loses (`loses_without_classes`).
* **Controls** (`Controls`): average lumping and support lumping each accept a false bound; the
  checker refuses both. A perturbed copy breaks the lumping and is apart from its sibling, so exact
  classes gain nothing there.
* **Through a quotient with an error** (`Abstraction`): a coupling bound between the chain and a small
  chain, error on the graph of the map and one elsewhere, composed with the small chain's certificate
  by the tree's sequential composition, bounds the distance by `e s + D (view s) (view t) + e t` at
  every discount `0 ≤ c` (`abstractionCheck_sound`). A lumping is the case of error zero. On the
  perturbed chain it brackets the two leaky copies between `3/20` and `87/319` and its checker is at
  least four times cheaper than every accepted prefixpoint certificate's
  (`perturbed_four_times_cheaper`).
* **On the transform step** (`StepClasses`): under the step controls' policy, the states with clocks
  `0, …, N + 1` form a closed region that lumps onto five classes. The certificate on classes is
  accepted at `N = 1, 2, 3`; on the step's own system, refusing states with the same reading are
  Larsen–Skou bisimilar (`late_bisimilar_three`); at `N = 3` its checker is at least four times
  cheaper than every accepted prefixpoint certificate's (`step_four_times_cheaper`).
* **Closures** (`UpTo`): meets, the symmetric minimum, the triangle (infimal convolution) and pullback
  along a lumping keep coupling bounds; convex combination does not (`average_not_couplingBound`), though
  the average's claims are true (`average_claims_true`).
* **Read on supports** (`Supported`, `SupportedControls`): the incumbent's certificate with, for every
  action and state, a set containing the successors of positive mass; tables are read and costs computed
  on products of supports only (`supportedCheck_sound`, every `0 ≤ c`). Without any classes: on the leak
  chain itself `281` counted operations against `799`; on the blown-up chain at `8` and `12` states at
  most a quarter of every accepted prefixpoint certificate's products and additions; for every chain with
  supports of at most two states, from ten states on (`two_successors_from_ten`).
-/
