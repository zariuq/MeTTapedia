import Mettapedia.GSLT.Contracts.FrameUpdate
import Mettapedia.GSLT.Contracts.ReifiedActions
import Mettapedia.GSLT.Contracts.RelyGuaranteeClaims
import Mettapedia.GSLT.Contracts.DependencyClaims
import Mettapedia.GSLT.Contracts.AuthorityControls
import Mettapedia.GSLT.Contracts.IndexedAuthority
import Mettapedia.GSLT.Contracts.RunAccounts
import Mettapedia.GSLT.Contracts.ContractDimensions
import Mettapedia.GSLT.Contracts.AdministrationJoins
import Mettapedia.GSLT.Contracts.SocietyControls
import Mettapedia.GSLT.Contracts.CoordinationFreedom
import Mettapedia.GSLT.Contracts.AbsenceFrontier
import Mettapedia.GSLT.Contracts.FrontierNegation
import Mettapedia.GSLT.Contracts.ConsumptionArbitration
import Mettapedia.GSLT.Contracts.ConeCapabilities
import Mettapedia.GSLT.Contracts.AppendAuthority

/-!
# Semantic contracts: structure over one base of worlds and runs

A contract for a replaceable component can be read along behaviour, cost,
authority, interaction, transaction and progress. The specified readouts of
the finite service language have separating pairs
(`Contracts.Dimensions.not_factors`). This is independence of those readouts,
not a completeness or minimality theorem for arbitrary component contracts.
The constructions below reuse the existing resource, machine, observation and
account interfaces.

## Accounts: behaviour traces and cost

A run account assigns a monoid element to every run, multiplicatively
(`Mettapedia.Effects.RunAccount`).  Visible traces (the free monoid of events)
and costs are both run accounts of the same runs, and a contract reads both at
once through the product account (`Contracts.Accounts.contractAccount`).  An
observer that forgets events is a monoid homomorphism; forgetting faults
identifies runs whose raw traces differ (`Contracts.Accounts.fault_erasure_identifies`).
Branching behaviour and its quotients are the ordered machines and observers
of `Mettapedia.GSLT.Distinction`.

## Authority and its state interpretation

Authority is an element of a separation algebra.  Its **frame-preserving
updates** (`Contracts.FrameUpdate`) order it as a resource theory: shared
authority never updates to exclusive authority, so reading never becomes
consuming.  Authority is **reified** to states, and an action is lawful when it
preserves every frame (`Contracts.ActionPreserves`, the action judgement of the
Views framework); from that alone follow framing, sequencing and the soundness
of every interleaving of two threads (`Contracts.parallel`).

The same structure carries three of the six dimensions:

* **ownership and rights** (`Contracts.Access`, fractional permissions);
* **interference**: rely–guarantee claims form a separation algebra whose
  separateness is Jones's coexistence condition (`Contracts.RGClaim`);
* **transactions**: a dependency set is a rely–guarantee claim whose rely is
  checked at commit instead of assumed (`Contracts.Dependencies.claim`,
  `Contracts.Dependencies.valid_of_coexist`).

Indexed by worlds (`Contracts.IndexedAuthority`), authority forms an
opfibration: every admitted base arrow has a strongly co-Cartesian lift. This
does not authorize an actor to take that base arrow. Cartesian lifts, the
weakest authority before a change, exist exactly when transport has a right
adjoint; the constructed all-access revocation example has none
(`Contracts.revocationWorlds.revocationWorlds_not_isPreFibered`).  Transport
along every change of world keeps duplicable read authority non-exclusive.  A
plain record of capability labels proves none of this.

The state interpretation composes through existing proof-relevant loose
relations (`Contracts.ActionPreserves.ReifiesThrough.comp`). Frame lifting,
a reification square and action reflection transport the frame judgement
(`Contracts.ActionPreserves.transport_relation_comp`). The cell-swap encoding
and the representation with an effect log are constructed controls. Forgetting
a resource component without lifting its target frames can fail even with a
reification square and action reflection; preserving frames also does not
establish effect-order commutation.

Concrete complete-query dependencies join the existing adaptive interpreter
(`Contracts.Dependencies.validated_adaptive_query`). Ordered occurrence IDs
and payload claims preserve its whole observation under the explicit payload
integrity law. The same certificate composes through bind, validates performed
prefixes at resumption, and is preserved by a coexisting environment run.
Native matching and compilation must establish their own interpretation and
dependency completeness; these laws cover the pure occurrence-query profile.

## Progress: a separate obligation on the same runs

A safety simulation admits an implementation that stutters forever
(`Contracts.Joins.stutter_block`, `Contracts.Joins.stutter_never_stable`).
The rank of ranked administration is the progress certificate: under it a
stable state recurs on every infinite run (`Contracts.Joins.ranked_stable_within_rank`).
Progress is a property of runs with its own certificate. Stable recurrence
does not imply fair service of each task or a bound on native scheduling slots.

## Refinement

Replacing one component by another is a relation between their runs: a loose
arrow of the operational equipment (`Mettapedia.GSLT.LooseRelationEquipment`).
A contract refinement asks one such relation to satisfy each dimension's
predicate; composition needs the corresponding laws. Resource/reification
transport is proved here; execution observations and cost/progress comparisons
reuse `ObservationRefinement` and `SimulationComposition`, with independent
instance obligations. The transport conditions of
`Mettapedia.GSLT.Logic.SeparationTransport` are the conditions under which
reindexing keeps the separating connectives, and lifting extensions is also
what makes transport preserve frame-preserving updates
(`Contracts.preservesUpdates_of_liftsExtensions`).

## Several agents

The dimensions above are read by one observer, for components that all keep
their contracts.  `Contracts.Society` gives controls for two further families
of environments that a society of agents needs.  Observers: two programs agree
on all six readouts while one reveals an item it does not own
(`Contracts.Society.secret_pair_readouts`), and agreement among peers is a
joint observation that no single peer can make
(`Contracts.Society.equivocation_not_detectable_alone`).  Compliance: two
decision rules agree when every party complies and tolerate incomparable sets
of deviating parties (`Contracts.Society.tolerated_families_incomparable`).
For parties that keep their contracts, conflicting rights need overlapping
holdings (`Contracts.Society.conflict_needs_overlap`). A principal/coalition
realization, fault families and protocol laws are further requirements for a
Byzantine quorum interpretation.

## Coordination: presence, absence and frontiers

Presence-only programs (monotone, inflationary rules) are confluent and compute
their closure without coordination, and an inflationary program that computes
a function without coordination computes a monotone one
(`Contracts.Coordination.coordinationFree_of_presenceOnly`,
`Contracts.Coordination.monotone_of_coordinationFree`).  Absence breaks
confluence; firing absence rules only at a frontier, where the strata they
read are quiescent, restores determinacy
(`Contracts.Coordination.stratified_determinate`).  In a self-modifying space a
frontier for a pattern is a region closed under outputs that contains no match
(`Contracts.AbsenceFrontier.frontier_iff_closedRegion`), and absence read there
is final.  Under the over-approximation of firing, absence at a frontier is
exactly intuitionistic negation over the reachable states
(`Contracts.FrontierNegation.knot_iff_absent_frontier`); it is sound for every
refinement and not complete for them.  A module that owns a pattern's head
certifies such a frontier by a check on its own atoms, and only the module's own
installations revoke it (`Contracts.FrontierNegation.ownership_certifies_frontier`,
`Contracts.FrontierNegation.foreign_extension_certified`).  Consumption needs
arbitration: the first commit wins in every schedule, and exclusive consume
authority makes a consuming program confluent, with the holder's outcome
(`Contracts.Arbitration.first_committer_wins`, `Contracts.Arbitration.gated_confluent`).

## Limits

Frame-preserving updates are affine: discarding authority is always an update
(`Contracts.FrameUpdate.to_zero`).  Obligations that must be discharged need a
further law; at settlement it is the erasure licence of ordered
administration (`Contracts.Joins.erased_owner_not_licensed`). A dependent family
of committed observers uses this same boundary componentwise
(`OrderedSystem.erasurePreserves_family_iff`); the duty control rejects erasure
unless the duty is retained. This does not construct a compensator, authenticate
a settlement, or establish eventual discharge. Reification is
supplied with each instance; the obligation that a reification accounts for
every observation an action can make (absences, complete and ordered results,
occurrence identity) is part of each instance.
-/
