import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.ReadPolarity
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.OwnedReads
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.DelegatedReads
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.VerdictBoard
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.HandleResolution
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.ServiceGrants
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.GrantLineage
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.AmbientPurity
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.KernelCommit
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.SharedReads

/-!
# Region permissions: one discipline for who may write a region and which reads stay true

A region's permissions are facets held at its name (`InteractionTypes.Facets`): `send` makes,
`receive` takes, `peek` keeps, `observe` queries. Authority moves only by passing
capabilities from a declared genesis (`Machines.Kernel.Delegation`). This folder joins the two and
reads off what each read of a region needs.

## A read's polarity says which capability fact it needs (`ReadPolarity`, `OwnedReads`, `DelegatedReads`)

| read | falsified by | correct without a region epoch when | stable over the others' runs when |
|---|---|---|---|
| existential (a matched witness) | a take of its witnesses | always: its witnesses validate it | no other subject can reach `receive` |
| universal (`∀`, absence) | one make | never: no occurrence validates it | no other subject can reach `send` (owned), or all of theirs were revoked (sealed) |
| exact (count, unique, snapshot) | any write | never | no other subject can reach `send` or `receive` |

The owned condition is a property of the genesis (`Delegation.canHold_iff`), and it is exact for
absence (`absence_preserved_iff`). Sealing is revocation of a root that every other `send` derives
from (`revoke_seals`, `stable_after_seal`). Otherwise the read is validated at commit time
(`Enabled.queries_hold`), which a runtime realizes with an epoch of the region. On the runtime's
revision protocol, another subject's authorized write makes the reading transaction stale for ever
(`SharedReads.shared_absence_stale_under_revision`), and so does any write outside the region
(`SharedReads.write_outside_stales_revision`).

So for any region the trade-off is: many writers and only existential reads (channels, logs), or
universal reads with one writer or a seal (boards, owned spaces), or both with validation on every
universal read (shared spaces).

## The kernel is an owner (`OwnedReads.kernel_reads_stable`, `VerdictBoard`)

Only the kernel holds `send` at its rule and verdict regions; its universal reads there are stable
against users, and its verdicts are all derivable (`board_verdicts_derivable`). "Sole writer" is
sole *sequential* writer: two of its own admissions of one head skew (`Controls.kernel_self_skew`).
Users hold `peek` on verdicts, not `receive`: with `receive` one user deletes another's theorem
(`Controls.receive_deletes_verdict`).

## Minting is one discipline, use is two (`VerdictBoard`, `HandleResolution`)

The mint law holds per region; a reader must also know which region it reads
(`Controls.forger_board_mints`). Resolving a written name to its holder's facets makes naming into
authority (`public_name_gives_holder`); handles alone keep the bound (`board_handles_no_other_send`).

## Learning: names carried are facets carried (`HandleResolution`)

A process learns from what it takes, keeps or sees in a predicate query (`Commit.learnedFrom`).
Reading a carried name as every facet at it, the facets it learns are the names it learns in
`ScopeExtrusion` (`facets_learned_eq_names`, `Controls.predicate_query_teaches`). Every one-process
authority run is a dynamic run, and a dynamic run is an authority run exactly when its commits make
only names held before them (`AuthorityRun.dynamicRun`, `authorityRun_iff_dynamicRun`).

The writes at a set of names (`MakesOutside`, `TakesOutside`) and their laws are those of
`OccurrenceCommits.ChannelAddressing`, the frame law of regions of `Commits` read through
addresses; the laws of a missing `send` or `receive` in `InteractionTypes.Facets` are its
instances. A fenced lease's token is
a versioned capability (`Coordination.AuthorityRoles.current_iff_valid`), and judgment authority
(`TypeTheory.Authority`, the evidence accepted for a judgment) is a different notion from these
interaction rights.

## The interaction kernel's commit check (`KernelCommit`)

The kernel's check is revisions, rights per handle, presence and the specification's linearity
(`check_iff`); what it accepts is enabled under the revision contract (`enabled_of_check`) and formed
under the handles' rights (`formedUnder_of_check`). The absence of sources escapes `observe`
(`Controls.absence_of_sources_not_formed`), and its printed record is vacuous for the trace checker
(`Controls.Printed.printed_absence_of_source_vacuous`).

## The draft's two other mechanisms, as models (`ServiceGrants`, `AmbientPurity`)

The space service's lineage attenuates rights. Its earlier rule let a child drop a ticket
requirement (`native_free_appends`); the draft's rule now keeps closed requirements
(`ServiceEdge`), which bounds every row addition by tickets (`rowAdds_le_tickets`). Its grant table
refines the delegation core, with principals as subjects and usages as objects, exactly for edge
rules that keep closed requirements (`GrantLineage.refines`, `not_refines_of_escape`), so every
live usage comes from a root (`usage_from_root`). The core over-approximates the service's
non-delegable grants (`Controls.core_spreads_nondelegable`).
The evaluator's effect gate is a dynamic flag whose soundness is a global invariant over its entry
points (`gate_sound`, `install_creates_authority`). Its combined flag cannot recover whether a
refusal belongs to the observation or its caller (`boundary_decision_not_from_combined`). For a
finite closed authority graph, distinct denying owners cannot be replaced by one owner identity
(`refusingOwners_not_singleton`); closed carriers agree on the graph's refusals
(`refusingGraph_independent`), while several denying scopes may share one owner
(`Controls.branching_shared_owner_control`). These are semantic models, not native graph transport.
-/
