import Mettapedia.Machines.StoreInteraction.AtomicObservation
import Mettapedia.Machines.StoreInteraction.BranchWorlds
import Mettapedia.Machines.StoreInteraction.ReactivePolicies
import Mettapedia.Machines.StoreInteraction.ReadDelivery
import Mettapedia.Machines.StoreInteraction.ReferenceOrder
import Mettapedia.Machines.StoreInteraction.TokenPolicies
import Mettapedia.Machines.StoreInteraction.ValidationChoices
import Mettapedia.Machines.StoreInteraction.ValidationCost
import Mettapedia.Machines.Cursor.ReadAdmissionProfiles
import Mettapedia.Machines.Cursor.ReadScopeComposition
import Mettapedia.Machines.Cursor.JoinOrderProfiles
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.AtomicFusion
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.StaticFootprints
import Mettapedia.GSLT.OpenEnded.ChaoticIteration

/-!
# Qualified mathematical comparisons for mutable-store interaction protocols

Read scope, historical versus current dependencies, delivery, commit size,
branch isolation, scheduling and reactive triggering are separate decisions.
The imported occurrence models supply validation and serializability laws;
the new controls separate choices that final-store or complete-bag equality
alone cannot identify. No source-language default or native refinement is
selected by this module.
-/
