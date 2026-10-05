import Mettapedia.GSLT.Distinction.PublicationBlocks
import Mettapedia.GSLT.Distinction.PublicationBlocksControls
import Mettapedia.Languages.MeTTa.HE.ModulePublication
import Mettapedia.GSLT.Distinction.ProductionLicences
import Mettapedia.GSLT.Distinction.ProductionLicencesControls
import Mettapedia.GSLT.Distinction.LevelAccounts
import Mettapedia.GSLT.Distinction.LevelAccountsControls
import Mettapedia.Machines.BranchLocalNeed.QualifiedReplay

/-!
# Index: publication blocks, production licences and level-indexed accounts

* `GSLT/Distinction/PublicationBlocks` and its controls: module publication as
  an effect-aware productive block, with atomic registry changes, exact
  resumption of imports and retained callback identities; the HE instance
  `Languages/MeTTa/HE/ModulePublication` reads its links as HE's guarded
  dependency insertion.
* `GSLT/Distinction/ProductionLicences` and its controls: ordered sharing
  licences whose answer occurrences carry monoid-valued production
  coefficients, the noncommutative moving condition, and the observation
  theorem separating coefficients from observer weights.
* `GSLT/Distinction/LevelAccounts` and its controls: reference, work and
  overhead readings, qualified replay, checked bounds, exactness only for real
  costs with fork and erasure, span and storage release apart from work, and
  whole-parent suspension; the Need instance
  `Machines/BranchLocalNeed/QualifiedReplay`.

The Prime-candidate instance `Languages/MeTTa/PrimeCandidates/NativeCandidateLevelAccounts`
is kept out of this index, beside the candidate cost interface.
-/
