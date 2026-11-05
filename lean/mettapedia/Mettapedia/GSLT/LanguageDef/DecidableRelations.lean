import Mettapedia.GSLT.LanguageDef.DecidableRelations.Core
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Stores
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Tables
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Disequality
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Membership
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Observers
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Composition
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Controls
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Frame
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Snapshots
import Mettapedia.GSLT.LanguageDef.DecidableRelations.Counting

/-!
# Complemented relations for GSLT languages

A GSLT's premises are positive. Negative information enters through relations complemented in a region, each with a
certified complement, and such relations are decidable there:
- `Core`: complemented relations, negation as failure in the region, their Boolean algebra, and the bridge to
  `IsCompl` on the region;
- `Stores`: decision procedures and closed fact stores as relation environments that decide their relations;
- `Tables`: stores that list their rows; a closed table's complement holds of exactly the first-order tuples it does not
  list;
- `Disequality`: equality and disequality derived by a language's own generated rules, complemented on the signature's
  terms;
- `Membership`: membership and non-membership in a closed bag or set, non-membership by `forAll` over the collection's
  elements with the language's own disequality, complemented;
- `Observers`: observers of the distinction calculus decide their distinctions and non-membership relative to them;
  the sharp observer is the language's own equality; a keyed index hosts a relation exactly when its keys are a
  canonical form;
- `Composition`: privacy survives joins, so complemented relations transfer; generated complements grow with the
  signature; joining the parts' complements is incomplete, so composition is a join followed by a closure;
- `Controls`: positive and negative examples, privacy shown necessary, and a closed fact store;
- `Frame`: local rules keep their steps under a frame, a rule guarded by non-membership does not, so
  non-membership needs a premise over the rest;
- `Snapshots`: a store at a vantage of a construction base is closed inside the snapshot; its counterexamples persist,
  and its universal verdicts hold in the full world exactly where "that's all" holds at the vantage;
- `Counting`: the number of occurrences in a closed collection, derived element by element with the language's own
  disequality; the count zero is non-membership, and a count is complemented by the other counts.
-/
