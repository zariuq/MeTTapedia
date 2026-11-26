import Mettapedia.GSLT.Equations.AtomicMatcher
import Mettapedia.GSLT.Equations.CandidateSelection
import Mettapedia.GSLT.Equations.RecipeMatching
import Mettapedia.GSLT.Equations.RelationalPlan
import Mettapedia.GSLT.Equations.ClassChange
import Mettapedia.GSLT.Equations.LinearRead
import Mettapedia.GSLT.Equations.SelectiveCursor
import Mettapedia.GSLT.Equations.Preference
import Mettapedia.GSLT.Equations.PreferredSection
import Mettapedia.GSLT.Equations.PostingInformation
import Mettapedia.GSLT.Equations.MixedRadix

/-! # Scoped equality: matching, presentations, and occurrence data

These are theories of distinct operations. A presentation chooses spelling;
a class key tests equality; a recipe query asks how a class can be built;
an occurrence cursor observes stored positions. A dense class number does
not authorize confusing any of these. Concrete controls and worked
instances are in `Mettapedia.GSLT.Equations.Examples`.
-/
