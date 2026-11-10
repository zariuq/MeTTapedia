import Mettapedia.Languages.MeTTa.StoreAndDemand.StoreEffects
import Mettapedia.Languages.MeTTa.StoreAndDemand.PeTTaSelection
import Mettapedia.Languages.MeTTa.StoreAndDemand.ValidationReuse
import Mettapedia.Languages.MeTTa.StoreAndDemand.RunReceipts
import Mettapedia.Languages.MeTTa.StoreAndDemand.Demand
import Mettapedia.Languages.MeTTa.StoreAndDemand.SearchCursor

/-!
# Store and demand acceptance contracts

This entry imports the source-level contracts, their occurrence-step adapters,
the scoped selector theorem, and first-answer/ownership observations. The
executable calibration fixtures are in `MettaKernel/Examples/StoreAndDemand`.
Neither the import closure nor the fixture replay proves CeTTa's C implementation.
-/
