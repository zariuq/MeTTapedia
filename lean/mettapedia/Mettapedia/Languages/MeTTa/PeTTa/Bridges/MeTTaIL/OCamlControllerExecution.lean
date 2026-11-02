import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlBeginExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdmittedRunningTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdministrativeTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTransitionTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalCorrespondence
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceSourcePreservation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTerminalAdvance
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlMatchFailureTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlClauseFailureTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStep
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickObservation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedControlFlow
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceCacheInvariant
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerResultInvariant
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerProgressControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFiniteEvaluationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompletionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedFiniteEvaluation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedTextExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmissionControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedObservationControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTreeEmittedEvaluation
import Mettapedia.Languages.OCaml.TreeEvaluationControls

/-! Loaded O0 controller execution boundaries: source initialization,
running search ticks, source-authorized service restarts, advance
composition and terminal observation. Prepared-program admission and composed
call/let paths, source-encoded service caches and every pending administrative
running tick are connected to the independent source. Ordinary
source-step entry is connected through all enabled rows to loaded ticks.
Terminal readback and all service restarts preserve the source relation and
the complete epoch invariant; primitive execution is derived for all source
operators. Actual begin and arbitrary advance pages preserve a finite
independent source result across all service epochs, and completed public
readout reflects that result. Every finite independent source evaluation
also reaches a completed public result for every positive work quantum.
Accepted complete module text reads back to its emitted program, and the
named begin/run wrappers retain the loaded controller's call contracts.
Finite independent source results are realized through the named run entry;
completed observations at any budget reflect that result. Unallocated tree
evaluation and indexed evaluation now preserve and reflect one another,
including closures and recursive groups. Actual source lowering retains its
produced tree; finite tree results reach the named emitted entry, whose
completed readout agrees with them. Raw syntax/binding adequacy, general
target termination reflection and frontend/printing qualification remain
separate.
-/
