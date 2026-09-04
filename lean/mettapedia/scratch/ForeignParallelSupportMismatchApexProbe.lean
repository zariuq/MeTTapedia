import ForeignParallelSupportMismatchCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignParallelSupportMismatchApexProbe

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open ForeignParallelSupportMismatchCanary

theorem leftEntries_length :
    leftViewPair.2.node.finiteBoundaryTable.entries.length = 1 := by
  decide

theorem rightEntries_length :
    rightViewPair.2.node.finiteBoundaryTable.entries.length = 1 := by
  decide

theorem leftEntries_support :
    leftViewPair.2.node.finiteBoundaryTable.entries.map
        (fun entry => entry.boundary.targetSupport) = [available] := by
  decide

theorem rightEntries_support :
    rightViewPair.2.node.finiteBoundaryTable.entries.map
        (fun entry => entry.boundary.targetSupport) = [available] := by
  decide

end ForeignParallelSupportMismatchApexProbe
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
