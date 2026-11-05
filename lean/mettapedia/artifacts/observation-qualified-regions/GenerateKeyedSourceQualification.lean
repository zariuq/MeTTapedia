import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedSourceQualification

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedSourceQualification

#eval IO.println (Lean.Json.mkObj [
  ("rendering_checks", Lean.toJson renderingChecks),
  ("packets", Lean.Json.arr packets.toArray)]).compress
