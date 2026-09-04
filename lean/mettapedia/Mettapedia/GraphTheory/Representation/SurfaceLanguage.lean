import Mettapedia.GraphTheory.Representation.RepresentationGSLT
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export

/-!
# An ergonomic, compositional surface language for graph representations

This `languageDef!` value gives the representation portfolio a compact,
printable object language.  It is deliberately a syntax boundary: the typed
operational GSLTs and their commuting theorems remain the semantic authority.
A later codec can connect concrete payload encodings to this surface without
changing the mathematical representation rules.

Atomic representation operations and composed plans are different syntactic
sorts.  A plan explicitly records the source and target stage of each atomic
leg, and `then` retains the authored order of legs.  Endpoint compatibility is
an elaboration obligation for the later exact codec; the surface grammar does
not pretend to prove it merely by parsing.
-/

namespace Mettapedia.GraphTheory.Representation.SurfaceLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- Pretty syntax for layouts, observations, and explicit transformation
requests. -/
def language : LanguageDef :=
  languageDef! {
    name : "FiniteGraphRepresentations"
    types {
      Vertex
      EdgeSeq
      MatrixRows
      AdjacencyRows
      NeighborSets
      IncidenceRows
      Offsets
      Neighbors
      Graph
      Stage
      Route
      Plan
      Bool
      Command
      Answer
    }
    terms {
      EdgeListStage . |- "edge-list" : Stage;
      MatrixStage . |- "adjacency-matrix" : Stage;
      RowsStage . |- "adjacency-rows" : Stage;
      NeighborSetsStage . |- "neighbor-finsets" : Stage;
      IncidenceStage . |- "incidence-matrix" : Stage;
      CSRStage . |- "csr" : Stage;

      EdgeListGraph . es:EdgeSeq |- "edge-list" "{" es "}" : Graph;
      MatrixGraph . rows:MatrixRows |- "matrix" "{" rows "}" : Graph;
      RowsGraph . rows:AdjacencyRows |- "rows" "{" rows "}" : Graph;
      NeighborSetsGraph . rows:NeighborSets |-
        "neighbor-sets" "{" rows "}" : Graph;
      IncidenceGraph . rows:IncidenceRows |- "incidence" "{" rows "}" : Graph;
      CSRGraph . offsets:Offsets, neighbors:Neighbors |-
        "csr" "{" offsets ";" neighbors "}" : Graph;

      MaterializeMatrix . |- "materialize-matrix" : Route;
      ExpandRows . |- "expand-rows" : Route;
      CollectNeighborSets . |- "collect-neighbor-sets" : Route;
      SerializeEdges . |- "serialize-edges" : Route;
      BuildIncidence . |- "build-incidence" : Route;
      PackCSR . |- "pack-csr" : Route;

      IdentityPlan . stage:Stage |-
        "identity" "(" stage ")" : Plan;
      AtomicPlan . route:Route, source:Stage, target:Stage |-
        "step" "(" route "," source "->" target ")" : Plan;
      ThenPlan . first:Plan, second:Plan |-
        "(" first ";" second ")" : Plan;

      At . stage:Stage, graph:Graph |-
        "at" "(" stage "," graph ")" : Command;
      Via . plan:Plan, graph:Graph |-
        "via" "(" plan "," graph ")" : Command;
      EdgeQuery . graph:Graph, source:Vertex, target:Vertex |-
        "edge?" "(" graph "," source "," target ")" : Command;
      NeighborsQuery . graph:Graph, vertex:Vertex |-
        "neighbors" "(" graph "," vertex ")" : Command;
      EdgesQuery . graph:Graph |- "edges" "(" graph ")" : Command;

      Yes . |- "yes" : Bool;
      No . |- "no" : Bool;
      BoolAnswer . value:Bool |- "answer" "(" value ")" : Answer;
      GraphAnswer . stage:Stage, graph:Graph |-
        "answer" "(" stage "," graph ")" : Answer;
    }
    equations { }
    rewrites { }
  }

/-- The ergonomic syntax passes the ordinary structural validator. -/
theorem language_validate : language.validate = [] := by
  decide +kernel

/-- Render through the shared MeTTaIL exporter rather than maintaining a
second handwritten printer. -/
def rendered : String :=
  Mettapedia.OSLF.MeTTaIL.Export.renderLanguageWithUserSyntax language

#print axioms language_validate

end Mettapedia.GraphTheory.Representation.SurfaceLanguage
