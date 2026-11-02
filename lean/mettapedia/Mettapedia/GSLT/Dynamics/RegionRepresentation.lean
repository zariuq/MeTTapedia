import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.GSLT.Dynamics.CertifiedRepresentationPlanning
import Mettapedia.Machines.ShapeCutComposition

/-!
# Representation routes and occurrence-preserving storage portfolios

The region portfolio consumes the existing heterogeneous execution routes.
Their local commuting squares, not a new interpreter, prove composition.
The concrete storage instance tags every row with its occurrence identity and
chooses among reversible skeleton cuts without contracting duplicates.
Selection is optimal for supplied catalogue scores only. Neither catalogue
completeness nor physical memory optimality is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified

open RegionHolePlan RepresentationSwitching CertifiedRepresentationPlanning
open OrderedOccurrenceBodyAlgebra

universe u

section Routes

variable {Obj : Type u} {Region Hole : Obj → Obj → Type u} {Engine Regime : Type u}
variable {source : IndexedCategory Obj Region}
variable {family : RepresentationSwitching.Family source Hole functionCategory.{u} Engine}
variable {origin : Engine} {X Y Z : Obj}

def routeBoundary (authored : Plan Obj Region Hole X Y)
    (future : RegionObservations.Family.{u, u, u} (family.reference.objectMap Y))
    {Summary : Type u} (summarize : family.reference.objectMap Y → Summary)
    (sufficient : future.Sufficient summarize) :
    Boundary ((family.engine origin).objectMap X) (family.reference.objectMap Y) Summary where
  source state := Plan.denote family.reference authored ((family.decode origin).component X state)
  summarize := summarize
  future := future
  sufficient := sufficient

def routeRegion {authored : Plan Obj Region Hole X Y}
    (route : CertifiedRoute family origin authored) (regime : Regime)
    (future : RegionObservations.Family.{u, u, u} (family.reference.objectMap Y))
    {Summary : Type u} (summarize : family.reference.objectMap Y → Summary)
    (sufficient : future.Sufficient summarize) :
    CertifiedRegion (routeBoundary (origin := origin) authored future summarize sufficient) Regime where
  regime := regime
  Artifact := Result family Y
  attempt state := .committed (route.run state)
  decode result := summarize (observeResult result)
  restores _ _ impossible := by cases impossible
  exact state _ committed := by
    cases committed
    exact congrArg summarize (route.run_exact state)

/-- The actual middle engine and source position must agree for composition.
Conversions retain their existing route evidence and cost records. -/
def appendRoutes {first : Plan Obj Region Hole X Y} {later : Plan Obj Region Hole Y Z}
    (earlier : CertifiedRoute family origin first)
    (next : CertifiedRoute family earlier.finish later) :
    CertifiedRoute family origin (first.append later) where
  finish := next.finish
  execution := earlier.execution.append next.execution
  source_exact := by rw [Execution.erase_append, earlier.source_exact, next.source_exact]

theorem appended_route_exact {first : Plan Obj Region Hole X Y} {later : Plan Obj Region Hole Y Z}
    (earlier : CertifiedRoute family origin first)
    (next : CertifiedRoute family earlier.finish later)
    (state : (family.engine origin).objectMap X) :
    observeResult ((appendRoutes earlier next).run state) =
      Plan.denote family.reference later
        (Plan.denote family.reference first ((family.decode origin).component X state)) := by
  rw [(appendRoutes earlier next).run_exact, Plan.denote_append]
  rfl

end Routes

namespace StorageCuts

open Mettapedia.Machines.ShapeStore

variable {Id Atom : Type}

abbrev Facts (Id Atom : Type) := Multiset (Id × Tm Atom)
abbrev Rows (Id Atom : Type) := Multiset (Id × Row Atom)

def encode (cut : Cut Atom) (facts : Facts Id Atom) : Rows Id Atom :=
  facts.map fun fact => (fact.1, cut.d fact.2)

def decode (rows : Rows Id Atom) : Facts Id Atom :=
  rows.filterMap fun row => (reassemble row.2).map (fun term => (row.1, term))

theorem decode_encode (cut : Cut Atom) (facts : Facts Id Atom) : decode (encode cut facts) = facts := by
  simp only [decode, encode, Multiset.filterMap_map, Function.comp_def, cut.sec,
    Option.map_some, Prod.mk.eta, Multiset.filterMap_some]

/-- This exact future family can inspect identities as well as payloads.
It therefore never licenses identifying equal payloads at different IDs. -/
def questions : RegionObservations.Family (Facts Id Atom) where
  Question := Facts Id Atom → Bool
  Answer _ := Bool
  read question facts := question facts

def boundary : Boundary (Facts Id Atom) (Facts Id Atom) (Facts Id Atom) where
  source := id
  summarize := id
  future := questions
  sufficient _ _ same _ := congrArg _ same

def region (cut : Cut Atom) : CertifiedRegion (boundary (Id := Id) (Atom := Atom)) Nat where
  regime := 0
  Artifact := Rows Id Atom
  attempt facts := .committed (encode cut facts)
  decode := decode
  restores _ _ impossible := by cases impossible
  exact facts _ committed := by
    cases committed
    exact decode_encode cut facts

def candidates (cuts : List (Cut Atom × (Facts Id Atom → Estimate))) :
    List (Candidate (boundary (Id := Id) (Atom := Atom)) Nat) :=
  cuts.zipIdx |>.map fun entry =>
    { region := region entry.1.1, estimate := entry.1.2, ordinal := entry.2 }

theorem catalogue_exact (cuts : List (Cut Atom × (Facts Id Atom → Estimate)))
    (facts : Facts Id Atom) : RegionPortfolio.execute facts (candidates cuts) = facts :=
  RegionPortfolio.execute_exact facts _

theorem chosen_catalogue_minimal (cuts : List (Cut Atom × (Facts Id Atom → Estimate)))
    (facts : Facts Id Atom) (chosen other : Candidate (boundary (Id := Id) (Atom := Atom)) Nat)
    (selected : RegionPortfolio.select facts (candidates cuts) = some chosen)
    (present : other ∈ candidates cuts) : chosen.score facts ≤ other.score facts :=
  RegionPortfolio.selected_minimal facts _ chosen selected other present

/-- Re-cut by decoding the old row and encoding it with the new cut. The
identity field is never regenerated from position or value. -/
def transfer (cut : Cut Atom) (rows : Rows Id Atom) : Rows Id Atom := encode cut (decode rows)

theorem transfer_preserves (cut : Cut Atom) (rows : Rows Id Atom) :
    decode (transfer cut rows) = decode rows := decode_encode cut _

theorem transfer_comp (first second : Cut Atom) (rows : Rows Id Atom) :
    transfer second (transfer first rows) = transfer second rows := by
  simp [transfer, decode_encode]

namespace Controls

def repeated : Facts Nat Nat := {(10, .atom 7), (20, .atom 7), (20, .atom 7)}

theorem cuts_really_change_storage :
    encode rootCut repeated ≠ encode noCut repeated := by decide

theorem both_cuts_keep_all_occurrences :
    decode (encode rootCut repeated) = repeated ∧ decode (encode noCut repeated) = repeated :=
  ⟨decode_encode _ _, decode_encode _ _⟩

theorem repeated_identity_occurrence_stays_repeated :
    (decode (transfer noCut (encode rootCut repeated))).count (20, .atom 7) = 2 := by
  rw [transfer_preserves, decode_encode]
  decide

theorem payload_only_identity_is_insufficient :
    ([(10, 7), (20, 7)] : List (Nat × Nat)).map Prod.snd = [7, 7] ∧
      ([(10, 7), (20, 7)] : List (Nat × Nat)) ≠ [(10, 7), (10, 7)] := by decide

end Controls
end StorageCuts

#print axioms routeRegion
#print axioms appended_route_exact
#print axioms StorageCuts.decode_encode
#print axioms StorageCuts.catalogue_exact
#print axioms StorageCuts.transfer_comp

end Mettapedia.GSLT.Dynamics.ObservationQualified
