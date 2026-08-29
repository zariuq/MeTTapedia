import Mettapedia.Languages.Metamath.MM2DataEncoding

/-!
# Source-derived rows for the MM2 normal-proof machine

This module is the small data boundary shared by the Metamath-to-MM2
transformer and source-action planning.  It contains only total encoders from
an authored source state to inert MM2 rows; it contains no verifier rules,
scheduler, proof checker, or target execution semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2Transformation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceGSLTState

/-- Runtime lookup for the caller's symmetric DV relation. -/
def callerDVRow (scopeOwner : Atom) (left right : String) : Atom :=
  .expression
    [.symbol "mm-caller-dv", scopeOwner, stringAtom left, stringAtom right]

/-- Both licensed query orientations of one canonical source DV pair. -/
def callerDVRowsForPair (scopeOwner : Atom)
    (pair : String × String) : List Atom :=
  [callerDVRow scopeOwner pair.1 pair.2,
   callerDVRow scopeOwner pair.2 pair.1]

def callerDVRowsOfPairs (scopeOwner : Atom)
    (pairs : List (String × String)) : List Atom :=
  (pairs.map (callerDVRowsForPair scopeOwner)).flatten

def callerDVRows (scopeOwner : Atom) (state : SourceState) : List Atom :=
  callerDVRowsOfPairs scopeOwner state.proofDistinctVariables

/-- Execution indexes derived from every assertion occurrence in the
authored ordered source state. -/
def assertionExecutionRows (scopeOwner : Atom)
    (state : SourceState) : List Atom :=
  (state.assertions.mapIdx fun position assertion =>
    assertionExecutionRowsFor scopeOwner position assertion).flatten

/-- Complete inert data read by the generic normal-proof machine. -/
def normalExecutionRows (scopeOwner : Atom)
    (state : SourceState) : List Atom :=
  callerDVRows scopeOwner state ++ assertionExecutionRows scopeOwner state

end Mettapedia.Languages.Metamath.MM2Transformation
