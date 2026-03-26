import Mettapedia.Languages.Metamath.MMLean4Bridge

/-!
# Grounded Metamath Semantics (mm-lean4 backed)

This module intentionally keeps Metamath semantics in `mettapedia` grounded in
`mm-lean4` runtime + kernel artifacts, with no opaque relation placeholders.
-/

namespace Mettapedia.Languages.Metamath.GroundedSemantics

open Mettapedia.Languages.Metamath.MMLean4Bridge

/-- Execute the verified parser/checker pipeline from `mm-lean4`. -/
def checkBytesDB (arr : ByteArray) (config : RuntimeMode := {}) : RuntimeDB :=
  Metamath.Verify.checkBytes arr config

/-- Runtime acceptance criterion: no parser/proof error was recorded. -/
def acceptsDB (db : RuntimeDB) : Prop :=
  db.error = false

/-- Byte-level acceptance criterion via the verified checker pipeline. -/
def acceptsBytes (arr : ByteArray) (config : RuntimeMode := {}) : Prop :=
  acceptsDB (checkBytesDB arr config)

/-- Byte-level rejection criterion (dual to acceptance). -/
def rejectsBytes (arr : ByteArray) (config : RuntimeMode := {}) : Prop :=
  (checkBytesDB arr config).error = true

/-- Parse/proof diagnostic code exposed directly from `mm-lean4`. -/
def parseErrorCode? (arr : ByteArray) (config : RuntimeMode := {}) :
    Option Metamath.Verify.ParseErrorCode :=
  (checkBytesDB arr config).parseErrorCode?

theorem acceptsBytes_iff_noError
    (arr : ByteArray) (config : RuntimeMode := {}) :
    acceptsBytes arr config ↔ (checkBytesDB arr config).error = false := by
  rfl

theorem rejectsBytes_iff_error
    (arr : ByteArray) (config : RuntimeMode := {}) :
    rejectsBytes arr config ↔ (checkBytesDB arr config).error = true := by
  rfl

/-- One-step runtime reduction (normal proof step) as an option-level wrapper. -/
def RuntimeState.step? (rt : RuntimeState) (label : String) : Option RuntimeState :=
  match rt.stepNormal label with
  | .ok rt' => some rt'
  | .error _ => none

/-- Optional spec image after one runtime step. -/
def RuntimeState.stepSpec? (rt : RuntimeState) (label : String) : Option SpecState := do
  let rt' ← RuntimeState.step? rt label
  RuntimeState.toSpecState? rt'

end Mettapedia.Languages.Metamath.GroundedSemantics
