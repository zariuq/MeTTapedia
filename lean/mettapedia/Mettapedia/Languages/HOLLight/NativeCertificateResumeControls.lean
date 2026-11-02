import Mettapedia.Languages.HOLLight.NativeCertificateResume

/-!
# Producer-state resumption controls

The fixture has two Boolean variables and an assumption theorem. The resumed
writer must allocate the same next term/theorem identifiers and emit the same
suffix as the original writer. These are executable format controls, not
logical validity claims for arbitrary imported streams.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.NativeCertificateResume.Controls
open Mettapedia.Languages.OpenTheory NativeCertificateExport
open SharedCertificateExport (NamedNode)

def digest : String := String.ofList (List.replicate 64 '0')

def fixture (sourceDigest : String) : Except String NativeCertificateExport.State := do
  let initial ← NativeCertificateExport.initial .unrestricted sourceDigest
  let (_,writer) ← (do
    let first ← internName "resume-p"
    let second ← internName "resume-q"
    let boolean ← internType Ty.bool
    record 4 [first,boolean]
    modify fun (state : NativeCertificateExport.State) => {state with terms := state.terms.insert (.variable first boolean) 0}
    record 4 [second,boolean]
    modify fun (state : NativeCertificateExport.State) => {state with terms := state.terms.insert (.variable second boolean) 1}
    record 0x15 [0]
    modify fun (state : NativeCertificateExport.State) => {state with theorems := state.theorems+1}
    record 0x35 [0,1,0,0]
    record 0x34 [0,0]
    emitRoot 0).run initial
  return writer

def appendIdentity (writer : NativeCertificateExport.State) : Except String NativeCertificateExport.State := do
  let (_,writer) ← (do
    record 0x19 [0,0]
    modify fun (state : NativeCertificateExport.State) => {state with theorems := state.theorems+1}
    record 0x35 [1,1,0,0]
    record 0x34 [1,0]
    emitRoot 1).run writer
  return writer

def continuationAgrees : Bool := match fixture digest with
  | .error _ => false
  | .ok original => match restore .unrestricted digest (finish original) with
    | .error _ => false
    | .ok resumed =>
      resumed.roots == #[0] && resumed.writer.records == original.records &&
      resumed.writer.names.size == 3 && resumed.writer.types.size == 1 && resumed.writer.terms.size == 2 &&
      resumed.writer.theorems == 1 && resumed.writer.axioms.isEmpty &&
      match appendIdentity original,appendIdentity resumed.writer with
      | .ok first,.ok second => finish first == finish second && first.theorems == 2 && second.theorems == 2
      | _,_ => false

def rejects (input : ByteArray) : Bool := match restore .unrestricted digest input with
  | .error _ => true
  | .ok _ => false
def headerRefusal : Bool := match fixture digest with
  | .error _ => false
  | .ok writer => rejects ((finish writer).set! 0 0)
def checksumRefusal : Bool := match fixture digest with
  | .error _ => false
  | .ok writer => let bytes := finish writer; rejects (bytes.set! (bytes.size-1) (bytes[bytes.size-1]! ^^^ 1))
def truncationRefusal : Bool := match fixture digest with
  | .error _ => false
  | .ok writer => let bytes := finish writer; rejects (bytes.extract 0 (bytes.size-1))
def trailingRefusal : Bool := match fixture digest with
  | .error _ => false
  | .ok writer => rejects ((finish writer).push 0)
def futureRefusal : Bool := match fixture digest with
  | .error _ => false
  | .ok writer => match (record 0x19 [0,1]).run writer with
    | .error _ => false
    | .ok (_,bad) => rejects (finish bad)
def duplicateRefusal : Bool := match fixture digest with
  | .error _ => false
  | .ok writer => match (record 4 [0,0]).run writer with
    | .error _ => false
    | .ok (_,bad) => rejects (finish bad)
def wideRefusal : Bool := match fixture digest with
  | .error _ => false
  | .ok writer => rejects (finish {writer with bytes := writer.bytes.push 1 ++ varint (2^62),records := writer.records+1})

def checks : List (String × Bool) :=
  [("continued dictionary and theorem allocation",continuationAgrees),
   ("wrong header",headerRefusal),("wrong checksum",checksumRefusal),
   ("truncation",truncationRefusal),("trailing bytes",trailingRefusal),
   ("future theorem reference",futureRefusal),("duplicate producer dictionary key",duplicateRefusal),
   ("oversized native integer",wideRefusal)]

def run : IO Unit := do
  for (name,passed) in checks do
    unless passed do throw (IO.userError s!"Native resume control failed: {name}")
  IO.println s!"PASS {checks.length} native producer-state controls"

end Mettapedia.Languages.HOLLight.NativeCertificateResume.Controls
