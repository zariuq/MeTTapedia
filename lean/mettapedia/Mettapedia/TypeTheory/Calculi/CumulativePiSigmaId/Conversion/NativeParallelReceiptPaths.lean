import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptJoin

/-!
# Computed finite confluence for native receipts

The native local diamond instantiates the generic quiver-path construction.
Both directed paths and finite symmetric paths compute a common term with
retained continuation paths. Authored replay uses the unchanged finite-code
checker. This accepts supplied parallel evidence, not a conversion-search
oracle or a normalization assumption.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt

open Presentation NativeCompletedRootCertificate
open Mettapedia.Logic.Relation

abbrev DirectedPath {n : Nat} (left right : Tower.Tm n) :=
  @Quiver.Path (ReceiptGraph n) _ left right

abbrev SymmetricPath {n : Nat} (left right : Tower.Tm n) :=
  @Quiver.Path (Quiver.Symmetrify (ReceiptGraph n)) _ left right

def diamond {n : Nat} : PathConfluence.DiamondOperation (ReceiptGraph n) :=
  fun {source _ _} first second => localJoin source first second

/-- Replay all selected edges, retaining their order in a composed certificate. -/
def replayPath {n : Nat} {source : Tower.Tm n} :
    {target : Tower.Tm n} → DirectedPath source target → Certificate source target
  | _, .nil => .refl source
  | _, .cons earlier last => (replayPath earlier).trans last.toCertificate

def joinPaths {n : Nat} {source left right : Tower.Tm n}
    (first : DirectedPath source left) (second : DirectedPath source right) :
    PathConfluence.Join (V := ReceiptGraph n) left right :=
  PathConfluence.join diamond first second

def joinSymmetricPath {n : Nat} {left right : Tower.Tm n}
    (path : SymmetricPath left right) : PathConfluence.Join (V := ReceiptGraph n) left right :=
  PathConfluence.joinZigzag diamond path

theorem joinPaths_lengths {n : Nat} {source left right : Tower.Tm n}
    (first : DirectedPath source left) (second : DirectedPath source right) :
    (joinPaths first second).fromLeft.length = second.length ∧
      (joinPaths first second).fromRight.length = first.length :=
  PathConfluence.join_lengths diamond first second

theorem joinSymmetricPath_lengths {n : Nat} {left right : Tower.Tm n}
    (path : SymmetricPath left right) :
    (joinSymmetricPath path).fromLeft.length = (PathConfluence.directions (V := ReceiptGraph n) path).1 ∧
      (joinSymmetricPath path).fromRight.length = (PathConfluence.directions (V := ReceiptGraph n) path).2 :=
  PathConfluence.joinZigzag_lengths diamond path

/-- Every computed continuation rechecks at its computed endpoint. -/
theorem joinPaths_rechecks {n : Nat} {source left right : Tower.Tm n}
    (first : DirectedPath source left) (second : DirectedPath source right) :
    NativeRelatorConversionChecking.check
        (replayPath (joinPaths first second).fromLeft).code left (joinPaths first second).common = true ∧
    NativeRelatorConversionChecking.check
        (replayPath (joinPaths first second).fromRight).code right (joinPaths first second).common = true :=
  ⟨(replayPath (joinPaths first second).fromLeft).checked,
    (replayPath (joinPaths first second).fromRight).checked⟩

#print axioms diamond
#print axioms replayPath
#print axioms joinPaths
#print axioms joinSymmetricPath
#print axioms joinPaths_lengths
#print axioms joinSymmetricPath_lengths
#print axioms joinPaths_rechecks

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt
