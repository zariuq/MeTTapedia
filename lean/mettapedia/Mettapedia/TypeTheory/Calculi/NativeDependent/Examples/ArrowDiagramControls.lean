import Mettapedia.CategoryTheory.ArrowDiagrams
import Mathlib.CategoryTheory.Types.Basic

/-!
# Both components matter in the arrow presentation

Two real commuting squares over the same Boolean-to-terminal arrow have
identical public codomain maps and different maps on the Boolean evidence.
The length-one diagram comparison retains that difference and both
endpoint maps; codomain projection alone loses it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ArrowDiagramControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.ArrowDiagrams

def specification : Arrow (Type) :=
  Arrow.mk (TypeCat.ofHom (fun _ : Bool => PUnit.unit))

def keep : specification ⟶ specification :=
  Arrow.homMk (TypeCat.ofHom id) (TypeCat.ofHom id) (by rfl)

def exchange : specification ⟶ specification :=
  Arrow.homMk (TypeCat.ofHom Bool.not) (TypeCat.ofHom id) (by rfl)

theorem readout_of_actual_exchange :
    ((toDiagrams (Type)).map exchange).app 0 false = true := rfl

theorem roundtrip_keeps_evidence_map :
    ((toArrows (Type)).map ((toDiagrams (Type)).map exchange)).left = exchange.left := rfl

theorem roundtrip_keeps_program_map :
    ((toArrows (Type)).map ((toDiagrams (Type)).map exchange)).right = exchange.right := rfl

theorem codomain_alone_identifies_squares :
    Arrow.rightFunc.map keep = Arrow.rightFunc.map exchange := rfl

theorem squares_remain_distinct : keep ≠ exchange := by
  intro same
  have values := congrArg (fun square : specification ⟶ specification => square.left false) same
  change false = true at values
  cases values

theorem diagrams_remain_distinct :
    (toDiagrams (Type)).map keep ≠ (toDiagrams (Type)).map exchange := by
  intro same
  have values := congrArg (fun square => square.app 0 false) same
  change false = true at values
  cases values

end Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ArrowDiagramControls
