import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSOperational
import Mettapedia.TypeTheory.PresheafFiniteSuccessorEvents

/-!
# Native operational edges of a finite-per-action GSOS law

The earned operational lifting of a natural law supplies the complete
successor presheaf. Exact direct-image substitution is obtained from the
actual variable-coalgebra square. The shared event construction therefore
retains independently supplied positive occurrence origins and derives
native negative availability. The action alphabet remains arbitrary.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.NativeEdges

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open PresheafFiniteSuccessorEvents PresheafEventCertificates

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]

def sortFunctor (sort : S.Srt) : S.Families ⥤ Type u where
  obj X := X PUnit.unit sort
  map mapping := mapping PUnit.unit sort

variable (law : Law S Actions) (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

abbrev terms (sort : S.Srt) : Cᵒᵖ ⥤ Type u :=
  worlds ⋙ S.termMonad.toFunctor ⋙ sortFunctor sort

theorem step_map {world future : Cᵒᵖ} (change : world ⟶ future)
    (sort : S.Srt) (source : S.Term (worlds.obj world) sort) (action : Actions sort) :
    Operational.coalgebra law (steps.app future) PUnit.unit sort
      (S.rename (worlds.map change) source) action =
    Mettapedia.CategoryTheory.FinitePowerset.map (S.rename (worlds.map change))
      (Operational.coalgebra law (steps.app world) PUnit.unit sort source action) := by
  have respects : ∀ base index value label,
      steps.app future base index (worlds.map change base index value) label =
        Mettapedia.CategoryTheory.FinitePowerset.map (worlds.map change base index)
          (steps.app world base index value label) := by
    intro base index value label
    exact congrArg (fun mapping => mapping base index value label) (steps.naturality change)
  exact Operational.coalgebra_rename law (steps.app world) (steps.app future)
    (worlds.map change) respects PUnit.unit sort source action

def system (sort : S.Srt) : System (terms worlds sort) (Actions sort) where
  successors world source action := Operational.coalgebra law (steps.app world) PUnit.unit sort source action
  map_successors change source action := step_map law worlds steps change sort source action

abbrev Event (Origins : Type u) (sort : S.Srt) (action : Actions sort) (world : Cᵒᵖ) :=
  (system law worlds steps sort).Event Origins action world

abbrev SourceFibre (Origins : Type u) (sort : S.Srt) (action : Actions sort)
    (world : Cᵒᵖ) (source : S.Term (worlds.obj world) sort) :=
  (system law worlds steps sort).SourceFibre Origins action world source

abbrev noAction (sort : S.Srt) (action : Actions sort) : Subfunctor (terms worlds sort) :=
  (system law worlds steps sort).absent PUnit.{u + 1} action

theorem noAction_iff_empty (sort : S.Srt) (action : Actions sort)
    (world : Cᵒᵖ) (source : S.Term (worlds.obj world) sort) :
    source ∈ (noAction law worlds steps sort action).obj world ↔
      Operational.coalgebra law (steps.app world) PUnit.unit sort source action = ∅ :=
  (system law worlds steps sort).absent_iff_empty action world source

end Mettapedia.OSLF.FiniteBranching.NativeEdges
