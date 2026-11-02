import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.OSLF.MeTTaIL.ScopedEquationControls
import Mettapedia.OSLF.MeTTaIL.Upstream.Ambient

/-!
# Controls: declared equations in the reference relation

An equation with binders that declares the bound names its metavariables may use is read through that declaration.

- **Exchanging restrictions swaps**: upstream's ambient `NewComm` has the same pattern on both sides, so the ordinary
  matcher reads it as `P = P` (`newComm_raw_is_identity`). Read through its declaration, stated as upstream's
  declaration reduces, it relates `(νx)(νy) x[y[0]]` to `(νx)(νy) y[x[0]]` (`newComm_swaps`).
- **Scope extrusion** is an equation step under a binder, in both directions (`extrusion_step`,
  `extrusion_step_back`).
- **Negative**: a component that uses the restricted name is not moved out of its scope (`dependent_not_extruded`), and
  the ordinary matcher no longer reads either equation (`newComm_not_raw`, `extrusion_not_raw`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStepDeclaredControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution

/-! ## Exchanging restrictions -/

def name : TypeExpr := .base "Name"
def zero : Pattern := .apply "PZero" []
def new (body : Pattern) : Pattern := .apply "PNew" [.lambda none body]
def amb (name body : Pattern) : Pattern := .apply "PAmb" [name, body]

/-- Upstream's ambient `NewComm`, as its declaration reduces: the body's arguments follow the binder names. -/
def newComm : Equation where
  name := "NewComm"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := new (new (.fvar "P"))
  right := new (new (.fvar "P"))
  bindings := some
    { dependencies := [("P", [name, name])]
      occurrences :=
        [{ name := "P", site := .left, path := [0, 0, 0, 0], arguments := [.bvar 0, .bvar 1] },
         { name := "P", site := .right, path := [0, 0, 0, 0], arguments := [.bvar 1, .bvar 0] }] }

-- The literal is upstream's reduced declaration.
#guard (Upstream.Ambient.reduced.equations[0]?).map (fun row => (row.left, row.right, row.bindings)) ==
  some (newComm.left, newComm.right, newComm.bindings)

def exchange : LanguageDef := { LanguageDef.empty "Exchange" with equations := [newComm] }

/-- `(νx)(νy) x[y[0]]` -/
def nested : Pattern := new (new (amb (.bvar 1) (amb (.bvar 0) zero)))

/-- `(νx)(νy) y[x[0]]` -/
def swapped : Pattern := new (new (amb (.bvar 0) (amb (.bvar 1) zero)))

/-- The ordinary matcher sees the same pattern on both sides. -/
theorem newComm_raw_is_identity : newComm.left = newComm.right := rfl

theorem newComm_not_raw : readsRaw newComm = false := by decide +kernel

/-- **Read through its declaration, `NewComm` exchanges the restrictions.** -/
theorem newComm_swaps : AuthoredEquation RelationEnv.empty exchange nested swapped :=
  .declared (orientation := .forward) (ambient := 0) (List.mem_singleton_self _) newComm_not_raw (by decide +kernel)

theorem nested_ne_swapped : nested ≠ swapped := by decide

/-! ## Scope extrusion -/

theorem extrusion_member : ScopedEquationControls.extrusionEquation ∈ ScopedEquationControls.language.equations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem extrusion_not_raw : readsRaw ScopedEquationControls.extrusionEquation = false := by decide +kernel

/-- **Extrusion is an equation step under an outer binder.** -/
theorem extrusion_step :
    EquationStep RelationEnv.empty ScopedEquationControls.language (.lambda none ScopedEquationControls.extrusionSource)
      (.lambda none ScopedEquationControls.extrusionTarget) :=
  .inContext (.lambda none .hole)
    (Or.inl (.declared (orientation := .forward) (ambient := 1) (source := ScopedEquationControls.extrusionSource)
      (target := ScopedEquationControls.extrusionTarget) extrusion_member extrusion_not_raw
      (by rw [ScopedEquationControls.extrusion_preserves_the_two_contexts]; exact List.mem_singleton_self _)))

/-- **And back**: the restriction widens over the independent component. -/
theorem extrusion_step_back :
    EquationStep RelationEnv.empty ScopedEquationControls.language (.lambda none ScopedEquationControls.extrusionTarget)
      (.lambda none ScopedEquationControls.extrusionSource) :=
  .inContext (.lambda none .hole)
    (Or.inl (.declared (orientation := .reverse) (ambient := 1) (source := ScopedEquationControls.extrusionTarget)
      (target := ScopedEquationControls.extrusionSource) extrusion_member extrusion_not_raw
      (by rw [ScopedEquationControls.extrusion_reverse_restores_the_two_contexts]; exact List.mem_singleton_self _)))

/-- **A component using the restricted name stays in its scope.** -/
theorem dependent_not_extruded (target : Pattern) :
    target ∉ applyEquationAt ScopedEquationControls.language 1 ScopedEquationControls.extrusionEquation .forward
      (.apply "Nu" [.lambda none (.apply "Pair"
        [.apply "Out" [.bvar 0, .bvar 1], .apply "Out" [.bvar 0, .bvar 1]])]) := by
  rw [ScopedEquationControls.dependent_component_cannot_be_extruded]
  exact List.not_mem_nil

end Mettapedia.OSLF.MeTTaIL.ReferenceStepDeclaredControls
