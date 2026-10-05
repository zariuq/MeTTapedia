import Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution

/-!
# Controls for scoped equation orientations

These declarations exercise scope-level execution. They distinguish ambient
variables from a new local binder, exchange occurrence addresses in the reverse
orientation, and extrude a component only when it is independent of the moved
binder. The final controls expose literal-index validation and noninvertible
occurrence substitutions as separate boundaries.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedEquationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution

set_option autoImplicit false

def ambientBinderEquation : Equation where
  name := "ambient-binder"
  typeContext := [("X", .proc)]
  premises := []
  left := .apply "Box" [.fvar "X"]
  right := .lambda none (.fvar "X")
  bindings := some { dependencies := [("X", [])] }

def wrappedBinderEquation : Equation where
  name := "wrapped-binder"
  typeContext := [("X", .proc)]
  premises := []
  left := .lambda none (.fvar "X")
  right := .apply "Box" [.lambda none (.fvar "X")]
  bindings := some {
    dependencies := [("X", [.proc])]
    occurrences :=
      [{ name := "X", site := .left, path := [0], arguments := [.bvar 0] },
       { name := "X", site := .right, path := [0, 0], arguments := [.bvar 0] }] }

def extrusionEquation : Equation where
  name := "binder-extrusion"
  typeContext := [("P", .proc), ("Q", .proc)]
  premises := []
  left := .apply "Nu" [.lambda none (.apply "Pair" [.fvar "P", .fvar "Q"])]
  right := .apply "Pair" [.apply "Nu" [.lambda none (.fvar "P")], .fvar "Q"]
  bindings := some {
    dependencies := [("P", [.proc]), ("Q", [])]
    occurrences :=
      [{ name := "P", site := .left, path := [0, 0, 0], arguments := [.bvar 0] },
       { name := "Q", site := .left, path := [0, 0, 1], arguments := [] },
       { name := "P", site := .right, path := [0, 0, 0], arguments := [.bvar 0] },
       { name := "Q", site := .right, path := [1], arguments := [] }] }

def literalEscapeEquation : Equation where
  name := "literal-escape"
  typeContext := []
  premises := []
  left := .apply "Atom" []
  right := .bvar 0
  bindings := some { dependencies := [] }

def constantSpineEquation : Equation where
  name := "constant-spine"
  typeContext := [("X", .proc)]
  premises := []
  left := .lambda none (.fvar "X")
  right := .lambda none (.fvar "X")
  bindings := some {
    dependencies := [("X", [.proc])]
    occurrences :=
      [{ name := "X", site := .left, path := [0], arguments := [.bvar 0] },
       { name := "X", site := .right, path := [0],
         arguments := [.apply "Atom" []] }] }

def language : LanguageDef where
  name := "ScopedEquationControls"
  types := ["Proc"]
  terms := []
  equations := [ambientBinderEquation, wrappedBinderEquation, extrusionEquation]
  rewrites := []

/-- A dependency-free capture retains its ambient variable beneath the new
binder. -/
theorem forward_binder_keeps_ambient_variable :
    applyEquationAt language 1 ambientBinderEquation .forward
      (.apply "Box" [.bvar 0]) = [.lambda none (.bvar 1)] := by
  decide +kernel

/-- Matching the opposite side recovers the original ambient variable. -/
theorem reverse_binder_recovers_ambient_variable :
    applyEquationAt language 1 ambientBinderEquation .reverse
      (.lambda none (.bvar 1)) = [.apply "Box" [.bvar 0]] := by
  decide +kernel

/-- A local binder variable cannot be captured as a dependency-free value. -/
theorem reverse_binder_rejects_local_dependency :
    applyEquationAt language 1 ambientBinderEquation .reverse
      (.lambda none (.bvar 0)) = [] := by
  decide +kernel

/-- The forward side supplies its declared one-variable spine. -/
theorem forward_wrapped_binder :
    applyEquationAt language 0 wrappedBinderEquation .forward
      (.lambda none (.bvar 0)) = [.apply "Box" [.lambda none (.bvar 0)]] := by
  decide +kernel

/-- Reversing changes the occurrence address from `[0, 0]` to `[0]`. -/
theorem reverse_wrapped_binder :
    applyEquationAt language 0 wrappedBinderEquation .reverse
      (.apply "Box" [.lambda none (.bvar 0)]) = [.lambda none (.bvar 0)] := by
  decide +kernel

/-- Swapping only the endpoint patterns leaves stale occurrence addresses and
cannot execute the reverse instance. -/
theorem unchanged_occurrence_sites_reject_reverse :
    applyRuleAt RelationEnv.empty language 0
      { orientedRule wrappedBinderEquation .reverse with
        bindings := wrappedBinderEquation.bindings }
      (.apply "Box" [.lambda none (.bvar 0)]) = [] := by
  decide +kernel

def extrusionSource : Pattern :=
  .apply "Nu" [.lambda none (.apply "Pair"
    [.apply "Out" [.bvar 0, .bvar 1], .apply "Out" [.bvar 1, .bvar 1]])]

def extrusionTarget : Pattern :=
  .apply "Pair"
    [.apply "Nu" [.lambda none (.apply "Out" [.bvar 0, .bvar 1])],
     .apply "Out" [.bvar 0, .bvar 0]]

/-- Removing the local binder from an independent component lowers only its
ambient indices. The component retained under restriction keeps both indices. -/
theorem extrusion_preserves_the_two_contexts :
    applyEquationAt language 1 extrusionEquation .forward extrusionSource =
      [extrusionTarget] := by
  decide +kernel

/-- The opposite orientation restores the binder and raises the independent
component's ambient indices. -/
theorem extrusion_reverse_restores_the_two_contexts :
    applyEquationAt language 1 extrusionEquation .reverse extrusionTarget =
      [extrusionSource] := by
  decide +kernel

/-- A component mentioning the moved local binder is rejected rather than
emitted with a dangling or captured index. -/
theorem dependent_component_cannot_be_extruded :
    applyEquationAt language 1 extrusionEquation .forward
      (.apply "Nu" [.lambda none (.apply "Pair"
        [.apply "Out" [.bvar 0, .bvar 1], .apply "Out" [.bvar 0, .bvar 1]])]) = [] := by
  decide +kernel

/-- Binding admission does not alone validate literal indices elsewhere in
the authored schema. The endpoint gate rejects the escaping literal. -/
theorem literal_index_requires_endpoint_scope :
    admittedFor (orientedRule literalEscapeEquation .forward)
      { dependencies := [] } = true ∧
    applyRuleAt RelationEnv.empty language 0
      (orientedRule literalEscapeEquation .forward) (.apply "Atom" []) = [.bvar 0] ∧
    applyEquationAt language 0 literalEscapeEquation .forward (.apply "Atom" []) = [] := by
  decide +kernel

/-- A general output substitution is executable in its authored direction. -/
theorem constant_output_spine_executes :
    applyEquationAt language 0 constantSpineEquation .forward
      (.lambda none (.bvar 0)) = [.lambda none (.apply "Atom" [])] := by
  decide +kernel

/-- Its nonvariable input spine is not invertible by the declared matcher. -/
theorem constant_input_spine_does_not_claim_an_inverse :
    applyEquationAt language 0 constantSpineEquation .reverse
      (.lambda none (.apply "Atom" [])) = [] := by
  decide +kernel

/-- Equation enumeration consumes the actual declared list, including both
orientations, without manufacturing a language rewrite. -/
theorem declared_equation_enumeration_keeps_the_ambient_variable :
    equationResultsAt language 1 (.apply "Box" [.bvar 0]) =
      [.lambda none (.bvar 1)] := by
  decide +kernel

/-- Repeated declarations retain their separate equation occurrences. -/
theorem duplicate_equations_retain_multiplicity :
    equationResultsAt
      { language with equations := [ambientBinderEquation, ambientBinderEquation] }
      1 (.apply "Box" [.bvar 0]) =
        [.lambda none (.bvar 1), .lambda none (.bvar 1)] := by
  decide +kernel

end Mettapedia.OSLF.MeTTaIL.ScopedEquationControls
