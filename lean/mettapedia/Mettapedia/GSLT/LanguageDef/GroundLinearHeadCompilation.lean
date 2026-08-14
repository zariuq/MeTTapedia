import Mettapedia.GSLT.Core.Composition
import Mettapedia.Languages.MeTTa.LeafPatchViewKernel

/-!
# Ground linear-head compilation

A first-order rule head whose variables occur once can match a ground input by
reading the corresponding input leaves directly.  It need not allocate fresh
rule variables and invoke a general unifier.  This module packages the exact
linearity recognizer and the positional leaf program as a composable
realization.

The theorem is language-neutral.  A generated backend may select this route
only after both the static linearity admission and the dynamic groundness
check succeed.  Nonlinear patterns fail admission and remain on the general
matcher path.
-/

namespace Mettapedia.GSLT.LanguageDef.GroundLinearHeadCompilation

open Mettapedia.Languages.MeTTa.LeafPatchViewKernel

variable {Symbol : Type} [DecidableEq Symbol]

/-- A source head paired with the linearity fact required by positional leaf
matching. -/
structure AdmittedLinearHead (Symbol : Type) [DecidableEq Symbol] where
  source : Pat Symbol
  linear : Linear source

/-- The generated program needs only the variable slots in traversal order.
The rigid skeleton is checked while traversing the ground input. -/
structure LinearHeadPlan where
  variableOrder : List Nat
  deriving DecidableEq, Repr

/-- Decide whether the source head licenses the positional matcher. -/
def admit? (source : Pat Symbol) : Option (AdmittedLinearHead Symbol) :=
  if linear : (vars source).Nodup then
    some { source, linear }
  else
    none

/-- Admission is exactly the source pattern's no-duplicate-slots property. -/
theorem admit?_isSome_iff (source : Pat Symbol) :
    (admit? source).isSome = true ↔ Linear source := by
  simp [admit?, Linear]

/-- Compile an admitted source head to its positional slot program. -/
def compile (source : AdmittedLinearHead Symbol) : LinearHeadPlan :=
  { variableOrder := vars source.source }

/-- Execute the positional program on the ground leaves supplied by an
instantiation environment. -/
def readLeaves (assignment : Nat → Tm Symbol)
    (plan : LinearHeadPlan) : Option (List (Nat × Tm Symbol)) :=
  some ((plan.variableOrder.map fun slot => (slot, assignment slot)).reverse)

/-- The positional program returns exactly the environment produced by the
general matcher on every admitted linear head. -/
theorem readLeaves_eq_match
    (source : AdmittedLinearHead Symbol) (assignment : Nat → Tm Symbol) :
    readLeaves assignment (compile source) =
      matchP source.source (subst assignment source.source) [] := by
  symm
  exact view_eq_match source.source assignment source.linear

/-- Ground linear-head selection as a composable certified realization. -/
def groundLinearHeadRealization :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedLinearHead Symbol) LinearHeadPlan
      ((Nat → Tm Symbol) → Option (List (Nat × Tm Symbol))) where
  compile := fun _ source => compile source
  observeSource := fun _ source assignment =>
    matchP source.source (subst assignment source.source) []
  observeArtifact := fun _ plan assignment => readLeaves assignment plan
  adequate := by
    intro _ source
    funext assignment
    exact readLeaves_eq_match source assignment

/-! ## Positive and negative admission canaries -/

private def nestedLinear : Pat String :=
  .node (.sym "edge") (.node (.var 4) (.var 9))

private def wideLinear : Pat String :=
  .node (.node (.var 0) (.var 1))
    (.node (.var 2) (.node (.var 3) (.var 4)))

private def nonlinear : Pat String :=
  .node (.var 2) (.node (.sym "same") (.var 2))

/-- Structurally different linear heads yield their generated positional
inventories. -/
example :
    (admit? nestedLinear).map compile = some { variableOrder := [4, 9] } ∧
    (admit? wideLinear).map compile =
      some { variableOrder := [0, 1, 2, 3, 4] } := by
  decide

/-- A repeated variable is rejected rather than silently changing equality
constraints into unrelated leaf reads. -/
example : (admit? nonlinear).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.GroundLinearHeadCompilation
