import Mettapedia.GSLT.Weighting.Keys
import Mettapedia.OSLF.Formula
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquationDiscipline

/-!
# Keys from the generated logic

Admissible keys lie in the structural fragment of the generated formulas: no
behavioural modality and so modal depth zero. The formula language here has
least fixed points only and no name quantifier, so the structural fragment is
the formulas without a diamond or a box.

Keys read a redex as a term, and a key that reads the shape of a representative
need not respect the equations. In the rho platform the terminated process
equals the name quoting its drop, so a key for "headed by the terminated
process" holds of one and not of the other: classification by head shape is
not well defined on equation classes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.FormulaKeys

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationInvariant)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquationDiscipline

/-! ## The structural fragment -/

/-- The modal depth of a formula: nesting of diamonds and boxes. -/
def modalDepth : OSLFFormula → ℕ
  | .top | .bot | .atom _ | .var _ | .emptyColl _ => 0
  | .and φ ψ | .or φ ψ | .imp φ ψ | .cut _ φ ψ => max (modalDepth φ) (modalDepth ψ)
  | .dia φ | .box φ => modalDepth φ + 1
  | .mu φ | .headed _ φ => modalDepth φ

/-- Formulas without a behavioural modality. -/
def Structural : OSLFFormula → Prop
  | .top | .bot | .atom _ | .var _ | .emptyColl _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ | .cut _ φ ψ => Structural φ ∧ Structural ψ
  | .dia _ | .box _ => False
  | .mu φ | .headed _ φ => Structural φ

/-- **The structural fragment is modal depth zero.** -/
theorem structural_iff_modalDepth_eq_zero : ∀ φ : OSLFFormula, Structural φ ↔ modalDepth φ = 0
  | .top | .bot | .atom _ | .var _ | .emptyColl _ => by simp [Structural, modalDepth]
  | .and φ ψ | .or φ ψ | .imp φ ψ | .cut _ φ ψ => by
      simp [Structural, modalDepth, structural_iff_modalDepth_eq_zero φ,
        structural_iff_modalDepth_eq_zero ψ]
  | .dia _ | .box _ => by simp [Structural, modalDepth]
  | .mu φ | .headed _ φ => by
      simp [Structural, modalDepth, structural_iff_modalDepth_eq_zero φ]

/-- An admissible key in the generated language: structural, and so of local
depth below any bound. Decidability on the terms of interest is supplied with
the key set (`Admissible` in the text). -/
def AdmissibleFormula (bound : ℕ) (φ : OSLFFormula) : Prop :=
  Structural φ ∧ modalDepth φ ≤ bound

theorem admissible_of_structural {φ : OSLFFormula} (structural : Structural φ) (bound : ℕ) :
    AdmissibleFormula bound φ :=
  ⟨structural, (structural_iff_modalDepth_eq_zero φ).mp structural ▸ Nat.zero_le bound⟩

/-- A diamond is not admissible: a rate that depends on what a redex can do next
is not a key. -/
theorem dia_not_admissible (φ : OSLFFormula) (bound : ℕ) :
    ¬ AdmissibleFormula bound (.dia φ) :=
  fun admissible => admissible.1

/-! ## Head-shape keys in the rho platform -/

/-- The key "headed by the terminated process". -/
def stopHeaded (term : Pattern) : Prop := term = stop

theorem stop_ne_quote (inner : Pattern) : stop ≠ .apply quoteLabel [inner] := by
  intro same
  simp [stop, stopDeclaration, quoteLabel] at same

/-- **A head-shape key does not respect the rho platform's equations**: the
terminated process is equal to the name quoting its drop, and the key holds of
the first only. -/
theorem stopHeaded_not_invariant (relEnv : RelationEnv) (arities : List ℕ) :
    ¬ EquationInvariant (langGSLTUsing relEnv (rhoPlatform arities)) stopHeaded := by
  intro invariant
  obtain ⟨inner, equal⟩ := permissive_quote_predicate_is_trivial arities relEnv stop
  exact stop_ne_quote inner ((invariant equal).mp rfl).symm

/-- **So classification by head shape is not well defined on equation
classes** in the rho platform: for any partition of its terms that has the
head-shape key, two equal terms are classified differently. -/
theorem headClassification_not_on_classes (relEnv : RelationEnv) (arities : List ℕ)
    {Key : Type} {keys : Key → Pattern → Prop} (partition : Partition (fun _ => True) keys)
    (key : Key) (isStopKey : keys key = stopHeaded) :
    ¬ ∀ {first second : Subtype fun _ : Pattern => True},
      (langGSLTUsing relEnv (rhoPlatform arities)).Equiv first.val second.val →
        partition.classify first = partition.classify second := by
  intro classes
  apply stopHeaded_not_invariant relEnv arities
  intro first second equal
  have invariant := Partition.keys_invariant_of_classify (langGSLTUsing relEnv (rhoPlatform arities))
    partition classes key (first := ⟨first, trivial⟩) (second := ⟨second, trivial⟩) equal
  rwa [isStopKey] at invariant

end Mettapedia.GSLT.Weighting.FormulaKeys
