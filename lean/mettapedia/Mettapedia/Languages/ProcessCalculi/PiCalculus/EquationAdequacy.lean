import Mettapedia.Languages.ProcessCalculi.PiCalculus.AtomicFragment
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.GSLT.LanguageDef.BagEquationDecision
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence

/-!
# Exact scope of the authored pi static theory

The declared parallel monoid has a complete normal-form comparison on named
processes. Textbook restriction laws and guarded replication unfolding are
strictly additional equations: the controls below give structurally congruent
named processes with distinct declared normal forms. A canonical section for
the monoid therefore cannot be reused as a section for those larger quotients.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.EquationSemantics

theorem piToPattern_admissible (process : Process) :
    Admissible piCalc piNameContext [] (.base "Proc") (piToPattern process) :=
  ⟨piToPattern_hasType process, (piToPattern_atomic process).canonical,
    (piToPattern_atomic process).object⟩

/-- All and only the actual authored equations are decided by this normal form. -/
theorem pi_equations_iff_normal_form (left right : Process) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern left) (piToPattern right) ↔
    normalForm (some "PiNil") (piToPattern left) =
      normalForm (some "PiNil") (piToPattern right) :=
  equationEquiv_iff_normalForm_eq piBagTheory _
    (piToPattern_admissible left) (piToPattern_admissible right) rfl

def decideNamedEquation (left right : Process) :
    Decidable (EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern left) (piToPattern right)) :=
  decideEquationEquiv piBagTheory _ (piToPattern_admissible left) (piToPattern_admissible right) rfl

/-- Vacuous restriction is a named structural law absent from the monoid quotient. -/
theorem restriction_unit_equation_boundary :
    Nonempty (StructuralCongruence (.nu "a" .nil) .nil) ∧
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (piToPattern (.nu "a" .nil)) (piToPattern .nil) := by
  refine ⟨⟨.nu_nil "a"⟩, ?_⟩
  intro equal
  have normalized := (pi_equations_iff_normal_form _ _).mp equal
  have distinct : normalForm (some "PiNil") (piToPattern (.nu "a" .nil)) ≠
      normalForm (some "PiNil") (piToPattern .nil) := by decide +kernel
  exact distinct normalized

/-- Extrusion preserves the freshness side condition but changes the monoid normal form. -/
theorem scope_extrusion_equation_boundary :
    Nonempty (StructuralCongruence
      (.nu "x" (.par (.output "x" "w") (.output "a" "b")))
      (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) ∧
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (piToPattern (.nu "x" (.par (.output "x" "w") (.output "a" "b"))))
        (piToPattern (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) := by
  refine ⟨⟨.nu_par "x" _ _ (by decide +kernel)⟩, ?_⟩
  intro equal
  have normalized := (pi_equations_iff_normal_form _ _).mp equal
  have distinct : normalForm (some "PiNil")
      (piToPattern (.nu "x" (.par (.output "x" "w") (.output "a" "b")))) ≠
      normalForm (some "PiNil")
        (piToPattern (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) := by
    intro same
    have bag : IsBagNode (normalForm (some "PiNil")
        (piToPattern (.par (.nu "x" (.output "x" "w")) (.output "a" "b")))) := by
      apply normalizeBag_isBagNode_of_length
      simp [bagContents, splice, normalForm, normalFormList, piToPattern]
    rw [← same] at bag
    rcases bag with ⟨elements, impossible⟩
    cases impossible
  exact distinct normalized

theorem restriction_exchange_equation_boundary :
    Nonempty (StructuralCongruence (.nu "x" (.nu "y" (.output "x" "y")))
      (.nu "y" (.nu "x" (.output "x" "y")))) ∧
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (piToPattern (.nu "x" (.nu "y" (.output "x" "y"))))
        (piToPattern (.nu "y" (.nu "x" (.output "x" "y")))) := by
  refine ⟨⟨.nu_swap "x" "y" _⟩, ?_⟩
  intro equal
  have normalized := (pi_equations_iff_normal_form _ _).mp equal
  have distinct : normalForm (some "PiNil")
      (piToPattern (.nu "x" (.nu "y" (.output "x" "y")))) ≠
      normalForm (some "PiNil")
        (piToPattern (.nu "y" (.nu "x" (.output "x" "y")))) := by decide +kernel
  exact distinct normalized

theorem replication_unfold_equation_boundary :
    Nonempty (StructuralCongruence (.replicate "a" "x" .nil)
      (.par (.input "a" "x" .nil) (.replicate "a" "x" .nil))) ∧
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (piToPattern (.replicate "a" "x" .nil))
        (piToPattern (.par (.input "a" "x" .nil) (.replicate "a" "x" .nil))) := by
  refine ⟨⟨.replicate_unfold "a" "x" .nil⟩, ?_⟩
  intro equal
  have normalized := (pi_equations_iff_normal_form _ _).mp equal
  have distinct : normalForm (some "PiNil") (piToPattern (.replicate "a" "x" .nil)) ≠
      normalForm (some "PiNil")
        (piToPattern (.par (.input "a" "x" .nil) (.replicate "a" "x" .nil))) := by
    intro same
    have bag : IsBagNode (normalForm (some "PiNil")
        (piToPattern (.par (.input "a" "x" .nil) (.replicate "a" "x" .nil)))) := by
      apply normalizeBag_isBagNode_of_length
      simp [bagContents, splice, normalForm, normalFormList, piToPattern]
    rw [← same] at bag
    rcases bag with ⟨elements, impossible⟩
    cases impossible
  exact distinct normalized

/-- A full structural-congruence comparison cannot use this monoid section. -/
theorem no_full_structural_equation_comparison :
    ¬ ∀ (left right : Process), Nonempty (StructuralCongruence left right) →
      EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (piToPattern left) (piToPattern right) := by
  intro comparison
  exact restriction_unit_equation_boundary.2
    (comparison _ _ restriction_unit_equation_boundary.1)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
