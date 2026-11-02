import Mettapedia.Languages.ProcessCalculi.PiCalculus.AtomicFragment
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.GSLT.LanguageDef.BagEquationDecision
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence

/-!
# π's parallel fragment, and the restriction laws beyond it

The parallel monoid alone (`piParallelFragment`, the presentation without its authored equations) has a complete
normal-form comparison on named processes. `piCalc` authors the restriction laws on top of it: ν of inaction,
exchange of restrictions and scope extrusion. Each control below gives named processes that are structurally
congruent, that `piCalc` identifies, and that the fragment's normal form separates. Replication unfolding is not an
authored law: guarded replication keeps its server when it communicates.
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

theorem piToPattern_parallel_admissible (process : Process) :
    Admissible piParallelFragment piNameContext [] (.base "Proc") (piToPattern process) :=
  ⟨HasType.of_terms_subset (source := piCalc) (target := piParallelFragment) (fun _ member => member)
      (piToPattern_admissible process).typed,
    (piToPattern_admissible process).canonical, (piToPattern_admissible process).object⟩

/-- **The fragment's static theory is decided by the bag normal form.** -/
theorem piParallel_equations_iff_normal_form (left right : Process) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment
      (piToPattern left) (piToPattern right) ↔
    normalForm (some "PiNil") (piToPattern left) =
      normalForm (some "PiNil") (piToPattern right) :=
  equationEquiv_iff_normalForm_eq (piParallelBagTheory.asBare rfl) _
    (piToPattern_parallel_admissible left) (piToPattern_parallel_admissible right) rfl

def decideParallelEquation (left right : Process) :
    Decidable (EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment
      (piToPattern left) (piToPattern right)) :=
  decideEquationEquiv (piParallelBagTheory.asBare rfl) _ (piToPattern_parallel_admissible left)
    (piToPattern_parallel_admissible right) rfl

/-! ## The restriction laws are laws of `piCalc` -/

theorem restrictionNil_member : restrictionNil ∈ piCalc.equations := List.Mem.head _

theorem restrictionExchange_member : restrictionExchange ∈ piCalc.equations :=
  List.Mem.tail _ (List.Mem.head _)

theorem scopeExtrusion_member : scopeExtrusion ∈ piCalc.equations :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- **`(νa) 0 = 0` in `piCalc`.** -/
theorem restriction_unit_equivalent :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc (piToPattern (.nu "a" .nil)) (piToPattern .nil) :=
  equationInstance_equivalent ⟨0, .forward (initialBindings := []) (finalBindings := []) restrictionNil_member
    (readsRaw_of_none rfl) (by decide +kernel) (.nil _) (by simp [restrictionNil, Mettapedia.OSLF.MeTTaIL.Match.applyBindings, piToPattern])⟩

/-- **Scope extrusion in `piCalc`**: `(νx)(x⟨w⟩ | a⟨b⟩) = (νx) x⟨w⟩ | a⟨b⟩`. -/
theorem scope_extrusion_equivalent :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern (.nu "x" (.par (.output "x" "w") (.output "a" "b"))))
      (piToPattern (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) :=
  equationInstance_equivalent ⟨0, .declared (orientation := .reverse) (ambient := 0) scopeExtrusion_member
    (by decide +kernel) (declaredInstanceAt_of_applyEquationAt (by decide +kernel))⟩

/-- **Exchange of restrictions in `piCalc`**: `(νx)(νy) x⟨y⟩ = (νy)(νx) x⟨y⟩`. -/
theorem restriction_exchange_equivalent :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
      (piToPattern (.nu "x" (.nu "y" (.output "x" "y"))))
      (piToPattern (.nu "y" (.nu "x" (.output "x" "y")))) :=
  equationInstance_equivalent ⟨0, .declared (orientation := .forward) (ambient := 0) restrictionExchange_member
    (by decide +kernel) (declaredInstanceAt_of_applyEquationAt (by decide +kernel))⟩

/-! ## The fragment separates them -/

/-- Vacuous restriction is a structural law absent from the parallel fragment. -/
theorem restriction_unit_equation_boundary :
    Nonempty (StructuralCongruence (.nu "a" .nil) .nil) ∧
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment
        (piToPattern (.nu "a" .nil)) (piToPattern .nil) := by
  refine ⟨⟨.nu_nil "a"⟩, ?_⟩
  intro equal
  have normalized := (piParallel_equations_iff_normal_form _ _).mp equal
  have distinct : normalForm (some "PiNil") (piToPattern (.nu "a" .nil)) ≠
      normalForm (some "PiNil") (piToPattern .nil) := by decide +kernel
  exact distinct normalized

/-- Extrusion preserves the freshness side condition but changes the fragment's normal form. -/
theorem scope_extrusion_equation_boundary :
    Nonempty (StructuralCongruence
      (.nu "x" (.par (.output "x" "w") (.output "a" "b")))
      (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) ∧
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment
        (piToPattern (.nu "x" (.par (.output "x" "w") (.output "a" "b"))))
        (piToPattern (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) := by
  refine ⟨⟨.nu_par "x" _ _ (by decide +kernel)⟩, ?_⟩
  intro equal
  have normalized := (piParallel_equations_iff_normal_form _ _).mp equal
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
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment
        (piToPattern (.nu "x" (.nu "y" (.output "x" "y"))))
        (piToPattern (.nu "y" (.nu "x" (.output "x" "y")))) := by
  refine ⟨⟨.nu_swap "x" "y" _⟩, ?_⟩
  intro equal
  have normalized := (piParallel_equations_iff_normal_form _ _).mp equal
  have distinct : normalForm (some "PiNil")
      (piToPattern (.nu "x" (.nu "y" (.output "x" "y")))) ≠
      normalForm (some "PiNil")
        (piToPattern (.nu "y" (.nu "x" (.output "x" "y")))) := by decide +kernel
  exact distinct normalized

theorem replication_unfold_equation_boundary :
    Nonempty (StructuralCongruence (.replicate "a" "x" .nil)
      (.par (.input "a" "x" .nil) (.replicate "a" "x" .nil))) ∧
      ¬ EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment
        (piToPattern (.replicate "a" "x" .nil))
        (piToPattern (.par (.input "a" "x" .nil) (.replicate "a" "x" .nil))) := by
  refine ⟨⟨.replicate_unfold "a" "x" .nil⟩, ?_⟩
  intro equal
  have normalized := (piParallel_equations_iff_normal_form _ _).mp equal
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

/-- The parallel fragment does not capture structural congruence. -/
theorem no_full_structural_equation_comparison :
    ¬ ∀ (left right : Process), Nonempty (StructuralCongruence left right) →
      EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment
        (piToPattern left) (piToPattern right) := by
  intro comparison
  exact restriction_unit_equation_boundary.2
    (comparison _ _ restriction_unit_equation_boundary.1)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
