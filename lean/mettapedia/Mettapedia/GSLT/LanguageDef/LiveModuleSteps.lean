import Mettapedia.GSLT.LanguageDef.LiveModuleEdits
import Mettapedia.GSLT.LanguageDef.RootRewriting

/-! The maintained literal-key table against the existing GSLT step modulo
equations. This uses the MeTTaIL matcher and the source step, not a second
definition of firing. It applies only when every authored rule is admitted. -/
set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.LiveModuleSteps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open RootRewriting
open EquationSemantics DefinitionalEquations DecidableRelations LiveModuleEdits
open Mettapedia.GSLT.Contracts.ScopedAliasDispatch (RootStep)

private theorem literal_roots (l : LanguageDef) (ok : admitted l = true) : LiteralRoots l := by
  intro r member
  simp only [admitted, Bool.and_eq_true, List.all_eq_true] at ok
  have safe := ok.2 r member
  simp only [literal, Bool.and_eq_true, List.isEmpty_iff, isFirstOrder_iff] at safe
  tauto

/-- The acyclic specialization selects the same rules as the general
equation theory; it does not impose acyclicity on the source step. -/
theorem modulo_step_iff (base : BasePremiseEvaluator) (l : LanguageDef) (ok : admitted l = true)
    (x y : Pattern) : StepModuloEquations base l x y ↔ RootStep base l (·.left) (·.right) l.rewrites x y := by
  rw [literal_root_iff base l (literal_roots l ok)]
  classical
  simp only [RootStep, Contracts.ScopedAliasDispatch.moduloRead, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨r, ⟨authored, source⟩, target⟩
    exact ⟨r, authored, source, target⟩
  · rintro ⟨r, authored, source, target⟩
    exact ⟨r, ⟨authored, source⟩, target⟩

theorem updated_successors_iff {D : Type*} (base : BasePremiseEvaluator) (o : Order)
    (l : LanguageDef) (valid : admitted l = true) (es : List (Edit D)) {out}
    (loaded : run? o l (build l) es = some out) (x y : Pattern) :
    let after := resulting o l es
    expand (definitions after) y ∈ (answers after out x).map (fun r => expand (definitions after) r.right) ↔
      StepModuloEquations base after x y := by
  let after := resulting o l es
  have accepted : admitted after = true := (run_exact o l valid _ rfl es loaded).1
  have checked : checkDefinitional after = true := by
    simp only [admitted, Bool.and_eq_true] at accepted
    exact accepted.1
  have cert := checkDefinitional_sound checked
  have indexed := Contracts.ScopedAliasDispatch.indexed_eq_modulo base cert.acyclic cert.presents
    cert.noBags cert.noSets cert.noAlgebra RewriteRule.left x after.rewrites
  dsimp only
  rw [answers_after_edits base o l valid es loaded x, ← indexed, modulo_step_iff base after accepted]
  exact Contracts.ScopedAliasDispatch.root_successors_iff base cert.acyclic cert.presents
    cert.noBags cert.noSets cert.noAlgebra _ _ _ _ _

end Mettapedia.GSLT.LanguageDef.LiveModuleSteps
