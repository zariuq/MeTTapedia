import Mettapedia.OSLF.Syntax.RhoScopedEventPresheaf
import Mettapedia.OSLF.Syntax.SyntacticRetractionEventAbsence
import Mettapedia.OSLF.Syntax.RhoScopedParallelReactiveSystem

/-!
# Native reaction guards for the original scoped rho graph

Positive support uses actual original source fibres. Full native negation
excludes reactions after every syntactic substitution. Over the explicitly
restricted category of retractable futures it agrees with current reaction
absence. This does not assert stability under arbitrary substitutions or
under adjoining parallel components.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedNativeAbsence

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres
open RhoScopedParallelEvents RhoScopedEventPresheaf
open SyntacticRetractionContexts SyntacticRetractionEventAbsence
open Mettapedia.GSLT.Topos.PresheafEventAbsence

def Enabled {context : Ctx sig} (admitted : SourceRule → Prop) (process : Process context) : Prop :=
  ∃ result, RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := admitted) process result

theorem enabled_substitution {context destination : Ctx sig}
    (admitted : SourceRule → Prop) (change : Sub sig context destination)
    {process : Process context} (holds : Enabled admitted process) :
    Enabled admitted (bindQ change process) := by
  obtain ⟨result, step⟩ := holds
  exact ⟨bindQ change result, step_substitution change step⟩

def present (admitted : SourceRule → Prop) : Subfunctor (terms .pr) :=
  enabled (source admitted) ⊤

noncomputable def absentAtAllFutures (admitted : SourceRule → Prop) : Subfunctor (terms .pr) :=
  absent (source admitted) ⊤

theorem present_iff_enabled (admitted : SourceRule → Prop)
    (world : (Syntactic.Ctxt sig)ᵒᵖ) (process : Process world.unop.vars) :
    process ∈ (present admitted).obj world ↔ Enabled admitted process := by
  have comparison := mem_enabled (source admitted) ⊤ world process
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and] at comparison
  exact comparison.trans (source_fibre_iff_step admitted world process)

theorem full_absence_iff_future (admitted : SourceRule → Prop)
    (world : (Syntactic.Ctxt sig)ᵒᵖ) (process : Process world.unop.vars) :
    process ∈ (absentAtAllFutures admitted).obj world ↔
      ∀ (future : (Syntactic.Ctxt sig)ᵒᵖ) (change : world ⟶ future),
        ¬ Enabled admitted (bindQ change.unop process) := by
  have comparison := mem_absent (source admitted) ⊤ world process
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and] at comparison
  exact comparison.trans (forall_congr' (fun future => forall_congr' (fun change =>
    not_congr (source_fibre_iff_step admitted future (bindQ change.unop process)))))

def permittedPresent (admitted : SourceRule → Prop) : Subfunctor (restrict (terms .pr)) :=
  enabled (restrictSource (source admitted)) ⊤

noncomputable def permittedAbsent (admitted : SourceRule → Prop) :
    Subfunctor (restrict (terms .pr)) :=
  absent (restrictSource (source admitted)) ⊤

theorem permitted_absence_iff_current (admitted : SourceRule → Prop)
    (world : (Object sig)ᵒᵖ) (process : Process world.unop.context.vars) :
    process ∈ (permittedAbsent admitted).obj world ↔ ¬ Enabled admitted process := by
  exact (native_absence_iff_present (source admitted) world process).trans
    (not_congr (source_fibre_iff_step admitted (Opposite.op world.unop.context) process))

theorem permitted_enabled_iff (admitted : SourceRule → Prop)
    {world future : (Object sig)ᵒᵖ} (change : world ⟶ future)
    (process : Process world.unop.context.vars) :
    Enabled admitted (bindQ change.unop.val process) ↔ Enabled admitted process := by
  constructor
  · intro holds
    have native := (permitted_absence_iff_current admitted world process).mpr
    by_contra missing
    have absentFuture := (permittedAbsent admitted).map change (native missing)
    exact (permitted_absence_iff_current admitted future _).mp absentFuture holds
  · exact enabled_substitution admitted change.unop.val

theorem permitted_no_identity_labelled_reaction (admitted : SourceRule → Prop)
    (world : (Object sig)ᵒᵖ) (process : Process world.unop.context.vars) :
    process ∈ (permittedAbsent admitted).obj world ↔
      ¬ ∃ result, Mettapedia.GSLT.RedexRelativeCongruence.ActIPO
        (RhoScopedParallelReactiveSystem.reactionRules sourceRules admitted)
        (𝟙 (RhoScopedParallelContexts.interface world.unop.context.vars))
        (RhoScopedParallelContexts.arrow process)
        (RhoScopedParallelContexts.arrow result) := by
  rw [permitted_absence_iff_current]
  apply not_congr
  exact exists_congr (fun result => RhoScopedParallelReactiveSystem.step_iff_actIPO_identity _ _)

end Mettapedia.OSLF.Binding.RhoScopedNativeAbsence
