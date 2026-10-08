import Mettapedia.TypeTheory.ContextualPredicateCapabilities

/-!
# Guarded context maps from local assumption capabilities

The assumption inclusion has a true pulled guard. Every actual arrow into
an assumed context therefore carries its complete guard, and a guarded map
factors uniquely through that inclusion. The factorization commutes with
precomposition; it does not choose any data witness from existential truth.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateAssumptions

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities

universe c s t m p
variable {C : Cwf.{c, s, t, m}}
variable {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
variable (assumptions : AssumptionOperations doctrine)

@[simp] theorem inclusion_guard {context : C.Ctx} (predicate : doctrine.Predicate context) :
    doctrine.reindex (assumptions.inclusion predicate) predicate = ⊤ :=
  (assumptions.consequence predicate predicate).mpr le_rfl

theorem arrow_guard {source target : C.Ctx} (predicate : doctrine.Predicate target)
    (substitution : C.Sub source (assumptions.assumed target predicate)) :
    doctrine.reindex (C.compS (assumptions.inclusion predicate) substitution) predicate = ⊤ := by
  rw [doctrine.reindex_comp, inclusion_guard]
  exact map_top (doctrine.reindex substitution)

@[simp] theorem select_eta {source target : C.Ctx} (predicate : doctrine.Predicate target)
    (substitution : C.Sub source (assumptions.assumed target predicate)) :
    assumptions.select predicate (C.compS (assumptions.inclusion predicate) substitution)
      (arrow_guard assumptions predicate substitution) = substitution :=
  assumptions.inclusion_monic predicate _ _ (assumptions.select_beta _ _ _)

theorem select_unique {source target : C.Ctx} (predicate : doctrine.Predicate target)
    (substitution : C.Sub source target) (guard : doctrine.reindex substitution predicate = ⊤)
    (selected : C.Sub source (assumptions.assumed target predicate))
    (projection : C.compS (assumptions.inclusion predicate) selected = substitution) :
    selected = assumptions.select predicate substitution guard :=
  assumptions.inclusion_monic predicate _ _
    (projection.trans (assumptions.select_beta predicate substitution guard).symm)

theorem substituted_guard {source middle target : C.Ctx} (predicate : doctrine.Predicate target)
    (substitution : C.Sub middle target) (guard : doctrine.reindex substitution predicate = ⊤)
    (earlier : C.Sub source middle) :
    doctrine.reindex (C.compS substitution earlier) predicate = ⊤ := by
  rw [doctrine.reindex_comp, guard]
  exact map_top (doctrine.reindex earlier)

theorem select_precomposition {source middle target : C.Ctx} (predicate : doctrine.Predicate target)
    (substitution : C.Sub middle target) (guard : doctrine.reindex substitution predicate = ⊤)
    (earlier : C.Sub source middle) :
    C.compS (assumptions.select predicate substitution guard) earlier =
      assumptions.select predicate (C.compS substitution earlier)
        (substituted_guard predicate substitution guard earlier) := by
  apply select_unique assumptions
  rw [← C.comp_assoc, assumptions.select_beta]

/-- Conditional consequence is applied only after its antecedent guard has
been earned along the supplied map. -/
theorem consequence_apply {source target : C.Ctx}
    (antecedent consequent : doctrine.Predicate target) (below : antecedent ≤ consequent)
    (substitution : C.Sub source target) (guard : doctrine.reindex substitution antecedent = ⊤) :
    doctrine.reindex substitution consequent = ⊤ := by
  apply le_antisymm le_top
  rw [← guard]
  exact OrderHomClass.mono (doctrine.reindex substitution) below

/-- No type-valued witness is recovered from this logical image equality. -/
theorem universal_truth_iff {context : C.Ctx} (type : C.Ty context)
    (body : doctrine.Predicate (C.ext context type)) :
    doctrine.all type body = ⊤ ↔ body = ⊤ := by
  rw [eq_top_iff, ← doctrine.all_adjunction, map_top, top_le_iff]

end Mettapedia.TypeTheory.ContextualPredicateAssumptions
