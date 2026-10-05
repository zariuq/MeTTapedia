import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.OSLF.MeTTaIL.NameSubstitutionLaws

/-!
# Named pi binding and the authored locally nameless presentation

The translation preserves free names and local scope. Capture-avoiding
substitution commutes with translation, and the binder-eliminating operation
of the authored communication rule returns the translated named reduct.
Alpha conversion preserves the same pattern even with shadowing binders.

These are binding and contraction comparisons. Context closure and structural
congruence still require their own comparison with the authored rule/equation
presentation.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

private theorem parts_applySubst (P : Pattern) (y z : String)
    (normal : noExplicitSubst P = true) :
    piComponents (applySubst [(y, .fvar z)] P) =
      (piComponents P).map (applySubst [(y, .fvar z)]) := by
  cases P with
  | bvar _ | apply _ _ | lambda _ _ | multiLambda _ _ _ =>
      simp only [piComponents, applySubst, List.map_cons, List.map_nil]
  | fvar name => simp only [piComponents, List.map_cons, List.map_nil, applySubst_fvar_single]
  | subst _ _ => exact absurd normal Bool.false_ne_true
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp only [applySubst, piComponents, List.map_cons, List.map_nil]

private theorem applySubst_piPar (P Q : Pattern) (y z : String)
    (normalP : noExplicitSubst P = true) (normalQ : noExplicitSubst Q = true) :
    applySubst [(y, .fvar z)] (piPar P Q) =
      piPar (applySubst [(y, .fvar z)] P) (applySubst [(y, .fvar z)] Q) := by
  simp only [piPar_components, applySubst, List.map_append,
    parts_applySubst P y z normalP, parts_applySubst Q y z normalQ]

private theorem freeVars_piPar (P Q : Pattern) (name : String) :
    name ∈ freeVars (piPar P Q) ↔ name ∈ freeVars P ∨ name ∈ freeVars Q := by
  unfold piPar
  split <;> simp [freeVars, List.mem_append]

private theorem allNoExplicitSubst_append {ps qs : List Pattern}
    (hp : allNoExplicitSubst ps = true) (hq : allNoExplicitSubst qs = true) :
    allNoExplicitSubst (ps ++ qs) = true := by
  induction ps with
  | nil => exact hq
  | cons p ps ih =>
      simp only [allNoExplicitSubst, Bool.and_eq_true] at hp
      simpa only [List.cons_append, allNoExplicitSubst, hp.1, Bool.true_and] using ih hp.2

private theorem noExplicitSubst_piPar {P Q : Pattern}
    (hp : noExplicitSubst P = true) (hq : noExplicitSubst Q = true) :
    noExplicitSubst (piPar P Q) = true := by
  unfold piPar
  split
  · exact allNoExplicitSubst_append hp hq
  · exact allNoExplicitSubst_append hp (by simp only [allNoExplicitSubst, hq, Bool.true_and])
  · simpa only [noExplicitSubst, allNoExplicitSubst, hp, Bool.true_and] using hq
  · simp only [noExplicitSubst, allNoExplicitSubst, hp, hq, Bool.true_and]

theorem piToPattern_noExplicitSubst (P : Process) : noExplicitSubst (piToPattern P) = true := by
  induction P with
  | nil | output => rfl
  | par P Q ihP ihQ => exact noExplicitSubst_piPar ihP ihQ
  | input x w P ih | replicate x w P ih =>
      simp only [piToPattern, noExplicitSubst, allNoExplicitSubst, Bool.true_and, Bool.and_true]
      exact noExplicitSubst_closeFVar ih
  | nu w P ih =>
      simp only [piToPattern, noExplicitSubst, allNoExplicitSubst, Bool.and_true]
      exact noExplicitSubst_closeFVar ih

theorem freeVars_piToPattern (P : Process) (name : String) :
    name ∈ freeVars (piToPattern P) ↔ name ∈ P.freeNames := by
  induction P with
  | nil => simp [piToPattern, freeVars, Process.freeNames]
  | par P Q ihP ihQ =>
      simp only [piToPattern, freeVars_piPar, Process.freeNames, Finset.mem_union, ihP, ihQ]
  | input x w P ih | replicate x w P ih =>
      simp only [piToPattern, freeVars, List.flatMap_cons, List.flatMap_nil,
        List.mem_append, List.mem_singleton, List.mem_nil_iff, or_false,
        freeVars_closeFVar_iff, ih, Process.freeNames, Finset.mem_insert,
        Finset.mem_sdiff, Finset.mem_singleton]
      tauto
  | output x w => simp [piToPattern, freeVars, Process.freeNames]
  | nu w P ih =>
      simp only [piToPattern, freeVars, List.flatMap_cons, List.flatMap_nil,
        List.mem_append, List.mem_nil_iff, or_false, freeVars_closeFVar_iff,
        ih, Process.freeNames, Finset.mem_sdiff, Finset.mem_singleton]
      tauto

/-- Renaming to a name disjoint from all binders agrees with free-name substitution. -/
theorem piToPattern_renameFree (P : Process) (y z : Name)
    (fresh : z ∉ P.boundNames) :
    piToPattern (P.renameFree y z) = applySubst [(y, .fvar z)] (piToPattern P) := by
  induction P with
  | nil => simp [Process.renameFree, piToPattern, applySubst]
  | par P Q ihP ihQ =>
      have freshP : z ∉ P.boundNames := fun member => fresh (Finset.mem_union_left _ member)
      have freshQ : z ∉ Q.boundNames := fun member => fresh (Finset.mem_union_right _ member)
      rw [Process.renameFree, piToPattern, piToPattern,
        applySubst_piPar _ _ y z (piToPattern_noExplicitSubst P) (piToPattern_noExplicitSubst Q),
        ihP freshP, ihQ freshQ]
  | input x w P ih | replicate x w P ih =>
      have freshBody : z ∉ P.boundNames := fun member => fresh (Finset.mem_insert_of_mem member)
      have wz : w ≠ z := fun same => fresh (same ▸ Finset.mem_insert_self w P.boundNames)
      by_cases wy : w = y
      · subst w
        simp only [Process.renameFree, ite_true, piToPattern, applySubst,
          List.map_cons, List.map_nil, applySubst_fvar_single]
        erw [applySubst_fresh_single (isFresh_closeFVar_self 0 y (piToPattern P))
          (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst P))]
      · simp only [Process.renameFree, if_neg wy, piToPattern, applySubst,
          List.map_cons, List.map_nil, applySubst_fvar_single]
        rw [ih freshBody]
        erw [applySubst_closeFVar_comm_single (Ne.symm wy) (Ne.symm wz)
          (piToPattern_noExplicitSubst P)]
        rfl
  | output x w =>
      simp only [Process.renameFree, piToPattern, applySubst, List.map_cons,
        List.map_nil, applySubst_fvar_single]
  | nu w P ih =>
      have freshBody : z ∉ P.boundNames := fun member => fresh (Finset.mem_insert_of_mem member)
      have wz : w ≠ z := fun same => fresh (same ▸ Finset.mem_insert_self w P.boundNames)
      by_cases wy : w = y
      · subst w
        simp only [Process.renameFree, ite_true, piToPattern, applySubst,
          List.map_cons, List.map_nil]
        erw [applySubst_fresh_single (isFresh_closeFVar_self 0 y (piToPattern P))
          (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst P))]
      · simp only [Process.renameFree, if_neg wy, piToPattern, applySubst,
          List.map_cons, List.map_nil]
        rw [ih freshBody]
        erw [applySubst_closeFVar_comm_single (Ne.symm wy) (Ne.symm wz)
          (piToPattern_noExplicitSubst P)]
        rfl

private theorem subst_closed_absent (P : Process) (y z w : Name)
    (absent : y ∉ P.freeNames) :
    applySubst [(y, .fvar z)] (closeFVar 0 w (piToPattern P)) =
      closeFVar 0 w (piToPattern P) := by
  apply applySubst_fresh_single _ (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst P))
  apply (isFresh_iff_not_mem _ _).mpr
  intro member
  exact absent ((freeVars_piToPattern P y).mp
    ((freeVars_closeFVar_iff (piToPattern P) 0 w y).mp member).2)

private theorem subst_absent (P : Process) (y z : Name) (absent : y ∉ P.freeNames) :
    applySubst [(y, .fvar z)] (piToPattern P) = piToPattern P := by
  apply applySubst_fresh_single _ (piToPattern_noExplicitSubst P)
  apply (isFresh_iff_not_mem _ _).mpr
  exact fun member => absent ((freeVars_piToPattern P y).mp member)

private theorem capture_body_pattern (P : Process) (y z w : Name)
    (different : w ≠ y)
    (ih : piToPattern ((P.renameFree w (P.freshFor y z)).substitute y z) =
      applySubst [(y, .fvar z)] (piToPattern (P.renameFree w (P.freshFor y z)))) :
    closeFVar 0 (P.freshFor y z)
        (piToPattern ((P.renameFree w (P.freshFor y z)).substitute y z)) =
      applySubst [(y, .fvar z)] (closeFVar 0 w (piToPattern P)) := by
  rw [ih, piToPattern_renameFree P w _ (Process.freshFor_not_boundNames P y z)]
  exact closeFVar_applySubst_freshen 0 (Ne.symm different)
    (Ne.symm (Process.freshFor_ne_source P y z))
    (Ne.symm (Process.freshFor_ne_target P y z))
    (fun member => Process.freshFor_not_freeNames P y z
      ((freeVars_piToPattern P _).mp member)) (piToPattern_noExplicitSubst P)

/-- Named capture-avoiding substitution agrees with the locally nameless
operation on every pi process, without a disjoint-binder convention. -/
theorem piToPattern_substitute (P : Process) (y z : Name) :
    piToPattern (P.substitute y z) = applySubst [(y, .fvar z)] (piToPattern P) := by
  fun_induction Process.substitute P y z with
  | case1 y z => simp only [piToPattern, applySubst, List.map_nil]
  | case2 P Q y z ihP ihQ =>
      rw [piToPattern, piToPattern, applySubst_piPar _ _ y z
        (piToPattern_noExplicitSubst P) (piToPattern_noExplicitSubst Q), ihP, ihQ]
  | case3 x P y z | case10 x P y z =>
      simp only [piToPattern, applySubst, List.map_cons, List.map_nil, applySubst_fvar_single]
      erw [applySubst_fresh_single (isFresh_closeFVar_self 0 y (piToPattern P))
        (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst P))]
  | case4 x w P y z different capture fresh ih | case11 x w P y z different capture fresh ih =>
      simp only [piToPattern, applySubst, List.map_cons, List.map_nil, applySubst_fvar_single]
      rw [capture_body_pattern P y z w different ih]
  | case5 x w P y z different noCapture ih | case12 x w P y z different noCapture ih =>
      simp only [piToPattern, applySubst, List.map_cons, List.map_nil, applySubst_fvar_single]
      rw [ih]
      by_cases same : w = z
      · have absent : y ∉ P.freeNames := fun member => noCapture ⟨same, member⟩
        rw [subst_absent P y z absent, subst_closed_absent P y z w absent]
      · erw [applySubst_closeFVar_comm_single (Ne.symm different) (Ne.symm same)
          (piToPattern_noExplicitSubst P)]
        rfl
  | case6 x w y z =>
      simp only [piToPattern, applySubst, List.map_cons, List.map_nil, applySubst_fvar_single]
  | case7 P y z =>
      simp only [piToPattern, applySubst, List.map_cons, List.map_nil]
      erw [applySubst_fresh_single (isFresh_closeFVar_self 0 y (piToPattern P))
        (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst P))]
  | case8 w P y z different capture fresh ih =>
      simp only [piToPattern, applySubst, List.map_cons, List.map_nil]
      rw [capture_body_pattern P y z w different ih]
  | case9 w P y z different noCapture ih =>
      simp only [piToPattern, applySubst, List.map_cons, List.map_nil]
      rw [ih]
      by_cases same : w = z
      · have absent : y ∉ P.freeNames := fun member => noCapture ⟨same, member⟩
        rw [subst_absent P y z absent, subst_closed_absent P y z w absent]
      · erw [applySubst_closeFVar_comm_single (Ne.symm different) (Ne.symm same)
          (piToPattern_noExplicitSubst P)]
        rfl

private theorem lc_at_list_append {ps qs : List Pattern} {k : Nat}
    (hp : lc_at_list k ps = true) (hq : lc_at_list k qs = true) :
    lc_at_list k (ps ++ qs) = true := by
  induction ps with
  | nil => exact hq
  | cons p ps ih =>
      simp only [lc_at_list, Bool.and_eq_true] at hp
      simpa only [List.cons_append, lc_at_list, hp.1, Bool.true_and] using ih hp.2

private theorem lc_at_piPar {P Q : Pattern} {k : Nat}
    (hp : lc_at k P = true) (hq : lc_at k Q = true) : lc_at k (piPar P Q) = true := by
  unfold piPar
  split
  · exact lc_at_list_append hp hq
  · exact lc_at_list_append hp (by simp only [lc_at_list, hq, Bool.true_and])
  · simpa only [lc_at, lc_at_list, hp, Bool.true_and] using hq
  · simp only [lc_at, lc_at_list, hp, hq, Bool.true_and]

/-- Translating a named process introduces no dangling de Bruijn indices. -/
theorem piToPattern_lc (P : Process) : lc_at 0 (piToPattern P) = true := by
  induction P with
  | nil | output => rfl
  | par P Q ihP ihQ => exact lc_at_piPar ihP ihQ
  | input x w P ih | replicate x w P ih =>
      simp only [piToPattern, lc_at, lc_at_list, Bool.true_and, Bool.and_true]
      exact lc_at_closeFVar ih
  | nu w P ih =>
      simp only [piToPattern, lc_at, lc_at_list, Bool.and_true]
      exact lc_at_closeFVar ih

/-- Opening the translated input body performs the named substitution. -/
theorem piToPattern_open_close_substitute (P : Process) (y z : Name) :
    openBVar 0 (.fvar z) (closeFVar 0 y (piToPattern P)) = piToPattern (P.substitute y z) := by
  have substituted := subst_intro (u := .fvar z)
    (isFresh_closeFVar_self 0 y (piToPattern P))
    (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst P))
  rw [open_close_id 0 y (piToPattern P) (piToPattern_lc P)] at substituted
  rw [← substituted]
  exact (piToPattern_substitute P y z).symm

/-- The binder-eliminating operation used by the authored COMM rule agrees
with named capture-avoiding substitution. -/
theorem piToPattern_instantiate_substitute (P : Process) (y z : Name) :
    instantiateBVar (.fvar z) (closeFVar 0 y (piToPattern P)) =
      piToPattern (P.substitute y z) := by
  rw [instantiateBVar_eq_openBVar_of_isWellScoped
    (by rw [isWellScopedAt_eq_lc_at]; exact lc_at_closeFVar (piToPattern_lc P))
    (by rfl)]
  exact piToPattern_open_close_substitute P y z

/-- Alpha conversion preserves binder incidence even when an inner binder
uses the new name. -/
theorem piToPattern_close_substitute_of_fresh (P : Process) (y z : Name)
    (fresh : z ∉ P.freeNames) :
    closeFVar 0 z (piToPattern (P.substitute y z)) = closeFVar 0 y (piToPattern P) := by
  rw [← piToPattern_open_close_substitute]
  apply close_open_id
  intro member
  exact fresh ((freeVars_piToPattern P z).mp
    ((freeVars_closeFVar_iff (piToPattern P) 0 y z).mp member).2)

theorem piToPattern_alpha_input (channel old new : Name) (P : Process)
    (fresh : new ∉ P.freeNames) :
    piToPattern (.input channel old P) =
      piToPattern (.input channel new (P.substitute old new)) := by
  simp only [piToPattern, piToPattern_close_substitute_of_fresh P old new fresh]

theorem piToPattern_alpha_nu (old new : Name) (P : Process)
    (fresh : new ∉ P.freeNames) :
    piToPattern (.nu old P) = piToPattern (.nu new (P.substitute old new)) := by
  simp only [piToPattern, piToPattern_close_substitute_of_fresh P old new fresh]

theorem piToPattern_alpha_replicate (channel old new : Name) (P : Process)
    (fresh : new ∉ P.freeNames) :
    piToPattern (.replicate channel old P) =
      piToPattern (.replicate channel new (P.substitute old new)) := by
  simp only [piToPattern, piToPattern_close_substitute_of_fresh P old new fresh]

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
