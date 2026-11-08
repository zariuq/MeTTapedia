import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersUnmatched
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramUnmatched

/-!
# The two program hosts agree on first-order rows

The program core runs on two hosts: the first-order equation core (`ProgramEquations.EqStep`, with
R95's unmatched calls as values) and the binder-bearing core on the contextual step
(`ProgramBinders`, with R100's absence check). `ProgramBindersFirstOrder` embeds first-order rows
(`encSx`, `encPat`) and joins the cores' rewriting on ground rows (`step_join`, `execution_join`).
This module joins their absence checks.

* **Matching agrees** (`matches_iff`): a translated left-hand side matches an embedded call exactly
  when the first-order pattern matches the row.
* **R100's absence is first-order non-matching** (`unmatched_iff_firstOrder`), and so is **R95's**
  (`matchedBy_false_iff`): its test, renamed-apart unification against the embedded row, sees no
  equation exactly when no pattern matches the row.
* **The two absence checks are one** (`absence_agrees`): for programs with the same left-hand sides,
  R100's `Unmatched` at an embedded call holds exactly when R95's query test `matchedBy` is false at
  the embedded row.
* **And so are the return firings' admissions at an embedded call** (`return_admitted_iff`): R100's
  return firing at the initial state of an embedded call is admitted exactly when R95's test is
  false there.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramHosts

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (Subst Unifies)
open ProgramRows (Sx Pat embed apply_embed apply_at match_at embed_bounded)
open ProgramBinders (Matches Unmatched)
open ProgramBinders.FirstOrder (encSx encPat translate foProgram encPat_inversion instantiate_encPat)

/-! ## Matching -/

/-- **Matching agrees**: the translated left-hand side matches an embedded call exactly when the
first-order pattern matches the row. -/
theorem matches_iff (e : ProgramEquations.Equation) (s : Sx) :
    (∃ θ, Matches (translate e) (encSx s) θ) ↔ ∃ θ : ℕ → Sx, e.lhs.inst θ = s := by
  constructor
  · rintro ⟨solution, matched⟩
    obtain ⟨θ, _, read⟩ := encPat_inversion _ e.lhs s matched
    exact ⟨θ, read⟩
  · rintro ⟨θ, matched⟩
    refine ⟨fun x => encSx (θ x), ?_⟩
    have read := instantiate_encPat ((translate e).assign (fun x => encSx (θ x)) (ProgramBinders.ground _)) θ e.lhs
      (fun _ _ => rfl)
    rw [matched] at read
    exact read

/-- **R100's absence at an embedded call is first-order non-matching.** -/
theorem unmatched_iff_firstOrder (prog : ProgramEquations.Program) (s : Sx) :
    Unmatched (foProgram prog) (encSx s) ↔ ∀ e ∈ prog, ∀ θ : ℕ → Sx, e.lhs.inst θ ≠ s := by
  constructor
  · intro unmatched e member θ matched
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    obtain ⟨solution, found⟩ := (matches_iff (prog.get index) s).mpr ⟨θ, matched⟩
    exact unmatched index solution found
  · intro none index solution matched
    obtain ⟨θ, read⟩ := (matches_iff (prog.get index) s).mp ⟨solution, matched⟩
    exact none _ (List.get_mem prog index) θ read

/-! ## R95's test at an embedded row -/

/-- **Unification against an embedded row is matching.** -/
theorem unifies_embed_iff (p : Pat) (s : Sx) (n : ℕ) :
    (∃ δ : Subst ProgramRows.rows, Unifies δ [(p.at n, embed s)]) ↔ ∃ θ : ℕ → Sx, p.inst θ = s := by
  constructor
  · rintro ⟨δ, unifies⟩
    have solved : δ.applyTerm (p.at n) = embed s := by
      have h := unifies _ (List.mem_singleton_self _)
      rw [apply_embed] at h
      exact h
    exact ⟨_, (match_at p solved).1⟩
  · rintro ⟨θ, matched⟩
    refine ⟨fun v => if v.1 = n then embed (θ v.2) else .var v, fun q member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    show Subst.applyTerm _ (p.at n) = Subst.applyTerm _ (embed s)
    rw [apply_embed, apply_at p (θ := θ) (fun x _ => by simp), matched]

/-- **R95's test sees nothing at an embedded row exactly when no pattern matches it.** -/
theorem matchedBy_false_iff (eqs : List ProgramNested.NEquation) (s : Sx) :
    ProgramNested.matchedBy eqs (embed s) = false ↔ ∀ e ∈ eqs, ∀ θ : ℕ → Sx, e.lhs.inst θ ≠ s := by
  rw [ProgramNested.unmatched_iff (embed_bounded 0 s)]
  constructor
  · intro none e member θ matched
    obtain ⟨δ, unifies⟩ := (unifies_embed_iff e.lhs s 0).mpr ⟨θ, matched⟩
    exact none e member δ unifies
  · intro none e member δ unifies
    obtain ⟨θ, matched⟩ := (unifies_embed_iff e.lhs s 0).mp ⟨δ, unifies⟩
    exact none e member θ matched

/-! ## The agreement -/

/-- **The two absence checks are one on first-order rows**: for programs with the same left-hand
sides, R100's `Unmatched` at an embedded call is R95's query test being false at the embedded row. -/
theorem absence_agrees (prog : ProgramEquations.Program) (eqs : List ProgramNested.NEquation)
    (sameLhs : eqs.map ProgramNested.NEquation.lhs = prog.map ProgramEquations.Equation.lhs) (s : Sx) :
    Unmatched (foProgram prog) (encSx s) ↔ ProgramNested.matchedBy eqs (embed s) = false := by
  rw [unmatched_iff_firstOrder, matchedBy_false_iff]
  have left : (∀ e ∈ prog, ∀ θ : ℕ → Sx, e.lhs.inst θ ≠ s) ↔
      ∀ p ∈ prog.map ProgramEquations.Equation.lhs, ∀ θ : ℕ → Sx, p.inst θ ≠ s := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  have right : (∀ e ∈ eqs, ∀ θ : ℕ → Sx, e.lhs.inst θ ≠ s) ↔
      ∀ p ∈ eqs.map ProgramNested.NEquation.lhs, ∀ θ : ℕ → Sx, p.inst θ ≠ s := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [left, right, sameLhs]

/-- **The return firings agree at an embedded call**: R100's return firing at the initial state of
an embedded call is admitted exactly when R95's test is false at the embedded row. -/
theorem return_admitted_iff (prog : ProgramEquations.Program) (eqs : List ProgramNested.NEquation)
    (sameLhs : eqs.map ProgramNested.NEquation.lhs = prog.map ProgramEquations.Equation.lhs) (s : Sx) :
    ProgramBinders.UnmatchedAdmitted (foProgram prog) (ProgramBinders.initial (encSx s)) ↔
      ProgramNested.matchedBy eqs (embed s) = false :=
  (ProgramBinders.returns_iff _ (encSx s) (ProgramBinders.initial_determines _)).trans
    (absence_agrees prog eqs sameLhs s)

#print axioms matches_iff
#print axioms unmatched_iff_firstOrder
#print axioms unifies_embed_iff
#print axioms matchedBy_false_iff
#print axioms absence_agrees
#print axioms return_admitted_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramHosts
