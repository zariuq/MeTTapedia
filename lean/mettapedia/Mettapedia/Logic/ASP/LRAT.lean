import Mettapedia.Logic.ASP.ProgramCNF
import Mettapedia.GSLT.Logic.PropositionalLRATActions

/-!
# LRAT certificates for the Boolean kernel

Mettapedia's `PropositionalLRAT` adapts the verified LRAT checker of Lean's
standard library to native propositional clauses over natural-number variables,
and `PropositionalLRATActions` checks the reverse-unit-propagation fragment
action by action. Both prove that an accepted proof refutes its formula. This
module does not re-prove any LRAT theory; it connects the numbered CNF of
`CNF` to those clauses.

* A numbered literal is the same data as a native propositional literal
  (`CNF.Literal.toLRAT`, a bijection with inverse `CNF.Literal.ofLRAT`), so a
  numbered formula is a native one literal for literal (`CNF.Formula.toLRAT`),
  with the same value under every assignment (`CNF.Formula.sat_toLRAT`).
* An accepted proof, whole (`CNF.Formula.unsat_of_lrat`), as text
  (`CNF.Formula.unsat_of_lratText`) or action by action
  (`CNF.Formula.unsat_of_lratActions`), refutes the numbered formula.

## Certificates for programs

* An accepted proof for the numbered completion and loop nogoods proves that the
  program has no stable model (`Program.not_stable_of_lrat`).
* An accepted proof for the numbered completion alone proves that it has no
  supported model (`Program.not_supported_of_lrat`), hence no stable model.
* The proof may be for any selection of those clauses, in any order
  (`Program.not_stable_of_lrat_subset`, `Program.not_supported_of_lrat_subset`).
* More generally, any list of entailed nogoods over program variables, such as the
  completion nogoods with learned ones, may be refuted
  (`Program.not_stable_of_entailed_lrat`): this is the certificate a solver emits
  for its own learned database.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Mettapedia.GSLT.Logic

universe u

namespace CNF

/-- A numbered literal as a native propositional literal. -/
def Literal.toLRAT (l : CNF.Literal ℕ) : PropositionalFormula.Literal :=
  if l.sign then .pos l.var else .neg l.var

/-- A native propositional literal as a numbered literal. -/
def Literal.ofLRAT : PropositionalFormula.Literal → CNF.Literal ℕ
  | .pos n => ⟨n, true⟩
  | .neg n => ⟨n, false⟩

@[simp] theorem Literal.ofLRAT_toLRAT (l : CNF.Literal ℕ) : Literal.ofLRAT l.toLRAT = l := by
  obtain ⟨n, b⟩ := l
  cases b <;> rfl

@[simp] theorem Literal.toLRAT_ofLRAT (l : PropositionalFormula.Literal) : (Literal.ofLRAT l).toLRAT = l := by
  cases l <;> rfl

theorem Literal.sat_toLRAT (σ : ℕ → Bool) (l : CNF.Literal ℕ) :
    PropositionalFormula.Literal.sat σ l.toLRAT = l.eval σ := by
  obtain ⟨n, b⟩ := l
  cases b <;> simp [Literal.toLRAT, PropositionalFormula.Literal.sat, CNF.Literal.eval]

/-- A numbered clause as a native clause. -/
def Clause.toLRAT (c : CNF.Clause ℕ) : PropositionalFormula.Clause := c.map Literal.toLRAT

/-- A numbered formula as a native formula. -/
def Formula.toLRAT (F : CNF.Formula ℕ) : PropositionalFormula.CNF := F.map Clause.toLRAT

theorem Clause.sat_toLRAT (σ : ℕ → Bool) (c : CNF.Clause ℕ) :
    PropositionalFormula.Clause.sat σ c.toLRAT = c.eval σ := by
  simp [PropositionalFormula.Clause.sat, Clause.toLRAT, Clause.eval, List.any_map, Function.comp_def,
    Literal.sat_toLRAT]

/-- **A numbered formula and its native form have the same value.** -/
theorem Formula.sat_toLRAT (σ : ℕ → Bool) (F : CNF.Formula ℕ) :
    PropositionalFormula.CNF.sat σ F.toLRAT = F.eval σ := by
  simp [PropositionalFormula.CNF.sat, Formula.toLRAT, Formula.eval, List.all_map, Function.comp_def,
    Clause.sat_toLRAT]

theorem Formula.unsat_toLRAT_iff (F : CNF.Formula ℕ) : PropositionalResolution.Unsat F.toLRAT ↔ F.Unsat := by
  simp only [PropositionalResolution.Unsat, Formula.Unsat, Formula.sat_toLRAT]

/-- **An accepted LRAT proof refutes the numbered formula.** -/
theorem Formula.unsat_of_lrat {F : CNF.Formula ℕ} {proof : PropositionalLRAT.Proof}
    (accepted : PropositionalLRAT.checker.check F.toLRAT proof = true) : F.Unsat :=
  (Formula.unsat_toLRAT_iff F).mp (PropositionalLRAT.check_sound _ proof accepted)

/-- An accepted LRAT text refutes the numbered formula. -/
theorem Formula.unsat_of_lratText {F : CNF.Formula ℕ} {bytes : ByteArray}
    (accepted : PropositionalLRAT.checkText F.toLRAT bytes = true) : F.Unsat := by
  unfold PropositionalLRAT.checkText at accepted
  obtain ⟨proof, published⟩ := Option.isSome_iff_exists.mp accepted
  exact (Formula.unsat_toLRAT_iff F).mp (PropositionalLRAT.reconstructText_sound published)

/-- An accepted stream of LRAT actions, checked one reverse-unit-propagation step at a time,
refutes the numbered formula. -/
theorem Formula.unsat_of_lratActions {F : CNF.Formula ℕ} {actions : List PropositionalLRATActions.Action}
    (accepted : PropositionalLRATActions.check F.toLRAT actions = true) : F.Unsat :=
  (Formula.unsat_toLRAT_iff F).mp (PropositionalLRATActions.check_sound accepted)

end CNF

namespace Program

variable {A : Type u} [DecidableEq A] (P : Program A)

/-- **An accepted LRAT proof for the completion and loop nogoods: no stable model.** -/
theorem not_stable_of_lrat {proof : PropositionalLRAT.Proof}
    (accepted : PropositionalLRAT.checker.check P.stableNumbered.toLRAT proof = true) (M : Set A) :
    ¬ P.Stable M :=
  P.not_stable_of_stableNumbered_unsat (CNF.Formula.unsat_of_lrat accepted) M

/-- **An accepted LRAT proof for the completion alone: no supported model.** -/
theorem not_supported_of_lrat {proof : PropositionalLRAT.Proof}
    (accepted : PropositionalLRAT.checker.check P.completionNumbered.toLRAT proof = true) (M : Set A) :
    ¬ P.Supported M :=
  P.not_supported_of_completionNumbered_unsat (CNF.Formula.unsat_of_lrat accepted) M

/-- An accepted LRAT proof for the completion alone refutes every stable model too. -/
theorem not_stable_of_completion_lrat {proof : PropositionalLRAT.Proof}
    (accepted : PropositionalLRAT.checker.check P.completionNumbered.toLRAT proof = true) (M : Set A) :
    ¬ P.Stable M :=
  P.not_stable_of_completionNumbered_unsat (CNF.Formula.unsat_of_lrat accepted) M

theorem not_stable_of_lratText {bytes : ByteArray}
    (accepted : PropositionalLRAT.checkText P.stableNumbered.toLRAT bytes = true) (M : Set A) : ¬ P.Stable M :=
  P.not_stable_of_stableNumbered_unsat (CNF.Formula.unsat_of_lratText accepted) M

theorem not_stable_of_lratActions {actions : List PropositionalLRATActions.Action}
    (accepted : PropositionalLRATActions.check P.stableNumbered.toLRAT actions = true) (M : Set A) :
    ¬ P.Stable M :=
  P.not_stable_of_stableNumbered_unsat (CNF.Formula.unsat_of_lratActions accepted) M

theorem not_supported_of_lratActions {actions : List PropositionalLRATActions.Action}
    (accepted : PropositionalLRATActions.check P.completionNumbered.toLRAT actions = true) (M : Set A) :
    ¬ P.Supported M :=
  P.not_supported_of_completionNumbered_unsat (CNF.Formula.unsat_of_lratActions accepted) M

/-- **A proof for some of the clauses suffices**: a solver may emit any selection of the clauses of
the numbered completion and loop nogoods, in any order; an accepted proof for it refutes every
stable model. -/
theorem not_stable_of_lrat_subset {G : CNF.Formula ℕ} (sub : ∀ c ∈ G, c ∈ P.stableNumbered)
    {proof : PropositionalLRAT.Proof} (accepted : PropositionalLRAT.checker.check G.toLRAT proof = true)
    (M : Set A) : ¬ P.Stable M :=
  P.not_stable_of_stableNumbered_unsat ((CNF.Formula.unsat_of_lrat accepted).of_subset sub) M

theorem not_supported_of_lrat_subset {G : CNF.Formula ℕ} (sub : ∀ c ∈ G, c ∈ P.completionNumbered)
    {proof : PropositionalLRAT.Proof} (accepted : PropositionalLRAT.checker.check G.toLRAT proof = true)
    (M : Set A) : ¬ P.Supported M :=
  P.not_supported_of_completionNumbered_unsat ((CNF.Formula.unsat_of_lrat accepted).of_subset sub) M

/-- **Refuting entailed nogoods refutes the program.** If every nogood of `Δ` is entailed and over
program variables, for example the completion nogoods with the learned ones, an unsatisfiable
numbered CNF of `Δ` means there is no stable model. -/
theorem not_stable_of_entailed_unsat {Δ : List (Nogood A)} (entailed : ∀ δ ∈ Δ, P.Entailed δ.lits)
    (vars : ∀ δ ∈ Δ, ∀ l ∈ δ.lits, P.IsVar l.var) (unsat : (P.numbered (nogoodCNF Δ)).Unsat) (M : Set A) :
    ¬ P.Stable M := by
  intro stable
  obtain ⟨admissible, correct, stable'⟩ := P.stable_canonical stable
  have cnfVars : (nogoodCNF Δ).VarsIn {x | P.IsVar x} := by
    intro c hc l hl
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hc
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    exact vars δ hδ m hm
  have sat : (nogoodCNF Δ).eval (canonical M) = true :=
    (eval_nogoodCNF _ _).mpr fun δ hδ violated => by
      obtain ⟨l, hl, notSat⟩ := entailed δ hδ _ admissible correct stable'
      exact notSat (violated l hl)
  have := unsat (P.encode (canonical M))
  rw [P.numbered_eval cnfVars, P.eval_decode_encode cnfVars, sat] at this
  cases this

theorem not_stable_of_entailed_lrat {Δ : List (Nogood A)} (entailed : ∀ δ ∈ Δ, P.Entailed δ.lits)
    (vars : ∀ δ ∈ Δ, ∀ l ∈ δ.lits, P.IsVar l.var) {proof : PropositionalLRAT.Proof}
    (accepted : PropositionalLRAT.checker.check (P.numbered (nogoodCNF Δ)).toLRAT proof = true) (M : Set A) :
    ¬ P.Stable M :=
  P.not_stable_of_entailed_unsat entailed vars (CNF.Formula.unsat_of_lrat accepted) M

end Program

end Mettapedia.Logic.ASP
