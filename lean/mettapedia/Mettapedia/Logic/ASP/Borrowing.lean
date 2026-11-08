import Mettapedia.Logic.ASP.ProgramCNF
import Mettapedia.Logic.InstitutionBorrowing

/-!
# Completion with loop nogoods as a conservative route

`InstitutionBorrowing` reads "certify a source sentence by proving its
translation in the target logic" as a route between theories, and calls the
route conservative when the target certifies nothing the source lacks. Here the
sentences are clauses over the program's variables (`Program.ProgramClause`).

* The source theory is the theory of the program's stable models
  (`Program.stableTheory`): the clauses every stable model satisfies, which are
  exactly the negations of the entailed nogoods (`Program.mem_stableTheory_iff`).
* The target theory of a CNF over solver variables is the set of clauses it
  entails (`Program.cnfTheory`).

Results:

* Completion with loop nogoods is a route (`Program.stableRoute`): every clause
  true in all stable models is entailed by the stable CNF. It is conservative
  (`Program.stableRoute_conservative`), so its borrowed theory is exactly the
  stable theory (`Program.stableRoute_borrowed`): a SAT solver's verdict on the
  stable CNF is a verdict on the program.
* Completion alone always borrows soundly: what the completion CNF entails holds
  in every stable model (`Program.cnfTheory_completion_subset`). For tight
  programs it is also a route, and conservative (`Program.completionRoute`,
  `Program.completionRoute_conservative`). Without tightness it can lose
  theorems: the controls show a clause true in the only stable model of
  `p :- p.` that the completion does not entail.

Answer set programs under the stable model semantics do not form an institution
whose sentences are rules (stability is not a satisfaction relation of single
rules), so the translation is stated at the level of theories, which is what
`TheoryRoute` expresses; the comorphism view of the plan reads it the same way,
with the signature fixed to the program's variables.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.Program

open InstitutionBorrowing

universe u

variable {A : Type u} [DecidableEq A] (P : Program A)

/-- Clauses over the program's variables. -/
abbrev ProgramClause := {c : CNF.Clause (Var A) // ∀ l ∈ c, P.IsVar l.var}

/-- **The theory of the stable models**: the clauses every stable model satisfies. -/
def stableTheory : Set P.ProgramClause :=
  {c | ∀ v, P.Admissible v → P.BodiesCorrect v → P.Stable v.atoms → c.1.eval v = true}

/-- **The theory of a CNF**: the clauses it entails. -/
def cnfTheory (F : CNF.Formula (Var A)) : Set P.ProgramClause := {c | F.Entails c.1}

omit [DecidableEq A] in
/-- The source theory is the theory of entailed nogoods, read as clauses. -/
theorem mem_stableTheory_iff (δ : Nogood A) (vars : ∀ l ∈ δ.clause, P.IsVar l.var) :
    (⟨δ.clause, vars⟩ : P.ProgramClause) ∈ P.stableTheory ↔ P.Entailed δ.lits := by
  simp only [stableTheory, Set.mem_ofPred_eq, Nogood.eval_clause, Nogood.not_violated_iff]
  rfl

/-- A clause over program variables has the same value under an assignment and under the
admissible assignment that agrees with it on the program. -/
theorem eval_clause_restrict (c : P.ProgramClause) (σ : Valuation A) :
    c.1.eval (P.decode (P.encode σ)) = c.1.eval σ :=
  CNF.Clause.eval_congr fun l hl => P.decode_encode σ (c.2 l hl)

/-- **Completion with loop nogoods is a route.** -/
def stableRoute : TheoryRoute P.stableTheory (P.cnfTheory P.stableCNF) where
  translate := id
  preserves := by
    intro c hc σ sat
    rw [← P.eval_decode_encode P.stableCNF_vars] at sat
    obtain ⟨stable, correct⟩ := (P.stableCNF_eval_iff _ (P.decode_admissible _)).mp sat
    rw [← P.eval_clause_restrict]
    exact hc _ (P.decode_admissible _) correct stable

/-- **It is conservative**: what the stable CNF entails holds in every stable model. -/
theorem stableRoute_conservative : P.stableRoute.Conservative := by
  intro c hc v admissible correct stable
  exact hc v ((P.stableCNF_eval_iff v admissible).mpr ⟨stable, correct⟩)

/-- **Borrowing along completion with loop nogoods is exact.** -/
theorem stableRoute_borrowed : P.stableRoute.borrowed = P.stableTheory :=
  (TheoryRoute.conservative_iff_borrowed_eq _).mp P.stableRoute_conservative

/-- **Completion alone borrows soundly**, for every program. -/
theorem cnfTheory_completion_subset : P.cnfTheory P.completionCNF ⊆ P.stableTheory := by
  intro c hc v admissible correct stable
  exact hc v ((P.completionCNF_eval_iff v admissible).mpr ⟨P.stable_supported stable, correct⟩)

/-- For a tight program, completion alone is a route. -/
def completionRoute (tight : P.Tight) : TheoryRoute P.stableTheory (P.cnfTheory P.completionCNF) where
  translate := id
  preserves := by
    intro c hc σ sat
    rw [← P.eval_decode_encode P.completionCNF_vars] at sat
    obtain ⟨stable, correct⟩ :=
      (P.completionCNF_eval_iff_stable tight _ (P.decode_admissible _)).mp sat
    rw [← P.eval_clause_restrict]
    exact hc _ (P.decode_admissible _) correct stable

theorem completionRoute_conservative (tight : P.Tight) : (P.completionRoute tight).Conservative :=
  P.cnfTheory_completion_subset

end Mettapedia.Logic.ASP.Program
