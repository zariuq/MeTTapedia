import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Renaming

/-!
# Codes up to renaming: the canonical code of a rule

The code of a rule is syntax: the codes of a rule and of a renamed copy are different rows
(`Renaming.renamed_code_ne`), and a rule reading a code by its text tells them apart
(`Renaming.probe_refuses_renamed`). Coding the canonical form of a rule instead makes the code row a
function of the rule up to injective renaming of its own unknowns, with the same interpreter.

* **The canonical numbering** (`canonNum r`): an unknown of `r` goes to the position of its first
  occurrence in the list of the rule's terms (`occ`); every other unknown goes above all positions. It
  is injective (`canonNum_injective`).
* **The canonical form** (`canon r`, the rule renamed by its canonical numbering) and **the canonical
  code** (`canonCode r`, the code of the canonical form).
* **Invariance** (`canon_rename`, `canonCode_rename`): for every injective renaming `π`, the canonical
  form, hence the canonical code, of `rename π r` is that of `r`.
* **What the canonical code determines** (`canonCode_eq_iff`): two rules have the same canonical code
  exactly when they have the same canonical form, and each rule is an injective renaming of its
  canonical form (`canon` is `rename (canonNum r) r`, `canonNum_injective`).
* **Through the interpreter** (`canonical_codes_bisimulation`): the interpreter, from the canonical
  codes of a fixed program, is strongly bisimilar to the program. A program and a renamed copy have the
  same canonical program (`canonProgram_rename`), so they store the same code rows.

**Examples and controls.** Computed: the canonical code of `first` and of its copy with unknowns moved
up by one hundred are both the code of `first` (`first_canonical`, `shifted_canonical`). The pair rule
and its collapsed copy, which have different steps (`Renaming.collapsed_refused`), have different
canonical codes (`collapsed_canonical_ne`). The two-step run of the example program goes through the
interpreter from the canonical codes (`canonical_demo_interpreter_run`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Canonical

open LogicOverTheStep.StepSpan (Succ)
open Expr
open Examples (DataFragment first)
open Gating
open Renaming

/-! ## The unknowns of a rule, in order of occurrence -/

/-- The unknowns of a term, in order of occurrence. -/
def varsOf : Expr → List ℕ
  | var v => [v]
  | sym _ => []
  | cell a b => varsOf a ++ varsOf b
  | slot _ _ => []
  | drop c e => varsOf c ++ varsOf e

/-- The unknowns of a rule, in order of occurrence in its terms. -/
def occ (r : Rule Tm) : List ℕ := r.terms.flatMap varsOf

theorem varsOf_rename (π : ℕ → ℕ) : ∀ t : Expr, varsOf (subst (renamer π) t) = (varsOf t).map π
  | var _ => rfl
  | sym _ => rfl
  | cell a b => by
      simp only [subst, varsOf, List.map_append, varsOf_rename π a, varsOf_rename π b]
  | slot _ _ => rfl
  | drop c e => by
      simp only [subst, varsOf, List.map_append, varsOf_rename π c, varsOf_rename π e]

theorem occ_rename (π : ℕ → ℕ) (r : Rule Tm) : occ (rename π r) = (occ r).map π := by
  unfold occ
  rw [terms_rename, List.flatMap_map, List.map_flatMap]
  congr 1
  funext t
  exact varsOf_rename π t

/-! ## The canonical numbering -/

/-- **The canonical numbering** of a rule's unknowns: an unknown of the rule goes to the position of its
first occurrence; every other unknown goes above all positions. -/
def canonNum (r : Rule Tm) (v : ℕ) : ℕ :=
  if v ∈ occ r then (occ r).idxOf v else (occ r).length + v

theorem canonNum_injective (r : Rule Tm) : Function.Injective (canonNum r) := by
  intro v w same
  unfold canonNum at same
  by_cases hv : v ∈ occ r <;> by_cases hw : w ∈ occ r
  · rw [if_pos hv, if_pos hw] at same
    exact (List.idxOf_inj hv).mp same
  · rw [if_pos hv, if_neg hw] at same
    have := List.idxOf_lt_length_of_mem hv
    omega
  · rw [if_neg hv, if_pos hw] at same
    have := List.idxOf_lt_length_of_mem hw
    omega
  · rw [if_neg hv, if_neg hw] at same
    omega

theorem idxOf_map {π : ℕ → ℕ} (inj : Function.Injective π) (v : ℕ) :
    ∀ l : List ℕ, (l.map π).idxOf (π v) = l.idxOf v
  | [] => rfl
  | a :: l => by
      have same : (π a == π v) = (a == v) := by
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        exact inj.eq_iff
      rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, idxOf_map inj v l, same]

/-- An unknown of a rule and its renamed copy have the same canonical number. -/
theorem canonNum_rename {π : ℕ → ℕ} (inj : Function.Injective π) (r : Rule Tm) {v : ℕ}
    (inside : v ∈ occ r) : canonNum (rename π r) (π v) = canonNum r v := by
  unfold canonNum
  rw [occ_rename, if_pos (List.mem_map.mpr ⟨v, inside, rfl⟩), if_pos inside, idxOf_map inj]

/-! ## Renaming composes, and only the unknowns that occur matter -/

theorem subst_congr_vars {σ τ : ℕ → Expr} :
    ∀ t : Expr, (∀ v ∈ varsOf t, σ v = τ v) → subst σ t = subst τ t
  | var v, same => same v List.mem_cons_self
  | sym _, _ => rfl
  | cell a b, same => by
      show cell (subst σ a) (subst σ b) = cell (subst τ a) (subst τ b)
      rw [subst_congr_vars a fun v inside => same v (List.mem_append_left _ inside),
        subst_congr_vars b fun v inside => same v (List.mem_append_right _ inside)]
  | slot _ _, _ => rfl
  | drop c e, same => by
      show drop (subst σ c) (subst σ e) = drop (subst τ c) (subst τ e)
      rw [subst_congr_vars c fun v inside => same v (List.mem_append_left _ inside),
        subst_congr_vars e fun v inside => same v (List.mem_append_right _ inside)]

/-- **Two renamings that agree on the unknowns of a rule rename it alike.** -/
theorem rename_congr {π π' : ℕ → ℕ} {r : Rule Tm} (same : ∀ v ∈ occ r, π v = π' v) :
    rename π r = rename π' r := by
  have terms : ∀ t ∈ r.terms, subst (renamer π) t = subst (renamer π') t := fun t inside =>
    subst_congr_vars t fun v member => by
      show var (π v) = var (π' v)
      rw [same v (List.mem_flatMap.mpr ⟨t, inside, member⟩)]
  obtain ⟨locals, ⟨take, read, tell, checks, produce⟩, collect⟩ := r
  have inTerms : ∀ {t : Expr}, t ∈ take ∨ t ∈ read ∨ t ∈ tell.map Prod.fst ∨ t ∈ tell.map Prod.snd ∨
      t ∈ checks.flatMap checkTerms ∨ t ∈ produce ∨ t ∈ collect →
        subst (renamer π) t = subst (renamer π') t := by
    intro t inside
    apply terms t
    simp only [Rule.terms, List.mem_append]
    tauto
  have takes : take.map (subst (renamer π)) = take.map (subst (renamer π')) :=
    List.map_congr_left fun t inside => inTerms (Or.inl inside)
  have reads : read.map (subst (renamer π)) = read.map (subst (renamer π')) :=
    List.map_congr_left fun t inside => inTerms (Or.inr (Or.inl inside))
  have tells : tell.map (fun pair => (subst (renamer π) pair.1, subst (renamer π) pair.2)) =
      tell.map (fun pair => (subst (renamer π') pair.1, subst (renamer π') pair.2)) := by
    refine List.map_congr_left fun e inside => ?_
    rw [inTerms (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩)))),
      inTerms (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨e, inside, rfl⟩)))))]
  have checksEq : checks.map (Check.map (subst (renamer π))) = checks.map (Check.map (subst (renamer π'))) := by
    refine List.map_congr_left fun c inside => ?_
    have all : ∀ t ∈ checkTerms c, subst (renamer π) t = subst (renamer π') t := fun t member =>
      inTerms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_flatMap.mpr ⟨c, inside, member⟩))))))
    cases c with
    | equal left right =>
        show Check.equal _ _ = Check.equal _ _
        rw [all left (by simp [checkTerms]), all right (by simp [checkTerms])]
    | predicate quantifier pattern =>
        show Check.predicate quantifier _ = Check.predicate quantifier _
        rw [all pattern (by simp [checkTerms])]
    | count pattern number =>
        show Check.count _ number = Check.count _ number
        rw [all pattern (by simp [checkTerms])]
  have produces : produce.map (subst (renamer π)) = produce.map (subst (renamer π')) :=
    List.map_congr_left fun t inside => inTerms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inside))))))
  have collectEq : collect.map (subst (renamer π)) = collect.map (subst (renamer π')) :=
    List.map_congr_left fun t inside => inTerms (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inside))))))
  show (⟨locals, ⟨take.map (subst (renamer π)), read.map (subst (renamer π)),
      tell.map (fun pair => (subst (renamer π) pair.1, subst (renamer π) pair.2)),
      checks.map (Check.map (subst (renamer π))), produce.map (subst (renamer π))⟩,
      collect.map (subst (renamer π))⟩ : Rule Tm) =
    ⟨locals, ⟨take.map (subst (renamer π')), read.map (subst (renamer π')),
      tell.map (fun pair => (subst (renamer π') pair.1, subst (renamer π') pair.2)),
      checks.map (Check.map (subst (renamer π'))), produce.map (subst (renamer π'))⟩,
      collect.map (subst (renamer π'))⟩
  rw [takes, reads, tells, checksEq, produces, collectEq]

/-- **Renaming twice is renaming by the composite.** -/
theorem rename_rename (π π' : ℕ → ℕ) (r : Rule Tm) :
    rename π' (rename π r) = rename (fun v => π' (π v)) r := by
  have comp : ∀ t, subst (renamer π') (subst (renamer π) t) = subst (renamer fun v => π' (π v)) t :=
    fun t => subst_renaming π (renamer π') t
  have collectEq : (r.collect.map (subst (renamer π))).map (subst (renamer π')) =
      r.collect.map (subst (renamer fun v => π' (π v))) := by
    rw [List.map_map]
    exact List.map_congr_left fun t _ => comp t
  show (⟨r.locals, (r.body.map (subst (renamer π))).map (subst (renamer π')),
      (r.collect.map (subst (renamer π))).map (subst (renamer π'))⟩ : Rule Tm) =
    ⟨r.locals, r.body.map (subst (renamer fun v => π' (π v))),
      r.collect.map (subst (renamer fun v => π' (π v)))⟩
  rw [body_map_map r.body (g := subst (renamer π)) (h := subst (renamer π'))
    (k := subst (renamer fun v => π' (π v))) comp, collectEq]

/-! ## The canonical form and the canonical code -/

/-- **The canonical form** of a rule: its unknowns renamed by the canonical numbering. -/
def canon (r : Rule Tm) : Rule Tm := rename (canonNum r) r

/-- **The canonical code** of a rule: the code of its canonical form. -/
def canonCode (r : Rule Tm) : Expr := ruleCode (canon r)

/-- **Renaming does not change the canonical form.** -/
theorem canon_rename {π : ℕ → ℕ} (inj : Function.Injective π) (r : Rule Tm) :
    canon (rename π r) = canon r := by
  unfold canon
  rw [rename_rename]
  exact rename_congr fun v inside => canonNum_rename inj r inside

/-- **Renaming does not change the canonical code.** -/
theorem canonCode_rename {π : ℕ → ℕ} (inj : Function.Injective π) (r : Rule Tm) :
    canonCode (rename π r) = canonCode r := by
  unfold canonCode
  rw [canon_rename inj]

/-- **The canonical code determines the canonical form.** -/
theorem canonCode_eq_iff (r r' : Rule Tm) : canonCode r = canonCode r' ↔ canon r = canon r' :=
  ⟨fun same => RunTime.ruleCode_injective same, fun same => by unfold canonCode; rw [same]⟩

/-! ## Through the interpreter -/

/-- **A fixed program with its rules in canonical form.** -/
def canonProgram (P : FixedProgram) : FixedProgram := renameProgram P canonNum

theorem fixedProgram_ext : ∀ {A B : FixedProgram}, A.rules = B.rules → A = B
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/-- **A program and a renamed copy have the same canonical program**, so the same code rows. -/
theorem canonProgram_rename {P : FixedProgram} {ρ : Rule Tm → ℕ → ℕ}
    (inj : ∀ r ∈ P.rules, Function.Injective (ρ r)) :
    canonProgram (renameProgram P ρ) = canonProgram P := by
  apply fixedProgram_ext
  show (P.rules.map fun r => rename (ρ r) r).map canon = P.rules.map canon
  rw [List.map_map]
  exact List.map_congr_left fun r inside => canon_rename (inj r inside) r

variable {O : Type*} [DecidableEq O]

/-- **The interpreter, from the canonical codes of a fixed program, runs the program**: strongly
bisimilar, step for step. -/
theorem canonical_codes_bisimulation {P : FixedProgram} {s : State Tm O}
    {u : State Tm (O ⊕ Fin (canonProgram P).rules.length)} (related : Runs (canonProgram P) s u) :
    (∀ s', Succ (step X O Ext P.program).toStep s s' → ∃ u', InterpSucc u u' ∧ Runs (canonProgram P) s' u') ∧
      (∀ u', InterpSucc u u' →
        ∃ s', Succ (step X O Ext P.program).toStep s s' ∧ Runs (canonProgram P) s' u') :=
  renamed_codes_bisimulation (fun r _ => canonNum_injective r) related

/-! ## Examples and controls -/

/-- **`first` is in canonical form**, by the computation. -/
theorem first_canonical : canonCode first = ruleCode first := by decide

/-- **Its copy with unknowns moved up by one hundred has the same canonical code**, by the computation
(and by `canonCode_rename`). -/
theorem shifted_canonical : canonCode (rename (shiftAll first) first) = ruleCode first := by decide

/-- **The pair rule and its collapsed copy have different canonical codes.** -/
theorem collapsed_canonical_ne : canonCode (rename collapse pairRule) ≠ canonCode pairRule := by decide

/-- **The two-step run of the example program through the interpreter, from the canonical codes.** -/
theorem canonical_demo_interpreter_run :
    ∃ u₁ u₂, InterpSucc (withCodes (canonProgram demoProgram) dataStart) u₁ ∧ InterpSucc u₁ u₂ ∧
      Runs (canonProgram demoProgram) (demoSecond.result X dataMiddle) u₂ := by
  have start := fixed_program_start (P := canonProgram demoProgram) dataStart_rows
  obtain ⟨u₁, moved₁, related₁⟩ := (canonical_codes_bisimulation start).1 _ demo_run.1
  obtain ⟨u₂, moved₂, related₂⟩ := (canonical_codes_bisimulation related₁).1 _ demo_run.2
  exact ⟨u₁, u₂, moved₁, moved₂, related₂⟩

#print axioms canonNum_injective
#print axioms canon_rename
#print axioms canonCode_rename
#print axioms canonCode_eq_iff
#print axioms canonProgram_rename
#print axioms canonical_codes_bisimulation
#print axioms first_canonical
#print axioms shifted_canonical
#print axioms collapsed_canonical_ne
#print axioms canonical_demo_interpreter_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Canonical
