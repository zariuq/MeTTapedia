import Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus

/-!
# Template scope: an adjoint reading of the scope constructs (remark)

For a context projection `p : Γ.A → Γ`, the type face has `Σ_p ⊣ p* ⊣ Π_p` and
the predicate face `∃_p ⊣ p* ⊣ ∀_p`.  Mettapedia has both, and this module
only points to them:

* `TypeTheory.PresheafDependentAdjunction` — `familyAdjunction`,
  `dependentAdjunction`, `transpose`, `beta`, `eta`;
* `GSLT.Topos.PresheafPredicateFirstOrder` — `existsAdjunction`,
  `forallAdjunction`, `equality`, `diagonalAdjunction`, `image_frobenius`;
* `CategoryTheory.PredicateDoctrine`, `PredicateDoctrineEquality` — the
  abstract doctrine with Beck–Chevalley, and equality as the left adjoint to
  contraction (`equalityWithParameters`, `contractionAdjunction`).

The scope constructs of the model read as follows.  Each row has one lemma
about the model.  The rows are readings: no adjunction implies an ownership
profile, a surface convention or an elaboration law, and an adjoint product
need not even be a substitution-stable former
(`TypeTheory.CategoryIndexedFamilyGeneralPiBoundary`).

| Construct | Reading | Lemma on the model |
|---|---|---|
| a shared name (in a crossing set) | `p*`: the inner region sees the outer variable unchanged | `crossing_name_outer` |
| a fresh name, per call | `∃_p`: each call allocates its own variable, hidden outside | `fresh_per_call` |
| a lambda; its application | the transpose of the `Π` adjunction; the counit, β | `run_beta` |
| an equality constraint | equality is the image of truth along the diagonal; `unify` and a `let` pattern are the refinement procedure that records it, and fails on conflict (a procedure, not the predicate) | `refine_records`, `refine_conflict` |
| a per-call hole; a persistent hole | `Π_x Σ_y R`; `Σ_y Π_x R` | `holes_per_call_persistent` |
| a captured hole | a parameter | `run_lifted_call` (`TemplateScope.Evaluation`) |

Rule M builds the diagonal into spelling: two occurrences of one spelling in
one scope are contracted with no written constraint, which is what
`ownRule_tension` measures against modularity.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- **Weakening, `p*`.**  A name in a construct's crossing set is never the
construct's own: inside it, the name resolves to the slot the enclosing scope
gives it. -/
theorem crossing_name_outer (env : REnv X) (sh U d : List X) (o : Owner) {y : X}
    (hy : y ∈ sh) :
    y ∉ crossOwn (some sh) U d ∧ env.update (crossOwn (some sh) U d) o y = env y := by
  have hn : y ∉ crossOwn (some sh) U d := by
    simp [crossOwn, List.mem_dedup, hy]
  exact ⟨hn, by simp [REnv.update, hn]⟩

variable [DecidableEq S]

omit [DecidableEq S] in
/-- **The existential, per call.**  An activation copies each own name to a
name tagged by its own path; activations at different paths make different
names, so each call has its own variable, which no other call sees. -/
theorem fresh_per_call (own : List X) {y : X} (hy : y ∈ own) {ρ ρ' : Path} (h : ρ ≠ ρ') :
    (renameOwn ρ own (.src y) : Option (Tm S X)) = some (.var (.inst ρ (.src y))) ∧
      (renameOwn ρ own (.src y) : Option (Tm S X)) ≠ renameOwn ρ' own (.src y) := by
  have hk : ownKey own (.src y) = true := by simp [ownKey, hy]
  refine ⟨by simp [renameOwn, hk], ?_⟩
  simp only [renameOwn, hk, if_true, ne_eq, Option.some.injEq, Tm.var.injEq, Nm.inst.injEq,
    and_true]
  exact h

/-- **The counit, β.**  Applying a lambda that owns nothing to a value runs its
body with the value for the parameter. -/
theorem run_beta (prog : S → Option (Tm S X)) (n : ℕ) (π : Path) (σ : GStore S X) (x : Nm X)
    (b : Tm S X) (s : S) :
    run .static prog (n + 2) π σ (.app (.lam x [] b) (.sym s)) =
      run .static prog (n + 1) (π ++ [2]) σ (subst Sub.none (Sub.single x (.sym s)) b) := by
  show step .static prog (run .static prog (n + 1)) π σ _ = _
  simp only [step]
  rw [run_lam, bindOpt_some_singleton]
  show bindOpt (step .static prog (run .static prog n) (π ++ [1]) σ (.sym s)) _ = _
  simp only [step, bindOpt_some_singleton, activate, renameOwn_nil]

/-- **Equality, recorded.**  Matching a store name against a ground value is the
refinement step that records the equation in the store. -/
theorem refine_records (σ : GStore S X) (n : Nm X) (g : GVal S X) :
    matchT σ (.var n) g.toTm = refineStep σ (n, g) := by
  simp [matchT, GVal.toTm_toGVal?]

/-- **Equality, failing.**  Recording a second, different value for a bound
name fails: two inconsistent equations on one variable have no answer. -/
theorem refine_conflict (σ : GStore S X) (n : Nm X) {g g' : GVal S X} (hσ : σ n = some g)
    (hne : g ≠ g') : refineStep σ (n, g') = none := by
  simp [refineStep, hσ, hne]

end Mettapedia.GSLT.LanguageDef.TemplateScope

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

/-- **`Π_x Σ_y R` against `Σ_y Π_x R`.**  Row 1 calls one closure twice.  Per
call (`Π_x Σ_y`), each call has its own `$y`, and the two calls answer
independently.  Per closure (`Σ_y Π_x`), one `$y` serves every call, and the
two constraints conflict.  A `let` reads the same way: with `{}` the inner
`$y` is hidden (`∃`, row 23cf); with `{$y}` it is the outer one (`p*`, row
23cs), and the two equations conflict. -/
theorem holes_per_call_persistent :
    ans cfgM clauses row1 = some [pairT (gT (kT .n1)) (gT (kT .n2))] ∧
    ans cfgPC clauses row1 = some [] ∧
    ans cfgM clauses row23cf = some [pairT (kT .n1) (kT .n2)] ∧
    ans cfgM clauses row23cs = some [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus
