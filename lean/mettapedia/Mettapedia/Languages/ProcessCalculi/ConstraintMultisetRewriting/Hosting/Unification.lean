import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Hosting

/-!
# Where the unification is done

The step's own matching does the work:

* `schema_information`: the information of an equation's firing is the knowledge, transported, and
  **one equation**: the opened take pattern `alt(eval(apply lhs), FS)` equated with the alternative's
  row. No matcher, no substitution and no answer of the source enters it.
* `schema_admitted_iff`: the **canonical** firing of an equation's schema at the alternative's row
  (the rule opened at its own new names, making a fresh row) is admitted **exactly when the source's
  two-way unification of a fresh copy of the left side with the call is solvable** in the alternative's
  store. Admission is the step's solvability of its information at the contextual frames, whose
  equality is syntax (`contextual_equality`): equations between terms with second-order unknowns,
  solved modulo nothing, for any left side; second-order pattern unification where the left side is
  in the pattern class. That every other admitted firing of the schema is a source move too is
  `reflection`.
* `translate_rules` (in `Rules`) and `translate_equations`: the translation is a function of the
  program's equations alone; the term being run contributes rows, never rules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {Ty : Type}

/-- The translation depends only on the program's equations. -/
theorem translate_equations {P P' : SourceLanguage.Program κ Γ star Ty} (same : P.equations = P'.equations) :
    translate N P = translate N P' := by
  simp only [translate, same]

variable {P : SourceLanguage.Program κ Γ star Ty}

/-- **The information of an equation's firing**: the knowledge and one take equation. -/
theorem schema_information {s : HostState S} {a : ℕ} {e : SourceLanguage.Equation κ Γ star Ty}
    (member : e ∈ P.equations) :
    (canonicalAt s (schema N e) (schema_mem N P member) a).information (Interface.Frames.contextual S) s =
      (Interface.Frames.contextual S).applyStore
          ((RuleSyntax.Contextual.declarations S).weaken (canonicalAt s (schema N e) (schema_mem N P member) a).ext)
          s.knowledge ++
        [(instantiateObservation (canonicalAt s (schema N e) (schema_mem N P member) a).opening
            (observe (altN N (evalN N (applyN N (instantiate asUnknowns e.lhs))) schemaStack)),
          RuleSyntax.Firing.row (Interface.Frames.contextual S) s
            (canonicalAt s (schema N e) (schema_mem N P member) a) a)] ++ [] ++ [] :=
  simple_information (canonical_simple rfl rfl rfl)

/-- **The step's matching is the source's unification.** The canonical firing of an equation's schema
at a represented alternative's row is admitted exactly when a fresh copy of the equation's left side
unifies with the call in the alternative's store. -/
theorem schema_admitted_iff {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    {s : HostState S} {a : ℕ} (rep : Represents N P n ⟨K, .eval (.apply t), fs, ps⟩ s a)
    {e : SourceLanguage.Equation κ Γ star Ty} (member : e ∈ P.equations) :
    (canonicalAt s (schema N e) (schema_mem N P member) a).Admits (Interface.Frames.contextual S) s ↔
      Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)]) := by
  have simple := canonical_simple (s := s) (member := schema_mem N P member) (a := a)
    (pat := observe (altN N (evalN N (applyN N (instantiate asUnknowns e.lhs))) schemaStack))
    (out := observe (altN N (evalN N (encComp N (instantiate asUnknowns) e.rhs)) schemaStack)) rfl rfl rfl
  have shapes := canonical_shapes (s := s) (member := schema_mem N P member) (a := a)
    (pat := observe (altN N (evalN N (applyN N (instantiate asUnknowns e.lhs))) schemaStack))
    (out := observe (altN N (evalN N (encComp N (instantiate asUnknowns) e.rhs)) schemaStack)) rfl rfl rfl rfl
  have aPresent : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have callBelow : DependsBelow n t := rep.fresh.2.1 t (by simp [focusData, Comp.data])
  constructor
  · rintro ⟨_, _, ⟨B, u, solved⟩, _⟩
    obtain ⟨known, _, matched⟩ := simple_restrict simple u solved
    have reads := (rep.reads B _).mp ⟨_, known, matched.symm⟩
    change branchReads N _ B (observe (instantiate _ _)) at reads
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns] at reads
    obtain ⟨t', σ, focus, solvedσ, onCall⟩ := shape_apply N reads
    simp only [Focus.eval.injEq, Comp.apply.injEq] at focus
    subst focus
    exact (solvable_copy_iff e.lhs rep.fresh.1 callBelow).mpr ⟨_, _, σ, _, solvedσ, onCall.symm⟩
  · intro live
    refine ⟨shapes, enabled_single aPresent (freshId_not_mem s), ?_, entails_of_no_checks rfl rfl⟩
    obtain ⟨W, target, σ, solved⟩ := live
    have reads : branchReads N
        (⟨K ++ [(instantiate (copyAt κ n) e.lhs, t)], .eval (e.rhs.inst (copyAt κ n)), fs, ps⟩ :
          Branch κ Γ star Ty) ⟨W, target⟩ (observe (encBranch N (instantiate σ) _)) := ⟨σ, solved, rfl⟩
    obtain ⟨h, readsB, told, _⟩ := (transfer_schema N e rfl rep.fresh _).mpr reads
    obtain ⟨g, known, matched⟩ := (rep.reads _ _).mpr readsB
    obtain ⟨u, solvedU, _⟩ := simple_amalgamate simple shapes.1 aPresent g h known told matched.symm
    exact ⟨_, u, solvedU⟩

#print axioms translate_equations
#print axioms schema_information
#print axioms schema_admitted_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
