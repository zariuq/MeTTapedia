import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanReplay

/-!
# The public compiler allowance admits every derivable result

Any successful formation, at any finite recursion allowance, succeeds at the
actual source-derived default with the same plan, allocation and aliases.
This excludes false refusal caused solely by that default. Unsupported source
regions remain distinct from both recursion cutoff and source failure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem compile_at_default (context : Context) : ∀ depth supply expression result,
    compile context depth supply expression = some result →
      compile context (LambdaStaging.depthOf expression * 2 + 2) supply expression = some result := by
  intro depth
  induction depth with
  | zero => intro supply expression result computed; cases computed
  | succ depth ih =>
      intro supply expression result computed
      change perform context (compile context depth) supply (classify expression) = some result at computed
      change perform context (compile context (LambdaStaging.depthOf expression * 2 + 1))
        supply (classify expression) = some result
      apply perform_replay context _ _ supply (classify expression) result _ computed
      intro s child returned present found
      rcases classified_child_bound expression child present with smaller | rfl
      · exact compile_of_allowance_le context (LambdaStaging.depthOf child * 2 + 2)
          (LambdaStaging.depthOf expression * 2 + 1) s child returned (by omega)
          (ih s child returned found)
      · cases depth with
        | zero => cases found
        | succ earlier =>
            simp only [compile,call,classify,perform,Option.some.injEq] at found
            subst returned
            rfl

theorem formation_at_default {context : Context} {depth : Nat} {supply : Supply}
    {expression : Atom} {result : Result} (source : FormationAt context depth supply expression result) :
    FormationAt context (LambdaStaging.depthOf expression * 2 + 2) supply expression result :=
  (compile_iff _ _ _ _ _).mp (compile_at_default context depth supply expression result
    ((compile_iff _ _ _ _ _).mpr source))

/-- Public entry preserves and reflects every finite derivation of the
independent formation rules, rather than only derivations at its own bound. -/
theorem compileExpression_iff_any_formation (context : Context) (expression : Atom) (plan : Plan) :
    compileExpression context expression = some plan ↔
      ∃ depth result, FormationAt context depth (Supply.start [expression]) expression result ∧ normalized result = plan := by
  constructor
  · intro computed
    simp only [compileExpression,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
    obtain ⟨result,formed,same⟩ := computed
    exact ⟨_,result,(compile_iff _ _ _ _ _).mp formed,same⟩
  · rintro ⟨depth,result,formed,rfl⟩
    have computed := (compile_iff _ _ _ _ _).mpr (formation_at_default formed)
    simp only [compileExpression,computed,bind,pure,Option.bind_some]

theorem default_refusal_iff_no_formation (context : Context) (expression : Atom) :
    compileExpression context expression = none ↔
      ∀ depth result, ¬FormationAt context depth (Supply.start [expression]) expression result := by
  constructor
  · intro refused depth result formed
    have successful := (compileExpression_iff_any_formation context expression (normalized result)).mpr
      ⟨depth,result,formed,rfl⟩
    rw [refused] at successful
    cases successful
  · intro none
    cases found : compileExpression context expression with
    | none => rfl
    | some plan =>
        obtain ⟨depth,result,formed,same⟩ := (compileExpression_iff_any_formation context expression plan).mp found
        exact False.elim (none depth result formed)

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
