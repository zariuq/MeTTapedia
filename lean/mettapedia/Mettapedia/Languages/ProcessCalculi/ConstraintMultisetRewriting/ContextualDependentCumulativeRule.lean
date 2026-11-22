import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeRetype
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEtaRound

/-!
# The cumulative argument

`λ x. F x ≐ λ x. N` at `Π U_v C`, where the newest metavariable `F` declares `Π U_u E` and `U_v` lies below `U_u`.
The equation's local is declared `U_v`, `F`'s binder `U_u`, so recognition, which needs the local's declared type to
be `F`'s binder, does not read it.

**The rule.** The equation is read under its abstraction (`viewEquation`). The local is retyped to `U_u`: the
annotation and both sides are checked as the same codes under `y : U_u` (`retypeAt`), and then the scoped equation has
exactly the solutions of the original one (`retype_holds_iff`, from narrowing reflection). The retyped equation is an
ordinary pattern; R107's conversion pattern step solves or refutes it (`cumulativeActive`). In both orientations, through
the store, at the newest declaration (`cumulativeRule`).

**The rank.** A solution removes `F`, so the arity drops, and the weight rank with it (`below_of_arity`).

The **cumulative round** is the flexible-base round, and when that round is stuck, the cumulative rule on the store as
it is (`cumulativeRound`). It is conservative over the flexible-base round, eventually constant, and settles where it is
not stuck.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulative

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentRecognitionConversion
open ContextualDependentSpineEta ContextualDependentPruneSolve

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-! ## Retyping the local -/

/-- A checked code, as a term of its type. -/
def ofChecked {C : Context S.R} (type : TypeOver C) (code : Tm Head C.arity)
    (checked : Option (ExecutableChecking.CheckResult S.R C.raw code type.code)) :
    Option {term : Term C type // term.code = code} :=
  match checked with
  | some checked =>
      some ⟨⟨code, CheckingAlgorithm.sound (S := S) facts roots heads algebra declared checked.down C.formed
        type.isType⟩, rfl⟩
  | none => none

/-- A code checked as a term of a type, at the budget. -/
def checkAt (fuel : Nat) {C : Context S.R} (type : TypeOver C) (code : Tm Head C.arity) :
    Option {term : Term C type // term.code = code} :=
  ofChecked facts roots heads algebra declared type code (ExecutableChecking.check S.R choices reducer fuel C.raw code type.code)

/-- The local and the opened equation of a reading under exactly one abstraction. -/
def oneBinder : {Θ : Context S.R} → {whole : TypeOver Θ} → (scope : Spine whole) → (active : Active scope.target) →
    Option ((domain : TypeOver Θ) × (opened : Active (extend Θ domain)) ×'
      ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (scope.toScoped active).Holds σ ↔ (Scoped.bind domain (.active opened)).Holds σ)
  | _, _, .bind shape (.stop _), active => some ⟨shape.domain, active, fun _ => Iff.rfl⟩
  | _, _, .stop _, _ => none
  | _, _, .bind _ _, _ => none

/-- **Retype a universe local to a universe above it**: the annotation and both sides are checked as the same codes
under the larger universe, and the scoped equation keeps its solutions. -/
def retypeAt (fuel : Nat) {Θ : Context S.R} (domain : TypeOver Θ) (opened : Active (extend Θ domain)) (u : Head) :
    Option ((binder : TypeOver Θ) × (retyped : Active (extend Θ binder)) ×'
      ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
        (Scoped.bind domain (.active opened)).Holds σ ↔ (Scoped.bind binder (.active retyped)).Holds σ) :=
  match codeD : domain.code with
  | .head v =>
      if lower : S.R.cumulative v u then
        match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ (.head u) with
        | none => none
        | some binder =>
            match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                (extend Θ binder.1) opened.type.code with
            | none => none
            | some annotation =>
                match checkAt facts roots heads algebra declared choices reducer fuel annotation.1 opened.left.code,
                    checkAt facts roots heads algebra declared choices reducer fuel annotation.1 opened.right.code with
                | some left, some right =>
                    some ⟨binder.1, ⟨annotation.1, left.1, right.1⟩, fun σ =>
                      retype_holds_iff facts roots heads algebra rigid complete domain binder.1 codeD binder.2 lower
                        opened ⟨annotation.1, left.1, right.1⟩ left.2 right.2 annotation.2 σ⟩
                | _, _ => none
      else none
  | _ => none

/-! ## The rule -/

/-- **The cumulative rule on one scoped reading**: retype the local to `F`'s binder, then the conversion pattern step. -/
def cumulativeActive (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) {whole : TypeOver (extend Γ type)}
    (scope : Spine whole) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) : Option (Found (equation :: rest)) :=
  match type.code with
  | .pi (.head u) _ =>
      match oneBinder scope active with
      | none => none
      | some ⟨domain, opened, readOpened⟩ =>
          match retypeAt facts roots heads algebra rigid complete declared choices reducer fuel domain opened u with
          | none => none
          | some ⟨binder, retyped, same⟩ =>
              match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                  (extend Γ type) (.pi binder.code retyped.type.code) with
              | none => none
              | some whole' =>
                  tryActiveConv facts roots heads algebra declared choices reducer rigid complete normalizes
                    certifyNormal fuel type (Spine.bind ⟨binder, retyped.type, whole'.1, whole'.2⟩ (.stop retyped.type))
                    retyped equation (fun solution => (view solution).trans ((readOpened solution).trans
                      (same solution))) rest
  | _ => none

/-- The cumulative rule on one store equation, in both orientations. -/
def cumulativeEquation (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type))) :
    Option (Found (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match cumulativeActive facts roots heads algebra rigid complete declared choices reducer normalizes certifyNormal
          fuel type scope active equation view rest with
      | some found => some found
      | none =>
          cumulativeActive facts roots heads algebra rigid complete declared choices reducer normalizes certifyNormal
            fuel type scope ⟨active.type, active.right, active.left⟩ equation
            (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest

/-- Search the store for an equation on which the cumulative rule decides. -/
def cumulativeSearch (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    (problem : EquationStore (TotalTerm (extend Γ type))) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match cumulativeEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal fuel type equation rest with
      | some found => some found
      | none => (cumulativeSearch fuel type rest).map (Found.keepLeft equation)

/-- **The cumulative rule** at the newest declaration. -/
def cumulativeRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some view => throughNewest view problem
      (cumulativeSearch facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        fuel view.type)

/-! ## The round -/

/-- **One cumulative round**: the flexible-base round; when it is stuck, the cumulative rule on the store as it is. -/
def cumulativeRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match cumulativeRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal fuel problem with
      | some (.solved update smaller) => .progress update (below_of_arity facts roots heads algebra rigid complete smaller)
      | some (.refuted absent) => .refuted absent
      | none => .stuck
  | other => other

/-- **The cumulative family**, at the weight rank. -/
noncomputable def cumulativeFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

end ContextualDependentCumulative
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
