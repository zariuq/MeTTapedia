import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Translation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Controls

/-!
# The translated proof computes reflexivity at every numeral

At a numeral `m`, the linked source proof of `zero-add` runs, in the draft's
program, to `refl m`.

* The induction realization hands `m` to the recursor, which unfolds it.
* At each successor, the linked induction step calls the substitution
  realization, which eliminates the incoming identity proof.  The point
  `add zero k` computes to the endpoint `k`, and the incoming proof computes to
  `refl k`, so identity elimination fires, even under the draft's rule that
  compares the point, the endpoint and the witness syntactically.
* It returns the reflexivity realization at `suc (add zero k)`, which computes
  to `refl (suc k)`.

The successor unfolding is computed once at open variables and then
instantiated.  With preservation, every intermediate term of these runs keeps
the type `eqAt m` in the linearized profile.  In the profile over the draft's
program itself, the call and its value `refl m` are both typed at `eqAt m`, and
every run of the call that stops, stops at `refl m`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Evaluation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence Presentation.AlgebraicParallel
open SetProfile (numTy holdsName zeroNative sucNative addNative eqNumNative)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Execution
open CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Realizations
open CertifiedTransformProgram.IdentityEquality.Translation
open Presentation.ConstructorSystem (Normal)

/-- Runs are closed under substitution. -/
theorem runs_substitute {n m : Nat} (σ : Sub Tower.Head n m) {source target : Tower.Tm n}
    (runs : Runs source target) : Runs (subst σ source) (subst σ target) :=
  stepStar_map (subst σ) (fun step => step.substitute σ) runs

/-- The predicate of `zero-add`, `λ k. add zero k = k`. -/
abbrev predicate {n : Nat} : Tower.Tm n := .lam (eqNumNative (addNative zeroNative (.var 0)) (.var 0))

/-- The recursor's motive at that predicate. -/
abbrev family : Tower.Tm 0 := .lam (Holds (.app predicate (.var 0)))

/-- The linked base case `refl@ zero`. -/
abbrev base : Tower.Tm 0 := .app reflRealization zeroNative

/-- The linked induction step. -/
def linkedStep : Tower.Tm 0 := ConstantExpansion.expand linking zeroAddStepTerm

/-- The recursion the induction realization starts at a numeral. -/
def recursion (count : Nat) : Tower.Tm 0 := numRecApp family base linkedStep (numeral count)

/-- The linked proof applied to a numeral is the recursion at it. -/
theorem linked_unfolds (count : Nat) :
    Runs (.app linkedZeroAdd (numeral count)) (recursion count) := by
  refine (Runs.app (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl) .refl).trans ?_
  refine (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl).trans ?_
  refine (Runs.app (Runs.beta _ _) .refl).trans ?_
  exact Runs.beta _ _

/-- The step at an open index `k` and an open incoming proof `h`, unfolded to
identity elimination: `id:eliminate num (add zero k) (λ y p. Holds (Q y))
(refl@ (suc (add zero k))) k h`, with `Q y` the proposition
`suc (add zero k) = suc y`. -/
def stepElimination : Tower.Tm 2 :=
  jApp numT (addNative zeroNative (.var 1))
    (.lam (.lam (Holds (.app (.lam (eqNumNative (sucNative (addNative zeroNative (.var 4)))
      (sucNative (.var 0)))) (.var 1)))))
    (.app (liftClosed reflRealization) (sucNative (addNative zeroNative (.var 1)))) (.var 1) (.var 0)

theorem step_unfolds :
    Runs (app2 (liftClosed linkedStep) (.var 1) (.var 0) : Tower.Tm 2) stepElimination := by
  refine (Runs.app (Runs.beta _ _) .refl).trans ?_
  refine (Runs.beta _ _).trans ?_
  refine (Runs.app (Runs.app (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl) .refl) .refl).trans ?_
  refine (Runs.app (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl) .refl).trans ?_
  refine (Runs.app (Runs.app (Runs.beta _ _) .refl) .refl).trans ?_
  refine (Runs.app (Runs.beta _ _) .refl).trans ?_
  exact Runs.beta _ _

/-- The recursion at every numeral computes reflexivity. -/
theorem recursion_runs : ∀ count : Nat, Runs (recursion count) (.refl (numeral count))
  | 0 =>
      (Runs.equation listed_numRecZero (patternValues ![family, base, linkedStep])).trans
        (Runs.beta _ _)
  | count + 1 => by
      have unfold := Runs.equation listed_numRecSuc
        (patternValues ![family, base, linkedStep, numeral count])
      have step := runs_substitute (patternValues ![numeral count, recursion count]) step_unfolds
      have point := add_zero_numeral (n := 0) count
      have method : Runs (.app reflRealization (sucNative (addNative zeroNative (numeral count))))
          (.refl (numeral (count + 1))) :=
        (Runs.beta _ _).trans (Runs.reflexivity (Runs.app .refl point))
      refine unfold.trans (step.trans ?_)
      refine (Runs.app (Runs.app (Runs.app (Runs.app (Runs.app .refl point) .refl) .refl) .refl)
        (recursion_runs count)).trans ?_
      exact (Runs.equation listed_jIota (patternValues ![numT, numeral count, _, _])).trans method

/-- At every numeral `m`, the linked source proof applied to `m` runs to
`refl m`. -/
theorem linkedZeroAdd_runs (count : Nat) :
    Runs (.app linkedZeroAdd (numeral count)) (.refl (numeral count)) :=
  (linked_unfolds count).trans (recursion_runs count)

/-- The call is typed at `eqAt m`, and so is every term it runs to. -/
theorem linkedZeroAdd_closed_typed (count : Nat) :
    Typing identityRules .nil (.app linkedZeroAdd (numeral count)) (eqAtApp (numeral count)) :=
  Typing.conv (Typing.appElim linkedZeroAdd_decoded (toIdentity (numeral_typed count)))
    (toIdentity (eqAt_typed (numeral_typed count))) (isUniverseAt Tower.zero)
    (.symm _ _ (toIdentity_conversion (package_step listed_eqAt (at1 (numeral count)))))

theorem linkedZeroAdd_runs_typed (count : Nat) {target : Tower.Tm 0}
    (runs : StepStar identityRules (.app linkedZeroAdd (numeral count)) target) :
    Judgment Metatheory.identityLinearRules .nil target (eqAtApp (numeral count)) :=
  Metatheory.runs_preserve ⟨.nil, linkedZeroAdd_closed_typed count⟩ runs

/-- Runs of the draft's program are runs of the profile over it. -/
theorem runs_toIdentity {n : Nat} {source target : Tower.Tm n} (runs : Runs source target) :
    StepStar identityRules source target := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih =>
      refine .tail ih ?_
      simpa only [Tm.mapHead_id] using
        StepCore.mapHead (fun head => head) packageToIdentity.headEq packageToIdentity.computation step

/-- `refl m` has no step. -/
theorem refl_numeral_normal (count : Nat) :
    Normal Metatheory.identityLinearRules (.refl (numeral count) : Tower.Tm 0) := by
  intro target step
  cases step with
  | root rootStep => exact Metatheory.identityConstructors.no_root_of_spineHead rootStep rfl
  | congRefl inner =>
      exact CertifiedTransformProgram.IdentityEquality.Controls.numeral_normal count inner

/-- `refl m` is typed at `eqAt m` in the profile over the draft's program. -/
theorem refl_numeral_typed (count : Nat) :
    Typing identityRules .nil (.refl (numeral count)) (eqAtApp (numeral count)) :=
  Typing.conv (toIdentity (Typing.reflIntro (numeral_typed count)))
    (toIdentity (eqAt_typed (numeral_typed count))) (isUniverseAt Tower.zero)
    (.symm _ _ (toIdentity_conversion (.trans _ _ _ (package_step listed_eqAt (at1 (numeral count)))
      (Runs.conv (Runs.identity .refl (add_zero_numeral count) .refl)))))

/-- Every run of the call in the profile over the draft's program that stops,
stops at `refl m`. -/
theorem linkedZeroAdd_result (count : Nat) {result : Tower.Tm 0}
    (runs : StepStar identityRules (.app linkedZeroAdd (numeral count)) result)
    (stopped : Normal identityRules result) : result = .refl (numeral count) :=
  Metatheory.stopped_unique ⟨.nil, linkedZeroAdd_closed_typed count⟩ runs stopped
    (runs_toIdentity (linkedZeroAdd_runs count))
    (Metatheory.identityDraft.normal_of_host (refl_numeral_normal count))

#print axioms step_unfolds
#print axioms recursion_runs
#print axioms linkedZeroAdd_runs
#print axioms linkedZeroAdd_closed_typed
#print axioms linkedZeroAdd_runs_typed
#print axioms refl_numeral_typed
#print axioms linkedZeroAdd_result

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Evaluation
