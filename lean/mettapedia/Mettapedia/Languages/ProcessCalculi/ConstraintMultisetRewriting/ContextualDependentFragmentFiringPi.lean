import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentDecidedIdentity

/-!
# Decomposing dependent function and pair types with one domain

At a universe, `Π A B ≐ Π A B'` has **exactly** the solutions of `B ≐ B'` under a new local of
type `A`, in every future context (`pi_decompose_scoped`); so has `Σ A B ≐ Σ A B'`
(`sigma_decompose_scoped`). The codomain equation sits at the join of
the universes the executable type former finds for `B` and `B'`.

Both directions go through **universe irrelevance**: two types of one universe are equal there
exactly when they are equal types at any universe (`equal_of_typeEq`). This is the conversion
algorithm, complete for type equality and sound at every universe that both types inhabit.
Injectivity of Π and Σ types does the rest (`typeEq_pi_iff`, `typeEq_sigma_iff`). No inhabitation premise is needed.

The decomposed equation is one binder deeper than the original. It is a scoped equation under the
spine followed by the new binder (`scopeWith`), closed with the executable universe joins.

As for the other decompositions, the **binder decomposition** (Π, then Σ) of a store equation
continues at once on the decomposed store with the distinct-locals rule and the pattern rule. The
**Π round** prepares the store, tries the binder decomposition on the prepared store, and otherwise
runs the identity round.
Every refutation is certified and every progress lowers the rank.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentPatternSolver ContextualDependentGeneralPattern
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget
open TypedContextual.QuotientComprehensionSyntax

/-! ## Scoped equations with a scoped body -/

section Scoping

variable {Head : Type} {rules : Rules Head}

/-- A scoped body under the binders of a spine. -/
def scopeWith : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) → Scoped spine.target → Scoped Γ
  | _, _, .stop _, body => body
  | _, _, .bind shape rest, body => .bind shape.domain (scopeWith rest body)

theorem scopeWith_holds_iff {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ (body : Scoped spine.target) {Δ : Context rules} (solution : Δ ⟶ Γ),
      (scopeWith spine body).Holds solution ↔ body.Holds (spine.map solution) := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih => intro body Δ solution; exact ih body (rawLift solution shape.domain)

end Scoping

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Universe irrelevance -/

section Irrelevance

variable [DecidableRel S.R.headEq] (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableRel S.R.headEq] in
include facts roots heads algebra complete in
/-- **Universe irrelevance**: two types of one universe that are equal types are equal at that
universe. -/
theorem equal_of_typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head} (formed : CtxFormed S.R Γ)
    (universal : S.R.isUniverse u) (typedA : Typed S.R Γ A (.head u)) (typedB : Typed S.R Γ B (.head u))
    (same : TypeEq S.R Γ A B) : Equal S.R Γ A B (.head u) :=
  (algorithm_iff_typeEq facts roots heads algebra complete formed universal typedA typedB).mp
    (TypeEq.algorithm complete same formed)

omit [DecidableRel S.R.headEq] in
include facts roots heads algebra complete in
/-- **Dependent function types with one domain decompose**, with exactly the original solutions in
every future context. -/
theorem pi_decompose_scoped {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (equation : Active scope.target) {u : Head} (universal : S.R.isUniverse u)
    (typeCode : equation.type.code = .head u) (domain : TypeOver scope.target)
    (codomain : Active (extend scope.target domain)) {w : Head} (codomainUniverse : S.R.isUniverse w)
    (codomainType : codomain.type.code = .head w)
    (leftCode : equation.left.code = .pi domain.code codomain.left.code)
    (rightCode : equation.right.code = .pi domain.code codomain.right.code)
    {Δ : Context S.R} (solution : Δ ⟶ Γ) :
    (scope.toScoped equation).Holds solution ↔
      (scopeWith scope (.bind domain (.active codomain))).Holds solution := by
  rw [Spine.toScoped_holds_iff, scopeWith_holds_iff]
  have typedLeft := equation.left.typed
  have typedRight := equation.right.typed
  have typedCodLeft := codomain.left.typed
  have typedCodRight := codomain.right.typed
  rw [leftCode, typeCode] at typedLeft
  rw [rightCode, typeCode] at typedRight
  rw [codomainType] at typedCodLeft typedCodRight
  have movedLeft := typedLeft.substitute (scope.map solution).typed
  have movedRight := typedRight.substitute (scope.map solution).typed
  have movedCodLeft := typedCodLeft.substitute ((scope.map solution).typed.lift domain.code)
  have movedCodRight := typedCodRight.substitute ((scope.map solution).typed.lift domain.code)
  have domainTyped := domain.formed.substitute (scope.map solution).typed
  have outerFormed := (scope.reindex solution).target.formed
  have innerFormed := (extend (scope.reindex solution).target (domain.reindex (scope.map solution))).formed
  change Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution equation.left.code)
      (subst (scope.map solution).substitution equation.right.code)
      (subst (scope.map solution).substitution equation.type.code) ↔
    Equal S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.left.code)
      (subst (liftSub (scope.map solution).substitution) codomain.right.code)
      (subst (liftSub (scope.map solution).substitution) codomain.type.code)
  rw [leftCode, rightCode, typeCode, codomainType]
  change Equal S.R (scope.reindex solution).target.raw
      (.pi (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.left.code))
      (.pi (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.right.code)) (.head u) ↔
    Equal S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.left.code)
      (subst (liftSub (scope.map solution).substitution) codomain.right.code) (.head w)
  change Typed S.R (scope.reindex solution).target.raw
      (.pi (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.left.code)) (.head u) at movedLeft
  change Typed S.R (scope.reindex solution).target.raw
      (.pi (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.right.code)) (.head u) at movedRight
  change Typed S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.left.code) (.head w) at movedCodLeft
  change Typed S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.right.code) (.head w) at movedCodRight
  change Typed S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code)
      (.head domain.level) at domainTyped
  constructor
  · intro held
    have codomains := ((ContextualDependentRigid.typeEq_pi_iff facts outerFormed).mp ⟨u, universal, held⟩).2
    exact equal_of_typeEq facts roots heads algebra complete innerFormed codomainUniverse movedCodLeft movedCodRight
      codomains
  · intro held
    have types := (ContextualDependentRigid.typeEq_pi_iff facts outerFormed).mpr
      ⟨⟨domain.level, domain.universeWitness, .refl domainTyped⟩, ⟨w, codomainUniverse, held⟩⟩
    exact equal_of_typeEq facts roots heads algebra complete outerFormed universal movedLeft movedRight types

omit [DecidableRel S.R.headEq] in
include facts roots heads algebra complete in
/-- **Dependent pair types with one first component type decompose**, with exactly the original solutions in
every future context. -/
theorem sigma_decompose_scoped {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (equation : Active scope.target) {u : Head} (universal : S.R.isUniverse u)
    (typeCode : equation.type.code = .head u) (domain : TypeOver scope.target)
    (codomain : Active (extend scope.target domain)) {w : Head} (codomainUniverse : S.R.isUniverse w)
    (codomainType : codomain.type.code = .head w)
    (leftCode : equation.left.code = .sigma domain.code codomain.left.code)
    (rightCode : equation.right.code = .sigma domain.code codomain.right.code)
    {Δ : Context S.R} (solution : Δ ⟶ Γ) :
    (scope.toScoped equation).Holds solution ↔
      (scopeWith scope (.bind domain (.active codomain))).Holds solution := by
  rw [Spine.toScoped_holds_iff, scopeWith_holds_iff]
  have typedLeft := equation.left.typed
  have typedRight := equation.right.typed
  have typedCodLeft := codomain.left.typed
  have typedCodRight := codomain.right.typed
  rw [leftCode, typeCode] at typedLeft
  rw [rightCode, typeCode] at typedRight
  rw [codomainType] at typedCodLeft typedCodRight
  have movedLeft := typedLeft.substitute (scope.map solution).typed
  have movedRight := typedRight.substitute (scope.map solution).typed
  have movedCodLeft := typedCodLeft.substitute ((scope.map solution).typed.lift domain.code)
  have movedCodRight := typedCodRight.substitute ((scope.map solution).typed.lift domain.code)
  have domainTyped := domain.formed.substitute (scope.map solution).typed
  have outerFormed := (scope.reindex solution).target.formed
  have innerFormed := (extend (scope.reindex solution).target (domain.reindex (scope.map solution))).formed
  change Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution equation.left.code)
      (subst (scope.map solution).substitution equation.right.code)
      (subst (scope.map solution).substitution equation.type.code) ↔
    Equal S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.left.code)
      (subst (liftSub (scope.map solution).substitution) codomain.right.code)
      (subst (liftSub (scope.map solution).substitution) codomain.type.code)
  rw [leftCode, rightCode, typeCode, codomainType]
  change Equal S.R (scope.reindex solution).target.raw
      (.sigma (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.left.code))
      (.sigma (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.right.code)) (.head u) ↔
    Equal S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.left.code)
      (subst (liftSub (scope.map solution).substitution) codomain.right.code) (.head w)
  change Typed S.R (scope.reindex solution).target.raw
      (.sigma (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.left.code)) (.head u) at movedLeft
  change Typed S.R (scope.reindex solution).target.raw
      (.sigma (subst (scope.map solution).substitution domain.code)
        (subst (liftSub (scope.map solution).substitution) codomain.right.code)) (.head u) at movedRight
  change Typed S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.left.code) (.head w) at movedCodLeft
  change Typed S.R (.snoc (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code))
      (subst (liftSub (scope.map solution).substitution) codomain.right.code) (.head w) at movedCodRight
  change Typed S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution domain.code)
      (.head domain.level) at domainTyped
  constructor
  · intro held
    have codomains := ((ContextualDependentRigid.typeEq_sigma_iff facts outerFormed).mp ⟨u, universal, held⟩).2
    exact equal_of_typeEq facts roots heads algebra complete innerFormed codomainUniverse movedCodLeft movedCodRight
      codomains
  · intro held
    have types := (ContextualDependentRigid.typeEq_sigma_iff facts outerFormed).mpr
      ⟨⟨domain.level, domain.universeWitness, .refl domainTyped⟩, ⟨w, codomainUniverse, held⟩⟩
    exact equal_of_typeEq facts roots heads algebra complete outerFormed universal movedLeft movedRight types


end Irrelevance

/-! ## The Π decomposition in the solver -/

section Rule

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- The universe of the codomain equation: the common universe of both codomains when the type
former finds the same one, their join otherwise. -/
def codomainUniverse (first second : Head) : Option {w : Head // S.R.cumulative first w ∧ S.R.cumulative second w} :=
  if same : first = second then
    if universal : S.R.isUniverse first then some ⟨first, S.levels.cumulative_refl universal,
      same ▸ S.levels.cumulative_refl universal⟩
    else none
  else (choices.join first second).map fun joined => ⟨joined.val, S.levels.join_upper joined.property⟩

/-- **The Π decomposition of one scoped equation**: the codomain equation under the domain, with
exactly the same solutions. -/
def piDecomposeActive (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    Option {body : Scoped scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (scopeWith scope body).Holds solution} :=
  match leftCode : active.left.code, rightCode : active.right.code, typeCode : active.type.code with
  | .pi A B, .pi A' B', .head u =>
      if same : A' = A then
        if universal : S.R.isUniverse u then
          match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
              scope.target A with
          | none => none
          | some domain =>
              match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                  (extend scope.target domain.val) B,
                ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                  (extend scope.target domain.val) B' with
              | some first, some second =>
                  match codomainUniverse choices first.val.level second.val.level with
                  | none => none
                  | some level =>
                      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                          (extend scope.target domain.val) (.head level.val) with
                      | none => none
                      | some annotation =>
                          let codomain : Active (extend scope.target domain.val) :=
                            ⟨annotation.val,
                              ⟨B, by
                                rw [annotation.property]
                                have formed := first.val.formed
                                rw [first.property] at formed
                                exact .cumul formed level.property.1⟩,
                              ⟨B', by
                                rw [annotation.property]
                                have formed := second.val.formed
                                rw [second.property] at formed
                                exact .cumul formed level.property.2⟩⟩
                          some ⟨.bind domain.val (.active codomain), fun solution =>
                            pi_decompose_scoped facts roots heads algebra complete scope active universal typeCode
                              domain.val codomain (S.levels.cumulative_universe level.property.1).2.1
                              annotation.property (by rw [leftCode, domain.property])
                              (by rw [rightCode, same, domain.property]) solution⟩
              | _, _ => none
        else none
      else none
  | _, _, _ => none

/-- **The Σ decomposition of one scoped equation**: the second component type equation under the first, with
exactly the same solutions. -/
def sigmaDecomposeActive (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    Option {body : Scoped scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (scopeWith scope body).Holds solution} :=
  match leftCode : active.left.code, rightCode : active.right.code, typeCode : active.type.code with
  | .sigma A B, .sigma A' B', .head u =>
      if same : A' = A then
        if universal : S.R.isUniverse u then
          match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
              scope.target A with
          | none => none
          | some domain =>
              match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                  (extend scope.target domain.val) B,
                ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                  (extend scope.target domain.val) B' with
              | some first, some second =>
                  match codomainUniverse choices first.val.level second.val.level with
                  | none => none
                  | some level =>
                      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                          (extend scope.target domain.val) (.head level.val) with
                      | none => none
                      | some annotation =>
                          let codomain : Active (extend scope.target domain.val) :=
                            ⟨annotation.val,
                              ⟨B, by
                                rw [annotation.property]
                                have formed := first.val.formed
                                rw [first.property] at formed
                                exact .cumul formed level.property.1⟩,
                              ⟨B', by
                                rw [annotation.property]
                                have formed := second.val.formed
                                rw [second.property] at formed
                                exact .cumul formed level.property.2⟩⟩
                          some ⟨.bind domain.val (.active codomain), fun solution =>
                            sigma_decompose_scoped facts roots heads algebra complete scope active universal typeCode
                              domain.val codomain (S.levels.cumulative_universe level.property.1).2.1
                              annotation.property (by rw [leftCode, domain.property])
                              (by rw [rightCode, same, domain.property]) solution⟩
              | _, _ => none
        else none
      else none
  | _, _, _ => none


/-- **The binder decomposition of one scoped equation**: Π types, then Σ types. -/
def binderDecomposeActive (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    Option {body : Scoped scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (scopeWith scope body).Holds solution} :=
  (piDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active).or
    (sigmaDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active)

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- A scoped reading with a closed form gives an equivalent store equation in its place. -/
theorem pi_replace_equivalent {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {constraint body : Scoped Θ}
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      (frames S.levels).Models solution [equation] ↔ constraint.Holds solution)
    (split : ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ), constraint.Holds solution ↔ body.Holds solution)
    {closed : Active Θ} (computed : body.closeWith S.levels choices = some closed)
    (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent (equation :: rest) (closed.equation :: rest) := by
  intro Δ solution
  have first : (frames S.levels).Models solution [equation] ↔ (frames S.levels).Models solution [closed.equation] :=
    (view solution).trans ((split solution).trans ((Scoped.closeWith_holds_iff S.levels choices body computed
      solution).symm.trans (Active.holds_iff_models S.levels closed solution)))
  have whole := Frames.models_append (X := frames S.levels) solution [equation] rest
  have whole' := Frames.models_append (X := frames S.levels) solution [closed.equation] rest
  exact whole.trans ((and_congr_left fun _ => first).trans whole'.symm)

/-- **The Π decomposition of one store equation**, continued on the decomposed store by the
distinct-locals rule and the pattern rule. -/
def piDecomposeEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (Found (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match binderDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active with
      | none => none
      | some ⟨body, split⟩ =>
          match computed : (scopeWith scope body).closeWith S.levels choices with
          | none => none
          | some closed =>
              let moved : Update S.levels (equation :: rest) :=
                (Update.pending S.levels (closed.equation :: rest)).rephrase
                  (pi_replace_equivalent choices view split computed rest)
              match ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
                  choices reducer root fuel (closed.equation :: rest) with
              | some absent => some (.refuted fun solvable => absent.down (moved.solvable_iff.mp solvable))
              | none =>
                  match patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                      certifyNormal fuel (closed.equation :: rest) with
                  | some (.solved solved smaller) => some (.solved (moved.then solved) smaller)
                  | some (.refuted absent) => some (.refuted fun solvable => absent (moved.solvable_iff.mp solvable))
                  | none => none

/-- Search the store for an equation on which the Π decomposition decides. -/
def piDecomposeSearch (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match piDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal fuel equation rest with
      | some found => some found
      | none => (piDecomposeSearch fuel rest).map (Found.keepLeft equation)

variable (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **One Π round**: prepare, decompose a Π equation when that decides, and otherwise run the identity
round. -/
def piRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  match piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
  | some (.solved update smaller) =>
      .progress ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)
        (Prod.Lex.left _ _ (by
          have same := prepare_arity facts roots heads root rootComplete fuel problem
          change update.target.arity < Θ.arity
          omega))
  | some (.refuted absent) =>
      .refuted fun solvable =>
        absent ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).solvable_iff.mp
          solvable)
  | none => identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem

/-- **The Π solver** at one budget. -/
def piSolver (fuel : Nat) : Solver S.levels where
  rank := size
  round := piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
    headTypingUnique rootComplete fuel

/-- **The Π solver as a fuel-indexed family.** -/
def piFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
    headTypingUnique rootComplete fuel

end Rule

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
