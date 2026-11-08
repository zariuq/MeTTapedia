import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralAnywhere
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongWeakening

/-!
# Intersection behind a dead binder

In-place intersection strengthens the intersected equation past the declarations after the metavariable. An equation
whose annotation mentions one of them cannot be strengthened, even when the mention sits in the type of a binder that
neither the bodies nor the codomain use, as in

  `λ p x y. F x y ≐ λ p x y. F y x` at `Π (p : Id (F A A) b b). Π (x y : U0). U0`, with `b : F A A`

(`ContextualDependentIntersectionGeneral.AnywhereControls.annotated_gap`).

**A dead binder** (`DeadBinder`) is an equation of abstractions at one Π type whose bodies and codomain are read without
the bound variable. Dropping it

* keeps the solutions where typed equality strengthens past an unused variable (`EqualStrengthening`, a property of the
  rule package that the tower has): the binder comes back by weakening and congruence (`solves_of_reduced`), and goes
  by application to the bound variable, β and strengthening (`reduced_of_solves`);
* keeps the normal weight, since an abstraction weighs what its body weighs (`equationWeight_dead`).

The binder is read by the checker (`openAbstraction`: the binder's type and the codomain formed, the body typed by
inversion) and R86's strengthening of both bodies (`deadBinder`). **The dead-binder rule** (`deadRule`) drops the dead
binder of the first equation of each rotation of the store and runs in-place intersection there; the progress is a
progress of the store (`undead`, `unrotate`). The **dead-binder family** runs the anywhere round, then this rule; it is
conservative (`dead_run_of_anywhere`) and eventually constant (`deadRound_const`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentEtaLong
open ContextualDependentIntersection ContextualDependentDynamicFragment ContextualDependentInPlace

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Strengthening of typed equality past an unused variable**, a property of the rule package. -/
def EqualStrengthening (R : Rules Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {D : Tm Head n}, CtxFormed R (.snoc Γ D) → ∀ {t u A : Tm Head n},
    Typed R Γ t A → Typed R Γ u A →
      Equal R (.snoc Γ D) (Presentation.rename wk t) (Presentation.rename wk u) (Presentation.rename wk A) →
        Equal R Γ t u A

/-- **A dead binder**: an equation of abstractions at one Π type, read without the bound variable, which neither the
codomain nor the bodies mention. -/
structure DeadBinder {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  reduced : Equation (TotalTerm Θ)
  domain : Tm Head Θ.arity
  sameType : reduced.2.1.code = reduced.1.1.code
  leftType : equation.1.1.code = .pi domain (Presentation.rename wk reduced.1.1.code)
  rightType : equation.2.1.code = .pi domain (Presentation.rename wk reduced.1.1.code)
  leftTerm : equation.1.2.code = .lam (Presentation.rename wk reduced.1.2.code)
  rightTerm : equation.2.2.code = .lam (Presentation.rename wk reduced.2.2.code)

/-! ## The solutions -/

section Equivalence

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)

/-- **The binder can come back**: solving the reduced equation solves the equation. -/
theorem solves_of_reduced {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (dead : DeadBinder equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) (solved : (frames S.levels).Solves σ dead.reduced) :
    (frames S.levels).Solves σ equation := by
  obtain ⟨_, equal⟩ := solved
  change Equal S.R Δ.raw (subst σ.substitution dead.reduced.1.2.code) (subst σ.substitution dead.reduced.2.2.code)
      (subst σ.substitution dead.reduced.1.1.code) at equal
  change TypeEq S.R Δ.raw (subst σ.substitution equation.1.1.code) (subst σ.substitution equation.2.1.code) ∧
    Equal S.R Δ.raw (subst σ.substitution equation.1.2.code) (subst σ.substitution equation.2.2.code)
      (subst σ.substitution equation.1.1.code)
  have formed := (equation.1.1.reindex σ).formed
  have universe' := (equation.1.1.reindex σ).universeWitness
  refine ⟨by rw [dead.rightType, ← dead.leftType]; exact (equation.1.1.reindex σ).isType.refl, ?_⟩
  change Typed S.R Δ.raw (subst σ.substitution equation.1.1.code) _ at formed
  rw [dead.leftType] at formed ⊢
  rw [dead.leftTerm, dead.rightTerm]
  change Equal S.R Δ.raw (.lam (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.1.2.code)))
    (.lam (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.2.2.code)))
    (.pi (subst σ.substitution dead.domain)
      (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.1.1.code)))
  change Typed S.R Δ.raw (.pi (subst σ.substitution dead.domain)
    (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.1.1.code))) _ at formed
  rw [subst_liftSub_wk, subst_liftSub_wk, subst_liftSub_wk]
  rw [subst_liftSub_wk] at formed
  exact Derivable.lamCong formed universe' (Equal.weaken equal)

include facts roots in
/-- **The binder can go**, where typed equality strengthens past an unused variable. -/
theorem reduced_of_solves (strengthening : EqualStrengthening S.R) {Θ : Context S.R}
    {equation : Equation (TotalTerm Θ)} (dead : DeadBinder equation) {Δ : Context S.R} (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ equation) : (frames S.levels).Solves σ dead.reduced := by
  obtain ⟨_, equal⟩ := solved
  change Equal S.R Δ.raw (subst σ.substitution equation.1.2.code) (subst σ.substitution equation.2.2.code)
      (subst σ.substitution equation.1.1.code) at equal
  have isPi := (equation.1.1.reindex σ).isType
  change IsType S.R Δ.raw (subst σ.substitution equation.1.1.code) at isPi
  rw [dead.leftType] at isPi equal
  rw [dead.leftTerm, dead.rightTerm] at equal
  change Equal S.R Δ.raw (.lam (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.1.2.code)))
    (.lam (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.2.2.code)))
    (.pi (subst σ.substitution dead.domain)
      (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.1.1.code))) at equal
  change IsType S.R Δ.raw (.pi (subst σ.substitution dead.domain)
    (subst (liftSub σ.substitution) (Presentation.rename wk dead.reduced.1.1.code))) at isPi
  rw [subst_liftSub_wk, subst_liftSub_wk, subst_liftSub_wk] at equal
  rw [subst_liftSub_wk] at isPi
  have domainType : IsType S.R Δ.raw (subst σ.substitution dead.domain) := (IsType.pi_parts isPi).1
  have formedExt : CtxFormed S.R (.snoc Δ.raw (subst σ.substitution dead.domain)) := Δ.formed.snoc domainType
  have weakened := Equal.weaken (extension := subst σ.substitution dead.domain) equal
  have applied := Derivable.appCong weakened (.refl (Derivable.var 0))
  change Equal S.R _ _ _ (inst0 (.var 0) (Presentation.rename (liftRen wk)
    (Presentation.rename wk (subst σ.substitution dead.reduced.1.1.code)))) at applied
  rw [inst0_var_rename_liftRen_wk] at applied
  have left := (WhRed.preserve facts roots formedExt (whRed_eta_lam (R := S.R) (roles := S.roles)
    (Presentation.rename wk (subst σ.substitution dead.reduced.1.2.code))) (Equal.typed applied formedExt).1).2
  have right := (WhRed.preserve facts roots formedExt (whRed_eta_lam (R := S.R) (roles := S.roles)
    (Presentation.rename wk (subst σ.substitution dead.reduced.2.2.code))) (Equal.typed applied formedExt).2).2
  have body := left.symm.trans (applied.trans right)
  have typedLeft := (dead.reduced.1.2.reindex σ).typed
  have typedRight := (dead.reduced.2.2.reindex σ).typed
  change Typed S.R Δ.raw (subst σ.substitution dead.reduced.1.2.code) (subst σ.substitution dead.reduced.1.1.code)
    at typedLeft
  change Typed S.R Δ.raw (subst σ.substitution dead.reduced.2.2.code) (subst σ.substitution dead.reduced.2.1.code)
    at typedRight
  rw [dead.sameType] at typedRight
  refine ⟨?_, strengthening formedExt typedLeft typedRight body⟩
  change TypeEq S.R Δ.raw (subst σ.substitution dead.reduced.1.1.code) (subst σ.substitution dead.reduced.2.1.code)
  rw [dead.sameType]
  exact (dead.reduced.1.1.reindex σ).isType.refl

end Equivalence

/-! ## The weight -/

section Weights

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **Dropping a dead binder keeps the normal weight of a side**: an abstraction weighs what its body weighs. -/
theorem sideWeight_dead {Θ : Context S.R} (term strong : TotalTerm Θ) (domain : Tm Head Θ.arity)
    (typeCode : term.1.code = .pi domain (Presentation.rename wk strong.1.code))
    (termCode : term.2.code = .lam (Presentation.rename wk strong.2.code)) :
    sideWeight facts roots heads algebra rigid complete term =
      sideWeight facts roots heads algebra rigid complete strong := by
  obtain ⟨v, normal⟩ := long_exists facts roots heads algebra rigid complete Θ.formed strong.2.typed
  have isPi : IsType S.R Θ.raw term.1.code := term.1.isType
  have formedPi : Typed S.R Θ.raw term.1.code (.head term.1.level) := term.1.formed
  rw [typeCode] at isPi formedPi
  have domainType : IsType S.R Θ.raw domain := (IsType.pi_parts isPi).1
  have typedV : Typed S.R Θ.raw v strong.1.code := (Equal.typed normal.2 Θ.formed).2
  have normalLam : NormalForm S.R S.roles Θ.raw term.2.code (.lam (Presentation.rename wk v)) term.1.code := by
    rw [typeCode, termCode]
    exact ⟨Long.lam (IsType.refl isPi) domainType
        (Derivable.lamIntro formedPi term.1.universeWitness (Typed.weaken typedV))
        (Long.term_weaken facts normal.1 Θ.formed domainType),
      Derivable.lamCong formedPi term.1.universeWitness (Equal.weaken normal.2)⟩
  rw [sideWeight_eq facts roots heads algebra rigid complete term normalLam,
    sideWeight_eq facts roots heads algebra rigid complete strong normal]
  simp only [weight, weight_rename]

/-- **Dropping a dead binder keeps the normal weight of the equation.** -/
theorem equationWeight_dead {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (dead : DeadBinder equation) :
    equationWeight facts roots heads algebra rigid complete equation =
      equationWeight facts roots heads algebra rigid complete dead.reduced := by
  unfold equationWeight
  rw [sideWeight_dead facts roots heads algebra rigid complete equation.1 dead.reduced.1 dead.domain dead.leftType
      dead.leftTerm,
    sideWeight_dead facts roots heads algebra rigid complete equation.2 dead.reduced.2 dead.domain
      (dead.rightType.trans (by rw [dead.sameType])) dead.rightTerm]

end Weights

/-! ## Reading a dead binder -/

section Reading

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- A judged abstraction at a Π type, read as its body over the binder. -/
structure Opened {Θ : Context S.R} (term : TotalTerm Θ) where
  domain : TypeOver Θ
  body : TotalTerm (extend Θ domain)
  typeCode : term.1.code = .pi domain.code body.1.code
  termCode : term.2.code = .lam body.2.code

/-- The opened abstraction, once both types are formed. -/
def openedOf {Θ : Context S.R} (term : TotalTerm Θ) {P : Tm Head Θ.arity} {C M : Tm Head (Θ.arity + 1)}
    (typeCode : term.1.code = .pi P C) (termCode : term.2.code = .lam M)
    (domain : {type : TypeOver Θ // type.code = P})
    (codomain : {type : TypeOver (extend Θ domain.val) // type.code = C}) : Opened term where
  domain := domain.val
  body := ⟨codomain.val, ⟨M, by
    have typed := term.2.typed
    rw [typeCode, termCode] at typed
    have inv := Typed.lam_inv facts typed Θ.formed
    change Typed S.R (.snoc Θ.raw domain.val.code) M codomain.val.code
    rw [domain.property, codomain.property]
    exact inv⟩⟩
  typeCode := typeCode.trans (by
    show Tm.pi P C = Tm.pi domain.val.code codomain.val.code
    rw [domain.property, codomain.property])
  termCode := termCode

/-- Open an abstraction whose codes are read, forming the binder's type and the body's type by the checker. -/
def openWith (fuel : Nat) {Θ : Context S.R} (term : TotalTerm Θ) {P : Tm Head Θ.arity}
    {C M : Tm Head (Θ.arity + 1)} (typeCode : term.1.code = .pi P C) (termCode : term.2.code = .lam M) :
    Option (Opened term) :=
  match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ P with
  | none => none
  | some domain =>
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
        (extend Θ domain.val) C).map (openedOf facts term typeCode termCode domain)

/-- **Open an abstraction at a Π type**, at each budget. -/
def openAbstraction {Θ : Context S.R} (term : TotalTerm Θ) : Nat → Option (Opened term) :=
  match typeCode : term.1.code, termCode : term.2.code with
  | .pi _ _, .lam _ => fun fuel =>
      openWith facts roots heads algebra declared choices reducer fuel term typeCode termCode
  | _, _ => fun _ => none

/-- The dead binder, once both bodies are strengthened. -/
def deadOf {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (left : Opened equation.1) (right : Opened equation.2)
    (l : {strong : TotalTerm Θ // Presentation.rename wk strong.1.code = left.body.1.code ∧
      Presentation.rename wk strong.2.code = left.body.2.code})
    (r : {strong : TotalTerm Θ // Presentation.rename wk strong.1.code = right.body.1.code ∧
      Presentation.rename wk strong.2.code = right.body.2.code}) : Option (DeadBinder equation) :=
  if same : r.val.1.code = l.val.1.code ∧ right.domain.code = left.domain.code then
    some
      { reduced := (l.val, r.val)
        domain := left.domain.code
        sameType := same.1
        leftType := left.typeCode.trans (congrArg _ l.property.1.symm)
        rightType := right.typeCode.trans
          (congrArg₂ Tm.pi same.2 (r.property.1.symm.trans (congrArg _ same.1)))
        leftTerm := left.termCode.trans (congrArg _ l.property.2.symm)
        rightTerm := right.termCode.trans (congrArg _ r.property.2.symm) }
  else none

/-- Strengthen both opened bodies past their binders. -/
def deadOfOpened (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} :
    Option (Opened equation.1) × Option (Opened equation.2) → Option (DeadBinder equation)
  | (some left, some right) =>
      match strengthen facts roots heads algebra declared choices reducer fuel left.domain left.body,
          strengthen facts roots heads algebra declared choices reducer fuel right.domain right.body with
      | some l, some r => deadOf left right l r
      | _, _ => none
  | _ => none

/-- **Read a dead binder off an equation**: open both sides and strengthen both bodies past the binder. -/
def deadBinder (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (DeadBinder equation) :=
  deadOfOpened facts roots heads algebra declared choices reducer fuel
    (openAbstraction facts roots heads algebra declared choices reducer equation.1 fuel,
      openAbstraction facts roots heads algebra declared choices reducer equation.2 fuel)

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem openWith_const {Θ : Context S.R} (term : TotalTerm Θ) {P : Tm Head Θ.arity} {C M : Tm Head (Θ.arity + 1)}
    (typeCode : term.1.code = .pi P C) (termCode : term.2.code = .lam M) :
    EventuallyConst fun fuel => openWith facts roots heads algebra declared choices reducer fuel term typeCode termCode :=
  EventuallyConst.dep (h := fun fuel =>
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ P)
    (k := fun fuel domain => match domain with
      | none => none
      | some domain =>
          (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
            (extend Θ domain.val) C).map (openedOf facts term typeCode termCode domain))
    (ContextualDependentDecisiveFragment.formType_const facts roots heads algebra declared choices reducer stable P)
    (fun domain => by
      cases domain with
      | none => exact EventuallyConst.const _
      | some domain =>
          exact EventuallyConst.comp (Option.map (openedOf facts term typeCode termCode domain))
            (ContextualDependentDecisiveFragment.formType_const facts roots heads algebra declared choices reducer stable
              (Γ := extend Θ domain.val) C))

include stable in
theorem openAbstraction_const {Θ : Context S.R} (term : TotalTerm Θ) :
    EventuallyConst (openAbstraction facts roots heads algebra declared choices reducer term) := by
  unfold openAbstraction
  split
  · exact openWith_const facts roots heads algebra declared choices reducer stable term _ _
  · exact EventuallyConst.const _

include stable in
/-- **Reading a dead binder is eventually constant.** -/
theorem deadBinder_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => deadBinder facts roots heads algebra declared choices reducer fuel equation :=
  EventuallyConst.dep
    (EventuallyConst.pair (openAbstraction_const facts roots heads algebra declared choices reducer stable equation.1)
      (openAbstraction_const facts roots heads algebra declared choices reducer stable equation.2))
    (fun opened => by
      rcases opened with ⟨_ | left, _ | right⟩
      · exact EventuallyConst.const _
      · exact EventuallyConst.const _
      · exact EventuallyConst.const _
      · refine EventuallyConst.of_eq (fun fuel => ?_) (EventuallyConst.comp
          (fun pair : Option {strong : TotalTerm Θ // Presentation.rename wk strong.1.code = left.body.1.code ∧
              Presentation.rename wk strong.2.code = left.body.2.code} ×
            Option {strong : TotalTerm Θ // Presentation.rename wk strong.1.code = right.body.1.code ∧
              Presentation.rename wk strong.2.code = right.body.2.code} => match pair with
            | (some l, some r) => deadOf left right l r
            | _ => none)
          (EventuallyConst.pair (ContextualDependentInPlace.strengthen_const facts roots heads algebra declared choices
              reducer stable left.domain left.body)
            (ContextualDependentInPlace.strengthen_const facts roots heads algebra declared choices reducer stable
              right.domain right.body)))
        simp only [deadOfOpened]
        cases strengthen facts roots heads algebra declared choices reducer fuel left.domain left.body <;>
          cases strengthen facts roots heads algebra declared choices reducer fuel right.domain right.body <;> rfl)

end Reading

/-! ## The rule, the round, the family -/

section Rule

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
  (strengthening : EqualStrengthening S.R)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts roots strengthening in
/-- **Dropping a dead binder keeps the solutions of the store.** -/
theorem equivalent_dead {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (dead : DeadBinder equation) : (frames S.levels).Equivalent (equation :: rest) (dead.reduced :: rest) := by
  intro Δ σ
  rw [models_cons, models_cons]
  exact and_congr ⟨reduced_of_solves facts roots strengthening dead σ, solves_of_reduced dead σ⟩ Iff.rfl

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **Dropping a dead binder keeps the weight of the store.** -/
theorem storeWeight_dead {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (dead : DeadBinder equation) :
    storeWeight facts roots heads algebra rigid complete (dead.reduced :: rest) =
      storeWeight facts roots heads algebra rigid complete (equation :: rest) := by
  simp only [storeWeight, equationWeight_dead facts roots heads algebra rigid complete dead]

/-- **A sited progress of the store read without the dead binder is a sited progress of the store.** -/
def undead {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (dead : DeadBinder equation)
    (found : SitedProgress facts roots heads algebra rigid complete (dead.reduced :: rest)) :
    SitedProgress facts roots heads algebra rigid complete (equation :: rest) :=
  ⟨found.val.rephrase (equivalent_dead facts roots strengthening dead), by
    have lower : ContextualDependentWorklist.Below
        (weightRank facts roots heads algebra rigid complete found.val.remaining)
        (Θ.arity, storeWeight facts roots heads algebra rigid complete (dead.reduced :: rest)) := found.property.1
    rw [storeWeight_dead facts roots heads algebra rigid complete rest dead] at lower
    exact lower,
    found.property.2⟩

/-- In-place intersection, at every depth, on the first equation read without its dead binder. -/
def deadAt (fuel : Nat) {Θ : Context S.R} :
    (stored : EquationStore (TotalTerm Θ)) → Option (SitedProgress facts roots heads algebra rigid complete stored)
  | [] => none
  | equation :: rest =>
      match deadBinder facts roots heads algebra declared choices reducer fuel equation with
      | none => none
      | some dead =>
          (inPlaceIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
            headTypingUnique fuel (dead.reduced :: rest) (List.range Θ.arity)).map
            (undead facts roots heads algebra rigid complete strengthening dead)

/-- The dead-binder rule on the rotations of the store in turn. -/
def deadSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    List Nat → Option (SitedProgress facts roots heads algebra rigid complete problem)
  | [] => none
  | k :: rest =>
      match deadAt facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
          strengthening fuel (problem.rotate k) with
      | some found => some (unrotate facts roots heads algebra rigid complete k found)
      | none => deadSearch fuel problem rest

/-- **Intersection behind a dead binder**, anywhere in the store. -/
def deadRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (SitedProgress facts roots heads algebra rigid complete problem) :=
  deadSearch facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
    strengthening fuel problem (List.range problem.length)

/-- **One dead-binder round**: the anywhere round; when it is stuck, the dead-binder rule. -/
def deadRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match deadRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique strengthening fuel problem with
      | some found => .progress found.val found.property.1
      | none => .stuck
  | other => other

/-- **The dead-binder family**, at the weight rank. -/
noncomputable def deadFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-- **The dead-binder round makes the anywhere round's move wherever that round moves.** -/
theorem deadRound_eq_of_anywhere (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold deadRound
  cases computed : anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the anywhere family decides, the dead-binder family decides with the same outcome.** -/
theorem dead_run_of_anywhere (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((anywhereFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((deadFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((anywhereFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => deadRound_eq_of_anywhere facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem deadAt_const {Θ : Context S.R} :
    ∀ stored : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      deadAt facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
        strengthening fuel stored
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.dep (h := fun fuel => deadBinder facts roots heads algebra declared choices reducer fuel equation)
        (k := fun fuel found => match found with
          | none => none
          | some dead =>
              (inPlaceIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
                headTypingUnique fuel (dead.reduced :: rest) (List.range Θ.arity)).map
                (undead facts roots heads algebra rigid complete strengthening dead))
        (deadBinder_const facts roots heads algebra declared choices reducer stable equation)
        (fun found => by
          cases found with
          | none => exact EventuallyConst.const _
          | some dead =>
              exact EventuallyConst.comp (Option.map (undead facts roots heads algebra rigid complete strengthening dead))
                (inPlaceIntersectSearch_const facts roots heads algebra rigid complete declared choices reducer root
                  normalizes headTypingUnique stable (dead.reduced :: rest) (List.range Θ.arity)))

include stable in
theorem deadSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ rotations : List Nat, EventuallyConst fun fuel =>
      deadSearch facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
        strengthening fuel problem rotations
  | [] => EventuallyConst.const _
  | k :: rest => by
      obtain ⟨t₁, first⟩ := (deadAt_const facts roots heads algebra rigid complete declared choices reducer root
        normalizes headTypingUnique strengthening stable (problem.rotate k)).spec
      obtain ⟨t₂, later⟩ := (deadSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [deadSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

theorem deadRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) =
      (roundView (anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (sitedView facts roots heads algebra rigid complete (deadRule facts roots heads algebra rigid
          complete declared choices reducer root normalizes headTypingUnique strengthening fuel problem)) := by
  unfold deadRound
  cases anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases deadRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique strengthening fuel problem with
      | some found => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The dead-binder round is eventually constant on every store.** -/
theorem deadRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => deadRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => deadRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (anywhereRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp (sitedView facts roots heads algebra rigid complete)
        (deadSearch_const facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique strengthening stable problem _)))

include stable in
/-- **The dead-binder family settles** on every class on which, from some budget on, its round is not stuck and keeps
the class. -/
noncomputable def deadSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (deadFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => deadRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

end Rule

end ContextualDependentIntersectionGeneral
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
