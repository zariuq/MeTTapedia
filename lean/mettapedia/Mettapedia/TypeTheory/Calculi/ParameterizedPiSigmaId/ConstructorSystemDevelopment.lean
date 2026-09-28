import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicParallelSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SigmaConversionBoundary

/-!
# Confluence of definitions by constructor patterns

A definition by constructor patterns stores equations whose left side is a
defined constant applied to exactly its arity of argument patterns.  A
pattern is a variable, an undefined constant applied to patterns, or
reflexivity at a pattern.  When every left side is linear, every variable of a
right side occurs on its left, and a redex determines its contraction, the
equations together with beta, pair projections and a symmetric universe-head
equality have the parallel diamond.  The original conversion is then
Church–Rosser.

The diamond is proved by induction on the size of the source and never asks
whether a term is an equation instance, which the schema family need not
decide.  The complete development, which contracts every visible instance,
has to ask it, so it is defined classically; the confluence results do not
use it.

These are the conditions a checker for definitions by patterns establishes:
one scrutinee pattern per argument, constructor patterns with linear
variables, and exact, non-overlapping coverage.  A non-left-linear rule, such
as identity elimination compared at a repeated point, is outside this class.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstructorSystem

open AlgebraicSchema AlgebraicParallel ConversionCoherence

variable {Head : Type}

/-! ## Patterns and left sides -/

/-- Argument patterns.  The flag records the position: `true` for an argument,
which may be a variable, `false` for the function part of a constructor
application, which must be a constant spine. -/
inductive Pattern (defined : DeclName → Prop) : {m : Nat} → Bool → Tm Head m → Prop where
  | var {m : Nat} (index : Fin m) : Pattern defined true (.var index)
  | const {m : Nat} {flag : Bool} {name : DeclName} (constructor : ¬ defined name) :
      Pattern defined flag (.const name : Tm Head m)
  | app {m : Nat} {flag : Bool} {function argument : Tm Head m} :
      Pattern defined false function → Pattern defined true argument →
        Pattern defined flag (.app function argument)
  | refl {m : Nat} {term : Tm Head m} :
      Pattern defined true term → Pattern defined true (.refl term)

/-- A defined constant applied to `count` argument patterns. -/
inductive LeftSide (defined : DeclName → Prop) : {m : Nat} → Tm Head m → DeclName → Nat → Prop where
  | const {m : Nat} (name : DeclName) : LeftSide defined (.const name : Tm Head m) name 0
  | app {m : Nat} {function argument : Tm Head m} {name : DeclName} {count : Nat} :
      LeftSide defined function name count → Pattern defined true argument →
        LeftSide defined (.app function argument) name (count + 1)

/-- The constant at the head of an application spine, and the spine's length. -/
def spineHead {n : Nat} : Tm Head n → Option (DeclName × Nat)
  | .const name => some (name, 0)
  | .app function _ => (spineHead function).map (fun found => (found.1, found.2 + 1))
  | _ => none

/-- A constructor system: the equations of definitions by constructor patterns. -/
structure System (Head : Type) where
  schema : SchemaFamily Head
  defined : DeclName → Prop
  arity : DeclName → Nat
  left : ∀ {m : Nat} {left right : Tm Head m}, schema left right →
    ∃ name, defined name ∧ 0 < arity name ∧ LeftSide defined left name (arity name)
  linear : LeftLinearFamily schema
  covered : ∀ {m : Nat} {left right : Tm Head m}, schema left right →
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left
  determined : ∀ {m m' n n' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'},
    schema left right → schema left' right' →
    ∀ (instantiation : Sub Head m n) (instantiation' : Sub Head m' n),
      subst instantiation left = subst instantiation' left' →
      ∀ (develop : Tm Head n → Tm Head n'),
        subst (fun index => develop (instantiation index)) right =
          subst (fun index => develop (instantiation' index)) right'

/-- An instance of an equation's left side. -/
structure Redex (system : System Head) {n : Nat} (term : Tm Head n) where
  slots : Nat
  left : Tm Head slots
  right : Tm Head slots
  rule : system.schema left right
  instantiation : Sub Head slots n
  agrees : subst instantiation left = term

/-! ## Shape under substitution -/

theorem spineHead_subst_pattern {defined : DeclName → Prop} {m n : Nat} {term : Tm Head m}
    (pattern : Pattern defined false term) (substitution : Sub Head m n) :
    spineHead (subst substitution term) = spineHead term := by
  generalize flagEq : false = flag at pattern
  induction pattern with
  | var _ => cases flagEq
  | const _ => rfl
  | app _ _ ih _ =>
      simp only [subst, spineHead]
      rw [ih rfl]
  | refl _ _ => cases flagEq

theorem spineHead_pattern {defined : DeclName → Prop} {m : Nat} {term : Tm Head m}
    (pattern : Pattern defined false term) :
    ∃ name count, ¬ defined name ∧ spineHead term = some (name, count) := by
  generalize flagEq : false = flag at pattern
  induction pattern with
  | var _ => cases flagEq
  | const constructor => exact ⟨_, 0, constructor, rfl⟩
  | app _ _ ih _ =>
      obtain ⟨name, count, constructor, found⟩ := ih rfl
      exact ⟨name, count + 1, constructor, by simp only [spineHead, found, Option.map_some]⟩
  | refl _ _ => cases flagEq

theorem spineHead_leftSide {defined : DeclName → Prop} {m : Nat} {term : Tm Head m}
    {name : DeclName} {count : Nat} (side : LeftSide defined term name count) :
    spineHead term = some (name, count) := by
  induction side with
  | const _ => rfl
  | app _ _ ih => simp only [spineHead, ih, Option.map_some]

theorem spineHead_subst_leftSide {defined : DeclName → Prop} {m n : Nat} {term : Tm Head m}
    {name : DeclName} {count : Nat} (side : LeftSide defined term name count)
    (substitution : Sub Head m n) :
    spineHead (subst substitution term) = some (name, count) := by
  induction side with
  | const _ => rfl
  | app _ _ ih => simp only [subst, spineHead, ih, Option.map_some]

/-- An equation instance is headed by its defined constant, with its full arity. -/
theorem Redex.spineHead {system : System Head} {n : Nat} {term : Tm Head n}
    (redex : Redex system term) :
    ∃ name, system.defined name ∧ 0 < system.arity name ∧
      ConstructorSystem.spineHead term = some (name, system.arity name) := by
  obtain ⟨name, isDefined, positive, side⟩ := system.left redex.rule
  refine ⟨name, isDefined, positive, ?_⟩
  rw [← redex.agrees]
  exact spineHead_subst_leftSide side _

/-! ## Sizes -/

theorem sizeOf_le_pattern {defined : DeclName → Prop} {m n : Nat} {flag : Bool}
    {term : Tm Head m} (pattern : Pattern defined flag term) (substitution : Sub Head m n)
    {index : Fin m} (occurs : 0 < variableMultiplicity index term) :
    sizeOf (substitution index) ≤ sizeOf (subst substitution term) := by
  induction pattern with
  | var candidate =>
      simp only [variableMultiplicity] at occurs
      split at occurs
      · subst candidate
        exact le_of_eq rfl
      · omega
  | const _ => simp only [variableMultiplicity] at occurs; omega
  | @app _ function argument _ _ functionIH argumentIH =>
      simp only [variableMultiplicity] at occurs
      simp only [subst, Tm.app.sizeOf_spec]
      by_cases inFunction : 0 < variableMultiplicity index function
      · have bound := functionIH inFunction
        clear functionIH argumentIH
        omega
      · have inArgument : 0 < variableMultiplicity index argument := by
          clear functionIH argumentIH
          omega
        have bound := argumentIH inArgument
        clear functionIH argumentIH
        omega
  | refl _ ih =>
      simp only [variableMultiplicity] at occurs
      simp only [subst, Tm.refl.sizeOf_spec]
      have bound := ih occurs
      clear ih
      omega

theorem sizeOf_le_leftSide {defined : DeclName → Prop} {m n : Nat} {term : Tm Head m}
    {name : DeclName} {count : Nat} (side : LeftSide defined term name count)
    (substitution : Sub Head m n) {index : Fin m} (occurs : 0 < variableMultiplicity index term) :
    sizeOf (substitution index) < sizeOf (subst substitution term) := by
  induction side with
  | const _ => simp only [variableMultiplicity] at occurs; omega
  | @app function argument _ _ _ argumentPattern functionIH =>
      simp only [variableMultiplicity] at occurs
      simp only [subst, Tm.app.sizeOf_spec]
      by_cases inFunction : 0 < variableMultiplicity index function
      · have bound := functionIH inFunction
        clear functionIH
        omega
      · have inArgument : 0 < variableMultiplicity index argument := by
          clear functionIH
          omega
        have bound := sizeOf_le_pattern argumentPattern substitution inArgument
        clear functionIH
        omega

/-- The value of an occurring variable is strictly smaller than the redex. -/
theorem Redex.sizeOf_lt {system : System Head} {n : Nat} {term : Tm Head n}
    (redex : Redex system term) {index : Fin redex.slots}
    (occurs : 0 < variableMultiplicity index redex.left) :
    sizeOf (redex.instantiation index) < sizeOf term := by
  obtain ⟨_, _, _, side⟩ := system.left redex.rule
  have bound := sizeOf_le_leftSide side redex.instantiation occurs
  rw [redex.agrees] at bound
  exact bound

/-! ## Node counts

`sizeOf` counts variable indices, so renaming changes it.  Under a binder an
instantiation is renamed, and the diamond below descends under binders; it
measures terms by their nodes instead. -/

/-- The number of nodes of a term.  Variable indices do not count. -/
def nodeCount {n : Nat} : Tm Head n → Nat
  | .var _ => 1
  | .const _ => 1
  | .head _ => 1
  | .pi domain codomain => nodeCount domain + nodeCount codomain + 1
  | .sigma domain codomain => nodeCount domain + nodeCount codomain + 1
  | .id carrier left right => nodeCount carrier + nodeCount left + nodeCount right + 1
  | .lam body => nodeCount body + 1
  | .app function argument => nodeCount function + nodeCount argument + 1
  | .pair first second => nodeCount first + nodeCount second + 1
  | .fst package => nodeCount package + 1
  | .snd package => nodeCount package + 1
  | .refl term => nodeCount term + 1

theorem nodeCount_pos {n : Nat} (term : Tm Head n) : 0 < nodeCount term := by
  cases term <;> exact Nat.succ_pos _

theorem one_lt_nodeCount_app {n : Nat} (function argument : Tm Head n) :
    1 < nodeCount (Tm.app function argument) := by
  have positive := nodeCount_pos function
  show 1 < nodeCount function + nodeCount argument + 1
  omega

theorem nodeCount_rename {n m : Nat} (rho : Ren n m) (term : Tm Head n) :
    nodeCount (rename rho term) = nodeCount term := by
  induction term generalizing m with
  | var _ | const _ | head _ => rfl
  | pi _ _ domainIH codomainIH | sigma _ _ domainIH codomainIH =>
      simp only [rename, nodeCount, domainIH, codomainIH]
  | id _ _ _ carrierIH leftIH rightIH => simp only [rename, nodeCount, carrierIH, leftIH, rightIH]
  | lam _ bodyIH => simp only [rename, nodeCount, bodyIH]
  | app _ _ firstIH secondIH | pair _ _ firstIH secondIH =>
      simp only [rename, nodeCount, firstIH, secondIH]
  | fst _ ih | snd _ ih | refl _ ih => simp only [rename, nodeCount, ih]

theorem nodeCount_le_pattern {defined : DeclName → Prop} {m n : Nat} {flag : Bool}
    {term : Tm Head m} (pattern : Pattern defined flag term) (substitution : Sub Head m n)
    {index : Fin m} (occurs : 0 < variableMultiplicity index term) :
    nodeCount (substitution index) ≤ nodeCount (subst substitution term) := by
  induction pattern with
  | var candidate =>
      simp only [variableMultiplicity] at occurs
      split at occurs
      · subst candidate
        exact Nat.le_refl _
      · exact absurd occurs (Nat.lt_irrefl 0)
  | const _ =>
      simp only [variableMultiplicity] at occurs
      exact absurd occurs (Nat.lt_irrefl 0)
  | @app _ function argument _ _ functionIH argumentIH =>
      simp only [variableMultiplicity] at occurs
      simp only [subst, nodeCount]
      by_cases inFunction : 0 < variableMultiplicity index function
      · have bound := functionIH inFunction
        clear functionIH argumentIH
        omega
      · have inArgument : 0 < variableMultiplicity index argument := by
          clear functionIH argumentIH
          omega
        have bound := argumentIH inArgument
        clear functionIH argumentIH
        omega
  | refl _ ih =>
      simp only [variableMultiplicity] at occurs
      simp only [subst, nodeCount]
      have bound := ih occurs
      clear ih
      omega

/-- An occurring variable of a left side is instantiated by fewer nodes than
the instance has. -/
theorem nodeCount_lt_leftSide {defined : DeclName → Prop} {m n : Nat} {term : Tm Head m}
    {name : DeclName} {count : Nat} (side : LeftSide defined term name count)
    (substitution : Sub Head m n) {index : Fin m} (occurs : 0 < variableMultiplicity index term) :
    nodeCount (substitution index) < nodeCount (subst substitution term) := by
  induction side with
  | const _ =>
      simp only [variableMultiplicity] at occurs
      exact absurd occurs (Nat.lt_irrefl 0)
  | @app function argument _ _ _ argumentPattern functionIH =>
      simp only [variableMultiplicity] at occurs
      simp only [subst, nodeCount]
      by_cases inFunction : 0 < variableMultiplicity index function
      · have bound := functionIH inFunction
        clear functionIH
        omega
      · have inArgument : 0 < variableMultiplicity index argument := by
          clear functionIH
          omega
        have bound := nodeCount_le_pattern argumentPattern substitution inArgument
        clear functionIH
        omega

/-- An instance of a left side with at least one argument is an application. -/
theorem one_lt_nodeCount_leftSide {defined : DeclName → Prop} {m n : Nat} {term : Tm Head m}
    {name : DeclName} {count : Nat} (side : LeftSide defined term name count)
    (positive : 0 < count) (substitution : Sub Head m n) :
    1 < nodeCount (subst substitution term) := by
  cases side with
  | const _ => exact absurd positive (Nat.lt_irrefl 0)
  | app _ _ => exact one_lt_nodeCount_app _ _

/-- Pointwise existence over a finite telescope gives one substitution. -/
theorem exists_sub_of_pointwise {m n : Nat} {property : Fin m → Tm Head n → Prop}
    (pointwise : ∀ index, ∃ value, property index value) :
    ∃ substitution : Sub Head m n, ∀ index, property index (substitution index) := by
  induction m with
  | zero => exact ⟨fun index => Fin.elim0 index, fun index => Fin.elim0 index⟩
  | succ m ih =>
      obtain ⟨first, firstHolds⟩ := pointwise 0
      obtain ⟨rest, restHolds⟩ := ih (fun index => pointwise index.succ)
      exact ⟨Fin.cases first rest, fun index => Fin.cases firstHolds restHolds index⟩

/-! ## Substitutions agreeing on occurring variables -/

/-- Substitutions that agree on the variables a term uses give the same
instance, under binders as well. -/
theorem subst_congr_occurring {m : Nat} (term : Tm Head m) :
    ∀ {n : Nat} {first second : Sub Head m n},
      (∀ index, 0 < variableMultiplicity index term → first index = second index) →
        subst first term = subst second term := by
  induction term with
  | var candidate =>
      intro n first second agree
      exact agree candidate (by simp [variableMultiplicity])
  | const _ => intro _ _ _ _; rfl
  | head _ => intro _ _ _ _; rfl
  | pi domain codomain domainIH codomainIH =>
      intro n first second agree
      simp only [subst]
      rw [domainIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega)),
        codomainIH (first := liftSub first) (second := liftSub second) (by
          intro index occurs
          refine Fin.cases (fun _ => rfl) (fun prior occursPrior => ?_) index occurs
          simp only [liftSub_succ]
          rw [agree prior (by simp only [variableMultiplicity]; omega)])]
  | sigma domain codomain domainIH codomainIH =>
      intro n first second agree
      simp only [subst]
      rw [domainIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega)),
        codomainIH (first := liftSub first) (second := liftSub second) (by
          intro index occurs
          refine Fin.cases (fun _ => rfl) (fun prior occursPrior => ?_) index occurs
          simp only [liftSub_succ]
          rw [agree prior (by simp only [variableMultiplicity]; omega)])]
  | id carrier left right carrierIH leftIH rightIH =>
      intro n first second agree
      simp only [subst]
      rw [carrierIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega)),
        leftIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega)),
        rightIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega))]
  | lam body bodyIH =>
      intro n first second agree
      simp only [subst]
      rw [bodyIH (first := liftSub first) (second := liftSub second) (by
          intro index occurs
          refine Fin.cases (fun _ => rfl) (fun prior occursPrior => ?_) index occurs
          simp only [liftSub_succ]
          rw [agree prior (by simp only [variableMultiplicity]; omega)])]
  | app function argument functionIH argumentIH =>
      intro n first second agree
      simp only [subst]
      rw [functionIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega)),
        argumentIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega))]
  | pair left right leftIH rightIH =>
      intro n first second agree
      simp only [subst]
      rw [leftIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega)),
        rightIH (fun index occurs => agree index (by simp only [variableMultiplicity]; omega))]
  | fst package ih =>
      intro n first second agree
      simp only [subst]
      rw [ih (fun index occurs => agree index (by simp only [variableMultiplicity]; omega))]
  | snd package ih =>
      intro n first second agree
      simp only [subst]
      rw [ih (fun index occurs => agree index (by simp only [variableMultiplicity]; omega))]
  | refl term ih =>
      intro n first second agree
      simp only [subst]
      rw [ih (fun index occurs => agree index (by simp only [variableMultiplicity]; omega))]

/-! ## Parallel reduction at constructor shapes -/

section Parallel

variable {headEq : Head → Head → Prop} (system : System Head)

/-- A parallel root contraction's source is an equation instance. -/
theorem redex_of_algebraic {n arity : Nat} {left right : Tm Head arity}
    (rule : system.schema left right) (substitution : Sub Head arity n) :
    Nonempty (Redex system (subst substitution left)) :=
  ⟨⟨arity, left, right, rule, substitution, rfl⟩⟩

theorem not_redex_of_spineHead {n : Nat} {term : Tm Head n}
    (shape : ∀ name, system.defined name → spineHead term ≠ some (name, system.arity name)) :
    ¬ Nonempty (Redex system term) := by
  rintro ⟨redex⟩
  obtain ⟨name, isDefined, _, found⟩ := redex.spineHead
  exact shape name isDefined found

private theorem par_const_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ name, source = .const name → target = .const name := by
  cases step with
  | const _ => intro _ equality; exact equality
  | algebraic rule substitution _ _ =>
      intro name equality
      have := (redex_of_algebraic system rule substitution)
      rw [equality] at this
      obtain ⟨redex⟩ := this
      obtain ⟨_, _, positive, found⟩ := redex.spineHead
      simp only [spineHead, Option.some.injEq, Prod.mk.injEq] at found
      exfalso
      omega
  | _ => intro _ equality; cases equality

theorem par_const {n : Nat} {name : DeclName} {target : Tm Head n}
    (step : ParRed headEq system.schema (.const name) target) : target = .const name :=
  par_const_aux system step name rfl

private theorem par_var_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ index, source = .var index → target = .var index := by
  cases step with
  | var _ => intro _ equality; exact equality
  | algebraic rule substitution _ _ =>
      intro index equality
      have := (redex_of_algebraic system rule substitution)
      rw [equality] at this
      obtain ⟨redex⟩ := this
      obtain ⟨_, _, _, found⟩ := redex.spineHead
      simp only [spineHead] at found
      exact absurd found (by simp)
  | _ => intro _ equality; cases equality

theorem par_var {n : Nat} {index : Fin n} {target : Tm Head n}
    (step : ParRed headEq system.schema (.var index) target) : target = .var index :=
  par_var_aux system step index rfl

private theorem par_refl_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ term, source = .refl term →
      ∃ term', target = .refl term' ∧ ParRed headEq system.schema term term' := by
  cases step with
  | refl inner => intro _ equality; cases equality; exact ⟨_, rfl, inner⟩
  | algebraic rule substitution _ _ =>
      intro term equality
      have := (redex_of_algebraic system rule substitution)
      rw [equality] at this
      obtain ⟨redex⟩ := this
      obtain ⟨_, _, _, found⟩ := redex.spineHead
      simp only [spineHead] at found
      exact absurd found (by simp)
  | _ => intro _ equality; cases equality

theorem par_refl_inv {n : Nat} {term target : Tm Head n}
    (step : ParRed headEq system.schema (.refl term) target) :
    ∃ term', target = .refl term' ∧ ParRed headEq system.schema term term' :=
  par_refl_aux system step term rfl

private theorem par_lam_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ body, source = .lam body →
      ∃ body', target = .lam body' ∧ ParRed headEq system.schema body body' := by
  cases step with
  | lam inner => intro _ equality; cases equality; exact ⟨_, rfl, inner⟩
  | algebraic rule substitution _ _ =>
      intro body equality
      have := (redex_of_algebraic system rule substitution)
      rw [equality] at this
      obtain ⟨redex⟩ := this
      obtain ⟨_, _, _, found⟩ := redex.spineHead
      simp only [spineHead] at found
      exact absurd found (by simp)
  | _ => intro _ equality; cases equality

theorem par_lam_inv {n : Nat} {body : Tm Head (n + 1)} {target : Tm Head n}
    (step : ParRed headEq system.schema (.lam body) target) :
    ∃ body', target = .lam body' ∧ ParRed headEq system.schema body body' :=
  par_lam_aux system step body rfl

private theorem par_pair_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ first second, source = .pair first second →
      ∃ first' second', target = .pair first' second' ∧
        ParRed headEq system.schema first first' ∧ ParRed headEq system.schema second second' := by
  cases step with
  | pair left right => intro _ _ equality; cases equality; exact ⟨_, _, rfl, left, right⟩
  | algebraic rule substitution _ _ =>
      intro first second equality
      have := (redex_of_algebraic system rule substitution)
      rw [equality] at this
      obtain ⟨redex⟩ := this
      obtain ⟨_, _, _, found⟩ := redex.spineHead
      simp only [spineHead] at found
      exact absurd found (by simp)
  | _ => intro _ _ equality; cases equality

theorem par_pair_inv {n : Nat} {first second target : Tm Head n}
    (step : ParRed headEq system.schema (.pair first second) target) :
    ∃ first' second', target = .pair first' second' ∧
      ParRed headEq system.schema first first' ∧ ParRed headEq system.schema second second' :=
  par_pair_aux system step first second rfl

/-- At an application that is neither an equation instance nor a beta redex,
parallel reduction is componentwise. -/
private theorem par_app_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ function argument, source = .app function argument →
      ¬ Nonempty (Redex system (.app function argument)) → (∀ body, function ≠ .lam body) →
      ∃ function' argument', target = .app function' argument' ∧
        ParRed headEq system.schema function function' ∧
          ParRed headEq system.schema argument argument' := by
  cases step with
  | app functionStep argumentStep =>
      intro _ _ equality _ _
      cases equality
      exact ⟨_, _, rfl, functionStep, argumentStep⟩
  | betaPi _ _ =>
      intro function _ equality _ notLambda
      cases equality
      exact absurd rfl (notLambda _)
  | algebraic rule substitution _ _ =>
      intro function argument equality notRedex _
      have := (redex_of_algebraic system rule substitution)
      rw [equality] at this
      exact absurd this notRedex
  | _ => intro _ _ equality; cases equality

theorem par_app_inv {n : Nat} {function argument target : Tm Head n}
    (notRedex : ¬ Nonempty (Redex system (.app function argument)))
    (notLambda : ∀ body, function ≠ .lam body)
    (step : ParRed headEq system.schema (.app function argument) target) :
    ∃ function' argument', target = .app function' argument' ∧
      ParRed headEq system.schema function function' ∧
        ParRed headEq system.schema argument argument' :=
  par_app_aux system step function argument rfl notRedex notLambda

/-- An equation instance is a constant spine. -/
theorem spineHead_algebraic {n arity : Nat} {left right : Tm Head arity}
    (rule : system.schema left right) (substitution : Sub Head arity n) :
    ∃ name count, spineHead (subst substitution left) = some (name, count) := by
  obtain ⟨name, _, _, side⟩ := system.left rule
  exact ⟨name, _, spineHead_subst_leftSide side substitution⟩

private theorem par_head_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ value, source = .head value →
      target = .head value ∨ ∃ value', headEq value value' ∧ target = .head value' := by
  cases step with
  | head _ => intro _ equality; exact .inl equality
  | headRel related => intro _ equality; cases equality; exact .inr ⟨_, related, rfl⟩
  | algebraic rule substitution _ _ =>
      intro _ equality
      obtain ⟨_, _, found⟩ := spineHead_algebraic system rule substitution
      rw [equality] at found
      cases found
  | _ => intro _ equality; cases equality

theorem par_head_inv {n : Nat} {value : Head} {target : Tm Head n}
    (step : ParRed headEq system.schema (.head value) target) :
    target = .head value ∨ ∃ value', headEq value value' ∧ target = .head value' :=
  par_head_aux system step value rfl

private theorem par_pi_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ domain codomain, source = .pi domain codomain →
      ∃ domain' codomain', target = .pi domain' codomain' ∧
        ParRed headEq system.schema domain domain' ∧
          ParRed headEq system.schema codomain codomain' := by
  cases step with
  | pi domainStep codomainStep =>
      intro _ _ equality; cases equality; exact ⟨_, _, rfl, domainStep, codomainStep⟩
  | algebraic rule substitution _ _ =>
      intro _ _ equality
      obtain ⟨_, _, found⟩ := spineHead_algebraic system rule substitution
      rw [equality] at found
      cases found
  | _ => intro _ _ equality; cases equality

theorem par_pi_inv {n : Nat} {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {target : Tm Head n} (step : ParRed headEq system.schema (.pi domain codomain) target) :
    ∃ domain' codomain', target = .pi domain' codomain' ∧
      ParRed headEq system.schema domain domain' ∧
        ParRed headEq system.schema codomain codomain' :=
  par_pi_aux system step domain codomain rfl

private theorem par_sigma_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ domain codomain, source = .sigma domain codomain →
      ∃ domain' codomain', target = .sigma domain' codomain' ∧
        ParRed headEq system.schema domain domain' ∧
          ParRed headEq system.schema codomain codomain' := by
  cases step with
  | sigma domainStep codomainStep =>
      intro _ _ equality; cases equality; exact ⟨_, _, rfl, domainStep, codomainStep⟩
  | algebraic rule substitution _ _ =>
      intro _ _ equality
      obtain ⟨_, _, found⟩ := spineHead_algebraic system rule substitution
      rw [equality] at found
      cases found
  | _ => intro _ _ equality; cases equality

theorem par_sigma_inv {n : Nat} {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {target : Tm Head n} (step : ParRed headEq system.schema (.sigma domain codomain) target) :
    ∃ domain' codomain', target = .sigma domain' codomain' ∧
      ParRed headEq system.schema domain domain' ∧
        ParRed headEq system.schema codomain codomain' :=
  par_sigma_aux system step domain codomain rfl

private theorem par_id_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ carrier left right, source = .id carrier left right →
      ∃ carrier' left' right', target = .id carrier' left' right' ∧
        ParRed headEq system.schema carrier carrier' ∧
          ParRed headEq system.schema left left' ∧ ParRed headEq system.schema right right' := by
  cases step with
  | id carrierStep leftStep rightStep =>
      intro _ _ _ equality
      cases equality
      exact ⟨_, _, _, rfl, carrierStep, leftStep, rightStep⟩
  | algebraic rule substitution _ _ =>
      intro _ _ _ equality
      obtain ⟨_, _, found⟩ := spineHead_algebraic system rule substitution
      rw [equality] at found
      cases found
  | _ => intro _ _ _ equality; cases equality

theorem par_id_inv {n : Nat} {carrier left right target : Tm Head n}
    (step : ParRed headEq system.schema (.id carrier left right) target) :
    ∃ carrier' left' right', target = .id carrier' left' right' ∧
      ParRed headEq system.schema carrier carrier' ∧
        ParRed headEq system.schema left left' ∧ ParRed headEq system.schema right right' :=
  par_id_aux system step carrier left right rfl

private theorem par_fst_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ package, source = .fst package →
      (∃ package', target = .fst package' ∧ ParRed headEq system.schema package package') ∨
      (∃ first second first' second', package = .pair first second ∧ target = first' ∧
        ParRed headEq system.schema first first' ∧
          ParRed headEq system.schema second second') := by
  cases step with
  | fst packageStep => intro _ equality; cases equality; exact .inl ⟨_, rfl, packageStep⟩
  | betaSigmaFst firstStep secondStep =>
      intro _ equality
      cases equality
      exact .inr ⟨_, _, _, _, rfl, rfl, firstStep, secondStep⟩
  | algebraic rule substitution _ _ =>
      intro _ equality
      obtain ⟨_, _, found⟩ := spineHead_algebraic system rule substitution
      rw [equality] at found
      cases found
  | _ => intro _ equality; cases equality

theorem par_fst_cases {n : Nat} {package target : Tm Head n}
    (step : ParRed headEq system.schema (.fst package) target) :
    (∃ package', target = .fst package' ∧ ParRed headEq system.schema package package') ∨
    (∃ first second first' second', package = .pair first second ∧ target = first' ∧
      ParRed headEq system.schema first first' ∧ ParRed headEq system.schema second second') :=
  par_fst_aux system step package rfl

private theorem par_snd_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ package, source = .snd package →
      (∃ package', target = .snd package' ∧ ParRed headEq system.schema package package') ∨
      (∃ first second first' second', package = .pair first second ∧ target = second' ∧
        ParRed headEq system.schema first first' ∧
          ParRed headEq system.schema second second') := by
  cases step with
  | snd packageStep => intro _ equality; cases equality; exact .inl ⟨_, rfl, packageStep⟩
  | betaSigmaSnd firstStep secondStep =>
      intro _ equality
      cases equality
      exact .inr ⟨_, _, _, _, rfl, rfl, firstStep, secondStep⟩
  | algebraic rule substitution _ _ =>
      intro _ equality
      obtain ⟨_, _, found⟩ := spineHead_algebraic system rule substitution
      rw [equality] at found
      cases found
  | _ => intro _ equality; cases equality

theorem par_snd_cases {n : Nat} {package target : Tm Head n}
    (step : ParRed headEq system.schema (.snd package) target) :
    (∃ package', target = .snd package' ∧ ParRed headEq system.schema package package') ∨
    (∃ first second first' second', package = .pair first second ∧ target = second' ∧
      ParRed headEq system.schema first first' ∧ ParRed headEq system.schema second second') :=
  par_snd_aux system step package rfl

/-! ## Stability of patterns and left sides -/

/-- Joining two substitutions on disjoint variable supports. -/
def join {m n : Nat} (first second : Sub Head m n) (support : Tm Head m) : Sub Head m n :=
  fun index => if 0 < variableMultiplicity index support then first index else second index

theorem not_lambda_of_pattern {m n : Nat} {term : Tm Head m}
    (pattern : Pattern system.defined false term) (substitution : Sub Head m n) :
    ∀ body, subst substitution term ≠ .lam body := by
  intro body equality
  generalize flagEq : false = flag at pattern
  cases pattern with
  | var _ => cases flagEq
  | const _ => simp only [subst] at equality; cases equality
  | app _ _ => simp only [subst] at equality; cases equality
  | refl _ => cases flagEq

theorem not_lambda_of_leftSide {m n : Nat} {term : Tm Head m} {name : DeclName} {count : Nat}
    (side : LeftSide system.defined term name count) (substitution : Sub Head m n) :
    ∀ body, subst substitution term ≠ .lam body := by
  intro body equality
  cases side with
  | const _ => simp only [subst] at equality; cases equality
  | app _ _ => simp only [subst] at equality; cases equality

/-- A parallel reduct of a pattern instance is an instance of the same
pattern: constructor nodes cannot contract. -/
theorem pattern_par {m n : Nat} {flag : Bool} {term : Tm Head m}
    (pattern : Pattern system.defined flag term) (linear : LeftLinear term)
    (substitution : Sub Head m n) {target : Tm Head n}
    (step : ParRed headEq system.schema (subst substitution term) target) :
    ∃ substitution' : Sub Head m n, target = subst substitution' term ∧
      (∀ index, 0 < variableMultiplicity index term →
        ParRed headEq system.schema (substitution index) (substitution' index)) ∧
      (∀ index, variableMultiplicity index term = 0 → substitution' index = substitution index) := by
  induction pattern generalizing target with
  | var candidate =>
      refine ⟨fun index => if index = candidate then target else substitution index, ?_, ?_, ?_⟩
      · simp only [subst, ite_true]
      · intro index occurs
        simp only [variableMultiplicity] at occurs
        split at occurs
        · subst index
          simpa only [subst, ite_true] using step
        · exfalso
          omega
      · intro index absent
        simp only [variableMultiplicity] at absent
        split at absent
        · exfalso
          omega
        · rename_i different
          show (if index = candidate then target else substitution index) = substitution index
          rw [if_neg (fun (same : index = candidate) => different same.symm)]
  | const constructor =>
      exact ⟨substitution, par_const system step, fun index occurs => by
        simp only [variableMultiplicity] at occurs; exfalso; omega, fun _ _ => rfl⟩
  | @app _ function argument functionPattern argumentPattern functionIH argumentIH =>
      have functionLinear : LeftLinear function := fun index => by
        have := linear index; simp only [variableMultiplicity] at this; omega
      have argumentLinear : LeftLinear argument := fun index => by
        have := linear index; simp only [variableMultiplicity] at this; omega
      obtain ⟨name, count, constructor, headFound⟩ := spineHead_pattern functionPattern
      have notRedex : ¬ Nonempty (Redex system
          (.app (subst substitution function) (subst substitution argument))) := by
        apply not_redex_of_spineHead system
        intro defined isDefined found
        simp only [spineHead, spineHead_subst_pattern functionPattern, headFound,
          Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
        exact constructor (found.1 ▸ isDefined)
      obtain ⟨function', argument', rfl, functionStep, argumentStep⟩ :=
        par_app_inv system notRedex (not_lambda_of_pattern system functionPattern substitution)
          step
      obtain ⟨first, functionShape, functionPar, functionRest⟩ :=
        functionIH functionLinear functionStep
      obtain ⟨second, argumentShape, argumentPar, argumentRest⟩ :=
        argumentIH argumentLinear argumentStep
      refine ⟨join first second function, ?_, ?_, ?_⟩
      · simp only [subst]
        rw [functionShape, argumentShape]
        congr 1
        · exact subst_congr_occurring function (fun index occurs => by
            simp only [join, occurs, ite_true])
        · exact subst_congr_occurring argument (fun index occurs => by
            have := linear index
            simp only [variableMultiplicity] at this
            have absent : variableMultiplicity index function = 0 := by omega
            simp only [join, absent, lt_self_iff_false, ite_false])
      · intro index occurs
        simp only [variableMultiplicity] at occurs
        by_cases inFunction : 0 < variableMultiplicity index function
        · simpa only [join, inFunction, ite_true] using functionPar index inFunction
        · have inArgument : 0 < variableMultiplicity index argument := by omega
          simpa only [join, inFunction, ite_false] using argumentPar index inArgument
      · intro index absent
        simp only [variableMultiplicity] at absent
        have functionAbsent : variableMultiplicity index function = 0 := by omega
        have argumentAbsent : variableMultiplicity index argument = 0 := by omega
        simp only [join, functionAbsent, lt_self_iff_false, ite_false]
        exact argumentRest index argumentAbsent
  | @refl inner innerPattern innerIH =>
      have innerLinear : LeftLinear inner := fun index => by
        have := linear index; simp only [variableMultiplicity] at this; omega
      obtain ⟨inner', rfl, innerStep⟩ := par_refl_inv system step
      obtain ⟨substitution', innerShape, innerPar, innerRest⟩ := innerIH innerLinear innerStep
      exact ⟨substitution', by simp only [subst, innerShape], fun index occurs =>
        innerPar index (by simpa only [variableMultiplicity] using occurs),
        fun index absent => innerRest index (by simpa only [variableMultiplicity] using absent)⟩

/-- The two halves of a linear application, combined. -/
theorem join_app {m n : Nat} {function argument : Tm Head m}
    (linear : LeftLinear (.app function argument))
    {substitution first second : Sub Head m n} {function' argument' : Tm Head n}
    (functionShape : function' = subst first function)
    (functionPar : ∀ index, 0 < variableMultiplicity index function →
      ParRed headEq system.schema (substitution index) (first index))
    (argumentShape : argument' = subst second argument)
    (argumentPar : ∀ index, 0 < variableMultiplicity index argument →
      ParRed headEq system.schema (substitution index) (second index))
    (argumentRest : ∀ index, variableMultiplicity index argument = 0 →
      second index = substitution index) :
    Tm.app function' argument' = subst (join first second function) (.app function argument) ∧
      (∀ index, 0 < variableMultiplicity index (.app function argument) →
        ParRed headEq system.schema (substitution index) (join first second function index)) ∧
      (∀ index, variableMultiplicity index (.app function argument) = 0 →
        join first second function index = substitution index) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [subst]
    rw [functionShape, argumentShape]
    congr 1
    · exact subst_congr_occurring function (fun index occurs => by
        simp only [join, occurs, ite_true])
    · exact subst_congr_occurring argument (fun index occurs => by
        have := linear index
        simp only [variableMultiplicity] at this
        have absent : variableMultiplicity index function = 0 := by omega
        simp only [join, absent, lt_self_iff_false, ite_false])
  · intro index occurs
    simp only [variableMultiplicity] at occurs
    by_cases inFunction : 0 < variableMultiplicity index function
    · simpa only [join, inFunction, ite_true] using functionPar index inFunction
    · have inArgument : 0 < variableMultiplicity index argument := by omega
      simpa only [join, inFunction, ite_false] using argumentPar index inArgument
  · intro index absent
    simp only [variableMultiplicity] at absent
    have functionAbsent : variableMultiplicity index function = 0 := by omega
    have argumentAbsent : variableMultiplicity index argument = 0 := by omega
    simp only [join, functionAbsent, lt_self_iff_false, ite_false]
    exact argumentRest index argumentAbsent

/-- Below the full arity no equation fires, so parallel reduction of a partial
spine is componentwise. -/
theorem leftSide_prefix_par {m n : Nat} {term : Tm Head m} {name : DeclName} {count : Nat}
    (side : LeftSide system.defined term name count) (short : count < system.arity name)
    (linear : LeftLinear term) (substitution : Sub Head m n) {target : Tm Head n}
    (step : ParRed headEq system.schema (subst substitution term) target) :
    ∃ substitution' : Sub Head m n, target = subst substitution' term ∧
      (∀ index, 0 < variableMultiplicity index term →
        ParRed headEq system.schema (substitution index) (substitution' index)) ∧
      (∀ index, variableMultiplicity index term = 0 → substitution' index = substitution index) := by
  induction side generalizing target with
  | const _ =>
      exact ⟨substitution, par_const system step, fun index occurs => by
        simp only [variableMultiplicity] at occurs; exfalso; omega, fun _ _ => rfl⟩
  | @app function argument name count functionSide argumentPattern functionIH =>
      have functionLinear : LeftLinear function := fun index => by
        have := linear index; simp only [variableMultiplicity] at this; omega
      have argumentLinear : LeftLinear argument := fun index => by
        have := linear index; simp only [variableMultiplicity] at this; omega
      have notRedex : ¬ Nonempty (Redex system
          (.app (subst substitution function) (subst substitution argument))) := by
        apply not_redex_of_spineHead system
        intro defined isDefined found
        have shape := spineHead_subst_leftSide (.app functionSide argumentPattern) substitution
        simp only [subst] at shape
        rw [shape, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, same⟩ := found
        omega
      obtain ⟨function', argument', rfl, functionStep, argumentStep⟩ :=
        par_app_inv system notRedex (not_lambda_of_leftSide system functionSide substitution) step
      obtain ⟨first, functionShape, functionPar, _⟩ :=
        functionIH (by omega) functionLinear functionStep
      obtain ⟨second, argumentShape, argumentPar, argumentRest⟩ :=
        pattern_par system argumentPattern argumentLinear substitution argumentStep
      exact ⟨join first second function,
        join_app system linear functionShape functionPar argumentShape argumentPar argumentRest⟩

theorem parSub_pointwise {arity n : Nat} {source target : Sub Head arity n} :
    ParSub headEq system.schema source target →
      ∀ index, ParRed headEq system.schema (source index) (target index)
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases head (fun prior => parSub_pointwise tail prior) index

theorem parSub_of_pointwise :
    ∀ {arity n : Nat} {source target : Sub Head arity n},
      (∀ index, ParRed headEq system.schema (source index) (target index)) →
        ParSub headEq system.schema source target := by
  intro arity
  induction arity with
  | zero =>
      intro n source target _
      have sourceEmpty : source = (fun index : Fin 0 => (Fin.elim0 index : Tm Head n)) := by
        funext index; exact Fin.elim0 index
      have targetEmpty : target = (fun index : Fin 0 => (Fin.elim0 index : Tm Head n)) := by
        funext index; exact Fin.elim0 index
      subst sourceEmpty targetEmpty
      exact .nil
  | succ arity ih =>
      intro n source target pointwise
      have sourceSplit : source = Fin.cases (source 0) (fun index => source index.succ) := by
        funext index; exact Fin.cases rfl (fun _ => rfl) index
      have targetSplit : target = Fin.cases (target 0) (fun index => target index.succ) := by
        funext index; exact Fin.cases rfl (fun _ => rfl) index
      rw [sourceSplit, targetSplit]
      exact .cons (pointwise 0) (ih (fun index => pointwise index.succ))

private theorem par_app_all_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ function argument, source = .app function argument →
      (∃ function' argument', target = .app function' argument' ∧
        ParRed headEq system.schema function function' ∧
          ParRed headEq system.schema argument argument') ∨
      (∃ body body' argument', function = .lam body ∧ target = inst0 argument' body' ∧
        ParRed headEq system.schema body body' ∧
          ParRed headEq system.schema argument argument') ∨
      (∃ (arity : Nat) (left right : Tm Head arity) (_ : system.schema left right)
          (instantiation instantiation' : Sub Head arity n),
        subst instantiation left = .app function argument ∧
        (∀ index, ParRed headEq system.schema (instantiation index) (instantiation' index)) ∧
        target = subst instantiation' right) := by
  cases step with
  | app functionStep argumentStep =>
      intro _ _ equality
      cases equality
      exact .inl ⟨_, _, rfl, functionStep, argumentStep⟩
  | betaPi bodyStep argumentStep =>
      intro _ _ equality
      cases equality
      exact .inr (.inl ⟨_, _, _, rfl, rfl, bodyStep, argumentStep⟩)
  | algebraic rule instantiation instantiation' arguments =>
      intro _ _ equality
      exact .inr (.inr ⟨_, _, _, rule, instantiation, instantiation', equality,
        parSub_pointwise system arguments, rfl⟩)
  | _ => intro _ _ equality; cases equality

/-- Every parallel step out of an application is componentwise, a beta
contraction, or the contraction of an equation instance. -/
theorem par_app_cases {n : Nat} {function argument target : Tm Head n}
    (step : ParRed headEq system.schema (.app function argument) target) :
    (∃ function' argument', target = .app function' argument' ∧
      ParRed headEq system.schema function function' ∧
        ParRed headEq system.schema argument argument') ∨
    (∃ body body' argument', function = .lam body ∧ target = inst0 argument' body' ∧
      ParRed headEq system.schema body body' ∧
        ParRed headEq system.schema argument argument') ∨
    (∃ (arity : Nat) (left right : Tm Head arity) (_ : system.schema left right)
        (instantiation instantiation' : Sub Head arity n),
      subst instantiation left = .app function argument ∧
      (∀ index, ParRed headEq system.schema (instantiation index) (instantiation' index)) ∧
      target = subst instantiation' right) :=
  par_app_all_aux system step function argument rfl

private theorem par_app_cases_aux {n : Nat} {source target : Tm Head n}
    (step : ParRed headEq system.schema source target) :
    ∀ function argument, source = .app function argument →
      (∃ function' argument', target = .app function' argument' ∧
        ParRed headEq system.schema function function' ∧
          ParRed headEq system.schema argument argument') ∨
      (∃ body, function = .lam body) ∨
      (∃ (arity : Nat) (left right : Tm Head arity) (_ : system.schema left right)
          (instantiation instantiation' : Sub Head arity n),
        subst instantiation left = .app function argument ∧
        ParSub headEq system.schema instantiation instantiation' ∧
        target = subst instantiation' right) := by
  cases step with
  | app functionStep argumentStep =>
      intro _ _ equality
      cases equality
      exact .inl ⟨_, _, rfl, functionStep, argumentStep⟩
  | betaPi _ _ =>
      intro _ _ equality
      cases equality
      exact .inr (.inl ⟨_, rfl⟩)
  | algebraic rule instantiation instantiation' arguments =>
      intro _ _ equality
      exact .inr (.inr ⟨_, _, _, rule, instantiation, instantiation', equality, arguments, rfl⟩)
  | _ => intro _ _ equality; cases equality

private theorem redex_par_aux {slots n : Nat} {left : Tm Head slots}
    {name : DeclName} {count : Nat} (side : LeftSide system.defined left name count)
    (full : count = system.arity name) (positive : 0 < count) (linear : LeftLinear left)
    (instantiation : Sub Head slots n) {target : Tm Head n}
    (step : ParRed headEq system.schema (subst instantiation left) target) :
    (∃ (arity : Nat) (left' right' : Tm Head arity) (_ : system.schema left' right')
        (instantiation₂ instantiation' : Sub Head arity n),
      subst instantiation₂ left' = subst instantiation left ∧
      (∀ index, ParRed headEq system.schema (instantiation₂ index) (instantiation' index)) ∧
      target = subst instantiation' right') ∨
    (∃ substitution' : Sub Head slots n, target = subst substitution' left ∧
      (∀ index, 0 < variableMultiplicity index left →
        ParRed headEq system.schema (instantiation index) (substitution' index)) ∧
      (∀ index, variableMultiplicity index left = 0 →
        substitution' index = instantiation index)) := by
  cases side with
  | const _ => exfalso; omega
  | @app function argument _ count functionSide argumentPattern =>
      have functionLinear : LeftLinear function := fun index => by
        have := linear index; simp only [variableMultiplicity] at this; omega
      have argumentLinear : LeftLinear argument := fun index => by
        have := linear index; simp only [variableMultiplicity] at this; omega
      rcases par_app_cases_aux system step _ _ rfl with
        ⟨function', argument', rfl, functionStep, argumentStep⟩ | ⟨body, isLambda⟩ |
          ⟨arity, left', right', rule, instantiation₂, instantiation', agrees, arguments, rfl⟩
      · obtain ⟨first, functionShape, functionPar, _⟩ :=
          leftSide_prefix_par system functionSide (by omega) functionLinear instantiation functionStep
        obtain ⟨second, argumentShape, argumentPar, argumentRest⟩ :=
          pattern_par system argumentPattern argumentLinear instantiation argumentStep
        exact .inr ⟨join first second function,
          join_app system linear functionShape functionPar argumentShape argumentPar argumentRest⟩
      · exact absurd isLambda (not_lambda_of_leftSide system functionSide instantiation body)
      · exact .inl ⟨arity, left', right', rule, instantiation₂, instantiation', agrees,
          parSub_pointwise system arguments, rfl⟩

/-- At an equation instance, parallel reduction either contracts some equation at
the root, or reduces inside the pattern variables only. -/
theorem redex_par {n : Nat} {source target : Tm Head n} (redex : Redex system source)
    (step : ParRed headEq system.schema source target) :
    (∃ (arity : Nat) (left right : Tm Head arity) (_ : system.schema left right)
        (instantiation instantiation' : Sub Head arity n),
      subst instantiation left = source ∧
      (∀ index, ParRed headEq system.schema (instantiation index) (instantiation' index)) ∧
      target = subst instantiation' right) ∨
    (∃ substitution' : Sub Head redex.slots n, target = subst substitution' redex.left ∧
      (∀ index, 0 < variableMultiplicity index redex.left →
        ParRed headEq system.schema (redex.instantiation index) (substitution' index)) ∧
      (∀ index, variableMultiplicity index redex.left = 0 →
        substitution' index = redex.instantiation index)) := by
  obtain ⟨name, _, positive, side⟩ := system.left redex.rule
  have step' : ParRed headEq system.schema (subst redex.instantiation redex.left) target := by
    rw [redex.agrees]; exact step
  rcases redex_par_aux system side rfl positive (system.linear redex.rule) redex.instantiation
      step' with ⟨arity, left, right, rule, instantiation, instantiation', agrees, pointwise, shape⟩ |
      second
  · exact .inl ⟨arity, left, right, rule, instantiation, instantiation',
      agrees.trans redex.agrees, pointwise, shape⟩
  · exact .inr second

end Parallel

/-! ## The complete development

Whether a term is an equation instance is a proposition about the schema
family, which need not be decidable; the development decides it classically.
It cannot do otherwise: a development for every constructor system decides
every proposition (`em_of_development`). -/

section Develop

variable {headEq : Head → Head → Prop} (system : System Head)

open Classical in
/-- Contract every equation instance, beta redex and projection redex visible in
the input, developing their components.  Newly exposed redexes are left. -/
noncomputable def develop {n : Nat} (term : Tm Head n) : Tm Head n :=
  if found : Nonempty (Redex system term) then
    subst (fun index =>
      if _occurs : 0 < variableMultiplicity index (Classical.choice found).left then
        develop ((Classical.choice found).instantiation index)
      else (Classical.choice found).instantiation index) (Classical.choice found).right
  else
    match term with
    | .var index => .var index
    | .const name => .const name
    | .head value => .head value
    | .pi domain codomain => .pi (develop domain) (develop codomain)
    | .sigma domain codomain => .sigma (develop domain) (develop codomain)
    | .id carrier left right => .id (develop carrier) (develop left) (develop right)
    | .lam body => .lam (develop body)
    | .app (.lam body) argument => inst0 (develop argument) (develop body)
    | .app function argument => .app (develop function) (develop argument)
    | .pair first second => .pair (develop first) (develop second)
    | .fst (.pair first _) => develop first
    | .fst package => .fst (develop package)
    | .snd (.pair _ second) => develop second
    | .snd package => .snd (develop package)
    | .refl inner => .refl (develop inner)
termination_by sizeOf term
decreasing_by
  all_goals first
    | exact Redex.sizeOf_lt (Classical.choice found) _occurs
    | (simp_wf; omega)

theorem not_redex_lam {n : Nat} (body : Tm Head (n + 1)) :
    ¬ Nonempty (Redex system (.lam body : Tm Head n)) :=
  not_redex_of_spineHead system (fun _ _ found => by simp [spineHead] at found)

theorem not_redex_pair {n : Nat} (first second : Tm Head n) :
    ¬ Nonempty (Redex system (.pair first second)) :=
  not_redex_of_spineHead system (fun _ _ found => by simp [spineHead] at found)

theorem develop_lam {n : Nat} (body : Tm Head (n + 1)) :
    develop system (.lam body : Tm Head n) = .lam (develop system body) := by
  rw [develop, dif_neg (not_redex_lam system body)]

theorem develop_pair {n : Nat} (first second : Tm Head n) :
    develop system (.pair first second) = .pair (develop system first) (develop system second) := by
  rw [develop, dif_neg (not_redex_pair system first second)]

/-- Every parallel reduct of a term reaches its complete development. -/
theorem par_develop (symmetric : Std.Symm headEq) :
    ∀ (bound : Nat) {n : Nat} {source target : Tm Head n}, sizeOf source < bound →
      ParRed headEq system.schema source target →
        ParRed headEq system.schema target (develop system source) := by
  intro bound
  induction bound with
  | zero => intro n source target small; exact absurd small (Nat.not_lt_zero _)
  | succ bound ih =>
    intro n source target small step
    by_cases found : Nonempty (Redex system source)
    · rw [develop, dif_pos found]
      have key : ∀ redex : Redex system source,
          ParRed headEq system.schema target (subst (fun index =>
            if occurs : 0 < variableMultiplicity index redex.left then
              develop system (redex.instantiation index)
            else redex.instantiation index) redex.right) := by
        intro redex
        rcases redex_par system redex step with
          ⟨arity, left, right, rule, instantiation, instantiation', agrees, pointwise, rfl⟩ |
          ⟨substitution', rfl, occurringPar, rest⟩
        · have developed : subst (fun index =>
              if occurs : 0 < variableMultiplicity index redex.left then
                develop system (redex.instantiation index)
              else redex.instantiation index) redex.right =
              subst (fun index => develop system (redex.instantiation index)) redex.right :=
            subst_congr_occurring redex.right (fun index occurs => by
              simp only [dif_pos (system.covered redex.rule index occurs)])
          rw [developed, system.determined redex.rule rule redex.instantiation instantiation
            (redex.agrees.trans agrees.symm) (develop system)]
          have agreeRight : subst instantiation' right = subst (fun index =>
              if 0 < variableMultiplicity index left then instantiation' index
              else develop system (instantiation index)) right :=
            subst_congr_occurring right (fun index occurs => by
              simp only [system.covered rule index occurs, ite_true])
          rw [agreeRight]
          apply par_substitute _ (par_refl right)
          intro index
          by_cases occurs : 0 < variableMultiplicity index left
          · simp only [occurs, ite_true]
            obtain ⟨_, _, _, side⟩ := system.left rule
            have size := sizeOf_le_leftSide side instantiation occurs
            rw [agrees] at size
            exact ih (by omega) (pointwise index)
          · simp only [occurs, ite_false]
            exact par_refl _
        · refine .algebraic redex.rule substitution' _ (parSub_of_pointwise system ?_)
          intro index
          by_cases occurs : 0 < variableMultiplicity index redex.left
          · simp only [dif_pos occurs]
            have size := redex.sizeOf_lt occurs
            exact ih (by omega) (occurringPar index occurs)
          · have absent : variableMultiplicity index redex.left = 0 := by omega
            simp only [dif_neg occurs, rest index absent]
            exact par_refl _
      exact key _
    · rw [develop, dif_neg found]
      cases step with
      | var index => exact .var index
      | const name => exact .const name
      | head value => exact .head value
      | headRel equality => exact .headRel (symmetric.symm _ _ equality)
      | pi domainStep codomainStep =>
          simp only [Tm.pi.sizeOf_spec] at small
          exact .pi (ih (by omega) domainStep) (ih (by omega) codomainStep)
      | sigma domainStep codomainStep =>
          simp only [Tm.sigma.sizeOf_spec] at small
          exact .sigma (ih (by omega) domainStep) (ih (by omega) codomainStep)
      | id carrierStep leftStep rightStep =>
          simp only [Tm.id.sizeOf_spec] at small
          exact .id (ih (by omega) carrierStep) (ih (by omega) leftStep) (ih (by omega) rightStep)
      | lam bodyStep =>
          simp only [Tm.lam.sizeOf_spec] at small
          exact .lam (ih (by omega) bodyStep)
      | @app _ function function' argument argument' functionStep argumentStep =>
          simp only [Tm.app.sizeOf_spec] at small
          have functionDevelop := ih (by omega) functionStep
          have argumentDevelop := ih (by omega) argumentStep
          cases function with
          | lam body =>
              obtain ⟨body', rfl, _⟩ := par_lam_inv system functionStep
              rw [develop_lam] at functionDevelop
              obtain ⟨body'', equality, bodyDevelop⟩ := par_lam_inv system functionDevelop
              obtain rfl := (Tm.lam.inj equality).symm
              exact .betaPi bodyDevelop argumentDevelop
          | _ => exact .app functionDevelop argumentDevelop
      | pair firstStep secondStep =>
          simp only [Tm.pair.sizeOf_spec] at small
          exact .pair (ih (by omega) firstStep) (ih (by omega) secondStep)
      | @fst _ package package' packageStep =>
          simp only [Tm.fst.sizeOf_spec] at small
          have packageDevelop := ih (by omega) packageStep
          cases package with
          | pair first second =>
              obtain ⟨first', second', rfl, _, _⟩ := par_pair_inv system packageStep
              rw [develop_pair] at packageDevelop
              obtain ⟨first'', second'', equality, firstDevelop, secondDevelop⟩ :=
                par_pair_inv system packageDevelop
              obtain ⟨rfl, rfl⟩ := Tm.pair.inj equality
              exact .betaSigmaFst firstDevelop secondDevelop
          | _ => exact .fst packageDevelop
      | @snd _ package package' packageStep =>
          simp only [Tm.snd.sizeOf_spec] at small
          have packageDevelop := ih (by omega) packageStep
          cases package with
          | pair first second =>
              obtain ⟨first', second', rfl, _, _⟩ := par_pair_inv system packageStep
              rw [develop_pair] at packageDevelop
              obtain ⟨first'', second'', equality, firstDevelop, secondDevelop⟩ :=
                par_pair_inv system packageDevelop
              obtain ⟨rfl, rfl⟩ := Tm.pair.inj equality
              exact .betaSigmaSnd firstDevelop secondDevelop
          | _ => exact .snd packageDevelop
      | refl innerStep =>
          simp only [Tm.refl.sizeOf_spec] at small
          exact .refl (ih (by omega) innerStep)
      | betaPi bodyStep argumentStep =>
          simp only [Tm.app.sizeOf_spec, Tm.lam.sizeOf_spec] at small
          exact par_inst0 (ih (by omega) argumentStep) (ih (by omega) bodyStep)
      | betaSigmaFst firstStep _ =>
          simp only [Tm.fst.sizeOf_spec, Tm.pair.sizeOf_spec] at small
          exact ih (by omega) firstStep
      | betaSigmaSnd _ secondStep =>
          simp only [Tm.snd.sizeOf_spec, Tm.pair.sizeOf_spec] at small
          exact ih (by omega) secondStep
      | algebraic rule instantiation _ _ =>
          exact absurd (redex_of_algebraic system rule instantiation) found

end Develop

/-! ## The development cannot be constructive

A complete development that works for every constructor system decides every
proposition `P`: guard the single equation `f x = c` by `P` and compare the
development of `f x` with `c`. -/

namespace Guarded

/-- The equation `f x = c`, present exactly when `P` holds. -/
def schema (P : Prop) : SchemaFamily Empty := fun {arity} left right =>
  P ∧ (⟨arity, (left, right)⟩ : Σ arity : Nat, Tm Empty arity × Tm Empty arity) =
    ⟨1, (.app (.const `f) (.var 0), .const `c)⟩

/-- The constructor system of the guarded equation. -/
def system (P : Prop) : System Empty where
  schema := schema P
  defined := fun name => name = `f
  arity := fun _ => 1
  left := by
    intro _ _ _ ⟨_, equal⟩
    obtain ⟨rfl, pairs⟩ := Sigma.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq pairs)
    exact ⟨`f, rfl, Nat.one_pos, .app (.const `f) (.var 0)⟩
  linear := by
    intro _ _ _ ⟨_, equal⟩
    obtain ⟨rfl, pairs⟩ := Sigma.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq pairs)
    intro index
    refine Fin.cases ?_ (fun prior => prior.elim0) index
    decide
  covered := by
    intro _ _ _ ⟨_, equal⟩ index occurs
    obtain ⟨rfl, pairs⟩ := Sigma.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq pairs)
    exact absurd occurs (Nat.lt_irrefl 0)
  determined := by
    intro _ _ _ _ _ _ _ _ ⟨_, equal⟩ ⟨_, equal'⟩ _ _ _ _
    obtain ⟨rfl, pairs⟩ := Sigma.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq pairs)
    obtain ⟨rfl, pairs'⟩ := Sigma.mk.inj equal'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq pairs')
    rfl

end Guarded

/-- A complete development for every constructor system decides every
proposition. -/
theorem em_of_development (develop : System Empty → ∀ {n : Nat}, Tm Empty n → Tm Empty n)
    (reaches : ∀ (system : System Empty) {n : Nat} {source target : Tm Empty n},
      ParRed (fun _ _ => False) system.schema source target →
        ParRed (fun _ _ => False) system.schema target (develop system source))
    (P : Prop) : P ∨ ¬ P := by
  let source : Tm Empty 1 := .app (.const `f) (.var 0)
  by_cases found : develop (Guarded.system P) source = .const `c
  · left
    have step := reaches (Guarded.system P) (par_refl source)
    rw [found] at step
    rcases par_app_cases (Guarded.system P) step with
      ⟨_, _, equal, _, _⟩ | ⟨_, _, _, equal, _, _, _⟩ | ⟨_, _, _, rule, _, _, _, _, _⟩
    · cases equal
    · cases equal
    · exact (show P ∧ _ from rule).1
  · right
    intro holds
    have rule : (Guarded.system P).schema (.app (.const `f) (.var 0) : Tm Empty 1) (.const `c) :=
      ⟨holds, rfl⟩
    have step : ParRed (fun _ _ => False) (Guarded.system P).schema source (.const `c) :=
      .algebraic rule (fun index => .var index) (fun index => .var index) (parSub_refl _)
    exact found (par_const (Guarded.system P) (reaches (Guarded.system P) step))

/-! ## The parallel diamond

The complete development has to decide whether a term is an equation
instance, and a schema family need not decide it.  The diamond does not need
to: it is proved by induction on the node count of the source.  Two steps at
the same constructor are joined componentwise.  At an equation instance, a
contraction is joined with any other step through the instantiating terms,
which are smaller; two contractions have equal instances before reduction,
because the system determines its contractions. -/

section Diamond

variable {headEq : Head → Head → Prop} (system : System Head)

private theorem liftSub_par {m n : Nat} {first second : Sub Head m n}
    (pointwise : ∀ index, ParRed headEq system.schema (first index) (second index)) :
    ∀ index, ParRed headEq system.schema (liftSub first index) (liftSub second index) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact .var 0
  · exact par_rename wk (pointwise prior)

private theorem liftSub_small {bound m n : Nat} (nontrivial : 1 < bound)
    {substitution : Sub Head m n} {body : Tm Head (m + 1)}
    (small : ∀ index, 0 < variableMultiplicity index.succ body →
      nodeCount (substitution index) < bound) :
    ∀ index, 0 < variableMultiplicity index body →
      nodeCount (liftSub substitution index) < bound := by
  intro index
  refine Fin.cases (fun _ => nontrivial) (fun prior occurs => ?_) index
  rw [liftSub_succ, nodeCount_rename]
  exact small prior occurs

private theorem join_var_right (bound : Nat)
    (diamond : ∀ {n : Nat} {source left right : Tm Head n}, nodeCount source < bound →
      ParRed headEq system.schema source left → ParRed headEq system.schema source right →
        ∃ common, ParRed headEq system.schema left common ∧
          ParRed headEq system.schema right common)
    {m m' n : Nat} {term : Tm Head m} {index' : Fin m'}
    {first firstTarget : Sub Head m n} {second secondTarget : Sub Head m' n}
    (same : subst first term = second index')
    (firstPar : ∀ index, ParRed headEq system.schema (first index) (firstTarget index))
    (secondPar : ∀ index, ParRed headEq system.schema (second index) (secondTarget index))
    (small : nodeCount (second index') < bound) :
    ∃ common, ParRed headEq system.schema (subst firstTarget term) common ∧
      ParRed headEq system.schema (secondTarget index') common := by
  have otherStep : ParRed headEq system.schema (second index') (subst firstTarget term) := by
    rw [← same]
    exact par_substitute firstPar (par_refl term)
  obtain ⟨common, left, right⟩ := diamond small (secondPar index') otherStep
  exact ⟨common, right, left⟩

/-- Equal instances of two terms stay joinable when both instantiations are
reduced in parallel, provided the diamond holds at every instantiating term
that occurs. -/
theorem join_instances (bound : Nat) (nontrivial : 1 < bound)
    (diamond : ∀ {n : Nat} {source left right : Tm Head n}, nodeCount source < bound →
      ParRed headEq system.schema source left → ParRed headEq system.schema source right →
        ∃ common, ParRed headEq system.schema left common ∧
          ParRed headEq system.schema right common) :
    ∀ {m : Nat} (term : Tm Head m) {m' n : Nat} (term' : Tm Head m')
      {first firstTarget : Sub Head m n} {second secondTarget : Sub Head m' n},
      subst first term = subst second term' →
      (∀ index, ParRed headEq system.schema (first index) (firstTarget index)) →
      (∀ index, ParRed headEq system.schema (second index) (secondTarget index)) →
      (∀ index, 0 < variableMultiplicity index term → nodeCount (first index) < bound) →
      (∀ index, 0 < variableMultiplicity index term' → nodeCount (second index) < bound) →
      ∃ common, ParRed headEq system.schema (subst firstTarget term) common ∧
        ParRed headEq system.schema (subst secondTarget term') common := by
  intro m term
  induction term with
  | var candidate =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar firstSmall _
      have otherStep :
          ParRed headEq system.schema (first candidate) (subst secondTarget term') := by
        rw [show first candidate = subst second term' from same]
        exact par_substitute secondPar (par_refl term')
      exact diamond (firstSmall candidate (by simp [variableMultiplicity])) (firstPar candidate)
        otherStep
  | const name =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar _ secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | const name' =>
          simp only [subst, Tm.const.injEq] at same
          subst same
          exact ⟨_, .const _, .const _⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | head value =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar _ secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | head value' =>
          simp only [subst, Tm.head.injEq] at same
          subst same
          exact ⟨_, .head _, .head _⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | pi domain codomain domainIH codomainIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | pi domain' codomain' =>
          simp only [subst, Tm.pi.injEq] at same
          obtain ⟨domainCommon, domainLeft, domainRight⟩ :=
            domainIH domain' same.1 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          obtain ⟨codomainCommon, codomainLeft, codomainRight⟩ :=
            codomainIH codomain' same.2 (liftSub_par system firstPar) (liftSub_par system secondPar)
              (liftSub_small nontrivial fun index occurs =>
                firstSmall index (by simp only [variableMultiplicity]; omega))
              (liftSub_small nontrivial fun index occurs =>
                secondSmall index (by simp only [variableMultiplicity]; omega))
          exact ⟨.pi domainCommon codomainCommon, .pi domainLeft codomainLeft,
            .pi domainRight codomainRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | sigma domain codomain domainIH codomainIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | sigma domain' codomain' =>
          simp only [subst, Tm.sigma.injEq] at same
          obtain ⟨domainCommon, domainLeft, domainRight⟩ :=
            domainIH domain' same.1 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          obtain ⟨codomainCommon, codomainLeft, codomainRight⟩ :=
            codomainIH codomain' same.2 (liftSub_par system firstPar) (liftSub_par system secondPar)
              (liftSub_small nontrivial fun index occurs =>
                firstSmall index (by simp only [variableMultiplicity]; omega))
              (liftSub_small nontrivial fun index occurs =>
                secondSmall index (by simp only [variableMultiplicity]; omega))
          exact ⟨.sigma domainCommon codomainCommon, .sigma domainLeft codomainLeft,
            .sigma domainRight codomainRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | id carrier left right carrierIH leftIH rightIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | id carrier' left' right' =>
          simp only [subst, Tm.id.injEq] at same
          obtain ⟨carrierCommon, carrierLeft, carrierRight⟩ :=
            carrierIH carrier' same.1 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          obtain ⟨leftCommon, leftLeft, leftRight⟩ :=
            leftIH left' same.2.1 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          obtain ⟨rightCommon, rightLeft, rightRight⟩ :=
            rightIH right' same.2.2 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          exact ⟨.id carrierCommon leftCommon rightCommon, .id carrierLeft leftLeft rightLeft,
            .id carrierRight leftRight rightRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | lam body bodyIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | lam body' =>
          simp only [subst, Tm.lam.injEq] at same
          obtain ⟨bodyCommon, bodyLeft, bodyRight⟩ :=
            bodyIH body' same (liftSub_par system firstPar) (liftSub_par system secondPar)
              (liftSub_small nontrivial fun index occurs => firstSmall index occurs)
              (liftSub_small nontrivial fun index occurs => secondSmall index occurs)
          exact ⟨.lam bodyCommon, .lam bodyLeft, .lam bodyRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | app function argument functionIH argumentIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | app function' argument' =>
          simp only [subst, Tm.app.injEq] at same
          obtain ⟨functionCommon, functionLeft, functionRight⟩ :=
            functionIH function' same.1 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          obtain ⟨argumentCommon, argumentLeft, argumentRight⟩ :=
            argumentIH argument' same.2 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          exact ⟨.app functionCommon argumentCommon, .app functionLeft argumentLeft,
            .app functionRight argumentRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | pair left right leftIH rightIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | pair left' right' =>
          simp only [subst, Tm.pair.injEq] at same
          obtain ⟨leftCommon, leftLeft, leftRight⟩ :=
            leftIH left' same.1 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          obtain ⟨rightCommon, rightLeft, rightRight⟩ :=
            rightIH right' same.2 firstPar secondPar
              (fun index occurs => firstSmall index (by simp only [variableMultiplicity]; omega))
              (fun index occurs => secondSmall index (by simp only [variableMultiplicity]; omega))
          exact ⟨.pair leftCommon rightCommon, .pair leftLeft rightLeft,
            .pair leftRight rightRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | fst package packageIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | fst package' =>
          simp only [subst, Tm.fst.injEq] at same
          obtain ⟨common, packageLeft, packageRight⟩ :=
            packageIH package' same firstPar secondPar firstSmall secondSmall
          exact ⟨.fst common, .fst packageLeft, .fst packageRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | snd package packageIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | snd package' =>
          simp only [subst, Tm.snd.injEq] at same
          obtain ⟨common, packageLeft, packageRight⟩ :=
            packageIH package' same firstPar secondPar firstSmall secondSmall
          exact ⟨.snd common, .snd packageLeft, .snd packageRight⟩
      | _ => simp only [subst, reduceCtorEq] at same
  | refl inner innerIH =>
      intro m' n term' first firstTarget second secondTarget same firstPar secondPar
        firstSmall secondSmall
      cases term' with
      | var index' =>
          exact join_var_right system bound diamond same firstPar secondPar
            (secondSmall index' (by simp [variableMultiplicity]))
      | refl inner' =>
          simp only [subst, Tm.refl.injEq] at same
          obtain ⟨common, innerLeft, innerRight⟩ :=
            innerIH inner' same firstPar secondPar firstSmall secondSmall
          exact ⟨.refl common, .refl innerLeft, .refl innerRight⟩
      | _ => simp only [subst, reduceCtorEq] at same

/-- The contraction of an equation instance is joinable with every parallel
reduct of the instance, once the diamond holds below the instance. -/
theorem join_contraction (bound : Nat)
    (diamond : ∀ {n : Nat} {source left right : Tm Head n}, nodeCount source < bound →
      ParRed headEq system.schema source left → ParRed headEq system.schema source right →
        ∃ common, ParRed headEq system.schema left common ∧
          ParRed headEq system.schema right common)
    {arity n : Nat} {left right : Tm Head arity} (rule : system.schema left right)
    {instantiation instantiation' : Sub Head arity n}
    (arguments : ∀ index,
      ParRed headEq system.schema (instantiation index) (instantiation' index))
    (small : nodeCount (subst instantiation left) ≤ bound) {target : Tm Head n}
    (step : ParRed headEq system.schema (subst instantiation left) target) :
    ∃ common, ParRed headEq system.schema (subst instantiation' right) common ∧
      ParRed headEq system.schema target common := by
  obtain ⟨_, _, positive, side⟩ := system.left rule
  have nontrivial : 1 < bound :=
    Nat.lt_of_lt_of_le (one_lt_nodeCount_leftSide side positive instantiation) small
  rcases redex_par system ⟨arity, left, right, rule, instantiation, rfl⟩ step with
    ⟨_, left₂, right₂, rule₂, instantiation₂, instantiation₂', agrees, arguments₂,
      rfl⟩ |
    ⟨substitution, rfl, occurringPar, rest⟩
  · obtain ⟨_, _, _, side₂⟩ := system.left rule₂
    exact join_instances system bound nontrivial diamond right right₂
      (system.determined rule rule₂ instantiation instantiation₂ agrees.symm (fun term => term))
      arguments arguments₂
      (fun index occurs => Nat.lt_of_lt_of_le
        (nodeCount_lt_leftSide side instantiation (system.covered rule index occurs)) small)
      (fun index occurs => Nat.lt_of_lt_of_le (agrees ▸
        nodeCount_lt_leftSide side₂ instantiation₂ (system.covered rule₂ index occurs)) small)
  · have joins : ∀ index, ∃ value, ParRed headEq system.schema (instantiation' index) value ∧
        ParRed headEq system.schema (substitution index) value := by
      intro index
      by_cases occurs : 0 < variableMultiplicity index left
      · exact diamond (Nat.lt_of_lt_of_le (nodeCount_lt_leftSide side instantiation occurs) small)
          (arguments index) (occurringPar index occurs)
      · rw [rest index (Nat.eq_zero_of_not_pos occurs)]
        exact ⟨instantiation' index, par_refl _, arguments index⟩
    obtain ⟨joint, jointPar⟩ := exists_sub_of_pointwise joins
    exact ⟨subst joint right, par_substitute (fun index => (jointPar index).1) (par_refl right),
      .algebraic rule substitution joint
        (parSub_of_pointwise system (fun index => (jointPar index).2))⟩

/-- The one-step parallel diamond of a constructor system with symmetric head
equality, for sources with fewer than `bound` nodes. -/
theorem par_diamond (symmetric : Std.Symm headEq) :
    ∀ (bound : Nat) {n : Nat} {source left right : Tm Head n}, nodeCount source < bound →
      ParRed headEq system.schema source left → ParRed headEq system.schema source right →
        ∃ common, ParRed headEq system.schema left common ∧
          ParRed headEq system.schema right common := by
  intro bound
  induction bound with
  | zero => intro n source left right small; exact absurd small (Nat.not_lt_zero _)
  | succ bound ih =>
    intro n source left right small step other
    cases step with
    | var index =>
        obtain rfl := par_var system other
        exact ⟨_, .var index, .var index⟩
    | const name =>
        obtain rfl := par_const system other
        exact ⟨_, .const name, .const name⟩
    | head value => exact ⟨right, other, par_refl right⟩
    | headRel related =>
        rcases par_head_inv system other with rfl | ⟨_, related', rfl⟩
        · exact ⟨_, .headRel (symmetric.symm _ _ related), .head _⟩
        · exact ⟨_, .headRel (symmetric.symm _ _ related),
            .headRel (symmetric.symm _ _ related')⟩
    | pi domainStep codomainStep =>
        obtain ⟨_, _, rfl, domainStep', codomainStep'⟩ := par_pi_inv system other
        simp only [nodeCount] at small
        obtain ⟨domainCommon, domainLeft, domainRight⟩ := ih (by omega) domainStep domainStep'
        obtain ⟨codomainCommon, codomainLeft, codomainRight⟩ :=
          ih (by omega) codomainStep codomainStep'
        exact ⟨.pi domainCommon codomainCommon, .pi domainLeft codomainLeft,
          .pi domainRight codomainRight⟩
    | sigma domainStep codomainStep =>
        obtain ⟨_, _, rfl, domainStep', codomainStep'⟩ := par_sigma_inv system other
        simp only [nodeCount] at small
        obtain ⟨domainCommon, domainLeft, domainRight⟩ := ih (by omega) domainStep domainStep'
        obtain ⟨codomainCommon, codomainLeft, codomainRight⟩ :=
          ih (by omega) codomainStep codomainStep'
        exact ⟨.sigma domainCommon codomainCommon, .sigma domainLeft codomainLeft,
          .sigma domainRight codomainRight⟩
    | id carrierStep leftStep rightStep =>
        obtain ⟨_, _, _, rfl, carrierStep', leftStep', rightStep'⟩ := par_id_inv system other
        simp only [nodeCount] at small
        obtain ⟨carrierCommon, carrierLeft, carrierRight⟩ :=
          ih (by omega) carrierStep carrierStep'
        obtain ⟨leftCommon, leftLeft, leftRight⟩ := ih (by omega) leftStep leftStep'
        obtain ⟨rightCommon, rightLeft, rightRight⟩ := ih (by omega) rightStep rightStep'
        exact ⟨.id carrierCommon leftCommon rightCommon, .id carrierLeft leftLeft rightLeft,
          .id carrierRight leftRight rightRight⟩
    | lam bodyStep =>
        obtain ⟨_, rfl, bodyStep'⟩ := par_lam_inv system other
        simp only [nodeCount] at small
        obtain ⟨bodyCommon, bodyLeft, bodyRight⟩ := ih (by omega) bodyStep bodyStep'
        exact ⟨.lam bodyCommon, .lam bodyLeft, .lam bodyRight⟩
    | app functionStep argumentStep =>
        simp only [nodeCount] at small
        rcases par_app_cases system other with
          ⟨_, _, rfl, functionStep', argumentStep'⟩ |
          ⟨_, _, _, rfl, rfl, bodyStep', argumentStep'⟩ |
          ⟨_, left', right', rule, instantiation, instantiation', agrees, arguments, rfl⟩
        · obtain ⟨functionCommon, functionLeft, functionRight⟩ :=
            ih (by omega) functionStep functionStep'
          obtain ⟨argumentCommon, argumentLeft, argumentRight⟩ :=
            ih (by omega) argumentStep argumentStep'
          exact ⟨.app functionCommon argumentCommon, .app functionLeft argumentLeft,
            .app functionRight argumentRight⟩
        · obtain ⟨_, rfl, bodyStep⟩ := par_lam_inv system functionStep
          simp only [nodeCount] at small
          obtain ⟨bodyCommon, bodyLeft, bodyRight⟩ := ih (by omega) bodyStep bodyStep'
          obtain ⟨argumentCommon, argumentLeft, argumentRight⟩ :=
            ih (by omega) argumentStep argumentStep'
          exact ⟨inst0 argumentCommon bodyCommon, .betaPi bodyLeft argumentLeft,
            par_inst0 argumentRight bodyRight⟩
        · obtain ⟨common, contracted, joined⟩ :=
            join_contraction system bound ih rule arguments
              (by rw [agrees]; simp only [nodeCount]; omega)
              (by rw [agrees]; exact .app functionStep argumentStep)
          exact ⟨common, joined, contracted⟩
    | pair firstStep secondStep =>
        obtain ⟨_, _, rfl, firstStep', secondStep'⟩ := par_pair_inv system other
        simp only [nodeCount] at small
        obtain ⟨firstCommon, firstLeft, firstRight⟩ := ih (by omega) firstStep firstStep'
        obtain ⟨secondCommon, secondLeft, secondRight⟩ := ih (by omega) secondStep secondStep'
        exact ⟨.pair firstCommon secondCommon, .pair firstLeft secondLeft,
          .pair firstRight secondRight⟩
    | fst packageStep =>
        simp only [nodeCount] at small
        rcases par_fst_cases system other with
          ⟨_, rfl, packageStep'⟩ | ⟨_, _, _, _, rfl, rfl, firstStep', _⟩
        · obtain ⟨common, packageLeft, packageRight⟩ := ih (by omega) packageStep packageStep'
          exact ⟨.fst common, .fst packageLeft, .fst packageRight⟩
        · obtain ⟨_, second, rfl, firstStep, _⟩ := par_pair_inv system packageStep
          simp only [nodeCount] at small
          obtain ⟨common, firstLeft, firstRight⟩ := ih (by omega) firstStep firstStep'
          exact ⟨common, .betaSigmaFst firstLeft (par_refl second), firstRight⟩
    | snd packageStep =>
        simp only [nodeCount] at small
        rcases par_snd_cases system other with
          ⟨_, rfl, packageStep'⟩ | ⟨_, _, _, _, rfl, rfl, _, secondStep'⟩
        · obtain ⟨common, packageLeft, packageRight⟩ := ih (by omega) packageStep packageStep'
          exact ⟨.snd common, .snd packageLeft, .snd packageRight⟩
        · obtain ⟨first, _, rfl, _, secondStep⟩ := par_pair_inv system packageStep
          simp only [nodeCount] at small
          obtain ⟨common, secondLeft, secondRight⟩ := ih (by omega) secondStep secondStep'
          exact ⟨common, .betaSigmaSnd (par_refl first) secondLeft, secondRight⟩
    | refl innerStep =>
        obtain ⟨_, rfl, innerStep'⟩ := par_refl_inv system other
        simp only [nodeCount] at small
        obtain ⟨common, innerLeft, innerRight⟩ := ih (by omega) innerStep innerStep'
        exact ⟨.refl common, .refl innerLeft, .refl innerRight⟩
    | betaPi bodyStep argumentStep =>
        simp only [nodeCount] at small
        rcases par_app_cases system other with
          ⟨_, _, rfl, functionStep', argumentStep'⟩ |
          ⟨_, _, _, same, rfl, bodyStep', argumentStep'⟩ |
          ⟨_, left', right', rule, instantiation, instantiation', agrees, arguments, rfl⟩
        · obtain ⟨_, rfl, bodyStep'⟩ := par_lam_inv system functionStep'
          obtain ⟨bodyCommon, bodyLeft, bodyRight⟩ := ih (by omega) bodyStep bodyStep'
          obtain ⟨argumentCommon, argumentLeft, argumentRight⟩ :=
            ih (by omega) argumentStep argumentStep'
          exact ⟨inst0 argumentCommon bodyCommon, par_inst0 argumentLeft bodyLeft,
            .betaPi bodyRight argumentRight⟩
        · obtain rfl := Tm.lam.inj same
          obtain ⟨bodyCommon, bodyLeft, bodyRight⟩ := ih (by omega) bodyStep bodyStep'
          obtain ⟨argumentCommon, argumentLeft, argumentRight⟩ :=
            ih (by omega) argumentStep argumentStep'
          exact ⟨inst0 argumentCommon bodyCommon, par_inst0 argumentLeft bodyLeft,
            par_inst0 argumentRight bodyRight⟩
        · obtain ⟨common, contracted, joined⟩ :=
            join_contraction system bound ih rule arguments
              (by rw [agrees]; simp only [nodeCount]; omega)
              (by rw [agrees]; exact .betaPi bodyStep argumentStep)
          exact ⟨common, joined, contracted⟩
    | betaSigmaFst firstStep secondStep =>
        simp only [nodeCount] at small
        rcases par_fst_cases system other with
          ⟨_, rfl, packageStep'⟩ | ⟨_, _, _, _, same, rfl, firstStep', _⟩
        · obtain ⟨_, second, rfl, firstStep', _⟩ := par_pair_inv system packageStep'
          obtain ⟨common, firstLeft, firstRight⟩ := ih (by omega) firstStep firstStep'
          exact ⟨common, firstLeft, .betaSigmaFst firstRight (par_refl second)⟩
        · obtain ⟨rfl, rfl⟩ := Tm.pair.inj same
          exact ih (by omega) firstStep firstStep'
    | betaSigmaSnd firstStep secondStep =>
        simp only [nodeCount] at small
        rcases par_snd_cases system other with
          ⟨_, rfl, packageStep'⟩ | ⟨_, _, _, _, same, rfl, _, secondStep'⟩
        · obtain ⟨first, _, rfl, _, secondStep'⟩ := par_pair_inv system packageStep'
          obtain ⟨common, secondLeft, secondRight⟩ := ih (by omega) secondStep secondStep'
          exact ⟨common, secondLeft, .betaSigmaSnd (par_refl first) secondRight⟩
        · obtain ⟨rfl, rfl⟩ := Tm.pair.inj same
          exact ih (by omega) secondStep secondStep'
    | algebraic rule instantiation instantiation' arguments =>
        exact join_contraction system bound ih rule (parSub_pointwise system arguments)
          (Nat.le_of_lt_succ small) other

end Diamond

/-- A schema presentation whose schemas form a constructor system, with
symmetric head equality, has a complete development. -/
noncomputable def completeDevelopment {rules : Rules Head} (presentation : SchemaPresentation rules)
    (system : System Head) (same : ∀ {arity : Nat} (left right : Tm Head arity),
      presentation.schema left right ↔ system.schema left right)
    (symmetric : Std.Symm rules.headEq) : CompleteDevelopment presentation where
  develop := develop system
  reaches := by
    intro n source target step
    have schemaEq : (fun {arity : Nat} => presentation.schema (arity := arity)) =
        (fun {arity : Nat} => system.schema (arity := arity)) := by
      funext arity left right
      exact propext (same left right)
    have step' : ParRed rules.headEq system.schema source target := by
      simpa only [SchemaPresentation.Par, schemaEq] using step
    have reached := par_develop system symmetric (sizeOf source + 1) (Nat.lt_succ_self _) step'
    simpa only [SchemaPresentation.Par, schemaEq] using reached

/-- Church–Rosser for the original conversion of such a presentation. -/
theorem churchRosser {rules : Rules Head} (presentation : SchemaPresentation rules)
    (system : System Head) (same : ∀ {arity : Nat} (left right : Tm Head arity),
      presentation.schema left right ↔ system.schema left right)
    (symmetric : Std.Symm rules.headEq) : ChurchRosser rules := by
  have schemaEq : (fun {arity : Nat} => presentation.schema (arity := arity)) =
      (fun {arity : Nat} => system.schema (arity := arity)) := by
    funext arity left right
    exact propext (same left right)
  let simulation : ParallelSimulation rules :=
    { parallel := presentation.Par
      ofStep := presentation.step_to_par
      realizes := presentation.realization }
  have diamond : ParallelDiamond simulation := by
    intro n source left right first second
    have first' : ParRed rules.headEq system.schema source left := by
      simpa only [simulation, SchemaPresentation.Par, schemaEq] using first
    have second' : ParRed rules.headEq system.schema source right := by
      simpa only [simulation, SchemaPresentation.Par, schemaEq] using second
    obtain ⟨common, leftJoin, rightJoin⟩ :=
      par_diamond system symmetric (nodeCount source + 1) (Nat.lt_succ_self _) first' second'
    exact ⟨common, by simpa only [simulation, SchemaPresentation.Par, schemaEq] using leftJoin,
      by simpa only [simulation, SchemaPresentation.Par, schemaEq] using rightJoin⟩
  intro n first second conversion
  exact churchRosserOfParallelDiamond simulation diamond conversion

/-! ## Determined contraction from pattern disjointness -/

/-- First-order unifiability of two binder-free left sides: a variable meets
anything, constants meet when equal, applications and reflexivity meet
componentwise. -/
def unifiable : {m m' : Nat} → Tm Head m → Tm Head m' → Bool
  | _, _, .var _, _ => true
  | _, _, _, .var _ => true
  | _, _, .const first, .const second => decide (first = second)
  | _, _, .app function argument, .app function' argument' =>
      unifiable function function' && unifiable argument argument'
  | _, _, .refl term, .refl term' => unifiable term term'
  | _, _, _, _ => false

theorem unifiable_of_pattern {defined : DeclName → Prop} {m m' n : Nat} {flag flag' : Bool}
    {first : Tm Head m} {second : Tm Head m'}
    (firstPattern : Pattern defined flag first) (secondPattern : Pattern defined flag' second)
    (instantiation : Sub Head m n) (instantiation' : Sub Head m' n)
    (same : subst instantiation first = subst instantiation' second) :
    unifiable first second = true := by
  induction firstPattern generalizing m' second flag' with
  | var _ => simp [unifiable]
  | const _ =>
      cases secondPattern with
      | var _ => simp [unifiable]
      | const _ => simp only [subst, Tm.const.injEq] at same; simp [unifiable, same]
      | app _ _ => simp only [subst] at same; cases same
      | refl _ => simp only [subst] at same; cases same
  | app _ _ functionIH argumentIH =>
      cases secondPattern with
      | var _ => simp [unifiable]
      | const _ => simp only [subst] at same; cases same
      | app functionPattern' argumentPattern' =>
          simp only [subst, Tm.app.injEq] at same
          simp only [unifiable, Bool.and_eq_true]
          exact ⟨functionIH functionPattern' instantiation' same.1,
            argumentIH argumentPattern' instantiation' same.2⟩
      | refl _ => simp only [subst] at same; cases same
  | refl _ innerIH =>
      cases secondPattern with
      | var _ => simp [unifiable]
      | const _ => simp only [subst] at same; cases same
      | app _ _ => simp only [subst] at same; cases same
      | refl innerPattern' =>
          simp only [subst, Tm.refl.injEq] at same
          simpa only [unifiable] using innerIH innerPattern' instantiation' same

theorem unifiable_of_leftSide {defined : DeclName → Prop} {m m' n : Nat}
    {first : Tm Head m} {second : Tm Head m'} {name name' : DeclName} {count count' : Nat}
    (firstSide : LeftSide defined first name count) (secondSide : LeftSide defined second name' count')
    (instantiation : Sub Head m n) (instantiation' : Sub Head m' n)
    (same : subst instantiation first = subst instantiation' second) :
    unifiable first second = true := by
  induction firstSide generalizing m' second name' count' with
  | const _ =>
      cases secondSide with
      | const _ => simp only [subst, Tm.const.injEq] at same; simp [unifiable, same]
      | app _ _ => simp only [subst] at same; cases same
  | app _ argumentPattern functionIH =>
      cases secondSide with
      | const _ => simp only [subst] at same; cases same
      | app functionSide' argumentPattern' =>
          simp only [subst, Tm.app.injEq] at same
          simp only [unifiable, Bool.and_eq_true]
          exact ⟨functionIH functionSide' instantiation' same.1,
            unifiable_of_pattern argumentPattern argumentPattern' _ _ same.2⟩

/-- Instances of a pattern agree exactly on its occurring variables. -/
theorem agree_of_pattern {defined : DeclName → Prop} {m n : Nat} {flag : Bool} {term : Tm Head m}
    (pattern : Pattern defined flag term) {first second : Sub Head m n}
    (same : subst first term = subst second term) :
    ∀ index, 0 < variableMultiplicity index term → first index = second index := by
  induction pattern with
  | var candidate =>
      intro index occurs
      simp only [variableMultiplicity] at occurs
      split at occurs
      · subst index; simpa only [subst] using same
      · exfalso; omega
  | const _ => intro index occurs; simp only [variableMultiplicity] at occurs; exfalso; omega
  | @app _ function argument _ _ functionIH argumentIH =>
      intro index occurs
      simp only [subst, Tm.app.injEq] at same
      simp only [variableMultiplicity] at occurs
      by_cases inFunction : 0 < variableMultiplicity index function
      · exact functionIH same.1 index inFunction
      · exact argumentIH same.2 index (by omega)
  | refl _ ih =>
      intro index occurs
      simp only [subst, Tm.refl.injEq] at same
      exact ih same index (by simpa only [variableMultiplicity] using occurs)

theorem agree_of_leftSide {defined : DeclName → Prop} {m n : Nat} {term : Tm Head m}
    {name : DeclName} {count : Nat} (side : LeftSide defined term name count)
    {first second : Sub Head m n} (same : subst first term = subst second term) :
    ∀ index, 0 < variableMultiplicity index term → first index = second index := by
  induction side with
  | const _ => intro index occurs; simp only [variableMultiplicity] at occurs; exfalso; omega
  | @app function argument _ _ _ argumentPattern functionIH =>
      intro index occurs
      simp only [subst, Tm.app.injEq] at same
      simp only [variableMultiplicity] at occurs
      by_cases inFunction : 0 < variableMultiplicity index function
      · exact functionIH same.1 index inFunction
      · exact agree_of_pattern argumentPattern same.2 index (by omega)

/-- An equation family whose unifiable left sides belong to the same equation
determines contractions. -/
theorem determined_of_disjoint {schema : SchemaFamily Head} {defined : DeclName → Prop}
    (shape : ∀ {m : Nat} {left right : Tm Head m}, schema left right →
      ∃ name count, LeftSide defined left name count)
    (covered : ∀ {m : Nat} {left right : Tm Head m}, schema left right →
      ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left)
    (disjoint : ∀ {m m' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'},
      schema left right → schema left' right' → unifiable left left' = true →
        (⟨m, (left, right)⟩ : Σ arity : Nat, Tm Head arity × Tm Head arity) = ⟨m', (left', right')⟩) :
    ∀ {m m' n n' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'},
      schema left right → schema left' right' →
      ∀ (instantiation : Sub Head m n) (instantiation' : Sub Head m' n),
        subst instantiation left = subst instantiation' left' →
        ∀ (develop : Tm Head n → Tm Head n'),
          subst (fun index => develop (instantiation index)) right =
            subst (fun index => develop (instantiation' index)) right' := by
  intro m m' n n' left right left' right' rule rule' instantiation instantiation' same develop
  obtain ⟨name, count, side⟩ := shape rule
  obtain ⟨name', count', side'⟩ := shape rule'
  have equal := disjoint rule rule' (unifiable_of_leftSide side side' _ _ same)
  obtain ⟨rfl, pairEq⟩ := Sigma.mk.inj equal
  have pairEq' := eq_of_heq pairEq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq'
  apply subst_congr_occurring right
  intro index occurs
  rw [agree_of_leftSide side same index (covered rule index occurs)]

/-! ## One-way matching

`unifiable` lets the variables of both sides stand for anything.  To show that
an open term is not an instance of a left side, the term's own variables must
stay rigid: a pattern variable matches anything, and a variable of the term
matches only a pattern variable. -/

/-- Whether a term can be an instance of a pattern. -/
def instanceOf : {m n : Nat} → Tm Head m → Tm Head n → Bool
  | _, _, .var _, _ => true
  | _, _, .const first, .const second => decide (first = second)
  | _, _, .app function argument, .app function' argument' =>
      instanceOf function function' && instanceOf argument argument'
  | _, _, .refl term, .refl term' => instanceOf term term'
  | _, _, _, _ => false

theorem instanceOf_of_pattern {defined : DeclName → Prop} {m n : Nat} {flag : Bool}
    {pattern : Tm Head m} (shape : Pattern defined flag pattern) (instantiation : Sub Head m n) :
    instanceOf pattern (subst instantiation pattern) = true := by
  induction shape with
  | var _ => simp [instanceOf]
  | const _ => simp [instanceOf, subst]
  | app _ _ functionIH argumentIH =>
      simp only [subst, instanceOf, functionIH, argumentIH, Bool.and_self]
  | refl _ innerIH => simpa only [subst, instanceOf] using innerIH

/-- Every instance of a left side is accepted by the one-way matcher. -/
theorem instanceOf_of_leftSide {defined : DeclName → Prop} {m n : Nat} {pattern : Tm Head m}
    {name : DeclName} {count : Nat} (side : LeftSide defined pattern name count)
    (instantiation : Sub Head m n) :
    instanceOf pattern (subst instantiation pattern) = true := by
  induction side with
  | const _ => simp [instanceOf, subst]
  | app _ argumentPattern functionIH =>
      simp only [subst, instanceOf, functionIH,
        instanceOf_of_pattern argumentPattern instantiation, Bool.and_self]

/-! ## Consequences for a presented rules package

A rules package whose computation is presented as a definition by constructor
patterns is Church–Rosser.  Its conversion therefore separates dependent
functions, dependent pairs and identity types componentwise, none of them
converts to a universe head, and terms without computation steps are
separated by conversion. -/

/-- A rules package whose root computation is a definition by constructor
patterns, with symmetric head equality. -/
structure ConstructorPresentation (rules : Rules Head) where
  presentation : SchemaPresentation rules
  system : System Head
  same : ∀ {arity : Nat} (left right : Tm Head arity),
    presentation.schema left right ↔ system.schema left right
  symmetric : Std.Symm rules.headEq

/-- No computation step starts at the term. -/
def Normal (rules : Rules Head) {n : Nat} (term : Tm Head n) : Prop :=
  ∀ {target : Tm Head n}, ¬ Step rules.headEq term target rules.computation

theorem Normal.stepStar {rules : Rules Head} {n : Nat} {term target : Tm Head n}
    (normal : Normal rules term) (steps : StepStar rules term target) : target = term := by
  induction steps with
  | refl => rfl
  | tail _ step ih => subst ih; exact (normal step).elim

theorem Normal.const {rules : Rules Head} {n : Nat} (name : DeclName)
    (root : ∀ {target : Tm Head n}, ¬ rules.computation.step (.const name) target) :
    Normal rules (.const name : Tm Head n) := by
  intro target step
  cases step with
  | root rootStep => exact root rootStep

theorem Normal.app {rules : Rules Head} {n : Nat} {function argument : Tm Head n}
    (functionNormal : Normal rules function) (argumentNormal : Normal rules argument)
    (notLambda : ∀ body, function ≠ .lam body)
    (root : ∀ {target : Tm Head n}, ¬ rules.computation.step (.app function argument) target) :
    Normal rules (.app function argument) := by
  intro target step
  cases step with
  | root rootStep => exact root rootStep
  | betaPi body _ => exact notLambda body rfl
  | congAppFun inner => exact functionNormal inner
  | congAppArg inner => exact argumentNormal inner

namespace ConstructorPresentation

variable {rules : Rules Head} (equations : ConstructorPresentation rules)

include equations

theorem churchRosser : ChurchRosser rules :=
  ConstructorSystem.churchRosser equations.presentation equations.system equations.same
    equations.symmetric

/-- A root step starts at a constant spine. -/
theorem root_spineHead {n : Nat} {source target : Tm Head n}
    (step : rules.computation.step source target) :
    ∃ name count, spineHead source = some (name, count) := by
  obtain ⟨_, left, right, substitution, rule, shape, _⟩ := equations.presentation.cover step
  obtain ⟨_, _, _, side⟩ := equations.system.left ((equations.same left right).mp rule)
  exact ⟨_, _, shape ▸ spineHead_subst_leftSide side substitution⟩

theorem no_root_of_spineHead {n : Nat} {source target : Tm Head n}
    (step : rules.computation.step source target) (shape : spineHead source = none) : False := by
  obtain ⟨_, _, found⟩ := equations.root_spineHead step
  rw [shape] at found
  cases found

/-- A root step starts at an instance, under one-way matching, of the left side
of a presented equation. -/
theorem root_instance {n : Nat} {source target : Tm Head n}
    (step : rules.computation.step source target) :
    ∃ (arity : Nat) (left right : Tm Head arity), equations.presentation.schema left right ∧
      instanceOf left source = true := by
  obtain ⟨arity, left, right, substitution, rule, shape, _⟩ := equations.presentation.cover step
  obtain ⟨_, _, _, side⟩ := equations.system.left ((equations.same left right).mp rule)
  exact ⟨arity, left, right, rule, shape ▸ instanceOf_of_leftSide side substitution⟩

theorem rootPiHeadNeutral : RootPiHeadNeutral rules where
  pi := fun step => equations.no_root_of_spineHead step rfl
  head := fun step => equations.no_root_of_spineHead step rfl

theorem piConversionBoundary : PiConversionBoundary rules :=
  piConversionBoundaryOfChurchRosser equations.rootPiHeadNeutral equations.churchRosser

theorem normal_var {n : Nat} (index : Fin n) : Normal rules (.var index : Tm Head n) := by
  intro target step
  cases step with
  | root rootStep => exact equations.no_root_of_spineHead rootStep rfl

/-- Convertible terms without computation steps are equal. -/
theorem eq_of_normal {n : Nat} {first second : Tm Head n} (firstNormal : Normal rules first)
    (secondNormal : Normal rules second)
    (conversion : Conv rules.headEq first second rules.computation) : first = second := by
  obtain ⟨_, firstPath, secondPath⟩ := equations.churchRosser conversion
  exact (firstNormal.stepStar firstPath).symm.trans (secondNormal.stepStar secondPath)

theorem stepStar_pi {n : Nat} {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {target : Tm Head n} (steps : StepStar rules (.pi domain codomain) target) :
    ∃ domain' codomain', target = .pi domain' codomain' := by
  induction steps with
  | refl => exact ⟨_, _, rfl⟩
  | tail _ step ih =>
      obtain ⟨_, _, rfl⟩ := ih
      cases step with
      | root rootStep => exact (equations.no_root_of_spineHead rootStep rfl).elim
      | congPiDom _ => exact ⟨_, _, rfl⟩
      | congPiCod _ => exact ⟨_, _, rfl⟩

theorem stepStar_sigma {n : Nat} {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {target : Tm Head n} (steps : StepStar rules (.sigma domain codomain) target) :
    ∃ domain' codomain', target = .sigma domain' codomain' ∧
      StepStar rules domain domain' ∧ StepStar rules codomain codomain' := by
  induction steps with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨_, _, rfl, first, second⟩ := ih
      cases step with
      | root rootStep => exact (equations.no_root_of_spineHead rootStep rfl).elim
      | congSigmaDom inner => exact ⟨_, _, rfl, .tail first inner, second⟩
      | congSigmaCod inner => exact ⟨_, _, rfl, first, .tail second inner⟩

theorem stepStar_identity {n : Nat} {carrier left right target : Tm Head n}
    (steps : StepStar rules (.id carrier left right) target) :
    ∃ carrier' left' right', target = .id carrier' left' right' ∧
      StepStar rules carrier carrier' ∧ StepStar rules left left' ∧
        StepStar rules right right' := by
  induction steps with
  | refl => exact ⟨_, _, _, rfl, .refl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨_, _, _, rfl, first, second, third⟩ := ih
      cases step with
      | root rootStep => exact (equations.no_root_of_spineHead rootStep rfl).elim
      | congIdTy inner => exact ⟨_, _, _, rfl, .tail first inner, second, third⟩
      | congIdLeft inner => exact ⟨_, _, _, rfl, first, .tail second inner, third⟩
      | congIdRight inner => exact ⟨_, _, _, rfl, first, second, .tail third inner⟩

theorem stepStar_head {n : Nat} {head : Head} {target : Tm Head n}
    (steps : StepStar rules (.head head) target) : ∃ head', target = .head head' := by
  induction steps with
  | refl => exact ⟨_, rfl⟩
  | tail _ step ih =>
      obtain ⟨_, rfl⟩ := ih
      cases step with
      | head _ => exact ⟨_, rfl⟩
      | root rootStep => exact (equations.no_root_of_spineHead rootStep rfl).elim

theorem sigmaConversionBoundary : SigmaConversionBoundary rules where
  components := by
    intro n domain domain' codomain codomain' conversion
    obtain ⟨_, firstPath, secondPath⟩ := equations.churchRosser conversion
    obtain ⟨_, _, firstShape, firstDomain, firstCodomain⟩ := equations.stepStar_sigma firstPath
    obtain ⟨_, _, secondShape, secondDomain, secondCodomain⟩ := equations.stepStar_sigma secondPath
    obtain ⟨rfl, rfl⟩ := Tm.sigma.inj (firstShape.symm.trans secondShape)
    exact ⟨.trans _ _ _ (stepStar_implies_conv firstDomain)
        (.symm _ _ (stepStar_implies_conv secondDomain)),
      .trans _ _ _ (stepStar_implies_conv firstCodomain)
        (.symm _ _ (stepStar_implies_conv secondCodomain))⟩
  headDisjoint := by
    intro n domain codomain head conversion
    obtain ⟨_, firstPath, secondPath⟩ := equations.churchRosser conversion
    obtain ⟨_, _, firstShape, _, _⟩ := equations.stepStar_sigma firstPath
    obtain ⟨_, secondShape⟩ := equations.stepStar_head secondPath
    rw [firstShape] at secondShape
    cases secondShape

/-- Identity types are separated componentwise by conversion. -/
theorem identity_components {n : Nat} {carrier carrier' left left' right right' : Tm Head n}
    (conversion : Conv rules.headEq (.id carrier left right) (.id carrier' left' right')
      rules.computation) :
    Conv rules.headEq carrier carrier' rules.computation ∧
      Conv rules.headEq left left' rules.computation ∧
        Conv rules.headEq right right' rules.computation := by
  obtain ⟨_, firstPath, secondPath⟩ := equations.churchRosser conversion
  obtain ⟨_, _, _, firstShape, firstCarrier, firstLeft, firstRight⟩ :=
    equations.stepStar_identity firstPath
  obtain ⟨_, _, _, secondShape, secondCarrier, secondLeft, secondRight⟩ :=
    equations.stepStar_identity secondPath
  obtain ⟨rfl, rfl, rfl⟩ := Tm.id.inj (firstShape.symm.trans secondShape)
  exact ⟨.trans _ _ _ (stepStar_implies_conv firstCarrier)
      (.symm _ _ (stepStar_implies_conv secondCarrier)),
    .trans _ _ _ (stepStar_implies_conv firstLeft) (.symm _ _ (stepStar_implies_conv secondLeft)),
    .trans _ _ _ (stepStar_implies_conv firstRight)
      (.symm _ _ (stepStar_implies_conv secondRight))⟩

/-- No identity type converts to a universe head. -/
theorem identity_not_head {n : Nat} {carrier left right : Tm Head n} {head : Head}
    (conversion : Conv rules.headEq (.id carrier left right) (.head head) rules.computation) :
    False := by
  obtain ⟨_, firstPath, secondPath⟩ := equations.churchRosser conversion
  obtain ⟨_, _, _, firstShape, _⟩ := equations.stepStar_identity firstPath
  obtain ⟨_, secondShape⟩ := equations.stepStar_head secondPath
  rw [firstShape] at secondShape
  cases secondShape

end ConstructorPresentation

/-! ## Axiom audit -/

#print axioms instanceOf_of_leftSide
#print axioms ConstructorPresentation.piConversionBoundary
#print axioms ConstructorPresentation.sigmaConversionBoundary
#print axioms ConstructorPresentation.identity_components
#print axioms ConstructorPresentation.eq_of_normal
#print axioms pattern_par
#print axioms redex_par
#print axioms par_develop
#print axioms em_of_development
#print axioms par_diamond
#print axioms churchRosser
#print axioms determined_of_disjoint

end ConstructorSystem
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
