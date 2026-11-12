import Mettapedia.TypeTheory.KnowledgeFrames
import Mettapedia.TypeTheory.BubbleWeakness

/-!
# Assumed equations on the dependent comparison core

`BubbleWeakness` reads a bubble's typing in its strict models: global typing followed by one
equation that every strict model validates (`hasTypeIn_iff_models`). This module states the same
fact in the vocabulary of the step interface, for a finite store of assumed equations, and adds
the local rule and its bounds.

* **Frames** (`congruenceFrames`): the strict models of the core (`BubbleWeakness.Congruence`),
  with coarsenings as morphisms. The knowledge of a frame is a store of equations between
  expressions; a solution is a strict model that validates them (`models_iff`).
* **An ask is a conversion** (`entails_iff_convertible`): an equation holds at every solution of a
  store exactly when the bubble whose steps are the store's equations (`assumed`) converts it.
* **Typing under knowledge is global typing and one ask** (`hasTypeIn_assumed_iff`). With no
  knowledge it is the global judgment (`hasTypeIn_assumed_nil`).
* **No transport term** (`typed_along`): if the knowledge entails `a ≐ b`, a term typed at
  `family a` is typed at `family b`, for every one-hole context of the core.
* **Typings accumulate** (`typed_of_more_knowledge`).

## Controls (`Controls`)

In the context `n : nat, v : Vec n`, with the knowledge `n ≐ 0`:
* `v` is typed at `Vec 0`, the same term (`vec_at_zero`);
* it is not so typed in the global judgment (`vec_at_zero_not_global`);
* the knowledge does not give `v : Vec 1`: a strict model validates the knowledge and keeps the
  two types apart (`vec_one_not_at_zero`);
* in the other direction, as in a branch of a match that told `n ≐ 0`, a vector of length zero is
  typed at `Vec n` (`emptyVector_at_n`), and not in the global judgment
  (`emptyVector_at_n_not_global`).

In the context `n m : nat, v : Vec n`, with the knowledge `n ≐ m`, `v` is typed at `Vec m`
(`vec_at_m`), and not without the knowledge (`vec_at_m_not_global`).

Read at the instance `n := 1`, the same equation is `1 ≐ 0` (`instance_at_one`). As knowledge it
identifies every numeral with zero (`numeral_collapses`), so a vector of length zero is typed at
every length (`every_length`). An equation assumed in one frame is knowledge of that frame; held
at every instance it identifies every length.

Scope: the comparison core of `SimpleSliceOfDependent`, whose bubble typing applies conversion
once, after syntax-directed typing; the morphisms of `congruenceFrames` are coarsenings and do not
instantiate variables. Assumed equations are applied as raw rewrite rules, with binders as
ordinary term formers: an equation that mentions a variable of the context is that frame's
knowledge at positions outside binders, where the controls use it. Under a binder the raw
equation speaks of another variable; `KnowledgeUnderBinders` gives the trap and the scoped
reading.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeFramesCore

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.Logic.TheoryModel
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleWeakness
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The root rules of a store of assumed equations. -/
def assumed (store : EquationStore (Expr Base Const)) :
    Expr Base Const → Expr Base Const → Prop :=
  fun left right => (left, right) ∈ store

variable (Base Const) in
/-- The frames of the comparison core: its strict models, with coarsenings as morphisms. -/
def congruenceFrames :
    Frames (fun _ : Congruence Base Const => Expr Base Const)
      (fun fine coarse : Congruence Base Const =>
        PLift (∀ e e' : Expr Base Const, fine.rel e e' → coarse.rel e e')) where
  E := fun {θ} e e' => θ.rel e e'
  equivalence := fun θ => θ.equivalence
  act := fun _ e => e
  id := fun _ => ⟨fun _ _ related => related⟩
  comp := fun later earlier => ⟨fun e e' related => later.down e e' (earlier.down e e' related)⟩
  act_id := fun _ => rfl
  act_comp := fun _ _ _ => rfl
  preserves := fun {_ _} coarsening {_ _} related => coarsening.down _ _ related

/-- Every strict model coarsens the syntactic one. -/
def fromSyntactic (θ : Congruence Base Const) :
    PLift (∀ e e' : Expr Base Const,
      (syntactic : Congruence Base Const).rel e e' → θ.rel e e') :=
  ⟨fun e e' same => by
    cases (show e = e' from same)
    exact θ.equivalence.refl e⟩

/-- A coarsening solves a store exactly when its target validates the store's equations. -/
theorem models_iff {fine coarse : Congruence Base Const}
    (coarsening : PLift (∀ e e' : Expr Base Const, fine.rel e e' → coarse.rel e e'))
    (store : EquationStore (Expr Base Const)) :
    (congruenceFrames Base Const).Models coarsening store ↔ ∀ e ∈ store, coarse.rel e.1 e.2 :=
  Iff.rfl

/-- The strict models of the bubble of assumed equations are the strict models that validate
the store. -/
theorem mem_models_assumed {store : EquationStore (Expr Base Const)} {θ : Congruence Base Const} :
    θ ∈ models strictSat (equations (assumed store)) ↔ ∀ e ∈ store, θ.rel e.1 e.2 := by
  constructor
  · intro model e member
    exact model (show e ∈ equations (assumed store) from member)
  · intro validates φ member
    exact validates φ member

/-- **An ask of the knowledge is a conversion of the bubble of assumed equations.** -/
theorem entails_iff_convertible (store : EquationStore (Expr Base Const))
    (e e' : Expr Base Const) :
    (congruenceFrames Base Const).Entails (a := syntactic) store (fun θ _ => θ.rel e e') ↔
      Convertible (assumed store) e e' := by
  constructor
  · intro entailed
    exact entailed (conversionModel (assumed store)) (fromSyntactic _)
      (fun _ member => Relation.EqvGen.rel _ _ (Rewrite.root member))
  · intro converted θ _ solved
    exact rel_of_convertible (mem_models_assumed.mpr solved) converted

/-- **Typing under assumed equations is global typing followed by one ask of the knowledge.** -/
theorem hasTypeIn_assumed_iff {store : EquationStore (Expr Base Const)}
    {Γ : List (Expr Base Const)} {e B : Expr Base Const} :
    HasTypeIn (assumed store) Γ e B ↔
      ∃ A, HasType Γ e A ∧
        (congruenceFrames Base Const).Entails (a := syntactic) store (fun θ _ => θ.rel A B) := by
  rw [hasTypeIn_iff]
  constructor
  · rintro ⟨A, typing, converted⟩
    exact ⟨A, typing, (entails_iff_convertible store A B).mpr converted⟩
  · rintro ⟨A, typing, entailed⟩
    exact ⟨A, typing, (entails_iff_convertible store A B).mp entailed⟩

/-- With nothing assumed, typing under knowledge is the global judgment. -/
theorem hasTypeIn_assumed_nil {Γ : List (Expr Base Const)} {e A : Expr Base Const} :
    HasTypeIn (assumed ([] : EquationStore (Expr Base Const))) Γ e A ↔ HasType Γ e A := by
  constructor
  · intro typed
    exact hasTypeIn_none_iff.mp
      (hasTypeIn_mono (fun _ _ member => absurd member List.not_mem_nil) typed)
  · exact fun typing => .of typing

/-- **No transport term.** If the knowledge entails `a ≐ b`, a term typed at `family a` is typed
at `family b`: the same term, for every one-hole context that rewrite steps cross. -/
theorem typed_along {store : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
    {e a b : Expr Base Const} (family : Expr Base Const → Expr Base Const)
    (crosses : ∀ {x x' : Expr Base Const},
      Rewrite (assumed store) x x' → Rewrite (assumed store) (family x) (family x'))
    (typed : HasTypeIn (assumed store) Γ e (family a))
    (known : (congruenceFrames Base Const).Entails (a := syntactic) store
      (fun θ _ => θ.rel a b)) :
    HasTypeIn (assumed store) Γ e (family b) :=
  .conv typed (convertible_context family crosses ((entails_iff_convertible store a b).mp known))

/-- **Typings accumulate**: what is typed under a store is typed under every larger store. -/
theorem typed_of_more_knowledge {small large : EquationStore (Expr Base Const)}
    (included : ∀ e ∈ small, e ∈ large) {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : HasTypeIn (assumed small) Γ e A) : HasTypeIn (assumed large) Γ e A :=
  hasTypeIn_mono (fun _ _ member => included _ member) typed

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- The knowledge `n ≐ 0`, for the variable `n` of the vector context. -/
def knowsZero : EquationStore AExpr := [(bvar 1, zeroE)]

theorem knowsZero_entails :
    (congruenceFrames Unit ArithConst).Entails (a := syntactic) knowsZero
      (fun θ _ => θ.rel (bvar 1) zeroE) :=
  (entails_iff_convertible knowsZero (bvar 1) zeroE).mpr
    (Relation.EqvGen.rel _ _
      (Rewrite.root (show assumed knowsZero (bvar 1) zeroE from List.mem_singleton_self _)))

/-- **In the frame that knows `n ≐ 0`, `v : Vec n` is typed at `Vec 0`**, the same term. -/
theorem vec_at_zero : HasTypeIn (assumed knowsZero) vecContext (bvar 0) (vec zeroE) :=
  typed_along (fun x => vec x) (fun step => Rewrite.appArgument step) (.of vecVariable_typed)
    knowsZero_entails

/-- **In the global judgment it is not.** -/
theorem vec_at_zero_not_global : ¬ HasType vecContext (bvar 0) (vec zeroE) := by
  intro typed
  have equal := vecVariable_type_unique typed
  simp [vec, zeroE] at equal

/-- Replace the variable `n` by zero, at every position. -/
def collapse : AExpr → AExpr
  | .bvar i => if i = 1 then zeroE else .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (collapse A) (collapse B)
  | .lam A b => .lam (collapse A) (collapse b)
  | .app f a => .app (collapse f) (collapse a)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (collapse p) (collapse q)
  | .or p q => .or (collapse p) (collapse q)
  | .imp p q => .imp (collapse p) (collapse q)
  | .not p => .not (collapse p)
  | .eq a b => .eq (collapse a) (collapse b)
  | .all A b => .all (collapse A) (collapse b)
  | .ex A b => .ex (collapse A) (collapse b)

/-- The strict model that reads every expression with `n` replaced by zero. -/
def collapseModel : Congruence Unit ArithConst where
  rel := fun e e' => collapse e = collapse e'
  equivalence := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  compatible := by
    intro e e' step
    induction step with
    | root same => exact same
    | piDomain _ ih => simp only [collapse, ih]
    | piBody _ ih => simp only [collapse, ih]
    | lamDomain _ ih => simp only [collapse, ih]
    | lamBody _ ih => simp only [collapse, ih]
    | appFunction _ ih => simp only [collapse, ih]
    | appArgument _ ih => simp only [collapse, ih]
    | andLeft _ ih => simp only [collapse, ih]
    | andRight _ ih => simp only [collapse, ih]
    | orLeft _ ih => simp only [collapse, ih]
    | orRight _ ih => simp only [collapse, ih]
    | impLeft _ ih => simp only [collapse, ih]
    | impRight _ ih => simp only [collapse, ih]
    | notBody _ ih => simp only [collapse, ih]
    | eqLeft _ ih => simp only [collapse, ih]
    | eqRight _ ih => simp only [collapse, ih]
    | allDomain _ ih => simp only [collapse, ih]
    | allBody _ ih => simp only [collapse, ih]
    | exDomain _ ih => simp only [collapse, ih]
    | exBody _ ih => simp only [collapse, ih]

theorem collapseModel_validates : ∀ e ∈ knowsZero, collapseModel.rel e.1 e.2 := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- **The knowledge `n ≐ 0` does not type `v` at `Vec 1`.** -/
theorem vec_one_not_at_zero :
    ¬ HasTypeIn (assumed knowsZero) vecContext (bvar 0) (vec (succE zeroE)) := by
  intro typed
  obtain ⟨A, typing, known⟩ := hasTypeIn_assumed_iff.mp typed
  rw [vecVariable_type_unique typing] at known
  have same : collapse (vec (bvar 1)) = collapse (vec (succE zeroE)) :=
    known collapseModel (fromSyntactic _) collapseModel_validates
  simp [collapse, vec, succE, zeroE] at same

/-- The context `n : nat, v : Vec n, w : Vec 0`, newest first: a branch in which a vector of
length zero is at hand. -/
def branchContext : List AExpr := [vec zeroE, vec (bvar 0), natType]

theorem emptyVector_typed : HasType branchContext (bvar 0) (vec zeroE) :=
  HasType.var (Γ := branchContext) (i := 0) rfl

/-- The knowledge `n ≐ 0` in the branch context, where `n` is the third variable. -/
def branchKnowsZero : EquationStore AExpr := [(bvar 2, zeroE)]

/-- **The other direction, as in a branch of a match.** Where the frame knows `n ≐ 0`, the vector
of length zero is typed at `Vec n`: the same term, with no motive and no transport. -/
theorem emptyVector_at_n :
    HasTypeIn (assumed branchKnowsZero) branchContext (bvar 0) (vec (bvar 2)) :=
  typed_along (fun x => vec x) (fun step => Rewrite.appArgument step) (.of emptyVector_typed)
    ((entails_iff_convertible branchKnowsZero zeroE (bvar 2)).mpr
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        (Rewrite.root (show assumed branchKnowsZero (bvar 2) zeroE from
          List.mem_singleton_self _)))))

/-- In the global judgment it is not. -/
theorem emptyVector_at_n_not_global : ¬ HasType branchContext (bvar 0) (vec (bvar 2)) := by
  intro typed
  have equal := emptyVector_typed.unique typed
  simp [vec, zeroE] at equal

/-- The context `n : nat, m : nat, v : Vec n`, newest first. -/
def transportContext : List AExpr := [vec (bvar 1), natType, natType]

theorem transported_typed : HasType transportContext (bvar 0) (vec (bvar 2)) :=
  HasType.var (Γ := transportContext) (i := 0) rfl

/-- The knowledge `n ≐ m` in that context. -/
def knowsSame : EquationStore AExpr := [(bvar 2, bvar 1)]

/-- **The transport example.** With `n ≐ m` known, `v : Vec n` is typed at `Vec m`: the term is
`v` itself, where an identity proof would ask for a transport of `v` along it. -/
theorem vec_at_m : HasTypeIn (assumed knowsSame) transportContext (bvar 0) (vec (bvar 1)) :=
  typed_along (fun x => vec x) (fun step => Rewrite.appArgument step) (.of transported_typed)
    ((entails_iff_convertible knowsSame (bvar 2) (bvar 1)).mpr
      (Relation.EqvGen.rel _ _
        (Rewrite.root (show assumed knowsSame (bvar 2) (bvar 1) from List.mem_singleton_self _))))

/-- Without the knowledge it is not. -/
theorem vec_at_m_not_global : ¬ HasType transportContext (bvar 0) (vec (bvar 1)) := by
  intro typed
  have equal := transported_typed.unique typed
  simp [vec] at equal

/-- The equation `n ≐ 0`, read at the instance `n := 1`. -/
theorem instance_at_one :
    (substAt 1 (succE zeroE) (bvar 1), substAt 1 (succE zeroE) zeroE) =
      ((succE zeroE, zeroE) : AExpr × AExpr) := rfl

/-- The knowledge `1 ≐ 0`. -/
def knowsOneZero : EquationStore AExpr := [(succE zeroE, zeroE)]

/-- The numerals. -/
def numeral : Nat → AExpr
  | 0 => zeroE
  | k + 1 => succE (numeral k)

/-- **Under `1 ≐ 0` every numeral converts to zero.** -/
theorem numeral_collapses (k : Nat) : Convertible (assumed knowsOneZero) (numeral k) zeroE := by
  induction k with
  | zero => exact Relation.EqvGen.refl _
  | succ k ih =>
      exact Relation.EqvGen.trans _ _ _
        (convertible_context (fun x => succE x) (fun step => Rewrite.appArgument step) ih)
        (Relation.EqvGen.rel _ _ (Rewrite.root
          (show assumed knowsOneZero (succE zeroE) zeroE from List.mem_singleton_self _)))

/-- **Held at the instance `n := 1`, the equation types a vector of length zero at every
length.** -/
theorem every_length (k : Nat) :
    HasTypeIn (assumed knowsOneZero) [vec zeroE] (bvar 0) (vec (numeral k)) :=
  .conv (.of ArithControl.zeroVec_typed)
    (convertible_context (fun x => vec x) (fun step => Rewrite.appArgument step)
      (Relation.EqvGen.symm _ _ (numeral_collapses k)))

/-- Without the equation, the vector of length zero is not typed at length one. -/
theorem zero_not_one_global : ¬ HasType [vec zeroE] (bvar 0) (vec (numeral 1)) := by
  intro typed
  have equal := ArithControl.zeroVec_typed.unique typed
  simp [vec, zeroE, numeral, succE] at equal

end Controls

/-! ## Axiom audit -/

#print axioms entails_iff_convertible
#print axioms hasTypeIn_assumed_iff
#print axioms hasTypeIn_assumed_nil
#print axioms typed_along
#print axioms typed_of_more_knowledge
#print axioms Controls.vec_at_zero
#print axioms Controls.vec_at_zero_not_global
#print axioms Controls.vec_one_not_at_zero
#print axioms Controls.emptyVector_at_n
#print axioms Controls.emptyVector_at_n_not_global
#print axioms Controls.vec_at_m
#print axioms Controls.vec_at_m_not_global
#print axioms Controls.instance_at_one
#print axioms Controls.numeral_collapses
#print axioms Controls.every_length
#print axioms Controls.zero_not_one_global

end Mettapedia.TypeTheory.KnowledgeFramesCore
