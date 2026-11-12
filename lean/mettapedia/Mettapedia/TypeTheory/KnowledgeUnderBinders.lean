import Mettapedia.TypeTheory.KnowledgeFramesCore
import Mettapedia.TypeTheory.BubbleTypingInside

/-!
# Knowledge under binders: the raw reading captures, the scoped reading does not

The bubbles of the comparison core rewrite at every position with binders as ordinary term
formers (the scope stated in `BubbleWeakness`). For a bubble whose rules are schemas, every
instance is a rule again and nothing goes wrong. An equation assumed at a frame is not a schema:
it speaks of particular variables of the frame. Under a binder those variables have other
indices, and the raw rewriting of `KnowledgeFramesCore.assumed` applies the unshifted equation
there, to whatever variable now carries the index.

* **The trap** (`Controls.raw_captures`): with the knowledge `n ≐ 0` for the one variable of the
  frame, raw rewriting converts `Π (m : nat). Vec m` with `Π (m : nat). Vec 0`. It has rewritten
  the bound variable.
* **Scoped rewriting** (`RewriteUnder`, `assumedAt`, `ConvertibleUnder`): the rules available at
  a position depend on the number of binders around it, and an assumed equation is read there
  shifted by that number. Entering a binder is a move to an extended frame, and the knowledge
  moves with it.
* **Bubbles are the case where depth does not matter** (`rewriteUnder_const_iff`): for rules that
  do not depend on the depth, scoped rewriting is the rewriting of `BubbleConversion`.
* **The scoped reading refuses the trap and keeps the intended use**
  (`Controls.scoped_refuses_capture`, `Controls.scoped_under_binder`): it does not convert
  `Π (m : nat). Vec m` with `Π (m : nat). Vec 0`, and it converts `Π (m : nat). Vec n` with
  `Π (m : nat). Vec 0`, where under the binder `n` has index one.

* **Typing at a frame with knowledge** (`TypedKnowing`): the frame is a context with a store; the
  conversion rule is available at every node; a rule that enters a binder judges its premise at
  the extended frame, with the store moved along (`shiftStore`). Every typing of the global
  judgment is a typing at every frame (`TypedKnowing.of_hasType`). Control: in the context
  `n : nat, v : Vec n` with `n ≐ 0` known, `λ (m : nat). v` is typed at `Π (m : nat). Vec 0`
  (`Controls.constant_function_at_zero`), and not in the global judgment
  (`Controls.constant_function_not_global`).

* **Knowledge the bubble proves adds no typing, at any depth** (`typedKnowing_iff_inside`): for a
  bubble whose rules are stable under shifting (`ShiftStable`), a frame whose equations the
  bubble converts types exactly what the bubble types with the conversion rule at every node.
  Controls: `n + 0 ≐ n` with the recursion equations (`Controls.redundant_knowledge`); `n ≐ 0`
  with no declared step adds a typing (`Controls.genuine_knowledge`).

So the statements of `KnowledgeFramesCore`, `BubbleTypingRuns` and `BubbleTypingInside` about
assumed equations are statements about the raw reading. They agree with the frame's knowledge at
positions outside binders, which is where their controls use it; under binders the scoped
reading of this module is the frame's knowledge.

Scope: the comparison core. The substitution property of `TypedKnowing`, with the store
instantiated along the substitution, is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeUnderBinders

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- One step of depth-indexed root rules: the rules available at a position depend on the number
of binders that enclose it. -/
inductive RewriteUnder (rules : Nat → Expr Base Const → Expr Base Const → Prop) :
    Nat → Expr Base Const → Expr Base Const → Prop where
  | root {depth : Nat} {left right : Expr Base Const} :
      rules depth left right → RewriteUnder rules depth left right
  | piDomain {depth : Nat} {A A' B : Expr Base Const} :
      RewriteUnder rules depth A A' → RewriteUnder rules depth (Expr.pi A B) (Expr.pi A' B)
  | piBody {depth : Nat} {A B B' : Expr Base Const} :
      RewriteUnder rules (depth + 1) B B' → RewriteUnder rules depth (Expr.pi A B) (Expr.pi A B')
  | lamDomain {depth : Nat} {A A' b : Expr Base Const} :
      RewriteUnder rules depth A A' → RewriteUnder rules depth (Expr.lam A b) (Expr.lam A' b)
  | lamBody {depth : Nat} {A b b' : Expr Base Const} :
      RewriteUnder rules (depth + 1) b b' → RewriteUnder rules depth (Expr.lam A b) (Expr.lam A b')
  | appFunction {depth : Nat} {f f' a : Expr Base Const} :
      RewriteUnder rules depth f f' → RewriteUnder rules depth (Expr.app f a) (Expr.app f' a)
  | appArgument {depth : Nat} {f a a' : Expr Base Const} :
      RewriteUnder rules depth a a' → RewriteUnder rules depth (Expr.app f a) (Expr.app f a')
  | andLeft {depth : Nat} {p p' q : Expr Base Const} :
      RewriteUnder rules depth p p' → RewriteUnder rules depth (Expr.and p q) (Expr.and p' q)
  | andRight {depth : Nat} {p q q' : Expr Base Const} :
      RewriteUnder rules depth q q' → RewriteUnder rules depth (Expr.and p q) (Expr.and p q')
  | orLeft {depth : Nat} {p p' q : Expr Base Const} :
      RewriteUnder rules depth p p' → RewriteUnder rules depth (Expr.or p q) (Expr.or p' q)
  | orRight {depth : Nat} {p q q' : Expr Base Const} :
      RewriteUnder rules depth q q' → RewriteUnder rules depth (Expr.or p q) (Expr.or p q')
  | impLeft {depth : Nat} {p p' q : Expr Base Const} :
      RewriteUnder rules depth p p' → RewriteUnder rules depth (Expr.imp p q) (Expr.imp p' q)
  | impRight {depth : Nat} {p q q' : Expr Base Const} :
      RewriteUnder rules depth q q' → RewriteUnder rules depth (Expr.imp p q) (Expr.imp p q')
  | notBody {depth : Nat} {p p' : Expr Base Const} :
      RewriteUnder rules depth p p' → RewriteUnder rules depth (Expr.not p) (Expr.not p')
  | eqLeft {depth : Nat} {a a' b : Expr Base Const} :
      RewriteUnder rules depth a a' → RewriteUnder rules depth (Expr.eq a b) (Expr.eq a' b)
  | eqRight {depth : Nat} {a b b' : Expr Base Const} :
      RewriteUnder rules depth b b' → RewriteUnder rules depth (Expr.eq a b) (Expr.eq a b')
  | allDomain {depth : Nat} {A A' b : Expr Base Const} :
      RewriteUnder rules depth A A' → RewriteUnder rules depth (Expr.all A b) (Expr.all A' b)
  | allBody {depth : Nat} {A b b' : Expr Base Const} :
      RewriteUnder rules (depth + 1) b b' → RewriteUnder rules depth (Expr.all A b) (Expr.all A b')
  | exDomain {depth : Nat} {A A' b : Expr Base Const} :
      RewriteUnder rules depth A A' → RewriteUnder rules depth (Expr.ex A b) (Expr.ex A' b)
  | exBody {depth : Nat} {A b b' : Expr Base Const} :
      RewriteUnder rules (depth + 1) b b' → RewriteUnder rules depth (Expr.ex A b) (Expr.ex A b')

/-- **Bubbles are the case where depth does not matter**: scoped rewriting by rules that ignore
the depth is rewriting. -/
theorem rewriteUnder_const_iff {rules : Expr Base Const → Expr Base Const → Prop} {depth : Nat}
    {e e' : Expr Base Const} :
    RewriteUnder (fun _ => rules) depth e e' ↔ Rewrite rules e e' := by
  constructor
  · intro step
    induction step with
    | root rule => exact .root rule
    | piDomain _ ih => exact .piDomain ih
    | piBody _ ih => exact .piBody ih
    | lamDomain _ ih => exact .lamDomain ih
    | lamBody _ ih => exact .lamBody ih
    | appFunction _ ih => exact .appFunction ih
    | appArgument _ ih => exact .appArgument ih
    | andLeft _ ih => exact .andLeft ih
    | andRight _ ih => exact .andRight ih
    | orLeft _ ih => exact .orLeft ih
    | orRight _ ih => exact .orRight ih
    | impLeft _ ih => exact .impLeft ih
    | impRight _ ih => exact .impRight ih
    | notBody _ ih => exact .notBody ih
    | eqLeft _ ih => exact .eqLeft ih
    | eqRight _ ih => exact .eqRight ih
    | allDomain _ ih => exact .allDomain ih
    | allBody _ ih => exact .allBody ih
    | exDomain _ ih => exact .exDomain ih
    | exBody _ ih => exact .exBody ih
  · intro step
    induction step generalizing depth with
    | root rule => exact .root rule
    | piDomain _ ih => exact .piDomain ih
    | piBody _ ih => exact .piBody ih
    | lamDomain _ ih => exact .lamDomain ih
    | lamBody _ ih => exact .lamBody ih
    | appFunction _ ih => exact .appFunction ih
    | appArgument _ ih => exact .appArgument ih
    | andLeft _ ih => exact .andLeft ih
    | andRight _ ih => exact .andRight ih
    | orLeft _ ih => exact .orLeft ih
    | orRight _ ih => exact .orRight ih
    | impLeft _ ih => exact .impLeft ih
    | impRight _ ih => exact .impRight ih
    | notBody _ ih => exact .notBody ih
    | eqLeft _ ih => exact .eqLeft ih
    | eqRight _ ih => exact .eqRight ih
    | allDomain _ ih => exact .allDomain ih
    | allBody _ ih => exact .allBody ih
    | exDomain _ ih => exact .exDomain ih
    | exBody _ ih => exact .exBody ih

/-- An assumed equation, read under `depth` binders: both sides shifted past them. -/
def assumedAt (store : EquationStore (Expr Base Const)) :
    Nat → Expr Base Const → Expr Base Const → Prop :=
  fun depth left right => ∃ e ∈ store, left = shiftN depth e.1 ∧ right = shiftN depth e.2

/-- **Conversion by the frame's knowledge, scoped**: the equivalence closure of rewriting by the
assumed equations, each read at the depth of the position where it is used. -/
abbrev ConvertibleUnder (store : EquationStore (Expr Base Const)) :=
  Relation.EqvGen (RewriteUnder (assumedAt store) 0)

/-! ## Typing at a frame with knowledge, with the knowledge moving under binders -/

/-- The frame's equations one binder further in. -/
def shiftStore (store : EquationStore (Expr Base Const)) : EquationStore (Expr Base Const) :=
  store.map fun e => (shiftAt 0 e.1, shiftAt 0 e.2)

/-- Conversion at a frame: by the bubble's rules at every depth, and by the frame's equations
read at the depth of the position. -/
abbrev ConvertibleKnowing (rules : Expr Base Const → Expr Base Const → Prop)
    (store : EquationStore (Expr Base Const)) :=
  Relation.EqvGen
    (RewriteUnder (fun depth left right => rules left right ∨ assumedAt store depth left right) 0)

/-- **Typing at a frame with knowledge.** The frame is a context with a store of equations. The
conversion rule is available at every node. A rule that enters a binder extends the context and
moves the store with it (`shiftStore`): the premise under the binder is judged at the extended
frame. -/
inductive TypedKnowing (rules : Expr Base Const → Expr Base Const → Prop) :
    EquationStore (Expr Base Const) → List (Expr Base Const) → Expr Base Const →
      Expr Base Const → Prop where
  | var {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} {i : Nat}
      {A : Expr Base Const} (lookup : Γ[i]? = some A) :
      TypedKnowing rules K Γ (bvar i) (shiftN (i + 1) A)
  | base {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} (b : Base) :
      TypedKnowing rules K Γ (Expr.base b) univ
  | prop {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} :
      TypedKnowing rules K Γ Expr.prop univ
  | pi {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} {A B : Expr Base Const} :
      TypedKnowing rules K Γ A univ → TypedKnowing rules (shiftStore K) (A :: Γ) B univ →
        TypedKnowing rules K Γ (Expr.pi A B) univ
  | lam {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {A b B : Expr Base Const} :
      TypedKnowing rules K Γ A univ → TypedKnowing rules (shiftStore K) (A :: Γ) b B →
        TypedKnowing rules K Γ (Expr.lam A b) (Expr.pi A B)
  | app {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {f a A B : Expr Base Const} :
      TypedKnowing rules K Γ f (Expr.pi A B) → TypedKnowing rules K Γ a A →
        TypedKnowing rules K Γ (Expr.app f a) (substAt 0 a B)
  | const {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} (τ : Ty Base)
      (c : Const τ) : TypedKnowing rules K Γ (Expr.const τ c) (tyToExpr τ)
  | tyFam {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} (b : Base) :
      TypedKnowing rules K Γ (Expr.tyFam b) (Expr.pi (Expr.base b) univ)
  | top {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} :
      TypedKnowing rules K Γ Expr.top Expr.prop
  | bot {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} :
      TypedKnowing rules K Γ Expr.bot Expr.prop
  | and {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {p q : Expr Base Const} :
      TypedKnowing rules K Γ p Expr.prop → TypedKnowing rules K Γ q Expr.prop →
        TypedKnowing rules K Γ (Expr.and p q) Expr.prop
  | or {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {p q : Expr Base Const} :
      TypedKnowing rules K Γ p Expr.prop → TypedKnowing rules K Γ q Expr.prop →
        TypedKnowing rules K Γ (Expr.or p q) Expr.prop
  | imp {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {p q : Expr Base Const} :
      TypedKnowing rules K Γ p Expr.prop → TypedKnowing rules K Γ q Expr.prop →
        TypedKnowing rules K Γ (Expr.imp p q) Expr.prop
  | not {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} {p : Expr Base Const} :
      TypedKnowing rules K Γ p Expr.prop → TypedKnowing rules K Γ (Expr.not p) Expr.prop
  | eq {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {a b A : Expr Base Const} :
      TypedKnowing rules K Γ a A → TypedKnowing rules K Γ b A →
        TypedKnowing rules K Γ (Expr.eq a b) Expr.prop
  | all {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {A b : Expr Base Const} :
      TypedKnowing rules K Γ A univ → TypedKnowing rules (shiftStore K) (A :: Γ) b Expr.prop →
        TypedKnowing rules K Γ (Expr.all A b) Expr.prop
  | ex {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {A b : Expr Base Const} :
      TypedKnowing rules K Γ A univ → TypedKnowing rules (shiftStore K) (A :: Γ) b Expr.prop →
        TypedKnowing rules K Γ (Expr.ex A b) Expr.prop
  | move {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
      {e A B : Expr Base Const} :
      TypedKnowing rules K Γ e A → ConvertibleKnowing rules K A B → TypedKnowing rules K Γ e B

/-- Every typing of the global judgment is a typing at every frame. -/
theorem TypedKnowing.of_hasType {rules : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (typing : HasType Γ e A) :
    ∀ K : EquationStore (Expr Base Const), TypedKnowing rules K Γ e A := by
  induction typing with
  | var lookup => exact fun _ => .var lookup
  | base b => exact fun _ => .base b
  | prop => exact fun _ => .prop
  | pi _ _ ihA ihB => exact fun K => .pi (ihA K) (ihB _)
  | lam _ _ ihA ihb => exact fun K => .lam (ihA K) (ihb _)
  | app _ _ ihf iha => exact fun K => .app (ihf K) (iha K)
  | const τ c => exact fun _ => .const τ c
  | tyFam b => exact fun _ => .tyFam b
  | top => exact fun _ => .top
  | bot => exact fun _ => .bot
  | and _ _ ihp ihq => exact fun K => .and (ihp K) (ihq K)
  | or _ _ ihp ihq => exact fun K => .or (ihp K) (ihq K)
  | imp _ _ ihp ihq => exact fun K => .imp (ihp K) (ihq K)
  | not _ ihp => exact fun K => .not (ihp K)
  | eq _ _ iha ihb => exact fun K => .eq (iha K) (ihb K)
  | all _ _ ihA ihb => exact fun K => .all (ihA K) (ihb _)
  | ex _ _ ihA ihb => exact fun K => .ex (ihA K) (ihb _)

/-! ## Knowledge that the bubble proves adds no typing, at any depth -/

/-- More rules at every depth, more scoped steps. -/
theorem RewriteUnder.mono {small large : Nat → Expr Base Const → Expr Base Const → Prop}
    (included : ∀ depth left right, small depth left right → large depth left right)
    {depth : Nat} {e e' : Expr Base Const} (step : RewriteUnder small depth e e') :
    RewriteUnder large depth e e' := by
  induction step with
  | root rule => exact .root (included _ _ _ rule)
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | impLeft _ ih => exact .impLeft ih
  | impRight _ ih => exact .impRight ih
  | notBody _ ih => exact .notBody ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | allDomain _ ih => exact .allDomain ih
  | allBody _ ih => exact .allBody ih
  | exDomain _ ih => exact .exDomain ih
  | exBody _ ih => exact .exBody ih

/-- A scoped step whose root instances are conversions of a bubble, at every depth, is a step of
the bubble's conversion taken as a rule. -/
theorem rewrite_of_rewriteUnder {rules : Expr Base Const → Expr Base Const → Prop}
    {available : Nat → Expr Base Const → Expr Base Const → Prop}
    (justified : ∀ depth left right, available depth left right → Convertible rules left right)
    {depth : Nat} {e e' : Expr Base Const} (step : RewriteUnder available depth e e') :
    Rewrite (Convertible rules) e e' := by
  induction step with
  | root rule => exact .root (justified _ _ _ rule)
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | impLeft _ ih => exact .impLeft ih
  | impRight _ ih => exact .impRight ih
  | notBody _ ih => exact .notBody ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | allDomain _ ih => exact .allDomain ih
  | allBody _ ih => exact .allBody ih
  | exDomain _ ih => exact .exDomain ih
  | exBody _ ih => exact .exBody ih

/-- A rule set is stable under shifting when every shifted instance of a rule is a rule. -/
def ShiftStable (rules : Expr Base Const → Expr Base Const → Prop) : Prop :=
  ∀ left right, rules left right → ∀ cutoff : Nat, rules (shiftAt cutoff left) (shiftAt cutoff right)

theorem rewrite_shiftAt {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {e e' : Expr Base Const} (step : Rewrite rules e e') :
    ∀ cutoff : Nat, Rewrite rules (shiftAt cutoff e) (shiftAt cutoff e') := by
  induction step with
  | root rule => exact fun cutoff => .root (stable _ _ rule cutoff)
  | piDomain _ ih => exact fun cutoff => .piDomain (ih cutoff)
  | piBody _ ih => exact fun cutoff => .piBody (ih (cutoff + 1))
  | lamDomain _ ih => exact fun cutoff => .lamDomain (ih cutoff)
  | lamBody _ ih => exact fun cutoff => .lamBody (ih (cutoff + 1))
  | appFunction _ ih => exact fun cutoff => .appFunction (ih cutoff)
  | appArgument _ ih => exact fun cutoff => .appArgument (ih cutoff)
  | andLeft _ ih => exact fun cutoff => .andLeft (ih cutoff)
  | andRight _ ih => exact fun cutoff => .andRight (ih cutoff)
  | orLeft _ ih => exact fun cutoff => .orLeft (ih cutoff)
  | orRight _ ih => exact fun cutoff => .orRight (ih cutoff)
  | impLeft _ ih => exact fun cutoff => .impLeft (ih cutoff)
  | impRight _ ih => exact fun cutoff => .impRight (ih cutoff)
  | notBody _ ih => exact fun cutoff => .notBody (ih cutoff)
  | eqLeft _ ih => exact fun cutoff => .eqLeft (ih cutoff)
  | eqRight _ ih => exact fun cutoff => .eqRight (ih cutoff)
  | allDomain _ ih => exact fun cutoff => .allDomain (ih cutoff)
  | allBody _ ih => exact fun cutoff => .allBody (ih (cutoff + 1))
  | exDomain _ ih => exact fun cutoff => .exDomain (ih cutoff)
  | exBody _ ih => exact fun cutoff => .exBody (ih (cutoff + 1))

theorem convertible_shiftAt {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {e e' : Expr Base Const} (converted : Convertible rules e e')
    (cutoff : Nat) : Convertible rules (shiftAt cutoff e) (shiftAt cutoff e') := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (rewrite_shiftAt stable step cutoff)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

theorem convertible_shiftN {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {e e' : Expr Base Const} (converted : Convertible rules e e') :
    ∀ count : Nat, Convertible rules (shiftN count e) (shiftN count e')
  | 0 => converted
  | count + 1 => convertible_shiftAt stable (convertible_shiftN stable converted count) 0

/-- Conversion at a frame whose equations the bubble converts is conversion of the bubble. -/
theorem convertible_of_knowing {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {store : EquationStore (Expr Base Const)}
    (sound : ∀ e ∈ store, Convertible rules e.1 e.2) {e e' : Expr Base Const}
    (converted : ConvertibleKnowing rules store e e') : Convertible rules e e' := by
  induction converted with
  | rel _ _ step =>
      refine BubbleWeakness.convertible_of_rewrite_convertible
        (rewrite_of_rewriteUnder (rules := rules) (fun depth left right rule => ?_) step)
      rcases rule with direct | ⟨equation, member, atLeft, atRight⟩
      · exact Relation.EqvGen.rel _ _ (Rewrite.root direct)
      · rw [atLeft, atRight]
        exact convertible_shiftN stable (sound equation member) depth
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

theorem sound_shiftStore {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {store : EquationStore (Expr Base Const)}
    (sound : ∀ e ∈ store, Convertible rules e.1 e.2) :
    ∀ e ∈ shiftStore store, Convertible rules e.1 e.2 := by
  intro e member
  obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp member
  exact convertible_shiftAt stable (sound original inStore) 0

/-- **Knowledge that the bubble proves is discharged, at every depth.** A typing at a frame whose
equations are conversions of a shift-stable bubble is a typing in the bubble. -/
theorem typedKnowing_discharge {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {store : EquationStore (Expr Base Const)}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : TypedKnowing rules store Γ e A) :
    (∀ equation ∈ store, Convertible rules equation.1 equation.2) →
      BubbleTypingInside.HasTypeInside rules Γ e A := by
  induction typed with
  | var lookup => exact fun _ => .var lookup
  | base b => exact fun _ => .base b
  | prop => exact fun _ => .prop
  | pi _ _ ihA ihB => exact fun sound => .pi (ihA sound) (ihB (sound_shiftStore stable sound))
  | lam _ _ ihA ihb => exact fun sound => .lam (ihA sound) (ihb (sound_shiftStore stable sound))
  | app _ _ ihf iha => exact fun sound => .app (ihf sound) (iha sound)
  | const τ c => exact fun _ => .const τ c
  | tyFam b => exact fun _ => .tyFam b
  | top => exact fun _ => .top
  | bot => exact fun _ => .bot
  | and _ _ ihp ihq => exact fun sound => .and (ihp sound) (ihq sound)
  | or _ _ ihp ihq => exact fun sound => .or (ihp sound) (ihq sound)
  | imp _ _ ihp ihq => exact fun sound => .imp (ihp sound) (ihq sound)
  | not _ ihp => exact fun sound => .not (ihp sound)
  | eq _ _ iha ihb => exact fun sound => .eq (iha sound) (ihb sound)
  | all _ _ ihA ihb => exact fun sound => .all (ihA sound) (ihb (sound_shiftStore stable sound))
  | ex _ _ ihA ihb => exact fun sound => .ex (ihA sound) (ihb (sound_shiftStore stable sound))
  | move _ converted ih =>
      exact fun sound => .move (ih sound) (convertible_of_knowing stable sound converted)

/-- A conversion of the bubble is a conversion at every frame of the bubble. -/
theorem convertibleKnowing_of_convertible {rules : Expr Base Const → Expr Base Const → Prop}
    (store : EquationStore (Expr Base Const)) {e e' : Expr Base Const}
    (converted : Convertible rules e e') : ConvertibleKnowing rules store e e' := by
  induction converted with
  | rel _ _ step =>
      exact Relation.EqvGen.rel _ _
        (RewriteUnder.mono (fun _ _ _ rule => Or.inl rule) (rewriteUnder_const_iff.mpr step))
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- What a bubble types is typed at every frame of the bubble. -/
theorem typedKnowing_of_inside {rules : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : BubbleTypingInside.HasTypeInside rules Γ e A) :
    ∀ store : EquationStore (Expr Base Const), TypedKnowing rules store Γ e A := by
  induction typed with
  | var lookup => exact fun _ => .var lookup
  | base b => exact fun _ => .base b
  | prop => exact fun _ => .prop
  | pi _ _ ihA ihB => exact fun store => .pi (ihA store) (ihB _)
  | lam _ _ ihA ihb => exact fun store => .lam (ihA store) (ihb _)
  | app _ _ ihf iha => exact fun store => .app (ihf store) (iha store)
  | const τ c => exact fun _ => .const τ c
  | tyFam b => exact fun _ => .tyFam b
  | top => exact fun _ => .top
  | bot => exact fun _ => .bot
  | and _ _ ihp ihq => exact fun store => .and (ihp store) (ihq store)
  | or _ _ ihp ihq => exact fun store => .or (ihp store) (ihq store)
  | imp _ _ ihp ihq => exact fun store => .imp (ihp store) (ihq store)
  | not _ ihp => exact fun store => .not (ihp store)
  | eq _ _ iha ihb => exact fun store => .eq (iha store) (ihb store)
  | all _ _ ihA ihb => exact fun store => .all (ihA store) (ihb _)
  | ex _ _ ihA ihb => exact fun store => .ex (ihA store) (ihb _)
  | move _ converted ih =>
      exact fun store => .move (ih store) (convertibleKnowing_of_convertible store converted)

/-- **For a shift-stable bubble, a frame whose equations the bubble converts types exactly what
the bubble types.** -/
theorem typedKnowing_iff_inside {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {store : EquationStore (Expr Base Const)}
    (sound : ∀ equation ∈ store, Convertible rules equation.1 equation.2)
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} :
    TypedKnowing rules store Γ e A ↔ BubbleTypingInside.HasTypeInside rules Γ e A :=
  ⟨fun typed => typedKnowing_discharge stable typed sound,
    fun typed => typedKnowing_of_inside typed store⟩

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- The knowledge `n ≐ 0` at the frame with the one variable `n`. -/
def knowsZero : EquationStore AExpr := [(bvar 0, zeroE)]

/-- **The trap in the raw reading**: with `n ≐ 0` known, raw rewriting converts
`Π (m : nat). Vec m` with `Π (m : nat). Vec 0`. Under the binder the index `0` is `m`. -/
theorem raw_captures :
    Convertible (assumed knowsZero) (Expr.pi natType (vec (bvar 0))) (Expr.pi natType (vec zeroE)) :=
  Relation.EqvGen.rel _ _
    (Rewrite.piBody (Rewrite.appArgument
      (Rewrite.root (show assumed knowsZero (bvar 0) zeroE from List.mem_singleton_self _))))

theorem shiftN_bvar_zero : ∀ depth : Nat, shiftN depth (bvar 0 : AExpr) = bvar depth
  | 0 => rfl
  | depth + 1 => by
      show shiftAt 0 (shiftN depth (bvar 0 : AExpr)) = bvar (depth + 1)
      rw [shiftN_bvar_zero depth]
      simp [shiftAt]

theorem shiftN_zeroE : ∀ depth : Nat, shiftN depth zeroE = zeroE
  | 0 => rfl
  | depth + 1 => by
      show shiftAt 0 (shiftN depth zeroE) = zeroE
      rw [shiftN_zeroE depth]
      rfl

/-- **The scoped reading keeps the intended use**: under one binder `n` has index one, and
`Π (m : nat). Vec n` converts with `Π (m : nat). Vec 0`. -/
theorem scoped_under_binder :
    ConvertibleUnder knowsZero (Expr.pi natType (vec (bvar 1))) (Expr.pi natType (vec zeroE)) :=
  Relation.EqvGen.rel _ _
    (RewriteUnder.piBody (RewriteUnder.appArgument
      (RewriteUnder.root ⟨(bvar 0, zeroE), List.mem_singleton_self _,
        (shiftN_bvar_zero 1).symm, (shiftN_zeroE 1).symm⟩)))

/-- Replace the frame's variable by zero: under `depth` binders it has index `depth`. -/
def collapseAt : Nat → AExpr → AExpr
  | depth, .bvar i => if i = depth then zeroE else .bvar i
  | _, .univ => .univ
  | _, .prop => .prop
  | _, .base b => .base b
  | depth, .pi A B => .pi (collapseAt depth A) (collapseAt (depth + 1) B)
  | depth, .lam A b => .lam (collapseAt depth A) (collapseAt (depth + 1) b)
  | depth, .app f a => .app (collapseAt depth f) (collapseAt depth a)
  | _, .const τ c => .const τ c
  | _, .tyFam b => .tyFam b
  | _, .top => .top
  | _, .bot => .bot
  | depth, .and p q => .and (collapseAt depth p) (collapseAt depth q)
  | depth, .or p q => .or (collapseAt depth p) (collapseAt depth q)
  | depth, .imp p q => .imp (collapseAt depth p) (collapseAt depth q)
  | depth, .not p => .not (collapseAt depth p)
  | depth, .eq a b => .eq (collapseAt depth a) (collapseAt depth b)
  | depth, .all A b => .all (collapseAt depth A) (collapseAt (depth + 1) b)
  | depth, .ex A b => .ex (collapseAt depth A) (collapseAt (depth + 1) b)

/-- Scoped rewriting by `n ≐ 0` keeps the reading with `n` replaced by zero. -/
theorem collapseAt_step {depth : Nat} {e e' : AExpr}
    (step : RewriteUnder (assumedAt knowsZero) depth e e') :
    collapseAt depth e = collapseAt depth e' := by
  induction step with
  | @root depth left right rule =>
      obtain ⟨equation, member, atLeft, atRight⟩ := rule
      obtain rfl := List.mem_singleton.mp member
      rw [atLeft, atRight, shiftN_bvar_zero, shiftN_zeroE]
      simp [collapseAt, zeroE]
  | piDomain _ ih => simp only [collapseAt, ih]
  | piBody _ ih => simp only [collapseAt, ih]
  | lamDomain _ ih => simp only [collapseAt, ih]
  | lamBody _ ih => simp only [collapseAt, ih]
  | appFunction _ ih => simp only [collapseAt, ih]
  | appArgument _ ih => simp only [collapseAt, ih]
  | andLeft _ ih => simp only [collapseAt, ih]
  | andRight _ ih => simp only [collapseAt, ih]
  | orLeft _ ih => simp only [collapseAt, ih]
  | orRight _ ih => simp only [collapseAt, ih]
  | impLeft _ ih => simp only [collapseAt, ih]
  | impRight _ ih => simp only [collapseAt, ih]
  | notBody _ ih => simp only [collapseAt, ih]
  | eqLeft _ ih => simp only [collapseAt, ih]
  | eqRight _ ih => simp only [collapseAt, ih]
  | allDomain _ ih => simp only [collapseAt, ih]
  | allBody _ ih => simp only [collapseAt, ih]
  | exDomain _ ih => simp only [collapseAt, ih]
  | exBody _ ih => simp only [collapseAt, ih]

theorem collapseAt_conv {e e' : AExpr} (converted : ConvertibleUnder knowsZero e e') :
    collapseAt 0 e = collapseAt 0 e' := by
  induction converted with
  | rel _ _ step => exact collapseAt_step step
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **The scoped reading refuses the trap**: it does not convert `Π (m : nat). Vec m` with
`Π (m : nat). Vec 0`. -/
theorem scoped_refuses_capture :
    ¬ ConvertibleUnder knowsZero (Expr.pi natType (vec (bvar 0)))
      (Expr.pi natType (vec zeroE)) := by
  intro converted
  have same := collapseAt_conv converted
  simp [collapseAt, vec, natType, zeroE] at same

/-- The context `n : nat, v : Vec n`, with the knowledge `n ≐ 0` (at the top, `n` has index
one). -/
def vectorKnowledge : EquationStore AExpr := [(bvar 1, zeroE)]

/-- One binder further in, the knowledge is about index two. -/
theorem shiftStore_vectorKnowledge : shiftStore vectorKnowledge = [(bvar 2, zeroE)] := rfl

/-- **The knowledge is used under a binder, at the right variable.** In the context
`n : nat, v : Vec n` with `n ≐ 0` known, the function `λ (m : nat). v` is typed at
`Π (m : nat). Vec 0`: under the binder `v` has type `Vec n` with `n` at index two, and the store
that moved with the frame converts it. -/
theorem constant_function_at_zero :
    TypedKnowing (fun _ _ => False) vectorKnowledge vecContext
      (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) :=
  TypedKnowing.lam (TypedKnowing.base ())
    (TypedKnowing.move
      (show TypedKnowing (fun _ _ => False) (shiftStore vectorKnowledge) (natType :: vecContext)
          (bvar 1) (vec (bvar 2)) from
        TypedKnowing.var (Γ := natType :: vecContext) (i := 1) rfl)
      (Relation.EqvGen.rel _ _
        (RewriteUnder.appArgument
          (RewriteUnder.root (Or.inr ⟨(bvar 2, zeroE), List.mem_singleton_self _, rfl, rfl⟩)))))

/-- In the global judgment the function has the type `Π (m : nat). Vec n` and no other. -/
theorem constant_function_not_global :
    ¬ HasType vecContext (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) := by
  intro typed
  have typing : HasType vecContext (Expr.lam natType (bvar 1)) (Expr.pi natType (vec (bvar 2))) :=
    HasType.lam (HasType.base ()) (HasType.var (Γ := natType :: vecContext) (i := 1) rfl)
  have same := typing.unique typed
  simp [vec, zeroE] at same

/-- The recursion equations of addition are stable under shifting. -/
theorem rule_shiftStable : ShiftStable Rule := by
  intro left right rule cutoff
  cases rule with
  | addZero => exact Rule.addZero _
  | addSucc => exact Rule.addSucc _ _

/-- The knowledge `n + 0 ≐ n`, which the recursion equations convert. -/
def redundantKnowledge : EquationStore AExpr := [(addE (bvar 1) zeroE, bvar 1)]

/-- **Knowledge the bubble proves adds nothing**: at the frame that knows `n + 0 ≐ n`, the
recursion equations type exactly what they type with no knowledge. -/
theorem redundant_knowledge {Γ : List AExpr} {e A : AExpr} :
    TypedKnowing Rule redundantKnowledge Γ e A ↔ BubbleTypingInside.HasTypeInside Rule Γ e A :=
  typedKnowing_iff_inside rule_shiftStable (by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact Relation.EqvGen.rel _ _ (Rewrite.root (Rule.addZero (bvar 1))))

/-- **Knowledge the bubble does not prove adds typings**: with no declared step, the function
`λ (m : nat). v` is typed at `Π (m : nat). Vec 0` at the frame that knows `n ≐ 0`
(`constant_function_at_zero`) and not without the knowledge. -/
theorem genuine_knowledge :
    TypedKnowing (fun _ _ => False) vectorKnowledge vecContext
        (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) ∧
      ¬ BubbleTypingInside.HasTypeInside (fun _ _ => False) vecContext
        (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) :=
  ⟨constant_function_at_zero,
    fun typed => constant_function_not_global (BubbleTypingInside.hasTypeInside_none_iff.mp typed)⟩

end Controls

/-! ## Axiom audit -/

#print axioms typedKnowing_discharge
#print axioms typedKnowing_iff_inside
#print axioms Controls.redundant_knowledge
#print axioms Controls.genuine_knowledge
#print axioms TypedKnowing.of_hasType
#print axioms Controls.constant_function_at_zero
#print axioms Controls.constant_function_not_global
#print axioms rewriteUnder_const_iff
#print axioms Controls.raw_captures
#print axioms Controls.scoped_under_binder
#print axioms Controls.scoped_refuses_capture

end Mettapedia.TypeTheory.KnowledgeUnderBinders
