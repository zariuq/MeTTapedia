import Mettapedia.TypeTheory.KnowledgeSubstitution
import Mettapedia.TypeTheory.BubbleTypingAlgorithmic

/-!
# Knowledge in solved form: a definition is an instantiation that has not been carried out

A frame's knowledge is in solved form for a variable when it is one equation `x ≐ u` whose right
side lives below `x` in the context. This module proves that such a frame and the frame
instantiated at `x := u` have the same conversion.

* `converts_with_instance`: at a frame that knows `x ≐ u`, every term converts with its instance
  at `x := u`, at every depth. The frame's knowledge replaces each occurrence of the variable.
* `solved_conversion_iff`: two terms convert at the frame exactly when their instances convert in
  the bubble. Conversion at such a frame is as decidable as the bubble's conversion.
* `typedKnowing_unique_solved`: at such a frame, the types of a term convert at the frame, as
  soon as the bubble's conversion is coherent.

This is the case that unification of an index with a term produces. It separates it from knowledge
that is not a definition: an equation between two closed terms is not the instantiation of any
variable (`Controls.closed_knowledge_is_not_an_instantiation`), and an equation between two
products gives one term two types that the frame does not convert
(`BubbleTypingAlgorithmic.Controls.product_knowledge_two_types`).

## Controls

* `Controls.vector_frame_conversion`: at the frame `n : nat, v : Vec n` that knows `n ≐ 0`, two
  terms convert exactly when their instances at `n := 0` are identical.
* `Controls.vec_n_converts`, `Controls.vec_one_does_not_convert`: `Vec n` converts with `Vec 0`
  there, and `Vec 1` does not.
* `Controls.constant_function_types_convert`: the two types of `λ (m : nat). v` at that frame,
  `Π (m : nat). Vec 0` and `Π (m : nat). Vec n`, convert at the frame.
* `Controls.arith_solved_conversion_iff`, `Controls.arith_unique_solved`,
  `Controls.vec_succ_n_converts`: over the arithmetic bubbles, conversion at the frame of a
  definition is decided by the normal forms of the instances, types are unique up to it, and the
  knowledge works together with the declared steps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeSolvedForm

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

theorem shiftN_bvar (k : Nat) : ∀ depth : Nat, shiftN depth (bvar k : Expr Base Const) = bvar (k + depth)
  | 0 => rfl
  | depth + 1 => by
      have step : shiftAt 0 (bvar (k + depth) : Expr Base Const) = bvar (k + depth + 1) :=
        shiftAt_bvar_ge (Nat.not_lt_zero _)
      show shiftAt 0 (shiftN depth (bvar k : Expr Base Const)) = bvar (k + (depth + 1))
      rw [shiftN_bvar k depth]
      exact step

theorem shiftN_shiftN (t : Expr Base Const) (height : Nat) :
    ∀ depth : Nat, shiftN depth (shiftN height t) = shiftN (height + depth) t
  | 0 => rfl
  | depth + 1 => by
      show shiftAt 0 (shiftN depth (shiftN height t)) = shiftAt 0 (shiftN (height + depth) t)
      rw [shiftN_shiftN t height depth]

/-! ## Scoped conversion is a congruence -/

theorem under_congr {R : Nat → Expr Base Const → Expr Base Const → Prop} {inner outer : Nat}
    (wrap : Expr Base Const → Expr Base Const)
    (lift : ∀ x y, RewriteUnder R inner x y → RewriteUnder R outer (wrap x) (wrap y))
    {x y : Expr Base Const} (converted : Relation.EqvGen (RewriteUnder R inner) x y) :
    Relation.EqvGen (RewriteUnder R outer) (wrap x) (wrap y) := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (lift _ _ step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

theorem under_congr₂ {R : Nat → Expr Base Const → Expr Base Const → Prop}
    {left right outer : Nat} (former : Expr Base Const → Expr Base Const → Expr Base Const)
    (liftLeft : ∀ x x' y, RewriteUnder R left x x' → RewriteUnder R outer (former x y) (former x' y))
    (liftRight : ∀ x y y',
      RewriteUnder R right y y' → RewriteUnder R outer (former x y) (former x y'))
    {x x' y y' : Expr Base Const} (first : Relation.EqvGen (RewriteUnder R left) x x')
    (second : Relation.EqvGen (RewriteUnder R right) y y') :
    Relation.EqvGen (RewriteUnder R outer) (former x y) (former x' y') :=
  Relation.EqvGen.trans _ _ _
    (under_congr (fun z => former z y) (fun _ _ step => liftLeft _ _ _ step) first)
    (under_congr (fun z => former x' z) (fun _ _ step => liftRight _ _ _ step) second)

/-! ## A definition replaces the variable everywhere -/

/-- **At a frame that knows `x ≐ u`, every term converts with its instance at `x := u`**, under any
number of binders. The instance is written back in the frame's context by a shift. -/
theorem converts_with_instance {rules : Expr Base Const → Expr Base Const → Prop} (k : Nat)
    (u : Expr Base Const) {K : EquationStore (Expr Base Const)}
    (known : (bvar k, shiftN (k + 1) u) ∈ K) :
    ∀ (e : Expr Base Const) (depth : Nat),
      Relation.EqvGen
        (RewriteUnder (fun depth left right => rules left right ∨ assumedAt K depth left right)
          depth)
        e (shiftAt (k + depth) (substAt (k + depth) u e))
  | .bvar i, depth => by
      rcases Nat.lt_trichotomy i (k + depth) with below | same | above
      · rw [substAt_bvar_lt u below, shiftAt_bvar_lt below]
        exact Relation.EqvGen.refl _
      · subst same
        rw [substAt_bvar_eq, shiftAt_shiftN u (k + depth) (k + depth) (Nat.le_refl _)]
        refine Relation.EqvGen.rel _ _
          (RewriteUnder.root (Or.inr ⟨(bvar k, shiftN (k + 1) u), known, ?_, ?_⟩))
        · exact (shiftN_bvar k depth).symm
        · show shiftN (k + depth + 1) u = shiftN depth (shiftN (k + 1) u)
          rw [shiftN_shiftN]
          exact congrArg (fun count => shiftN count u) (by omega)
      · rw [substAt_bvar_gt u above, shiftAt_bvar_ge (by omega : ¬ i - 1 < k + depth)]
        have back : i - 1 + 1 = i := by omega
        rw [back]
        exact Relation.EqvGen.refl _
  | .univ, _ => Relation.EqvGen.refl _
  | .prop, _ => Relation.EqvGen.refl _
  | .base _, _ => Relation.EqvGen.refl _
  | .pi A B, depth =>
      under_congr₂ Expr.pi (fun _ _ _ step => .piDomain step) (fun _ _ _ step => .piBody step)
        (converts_with_instance k u known A depth) (converts_with_instance k u known B (depth + 1))
  | .lam A b, depth =>
      under_congr₂ Expr.lam (fun _ _ _ step => .lamDomain step) (fun _ _ _ step => .lamBody step)
        (converts_with_instance k u known A depth) (converts_with_instance k u known b (depth + 1))
  | .app f a, depth =>
      under_congr₂ Expr.app (fun _ _ _ step => .appFunction step)
        (fun _ _ _ step => .appArgument step) (converts_with_instance k u known f depth)
        (converts_with_instance k u known a depth)
  | .const _ _, _ => Relation.EqvGen.refl _
  | .tyFam _, _ => Relation.EqvGen.refl _
  | .top, _ => Relation.EqvGen.refl _
  | .bot, _ => Relation.EqvGen.refl _
  | .and p q, depth =>
      under_congr₂ Expr.and (fun _ _ _ step => .andLeft step) (fun _ _ _ step => .andRight step)
        (converts_with_instance k u known p depth) (converts_with_instance k u known q depth)
  | .or p q, depth =>
      under_congr₂ Expr.or (fun _ _ _ step => .orLeft step) (fun _ _ _ step => .orRight step)
        (converts_with_instance k u known p depth) (converts_with_instance k u known q depth)
  | .imp p q, depth =>
      under_congr₂ Expr.imp (fun _ _ _ step => .impLeft step) (fun _ _ _ step => .impRight step)
        (converts_with_instance k u known p depth) (converts_with_instance k u known q depth)
  | .not p, depth =>
      under_congr Expr.not (fun _ _ step => .notBody step)
        (converts_with_instance k u known p depth)
  | .eq a b, depth =>
      under_congr₂ Expr.eq (fun _ _ _ step => .eqLeft step) (fun _ _ _ step => .eqRight step)
        (converts_with_instance k u known a depth) (converts_with_instance k u known b depth)
  | .all A b, depth =>
      under_congr₂ Expr.all (fun _ _ _ step => .allDomain step) (fun _ _ _ step => .allBody step)
        (converts_with_instance k u known A depth) (converts_with_instance k u known b (depth + 1))
  | .ex A b, depth =>
      under_congr₂ Expr.ex (fun _ _ _ step => .exDomain step) (fun _ _ _ step => .exBody step)
        (converts_with_instance k u known A depth) (converts_with_instance k u known b (depth + 1))

/-- Terms whose instances convert in the bubble convert at every frame that knows the
definition. -/
theorem convertibleKnowing_of_instances {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (k : Nat) (u : Expr Base Const)
    {K : EquationStore (Expr Base Const)} (known : (bvar k, shiftN (k + 1) u) ∈ K)
    {A B : Expr Base Const} (instances : Convertible rules (substAt k u A) (substAt k u B)) :
    ConvertibleKnowing rules K A B :=
  Relation.EqvGen.trans _ _ _ (converts_with_instance k u known A 0)
    (Relation.EqvGen.trans _ _ _
      (convertibleKnowing_of_convertible K (convertible_shiftAt stable instances k))
      (Relation.EqvGen.symm _ _ (converts_with_instance k u known B 0)))

/-- The definition, instantiated at itself, is a reflexive equation. -/
theorem definition_solves {rules : Expr Base Const → Expr Base Const → Prop} (k : Nat)
    (u : Expr Base Const) :
    ∀ equation ∈ [((bvar k : Expr Base Const), shiftN (k + 1) u)],
      Convertible rules (substAt k u equation.1) (substAt k u equation.2) := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  show Convertible rules (substAt k u (bvar k)) (substAt k u (shiftN (k + 1) u))
  rw [substAt_bvar_eq, substAt_shiftN_cancel u u k k (Nat.le_refl _)]
  exact Relation.EqvGen.refl _

/-- Terms that convert at the frame of a definition have instances that convert in the bubble. -/
theorem instances_of_convertibleKnowing {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules) (k : Nat)
    (u : Expr Base Const) {A B : Expr Base Const}
    (converted : ConvertibleKnowing rules [(bvar k, shiftN (k + 1) u)] A B) :
    Convertible rules (substAt k u A) (substAt k u B) := by
  refine convertible_of_knowing shiftStable ?_ (convertibleKnowing_subst substStable k u converted)
  intro equation member
  obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp member
  exact definition_solves k u original inStore

/-- **Conversion at the frame of a definition is conversion of the instances.** -/
theorem solved_conversion_iff {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules) (k : Nat)
    (u : Expr Base Const) {A B : Expr Base Const} :
    ConvertibleKnowing rules [(bvar k, shiftN (k + 1) u)] A B ↔
      Convertible rules (substAt k u A) (substAt k u B) :=
  ⟨instances_of_convertibleKnowing substStable shiftStable k u,
    convertibleKnowing_of_instances shiftStable k u (List.mem_singleton_self _)⟩

/-- **At the frame of a definition, the types of a term convert at the frame**, when the bubble's
conversion is coherent and the defining term is typed in the bubble. -/
theorem typedKnowing_unique_solved {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    (coherent : Coherent (Convertible rules)) {Θ : List (Expr Base Const)}
    {u C : Expr Base Const} (typedU : HasTypeInside rules Θ u C) (Δ : List (Expr Base Const))
    {Γ : List (Expr Base Const)} (split : Γ = Δ ++ C :: Θ) {e A B : Expr Base Const}
    (first : TypedKnowing rules [(bvar Δ.length, shiftN (Δ.length + 1) u)] Γ e A)
    (second : TypedKnowing rules [(bvar Δ.length, shiftN (Δ.length + 1) u)] Γ e B) :
    ConvertibleKnowing rules [(bvar Δ.length, shiftN (Δ.length + 1) u)] A B :=
  convertibleKnowing_of_instances shiftStable Δ.length u (List.mem_singleton_self _)
    (typed_unique coherent
      (typedKnowing_subst_solution substStable shiftStable typedU first Δ split
        (definition_solves Δ.length u))
      (typedKnowing_subst_solution substStable shiftStable typedU second Δ split
        (definition_solves Δ.length u)))

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls

/-- The rules of the arithmetic bubbles are stable under shifting. -/
theorem bubbleRules_shiftStable (plus : Bool) : ShiftStable (bubbleRules plus) := by
  intro left right rule cutoff
  cases plus with
  | false => exact rule_shiftStable left right rule cutoff
  | true =>
      cases rule with
      | recursion inner => exact RulePlus.recursion (rule_shiftStable _ _ inner cutoff)
      | zeroAdd => exact RulePlus.zeroAdd _

/-- With no declared step, conversion is coherent. -/
theorem none_coherent : Coherent (Convertible (fun _ _ : AExpr => False)) :=
  coherent_convertible (fun _ _ rule => rule.elim) (fun _ _ _ _ converted =>
    convertible_none_iff.mpr (Expr.pi.inj (convertible_none_iff.mp converted)).2)

/-- **A decision of conversion at a frame.** At the frame `n : nat, v : Vec n` that knows `n ≐ 0`,
with no declared step, two terms convert exactly when their instances at `n := 0` are
identical. -/
theorem vector_frame_conversion {A B : AExpr} :
    ConvertibleKnowing (fun _ _ => False) vectorKnowledge A B ↔
      substAt 1 zeroE A = substAt 1 zeroE B :=
  (solved_conversion_iff (rules := fun _ _ : AExpr => False) (fun _ _ rule => rule.elim)
    (fun _ _ rule => rule.elim) 1 zeroE).trans convertible_none_iff

/-- `Vec n` converts with `Vec 0` at the frame. -/
theorem vec_n_converts :
    ConvertibleKnowing (fun _ _ => False) vectorKnowledge (vec (bvar 1)) (vec zeroE) :=
  vector_frame_conversion.mpr rfl

/-- `Vec 1` does not convert with `Vec 0` at the frame. -/
theorem vec_one_does_not_convert :
    ¬ ConvertibleKnowing (fun _ _ => False) vectorKnowledge (vec (succE zeroE)) (vec zeroE) := by
  intro converted
  have same := vector_frame_conversion.mp converted
  simp [substAt, vec, succE, zeroE] at same

/-- **The two types of `λ (m : nat). v` at the frame convert at the frame**: the type found with
the knowledge, `Π (m : nat). Vec 0`, and the type of the global judgment, `Π (m : nat). Vec n`. -/
theorem constant_function_types_convert :
    ConvertibleKnowing (fun _ _ => False) vectorKnowledge (Expr.pi natType (vec zeroE))
      (Expr.pi natType (vec (bvar 2))) :=
  typedKnowing_unique_solved (rules := fun _ _ : AExpr => False) (fun _ _ rule => rule.elim)
    (fun _ _ rule => rule.elim) none_coherent
    (BubbleTypingInside.hasTypeInside_none_iff.mpr (HasType.const _ ArithConst.zero))
    [vec (bvar 0)] rfl constant_function_at_zero
    (TypedKnowing.of_hasType
      (HasType.lam (HasType.base ()) (HasType.var (Γ := natType :: vecContext) (i := 1) rfl)) _)

/-- **Over the arithmetic bubbles, conversion at the frame of a definition is decided by the
normal forms of the instances.** -/
theorem arith_solved_conversion_iff (plus : Bool) (k : Nat) (u : AExpr) {A B : AExpr} :
    ConvertibleKnowing (bubbleRules plus) [(bvar k, shiftN (k + 1) u)] A B ↔
      Arith.norm plus (substAt k u A) = Arith.norm plus (substAt k u B) :=
  (solved_conversion_iff (bubbleRules_stable plus) (bubbleRules_shiftStable plus) k u).trans
    (conv_iff_norm plus)

/-- **Over the arithmetic bubbles, the types of a term at the frame of a definition convert at
the frame.** -/
theorem arith_unique_solved (plus : Bool) {Θ : List AExpr} {u C : AExpr}
    (typedU : HasTypeInside (bubbleRules plus) Θ u C) (Δ : List AExpr) {Γ : List AExpr}
    (split : Γ = Δ ++ C :: Θ) {e A B : AExpr}
    (first : TypedKnowing (bubbleRules plus) [(bvar Δ.length, shiftN (Δ.length + 1) u)] Γ e A)
    (second : TypedKnowing (bubbleRules plus) [(bvar Δ.length, shiftN (Δ.length + 1) u)] Γ e B) :
    ConvertibleKnowing (bubbleRules plus) [(bvar Δ.length, shiftN (Δ.length + 1) u)] A B :=
  typedKnowing_unique_solved (bubbleRules_stable plus) (bubbleRules_shiftStable plus)
    (BubbleTypingAlgorithmic.Controls.arith_coherent plus) typedU Δ split first second

/-- With the recursion equations declared and `n ≐ 0` known, `Vec (n + 1)`, written
`Vec (succ (n + 0))`, converts with `Vec 1`: the knowledge and the declared steps work together. -/
theorem vec_succ_n_converts :
    ConvertibleKnowing (bubbleRules false) [((bvar 1 : AExpr), shiftN (1 + 1) zeroE)]
      (vec (succE (addE (bvar 1) zeroE))) (vec (succE zeroE)) :=
  (arith_solved_conversion_iff false 1 zeroE).mpr rfl

/-- **Knowledge between closed terms is not the instantiation of a variable.** The frame that
knows `0 ≐ 1` converts `Vec 0` with `Vec 1`, and no instantiation of a variable does. -/
theorem closed_knowledge_is_not_an_instantiation :
    ConvertibleKnowing (fun _ _ => False) [(zeroE, succE zeroE)] (vec zeroE)
        (vec (succE zeroE)) ∧
      ∀ (k : Nat) (u : AExpr),
        ¬ Convertible (fun _ _ => False) (substAt k u (vec zeroE))
          (substAt k u (vec (succE zeroE))) := by
  refine ⟨Relation.EqvGen.rel _ _
    (RewriteUnder.appArgument
      (RewriteUnder.root
        (Or.inr ⟨(zeroE, succE zeroE), List.mem_singleton_self _, rfl, rfl⟩))), ?_⟩
  intro k u converted
  have same := convertible_none_iff.mp converted
  simp [substAt, vec, succE, zeroE] at same

end Controls

/-! ## Axiom audit -/

#print axioms converts_with_instance
#print axioms convertibleKnowing_of_instances
#print axioms instances_of_convertibleKnowing
#print axioms solved_conversion_iff
#print axioms typedKnowing_unique_solved
#print axioms Controls.vector_frame_conversion
#print axioms Controls.vec_n_converts
#print axioms Controls.vec_one_does_not_convert
#print axioms Controls.constant_function_types_convert
#print axioms Controls.arith_solved_conversion_iff
#print axioms Controls.arith_unique_solved
#print axioms Controls.vec_succ_n_converts
#print axioms Controls.closed_knowledge_is_not_an_instantiation

end Mettapedia.TypeTheory.KnowledgeSolvedForm
