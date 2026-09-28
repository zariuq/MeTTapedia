import Mettapedia.TypeTheory.IndexedPolynomialFree
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.Data.Finite.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite contexts of event generators for an indexed rule presentation

Objects carry finitely many typed event variables. An arrow substitutes a
free rule tree for each target variable. Composition is the already proved
hole-filling operation, so it retains constructor occurrences and ordered
recursive positions. This is the contextual syntactic category underlying
the free operational theory at a fixed family of judgments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts

open Mettapedia.TypeTheory
open CategoryTheory
open CategoryTheory.Limits

universe uIndex uShape

/-- A finite family of event variables indexed by judgments. The support
may use arbitrary judgment indices, but the total number of variables is
finite. -/
structure Context {Judgment : Type uIndex}
    (P : IndexedPolynomial.{0, uIndex, uShape, 0}
      Unit (fun _ => Judgment)) where
  slots : Judgment → Type
  finite : Finite (Σ judgment, slots judgment)

variable {Judgment : Type uIndex}
variable (P : IndexedPolynomial.{0, uIndex, uShape, 0}
  Unit (fun _ => Judgment))

/-- Free operational syntax with leaves supplied by the context. -/
abbrev Term (Γ : Context P) (judgment : Judgment) : Type _ :=
  P.Free (fun _ index => Γ.slots index) PUnit.unit judgment

/-- A simultaneous substitution assigns a tree to each variable of the
target context, preserving its judgment index. -/
abbrev Substitution (Γ Δ : Context P) : Type _ :=
  ∀ judgment, Δ.slots judgment → Term P Γ judgment

/-- The identity substitution names each variable as a typed leaf. -/
def identity (Γ : Context P) :
    Substitution P Γ Γ :=
  fun _ slot => IndexedPolynomial.Free.pure P slot

/-- Compose substitutions by filling the leaves of the later trees with
the earlier trees. -/
noncomputable def compose {Γ Δ Θ : Context P}
    (earlier : Substitution P Γ Δ)
    (later : Substitution P Δ Θ) : Substitution P Γ Θ :=
  fun judgment slot =>
    IndexedPolynomial.Free.bind P
      (fun _ index seed => earlier index seed) PUnit.unit judgment
      (later judgment slot)

/-- Substitution by variables on the source side changes no tree. -/
theorem identity_comp {Γ Δ : Context P}
    (f : Substitution P Γ Δ) : compose P (identity P Γ) f = f := by
  funext judgment slot
  exact IndexedPolynomial.Free.bind_pure_right P (f judgment slot)

/-- Substitution into a target variable returns its assigned tree. -/
theorem comp_identity {Γ Δ : Context P}
    (f : Substitution P Γ Δ) : compose P f (identity P Δ) = f := by
  funext judgment slot
  exact IndexedPolynomial.Free.bind_pure P
    (fun _ index seed => f index seed) slot

/-- Filling a free tree in two stages agrees with one composite filling. -/
theorem compose_assoc {Γ Δ Θ Ψ : Context P}
    (first : Substitution P Γ Δ)
    (second : Substitution P Δ Θ)
    (third : Substitution P Θ Ψ) :
    compose P (compose P first second) third =
      compose P first (compose P second third) := by
  funext judgment slot
  exact (IndexedPolynomial.Free.bind_assoc P
    (fun _ index seed => second index seed)
    (fun _ index seed => first index seed)
    (third judgment slot)).symm

/-- The free operational term substitutions form a category, with
composition justified by the polynomial free-algebra laws. -/
noncomputable instance : Category (Context P) where
  Hom Γ Δ := Substitution P Γ Δ
  id Γ := identity P Γ
  comp f g := compose P f g
  id_comp := by intro Γ Δ f; exact identity_comp P f
  comp_id := by intro Γ Δ f; exact comp_identity P f
  assoc := by intro Γ Δ Θ Ψ f g h; exact compose_assoc P f g h

/-- A context with no event variables. -/
def empty : Context P where
  slots := fun _ => PEmpty
  finite := by
    exact .intro {
      toFun := fun ⟨_, impossible⟩ => impossible.elim
      invFun := fun index => Fin.elim0 index
      left_inv := by intro ⟨_, impossible⟩; exact impossible.elim
      right_inv := by intro index; exact Fin.elim0 index }

/-- Every context has one substitution into the empty context. -/
noncomputable def emptyIsTerminal : IsTerminal (empty P) :=
  IsTerminal.ofUniqueHom
    (fun _ _ slot => slot.elim)
    (fun _ mapping => by
      funext judgment slot
      exact slot.elim)

instance : HasTerminal (Context P) :=
  (emptyIsTerminal P).hasTerminal

/-- A finite family of variables in the sum context is equivalently a
variable from its left or right summand. -/
def sigmaSumEquiv (Γ Δ : Context P) :
    (Σ judgment, Γ.slots judgment ⊕ Δ.slots judgment) ≃
      (Σ judgment, Γ.slots judgment) ⊕
        (Σ judgment, Δ.slots judgment) where
  toFun
    | ⟨judgment, .inl slot⟩ => .inl ⟨judgment, slot⟩
    | ⟨judgment, .inr slot⟩ => .inr ⟨judgment, slot⟩
  invFun
    | .inl ⟨judgment, slot⟩ => ⟨judgment, .inl slot⟩
    | .inr ⟨judgment, slot⟩ => ⟨judgment, .inr slot⟩
  left_inv := by intro ⟨judgment, slot⟩; cases slot <;> rfl
  right_inv := by intro slot; cases slot with
    | inl value => cases value; rfl
    | inr value => cases value; rfl

/-- The sum has finite support because both summands do. -/
def product (Γ Δ : Context P) : Context P where
  slots := fun judgment => Γ.slots judgment ⊕ Δ.slots judgment
  finite := by
    obtain ⟨m, ⟨left⟩⟩ :=
      @Finite.exists_equiv_fin (Σ judgment, Γ.slots judgment) Γ.finite
    obtain ⟨n, ⟨right⟩⟩ :=
      @Finite.exists_equiv_fin (Σ judgment, Δ.slots judgment) Δ.finite
    exact Finite.intro ((sigmaSumEquiv P Γ Δ).trans
      ((Equiv.sumCongr left right).trans finSumFinEquiv))

/-- Project left by naming each left variable as a leaf of the sum. -/
def firstProjection (Γ Δ : Context P) : product P Γ Δ ⟶ Γ :=
  fun _ slot => IndexedPolynomial.Free.pure P (.inl slot)

/-- Project right by naming each right variable as a leaf of the sum. -/
def secondProjection (Γ Δ : Context P) : product P Γ Δ ⟶ Δ :=
  fun _ slot => IndexedPolynomial.Free.pure P (.inr slot)

set_option linter.checkUnivs false in
/-- Pair two substitutions by case analysis on the chosen target variable.
The constructor and event evidence inside each branch remain untouched. -/
noncomputable def pair {Ξ Γ Δ : Context P} (f : Ξ ⟶ Γ) (g : Ξ ⟶ Δ) :
    Ξ ⟶ product P Γ Δ :=
  fun judgment => fun
    | .inl slot => f judgment slot
    | .inr slot => g judgment slot

/-- The sum of finite event-variable contexts is their categorical product
for substitutions into free firing trees. -/
noncomputable def productIsLimit (Γ Δ : Context P) :
    IsLimit (BinaryFan.mk (firstProjection P Γ Δ)
      (secondProjection P Γ Δ)) :=
  BinaryFan.IsLimit.mk _ (fun f g => pair P f g)
    (by
      intro Ξ f g
      funext judgment slot
      rfl)
    (by
      intro Ξ f g
      funext judgment slot
      rfl)
    (by
      intro Ξ f g mapping left right
      funext judgment slot
      cases slot with
      | inl value =>
          have hvalue := congrFun (congrFun left judgment) value
          exact hvalue
      | inr value =>
          have hvalue := congrFun (congrFun right judgment) value
          exact hvalue)

noncomputable instance hasLimitPair (Γ Δ : Context P) :
    HasLimit (Limits.pair Γ Δ) :=
  ⟨⟨BinaryFan.mk (firstProjection P Γ Δ)
      (secondProjection P Γ Δ), productIsLimit P Γ Δ⟩⟩

noncomputable instance : HasBinaryProducts (Context P) :=
  hasBinaryProducts_of_hasLimit_pair (Context P)

noncomputable instance : HasFiniteProducts (Context P) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

/-- One variable at a chosen judgment, used to read out a model's carrier. -/
def singleton (judgment : Judgment) : Context P where
  slots := fun other => PLift (other = judgment)
  finite := by
    exact Finite.intro {
      toFun := fun _ => 0
      invFun := fun _ => ⟨judgment, ⟨rfl⟩⟩
      left_inv := by
        intro ⟨other, ⟨equal⟩⟩
        cases equal
        rfl
      right_inv := by intro index; exact (Fin.eq_zero index).symm }

/-- Forgetting the child's judgment identifies all typed input variables
with the constructor's ordered recursive positions. -/
def aritySlotsEquiv {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment) :
    (Σ child, {position : P.Position shape // P.next shape position = child}) ≃
      P.Position shape where
  toFun := fun ⟨_, position⟩ => position.1
  invFun := fun position => ⟨P.next shape position, ⟨position, rfl⟩⟩
  left_inv := by
    intro ⟨child, ⟨position, equal⟩⟩
    cases equal
    rfl
  right_inv := by intro position; rfl

/-- A constructor's typed input variables are exactly its recursive
positions. The equality in a slot records the child's judgment. -/
def arityContext {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] : Context P where
  slots := fun child => {position : P.Position shape // P.next shape position = child}
  finite := by
    exact Finite.of_equiv (P.Position shape) (aritySlotsEquiv P shape).symm

/-- The generator for a finitary rule shape is an actual free tree with
one variable at each ordered premise position. -/
def constructorArrow {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] :
    arityContext P shape ⟶ singleton P judgment :=
  fun target equal => by
    obtain ⟨equal⟩ := equal
    cases equal
    exact IndexedPolynomial.Free.node P shape
      (fun position => IndexedPolynomial.Free.pure P ⟨position, rfl⟩)

/-- Composing with a constructor arrow substitutes the supplied premise
trees into each exact recursive position, without changing the constructor. -/
theorem compose_constructorArrow {Γ : Context P}
    {judgment : Judgment} (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)]
    (arguments : Γ ⟶ arityContext P shape) :
    arguments ≫ constructorArrow P shape =
      (fun target equal => by
        obtain ⟨equal⟩ := equal
        cases equal
        exact IndexedPolynomial.Free.node P shape
          (fun position => arguments (P.next shape position) ⟨position, rfl⟩)) := by
  funext target equal
  obtain ⟨equal⟩ := equal
  cases equal
  change IndexedPolynomial.Free.bind P
      (fun _ index slot => arguments index slot) PUnit.unit judgment
      (IndexedPolynomial.Free.node P shape
        (fun position => IndexedPolynomial.Free.pure P ⟨position, rfl⟩)) = _
  rw [IndexedPolynomial.Free.bind_node]
  rfl

/-- Each recursive premise position determines a projection from the
constructor's arity context to a one-variable judgment context. -/
def positionProjection {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] (position : P.Position shape) :
    arityContext P shape ⟶ singleton P (P.next shape position) :=
  fun target equal => by
    obtain ⟨equal⟩ := equal
    cases equal
    exact IndexedPolynomial.Free.pure P ⟨position, rfl⟩

/-- The arity context is a product of its typed one-variable contexts.
This is the finite-product decomposition needed to recover a rule action
from a product-preserving interpretation. -/
noncomputable def arityFan {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] :
    Fan (fun position => singleton P (P.next shape position)) :=
  Fan.mk (arityContext P shape) (positionProjection P shape)

noncomputable def arityFanIsLimit {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment)
    [Finite (P.Position shape)] : IsLimit (arityFan P shape) :=
  Fan.IsLimit.mk (arityFan P shape)
    (fun source => fun child ⟨position, equal⟩ =>
      (source.proj position) child ⟨equal.symm⟩)
    (by
      intro source position
      funext child equal
      obtain ⟨equal⟩ := equal
      cases equal
      rfl)
    (by
      intro source mapping respects
      funext child slot
      obtain ⟨position, equal⟩ := slot
      cases equal
      have h := congrFun (congrFun (respects position)
        (P.next shape position)) (⟨rfl⟩ :
          (singleton P (P.next shape position)).slots (P.next shape position))
      exact h)

/-- Project a general finite context onto one selected typed variable. -/
def variableProjection (Γ : Context P)
    (selected : Σ judgment, Γ.slots judgment) :
    Γ ⟶ singleton P selected.1 :=
  fun target equal => by
    obtain ⟨equal⟩ := equal
    cases equal
    exact IndexedPolynomial.Free.pure P selected.2

/-- A free rule tree in a context is equivalently one arrow from that
context to the singleton context at its judgment. -/
def termArrow {Γ : Context P} {judgment : Judgment}
    (tree : Term P Γ judgment) : Γ ⟶ singleton P judgment :=
  fun target equal => by
    obtain ⟨equal⟩ := equal
    cases equal
    exact tree

/-- Pair the typed child trees into a substitution to the constructor's
arity context. -/
def tupleArrow {Γ : Context P} {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment) [Finite (P.Position shape)]
    (children : ∀ position, Term P Γ (P.next shape position)) :
    Γ ⟶ arityContext P shape :=
  fun child ⟨position, equal⟩ => by
    cases equal
    exact children position

/-- Selecting one premise from the paired substitution recovers its exact
free child tree. -/
theorem tupleArrow_projection {Γ : Context P} {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment) [Finite (P.Position shape)]
    (children : ∀ position, Term P Γ (P.next shape position))
    (position : P.Position shape) :
    tupleArrow P shape children ≫ positionProjection P shape position =
      termArrow P (children position) := by
  funext target equal
  obtain ⟨equal⟩ := equal
  cases equal
  rfl

/-- Applying a constructor to its paired child terms is exactly the
single arrow represented by the resulting free node. -/
theorem tupleArrow_constructor {Γ : Context P} {judgment : Judgment}
    (shape : P.Shape PUnit.unit judgment) [Finite (P.Position shape)]
    (children : ∀ position, Term P Γ (P.next shape position)) :
    tupleArrow P shape children ≫ constructorArrow P shape =
      termArrow P (IndexedPolynomial.Free.node P shape children) := by
  rw [compose_constructorArrow]
  rfl

theorem termArrow_pure {Γ : Context P} {judgment : Judgment}
    (slot : Γ.slots judgment) :
    termArrow P (IndexedPolynomial.Free.pure P slot) =
      variableProjection P Γ ⟨judgment, slot⟩ := rfl

/-- A substituted variable of the target context is the corresponding
free term arrow after composing with the substitution. -/
theorem compose_variableProjection {Γ Δ : Context P}
    (substitution : Γ ⟶ Δ) {judgment : Judgment}
    (slot : Δ.slots judgment) :
    substitution ≫ variableProjection P Δ ⟨judgment, slot⟩ =
      termArrow P (substitution judgment slot) := by
  funext target equal
  obtain ⟨equal⟩ := equal
  cases equal
  rfl

/-- Every finite context is a product of the singleton contexts for its
actual typed variables. -/
noncomputable def contextFan (Γ : Context P) :
    Fan (fun selected : Σ judgment, Γ.slots judgment =>
      singleton P selected.1) :=
  Fan.mk Γ (variableProjection P Γ)

noncomputable def contextFanIsLimit (Γ : Context P) :
    IsLimit (contextFan P Γ) :=
  Fan.IsLimit.mk (contextFan P Γ)
    (fun source => fun judgment slot =>
      (source.proj ⟨judgment, slot⟩) judgment ⟨rfl⟩)
    (by
      intro source selected
      obtain ⟨judgment, slot⟩ := selected
      funext target equal
      obtain ⟨equal⟩ := equal
      cases equal
      rfl)
    (by
      intro source mapping respects
      funext judgment slot
      have h := congrFun (congrFun (respects ⟨judgment, slot⟩)
        judgment) (⟨rfl⟩ : (singleton P judgment).slots judgment)
      exact h)

/-- An operation with countably many recursive inputs is a negative
boundary example: it has free trees and substitution, but its input arity
cannot be represented by a finite product of generator contexts. -/
def countablyBranching : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Nat
  next _ _ := ()

theorem countablyBranching_notFinitary :
    ¬ Finite (countablyBranching.Position (base := ()) (index := ()) ()) := by
  change ¬ Finite Nat
  exact Infinite.not_finite

end Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
