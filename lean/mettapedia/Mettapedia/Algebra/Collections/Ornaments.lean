import Mathlib.Data.W.Constructions
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.End

/-!
# Ornaments of datatype descriptions and the linear class

A datatype description is a polynomial: a type `α` of node shapes and, for
each shape `a`, the type `β a` of its recursive positions. The datatype it
describes is the W-type `WType β`, whose values are nodes `⟨a, children⟩`.

An **ornament** of a base description `β'` by a description `β` sends every
shape of `β` to a shape of `β'` and puts their recursive positions in
bijection (`Ornament`). It may add data at a node, or split one base shape
into several, but never changes the recursion; as a map of polynomial
functors it is cartesian.

* **Forgetting.** An ornament forgets down to its base (`Ornament.forget`).
  Ornaments compose, and forgetting along a composite is the composite of the
  forgettings (`Ornament.forget_comp`, `Ornament.forget_id`).
* **Base folds serve every ornament.** A fold of the base, read after
  forgetting, is a fold of the ornamented datatype, by the algebra that reads
  each node through the ornament (`Ornament.elim_forget`). An operation that
  is a fold of the base is written and proved once and applies to every
  ornament of that base.
* **The linear class.** A description is linear when every shape has at most
  one recursive position. Up to renaming its shapes are steps, carrying data
  in `C` and one recursive position, and stops, carrying data in `E` and none
  (`Linear`). Its datatype is the list of its steps followed by its stop
  (`Linear.spineEquiv : WType (Linear C E) ≃ List C × E`). Every linear
  description is an ornament of the natural numbers, forgetting to the number
  of its steps (`Linear.natOrnament`, `Linear.toNat_forget`), and an ornament
  of the lists of its steps, forgetting the stop (`Linear.listOrnament`,
  `Linear.toList_forget`). When steps and stops carry no data the ornament
  of the naturals is a bijection (`Linear.natOrnament_forget_bijective`):
  a Peano datatype is the naturals.
* **Indices maintained by a fold.** An algebraic ornament indexes a datatype
  by the value of a fold. A list fold whose steps are bijections is the
  product of its steps (`foldr_eq_prod_map`), so its value on every suffix is
  recovered from the value on the whole and the inverse of the dropped steps
  (`foldr_drop_of_perm`).

Controls: forgetting to the naturals loses the data, so two different lists
of one length forget alike (`Controls.forget_not_injective`); a description
with a node of two recursive positions is no ornament of the naturals
(`Controls.no_nat_ornament_of_trees`); and for a step that is not a
bijection, such as `max`, the value on the whole does not determine the value
on a suffix (`Controls.max_suffix_not_recovered`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.Ornaments

universe u u' u'' v v' v''

/-- An ornament of the description `β'` by the description `β`: a map of
shapes with a bijection of recursive positions over it. -/
structure Ornament {α : Type u} {α' : Type u'} (β : α → Type v) (β' : α' → Type v') where
  /-- The base shape of each shape. -/
  shape : α → α'
  /-- The recursive positions of a shape are those of its base shape. -/
  pos : ∀ a, β' (shape a) ≃ β a

namespace Ornament

variable {α : Type u} {α' : Type u'} {α'' : Type u''}
  {β : α → Type v} {β' : α' → Type v'} {β'' : α'' → Type v''}

/-- Forget an ornamented value down to the base. -/
def forget (o : Ornament β β') : WType β → WType β'
  | ⟨a, f⟩ => ⟨o.shape a, fun b => o.forget (f (o.pos a b))⟩

/-- The identity ornament. -/
def id (β : α → Type v) : Ornament β β where
  shape a := a
  pos _ := Equiv.refl _

/-- Ornaments compose. -/
def comp (o₂ : Ornament β' β'') (o₁ : Ornament β β') : Ornament β β'' where
  shape a := o₂.shape (o₁.shape a)
  pos a := (o₂.pos (o₁.shape a)).trans (o₁.pos a)

theorem forget_id : ∀ t : WType β, (id β).forget t = t
  | ⟨a, f⟩ => by
      simp only [forget, id]
      congr
      funext b
      exact forget_id (f b)

/-- Forgetting along a composite is the composite of the forgettings. -/
theorem forget_comp (o₂ : Ornament β' β'') (o₁ : Ornament β β') :
    ∀ t : WType β, (o₂.comp o₁).forget t = o₂.forget (o₁.forget t)
  | ⟨a, f⟩ => by
      simp only [forget, comp]
      congr
      funext b
      exact forget_comp o₂ o₁ (f (o₁.pos a (o₂.pos (o₁.shape a) b)))

/-- The algebra of the ornamented description that reads each node through
the ornament. -/
def pullback (o : Ornament β β') {γ : Type*} (alg : (Σ a' : α', β' a' → γ) → γ) :
    (Σ a : α, β a → γ) → γ :=
  fun node => alg ⟨o.shape node.1, fun b => node.2 (o.pos node.1 b)⟩

/-- **A fold of the base serves every ornament.** Folding after forgetting is
folding the ornamented value by the pulled-back algebra. -/
theorem elim_forget (o : Ornament β β') {γ : Type*} (alg : (Σ a' : α', β' a' → γ) → γ) :
    ∀ t : WType β, WType.elim γ alg (o.forget t) = WType.elim γ (o.pullback alg) t
  | ⟨a, f⟩ => by
      simp only [forget, WType.elim, pullback]
      congr
      funext b
      exact elim_forget o alg (f (o.pos a b))

end Ornament

/-! ## Linear descriptions -/

/-- The recursive positions of a linear description: a step `inl c` has one,
a stop `inr e` has none. -/
def Linear (C : Type u) (E : Type v) : C ⊕ E → Type
  | .inl _ => Unit
  | .inr _ => Empty

namespace Linear

variable {C : Type u} {E : Type v}

/-- The steps of a linear value, in order, and its stop. -/
def toSpine : WType (Linear C E) → List C × E
  | ⟨.inl c, f⟩ => (c :: (toSpine (f ())).1, (toSpine (f ())).2)
  | ⟨.inr e, _⟩ => ([], e)

/-- The linear value of a list of steps followed by a stop. -/
def ofSpine : List C → E → WType (Linear C E)
  | [], e => ⟨.inr e, fun b => nomatch b⟩
  | c :: cs, e => ⟨.inl c, fun _ => ofSpine cs e⟩

theorem ofSpine_toSpine : ∀ t : WType (Linear C E), ofSpine (toSpine t).1 (toSpine t).2 = t
  | ⟨.inl c, f⟩ => by
      simp only [toSpine, ofSpine]
      congr
      funext u
      exact ofSpine_toSpine (f u)
  | ⟨.inr e, f⟩ => by
      simp only [toSpine, ofSpine]
      congr
      funext b
      exact nomatch b

theorem toSpine_ofSpine : ∀ (cs : List C) (e : E), toSpine (ofSpine cs e) = (cs, e)
  | [], _ => rfl
  | c :: cs, e => by simp only [ofSpine, toSpine, toSpine_ofSpine cs e]

/-- **A linear datatype is the list of its steps with its stop.** -/
def spineEquiv : WType (Linear C E) ≃ List C × E where
  toFun := toSpine
  invFun s := ofSpine s.1 s.2
  left_inv := ofSpine_toSpine
  right_inv s := toSpine_ofSpine s.1 s.2

/-- Every linear description is an ornament of the natural numbers: steps
over successor, stops over zero. -/
def natOrnament : Ornament (Linear C E) WType.Natβ where
  shape
    | .inl _ => .succ
    | .inr _ => .zero
  pos
    | .inl _ => Equiv.refl _
    | .inr _ => Equiv.refl _

/-- The ornament of the naturals forgets a linear value to its number of
steps. -/
theorem toNat_forget : ∀ t : WType (Linear C E),
    WType.toNat (natOrnament.forget t) = (toSpine t).1.length
  | ⟨.inl c, f⟩ => by
      simp only [Ornament.forget, natOrnament, WType.toNat, toSpine, List.length_cons]
      exact congrArg Nat.succ (toNat_forget (f ()))
  | ⟨.inr e, f⟩ => rfl

/-- Every linear description is an ornament of the lists of its steps: a
step `c` over `cons c`, every stop over `nil`. -/
def listOrnament : Ornament (Linear C E) (WType.Listβ C) where
  shape
    | .inl c => .cons c
    | .inr _ => .nil
  pos
    | .inl _ => Equiv.punitEquivPUnit
    | .inr _ => (Equiv.equivPEmpty Empty).symm

/-- The ornament of lists forgets a linear value to its steps. -/
theorem toList_forget : ∀ t : WType (Linear C E),
    WType.toList C (listOrnament.forget t) = (toSpine t).1
  | ⟨.inl c, f⟩ => by
      simp only [Ornament.forget, listOrnament, WType.toList, toSpine]
      exact congrArg (c :: ·) (toList_forget (f ()))
  | ⟨.inr e, f⟩ => rfl

/-- **Peano datatypes are the naturals.** When steps and stops carry no data,
forgetting to the naturals is a bijection. -/
theorem natOrnament_forget_bijective [Subsingleton C] [Subsingleton E] [Inhabited C]
    [Inhabited E] : Function.Bijective (natOrnament (C := C) (E := E)).forget := by
  constructor
  · intro t₁ t₂ same
    have lengths := congrArg WType.toNat same
    rw [toNat_forget, toNat_forget] at lengths
    rw [← ofSpine_toSpine t₁, ← ofSpine_toSpine t₂]
    have steps : (toSpine t₁).1 = (toSpine t₂).1 :=
      List.ext_getElem lengths fun _ _ _ => Subsingleton.elim _ _
    rw [steps, Subsingleton.elim (toSpine t₁).2 (toSpine t₂).2]
  · intro n
    refine ⟨ofSpine (List.replicate (WType.toNat n) default) default, ?_⟩
    apply WType.equivNat.injective
    change WType.toNat _ = WType.toNat n
    rw [toNat_forget, toSpine_ofSpine, List.length_replicate]

end Linear

/-! ## Indices maintained by a fold -/

section Measures

variable {C : Type u} {R : Type v}

/-- A list fold whose steps are permutations is the product of its steps. -/
theorem foldr_eq_prod_map (step : C → Equiv.Perm R) (e : R) (xs : List C) :
    xs.foldr (fun c r => step c r) e = (xs.map step).prod e := by
  induction xs with
  | nil => rfl
  | cons c xs ih => simp [ih, Equiv.Perm.mul_apply]

/-- **Suffix recovery.** For a fold whose steps are permutations, the value
on the suffix after `i` steps is the value on the whole, with the first `i`
steps undone. -/
theorem foldr_drop_of_perm (step : C → Equiv.Perm R) (e : R) (xs : List C) (i : ℕ) :
    (xs.drop i).foldr (fun c r => step c r) e =
      ((xs.take i).map step).prod⁻¹ (xs.foldr (fun c r => step c r) e) := by
  have split : (xs.map step).prod = ((xs.take i).map step).prod * ((xs.drop i).map step).prod := by
    rw [← List.prod_append, ← List.map_append, List.take_append_drop]
  rw [foldr_eq_prod_map, foldr_eq_prod_map, split, Equiv.Perm.mul_apply]
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

end Measures

/-! ## Controls -/

namespace Controls

open Linear

/-- Forgetting to the naturals loses the data: `[true]` and `[false]` are
different values with one step each. -/
theorem forget_not_injective :
    ofSpine [true] () ≠ ofSpine [false] () ∧
      (natOrnament (C := Bool) (E := Unit)).forget (ofSpine [true] ()) =
        natOrnament.forget (ofSpine [false] ()) := by
  refine ⟨fun same => ?_, ?_⟩
  · have := congrArg (fun t => (toSpine t).1) same
    simp [toSpine_ofSpine] at this
  · apply WType.equivNat.injective
    change WType.toNat _ = WType.toNat _
    rw [toNat_forget, toNat_forget, toSpine_ofSpine, toSpine_ofSpine]
    rfl

/-- The description of binary trees: leaves have no recursive position, nodes
have two. -/
def treePositions : Bool → Type
  | false => Empty
  | true => Bool

/-- **Trees are not linear.** No ornament puts the two positions of a node
over a shape of the naturals. -/
theorem no_nat_ornament_of_trees : IsEmpty (Ornament treePositions WType.Natβ) := by
  constructor
  intro o
  have positions : WType.Natβ (o.shape true) ≃ Bool := o.pos true
  cases h : o.shape true with
  | zero =>
      rw [h] at positions
      change Empty ≃ Bool at positions
      exact nomatch positions.symm true
  | succ =>
      rw [h] at positions
      change Unit ≃ Bool at positions
      have := positions.symm.injective (Subsingleton.elim (positions.symm true) (positions.symm false))
      exact Bool.noConfusion this

/-- For `max`, which is no bijection, `[5, 1]` and `[5, 2]` have one value
while their suffixes after one step have two. -/
theorem max_suffix_not_recovered :
    [5, 1].foldr max 0 = [5, 2].foldr max 0 ∧
      ([5, 1].drop 1).foldr max 0 ≠ ([5, 2].drop 1).foldr max 0 := by
  decide

end Controls

end Mettapedia.Algebra.Collections.Ornaments
