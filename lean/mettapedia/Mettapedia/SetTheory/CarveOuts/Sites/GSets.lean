import Mettapedia.SetTheory.CarveOuts.Sites.Bridge

/-!
# Sets and `G`-sets: the same truth values, different objects

A set with an action of a group `G` is a functor from the one-object category of `G` to sets;
contextual forcing (`ContextualMaterialLogic.force`) reads formulas about it along the arrows of
that category, which are the elements of `G`.

**The truth values agree.** For a group every arrow is invertible, so a cosieve on the one
context contains every arrow as soon as it contains one: a truth value is decided by the
identity (`Cosieve.mem_iff_mem_id`), and the truth values at the context form the frame `Prop`
(`cosieveOrderIsoProp`), the frame of truth values of plain sets. Every one of them is global,
fixed by every arrow (`cosieve_isGlobal`), and the reading by reachable stages forgets nothing
(`reach_holds_iff_mem_id`). For the monoid with an idempotent (`Collapse`) the cosieve of
`collapse` is neither empty nor everything, and it is not global (`collapseCosieve_not_global`).

**Forcing is two-valued truth in the underlying structure.** Over a group, forcing does not
change along an arrow (`force_transport_iff`), and forcing a formula at the context is its
truth in the underlying set with its membership, read with Lean's own connectives
(`force_iff_tarski`). So the verdicts of all sentences on a `G`-set are a function of its
underlying set: the frame reading `frameReading` (forget the action) is a `Factors` map for
them (`factors_frameReading`).

**The objects differ.** Let the group with two elements act on `Bool` by negation (`swapBool`)
and trivially (`trivialBool`). Their frame readings are both `Bool`, and they are not isomorphic
`G`-sets (`not_iso_trivial_swap`): `fiber_frameReading` is the non-trivial fibre. The action is
also what carries global elements: both force "something exists", and only the trivial one has
a fixed point (`fiber_frameReading_globalElement`, `exists_without_global_element`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.GSLT.Core.NonFactorization

universe v

/-! ## Two-valued truth in a structure -/

/-- Truth of a formula in a set with a membership relation, read with Lean's connectives. -/
def Tarski {M : Type*} (member : M → M → Prop) : {n : ℕ} → Formula n → (Fin n → M) → Prop
  | _, .bottom, _ => False
  | _, .equal i j, e => e i = e j
  | _, .member i j, e => member (e i) (e j)
  | _, .both φ ψ, e => Tarski member φ e ∧ Tarski member ψ e
  | _, .either φ ψ, e => Tarski member φ e ∨ Tarski member ψ e
  | _, .imply φ ψ, e => Tarski member φ e → Tarski member ψ e
  | _, .all body, e => ∀ a, Tarski member body (Fin.cases a e)
  | _, .exist body, e => ∃ a, Tarski member body (Fin.cases a e)

/-! ## Forcing over a group -/

section Group

variable {G : Type} [Group G] {values : SingleObj G ⥤ Type v} (model : Model values)

/-- An arrow of the one-object category, read backwards. -/
def backward {s t : SingleObj G} (g : s ⟶ t) : t ⟶ s :=
  (g : G)⁻¹

theorem comp_backward {s t : SingleObj G} (g : s ⟶ t) : g ≫ backward g = 𝟙 s :=
  inv_mul_cancel (g : G)

/-- **Over a group, forcing does not change along an arrow.** -/
theorem force_transport_iff {n : ℕ} (φ : Formula n) {s t : SingleObj G} (g : s ⟶ t)
    (env : Environment values n s) :
    force values model φ t (transport values g env) ↔ force values model φ s env := by
  constructor
  · intro h
    have back := force_transport model φ (backward g) _ h
    rwa [← transport_comp, comp_backward, transport_id] at back
  · exact force_transport model φ g env

/-- **Forcing over a group is two-valued truth in the underlying structure.** -/
theorem force_iff_tarski {n : ℕ} (φ : Formula n) (s : SingleObj G) (env : Environment values n s) :
    force values model φ s env ↔ Tarski (model.member s) φ env := by
  induction φ generalizing s with
  | bottom => exact Iff.rfl
  | equal => exact Iff.rfl
  | member => exact Iff.rfl
  | both φ ψ ihφ ihψ => exact and_congr (ihφ s env) (ihψ s env)
  | either φ ψ ihφ ihψ => exact or_congr (ihφ s env) (ihψ s env)
  | imply φ ψ ihφ ihψ =>
    show (∀ (t : SingleObj G) (g : s ⟶ t), force values model φ t (transport values g env) →
        force values model ψ t (transport values g env)) ↔
      (Tarski (model.member s) φ env → Tarski (model.member s) ψ env)
    rw [← ihφ s env, ← ihψ s env]
    constructor
    · intro h hφ
      have := h s (𝟙 s)
      rw [transport_id] at this
      exact this hφ
    · intro h t g hφ
      exact (force_transport_iff model ψ g env).mpr
        (h ((force_transport_iff model φ g env).mp hφ))
  | all body ih =>
    show (∀ (t : SingleObj G) (g : s ⟶ t) (value : values.obj t),
        force values model body t (extend values (transport values g env) value)) ↔
      ∀ a, Tarski (model.member s) body (Fin.cases a env)
    constructor
    · intro h a
      have := h s (𝟙 s) a
      rw [transport_id] at this
      exact (ih s _).mp this
    · intro h t g value
      refine (force_transport_iff model body (backward g) _).mp ?_
      rw [transport_extend, ← transport_comp, comp_backward, transport_id]
      exact (ih s _).mpr (h _)
  | exist body ih =>
    exact exists_congr fun a => ih s (extend values env a)

/-- In a group every arrow into a cosieve brings the identity in. -/
theorem Cosieve.mem_iff_mem_id {s t : SingleObj G} (S : Cosieve s) (f : s ⟶ t) :
    S.mem t f ↔ S.mem s (𝟙 s) := by
  constructor
  · intro h
    have back := S.comp_mem f (backward f) h
    rwa [comp_backward] at back
  · intro h
    have forth := S.comp_mem (𝟙 s) f h
    rwa [Category.id_comp] at forth

/-- **Over a group the truth values at the context are `Prop`.** -/
def cosieveOrderIsoProp (s : SingleObj G) : Cosieve s ≃o Prop where
  toFun S := S.mem s (𝟙 s)
  invFun p := ⟨fun _ _ => p, fun _ _ h => h⟩
  left_inv S := Cosieve.ext' fun _ f => (Cosieve.mem_iff_mem_id S f).symm
  right_inv _ := rfl
  map_rel_iff' {S T} := by
    constructor
    · intro h t f hS
      exact (Cosieve.mem_iff_mem_id T f).mpr (h ((Cosieve.mem_iff_mem_id S f).mp hS))
    · intro h hS
      exact h s (𝟙 s) hS

/-- **Over a group the reach of a truth value is its verdict at the context.** -/
theorem reach_holds_iff_mem_id {s : SingleObj G} (S : Cosieve s) (t : Reach (SingleObj G)) :
    S.reach.holds t ↔ S.mem s (𝟙 s) :=
  ⟨fun ⟨f, h⟩ => (Cosieve.mem_iff_mem_id S f).mp h,
    fun h => ⟨(1 : G), (Cosieve.mem_iff_mem_id S _).mpr h⟩⟩

/-- A global truth value: a cosieve on the one context fixed by pulling back along every
arrow. -/
def Cosieve.IsGlobal {M : Type} [Monoid M] (S : Cosieve (SingleObj.star M)) : Prop :=
  ∀ g : SingleObj.star M ⟶ SingleObj.star M, S.pullback g = S

/-- **Over a group every truth value is global.** -/
theorem cosieve_isGlobal (S : Cosieve (SingleObj.star G)) : S.IsGlobal := fun g =>
  Cosieve.ext' fun _ f => (Cosieve.mem_iff_mem_id S (g ≫ f)).trans (Cosieve.mem_iff_mem_id S f).symm

end Group

/-- **Control: an idempotent makes a truth value that is not global.** -/
theorem collapseCosieve_not_global : ¬ Idempotent.collapseCosieve.IsGlobal := fun h => by
  have pulled := congrArg (fun S : Cosieve (SingleObj.star Collapse) => S.mem _ (𝟙 _))
    (h (Idempotent.collapseArrow _))
  have hmem : (Idempotent.collapseCosieve.pullback (Idempotent.collapseArrow _)).mem _
      (𝟙 (SingleObj.star Collapse)) := by
    show Collapse.one * Collapse.collapse = Collapse.collapse
    rfl
  exact Idempotent.collapseCosieve_not_id ((show _ = _ from pulled) ▸ hmem)

/-! ## `G`-sets and their frame reading -/

section GSet

variable {G : Type} [Group G]

/-- A `G`-set as a functor on the one-object category of `G`. -/
abbrev gValues (X : Action Type G) : SingleObj G ⥤ Type :=
  actionValues X

/-- A `G`-set with no membership: the language of equality. -/
def gModel (X : Action Type G) : Model (gValues X) where
  member _ _ _ := False
  member_transport := by
    intro _ _ _ _ _ h
    exact h

/-- The verdicts of all sentences on a `G`-set, forced at its one context. -/
def sentenceVerdicts (X : Action Type G) : Formula 0 → Prop :=
  fun φ => force (gValues X) (gModel X) φ (SingleObj.star G) Fin.elim0

/-- **The frame reading**: a `G`-set read through its two-valued truth values, as a plain set. -/
def frameReading (X : Action Type G) : Type :=
  X.V

/-- **The frame reading keeps every verdict.** -/
theorem factors_frameReading : Factors (frameReading (G := G)) sentenceVerdicts :=
  ⟨fun T φ => Tarski (fun _ _ : T => False) φ Fin.elim0, fun X => funext fun φ =>
    propext (force_iff_tarski (gModel X) φ (SingleObj.star G) Fin.elim0).symm⟩

/-- A global element: a fixed point of the action. -/
def GlobalElement (X : Action Type G) : Prop :=
  ∃ x : X.V, ∀ g : G, X.ρ g x = x

end GSet

/-- The group with two elements. -/
inductive Flip : Type where
  | keep
  | flip
  deriving DecidableEq

instance : Group Flip where
  mul a b := match a, b with
    | .keep, b => b
    | .flip, .keep => .flip
    | .flip, .flip => .keep
  one := .keep
  inv a := a
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  inv_mul_cancel a := by cases a <;> rfl

/-- `flip` negates. -/
instance : MulAction Flip Bool where
  smul a b := match a with
    | .keep => b
    | .flip => !b
  one_smul _ := rfl
  mul_smul a b x := by cases a <;> cases b <;> cases x <;> rfl

/-- The two-element group, acting on `Bool` by negation. -/
abbrev swapBool : Action Type Flip :=
  Action.ofMulAction Flip Bool

/-- The two-element group, acting trivially on `Bool`. -/
abbrev trivialBool : Action Type Flip :=
  Action.trivial Flip (Bool : Type)

theorem swap_ne_self (b : Bool) : (Flip.flip • b) ≠ b := by
  cases b <;> decide

/-- **The two `G`-sets are not isomorphic.** An isomorphism would carry each value of the
trivial action to a fixed point of the swap. -/
theorem not_iso_trivial_swap : ¬ Nonempty (trivialBool ≅ swapBool) := by
  rintro ⟨e⟩
  have comm := ConcreteCategory.congr_hom (e.hom.comm Flip.flip) true
  exact swap_ne_self _ comm.symm

theorem frameReading_swap_trivial : frameReading swapBool = frameReading trivialBool :=
  rfl

/-- **The frame reading is not injective on objects.** -/
theorem frameReading_not_injective :
    frameReading swapBool = frameReading trivialBool ∧ ¬ Nonempty (trivialBool ≅ swapBool) :=
  ⟨frameReading_swap_trivial, not_iso_trivial_swap⟩

/-- **The frame reading forgets the action.** Two `G`-sets with the same frame reading, one
isomorphic to the natural action and one not. -/
def fiber_frameReading :
    NonTrivialFiber (frameReading (G := Flip)) (fun X => Nonempty (X ≅ swapBool)) :=
  NonTrivialFiber.ofProp (a := swapBool) (b := trivialBool) frameReading_swap_trivial
    ⟨Iso.refl _⟩ not_iso_trivial_swap

theorem globalElement_trivial : GlobalElement trivialBool :=
  ⟨true, fun _ => rfl⟩

theorem not_globalElement_swap : ¬ GlobalElement swapBool := fun ⟨x, hx⟩ =>
  swap_ne_self x (hx Flip.flip)

/-- **The frame reading forgets global elements.** -/
def fiber_frameReading_globalElement :
    NonTrivialFiber (frameReading (G := Flip)) GlobalElement :=
  NonTrivialFiber.ofProp (a := trivialBool) (b := swapBool) frameReading_swap_trivial.symm
    globalElement_trivial not_globalElement_swap

/-- "Something exists." -/
def somethingExists : Formula 0 :=
  .exist (.equal 0 0)

/-- **An existential without a global witness.** The natural action forces that something
exists, and has no fixed point. -/
theorem exists_without_global_element :
    sentenceVerdicts swapBool somethingExists ∧ ¬ GlobalElement swapBool :=
  ⟨⟨true, rfl⟩, not_globalElement_swap⟩

end Mettapedia.SetTheory.CarveOuts.Sites
