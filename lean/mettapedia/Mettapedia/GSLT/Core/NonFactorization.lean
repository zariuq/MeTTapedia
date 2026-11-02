import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Factorization through an observation

`Factors shadow invariant` means that a total function of the observed value
recovers the invariant. A collision with different invariant values refutes
factorization; postprocessing cannot repair such a collision.

The exact positive criterion has two parts: the invariant is constant on
observation fibres, and an inhabited observation carrier permits an inhabited
result carrier. The second condition matters when the source is empty.
Surjective observations or inhabited result types discharge it automatically.
The general converse uses classical choice; a supplied recovery remains
explicit computational data.

Factorization composes. Its obstructions transport along coarsenings and
changes of coordinates, independently of the particular language or policy.
-/

namespace Mettapedia.GSLT.Core.NonFactorization

universe uA uS uV

/-- `invariant` **factors through** `shadow` when some function of the shadow
recovers it.  This is what it means for a projection to retain everything the
invariant depends on. -/
def Factors {A : Sort uA} {S : Sort uS} {V : Sort uV}
    (shadow : A → S) (invariant : A → V) : Prop :=
  ∃ recover : S → V, ∀ a, recover (shadow a) = invariant a

/-- `invariant` is **constant on fibres** of `shadow` when points with equal
shadows have equal values. -/
def ConstantOnFibers {A : Sort uA} {S : Sort uS} {V : Sort uV}
    (shadow : A → S) (invariant : A → V) : Prop :=
  ∀ a b, shadow a = shadow b → invariant a = invariant b

/-- Anything recoverable from the shadow is constant on fibres. -/
theorem Factors.constantOnFibers {A : Sort uA} {S : Sort uS} {V : Sort uV}
    {shadow : A → S} {invariant : A → V} (factors : Factors shadow invariant) :
    ConstantOnFibers shadow invariant := by
  obtain ⟨recover, recovers⟩ := factors
  exact fun a b sameShadow => (recovers a).symm.trans
    ((congrArg recover sameShadow).trans (recovers b))

/-- Total recovery needs both agreement on used fibres and a possible result
for every observation, including values outside the image. -/
theorem factors_iff_fibres_and_nonempty {A : Sort uA} {S : Sort uS} {V : Sort uV}
    (shadow : A → S) (invariant : A → V) :
    Factors shadow invariant ↔
      ConstantOnFibers shadow invariant ∧ (Nonempty S → Nonempty V) := by
  classical
  constructor
  · rintro ⟨recover, recovers⟩
    exact ⟨Factors.constantOnFibers ⟨recover, recovers⟩, Nonempty.map recover⟩
  · rintro ⟨constant, possible⟩
    refine ⟨fun value => if seen : ∃ a, shadow a = value then invariant seen.choose
      else Classical.choice (possible ⟨value⟩), fun a => ?_⟩
    have seen : ∃ other, shadow other = shadow a := ⟨a, rfl⟩
    dsimp only
    rw [dif_pos seen]
    exact constant seen.choose a seen.choose_spec

/-- An inhabited result type supplies all unused observation values. -/
theorem factors_iff_constantOnFibers_of_nonempty
    {A : Sort uA} {S : Sort uS} {V : Sort uV} [Nonempty V]
    (shadow : A → S) (invariant : A → V) :
    Factors shadow invariant ↔ ConstantOnFibers shadow invariant :=
  (factors_iff_fibres_and_nonempty shadow invariant).trans
    ⟨And.left, fun constant => ⟨constant, fun _ => inferInstance⟩⟩

/-- Recovering a view and then a result composes without choosing representatives. -/
theorem Factors.trans {A : Sort uA} {B : Sort uS} {C : Sort uV} {D : Sort*}
    {first : A → B} {second : A → C} {third : A → D}
    (before : Factors first second) (after : Factors second third) : Factors first third := by
  obtain ⟨recover, recovers⟩ := before
  obtain ⟨finish, finishes⟩ := after
  exact ⟨finish ∘ recover, fun a => (congrArg finish (recovers a)).trans (finishes a)⟩

/-- Two points with one observed value and distinct invariant values. -/
structure NonTrivialFiber {A : Sort uA} {S : Sort uS} {V : Sort uV}
    (shadow : A → S) (invariant : A → V) where
  /-- One ambient point. -/
  left : A
  /-- Another ambient point with the same shadow. -/
  right : A
  /-- The projection cannot tell them apart. -/
  sameShadow : shadow left = shadow right
  /-- The invariant can. -/
  differentValue : invariant left ≠ invariant right

/-- **The criterion.**  A non-trivial fibre refutes factorization. -/
theorem NonTrivialFiber.not_factors {A : Sort uA} {S : Sort uS} {V : Sort uV}
    {shadow : A → S} {invariant : A → V}
    (fiber : NonTrivialFiber shadow invariant) :
    ¬ Factors shadow invariant := fun factors =>
  fiber.differentValue (factors.constantOnFibers _ _ fiber.sameShadow)

/-- A non-trivial fibre is exactly the failure of fibre-constancy. -/
theorem NonTrivialFiber.not_constantOnFibers {A : Sort uA} {S : Sort uS}
    {V : Sort uV} {shadow : A → S} {invariant : A → V}
    (fiber : NonTrivialFiber shadow invariant) :
    ¬ ConstantOnFibers shadow invariant := fun constant =>
  fiber.differentValue (constant _ _ fiber.sameShadow)

/-- Conversely, failure of fibre-constancy produces a witness. -/
theorem nonTrivialFiber_of_not_constantOnFibers {A : Sort uA} {S : Sort uS}
    {V : Sort uV} {shadow : A → S} {invariant : A → V}
    (notConstant : ¬ ConstantOnFibers shadow invariant) :
    Nonempty (NonTrivialFiber shadow invariant) := by
  by_contra empty
  exact notConstant fun a b sameShadow => by
    by_contra differentValue
    exact empty ⟨⟨a, b, sameShadow, differentValue⟩⟩

/-- **Propositional form.**  When the invariant is a proposition, a fibre is
non-trivial as soon as it holds at one end and fails at the other. -/
def NonTrivialFiber.ofProp {A : Sort uA} {S : Sort uS} {shadow : A → S}
    {invariant : A → Prop} {a b : A} (sameShadow : shadow a = shadow b)
    (holds : invariant a) (fails : ¬ invariant b) :
    NonTrivialFiber shadow invariant where
  left := a
  right := b
  sameShadow := sameShadow
  differentValue := fun equalValues => fails (equalValues ▸ holds)

/-- Surjectivity supplies every output value. This proof uses only choice;
the general extension criterion also covers unused observation values. -/
theorem factors_iff_constantOnFibers {A S V : Type*} {shadow : A → S}
    (surjective : Function.Surjective shadow) (invariant : A → V) :
    Factors shadow invariant ↔ ConstantOnFibers shadow invariant := by
  refine ⟨Factors.constantOnFibers, fun constant => ?_⟩
  refine ⟨fun s => invariant (Function.surjInv surjective s), fun a => ?_⟩
  exact constant _ _ (Function.surjInv_eq surjective (shadow a))

/-! ## Change of ambient coordinates -/

/-- Replacing the ambient carrier by an equivalent one preserves and reflects
factorization when both the shadow and invariant are transported along that
equivalence. -/
theorem factors_precomp_equiv_iff
    {A : Type uA} {B : Type*} {S : Type uS} {V : Type uV}
    (equivalence : Equiv A B) (shadow : B → S) (invariant : B → V) :
    Factors (shadow ∘ equivalence) (invariant ∘ equivalence) ↔
      Factors shadow invariant := by
  exact exists_congr fun recover =>
    (equivalence.surjective.forall (p := fun value => recover (shadow value) = invariant value)).symm

/-- Nonfactorization is invariant under the same equivalent change of ambient
coordinates. -/
theorem not_factors_precomp_equiv_iff
    {A : Type uA} {B : Type*} {S : Type uS} {V : Type uV}
    (equivalence : Equiv A B) (shadow : B → S) (invariant : B → V) :
    (¬ Factors (shadow ∘ equivalence) (invariant ∘ equivalence)) ↔
      ¬ Factors shadow invariant :=
  not_congr (factors_precomp_equiv_iff equivalence shadow invariant)

/-! ## Coarsening

Further forgetting cannot repair a distinction already erased. -/

/-- If `shadow` is `fine` followed by a further forgetting step, then
anything recoverable from `shadow` was already recoverable from `fine`. -/
theorem Factors.of_coarsening {A : Sort uA} {S : Sort uS} {S' : Sort*}
    {V : Sort uV} {shadow : A → S} {fine : A → S'} {coarsen : S' → S}
    (coarsens : ∀ a, shadow a = coarsen (fine a)) {invariant : A → V}
    (factors : Factors shadow invariant) : Factors fine invariant :=
  (show Factors fine shadow from ⟨coarsen, fun a => (coarsens a).symm⟩).trans factors

/-- **Obstructions propagate outward.**  Failing to factor through a finer
projection implies failing to factor through any coarsening of it. -/
theorem not_factors_of_coarsening {A : Sort uA} {S : Sort uS} {S' : Sort*}
    {V : Sort uV} {shadow : A → S} {fine : A → S'} {coarsen : S' → S}
    (coarsens : ∀ a, shadow a = coarsen (fine a)) {invariant : A → V}
    (fineFails : ¬ Factors fine invariant) : ¬ Factors shadow invariant :=
  fun factors => fineFails (factors.of_coarsening coarsens)

/-- A fibre of a finer projection is a fibre of any coarsening. -/
def NonTrivialFiber.coarsen {A : Sort uA} {S : Sort uS} {S' : Sort*}
    {V : Sort uV} {shadow : A → S} {fine : A → S'} {coarsen : S' → S}
    (coarsens : ∀ a, shadow a = coarsen (fine a)) {invariant : A → V}
    (fiber : NonTrivialFiber fine invariant) :
    NonTrivialFiber shadow invariant where
  left := fiber.left
  right := fiber.right
  sameShadow := by simp only [coarsens, fiber.sameShadow]
  differentValue := fiber.differentValue

/-! ## Subsingleton shadows

A proposition-valued view separates no inhabitants. Thus erasing a derivation
to mere provability loses every nonconstant proof readout. -/

/-- Into a subsingleton, any two points share a shadow. -/
def NonTrivialFiber.ofSubsingleton {A : Sort uA} {S : Sort uS} {V : Sort uV}
    [Subsingleton S] {shadow : A → S} {invariant : A → V} {a b : A}
    (differentValue : invariant a ≠ invariant b) :
    NonTrivialFiber shadow invariant where
  left := a
  right := b
  sameShadow := Subsingleton.elim _ _
  differentValue := differentValue

/-- **Nothing that separates survives a subsingleton shadow.**  A projection
whose codomain is a proposition retains an invariant only when that invariant
was already constant. -/
theorem factors_subsingleton_iff_constant {A : Sort uA} {S : Sort uS}
    {V : Sort uV} [Subsingleton S] [Nonempty A] {shadow : A → S}
    (invariant : A → V) :
    Factors shadow invariant ↔ ∀ a b, invariant a = invariant b := by
  refine ⟨fun factors a b => factors.constantOnFibers a b (Subsingleton.elim _ _),
    fun constant => ?_⟩
  refine ⟨fun _ => invariant (Classical.arbitrary A), fun a => constant _ a⟩

namespace Controls

/-- A used view can support a concrete result despite having unused codes. -/
theorem unused_view_recovery :
    ¬ Function.Surjective (fun _ : Unit => false) ∧
      Factors (fun _ : Unit => false) (fun _ => (7 : Nat)) := by
  refine ⟨?_, ⟨fun _ => 7, fun _ => rfl⟩⟩
  intro onto
  obtain ⟨_, impossible⟩ := onto true
  cases impossible

/-- Fibre constancy alone misses the obstruction to filling unused codes. -/
theorem empty_source_requires_output :
    ConstantOnFibers (fun _ : Empty => ()) (id : Empty → Empty) ∧
      ¬ Factors (fun _ : Empty => ()) (id : Empty → Empty) :=
  ⟨(fun a => nomatch a), fun ⟨recover, _⟩ => nomatch recover ()⟩

end Controls

end Mettapedia.GSLT.Core.NonFactorization
