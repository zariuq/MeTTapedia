import Mathlib.Data.Sigma.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Membership evidence of material sets

`Mem x X` is the type of evidence that `x` is a member of `X`, the reading of
`holds (In x X)`. It is a `Sort`, so proof-relevant evidence and Lean
propositions are both instances. Two types are derived from it:

* `El Mem X := Σ' x, Mem x X`, the members of `X` with their evidence;
* `Members Mem X := {x // Nonempty (Mem x X)}`, the members as a bare fact.

`forget : El Mem X → Members Mem X` keeps a member and forgets its evidence.

The profile law `PropositionalMembership` says that any two pieces of evidence
for one membership are equal. The results:

* `forget_injective_iff`: forgetting evidence is injective exactly when each
  evidence type is a subsingleton;
* `elEquivMembers`: with an `EvidenceRecovery`, `El X` is then equivalent to the
  subtype of members, and every family on `El X` factors uniquely through the
  members (`descend_forget`, `eq_descend_of_factors`);
* `forall_descends_iff`: every proposition-valued family descends along the
  first projection exactly when membership is propositional;
* `not_factors_of_distinguishes`: a family that tells two
  witnesses of one membership apart factors through no function of the
  members;
* `transport`, the identity reading of `eq@set`: transport along an equality of
  sets keeps the member (`transport_fst`), and it is determined by the member
  exactly when membership is propositional (`transport_determined_iff`).

No set operation is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets

universe u v w

section Evidence

variable {S : Type u} (Mem : S → S → Sort v)

/-- The members of `X` together with their membership evidence,
`El X := Σ x. holds (In x X)`. -/
abbrev El (X : S) := Σ' x : S, Mem x X

/-- The members of `X`, with membership as a bare proposition. -/
abbrev Members (X : S) := {x : S // Nonempty (Mem x X)}

/-- The profile law: any two pieces of evidence for one membership are equal. -/
def PropositionalMembership : Prop :=
  ∀ x X : S, Subsingleton (Mem x X)

/-- Evidence recovered from the bare fact of membership. A model uses it to
eliminate an existential into a membership proposition. It is not the profile
law: the two-witness model has one. -/
structure EvidenceRecovery where
  recover : ∀ {x X : S}, Nonempty (Mem x X) → Mem x X

variable {Mem}

/-- Keep the member and forget its evidence. -/
def forget {X : S} (a : El Mem X) : Members Mem X := ⟨a.1, ⟨a.2⟩⟩

@[simp] theorem forget_val {X : S} (a : El Mem X) : (forget a).1 = a.1 := rfl

/-! ## Forgetting evidence -/

/-- Forgetting evidence: the first projection is injective exactly when each
evidence type is a subsingleton. -/
theorem fst_injective_iff {X : S} :
    Function.Injective (PSigma.fst : El Mem X → S) ↔ ∀ x, Subsingleton (Mem x X) := by
  constructor
  · intro injective x
    refine ⟨fun p q => ?_⟩
    have same : (⟨x, p⟩ : El Mem X) = ⟨x, q⟩ := injective rfl
    exact eq_of_heq (PSigma.mk.inj_iff.mp same).2
  · rintro fibres ⟨x, p⟩ ⟨y, q⟩ (same : x = y)
    subst same
    exact congrArg (PSigma.mk x) ((fibres x).elim p q)

theorem forget_injective_iff {X : S} :
    Function.Injective (forget : El Mem X → Members Mem X) ↔
      ∀ x, Subsingleton (Mem x X) := by
  rw [← fst_injective_iff]
  constructor
  · intro injective a b same
    exact injective (Subtype.ext same)
  · intro injective a b same
    exact injective (congrArg Subtype.val same)

theorem propositional_iff_forget_injective :
    PropositionalMembership Mem ↔
      ∀ X : S, Function.Injective (forget : El Mem X → Members Mem X) :=
  ⟨fun h X => forget_injective_iff.mpr fun x => h x X,
    fun h x X => forget_injective_iff.mp (h X) x⟩

theorem fst_injective (h : PropositionalMembership Mem) {X : S} :
    Function.Injective (PSigma.fst : El Mem X → S) :=
  fst_injective_iff.mpr fun x => h x X

/-- Members with the same underlying set are equal. -/
theorem El.ext (h : PropositionalMembership Mem) {X : S} {a b : El Mem X}
    (same : a.1 = b.1) : a = b :=
  fst_injective h same

/-! ## Descent of families on `El` -/

/-- The proposition-valued family anchored at one member with its evidence. -/
def anchored {X : S} (a₀ : El Mem X) : El Mem X → Prop := fun a => a = a₀

/-- A family on `El X` descends when its value depends only on the member. -/
def Descends {X : S} {B : Sort w} (F : El Mem X → B) : Prop :=
  ∀ a b : El Mem X, a.1 = b.1 → F a = F b

theorem descends_of_propositional (h : PropositionalMembership Mem) {X : S} {B : Sort w}
    (F : El Mem X → B) : Descends F :=
  fun _ _ same => congrArg F (El.ext h same)

/-- Universal descent: every proposition-valued family on `El X` descends
exactly when membership in `X` is propositional. The anchored equality
families already decide it. -/
theorem forall_descends_iff {X : S} :
    (∀ F : El Mem X → Prop, Descends F) ↔ ∀ x, Subsingleton (Mem x X) := by
  rw [← fst_injective_iff]
  constructor
  · intro all a b same
    exact (cast (all (anchored a) a b same) (rfl : a = a) : b = a).symm
  · intro injective F a b same
    rw [injective same]

/-- With propositional membership and evidence recovery, `El X` is the subtype
of members of `X`. -/
def elEquivMembers (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem) (X : S) :
    El Mem X ≃ Members Mem X where
  toFun := forget
  invFun m := ⟨m.1, r.recover m.2⟩
  left_inv _ := El.ext h rfl
  right_inv _ := rfl

/-- The family on the members induced by a family on `El X`, through recovered
evidence. -/
def descend (r : EvidenceRecovery Mem) {X : S} {B : Sort w} (F : El Mem X → B) :
    Members Mem X → B :=
  fun m => F ⟨m.1, r.recover m.2⟩

/-- Descent: a family on `El X` factors through the members. -/
theorem descend_forget (h : PropositionalMembership Mem) (r : EvidenceRecovery Mem)
    {X : S} {B : Sort w} (F : El Mem X → B) (a : El Mem X) :
    descend r F (forget a) = F a :=
  congrArg F (El.ext h rfl)

/-- The factorization is unique: recovery makes `forget` surjective. -/
theorem eq_descend_of_factors (r : EvidenceRecovery Mem) {X : S} {B : Sort w}
    (F : El Mem X → B) (f : Members Mem X → B) (factors : ∀ a, f (forget a) = F a) :
    f = descend r F :=
  funext fun m => factors ⟨m.1, r.recover m.2⟩

/-! ## Two witnesses -/

/-- The two-witness obstruction: a family
that tells two witnesses of one membership apart factors through no function
of the members. -/
theorem not_factors_of_distinguishes {X x : S} {B : Sort w} (F : El Mem X → B)
    {p q : Mem x X} (distinguishes : F ⟨x, p⟩ ≠ F ⟨x, q⟩) :
    ¬ ∃ f : Members Mem X → B, ∀ a, f (forget a) = F a := by
  rintro ⟨f, factors⟩
  exact distinguishes ((factors ⟨x, p⟩).symm.trans (factors ⟨x, q⟩))

theorem not_descends_of_distinguishes {X x : S} {B : Sort w} (F : El Mem X → B)
    {p q : Mem x X} (distinguishes : F ⟨x, p⟩ ≠ F ⟨x, q⟩) : ¬ Descends F :=
  fun descends => distinguishes (descends ⟨x, p⟩ ⟨x, q⟩ rfl)

/-- Two distinct witnesses are told apart by the family anchored at one. -/
theorem anchored_distinguishes {X x : S} {p q : Mem x X} (distinct : p ≠ q) :
    anchored (⟨x, p⟩ : El Mem X) ⟨x, p⟩ ≠ anchored ⟨x, p⟩ ⟨x, q⟩ := by
  intro same
  have back : (⟨x, q⟩ : El Mem X) = ⟨x, p⟩ := cast same (rfl : (⟨x, p⟩ : El Mem X) = ⟨x, p⟩)
  exact distinct (eq_of_heq (PSigma.mk.inj_iff.mp back).2).symm

theorem not_propositional_of_witnesses {X x : S} {p q : Mem x X} (distinct : p ≠ q) :
    ¬ PropositionalMembership Mem :=
  fun h => not_descends_of_distinguishes (anchored (⟨x, p⟩ : El Mem X))
    (anchored_distinguishes distinct) (descends_of_propositional h _)

/-! ## Equality of sets read as identity -/

/-- Transport of members along an equality of sets: `J` at the family `El`. -/
def transport {X Y : S} (e : X = Y) (a : El Mem X) : El Mem Y :=
  Eq.ndrec (motive := fun Z => El Mem Z) a e

@[simp] theorem transport_rfl {X : S} (a : El Mem X) : transport rfl a = a := rfl

/-- Transport along an equality of sets keeps the member. -/
theorem transport_fst {X Y : S} (e : X = Y) (a : El Mem X) : (transport e a).1 = a.1 := by
  subst e
  rfl

/-- Reindex members along an evidence map, keeping each member. -/
def reindex {X Y : S} (map : ∀ z, Mem z X → Mem z Y) (a : El Mem X) : El Mem Y :=
  ⟨a.1, map a.1 a.2⟩

theorem transport_eq_of_fst_eq (h : PropositionalMembership Mem) {X Y : S} (e : X = Y)
    (a : El Mem X) (b : El Mem Y) (same : a.1 = b.1) : transport e a = b :=
  El.ext h ((transport_fst e a).trans same)

/-- Transport computes as reindexing along any evidence map. -/
theorem transport_eq_reindex (h : PropositionalMembership Mem) {X Y : S} (e : X = Y)
    (map : ∀ z, Mem z X → Mem z Y) (a : El Mem X) : transport e a = reindex map a :=
  transport_eq_of_fst_eq h e a _ rfl

/-- Transport along equalities of sets is determined by the member exactly when
membership is propositional. -/
theorem transport_determined_iff :
    (∀ {X Y : S} (e : X = Y) (a : El Mem X) (b : El Mem Y), a.1 = b.1 → transport e a = b) ↔
      PropositionalMembership Mem := by
  constructor
  · intro determined x X
    exact fst_injective_iff.mp (fun a b same => determined rfl a b same) x
  · intro h X Y e a b same
    exact transport_eq_of_fst_eq h e a b same

end Evidence

end Mettapedia.TypeTheory.MaterialSets
