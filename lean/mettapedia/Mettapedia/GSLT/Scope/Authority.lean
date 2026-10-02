import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Order.Nat

/-!
# Authority separation and programs over scopes

**Motivation selects; it does not permit.**  Selection by a preference
ranges over an admissibility set fixed beforehand (`select`).
* Everything selected is admissible (`select_subset`), whatever the
  preference.
* Preferences about inadmissible observers change nothing
  (`select_congr`): no preference can make an inadmissible observer
  admissible, or influence the choice through one.
* Control: an admission rule gated by preference is not separated; raising
  the preference for an inadmissible observer admits it
  (`Gate.gate_admits_inadmissible`).

**Sealing composes.**  An observer is sealed against the distinctions of a
relation when it cannot tell related states apart (`SealedBy`).  Sealed
observers are exactly the observers of the quotient view
(`sealedBy_iff_factors`); sealing against two relations is sealing against
their union (`sealedBy_union_iff`), and against its equivalence closure
(`sealedBy_eqvGen_iff`); sealed observers are closed under post-composition
(`SealedBy.post`), and selection among sealed observers returns sealed
observers (`select_sealed`).

**Programs over scopes.**  A program that queries only its scope's declared
guarantees is unchanged by every scope change that preserves the guarantees
(`program_invariant`).  Control: a program reading an undeclared
representation detail changes under a guarantee-preserving change
(`Representation.not_invariant`), and it does not factor through the
guarantees (`Representation.not_factors`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

open Mettapedia.GSLT.Core.NonFactorization

universe u v w

/-! ## Motivation selects among admissible observers -/

section Select

variable {Observer : Type u} {Rank : Type v} [Preorder Rank]

/-- **Selection by a preference among the admissible observers**: the
admissible observers to which no admissible observer is strictly
preferred. -/
def select (admissible : Set Observer) (preference : Observer → Rank) : Set Observer :=
  {observer | observer ∈ admissible ∧
    ∀ other ∈ admissible, ¬ preference observer < preference other}

/-- **Everything selected is admissible.** -/
theorem select_subset (admissible : Set Observer) (preference : Observer → Rank) :
    select admissible preference ⊆ admissible :=
  fun _ selected => selected.1

/-- **Preferences about inadmissible observers change nothing.** -/
theorem select_congr {admissible : Set Observer} {preference preference' : Observer → Rank}
    (agree : ∀ observer ∈ admissible, preference observer = preference' observer) :
    select admissible preference = select admissible preference' := by
  ext observer
  constructor
  · rintro ⟨member, best⟩
    refine ⟨member, fun other otherMember => ?_⟩
    rw [← agree observer member, ← agree other otherMember]
    exact best other otherMember
  · rintro ⟨member, best⟩
    refine ⟨member, fun other otherMember => ?_⟩
    rw [agree observer member, agree other otherMember]
    exact best other otherMember

end Select

namespace Gate

/-- Two observers; only the first is admissible. -/
def admissible : Set Bool :=
  {true}

/-- **An anti-pattern**: admit every observer whose preference reaches a
threshold. -/
def gate (preference : Bool → ℕ) : Set Bool :=
  {observer | 1 ≤ preference observer}

/-- **Control**: raising the preference for the inadmissible observer admits
it. -/
theorem gate_admits_inadmissible :
    false ∈ gate (fun _ => 1) ∧ false ∉ admissible ∧
      false ∉ select admissible (fun _ : Bool => (1 : ℕ)) :=
  ⟨le_refl 1, fun member => Bool.noConfusion (member : false = true),
    fun selected => Bool.noConfusion (selected.1 : false = true)⟩

end Gate

/-! ## Sealing -/

section Seal

variable {X : Type u} {Z : Sort w}

/-- An observer is **sealed against** the distinctions of `R` when it cannot
tell `R`-related states apart. -/
def SealedBy (R : X → X → Prop) (observer : X → Z) : Prop :=
  ∀ ⦃x y : X⦄, R x y → observer x = observer y

/-- **Sealed observers are the observers of the quotient view.** -/
theorem sealedBy_iff_factors (R : X → X → Prop) (observer : X → Z) :
    SealedBy R observer ↔ Factors (Quot.mk R) observer := by
  constructor
  · exact fun sealed => ⟨Quot.lift observer fun _ _ related => sealed related, fun _ => rfl⟩
  · exact fun factors x y related => factors.constantOnFibers x y (Quot.sound related)

/-- **Sealing against two relations is sealing against their union.** -/
theorem sealedBy_union_iff (R R' : X → X → Prop) (observer : X → Z) :
    SealedBy R observer ∧ SealedBy R' observer ↔
      SealedBy (fun x y => R x y ∨ R' x y) observer :=
  ⟨fun ⟨sealed, sealed'⟩ _ _ related => related.elim (fun r => sealed r) fun r => sealed' r,
    fun sealed => ⟨fun _ _ related => sealed (Or.inl related),
      fun _ _ related => sealed (Or.inr related)⟩⟩

/-- Sealing against a relation is sealing against its equivalence closure. -/
theorem sealedBy_eqvGen_iff (R : X → X → Prop) (observer : X → Z) :
    SealedBy R observer ↔ SealedBy (Relation.EqvGen R) observer := by
  constructor
  · intro sealed x y generated
    induction generated with
    | rel _ _ related => exact sealed related
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  · exact fun sealed _ _ related => sealed (Relation.EqvGen.rel _ _ related)

/-- **Sealed observers are closed under post-composition.** -/
theorem SealedBy.post {R : X → X → Prop} {observer : X → Z} (sealed : SealedBy R observer)
    {W : Sort v} (f : Z → W) : SealedBy R fun x => f (observer x) :=
  fun _ _ related => congrArg f (sealed related)

/-- **Selection among sealed observers returns sealed observers.** -/
theorem select_sealed {Observer : Type v} {Rank : Type w} [Preorder Rank]
    (read : Observer → X → Bool) (R : X → X → Prop) (preference : Observer → Rank) :
    ∀ observer ∈ select {o | SealedBy R (read o)} preference, SealedBy R (read observer) :=
  fun _ selected => selected.1

end Seal

/-! ## Programs over scopes -/

section Programs

variable {Scope : Type u} {Guarantee : Type v} {Out : Sort w}

/-- **A program that queries only the declared guarantees is invariant under
every guarantee-preserving scope change.** -/
theorem program_invariant {guarantees : Scope → Guarantee} {program : Scope → Out}
    (queriesGuarantees : Factors guarantees program) (change : Scope → Scope)
    (preserves : ∀ scope, guarantees (change scope) = guarantees scope) (scope : Scope) :
    program (change scope) = program scope :=
  queriesGuarantees.constantOnFibers _ _ (preserves scope)

end Programs

namespace Representation

/-- A scope with a declared guarantee and an undeclared representation
detail. -/
structure Setup where
  /-- The declared guarantee. -/
  guarantee : Bool
  /-- An undeclared representation detail. -/
  layout : ℕ

/-- Change the representation, keep the guarantee. -/
def relayout (scope : Setup) : Setup :=
  { scope with layout := scope.layout + 1 }

/-- **Positive**: a program reading the guarantee is invariant. -/
theorem guarantee_program_invariant (scope : Setup) :
    (relayout scope).guarantee = scope.guarantee :=
  program_invariant (guarantees := Setup.guarantee) (program := Setup.guarantee)
    ⟨id, fun _ => rfl⟩
    relayout (fun _ => rfl) scope

/-- **Control**: a program reading the layout changes. -/
theorem not_invariant : (relayout ⟨true, 0⟩).layout ≠ (⟨true, 0⟩ : Setup).layout := by
  decide

/-- It does not factor through the guarantees. -/
theorem not_factors : ¬ Factors Setup.guarantee Setup.layout :=
  NonTrivialFiber.not_factors ⟨⟨true, 0⟩, ⟨true, 1⟩, rfl, by decide⟩

end Representation

end Mettapedia.GSLT.Scope
