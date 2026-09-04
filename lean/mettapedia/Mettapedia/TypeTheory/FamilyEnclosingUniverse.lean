import Mettapedia.TypeTheory.TarskiUniverseCapabilities
import Mathlib.Logic.Small.Basic

/-!
# Family-enclosing Tarski universes

A family-enclosing universe contains a named dependent family and is closed
under a declared collection of ordinary intensional type formers.  This is the
type-theoretic shape of a universe-above-family operation: it does not identify
the resulting codes with sets, assert a Grothendieck-universe axiom, or choose
rules for a concrete dependent calculus.

The ambient type model proves that the interface is jointly satisfiable.  Its
codes are all types in one predicative ambient level, so it is a semantic model
of the capability rather than an inductive-recursive syntax for generated
universes.  The paired negative theorem proves that this code carrier cannot
itself be represented at the same level.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FamilyEnclosingUniverse

open Mettapedia.TypeTheory.TarskiUniverseCapabilities

universe uCode u

/-- Ordinary well-founded trees, used to state W-type closure independently of
any particular dependent type theory syntax. -/
inductive WTree (Shape : Type u) (Position : Shape → Type u) : Type u where
  | sup (shape : Shape) (children : Position shape → WTree Shape Position) :
      WTree Shape Position

/-- A Tarski universe which contains a selected dependent family and is closed
under a useful predicative collection of type formers.  Every decoding law is
an equivalence rather than an equality so the interface does not install
equality reflection or a conversion policy. -/
structure ClosedTarskiUniverseOver (A : Type u) (B : A → Type u) where
  Code : Type uCode
  El : Code → Type u
  baseCode : Code
  elBase : El baseCode ≃ A
  fibreCode : A → Code
  elFibre : ∀ index, El (fibreCode index) ≃ B index
  emptyCode : Code
  elEmpty : El emptyCode ≃ Empty
  unitCode : Code
  elUnit : El unitCode ≃ PUnit.{1}
  natCode : Code
  elNat : El natCode ≃ Nat
  sumCode : Code → Code → Code
  elSum : ∀ left right,
    El (sumCode left right) ≃ Sum (El left) (El right)
  piCode : (domain : Code) → (El domain → Code) → Code
  elPi : ∀ domain codomain,
    El (piCode domain codomain) ≃
      ((argument : El domain) → El (codomain argument))
  sigmaCode : (domain : Code) → (El domain → Code) → Code
  elSigma : ∀ domain codomain,
    El (sigmaCode domain codomain) ≃
      (Σ argument : El domain, El (codomain argument))
  identityCode : (domain : Code) → El domain → El domain → Code
  elIdentity : ∀ domain left right,
    El (identityCode domain left right) ≃ (left = right)
  wCode : (shape : Code) → (El shape → Code) → Code
  elW : ∀ shape position,
    El (wCode shape position) ≃
      WTree (El shape) (fun value => El (position value))

namespace ClosedTarskiUniverseOver

variable {A : Type u} {B : A → Type u}

/-- Forget the selected family and expose a one-level semantic Tarski code
family. -/
def toCodeFamily (envelope : ClosedTarskiUniverseOver.{uCode, u} A B) :
    TarskiCodeFamily.{0, uCode, u} where
  Level := PUnit
  Code := fun _ => envelope.Code
  El := fun _ => envelope.El

/-- The exposed one-level family has dependent-product closure. -/
theorem piClosedAt (envelope : ClosedTarskiUniverseOver.{uCode, u} A B) :
    envelope.toCodeFamily.PiClosedAt PUnit.unit := by
  intro domain codomain
  exact ⟨envelope.piCode domain codomain,
    ⟨envelope.elPi domain codomain⟩⟩

/-- The exposed one-level family has dependent-sum closure. -/
theorem sigmaClosedAt (envelope : ClosedTarskiUniverseOver.{uCode, u} A B) :
    envelope.toCodeFamily.SigmaClosedAt PUnit.unit := by
  intro domain codomain
  exact ⟨envelope.sigmaCode domain codomain,
    ⟨envelope.elSigma domain codomain⟩⟩

end ClosedTarskiUniverseOver

/-- A uniform universe-above-family operation at one predicative size.  Its
output may depend on the entire family.  No minimality, initiality, semantic
self-code, or closure under universe formation is implicit. -/
structure FamilyEnclosingUniverseOperator where
  enclose : (A : Type u) → (B : A → Type u) →
    ClosedTarskiUniverseOver.{u + 1, u} A B

/-! ## The ambient predicative semantic model -/

/-- The ambient type universe encloses any family in its level and is closed
under the selected type formers.  This is a semantic compatibility model, not
an inductive-recursive construction of a smaller generated code language. -/
def ambientEnvelope (A : Type u) (B : A → Type u) :
    ClosedTarskiUniverseOver.{u + 1, u} A B where
  Code := Type u
  El := id
  baseCode := A
  elBase := Equiv.refl A
  fibreCode := B
  elFibre := fun index => Equiv.refl (B index)
  emptyCode := ULift.{u, 0} Empty
  elEmpty := Equiv.ulift
  unitCode := ULift.{u, 0} PUnit
  elUnit := Equiv.ulift
  natCode := ULift.{u, 0} Nat
  elNat := Equiv.ulift
  sumCode := Sum
  elSum := fun left right => Equiv.refl (Sum left right)
  piCode := fun domain codomain =>
    (argument : domain) → codomain argument
  elPi := fun domain codomain =>
    Equiv.refl ((argument : domain) → codomain argument)
  sigmaCode := fun domain codomain =>
    Σ argument : domain, codomain argument
  elSigma := fun domain codomain =>
    Equiv.refl (Σ argument : domain, codomain argument)
  identityCode := fun _domain left right =>
    ULift.{u, 0} (PLift (left = right))
  elIdentity := fun _domain _left _right =>
    Equiv.ulift.trans Equiv.plift
  wCode := fun shape position => WTree shape position
  elW := fun shape position => Equiv.refl (WTree shape position)

/-- The ambient semantic universe supplies one uniform family-enclosing
operator. -/
def ambientOperator : FamilyEnclosingUniverseOperator.{u} where
  enclose := ambientEnvelope

/-- The ambient semantic family has both dependent-product and dependent-sum
closure through the common capability interface. -/
theorem ambient_closure (A : Type u) (B : A → Type u) :
    let envelope := ambientEnvelope A B
    envelope.toCodeFamily.PiClosedAt PUnit.unit ∧
      envelope.toCodeFamily.SigmaClosedAt PUnit.unit :=
  ⟨(ambientEnvelope A B).piClosedAt,
    (ambientEnvelope A B).sigmaClosedAt⟩

/-- Negative canary: the ambient code carrier `Type u` cannot itself be coded
at the same universe level.  Moving to a larger level is a real predicative
boundary, not notation. -/
theorem no_sameLevel_ambient_selfCode :
    ¬ ∃ code : Type u, Nonempty (code ≃ Type u) := by
  rintro ⟨code, ⟨equivalence⟩⟩
  exact not_small_type (Small.mk' equivalence.symm)

/-- Consequently the one-level ambient family is predicatively ranked. -/
theorem ambient_predicativeRanks (A : Type u) (B : A → Type u) :
    (ambientEnvelope A B).toCodeFamily.PredicativeRanks := by
  intro level selfCode
  cases level
  change ∃ code : Type u, Nonempty (code ≃ Type u) at selfCode
  exact no_sameLevel_ambient_selfCode selfCode

/-! ## A nonconstant dependent-family control -/

/-- A small family whose fibres genuinely vary. -/
def varyingFamily : Bool → Type
  | false => PUnit
  | true => Bool

/-- The uniform operator encloses a genuinely varying family, not only a
constant-family or simple-type fragment. -/
def varyingEnvelope : ClosedTarskiUniverseOver Bool varyingFamily :=
  ambientOperator.enclose Bool varyingFamily

theorem varyingEnvelope_fibres_distinct :
    ¬ Nonempty
      ((varyingEnvelope.El (varyingEnvelope.fibreCode false)) ≃
        varyingEnvelope.El (varyingEnvelope.fibreCode true)) := by
  simp only [varyingEnvelope, ambientOperator, ambientEnvelope, varyingFamily]
  change ¬ Nonempty (PUnit ≃ Bool)
  rintro ⟨equivalence⟩
  have cardinality := Fintype.card_congr equivalence
  simp at cardinality

#print axioms ClosedTarskiUniverseOver.piClosedAt
#print axioms ClosedTarskiUniverseOver.sigmaClosedAt
#print axioms ambient_closure
#print axioms no_sameLevel_ambient_selfCode
#print axioms ambient_predicativeRanks
#print axioms varyingEnvelope_fibres_distinct

end Mettapedia.TypeTheory.FamilyEnclosingUniverse
