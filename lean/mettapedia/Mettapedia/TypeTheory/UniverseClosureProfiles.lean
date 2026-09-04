import Mettapedia.TypeTheory.FamilyEnclosingUniverse
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Closure profiles for type-theoretic universes

This module separates three increasingly demanding universe capabilities.

* A family-enclosing operator returns one closed Tarski universe above a
  selected dependent family.
* A superuniverse embeds, inside one outer universe, every universe produced
  by a selected small family-enclosing operator.
* A Mahlo reflection profile contains an ordinary subuniverse closed under
  every internal family operator.

The last two are capability interfaces, not new kernel rules and not existence
claims.  The ambient type hierarchy gives a positive semantic embedding one
level up.  A finite-code control proves that ordinary universe data alone does
not imply reflection under arbitrary family operators.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseClosureProfiles

open Mettapedia.TypeTheory.FamilyEnclosingUniverse

universe uOuter u

/-! ## Tarski universes and internal families -/

/-- The data common to the universe-closure comparisons: codes and decoding.
No closure, cumulativity, or self-code property is implicit. -/
structure SemanticTarskiUniverse where
  Code : Type uOuter
  El : Code → Type u

/-- Forget the selected family and closure operations of a closed envelope. -/
def semanticUniverseOfEnvelope
    {A : Type u} {B : A → Type u}
    (envelope : ClosedTarskiUniverseOver.{uOuter, u} A B) :
    SemanticTarskiUniverse.{uOuter, u} where
  Code := envelope.Code
  El := envelope.El

namespace SemanticTarskiUniverse

variable (outer : SemanticTarskiUniverse.{uOuter, u})

/-- A family represented inside a Tarski universe.  Its first code decodes to
the index type; its second component assigns a code to each index. -/
abbrev InternalFamily :=
  Σ base : outer.Code, outer.El base → outer.Code

/-- Inclusion of one internally represented family in another.  Codes embed,
while the types decoded at corresponding codes remain equivalent. -/
structure InternalFamilyEmbedding
    (small large : outer.InternalFamily) where
  onBase : outer.El small.1 ↪ outer.El large.1
  onFibre : ∀ index,
    outer.El (small.2 index) ≃ outer.El (large.2 (onBase index))

namespace InternalFamilyEmbedding

variable {outer : SemanticTarskiUniverse.{uOuter, u}}
variable {first middle last : outer.InternalFamily}

/-- Every internal family embeds in itself. -/
def refl (family : outer.InternalFamily) :
    outer.InternalFamilyEmbedding family family where
  onBase := Function.Embedding.refl _
  onFibre := fun _ => Equiv.refl _

/-- Internal-family embeddings compose. -/
def trans
    (left : outer.InternalFamilyEmbedding first middle)
    (right : outer.InternalFamilyEmbedding middle last) :
    outer.InternalFamilyEmbedding first last where
  onBase := left.onBase.trans right.onBase
  onFibre := fun index =>
    (left.onFibre index).trans (right.onFibre (left.onBase index))

end InternalFamilyEmbedding

/-- An operator on families represented inside one universe. -/
abbrev FamilyOperator := outer.InternalFamily → outer.InternalFamily

/-- An internal family is closed under an operator when the operator's output
embeds back into the family. -/
def ClosedUnder (operator : outer.FamilyOperator)
    (family : outer.InternalFamily) : Prop :=
  Nonempty (outer.InternalFamilyEmbedding (operator family) family)

/-- A family operator that transports internal-family embeddings.  Functor
identity and composition laws are not needed for the finite-iteration theorem,
so this structure records exactly the monotonicity used there. -/
structure MonotoneFamilyOperator where
  onFamily : outer.FamilyOperator
  mapEmbedding : ∀ {small large},
    outer.InternalFamilyEmbedding small large →
      outer.InternalFamilyEmbedding (onFamily small) (onFamily large)

namespace MonotoneFamilyOperator

variable {outer : SemanticTarskiUniverse.{uOuter, u}}

/-- Finite iteration of an internal family operator. -/
def iterate (operator : outer.MonotoneFamilyOperator) :
    Nat → outer.InternalFamily → outer.InternalFamily
  | 0, family => family
  | n + 1, family => operator.onFamily (operator.iterate n family)

/-- Closure under one monotone family operator contains every finite iterate
of that operator. -/
theorem iterate_embeds_of_closed
    (operator : outer.MonotoneFamilyOperator)
    {family : outer.InternalFamily}
    (closed : outer.ClosedUnder operator.onFamily family) :
    ∀ n, Nonempty
      (outer.InternalFamilyEmbedding (operator.iterate n family) family) := by
  intro n
  induction n with
  | zero =>
      exact ⟨InternalFamilyEmbedding.refl family⟩
  | succ n inductionHypothesis =>
      rcases inductionHypothesis with ⟨earlier⟩
      rcases closed with ⟨oneStep⟩
      exact ⟨(operator.mapEmbedding earlier).trans oneStep⟩

end MonotoneFamilyOperator

end SemanticTarskiUniverse

/-! ## Universe embeddings and superuniverse closure -/

/-- Embedding of a small inner Tarski universe inside an outer one.  The
outer universe codes both the inner code carrier and every decoded inner type.
This is embedding data, not an assertion that the two universes are
definitionally identical. -/
structure UniverseEmbedding
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (inner : SemanticTarskiUniverse.{u, u}) where
  codeCarrier : outer.Code
  decodeCodeCarrier : outer.El codeCarrier ≃ inner.Code
  decodedType : inner.Code → outer.Code
  decodeDecodedType : ∀ code,
    outer.El (decodedType code) ≃ inner.El code

/-- A universe-forming operation whose generated code carrier remains small at
the same object-language size.  This is the capability required before a
native superuniverse can internalize its outputs.  The ambient semantic
operator from `FamilyEnclosingUniverse` deliberately has a larger code
carrier, so it is not an inhabitant of this interface. -/
structure SmallFamilyEnclosingUniverseOperator where
  enclose : (A : Type u) → (B : A → Type u) →
    ClosedTarskiUniverseOver.{u, u} A B

/-- An outer universe has the superuniverse closure property for a selected
small universe operator when it embeds the generated universe for every
family already represented inside it. -/
def SuperuniverseFor
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (operator : SmallFamilyEnclosingUniverseOperator.{u}) : Prop :=
  ∀ family : outer.InternalFamily,
    Nonempty
      (UniverseEmbedding outer
        (semanticUniverseOfEnvelope (operator.enclose
          (outer.El family.1)
          (fun index => outer.El (family.2 index)))))

/-! ## Mahlo reflection -/

/-- A selected operator has a reflected subuniverse when some ordinary
subuniverse inside the outer universe is closed under that operator. -/
def HasOperatorClosedSubuniverse
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (IsOrdinarySubuniverse : outer.InternalFamily → Prop)
    (operator : outer.FamilyOperator) : Prop :=
  ∃ subuniverse : outer.InternalFamily,
    IsOrdinarySubuniverse subuniverse ∧
      outer.ClosedUnder operator subuniverse

/-- The structural content of a Mahlo universe: every internal family operator
has an ordinary subuniverse reflected inside the outer universe and closed
under that operator.  Which internal families count as ordinary universes is a
separate, explicit parameter. -/
structure MahloReflection
    (outer : SemanticTarskiUniverse.{uOuter, u})
    (IsOrdinarySubuniverse : outer.InternalFamily → Prop) : Prop where
  reflect : ∀ operator : outer.FamilyOperator,
    HasOperatorClosedSubuniverse outer IsOrdinarySubuniverse operator

/-- Mahlo reflection supplies, in particular, a superuniverse-shaped witness
for every selected next-universe operator. -/
theorem MahloReflection.hasOperatorClosedSubuniverse
    {outer : SemanticTarskiUniverse.{uOuter, u}}
    {IsOrdinarySubuniverse : outer.InternalFamily → Prop}
    (mahlo : MahloReflection outer IsOrdinarySubuniverse)
    (operator : outer.FamilyOperator) :
    HasOperatorClosedSubuniverse outer IsOrdinarySubuniverse operator :=
  mahlo.reflect operator

/-! ## A positive one-level-up semantic host -/

/-- The ambient type hierarchy regarded only as an extensional embedding
host.  Its code carrier lives one level above the types it decodes. -/
def ambientUniverse : SemanticTarskiUniverse.{u + 1, u} where
  Code := Type u
  El := id

/-- The ambient host embeds every small Tarski universe. -/
def ambientEmbedding
    (inner : SemanticTarskiUniverse.{u, u}) :
    UniverseEmbedding ambientUniverse inner where
  codeCarrier := inner.Code
  decodeCodeCarrier := Equiv.refl inner.Code
  decodedType := inner.El
  decodeDecodedType := fun code => Equiv.refl (inner.El code)

/-- Consequently the one-level-up ambient host satisfies the embedding part
of superuniverse closure for any already-supplied small universe operator. -/
theorem ambient_superuniverseFor
    (operator : SmallFamilyEnclosingUniverseOperator.{u}) :
    SuperuniverseFor ambientUniverse operator := by
  intro family
  exact ⟨ambientEmbedding _⟩

/-- Negative control: the positive ambient embedding host really uses a
level shift.  Its code carrier cannot be represented by a type at the same
decoded level. -/
theorem ambient_embedding_requires_level_shift :
    ¬ ∃ code : Type u,
      Nonempty (code ≃ Type u) :=
  no_sameLevel_ambient_selfCode

/-! ## Finite controls: selected closure is not Mahlo reflection -/

namespace Canary

/-- A small Tarski universe whose code `n` decodes to `Fin n`. -/
abbrev finiteUniverse : SemanticTarskiUniverse.{0, 0} where
  Code := Nat
  El := Fin

/-- A finite internal family with `n` base codes and singleton fibres. -/
def constantSingletonFamily (n : Nat) : finiteUniverse.InternalFamily :=
  ⟨n, fun _ => (1 : Nat)⟩

/-- The identity family operator, used only as a positive closure control. -/
def identityOperator : finiteUniverse.MonotoneFamilyOperator where
  onFamily := id
  mapEmbedding := fun embedding => embedding

theorem identityOperator_closed (n : Nat) :
    finiteUniverse.ClosedUnder identityOperator.onFamily
      (constantSingletonFamily n) :=
  ⟨SemanticTarskiUniverse.InternalFamilyEmbedding.refl _⟩

theorem identityOperator_all_iterates (n iterations : Nat) :
    Nonempty
      (finiteUniverse.InternalFamilyEmbedding
        (identityOperator.iterate iterations (constantSingletonFamily n))
        (constantSingletonFamily n)) :=
  identityOperator.iterate_embeds_of_closed (identityOperator_closed n) iterations

/-- A strict-growth family operator.  It adds one base code while retaining
singleton decoded fibres. -/
def successorOperator : finiteUniverse.FamilyOperator
  | ⟨base, _fibre⟩ => constantSingletonFamily (base + 1)

/-- No finite internal family is closed under strict base growth. -/
theorem successorOperator_not_closed
    (family : finiteUniverse.InternalFamily) :
    ¬ finiteUniverse.ClosedUnder successorOperator family := by
  rcases family with ⟨base, fibre⟩
  rintro ⟨embedding⟩
  have cardinality :=
    Nat.card_le_card_of_injective embedding.onBase embedding.onBase.injective
  change Nat.card (Fin (base + 1)) ≤ Nat.card (Fin base) at cardinality
  simp only [Nat.card_fin] at cardinality
  exact Nat.not_succ_le_self base cardinality

/-- An ordinary finite code universe can support selected closure while still
failing Mahlo reflection.  Thus ordinary universe structure does not imply the
arbitrary-operator reflection principle. -/
theorem finiteUniverse_not_mahlo :
    ¬ MahloReflection finiteUniverse (fun _ => True) := by
  intro mahlo
  rcases mahlo.reflect successorOperator with
    ⟨subuniverse, _ordinary, closed⟩
  exact successorOperator_not_closed subuniverse closed

end Canary

#print axioms SemanticTarskiUniverse.MonotoneFamilyOperator.iterate_embeds_of_closed
#print axioms MahloReflection.hasOperatorClosedSubuniverse
#print axioms ambient_superuniverseFor
#print axioms ambient_embedding_requires_level_shift
#print axioms Canary.identityOperator_all_iterates
#print axioms Canary.successorOperator_not_closed
#print axioms Canary.finiteUniverse_not_mahlo

end Mettapedia.TypeTheory.UniverseClosureProfiles
