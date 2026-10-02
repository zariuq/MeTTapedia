import Mettapedia.TypeTheory.TarskiUniverseEmbedding
import Mettapedia.TypeTheory.UniverseLevel.Order

/-!
# A conditional tower of family-enclosing universes

An independently supplied small family-enclosing operator can be iterated:
its next application encloses the preceding code carrier and decoding family.
The resulting Nat-indexed Tarski family has actual successor universe
embeddings and dependent product, sum, and identity codes at every level.

This is a conditional construction, not an existence theorem for that
operator. The small operator returns both codes and decoded types in Type u.
The ambient operator instead has codes in Type (u+1), so it cannot be silently
used for this same-level recursion. No predicative-rank theorem, injectivity of
code lifts, or strict commutation of lifts with type formers is assumed.

Canonical non-strict code lifts use the existing Nat.leRecOn paths and satisfy
identity/composition equations. Decoding is preserved by equivalences, not
definitional equality. Native syntax, level substitution, and contextual
formation rules are downstream interfaces, not supplied by this construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FamilyEnclosingUniverseTower

open FamilyEnclosingUniverse UniverseClosureProfiles TarskiUniverseCapabilities
open TarskiUniverseEmbedding

universe u

/-- The initial family is followed by the actual Code/El pairs produced by
successive enclosing operations. Smallness makes the recursive input legal. -/
def inputFamily (operator : SmallFamilyEnclosingUniverseOperator.{u})
    (A : Type u) (B : A → Type u) : Nat → SemanticTarskiUniverse.{u, u}
  | 0 => ⟨A, B⟩
  | level + 1 =>
      let previous := inputFamily operator A B level
      semanticUniverseOfEnvelope (operator.enclose previous.Code previous.El)

/-- Stage zero encloses the supplied family; each later stage encloses the
preceding stage's actual universe, with all the operator's closure data. -/
def envelope (operator : SmallFamilyEnclosingUniverseOperator.{u})
    (A : Type u) (B : A → Type u) (level : Nat) :
    ClosedTarskiUniverseOver.{u, u}
      (inputFamily operator A B level).Code (inputFamily operator A B level).El :=
  operator.enclose (inputFamily operator A B level).Code (inputFamily operator A B level).El

/-- The existing Tarski code-family interface, with no finite level ceiling. -/
def family (operator : SmallFamilyEnclosingUniverseOperator.{u})
    (A : Type u) (B : A → Type u) : TarskiCodeFamily.{0, u, u} where
  Level := Nat
  Code level := (envelope operator A B level).Code
  El level := (envelope operator A B level).El

variable (operator : SmallFamilyEnclosingUniverseOperator.{u})
variable (A : Type u) (B : A → Type u)

/-- The levels of the family are the natural numbers, as a level order. -/
instance : UniverseLevel.LevelOrder (family operator A B).Level :=
  inferInstanceAs (UniverseLevel.LevelOrder Nat)

/-- The first universe contains the initial family's base type. -/
def initialBaseCode : (family operator A B).Code (0 : Nat) :=
  (envelope operator A B 0).baseCode

def decodeInitialBase :
    (family operator A B).El (0 : Nat) (initialBaseCode operator A B) ≃ A :=
  (envelope operator A B 0).elBase

def initialFibreCode (index : A) : (family operator A B).Code (0 : Nat) :=
  (envelope operator A B 0).fibreCode index

def decodeInitialFibre (index : A) :
    (family operator A B).El (0 : Nat) (initialFibreCode operator A B index) ≃ B index :=
  (envelope operator A B 0).elFibre index

/-! ## Actual closure operations at every level -/

def piCode (level : Nat) (domain : (family operator A B).Code level)
    (codomain : (family operator A B).El level domain → (family operator A B).Code level) :
    (family operator A B).Code level :=
  (envelope operator A B level).piCode domain codomain

def decodePi (level : Nat) (domain : (family operator A B).Code level)
    (codomain : (family operator A B).El level domain → (family operator A B).Code level) :
    (family operator A B).El level (piCode operator A B level domain codomain) ≃
      ((argument : (family operator A B).El level domain) →
        (family operator A B).El level (codomain argument)) :=
  (envelope operator A B level).elPi domain codomain

def sigmaCode (level : Nat) (domain : (family operator A B).Code level)
    (codomain : (family operator A B).El level domain → (family operator A B).Code level) :
    (family operator A B).Code level :=
  (envelope operator A B level).sigmaCode domain codomain

def decodeSigma (level : Nat) (domain : (family operator A B).Code level)
    (codomain : (family operator A B).El level domain → (family operator A B).Code level) :
    (family operator A B).El level (sigmaCode operator A B level domain codomain) ≃
      (Σ argument : (family operator A B).El level domain,
        (family operator A B).El level (codomain argument)) :=
  (envelope operator A B level).elSigma domain codomain

def identityCode (level : Nat) (domain : (family operator A B).Code level)
    (left right : (family operator A B).El level domain) : (family operator A B).Code level :=
  (envelope operator A B level).identityCode domain left right

def decodeIdentity (level : Nat) (domain : (family operator A B).Code level)
    (left right : (family operator A B).El level domain) :
    (family operator A B).El level (identityCode operator A B level domain left right) ≃
      (left = right) :=
  (envelope operator A B level).elIdentity domain left right

theorem piClosed : (family operator A B).PiClosed :=
  fun level domain codomain =>
    ⟨piCode operator A B level domain codomain, ⟨decodePi operator A B level domain codomain⟩⟩

theorem sigmaClosed : (family operator A B).SigmaClosed :=
  fun level domain codomain =>
    ⟨sigmaCode operator A B level domain codomain, ⟨decodeSigma operator A B level domain codomain⟩⟩

theorem identityClosed (level : Nat) (domain : (family operator A B).Code level)
    (left right : (family operator A B).El level domain) :
    ∃ code : (family operator A B).Code level,
      Nonempty ((family operator A B).El level code ≃ (left = right)) :=
  ⟨identityCode operator A B level domain left right,
    ⟨decodeIdentity operator A B level domain left right⟩⟩

/-! ## Universe formation and canonical cumulative paths -/

/-- The upper base code decodes to the lower code carrier itself. Its fibre
codes decode to the lower represented types. Neither component is inferred
from mere preservation of already decoded types. -/
def successorEmbedding (level : Nat) :
    UniverseEmbedding (universeAt (family operator A B) (level + 1))
      (universeAt (family operator A B) level) where
  codeCarrier := (envelope operator A B (level + 1)).baseCode
  decodeCodeCarrier := (envelope operator A B (level + 1)).elBase
  decodedType := (envelope operator A B (level + 1)).fibreCode
  decodeDecodedType := (envelope operator A B (level + 1)).elFibre

/-- Non-strict lifting uses the unique increasing Nat path: the empty path
is identity, and each edge is the actual next envelope's fibre-code map. -/
def liftCode {lower upper : Nat} (below : lower ≤ upper)
    (code : (family operator A B).Code lower) : (family operator A B).Code upper :=
  Nat.leRecOn below (fun {level} => (successorEmbedding operator A B level).decodedType) code

@[simp] theorem liftCode_refl (level : Nat) (code : (family operator A B).Code level) :
    liftCode operator A B (Nat.le_refl level) code = code :=
  Nat.leRecOn_self code

theorem liftCode_succ {lower upper : Nat} (below : lower ≤ upper)
    (code : (family operator A B).Code lower) :
    liftCode operator A B (Nat.le_succ_of_le below) code =
      (successorEmbedding operator A B upper).decodedType (liftCode operator A B below code) :=
  Nat.leRecOn_succ below code

@[simp] theorem liftCode_successor (level : Nat) (code : (family operator A B).Code level) :
    liftCode operator A B (Nat.le_succ level) code =
      (successorEmbedding operator A B level).decodedType code :=
  Nat.leRecOn_succ' code

/-- This is equality of the actual iterated code maps, not only equivalence of
their decodings. It makes no claim about commuting lifts with Pi or Id codes. -/
theorem liftCode_trans {lower middle upper : Nat}
    (first : lower ≤ middle) (second : middle ≤ upper) (code : (family operator A B).Code lower) :
    liftCode operator A B (first.trans second) code =
      liftCode operator A B second (liftCode operator A B first code) :=
  Nat.leRecOn_trans first second code

/-- Decode a canonical lift by composing the actual successor equivalences. -/
def decodeLift {lower upper : Nat} (below : lower ≤ upper)
    (code : (family operator A B).Code lower) :
    (family operator A B).El upper (liftCode operator A B below code) ≃
      (family operator A B).El lower code := by
  induction below using Nat.leRec with
  | refl =>
      rw [liftCode_refl]
  | @le_succ_of_le upper below previous =>
      rw [liftCode_succ]
      exact ((successorEmbedding operator A B upper).decodeDecodedType
        (liftCode operator A B below code)).trans previous

/-- The existing cumulativity interface, now also allowing reflexive edges. -/
def cumulative : (family operator A B).Cumulative Nat.le where
  lift := liftCode operator A B
  decodeLift := decodeLift operator A B

/-- Every strictly higher level contains the lower universe. This composition
uses the existing universe-embedding operation, including its code-carrier
component, not just a composite decoded-type lift. -/
def embedding {lower upper : Nat} (below : lower < upper) :
    UniverseEmbedding (universeAt (family operator A B) upper)
      (universeAt (family operator A B) lower) :=
  Nat.leRecOn (show lower + 1 ≤ upper from below)
    (fun {level} earlier => TarskiUniverseEmbedding.compose earlier
      (successorEmbedding operator A B level))
    (successorEmbedding operator A B lower)

/-- The universe embedding and cumulative paths use the same code lifts. -/
theorem embedding_decodedType {lower upper : Nat} (below : lower < upper)
    (code : (family operator A B).Code lower) :
    (embedding operator A B below).decodedType code =
      liftCode operator A B (Nat.le_of_lt below) code := by
  induction below using Nat.leRec with
  | refl => simp [embedding, Nat.leRecOn_self]
  | @le_succ_of_le upper below previous =>
      rw [embedding, Nat.leRecOn_succ below]
      change (successorEmbedding operator A B upper).decodedType
        ((embedding operator A B below).decodedType code) = _
      rw [previous]
      exact (liftCode_succ operator A B (Nat.le_of_lt below) code).symm

/-- The code for the lower code carrier follows the same canonical path from
its first successor representation to the chosen strictly higher level. -/
theorem embedding_codeCarrier {lower upper : Nat} (below : lower < upper) :
    (embedding operator A B below).codeCarrier =
      liftCode operator A B (show lower + 1 ≤ upper from below)
        (successorEmbedding operator A B lower).codeCarrier := by
  induction below using Nat.leRec with
  | refl =>
      rw [embedding, Nat.leRecOn_self]
      exact (liftCode_refl operator A B (lower + 1)
        (successorEmbedding operator A B lower).codeCarrier).symm
  | @le_succ_of_le upper below previous =>
      rw [embedding, Nat.leRecOn_succ below]
      change (successorEmbedding operator A B upper).decodedType
        ((embedding operator A B below).codeCarrier) = _
      rw [previous]
      exact (liftCode_succ operator A B below
        (successorEmbedding operator A B lower).codeCarrier).symm

/-- Two successive lifts preserve the original decoded type with the actual
composite equivalence. Code-path equality is separately given by liftCode_trans. -/
def decodeComposite {lower middle upper : Nat}
    (first : lower ≤ middle) (second : middle ≤ upper) (code : (family operator A B).Code lower) :
    (family operator A B).El upper
        (liftCode operator A B second (liftCode operator A B first code)) ≃
      (family operator A B).El lower code :=
  (decodeLift operator A B second (liftCode operator A B first code)).trans
    (decodeLift operator A B first code)

/-! ## Conditional nondegeneracy and independent controls -/

/-- Every constructed stage distinguishes its actual empty and natural-number
codes. A one-code or empty decoder cannot satisfy the supplied interface. -/
theorem emptyCode_ne_natCode (level : Nat) :
    (envelope operator A B level).emptyCode ≠ (envelope operator A B level).natCode := by
  intro equal
  have natural : (envelope operator A B level).El (envelope operator A B level).natCode :=
    (envelope operator A B level).elNat.symm 0
  have empty : (envelope operator A B level).El (envelope operator A B level).emptyCode :=
    equal.symm ▸ natural
  exact Empty.elim ((envelope operator A B level).elEmpty empty)

/-- All formation edges and type-former closures come from the supplied
operator, with the same Code/El family at every occurrence. -/
theorem formation_and_closure :
    (family operator A B).PiClosed ∧ (family operator A B).SigmaClosed ∧
      (∀ (level : Nat) (domain : (family operator A B).Code level)
        (left right : (family operator A B).El level domain),
        ∃ code : (family operator A B).Code level,
        Nonempty ((family operator A B).El level code ≃ (left = right))) ∧
      (∀ level : Nat, Nonempty (UniverseEmbedding
        (universeAt (family operator A B) (level + 1))
        (universeAt (family operator A B) level))) := by
  exact ⟨piClosed operator A B, sigmaClosed operator A B,
    identityClosed operator A B, fun level => ⟨successorEmbedding operator A B level⟩⟩

/-- An actual infinite sequence of formation embeddings alone does not supply
dependent products: the finite-rank model still fails at its concrete level 3. -/
theorem finiteRank_formation_without_products :
    (∀ level, Nonempty (UniverseEmbedding
      (universeAt FiniteRank.family (level + 1)) (universeAt FiniteRank.family level))) ∧
      ¬ FiniteRank.family.PiClosed := by
  exact ⟨fun level => ⟨finiteRankSuccessor level⟩,
    fun closed => FiniteRank.not_piClosedAt_three (closed 3)⟩

/-- The concrete ambient envelope closes a genuinely varying family, but its
large code carrier cannot be identified with a same-level small tower stage. -/
theorem ambient_varying_control :
    varyingEnvelope.toCodeFamily.PiClosedAt PUnit.unit ∧
      varyingEnvelope.toCodeFamily.SigmaClosedAt PUnit.unit ∧
      ¬ Nonempty (varyingEnvelope.El (varyingEnvelope.fibreCode false) ≃
        varyingEnvelope.El (varyingEnvelope.fibreCode true)) ∧
      ¬ ∃ smallCode : Type, Nonempty (smallCode ≃ varyingEnvelope.Code) :=
  ⟨varyingEnvelope.piClosedAt, varyingEnvelope.sigmaClosedAt,
    varyingEnvelope_fibres_distinct, no_sameLevel_ambient_selfCode⟩

#print axioms successorEmbedding
#print axioms piClosed
#print axioms sigmaClosed
#print axioms identityClosed
#print axioms liftCode_refl
#print axioms liftCode_trans
#print axioms decodeLift
#print axioms embedding
#print axioms embedding_decodedType
#print axioms embedding_codeCarrier
#print axioms emptyCode_ne_natCode
#print axioms formation_and_closure
#print axioms finiteRank_formation_without_products
#print axioms ambient_varying_control

end Mettapedia.TypeTheory.FamilyEnclosingUniverseTower
