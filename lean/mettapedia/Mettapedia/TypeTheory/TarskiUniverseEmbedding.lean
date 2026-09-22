import Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
import Mettapedia.TypeTheory.UniverseClosureProfiles

/-!
# Cross-level universe coding in a Tarski family

Lifting codes preserves already represented types. Interpreting universe
formation needs more: the upper universe must also code the lower code
carrier itself. The existing `UniverseEmbedding` records both requirements.

This module applies that interface to level-indexed families. The concrete
two-level set-family hierarchy has exactly the lower-to-upper embedding; it
cannot interpret two consecutive universe-formation steps within its fixed
two levels. This is a boundary of that semantic model, not a proposed ceiling
on a dependent calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TarskiUniverseEmbedding

open TarskiUniverseCapabilities UniverseClosureProfiles
open CwfTarskiUniverseHierarchy

universe uLevel uCode uEl u

/-- A level of the existing code family as the existing semantic-universe
interface. This exposes the same codes and decoding, without new closure. -/
def universeAt (family : TarskiCodeFamily.{uLevel, uCode, uEl})
    (level : family.Level) : SemanticTarskiUniverse.{uCode, uEl} where
  Code := family.Code level
  El := family.El level

/-- Universe embeddings compose by lifting the middle code for the lower
code carrier, as well as each decoded lower type. -/
def compose {family : TarskiCodeFamily.{uLevel, u, u}}
    {lower middle upper : family.Level}
    (first : UniverseEmbedding (universeAt family middle) (universeAt family lower))
    (second : UniverseEmbedding (universeAt family upper) (universeAt family middle)) :
    UniverseEmbedding (universeAt family upper) (universeAt family lower) where
  codeCarrier := second.decodedType first.codeCarrier
  decodeCodeCarrier := (second.decodeDecodedType first.codeCarrier).trans first.decodeCodeCarrier
  decodedType code := second.decodedType (first.decodedType code)
  decodeDecodedType code :=
    (second.decodeDecodedType (first.decodedType code)).trans (first.decodeDecodedType code)

/-- Every finite-rank code carrier has an actual code one rank above it.
This is a formation control, not product closure or a dependent model. -/
def finiteRankSuccessor (level : Nat) :
    UniverseEmbedding (universeAt FiniteRank.family (level + 1))
      (universeAt FiniteRank.family level) where
  codeCarrier := ⟨level, Nat.lt_succ_self level⟩
  decodeCodeCarrier := Equiv.refl _
  decodedType code := FiniteRank.cumulative.lift (Nat.lt_succ_self level) code
  decodeDecodedType code := FiniteRank.cumulative.decodeLift (Nat.lt_succ_self level) code

/-- Coding a level inside itself contradicts the family's stated semantic
rank separation. The contradiction uses the actual code-carrier component. -/
theorem no_self_embedding (family : TarskiCodeFamily.{uLevel, u, u})
    (predicative : family.PredicativeRanks) (level : family.Level) :
    ¬ Nonempty (UniverseEmbedding (universeAt family level) (universeAt family level)) := by
  rintro ⟨embedding⟩
  exact predicative level ⟨embedding.codeCarrier, ⟨embedding.decodeCodeCarrier⟩⟩

/-- A cumulative edge cannot be reversed by a universe embedding: lifting
the purported code for the upper code carrier would make it self-coded. -/
theorem no_reverse_embedding (family : TarskiCodeFamily.{uLevel, u, u})
    (predicative : family.PredicativeRanks)
    {Below : family.Level → family.Level → Prop}
    (cumulative : family.Cumulative Below)
    {lower upper : family.Level} (below : Below lower upper) :
    ¬ Nonempty (UniverseEmbedding (universeAt family lower) (universeAt family upper)) := by
  rintro ⟨embedding⟩
  exact predicative upper
    ⟨cumulative.lift below embedding.codeCarrier,
      ⟨(cumulative.decodeLift below embedding.codeCarrier).trans embedding.decodeCodeCarrier⟩⟩

namespace TwoLevel

open TwoLevelSetFamilies

universe small

/-- The upper set universe codes the actual lower code carrier and lifts
every lower code with unchanged decoding. Neither carrier is replaced. -/
def lowerIntoUpper :
    UniverseEmbedding
      (universeAt externalFamily.{small} true)
      (universeAt externalFamily.{small} false) where
  codeCarrier := ⟨Type small⟩
  decodeCodeCarrier := Equiv.refl _
  decodedType code := externalCumulative.lift ⟨rfl, rfl⟩ code
  decodeDecodedType code := externalCumulative.decodeLift ⟨rfl, rfl⟩ code

/-- Both successful directions and exclusions are about the concrete
set-family codes, not just an order relation on two labels. -/
theorem embedding_iff (lower upper : Bool) :
    Nonempty (UniverseEmbedding
      (universeAt externalFamily.{small} upper)
      (universeAt externalFamily.{small} lower)) ↔
      lower = false ∧ upper = true := by
  cases lower <;> cases upper
  · constructor
    · exact fun embedding => (no_self_embedding _ predicativeRanks false embedding).elim
    · intro impossible
      cases impossible.2
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨lowerIntoUpper⟩⟩
  · constructor
    · exact fun embedding =>
        (no_reverse_embedding _ predicativeRanks externalCumulative ⟨rfl, rfl⟩ embedding).elim
    · intro impossible
      cases impossible.1
  · constructor
    · exact fun embedding => (no_self_embedding _ predicativeRanks true embedding).elim
    · intro impossible
      cases impossible.1

/-- One universe-formation step exists, but a second consecutive step
cannot remain within these same two semantic levels. -/
theorem no_two_successive_embeddings (first middle last : Bool) :
    ¬ (Nonempty (UniverseEmbedding
        (universeAt externalFamily.{small} middle)
        (universeAt externalFamily.{small} first)) ∧
      Nonempty (UniverseEmbedding
        (universeAt externalFamily.{small} last)
        (universeAt externalFamily.{small} middle))) := by
  rintro ⟨earlier, later⟩
  have middleTrue := ((embedding_iff first middle).mp earlier).2
  have middleFalse := ((embedding_iff middle last).mp later).1
  exact Bool.false_ne_true (middleFalse.symm.trans middleTrue)

end TwoLevel

#print axioms no_self_embedding
#print axioms compose
#print axioms finiteRankSuccessor
#print axioms no_reverse_embedding
#print axioms TwoLevel.lowerIntoUpper
#print axioms TwoLevel.embedding_iff
#print axioms TwoLevel.no_two_successive_embeddings

end Mettapedia.TypeTheory.TarskiUniverseEmbedding
