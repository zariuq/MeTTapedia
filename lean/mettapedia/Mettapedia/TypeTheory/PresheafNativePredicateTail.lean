import Mettapedia.TypeTheory.PresheafNativeStableRefinement
import Mettapedia.TypeTheory.PresheafNativePredicateSubstitution

/-!
# Dependent suffix elimination for native predicate comprehension

A suffix family may depend on the complete original inhabitant. Replacing
that inhabitant by a refinement pulls back the actual suffix, retaining its
evidence. The induced complete map proves the original predicate everywhere
in the refined suffix, transports any consequent proved under that predicate,
and commutes with further substitution. No constancy of the suffix or its
future action is required.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateTail

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers
open PresheafNativeStableRefinement

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

noncomputable def suffix (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) :
    NativeType (totalSpace (chosen A predicate).decoded) :=
  B.reindex (forgetComplete A predicate)

noncomputable def suffixMap (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) :
    totalSpace (suffix A predicate B).decoded ⟶ totalSpace B.decoded :=
  totalReindexMap (forgetComplete A predicate) B.decoded

def suffixGuard (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) : Subfunctor (totalSpace B.decoded) :=
  predicate.preimage (totalProjection B.decoded)

/-- The original premise is true on every complete refined suffix
receipt, irrespective of how its later evidence depends on the prefix. -/
theorem suffixGuard_holds (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) (world : Cᵒᵖ)
    (receipt : (totalSpace (suffix A predicate B).decoded).obj world) :
    (suffixMap A predicate B).app world receipt ∈ (suffixGuard A predicate B).obj world :=
  forgetComplete_satisfies A predicate world receipt.1

theorem suffixGuard_preimage (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) :
    (suffixGuard A predicate B).preimage (suffixMap A predicate B) = ⊤ := by
  ext world receipt
  constructor
  · intro _
    trivial
  · intro _
    exact suffixGuard_holds A predicate B world receipt

/-- The logical c°E rule transports an arbitrary actual consequent under
the guarded original suffix to the corresponding refined suffix. -/
theorem eliminateConsequent (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded))
    (consequent : Subfunctor (totalSpace B.decoded))
    (derivation : suffixGuard A predicate B ≤ consequent) :
    ⊤ ≤ consequent.preimage (suffixMap A predicate B) := by
  intro world receipt _
  exact derivation world (suffixGuard_holds A predicate B world receipt)

theorem prefix_square (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) :
    suffixMap A predicate B ≫ totalProjection B.decoded =
      totalProjection (suffix A predicate B).decoded ≫ forgetComplete A predicate :=
  totalReindexMap_square (forgetComplete A predicate) B.decoded

/-- The suffix receipt keeps the original suffix inhabitant rather than
replacing it with proposition-valued inhabited support. -/
theorem suffix_evidence (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded)) (world : Cᵒᵖ)
    (receipt : (totalSpace (suffix A predicate B).decoded).obj world) :
    HEq ((suffixMap A predicate B).app world receipt).2 receipt.2 := HEq.rfl

noncomputable def eliminateTerm (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded))
    (motive : NativeType (totalSpace B.decoded)) (term : motive.decoded.sections) :
    (motive.reindex (suffixMap A predicate B)).decoded.sections :=
  reindexDisplayedSection (suffixMap A predicate B) motive.decoded term

theorem eliminateTerm_value (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded))
    (motive : NativeType (totalSpace B.decoded)) (term : motive.decoded.sections)
    (world : Cᵒᵖ) (receipt : (totalSpace (suffix A predicate B).decoded).obj world) :
    (eliminateTerm A predicate B motive term).val ⟨world, receipt⟩ =
      term.val ⟨world, (suffixMap A predicate B).app world receipt⟩ := rfl

theorem suffix_reindex (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded))
    (substitution : Q ⟶ totalSpace (chosen A predicate).decoded) :
    (suffix A predicate B).reindex substitution =
      B.reindex (substitution ≫ forgetComplete A predicate) :=
  (LocalType.reindex_comp B (forgetComplete A predicate) substitution).symm

/-- Replacing the prefix and then making any further context substitution
is the same complete evidence map as the composed substitution. -/
theorem suffixMap_substitution (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded))
    (substitution : Q ⟶ totalSpace (chosen A predicate).decoded) :
    totalReindexMap substitution (suffix A predicate B).decoded ≫ suffixMap A predicate B =
      totalReindexMap (substitution ≫ forgetComplete A predicate) B.decoded :=
  totalReindexMap_comp (forgetComplete A predicate) B.decoded substitution

theorem eliminateTerm_substitution (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (B : NativeType (totalSpace A.decoded))
    (motive : NativeType (totalSpace B.decoded)) (term : motive.decoded.sections)
    (substitution : Q ⟶ totalSpace (suffix A predicate B).decoded) :
    HEq (reindexDisplayedSection substitution
        (motive.reindex (suffixMap A predicate B)).decoded
        (eliminateTerm A predicate B motive term))
      (reindexDisplayedSection (substitution ≫ suffixMap A predicate B) motive.decoded term) := by
  exact heq_of_eq (reindexDisplayedSection_comp
    (suffixMap A predicate B) motive.decoded substitution term).symm

end Mettapedia.TypeTheory.PresheafNativePredicateTail
