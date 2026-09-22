import Mettapedia.Languages.OpenTheory.ExcludedMiddleNotDerivable

/-!
# The defined connectives of the primitive kernel

OpenTheory's base theory, following HOL Light, has one primitive constant,
equality, and defines every logical connective from it.  Truth, the universal
quantifier, conjunction, implication, falsity, negation and disjunction are
`PrimitiveSentences.truthDB`, `ExcludedMiddle.forallDB`,
`ExcludedMiddle.andDB`, `ExcludedMiddle.impDB`,
`ExcludedMiddle.falsityDefinitionDB`, `ExcludedMiddle.notDB` and
`ExcludedMiddle.orDB`.  This module adds the existential quantifier, in HOL
Light's impredicative form

  `∃ = λ P. ∀ q. (∀ x. P x ⇒ q) ⇒ q`,

and records the type of every defined connective, so that derived rules and
translations can state their typing facts once.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

namespace DefinedConnectives

open ExcludedMiddle

/-- `∃ = λ P. ∀ q. (∀ x. P x ⇒ q) ⇒ q` at the element type `A`. -/
def existsDB (A : Ty) : DBTerm :=
  .abs (.function A Ty.bool)
    (.app (forallDB Ty.bool)
      (.abs Ty.bool
        (impAppDB
          (.app (forallDB A)
            (.abs A (impAppDB (.app (.bound 2) (.bound 0)) (.bound 1))))
          (.bound 0))))

theorem forallDB_inferType (A : Ty) :
    DBTerm.inferType [] (forallDB A) = some (.function (.function A Ty.bool) Ty.bool) := by
  simp [forallDB, DBTerm.inferType, CanonicalTerm.equalityDB,
    PrimitiveSentences.truthDB, PrimitiveSentences.identityBool, Ty.equality, Ty.function,
    TypeOp.function, Ty.destFunction?]

theorem andDB_inferType : DBTerm.inferType [] andDB = some boolBinaryTy := by
  simp [andDB, boolBinaryTy, DBTerm.inferType, CanonicalTerm.equalityDB,
    PrimitiveSentences.truthDB, PrimitiveSentences.identityBool, Ty.equality, Ty.function,
    TypeOp.function, Ty.destFunction?]

theorem impDB_inferType : DBTerm.inferType [] impDB = some boolBinaryTy := by
  simp [impDB, andDB, boolBinaryTy, DBTerm.inferType, CanonicalTerm.equalityDB,
    PrimitiveSentences.truthDB, PrimitiveSentences.identityBool, Ty.equality, Ty.function,
    TypeOp.function, Ty.destFunction?]

theorem existsDB_inferType (A : Ty) :
    DBTerm.inferType [] (existsDB A) = some (.function (.function A Ty.bool) Ty.bool) := by
  simp [existsDB, forallDB, impAppDB, impDB, andDB, boolBinaryTy, DBTerm.inferType,
    CanonicalTerm.equalityDB, PrimitiveSentences.truthDB, PrimitiveSentences.identityBool,
    Ty.equality, Ty.function, TypeOp.function, Ty.destFunction?]

end DefinedConnectives

end Mettapedia.Languages.OpenTheory
