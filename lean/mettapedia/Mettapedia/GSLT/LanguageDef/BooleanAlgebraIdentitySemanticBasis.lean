import Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
import Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

/-!
# Semantic-basis irrelevance for Boolean identities

The equational language of Boolean algebras cannot distinguish one
nontrivial Boolean algebra from another.  This module makes that precise at
the NIK authority boundary:

* every selected Boolean algebra supplies an independently defined meaning;
* the finite truth-table checker is exact for every such meaning;
* identity-on-syntax authority translations connect any two nontrivial
  semantic bases and are conservative;
* finite, infinite atomic, and infinite atomless carriers therefore agree on
  every equational claim even though they disagree on carrier properties such
  as gunk.

The final negative result is the important boundary.  Selecting an atomless
carrier does not make atomlessness observable in a language containing only
equations.  A ground intended to express gunk itself needs a richer claim
language rather than a different interpretation of the same identities.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentitySemanticBasis

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uBasis vBasis

/-- A semantic basis supplies the meaning of Boolean identities through
ordinary interpretation in its selected carrier. -/
def theory (B : Type uBasis) [BooleanAlgebra B] : TheoryFamily Nat where
  Signature := Unit
  signatureOf := fun _arity => ()
  Claim := fun arity => Equation (Fin arity)
  Scope := fun _arity equation => BoolValid equation
  Meaning := fun _arity equation => ValidIn B equation
  scope_sound := by
    intro _arity _equation valid
    exact valid.validIn

/-- The same finite truth-table replay discipline qualifies every selected
Boolean semantic basis. -/
def contract (B : Type uBasis) [BooleanAlgebra B] :
    AuthorityContract (theory B) where
  Certificate := fun arity => TruthTableCertificate (Fin arity)
  checker := fun _arity => truthTableChecker
  scopeAuthority := fun _arity => truthTableChecker_authority

/-- In a nontrivial basis, finite scope and independently interpreted meaning
agree extensionally. -/
theorem scope_iff_meaning (B : Type uBasis) [BooleanAlgebra B]
    [Nontrivial B] (arity : Nat) (equation : (theory B).Claim arity) :
    (theory B).Scope arity equation <->
      (theory B).Meaning arity equation :=
  boolValid_iff_validIn equation

/-- Every pair of nontrivial Boolean bases is connected by an exact
identity-on-claims, identity-on-certificates authority translation.  Only the
independently defined meaning predicate changes. -/
def basisTranslation
    {B : Type uBasis} {C : Type vBasis}
    [BooleanAlgebra B] [Nontrivial B]
    [BooleanAlgebra C] [Nontrivial C] :
    CertifiedTranslation (contract B) (contract C) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _arity; rfl
  mapClaim := fun _arity equation => equation
  mapCertificate := fun _arity certificate => certificate
  check_commutes := by intro _arity _equation _certificate; rfl
  meaning_preserved := by
    intro _arity _equation valid
    exact (boolValid_of_validIn valid).validIn

/-- Changing between nontrivial Boolean bases invents neither equational
scope nor equational meaning. -/
theorem basisTranslation_conservative
    {B : Type uBasis} {C : Type vBasis}
    [BooleanAlgebra B] [Nontrivial B]
    [BooleanAlgebra C] [Nontrivial C] :
    (basisTranslation (B := B) (C := C)).toTheoryTranslation.Conservative where
  scope_reflecting := by
    intro _arity _equation inScope
    exact inScope
  meaning_reflecting := by
    intro _arity _equation valid
    exact (boolValid_of_validIn valid).validIn

/-- All nontrivial Boolean bases validate exactly the same equations. -/
theorem meaning_iff
    (B : Type uBasis) (C : Type vBasis)
    [BooleanAlgebra B] [Nontrivial B]
    [BooleanAlgebra C] [Nontrivial C]
    (arity : Nat) (equation : Equation (Fin arity)) :
    (theory B).Meaning arity equation <->
      (theory C).Meaning arity equation :=
  (boolValid_iff_validIn (B := B) equation).symm.trans
    (boolValid_iff_validIn (B := C) equation)

/-- The complete indexed meaning predicates are extensionally equal across
nontrivial Boolean bases. -/
theorem meaning_predicate_eq
    (B : Type uBasis) (C : Type vBasis)
    [BooleanAlgebra B] [Nontrivial B]
    [BooleanAlgebra C] [Nontrivial C] :
    (theory B).Meaning = (theory C).Meaning := by
  funext arity equation
  exact propext (meaning_iff B C arity equation)

/-! ## Three bases and the expressive-boundary canary -/

/-- The ordinary finite two-valued basis. -/
abbrev FiniteBasis := Bool

/-- An infinite but atomic Boolean basis. -/
abbrev AtomicInfiniteBasis := Set Nat

/-- The infinite atomless Cantor-clopen basis. -/
abbrev AtomlessInfiniteBasis := CantorAlgebra

def finiteToAtomless :
    CertifiedTranslation (contract FiniteBasis)
      (contract AtomlessInfiniteBasis) :=
  basisTranslation

def atomlessToFinite :
    CertifiedTranslation (contract AtomlessInfiniteBasis)
      (contract FiniteBasis) :=
  basisTranslation

def atomicInfiniteToAtomless :
    CertifiedTranslation (contract AtomicInfiniteBasis)
      (contract AtomlessInfiniteBasis) :=
  basisTranslation

theorem finiteToAtomless_conservative :
    finiteToAtomless.toTheoryTranslation.Conservative :=
  basisTranslation_conservative

theorem atomlessToFinite_conservative :
    atomlessToFinite.toTheoryTranslation.Conservative :=
  basisTranslation_conservative

theorem atomicInfiniteToAtomless_conservative :
    atomicInfiniteToAtomless.toTheoryTranslation.Conservative :=
  basisTranslation_conservative

/-- The finite and atomless bases have exactly the same equational meaning. -/
theorem finite_atomless_meaning_eq :
    (theory FiniteBasis).Meaning =
      (theory AtomlessInfiniteBasis).Meaning :=
  meaning_predicate_eq FiniteBasis AtomlessInfiniteBasis

/-- The infinite atomic and infinite atomless bases also have exactly the
same equational meaning. -/
theorem atomic_atomless_meaning_eq :
    (theory AtomicInfiniteBasis).Meaning =
      (theory AtomlessInfiniteBasis).Meaning :=
  meaning_predicate_eq AtomicInfiniteBasis AtomlessInfiniteBasis

theorem finiteBasis_not_gunky :
    ¬ IsGunky FiniteBasis :=
  not_isGunky_bool

theorem atomicInfiniteBasis_not_gunky :
    ¬ IsGunky AtomicInfiniteBasis :=
  not_isGunky_set

theorem atomlessInfiniteBasis_gunky :
    IsGunky AtomlessInfiniteBasis :=
  isGunky_clopens_cantor

theorem atomlessInfiniteBasis_infinite :
    Infinite AtomlessInfiniteBasis :=
  infinite_of_isGunky atomlessInfiniteBasis_gunky

/-- Equal equational meaning does not determine whether the semantic carrier
is gunky.  Atomlessness is invisible at this language boundary. -/
theorem equational_meaning_equal_but_gunk_differs :
    (theory FiniteBasis).Meaning =
        (theory AtomlessInfiniteBasis).Meaning /\
      ¬ IsGunky FiniteBasis /\
      IsGunky AtomlessInfiniteBasis :=
  ⟨finite_atomless_meaning_eq, finiteBasis_not_gunky,
    atomlessInfiniteBasis_gunky⟩

/-- Even restricting to infinite carriers does not make gunk equationally
observable: the powerset and Cantor-clopen bases agree on all identities but
sit on opposite sides of atomlessness. -/
theorem infinite_equational_meaning_equal_but_gunk_differs :
    (theory AtomicInfiniteBasis).Meaning =
        (theory AtomlessInfiniteBasis).Meaning /\
      ¬ IsGunky AtomicInfiniteBasis /\
      IsGunky AtomlessInfiniteBasis :=
  ⟨atomic_atomless_meaning_eq, atomicInfiniteBasis_not_gunky,
    atomlessInfiniteBasis_gunky⟩

#print axioms scope_iff_meaning
#print axioms basisTranslation
#print axioms basisTranslation_conservative
#print axioms meaning_iff
#print axioms meaning_predicate_eq
#print axioms finiteToAtomless_conservative
#print axioms atomlessToFinite_conservative
#print axioms atomicInfiniteToAtomless_conservative
#print axioms finite_atomless_meaning_eq
#print axioms atomic_atomless_meaning_eq
#print axioms equational_meaning_equal_but_gunk_differs
#print axioms infinite_equational_meaning_equal_but_gunk_differs

end Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentitySemanticBasis
