import Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentitySemanticBasis

/-!
# A finite Boolean-identity authority with infinite-primary meaning

This module packages Boolean-algebra identities as a NIK theory family.  The
kind is the finite variable arity.  Its three faces remain distinct:

* scope is ordinary two-valued validity;
* certificates are explicit complete truth tables;
* meaning is validity in the infinite atomless algebra of Cantor clopens.

Stone representation proves that the finite scope is sound for the external
meaning.  Conversely, the nontrivial Cantor algebra reflects two-valued
validity, so the selected semantic profile is exact.  The checker nevertheless
depends only on finite syntax and finite tables; the Stone model is not placed
on the executable replay path.

This is an equational authority, not a decision procedure for the full
first-order theory of atomless Boolean algebras.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority

open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentitySemanticBasis
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-! ## Arity-indexed theory and certificate authority -/

/-- Each kind fixes the finite set of variables available to an identity. -/
abbrev Kind := Nat

/-- The independently interpreted Boolean-identity family. -/
def theory : TheoryFamily Kind where
  __ := BooleanAlgebraIdentitySemanticBasis.theory CantorAlgebra

/-- Exact finite replay for the independently declared two-valued scope. -/
def contract : AuthorityContract theory where
  __ := BooleanAlgebraIdentitySemanticBasis.contract CantorAlgebra

/-- The semantic face and the finite scope agree extensionally, although they
are defined through different structures. -/
theorem scope_iff_infinitePrimaryMeaning (arity : Kind)
    (equation : theory.Claim arity) :
    theory.Scope arity equation <-> theory.Meaning arity equation :=
  BooleanAlgebraIdentitySemanticBasis.scope_iff_meaning
    CantorAlgebra arity equation

/-- Accepted finite evidence projects to the infinite atomless semantic
carrier. -/
theorem accepted_has_infinitePrimaryMeaning {arity : Kind}
    (equation : theory.Claim arity)
    (certificate : contract.Certificate arity)
    (accepted : (contract.checker arity).check equation certificate = true) :
    theory.Meaning arity equation :=
  (contract.projection arity).sound equation certificate accepted

/-! ## Positive and negative controls -/

namespace Canary

open BooleanAlgebraIdentityDecision.Canary

/-- The canonical distributivity identity replays through the NIK contract. -/
theorem distributive_replays :
    (contract.checker 2).check distributiveIdentity
      (fullTruthTable (Var := TwoVar)) = true :=
  distributive_truth_table_accepted

/-- Replay projects to validity in the infinite atomless Cantor algebra. -/
theorem distributive_has_infinitePrimaryMeaning :
    theory.Meaning 2 distributiveIdentity :=
  accepted_has_infinitePrimaryMeaning distributiveIdentity
    (fullTruthTable (Var := TwoVar)) distributive_replays

/-- The semantic carrier is not a disguised finite algebra. -/
theorem semanticCarrier_is_gunky_and_infinite :
    Mettapedia.Foundations.Gunk.IsGunky CantorAlgebra /\
      Infinite CantorAlgebra :=
  cantor_is_gunky_and_infinite

/-- The selected false identity fails the independent semantic meaning. -/
theorem falseIdentity_not_infinitePrimaryMeaning :
    ¬ theory.Meaning 2 falseIdentity :=
  falseIdentity_not_cantorValid

/-- No alternate truth-table certificate can make the false identity pass. -/
theorem falseIdentity_rejected
    (certificate : contract.Certificate 2) :
    (contract.checker 2).check falseIdentity certificate = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact falseIdentity_not_infinitePrimaryMeaning
    (accepted_has_infinitePrimaryMeaning falseIdentity certificate accepted)

/-- A partial list of rows remains invalid evidence even for a true claim. -/
theorem incomplete_distributive_certificate_rejected :
    (contract.checker 2).check distributiveIdentity
      [separatingAssignment] = false :=
  incomplete_truth_table_rejected

end Canary

#print axioms theory
#print axioms contract
#print axioms scope_iff_infinitePrimaryMeaning
#print axioms accepted_has_infinitePrimaryMeaning
#print axioms Canary.distributive_replays
#print axioms Canary.distributive_has_infinitePrimaryMeaning
#print axioms Canary.semanticCarrier_is_gunky_and_infinite
#print axioms Canary.falseIdentity_not_infinitePrimaryMeaning
#print axioms Canary.falseIdentity_rejected
#print axioms Canary.incomplete_distributive_certificate_rejected

end Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityNIKAuthority
