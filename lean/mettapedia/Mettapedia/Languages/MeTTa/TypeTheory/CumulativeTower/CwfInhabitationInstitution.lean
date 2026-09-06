import Mettapedia.TypeTheory.CwfSimpleDependentInstitution
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ContextualLadderBridge

/-!
# The cumulative-tower syntax as a global-inhabitation institution

The declaration-aware cumulative-tower syntax already forms a CwF with a
terminal context.  Applying the generic construction exposes its logical
inhabitation face without adding syntax, equations, typing rules, or a second
model of the calculus.

This is deliberately only the global-inhabitation institution of the native
syntax CwF.  It is not claimed to be a category of all semantic models of
Martin-Lof type theory.  Its satisfaction observer also forgets which term
witnessed inhabitation; a checked pair of distinct universe terms records
that boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.CwfInhabitationInstitution

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CwfInhabitationInstitution
open Presentation
open Presentation.SyntacticContextual

/-- The existing declaration-aware syntactic CwF, with no replacement
carrier or typing relation. -/
abbrev towerCwf := SyntacticContextual.asCwfWithTerminal Tower.rules

/-- Its institution of contexts, contextual types, global substitutions, and
fibrewise inhabitation. -/
abbrev towerInstitution := ofCwf towerCwf

/-- The native cumulative-tower inhabitation logic as one node of the common
heterogeneous category of institutions. -/
def towerInstitutionObject :=
  Mettapedia.TypeTheory.CwfSimpleDependentInstitution.institutionObject towerCwf

/-- The empty native telescope, read as an institution signature. -/
def emptySignature : Signature towerCwf :=
  Opposite.op ⟨SyntacticContextual.TowerExamples.empty⟩

/-- The identity global substitution into the empty native telescope. -/
def emptyGlobal : towerInstitution.model.obj
    (Opposite.op emptySignature) :=
  Discrete.mk (towerCwf.toCwf.idS towerCwf.empty)

/-- `U₁` is a sentence of the native institution at the empty context. -/
def universeOneSentence : towerInstitution.sentence.obj emptySignature :=
  SyntacticContextual.TowerExamples.universeOne

/-- The native witness obtained from `U₀ : U₁`, transported only across the
CwF identity-substitution law. -/
def universeZeroWitness :
    Witness towerCwf emptySignature emptyGlobal universeOneSentence :=
  Term.cast
    (TypeOver.reindex_id
      SyntacticContextual.TowerExamples.universeOne).symm
    SyntacticContextual.TowerExamples.universeZero

/-- The distinct native legacy-ground witness in the same observed fibre. -/
def legacyGroundWitness :
    Witness towerCwf emptySignature emptyGlobal universeOneSentence :=
  Term.cast
    (TypeOver.reindex_id
      SyntacticContextual.TowerExamples.universeOne).symm
    SyntacticContextual.TowerExamples.legacyGround

/-- `U₀ : U₁` witnesses native satisfaction of the universe sentence. -/
theorem universeOne_satisfied :
    towerInstitution.satisfies emptySignature emptyGlobal
      universeOneSentence := by
  exact witnessSupport towerCwf emptySignature emptyGlobal
    universeOneSentence universeZeroWitness

/-- The independently authored legacy ground code is a second witness of
the same universe sentence. -/
theorem universeOne_satisfied_by_legacyGround :
    towerInstitution.satisfies emptySignature emptyGlobal
      universeOneSentence := by
  exact witnessSupport towerCwf emptySignature emptyGlobal
    universeOneSentence legacyGroundWitness

/-- The two native witnesses are not identified by the CwF packaging. -/
theorem universeZero_ne_legacyGround :
    SyntacticContextual.TowerExamples.universeZero ≠
      SyntacticContextual.TowerExamples.legacyGround := by
  intro equality
  have equalCodes := congrArg Term.code equality
  have equalHeads :
      Tower.Head.sort Tower.zero = Tower.Head.legacyGround :=
    Tm.head.inj equalCodes
  cases equalHeads

/-- The corresponding witnesses remain distinct after the identity
reindexing required by the institution fibre. -/
theorem universeZeroWitness_ne_legacyGroundWitness :
    universeZeroWitness ≠ legacyGroundWitness := by
  intro equality
  have equalCodes := congrArg Term.code equality
  change
    SyntacticContextual.TowerExamples.universeZero.code =
      SyntacticContextual.TowerExamples.legacyGround.code at equalCodes
  have equalHeads :
      Tower.Head.sort Tower.zero = Tower.Head.legacyGround :=
    Tm.head.inj equalCodes
  cases equalHeads

/-- Therefore the proposition-valued satisfaction observer is not faithful
on this proof-relevant native term fibre. -/
theorem witnessSupport_not_injective :
    ¬ Function.Injective
      (witnessSupport towerCwf emptySignature emptyGlobal
        universeOneSentence) := by
  rw [witnessSupport_injective_iff_subsingleton]
  intro thin
  exact universeZeroWitness_ne_legacyGroundWitness
    (thin.allEq universeZeroWitness legacyGroundWitness)

/-- Negative observer control: proposition-valued inhabitation deliberately
forgets witness identity even though the native syntax retains it. -/
theorem inhabitation_observer_is_not_witness_complete :
    towerInstitution.satisfies emptySignature emptyGlobal
        universeOneSentence ∧
      ¬ Function.Injective
        (witnessSupport towerCwf emptySignature emptyGlobal
          universeOneSentence) :=
  ⟨universeOne_satisfied, witnessSupport_not_injective⟩

#print axioms towerInstitution
#print axioms towerInstitutionObject
#print axioms universeOne_satisfied
#print axioms universeOne_satisfied_by_legacyGround
#print axioms universeZero_ne_legacyGround
#print axioms universeZeroWitness_ne_legacyGroundWitness
#print axioms witnessSupport_not_injective
#print axioms inhabitation_observer_is_not_witness_complete

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.CwfInhabitationInstitution
