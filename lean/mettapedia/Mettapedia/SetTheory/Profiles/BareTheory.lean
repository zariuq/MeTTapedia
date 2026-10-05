import Mettapedia.GSLT.LanguageDef.HOLTypeDerivedConsequence
import Mettapedia.Logic.HOL.LindenbaumSet

/-!
# The bare profile as an empty higher-order theory

`HOLTypeDerivedConsequence.institution` is a consequence institution whose
sentences are closed formulas of extensional higher-order logic. The bare
profile assumes no set principle, so its axiom set in that institution is
empty. Implication reflexivity belongs to the consequence closure of that
empty set.

The institution has no membership vocabulary. The Megalodon and hyperset
principle sets are not sentences of it.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

open Mettapedia.Logic.HOL
open Mettapedia.GSLT.LanguageDef.HOLTypeDerivedConsequence
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-- A signature with one base sort and no constants. -/
def bareSignature : TypeDerivedSignature.{0} :=
  ⟨Unit, ⟨fun _ => Empty⟩⟩

/-- The closed formula `⊤ → ⊤`. -/
def bareImplication : ClosedFormula (fun _ : Ty Unit => Empty) :=
  .imp .top .top

/-- The bare profile: the consequence closure of the empty axiom set. -/
def bareTheory : PiInstitution.TheoryObject institution :=
  PiInstitution.generatedTheory institution bareSignature ∅

/-- Implication reflexivity is a theorem of the bare profile's closure. -/
theorem bare_implication_refl : bareImplication ∈ bareTheory.theory.1 := by
  show ClosedTheorySet.Provable ∅ bareImplication
  exact ClosedTheorySet.provable_imp_refl ∅ .top

/-- The bare ledger: no set assumption, and one theorem of the empty closure. -/
structure BareLedger : Prop where
  implicationRefl : bareImplication ∈ bareTheory.theory.1

theorem bareLedger : BareLedger where
  implicationRefl := bare_implication_refl

end Mettapedia.SetTheory.Profiles
