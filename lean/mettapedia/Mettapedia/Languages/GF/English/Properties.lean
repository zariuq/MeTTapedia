/-
# English Linguistic Properties

Equivalence relations and correctness properties for English morphology.
Connects English concrete syntax to abstract GF notions.

## References
- Czech/Properties.lean: pattern followed
- GF Abstract.lean: NodeEquiv, NodeLinearize
-/

import Mettapedia.Languages.GF.English.Syntax

namespace Mettapedia.Languages.GF.English.Properties

open Mettapedia.Languages.GF.English
open Syntax

/-! ## Linguistic Equivalence

Two English nouns are linguistically equivalent iff they produce
identical surface forms for all Number x Case combinations.
-/

/-- Two English nouns are linguistically equivalent iff they produce
    the same surface string in every slot -/
def LinguisticallyEquivalent (n1 n2 : EnglishNoun) : Prop :=
  ∀ (p : EnglishParams), n1.s p.number p.case = n2.s p.number p.case

/-- Linguistic equivalence is reflexive -/
theorem lingEquiv_refl (n : EnglishNoun) : LinguisticallyEquivalent n n :=
  fun _ => rfl

/-- Linguistic equivalence is symmetric -/
theorem lingEquiv_symm {n1 n2 : EnglishNoun} :
    LinguisticallyEquivalent n1 n2 → LinguisticallyEquivalent n2 n1 :=
  fun h p => (h p).symm

/-- Linguistic equivalence is transitive -/
theorem lingEquiv_trans {n1 n2 n3 : EnglishNoun} :
    LinguisticallyEquivalent n1 n2 →
    LinguisticallyEquivalent n2 n3 →
    LinguisticallyEquivalent n1 n3 :=
  fun h12 h23 p => (h12 p).trans (h23 p)

/-! ## DetCN Properties -/

/-- Two equivalent CNs produce identical surface forms when declined directly -/
theorem lingEquiv_implies_same_decline (cn1 cn2 : EnglishCN) :
    LinguisticallyEquivalent cn1 cn2 →
    ∀ (n : Number) (c : Case), cn1.s n c = cn2.s n c :=
  fun h n c => h ⟨c, n⟩

end Mettapedia.Languages.GF.English.Properties
