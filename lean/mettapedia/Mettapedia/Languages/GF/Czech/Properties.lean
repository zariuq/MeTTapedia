/-
# Czech Morphology: Proven Properties

Canary theorems that verify Czech noun morphology correctness.
Each theorem category tests a different failure mode:
1. **Exact form counts** - fails if ANY declension rule changes
2. **Universal syncretism invariants** - proves ∀ lemma, not just test nouns
3. **Constructor coherence** - verifies paradigm-gender wiring
4. **Phonological regression** - pins specific morphophonological outputs
5. **Linguistic equivalence** - framework for bisimulation

These theorems are correctness certificates: a broken implementation
cannot satisfy them all simultaneously.
-/

import Mettapedia.Languages.GF.Czech.Morphology
import Mettapedia.Languages.GF.Czech.Declensions
import Mettapedia.Languages.GF.Czech.Examples

namespace Mettapedia.Languages.GF.Czech.Properties

open Mettapedia.Languages.GF.Czech
open Declensions Examples

/-! ## 1. Exact Form Counts

Pin the precise number of distinct forms per paradigm.
Would fail if: any suffix changes, any syncretism breaks, any rule is added/removed.
Would NOT pass with a trivial implementation (e.g., returning lemma = 1 form, not 10).
-/

-- Original 5 paradigms
theorem pán_exact_forms : countDistinctForms pán = 10 := by decide
theorem hrad_exact_forms : countDistinctForms hrad = 8 := by decide
theorem žena_exact_forms : countDistinctForms žena = 10 := by decide
theorem město_exact_forms : countDistinctForms město = 8 := by decide
theorem muž_exact_forms : countDistinctForms muž = 7 := by decide

-- New 9 paradigms
theorem předseda_exact_forms : countDistinctForms předseda = 10 := by decide
theorem soudce_exact_forms : countDistinctForms soudce = 6 := by decide
theorem stroj_exact_forms : countDistinctForms stroj = 7 := by decide
theorem růže_exact_forms : countDistinctForms růže = 6 := by decide
theorem píseň_exact_forms : countDistinctForms píseň = 7 := by decide
theorem kost_exact_forms : countDistinctForms kost = 6 := by decide
theorem kuře_exact_forms : countDistinctForms kuře = 9 := by decide
theorem moře_exact_forms : countDistinctForms moře = 6 := by decide
theorem stavení_exact_forms : countDistinctForms stavení = 4 := by decide

/-- All test nouns exhibit syncretism (fewer forms than 14 slots) -/
theorem test_nouns_have_syncretism :
    ∀ n ∈ testNouns, hasSyncretism n = true := by
  intro n hn
  simp [testNouns] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 2. Universal Syncretism Invariants

These hold for ALL possible lemmas (∀ lemma : String), encoding
real Czech linguistic knowledge, not just test data.
-/

section UniversalInvariants

/-- PAN: animate Gen.Sg = Acc.Sg (accusative = genitive for animates) -/
theorem pán_gen_eq_acc_sg (lemma : String) :
    declinePAN lemma ⟨Case.Gen, Number.Sg⟩ =
    declinePAN lemma ⟨Case.Acc, Number.Sg⟩ := by
  simp [declinePAN]

/-- PAN: Dat.Sg = Loc.Sg -/
theorem pán_dat_eq_loc_sg (lemma : String) :
    declinePAN lemma ⟨Case.Dat, Number.Sg⟩ =
    declinePAN lemma ⟨Case.Loc, Number.Sg⟩ := by
  simp [declinePAN]

/-- PAN: Nom.Pl = Voc.Pl (both use palatalization) -/
theorem pán_nom_eq_voc_pl (lemma : String) :
    declinePAN lemma ⟨Case.Nom, Number.Pl⟩ =
    declinePAN lemma ⟨Case.Voc, Number.Pl⟩ := by
  simp [declinePAN]

/-- PAN: Acc.Pl = Ins.Pl -/
theorem pán_acc_eq_ins_pl (lemma : String) :
    declinePAN lemma ⟨Case.Acc, Number.Pl⟩ =
    declinePAN lemma ⟨Case.Ins, Number.Pl⟩ := by
  simp [declinePAN]

/-- HRAD: inanimate Nom = Acc in singular -/
theorem hrad_nom_eq_acc_sg (lemma : String) :
    declineHRAD lemma ⟨Case.Nom, Number.Sg⟩ =
    declineHRAD lemma ⟨Case.Acc, Number.Sg⟩ := by
  simp [declineHRAD]

/-- HRAD: Gen = Dat = Loc in singular (triple syncretism) -/
theorem hrad_gen_dat_loc_sg (lemma : String) :
    declineHRAD lemma ⟨Case.Gen, Number.Sg⟩ =
    declineHRAD lemma ⟨Case.Dat, Number.Sg⟩ ∧
    declineHRAD lemma ⟨Case.Gen, Number.Sg⟩ =
    declineHRAD lemma ⟨Case.Loc, Number.Sg⟩ := by
  simp [declineHRAD]

/-- HRAD: Nom = Acc = Voc in plural -/
theorem hrad_nom_acc_voc_pl (lemma : String) :
    declineHRAD lemma ⟨Case.Nom, Number.Pl⟩ =
    declineHRAD lemma ⟨Case.Acc, Number.Pl⟩ ∧
    declineHRAD lemma ⟨Case.Nom, Number.Pl⟩ =
    declineHRAD lemma ⟨Case.Voc, Number.Pl⟩ := by
  simp [declineHRAD]

/-- ZENA: Dat.Sg = Loc.Sg -/
theorem žena_dat_eq_loc_sg (lemma : String) :
    declineZENA lemma ⟨Case.Dat, Number.Sg⟩ =
    declineZENA lemma ⟨Case.Loc, Number.Sg⟩ := by
  simp [declineZENA]

/-- MESTO: neuter Nom = Acc = Voc in singular -/
theorem město_nom_acc_voc_sg (lemma : String) :
    declineMESTO lemma ⟨Case.Nom, Number.Sg⟩ =
    declineMESTO lemma ⟨Case.Acc, Number.Sg⟩ ∧
    declineMESTO lemma ⟨Case.Nom, Number.Sg⟩ =
    declineMESTO lemma ⟨Case.Voc, Number.Sg⟩ := by
  simp [declineMESTO]

/-- MESTO: Nom = Acc = Voc in plural too -/
theorem město_nom_acc_voc_pl (lemma : String) :
    declineMESTO lemma ⟨Case.Nom, Number.Pl⟩ =
    declineMESTO lemma ⟨Case.Acc, Number.Pl⟩ ∧
    declineMESTO lemma ⟨Case.Nom, Number.Pl⟩ =
    declineMESTO lemma ⟨Case.Voc, Number.Pl⟩ := by
  simp [declineMESTO]

/-- MUZ: animate Gen.Sg = Acc.Sg -/
theorem muž_gen_eq_acc_sg (lemma : String) :
    declineMUZ lemma ⟨Case.Gen, Number.Sg⟩ =
    declineMUZ lemma ⟨Case.Acc, Number.Sg⟩ := by
  simp [declineMUZ]

/-- MUZ: Dat = Voc = Loc in singular -/
theorem muž_dat_voc_loc_sg (lemma : String) :
    declineMUZ lemma ⟨Case.Dat, Number.Sg⟩ =
    declineMUZ lemma ⟨Case.Voc, Number.Sg⟩ ∧
    declineMUZ lemma ⟨Case.Dat, Number.Sg⟩ =
    declineMUZ lemma ⟨Case.Loc, Number.Sg⟩ := by
  simp [declineMUZ]

/-- MUZ: Nom.Pl = Voc.Pl -/
theorem muž_nom_eq_voc_pl (lemma : String) :
    declineMUZ lemma ⟨Case.Nom, Number.Pl⟩ =
    declineMUZ lemma ⟨Case.Voc, Number.Pl⟩ := by
  simp [declineMUZ]

/-- SOUDCE: Nom = Gen = Acc = Voc in singular (extreme syncretism) -/
theorem soudce_nom_gen_acc_voc_sg (lemma : String) :
    declineSOUDCE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSOUDCE lemma ⟨Case.Gen, Number.Sg⟩ ∧
    declineSOUDCE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSOUDCE lemma ⟨Case.Acc, Number.Sg⟩ ∧
    declineSOUDCE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSOUDCE lemma ⟨Case.Voc, Number.Sg⟩ := by
  simp [declineSOUDCE]

/-- STROJ: inanimate Nom = Acc in singular -/
theorem stroj_nom_eq_acc_sg (lemma : String) :
    declineSTROJ lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSTROJ lemma ⟨Case.Acc, Number.Sg⟩ := by
  simp [declineSTROJ]

/-- STROJ: Dat = Voc = Loc in singular -/
theorem stroj_dat_voc_loc_sg (lemma : String) :
    declineSTROJ lemma ⟨Case.Dat, Number.Sg⟩ =
    declineSTROJ lemma ⟨Case.Voc, Number.Sg⟩ ∧
    declineSTROJ lemma ⟨Case.Dat, Number.Sg⟩ =
    declineSTROJ lemma ⟨Case.Loc, Number.Sg⟩ := by
  simp [declineSTROJ]

/-- KOST: Gen = Dat = Voc = Loc in singular -/
theorem kost_gen_dat_voc_loc_sg (lemma : String) :
    declineKOST lemma ⟨Case.Gen, Number.Sg⟩ =
    declineKOST lemma ⟨Case.Dat, Number.Sg⟩ ∧
    declineKOST lemma ⟨Case.Gen, Number.Sg⟩ =
    declineKOST lemma ⟨Case.Voc, Number.Sg⟩ ∧
    declineKOST lemma ⟨Case.Gen, Number.Sg⟩ =
    declineKOST lemma ⟨Case.Loc, Number.Sg⟩ := by
  simp [declineKOST]

/-- KURE: neuter Nom = Acc = Voc in singular -/
theorem kuře_nom_acc_voc_sg (lemma : String) :
    declineKURE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineKURE lemma ⟨Case.Acc, Number.Sg⟩ ∧
    declineKURE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineKURE lemma ⟨Case.Voc, Number.Sg⟩ := by
  simp [declineKURE]

/-- MORE: Nom = Gen = Acc = Voc in singular (maximal sg syncretism) -/
theorem moře_nom_gen_acc_voc_sg (lemma : String) :
    declineMORE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineMORE lemma ⟨Case.Gen, Number.Sg⟩ ∧
    declineMORE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineMORE lemma ⟨Case.Acc, Number.Sg⟩ ∧
    declineMORE lemma ⟨Case.Nom, Number.Sg⟩ =
    declineMORE lemma ⟨Case.Voc, Number.Sg⟩ := by
  simp [declineMORE]

/-- STAVENI: all singular forms except Ins are identical -/
theorem stavení_sg_invariance (lemma : String) :
    declineSTAVENI lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSTAVENI lemma ⟨Case.Gen, Number.Sg⟩ ∧
    declineSTAVENI lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSTAVENI lemma ⟨Case.Dat, Number.Sg⟩ ∧
    declineSTAVENI lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSTAVENI lemma ⟨Case.Acc, Number.Sg⟩ ∧
    declineSTAVENI lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSTAVENI lemma ⟨Case.Voc, Number.Sg⟩ ∧
    declineSTAVENI lemma ⟨Case.Nom, Number.Sg⟩ =
    declineSTAVENI lemma ⟨Case.Loc, Number.Sg⟩ := by
  simp [declineSTAVENI]

end UniversalInvariants

/-! ## 3. Constructor Coherence

Verify paradigm constructors produce correct gender/declension.
Would fail if: constructor accidentally swaps gender or declension type.
-/

theorem declPAN_gender (l : String) : (declPAN l).gender = Gender.MascAnim := rfl
theorem declPAN_declension (l : String) : (declPAN l).declension = DeclensionType.pan := rfl
theorem declHRAD_gender (l : String) : (declHRAD l).gender = Gender.MascInanim := rfl
theorem declHRAD_declension (l : String) : (declHRAD l).declension = DeclensionType.hrad := rfl
theorem declZENA_gender (l : String) : (declZENA l).gender = Gender.Fem := rfl
theorem declZENA_declension (l : String) : (declZENA l).declension = DeclensionType.zena := rfl
theorem declMESTO_gender (l : String) : (declMESTO l).gender = Gender.Neutr := rfl
theorem declMESTO_declension (l : String) : (declMESTO l).declension = DeclensionType.mesto := rfl
theorem declMUZ_gender (l : String) : (declMUZ l).gender = Gender.MascAnim := rfl
theorem declMUZ_declension (l : String) : (declMUZ l).declension = DeclensionType.muz := rfl
theorem declPREDSEDA_gender (l : String) : (declPREDSEDA l).gender = Gender.MascAnim := rfl
theorem declPREDSEDA_declension (l : String) : (declPREDSEDA l).declension = DeclensionType.predseda := rfl
theorem declSOUDCE_gender (l : String) : (declSOUDCE l).gender = Gender.MascAnim := rfl
theorem declSOUDCE_declension (l : String) : (declSOUDCE l).declension = DeclensionType.soudce := rfl
theorem declSTROJ_gender (l : String) : (declSTROJ l).gender = Gender.MascInanim := rfl
theorem declSTROJ_declension (l : String) : (declSTROJ l).declension = DeclensionType.stroj := rfl
theorem declRUZE_gender (l : String) : (declRUZE l).gender = Gender.Fem := rfl
theorem declRUZE_declension (l : String) : (declRUZE l).declension = DeclensionType.ruze := rfl
theorem declPISEN_gender (l : String) : (declPISEN l).gender = Gender.Fem := rfl
theorem declPISEN_declension (l : String) : (declPISEN l).declension = DeclensionType.pisen := rfl
theorem declKOST_gender (l : String) : (declKOST l).gender = Gender.Fem := rfl
theorem declKOST_declension (l : String) : (declKOST l).declension = DeclensionType.kost := rfl
theorem declKURE_gender (l : String) : (declKURE l).gender = Gender.Neutr := rfl
theorem declKURE_declension (l : String) : (declKURE l).declension = DeclensionType.kure := rfl
theorem declMORE_gender (l : String) : (declMORE l).gender = Gender.Neutr := rfl
theorem declMORE_declension (l : String) : (declMORE l).declension = DeclensionType.more := rfl
theorem declSTAVENI_gender (l : String) : (declSTAVENI l).gender = Gender.Neutr := rfl
theorem declSTAVENI_declension (l : String) : (declSTAVENI l).declension = DeclensionType.staveni := rfl

/-! ## 4. Phonological Regression Canaries

Pin specific morphophonological outputs that are hard to get right.
Would fail if: vowel shortening, palatalization, or stem extraction breaks.
-/

/-- Vocative shortening: pán → pane (á shortened to a, not *páne) -/
theorem pán_vocative_shortens :
    declineFull (declPAN "pán") ⟨Case.Voc, Number.Sg⟩ = "pane" := by decide

/-- k→c palatalization: kluk → kluci (not *kluki) -/
theorem kluk_palatalization :
    declineFull (declPAN "kluk") ⟨Case.Nom, Number.Pl⟩ = "kluci" := by decide

/-- h→z palatalization: vrh → vrzi (not *vrhi) -/
theorem vrh_palatalization :
    declineFull (declPAN "vrh") ⟨Case.Nom, Number.Pl⟩ = "vrzi" := by decide

/-- Feminine bare stem genitive: žena → žen (zero ending) -/
theorem žena_gen_pl_bare_stem :
    declineFull (declZENA "žena") ⟨Case.Gen, Number.Pl⟩ = "žen" := by decide

/-- Neuter Gen.Sg = Nom.Pl: město → města in both slots -/
theorem město_gen_sg_eq_nom_pl :
    declineFull (declMESTO "město") ⟨Case.Gen, Number.Sg⟩ =
    declineFull (declMESTO "město") ⟨Case.Nom, Number.Pl⟩ := by decide

/-! ## 5. Paradigm Coverage -/

/-- Check if a noun's declension paradigm is implemented -/
def isImplementedParadigm (n : CzechNoun) : Bool :=
  match n.declension with
  | .pan | .predseda | .soudce | .hrad | .muz | .stroj
  | .zena | .ruze | .pisen | .kost
  | .mesto | .kure | .more | .staveni => true
  | .irregular => false

/-- All test nouns use implemented paradigms -/
theorem test_nouns_paradigm_coverage :
    ∀ n ∈ testNouns, isImplementedParadigm n = true := by
  intro n hn
  simp [testNouns] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 6. Linguistic Equivalence

Two nouns are bisimilar if they decline identically in all contexts.
This is structurally trivial (any equality-based relation is an equivalence),
but serves as a framework for ontological categorization.
-/

/-- Linguistic equivalence: nouns with identical inflection -/
def LinguisticallyEquivalent (n₁ n₂ : CzechNoun) : Prop :=
  ∀ params : CzechParams, declineFull n₁ params = declineFull n₂ params

namespace LinguisticallyEquivalent

theorem refl (n : CzechNoun) : LinguisticallyEquivalent n n :=
  fun _ => Eq.refl _

theorem symm {n₁ n₂ : CzechNoun} :
    LinguisticallyEquivalent n₁ n₂ → LinguisticallyEquivalent n₂ n₁ :=
  fun h params => (h params).symm

theorem trans {n₁ n₂ n₃ : CzechNoun} :
    LinguisticallyEquivalent n₁ n₂ →
    LinguisticallyEquivalent n₂ n₃ →
    LinguisticallyEquivalent n₁ n₃ :=
  fun h12 h23 params => (h12 params).trans (h23 params)

theorem is_equivalence : Equivalence LinguisticallyEquivalent :=
  ⟨refl, symm, trans⟩

end LinguisticallyEquivalent

end Mettapedia.Languages.GF.Czech.Properties
