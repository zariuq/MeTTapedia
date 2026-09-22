import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentUniverseInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverseProducts

/-!
# Universe meanings on the actual shared native quotient

The unbounded native hierarchy, its mixed-level product/sum code operations,
and the formed-context interpretation use the same CwF. The primitive sort,
coverage, decoding and cumulative-meaning clauses below are proved on those
actual data. Code lifting keeps the selected native meaning and commutes
with the already qualified substitution action.

The model is syntactic. Its exact conversion-class view does not recover
raw source spelling, an ambient set interpretation, proof provenance, or a
least universe level. These results do not choose a host or runtime policy.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientUniverses

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive FormationSensitiveContextual SharedJudgmentFragment
open SharedJudgmentInterpretation (Context)
open SharedJudgmentQuotientInterpretation (context data)

variable {assembly : Assembly}

noncomputable def operations (assembly : Assembly) :
    SharedJudgmentUniverseInterpretation.Operations (QuotientCwf.cwf assembly.rules) where
  «universe» := QuotientUniverses.hierarchy assembly.declarations
  sortCode := QuotientUniverses.sortCode
  liftCode := QuotientUniverses.liftCode
  piCode := QuotientUniverseProducts.piCode
  sigmaCode := QuotientUniverseProducts.sigmaCode

theorem code_meaning {n : Nat} (source : Context assembly n) (level : LevelExpr)
    (type : Tower.Tm n) (typed : Typing assembly.rules source.raw type (sortTm level)) :
    (data assembly).term source type (sortTm level)
      ((operations assembly).universe.univ ((data assembly).ctx source) level)
      (QuotientUniverses.ofFormed level type typed) :=
  ⟨QuotientUniverses.universeType (context source) level, rfl,
    ⟨type, typed⟩, rfl, rfl, rfl⟩

/-- Meaning at an actual universe identifies this native term's code, not
just some equivalent carrier chosen after checking it. -/
theorem code_meaning_iff {n : Nat} (source : Context assembly n) (level : LevelExpr)
    (type : Tower.Tm n) (typed : Typing assembly.rules source.raw type (sortTm level))
    (code : QuotientUniverses.Code ((data assembly).ctx source) level) :
    (data assembly).term source type (sortTm level)
      ((operations assembly).universe.univ ((data assembly).ctx source) level) code ↔
      code = QuotientUniverses.ofFormed (context := (data assembly).ctx source) level type typed := by
  constructor
  · intro meaning
    exact SharedJudgmentQuotientInterpretation.term_meaning_unique meaning
      (code_meaning source level type typed)
  · intro same
    subst code
    exact code_meaning source level type typed

theorem sort_meaning : SharedJudgmentUniverseInterpretation.SortMeaning (data assembly) (operations assembly) := by
  intro n source level _
  exact ⟨QuotientInterpretation.type_meaning (context source)
    (QuotientUniverses.universeType (context source) level),
    code_meaning source (.succ level) (sortTm level) (.headType (.sort level))⟩

theorem code_total : SharedJudgmentUniverseInterpretation.CodeTotal (data assembly) (operations assembly) := by
  intro n source type level admitted
  exact ⟨QuotientUniverses.ofFormed level type admitted.typing,
    code_meaning source level type admitted.typing⟩

theorem codes_decode : SharedJudgmentUniverseInterpretation.CodesDecode (data assembly) (operations assembly) := by
  intro n source type level code admitted meaning
  have same := (code_meaning_iff source level type admitted.typing code).mp meaning
  subst code
  exact ⟨⟨type, .sort level, .sort level, admitted.typing⟩, rfl,
    (QuotientUniverses.decode_ofFormed (context := (data assembly).ctx source)
      level type admitted.typing).symm⟩

theorem cumulative_meaning :
    SharedJudgmentUniverseInterpretation.CumulativeMeaning (data assembly) (operations assembly) := by
  intro n source type lower upper order code admitted meaning
  have decoded : QuotientUniverses.decode code =
      QType.mk (⟨type, .sort lower, .sort lower, admitted.typing⟩ : TypeOver (context source)) := by
    rw [(code_meaning_iff source lower type admitted.typing code).mp meaning]
    exact QuotientUniverses.decode_ofFormed (context := (data assembly).ctx source)
      lower type admitted.typing
  have same : QuotientUniverses.liftCode order code =
      QuotientUniverses.ofFormed (context := (data assembly).ctx source)
        upper type (.cumul admitted.typing order) := by
    apply QuotientUniverses.decode_injective
    have sameClass :
        QType.mk (⟨type, .sort lower, .sort lower, admitted.typing⟩ : TypeOver (context source)) =
        QType.mk (⟨type, .sort upper, .sort upper, .cumul admitted.typing order⟩ : TypeOver (context source)) :=
      (QType.mk_eq_iff _ _).mpr (.refl _)
    exact (QuotientUniverses.decode_liftCode order code).trans
      (decoded.trans (sameClass.trans
        (QuotientUniverses.decode_ofFormed (context := (data assembly).ctx source)
          upper type (.cumul admitted.typing order)).symm))
  exact (code_meaning_iff source upper type (.cumul admitted.typing order) _).mpr same

theorem strict_code_uniqueness :
    SharedJudgmentUniverseInterpretation.StrictCodeUniqueness (data assembly) (operations assembly) := by
  intro n source type level first second _ firstMeaning secondMeaning
  exact SharedJudgmentQuotientInterpretation.term_meaning_unique firstMeaning secondMeaning

theorem strict_sort_decoding : SharedJudgmentUniverseInterpretation.StrictSortDecoding (operations assembly) :=
  QuotientUniverses.decode_sortCode

theorem strict_lift_decoding : SharedJudgmentUniverseInterpretation.StrictLiftDecoding (operations assembly) :=
  fun _ _ _ order code => QuotientUniverses.decode_liftCode order code

theorem universe_substitution : (operations assembly).universe.SubstitutionStable :=
  QuotientUniverses.substitutionStable assembly.declarations

/-- Actual nonidentity native substitution and two cumulative lifts meet
at the same displayed code and decoded dependent type. No semantic law is
left as a premise in this instance of the generic shared square. -/
theorem cumulative_substitution_square
    {n m : Nat} (source : Context assembly n) (target : Context assembly m)
    (sigma : Sub Tower.Head n m)
    (typed : FormationSensitive.CtxMor assembly.rules source.raw target.raw sigma)
    (semantic : (QuotientCwf.cwf assembly.rules).Sub
      ((data assembly).ctx target) ((data assembly).ctx source))
    (related : (data assembly).sub source target sigma semantic)
    {type : Tower.Tm n} {first middle last : LevelExpr}
    (earlier : Tower.Cumulative (.sort first) (.sort middle))
    (later : Tower.Cumulative (.sort middle) (.sort last))
    (admitted : Judgment assembly.rules source.raw type (sortTm first))
    (code : QuotientUniverses.Code ((data assembly).ctx source) first)
    (meaning : (data assembly).term source type (sortTm first)
      ((operations assembly).universe.univ ((data assembly).ctx source) first) code) :
    let finalCode := SharedJudgmentUniverseInterpretation.substituteCode (operations assembly)
      universe_substitution semantic
      ((operations assembly).liftCode later ((operations assembly).liftCode earlier code))
    Judgment assembly.rules target.raw (subst sigma type) (sortTm last) ∧
      finalCode = (operations assembly).liftCode
        (SharedJudgmentUniverseInterpretation.cumulativeTrans earlier later)
        (SharedJudgmentUniverseInterpretation.substituteCode (operations assembly)
          universe_substitution semantic code) ∧
      (data assembly).term target (subst sigma type) (sortTm last)
        ((operations assembly).universe.univ ((data assembly).ctx target) last) finalCode ∧
      (operations assembly).universe.el finalCode =
        (QuotientCwf.cwf assembly.rules).tySub ((operations assembly).universe.el code) semantic ∧
      (data assembly).ty target (subst sigma type)
        ((QuotientCwf.cwf assembly.rules).tySub ((operations assembly).universe.el code) semantic) :=
  SharedJudgmentUniverseInterpretation.cumulative_substitution_square
    (data assembly) (operations assembly) sort_meaning cumulative_meaning strict_code_uniqueness
    codes_decode strict_lift_decoding SharedJudgmentQuotientInterpretation.substitution_stable.2
    universe_substitution target.formed typed semantic related earlier later admitted code meaning

namespace Controls

open SharedJudgmentUniverseInterpretation (substituteCode cumulativeTrans)
open SharedJudgmentUniverseInterpretation.WeakeningControl

/-- An actual open code crosses the added Data binder and two universe
lifts in this model. Coverage and coherence are supplied by the constructions
above, not by assumptions about a proposed interpretation. -/
theorem open_code_square (level : LevelExpr) :
    ∃ (code : QuotientUniverses.Code ((data common).ctx (source level)) level)
      (semantic : (QuotientCwf.cwf common.rules).Sub
        ((data common).ctx (target level)) ((data common).ctx (source level))),
      (data common).term (source level) (.var 0) (sortTm level)
        ((operations common).universe.univ ((data common).ctx (source level)) level) code ∧
      (data common).sub (source level) (target level) substitution semantic ∧
      let finalCode := substituteCode (operations common) universe_substitution semantic
        ((operations common).liftCode (next_level (.succ level))
          ((operations common).liftCode (next_level level) code))
      Judgment common.rules (target level).raw (.var 1) (sortTm (.succ (.succ level))) ∧
        finalCode = (operations common).liftCode
          (cumulativeTrans (next_level level) (next_level (.succ level)))
          (substituteCode (operations common) universe_substitution semantic code) ∧
        (data common).term (target level) (.var 1) (sortTm (.succ (.succ level)))
          ((operations common).universe.univ ((data common).ctx (target level)) (.succ (.succ level)))
          finalCode ∧
        (operations common).universe.el finalCode =
          (QuotientCwf.cwf common.rules).tySub ((operations common).universe.el code) semantic ∧
        (data common).ty (target level) (.var 1)
          ((QuotientCwf.cwf common.rules).tySub ((operations common).universe.el code) semantic) :=
  semantic_control (data common) (operations common) sort_meaning code_total
    SharedJudgmentQuotientInterpretation.substitutions_total cumulative_meaning
    strict_code_uniqueness codes_decode strict_lift_decoding
    SharedJudgmentQuotientInterpretation.substitution_stable.2 universe_substitution level

/-- Cumulative admission does not identify the universe itself with its
successor. The changed semantic carrier is rejected by the actual graph. -/
theorem wrong_universe_meaning {n : Nat} (source : Context common n) (level : LevelExpr) :
    ¬ (data common).ty source (sortTm level)
      ((operations common).universe.univ ((data common).ctx source) (.succ level)) := by
  intro changed
  exact QuotientUniverses.universe_successor_distinct HOLNativeRelatorCompatibility.opacity
    ((data common).ctx source) level
    (SharedJudgmentQuotientInterpretation.type_meaning_unique
      (sort_meaning n source level source.formed).1 changed)

end Controls

#print axioms code_meaning_iff
#print axioms sort_meaning
#print axioms code_total
#print axioms codes_decode
#print axioms cumulative_meaning
#print axioms strict_code_uniqueness
#print axioms universe_substitution
#print axioms cumulative_substitution_square
#print axioms Controls.open_code_square
#print axioms Controls.wrong_universe_meaning

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientUniverses
