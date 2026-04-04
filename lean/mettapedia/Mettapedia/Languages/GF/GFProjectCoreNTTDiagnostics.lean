import Algorithms.GF.Generated.ProjectCoreSig
import Mettapedia.Languages.GF.GFRealSyntaxBridge
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Project-Core Real GF Syntax → OSLF → NTT Diagnostics

Theorem-bearing diagnostics for the larger grounded `project_core` slice.

Unlike the regression-style JSON checks in `GFProjectCoreConformance`, this file
works over the generated kernel-reducible `ProjectCoreSig.funsList`, so the
constructor/NTT surface is available for ordinary Lean proofs.

This remains intentionally syntax-only:

- real GF constructors and sorts are present;
- the larger English/Czech bilingual abstract surface is available as a
  theorem-level `LanguageDef`;
- the reduction relation is still empty, so modal structure is honest and
  vacuous until a separate grounded semantic layer exists above the grammar.
-/

namespace Mettapedia.Languages.GF.GFProjectCoreNTTDiagnostics

open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.TypeSynthesis

set_option maxRecDepth 10000

/-- Kernel-reducible syntax-only `project_core` language from the generated function list. -/
def projectCoreSyntaxLangKR : LanguageDef :=
  gfSyntaxLanguageDefFromList "Grammar"
    Algorithms.GF.Generated.ProjectCoreSig.funsList

example : projectCoreSyntaxLangKR.name = "Grammar" := rfl
example : projectCoreSyntaxLangKR.equations = [] := rfl
example : projectCoreSyntaxLangKR.rewrites = [] := rfl

theorem existNP_crossing :
    ("ExistNP", "NP", "Cl") ∈ unaryCrossings projectCoreSyntaxLangKR := by
  decide

theorem questCl_crossing :
    ("QuestCl", "Cl", "QCl") ∈ unaryCrossings projectCoreSyntaxLangKR := by
  decide

theorem usePron_crossing :
    ("UsePron", "Pron", "NP") ∈ unaryCrossings projectCoreSyntaxLangKR := by
  decide

private def presTempPattern : Pattern :=
  .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]

def somethingNPPattern : Pattern :=
  .apply "something_NP" []

def hePronPattern : Pattern :=
  .apply "he_Pron" []

def usePronHePattern : Pattern :=
  .apply "UsePron" [hePronPattern]

def existSomethingClPattern : Pattern :=
  .apply "ExistNP" [somethingNPPattern]

def questionExistClPattern : Pattern :=
  .apply "QuestCl" [existSomethingClPattern]

def progressiveHaveVPPattern : Pattern :=
  .apply "ProgrVP"
    [ .apply "ComplSlash"
        [ .apply "SlashV2a" [.apply "have_V2" []]
        , somethingNPPattern ] ]

def existSomethingSentencePattern : Pattern :=
  .apply "UseCl"
    [ presTempPattern
    , .apply "PPos" []
    , existSomethingClPattern ]

def questionExistSentencePattern : Pattern :=
  .apply "UseQCl"
    [ presTempPattern
    , .apply "PPos" []
    , questionExistClPattern ]

def progressiveHaveSentencePattern : Pattern :=
  .apply "UseCl"
    [ presTempPattern
    , .apply "PPos" []
    , .apply "PredVP" [usePronHePattern, progressiveHaveVPPattern] ]

mutual
  def containsLabel (label : String) : Pattern → Bool
    | .bvar _ => false
    | .fvar _ => false
    | .apply f args => f == label || containsLabelList label args
    | .lambda _ body => containsLabel label body
    | .multiLambda _ _ body => containsLabel label body
    | .subst p q => containsLabel label p || containsLabel label q
    | .collection _ elems _ => containsLabelList label elems

  def containsLabelList (label : String) : List Pattern → Bool
    | [] => false
    | p :: ps => containsLabel label p || containsLabelList label ps
end

abbrev ProjectCoreSNativeType := langNativeType projectCoreSyntaxLangKR "S"
abbrev ProjectCoreQSNativeType := langNativeType projectCoreSyntaxLangKR "QS"

def existentialSentenceType : ProjectCoreSNativeType :=
  { sort := "S", pred := fun p => containsLabel "ExistNP" p = true }

def progressiveSentenceType : ProjectCoreSNativeType :=
  { sort := "S", pred := fun p => containsLabel "ProgrVP" p = true }

def interrogativeSentenceType : ProjectCoreQSNativeType :=
  { sort := "QS"
  , pred := fun p => containsLabel "UseQCl" p = true ∧ containsLabel "QuestCl" p = true }

theorem existSomething_satisfies_existentialSentenceType :
    (langOSLF projectCoreSyntaxLangKR "S").satisfies
      existSomethingSentencePattern existentialSentenceType.pred := by
  show containsLabel "ExistNP" existSomethingSentencePattern = true
  decide

theorem progressiveHave_satisfies_progressiveSentenceType :
    (langOSLF projectCoreSyntaxLangKR "S").satisfies
      progressiveHaveSentencePattern progressiveSentenceType.pred := by
  show containsLabel "ProgrVP" progressiveHaveSentencePattern = true
  decide

theorem questionExist_satisfies_interrogativeSentenceType :
    (langOSLF projectCoreSyntaxLangKR "QS").satisfies
      questionExistSentencePattern interrogativeSentenceType.pred := by
  show
    containsLabel "UseQCl" questionExistSentencePattern = true ∧
      containsLabel "QuestCl" questionExistSentencePattern = true
  decide

theorem projectCoreSyntax_no_reduces {p q : Pattern} :
    ¬ langReduces projectCoreSyntaxLangKR p q := by
  intro h
  cases h with
  | topRule r hr bs0 hbs0 bs hprem hq =>
      have hnil : r ∈ ([] : List RewriteRule) := by
        simp [projectCoreSyntaxLangKR, gfSyntaxLanguageDefFromList, gfFunsListToLanguageDef] at hr
      cases hnil
  | congElem hct i hi r hr bs0 hbs0 bs hprem hq =>
      have hnil : r ∈ ([] : List RewriteRule) := by
        simp [projectCoreSyntaxLangKR, gfSyntaxLanguageDefFromList, gfFunsListToLanguageDef] at hr
      cases hnil

theorem projectCoreSyntax_no_diamond (φ : Pattern → Prop) (p : Pattern) :
    ¬ langDiamond projectCoreSyntaxLangKR φ p := by
  intro h
  rcases (langDiamond_spec (lang := projectCoreSyntaxLangKR) (φ := φ) (p := p)).1 h with
    ⟨q, hred, _⟩
  exact projectCoreSyntax_no_reduces hred

theorem projectCoreSyntax_vacuous_box (φ : Pattern → Prop) (p : Pattern) :
    langBox projectCoreSyntaxLangKR φ p := by
  rw [langBox_spec]
  intro q hred
  exact False.elim (projectCoreSyntax_no_reduces hred)

theorem existSomething_box_self :
    langBox projectCoreSyntaxLangKR
      (fun q => q = existSomethingSentencePattern) existSomethingSentencePattern :=
  projectCoreSyntax_vacuous_box _ _

theorem questionExist_box_self :
    langBox projectCoreSyntaxLangKR
      (fun q => q = questionExistSentencePattern) questionExistSentencePattern :=
  projectCoreSyntax_vacuous_box _ _

theorem progressiveHave_not_diamond_self :
    ¬ langDiamond projectCoreSyntaxLangKR
      (fun q => q = progressiveHaveSentencePattern) progressiveHaveSentencePattern :=
  projectCoreSyntax_no_diamond _ _

end Mettapedia.Languages.GF.GFProjectCoreNTTDiagnostics
