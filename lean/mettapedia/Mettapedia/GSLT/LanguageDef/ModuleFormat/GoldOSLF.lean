import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StaticDecider
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Hints
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProvider

/-! Executable native-type questions about operational compiler inputs. Finite
provider rows are read in their frozen environment. Equation-free languages
use the existing certified front-door deciders; other equation theories use
general certificate search or a supplied canonical-form interface. An unknown
answer is retained as unknown.
This is not a source-language or compiler adequacy theorem. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

def relationEnvironment (provider : GeneralPremise.ProviderSnapshot) : Engine.RelationEnv where
  tuples relation _ := (provider.rows.filter (fun row => row.relation == relation)).map (·.values)

def reaches (target : Pattern) : Formula 0 := .mu (.or (.is target) (.possibly .any (.var 0)))

def verdict : Answer → Option Bool
  | .proved _ => some true
  | .refuted _ => some false
  | .unknown _ => none

/-- Static questions at a successor do not require closing its future
region. Questions involving fixed points or parts retain the region decider. -/
def equationFreeBase {relEnv : Engine.RelationEnv} {language : LanguageDef}
    (free : language.isEquationFree = true) (fuel rounds : Nat) : Decider relEnv language where
  decide formula source :=
    match staticEval language formula source with
    | some answer => some answer
    | none => (equationFreeDecider (relEnv := relEnv) free fuel rounds).decide formula source
  exact := by
    intro formula source answer decided
    cases found : staticEval language formula source with
    | none =>
        simp only [found] at decided
        exact (equationFreeDecider free fuel rounds).exact decided
    | some value =>
        simp only [found, Option.some.injEq] at decided
        subst value
        exact staticEval_exact free Env.closed formula source found

def ask (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (fuel rounds : Nat) (formula : Formula 0) (source : Pattern) : Answer :=
  let relEnv := relationEnvironment provider
  if free : language.isEquationFree = true then
    askWith relEnv (signatureOf language) language fuel formula source
      (modalDecider (equationFreeSuccessors fuel free)
        (equationFreeBase free fuel rounds)) none rounds
  else Mettapedia.OSLF.NativeTypes.GeneratedLogic.ask relEnv (signatureOf language)
    language fuel formula source none rounds

theorem ask_proved {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}
    {fuel rounds : Nat} {formula : Formula 0} {source : Pattern} {evidence : Evidence}
    (answered : ask language provider fuel rounds formula source = .proved evidence) :
    (referenceStructure (relationEnvironment provider) language .syntax).sat Env.closed formula source := by
  unfold ask at answered
  split at answered
  · exact askWith_proved formsFor_none answered
  · exact Mettapedia.OSLF.NativeTypes.GeneratedLogic.ask_proved answered

theorem ask_refuted {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}
    {fuel rounds : Nat} {formula : Formula 0} {source : Pattern} {evidence : Evidence}
    (answered : ask language provider fuel rounds formula source = .refuted evidence) :
    ¬ (referenceStructure (relationEnvironment provider) language .syntax).sat Env.closed formula source := by
  unfold ask at answered
  split at answered
  · exact askWith_refuted formsFor_none answered
  · exact Mettapedia.OSLF.NativeTypes.GeneratedLogic.ask_refuted answered

/-- Equation-based cores supply the existing certified canonical-form
interface. A successful build or native comparison cannot supply it. -/
def askCanonical (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (fuel rounds : Nat) (forms : CanonicalForms (relationEnvironment provider) language fuel)
    (formula : Formula 0) (source : Pattern) : Answer :=
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.ask (relationEnvironment provider) (signatureOf language)
    language fuel formula source none rounds (some forms)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF
