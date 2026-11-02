import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SortWitnesses
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LanguageEquality
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextLabels

/-!
# Certified canonical forms, by language

Canonical forms whose coherence is proved for one language (the π-calculus with its restriction laws and its parallel
fragment, CCS with its sums and restriction laws and with replication, mobile ambients with their restriction,
replication and boundary laws, and with communication and paths too, the ρ-calculus, the grids modulo `A = B` and
`Wrap x = x`) are kept with that language. A
language read from a file gets them when it is that language: languages have decidable equality, and the forms are
carried along the equality (`certifiedFormsOf`). So the executable reads these languages modulo their equations, with
the forms their own theorems certify, and any other language as before. A certified language may also bring a decider
for the questions the search leaves open, in a reading (`certifiedDeciderOf`): π and CCS decide their step
modalities, their partners' labels included, at their listed successors, and mobile ambients with communication theirs,
their two-level context labels included.
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

/-- **A language with certified canonical forms**, at the premise fuels they are certified for, and a decider, in the
readings it is certified for. -/
structure Certified where
  name : String
  language : LanguageDef
  forms : (fuel : ℕ) → Option (CanonicalForms RelationEnv.empty language fuel)
  decider : (reading : LanguageReading) → Option (Decider RelationEnv.empty language reading)

/-- π's decider, in π's reading. -/
def piDecider (reading : LanguageReading) :
    Option (Decider RelationEnv.empty Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piCalc reading) :=
  if same : reading.equations = PiPrenexForms.reading.equations ∧ reading.rules.isReference = true then
    some (by
      have readingIs : PiPrenexForms.reading = reading := by
        obtain ⟨equations, rules⟩ := reading
        obtain ⟨equationsIs, reference⟩ := same
        simp only at equationsIs reference
        rw [RuleReading.eq_reference reference, equationsIs]
        rfl
      exact readingIs ▸ PiPartners.decider)
  else none

/-- CCS's decider, in CCS's reading. -/
def ccsDecider (reading : LanguageReading) :
    Option (Decider RelationEnv.empty Mettapedia.Languages.ProcessCalculi.CCS.ccsCalc reading) :=
  if same : reading.equations = CCSForms.reading.equations ∧ reading.rules.isReference = true then
    some (by
      have readingIs : CCSForms.reading = reading := by
        obtain ⟨equations, rules⟩ := reading
        obtain ⟨equationsIs, reference⟩ := same
        simp only at equationsIs reference
        rw [RuleReading.eq_reference reference, equationsIs]
        rfl
      exact readingIs ▸ CCSPartners.decider)
  else none

/-- The decider of mobile ambients with communication, in their reading. -/
def ambientCommDecider (reading : LanguageReading) :
    Option (Decider RelationEnv.empty Mettapedia.Languages.ProcessCalculi.Ambient.Comm.ambientCommCalc reading) :=
  if same : reading.equations = AmbientCommForms.reading.equations ∧ reading.rules.isReference = true then
    some (by
      have readingIs : AmbientCommForms.reading = reading := by
        obtain ⟨equations, rules⟩ := reading
        obtain ⟨equationsIs, reference⟩ := same
        simp only at equationsIs reference
        rw [RuleReading.eq_reference reference, equationsIs]
        rfl
      exact readingIs ▸ AmbientContextLabels.decider)
  else none

/-- Forms certified at one premise fuel. -/
def atFuel {language : LanguageDef} (certifiedFuel : ℕ) (forms : CanonicalForms RelationEnv.empty language certifiedFuel)
    (fuel : ℕ) : Option (CanonicalForms RelationEnv.empty language fuel) :=
  if same : certifiedFuel = fuel then some (same ▸ forms) else none

/-- **The languages with certified canonical forms.** -/
def certified : List Certified :=
  [⟨"pi", Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piCalc,
     fun fuel => some (PiPrenexForms.forms fuel), piDecider⟩,
   ⟨"pi-parallel", Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piParallelFragment,
     fun fuel => some (PiForms.forms fuel), fun _ => none⟩,
   ⟨"ambient-nu", Mettapedia.Languages.ProcessCalculi.Ambient.Full.ambientNuCalc,
     fun fuel => some (AmbientNuForms.forms fuel), fun _ => none⟩,
   ⟨"ambient-comm", Mettapedia.Languages.ProcessCalculi.Ambient.Comm.ambientCommCalc,
     fun fuel => some (AmbientCommForms.forms fuel), ambientCommDecider⟩,
   ⟨"ccs", Mettapedia.Languages.ProcessCalculi.CCS.ccsCalc, fun fuel => some (CCSForms.forms fuel), ccsDecider⟩,
   ⟨"ccs-rep", Mettapedia.Languages.ProcessCalculi.CCS.Replicated.ccsRepCalc,
     fun fuel => some (CCSRepForms.forms fuel), fun _ => none⟩,
   ⟨"rho", rhoCalc, atFuel 1 Rho.Controls.canonicalForms, fun _ => none⟩,
   ⟨"aliased", CanonicalRegionControls.aliased, atFuel 2 CanonicalRegionControls.aliasForms, fun _ => none⟩,
   ⟨"wrapped", CanonicalUnwrapControls.wrapped, atFuel 2 CanonicalUnwrapControls.wrapForms, fun _ => none⟩]

/-- **The certified canonical forms of a language**, when it is one of the certified languages. -/
def certifiedFormsOf (language : LanguageDef) (fuel : ℕ) : Option (CanonicalForms RelationEnv.empty language fuel) :=
  go certified
where
  go : List Certified → Option (CanonicalForms RelationEnv.empty language fuel)
    | [] => none
    | entry :: rest => if same : entry.language = language then same ▸ entry.forms fuel else go rest


/-- The decider that answers nothing. -/
def noDecider {language : LanguageDef} {reading : LanguageReading} : Decider RelationEnv.empty language reading where
  decide _ _ := none
  exact decided := by cases decided

/-- **The certified decider of a language**, in a reading, when it is one of the certified languages. -/
def certifiedDeciderOf (language : LanguageDef) (reading : LanguageReading) :
    Option (Decider RelationEnv.empty language reading) :=
  go certified
where
  go : List Certified → Option (Decider RelationEnv.empty language reading)
    | [] => none
    | entry :: rest => if same : entry.language = language then same ▸ entry.decider reading else go rest

end Mettapedia.OSLF.NativeTypes.Product
