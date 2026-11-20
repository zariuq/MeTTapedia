import Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorQueries

/-!
# Scoped factor graph handoff controls

A hidden door variable has two binary sensors. Each observation slot is local
to one sensor. Both readouts have the same ordered factor scopes and
elimination plan. The numerator's final factor selects an open door.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadoutControls

open Mettapedia.GSLT.LanguageDef
open PolynomialReadoutCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open CertificateGSLT ExecutableFactorTable ScopedFactorReadout

def domains (_ : Fin 3) : Nat := 2
theorem positive (v : Fin 3) : 0 < domains v := by simp [domains]

def report (sensor : Fin 3) (closed openWeight : ℚ) : Table domains :=
  tabulate domains positive [sensor] (by simp) fun cfg =>
    if (cfg sensor).val = 0 then closed else openWeight

private def sensorFactor (sensor : Fin 3) : Table domains :=
  tabulate domains positive ([0, sensor] : List (Fin 3)).dedup (List.nodup_dedup _) fun cfg =>
    if (cfg 0).val = (cfg sensor).val then 3 else 1

def inputTables (numerator : Bool) : Vector (Table domains) 6 :=
  ⟨#[report 0 1 1, sensorFactor 1, sensorFactor 2, report 1 1 1, report 2 1 1,
    report 0 (if numerator then 0 else 1) 1], rfl⟩

def scopes (i : Fin 6) : List (Fin 3) := (inputTables false)[i].scope
def order : List (Fin 3) := [1, 2, 0]
def assignment : Config domains := fun v => ⟨0, positive v⟩
def plan : EliminationPlan 3 6 := EliminationPlan.compile scopes order
def expression : Pattern := lower scopes plan assignment

abbrev Runtime := EliminationPlan.Runtime positive scopes order

def initial (numerator : Bool) : Runtime :=
  let tables := inputTables numerator
  ⟨tables, fun i => by fin_cases i <;> rfl,
    EliminationPlan.Retained.fromInputs positive plan (fun i : Fin 6 => tables[i])⟩

structure Step where
  name : String
  edit : Option (Fin 6 × Table domains)

def steps : List Step :=
  [⟨"Prior", none⟩,
    ⟨"FirstReport", some (3, report 1 0 1)⟩,
    ⟨"Replay", some (3, report 1 0 1)⟩,
    ⟨"BothReports", some (4, report 2 0 1)⟩,
    ⟨"ZeroSupport", some (3, report 1 0 0)⟩,
    ⟨"Retraction", some (3, report 1 1 1)⟩]

private def mass (state : Runtime) : Option ℚ :=
  let cached := state.table.value domains positive assignment
  if execute? (fun i : Fin 6 => state.factors[i]) expression = some cached then
    some cached
  else none

private def readPair (state : Runtime × Runtime) : Option Masses := do
  let num ← mass state.1
  let den ← mass state.2
  pure ⟨num, den⟩

private def editPair (state : Runtime × Runtime) (slot : Fin 6) (replacement : Table domains) :
    Option (Runtime × Runtime) := do
  let num ← state.1.tryReplace slot replacement
  let den ← state.2.tryReplace slot replacement
  pure (num.1, den.1)

def checkpoints : Option (List (String × Masses)) := do
  let mut state := (initial true, initial false)
  let mut results := []
  for step in steps do
    if let some (slot, replacement) := step.edit then
      state ← editPair state slot replacement
    let pair ← readPair state
    results := (step.name, pair) :: results
  pure results.reverse

#guard checkpoints == some [
  ("Prior", ⟨16, 32⟩), ("FirstReport", ⟨12, 16⟩), ("Replay", ⟨12, 16⟩),
  ("BothReports", ⟨9, 10⟩), ("ZeroSupport", ⟨0, 0⟩), ("Retraction", ⟨12, 16⟩)]

private def sameSlot (a b : Bool) : Option Masses := do
  let start := (initial true, initial false)
  let first ← editPair start 3 (report 1 (if a then 0 else 1) (if a then 1 else 0))
  let last ← editPair first 3 (report 1 (if b then 0 else 1) (if b then 1 else 0))
  readPair last

#guard sameSlot false true == some ⟨12, 16⟩
#guard sameSlot true false == some ⟨4, 16⟩

def provider (slot : Fin 6) : Table domains := (inputTables true)[slot]

#guard lookup? provider (entry 5 0) == some 0
#guard lookup? provider (entry 6 0) == none
#guard lookup? provider (entry 5 2) == none

private def firstRead : Pattern := lower scopes (.input 0) assignment
private def secondRead : Pattern := lower scopes (.input 1) assignment
private def productSource : Pattern := lower scopes (.mul (.input 0) (.input 1)) assignment
private def productTarget : Pattern := mul secondRead firstRead
private def swapProof : RawOpenProof := .node ⟨⟨"product-comm"⟩, [secondRead, firstRead]⟩ []

theorem swap_checked : checkReplacement productSource productTarget swapProof = true := by
  decide +kernel

#guard execute? provider productTarget == some 3

private def absentRead : Pattern := PolynomialReadoutCalculus.read (entry 6 0)
private def masked : Pattern := mul zero absentRead
private def maskProof : RawOpenProof := .node ⟨⟨"product-zero"⟩, [absentRead]⟩ []

theorem masked_arithmetic_equality :
    checkOpenRaw validated [] (equal masked zero) maskProof = true := by decide +kernel

theorem masked_footprint_refused :
    checkReplacement zero masked maskProof = false := by decide +kernel

#guard execute? provider masked == none

#guard ((conditionalMasses? (domains := fun _ : Fin 1 => 3) (fun _ => by decide)
  [] [] [⟨0, 1⟩] [0]).bind Masses.posterior?) == some (1 / 3)

#guard conditionalMasses? (domains := fun _ : Fin 1 => 3) (fun _ => by decide)
  [] [] [⟨0, 1⟩] [] == none

private def mixedDomains (v : Fin 2) : Nat := if v = 0 then 2 else 3
private theorem mixedPositive (v : Fin 2) : 0 < mixedDomains v := by
  fin_cases v <;> decide

private def mixedFactor : Table mixedDomains :=
  ⟨[1, 0], by decide, #[1, 2, 3, 5, 7, 11], rfl⟩

#guard conditionalMasses? mixedPositive [mixedFactor] [⟨1, ⟨2, by decide⟩⟩]
  [⟨0, ⟨1, by decide⟩⟩] [0, 1] ==
  some ⟨11, 18⟩

end Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadoutControls
