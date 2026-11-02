import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-! The executable closure machine drains one immutable snapshot search before
publishing a round. Its retained native receipts supply finite logical keys.
The machine never interprets a work budget as search exhaustion. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Executable

structure Key where
  statementIndex : Nat
  grounding : List (String × Pattern)
  premises : List Pattern
  deriving Repr, DecidableEq, BEq

def grounding? (names : List String) (assignment : ScopedRuleMatching.Assignment) :
    Option (List (String × Pattern)) := names.mapM fun name => do
  let value ← ScopedRuleMatching.lookup assignment (Join.logicalVariable name)
  if value.dependencies.isEmpty && value.ambient == 0 then some (name,value.body) else none

def premiseFacts? : Nat → List GeneralPremise.Event → List Pattern → Option (List Pattern)
  | 0,_,_ => some []
  | _+1,[],_ => none
  | count+1,.query _ quantifiers row _ :: rest,facts => do
      if quantifiers != 0 then none else
        let fact ← facts[row]?
        let tail ← premiseFacts? count rest facts
        pure (fact :: tail)
  | _+1,_::_,_ => none

def key? (prepared : Prepared) (facts : List Pattern) (receipt : GeneralOccurrenceSemantics.Receipt) : Option Key := do
  let (ordinal,clause) ← (LPBridge.numberedClauses prepared.source)[receipt.firing.job.declaration.declarationIndex]?
  let grounding ← grounding? (DerivationIdentity.clauseVariables clause) receipt.firing.completed
  let premises ← premiseFacts? clause.positiveAtoms.length receipt.firing.premiseHistory facts
  pure ⟨ordinal,grounding,premises⟩

def insert {α : Type} [BEq α] (items : List α) (item : α) : List α :=
  if items.contains item then items else items ++ [item]

def commit? (prepared : Prepared) (snapshot : List Pattern) :
    List GeneralOccurrenceSemantics.Receipt → List Pattern → List Key → Option (List Pattern × List Key)
  | [],facts,keys => some (facts,keys)
  | receipt :: rest,facts,keys => do
      let key ← key? prepared snapshot receipt
      commit? prepared snapshot rest (insert facts receipt.target) (insert keys key)

structure Epoch where
  ordinal : Nat
  facts : List Pattern
  receipts : List GeneralOccurrenceSemantics.Receipt

inductive Fault where
  | invalidProvider | invalidReceipt
  deriving Repr, DecidableEq

def search (prepared : Prepared) (facts : List Pattern) :=
  Complete.Normalized.search (plan prepared facts) [] (.base "DlStatement") .standard

def closed (prepared : Prepared) (facts : List Pattern) : Bool :=
  let snapshot := snapshot prepared facts
  GeneralPremise.checkProviderClosed snapshot.language snapshot.free snapshot.provider

structure Machine (prepared : Prepared) where
  complete : Bool
  fault : Option Fault
  round : Nat
  facts : List Pattern
  keys : List Key
  history : List Epoch
  run : Complete.Classes.State (plan prepared facts)

def begin (prepared : Prepared) : Machine prepared :=
  let facts := prepared.seedFacts.eraseDups
  ⟨false,if closed prepared facts then none else some .invalidProvider,0,facts,[],[],
    (search prepared facts).run (request prepared.vocabulary) 0⟩

def tick (prepared : Prepared) (machine : Machine prepared) (quantum : Nat) : Machine prepared :=
  if machine.complete || machine.fault.isSome then machine else
    let run := (search prepared machine.facts).resume machine.run quantum
    if (search prepared machine.facts).status run != .complete then {machine with run} else
      let receipts := (search prepared machine.facts).publication run
      match commit? prepared machine.facts receipts machine.facts machine.keys with
      | none => {machine with fault := some .invalidReceipt,run}
      | some (facts,keys) =>
        let history := machine.history ++ [⟨machine.round,machine.facts,receipts⟩]
        if facts = machine.facts then
          {machine with complete := true,round := machine.round+1,keys,history,run}
        else if closed prepared facts then
          ⟨false,none,machine.round+1,facts,keys,history,(search prepared facts).run (request prepared.vocabulary) 0⟩
        else {machine with fault := some .invalidProvider,run}

def advance (prepared : Prepared) : Nat → Nat → Machine prepared → Machine prepared
  | 0,_,machine => machine
  | ticks+1,quantum,machine => advance prepared ticks quantum (tick prepared machine quantum)

theorem advance_add (prepared : Prepared) (first second quantum : Nat) (machine : Machine prepared) :
    advance prepared (first+second) quantum machine =
      advance prepared second quantum (advance prepared first quantum machine) := by
  induction first generalizing machine with
  | zero => simp only [Nat.zero_add,advance]
  | succ first ih => simpa only [Nat.succ_add,advance] using ih (tick prepared machine quantum)

theorem stopped_tick (prepared : Prepared) (machine : Machine prepared) (quantum : Nat)
    (stopped : machine.complete = true ∨ machine.fault.isSome = true) :
    tick prepared machine quantum = machine := by
  rcases stopped with stopped | stopped <;> simp [tick,stopped]

def decodeKey? (prepared : Prepared) (key : Key) : Option DerivationKey := do
  let grounding ← key.grounding.mapM fun (name,value) => do
    let decoded ← IRCodec.value? (Match.applyBindings (dictionary prepared.vocabulary) value)
    pure (name,decoded)
  let premises ← key.premises.mapM (decodeFact? prepared)
  pure ⟨key.statementIndex,grounding,premises⟩

#print axioms advance_add
#print axioms stopped_tick

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
