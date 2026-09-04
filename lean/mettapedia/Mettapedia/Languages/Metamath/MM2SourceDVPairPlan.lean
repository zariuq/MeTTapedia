import Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup

/-!
# Source-derived Metamath `$d` pair plans for ordinary MM2

A `$d x y z $.` statement denotes the ordered sequence of canonical pairs
`(x,y), (x,z), (y,z)`.  Computing that syntax-directed sequence belongs to the
source transformation; deciding whether the declaration is currently legal
and whether each pair is a first or repeated occurrence belongs to ordinary
MM2 execution.

This module makes the boundary explicit.  The source compiler emits a passive,
owner-bound pair plan.  A canonical decoder validates its representation, but
authorization additionally requires equality with the plan recomputed from an
already admitted source fold.  Directly authored rows therefore cannot invent
a `$d` pair merely by satisfying the representation grammar.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceDVPairPlan

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceDVLicenseProjection
open Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTState

abbrev DVPair := String × String

/-! ## Exact source plan -/

/-- One `$d` occurrence and the exact canonical pair sequence derived from its
source spelling.  `position` is the statement occurrence, not a set index. -/
structure SourceDVPairPlan where
  position : Nat
  statement : RawStatement
  pairs : List DVPair
deriving DecidableEq, Repr

/-- Syntax-directed pair production.  Non-`$d` statements produce no pairs. -/
def statementDVPairs : RawStatement → List DVPair
  | .djDecl _ names _ => allDistinctPairs (names.map (·.name))
  | _ => []

/-- A statement contributes a plan exactly when it is a `$d` declaration.
Even a declaration with too few names receives a plan; the admitted source
fold rejects it before this data can reach execution. -/
def sourceDVPairPlan? (position : Nat) : RawStatement → Option SourceDVPairPlan
  | statement@(.djDecl _ names _) =>
      some
        { position
          statement
          pairs := allDistinctPairs (names.map (·.name)) }
  | _ => none

def buildSourceDVPairPlansFrom :
    Nat → List RawStatement → List SourceDVPairPlan
  | _, [] => []
  | position, statement :: statements =>
      match sourceDVPairPlan? position statement with
      | none => buildSourceDVPairPlansFrom (position + 1) statements
      | some plan => plan :: buildSourceDVPairPlansFrom (position + 1) statements

def buildSourceDVPairPlans (statements : List RawStatement) :
    List SourceDVPairPlan :=
  buildSourceDVPairPlansFrom 0 statements

/-! ## Checkable pair-generation witnesses -/

/-- One pair-generation event retains the earlier name, the current name, and
the canonical unordered pair emitted for them.  The first two fields let
ordinary MM2 validate source order without implementing string comparison. -/
structure SourceDVPairWitness where
  earlier : String
  current : String
  pair : DVPair
deriving DecidableEq, Repr

def sourceDVPairWitness (earlier current : String) : SourceDVPairWitness :=
  { earlier
    current
    pair := canonicalDJPair earlier current }

def sourceDVPairWitnessesFrom (prior : List String) :
    List String → List SourceDVPairWitness
  | [] => []
  | current :: rest =>
      prior.map (fun earlier => sourceDVPairWitness earlier current) ++
        sourceDVPairWitnessesFrom (prior ++ [current]) rest

def sourceDVPairWitnesses (names : List String) :
    List SourceDVPairWitness :=
  sourceDVPairWitnessesFrom [] names

@[simp] theorem pair_projection_sourceDVPairWitnessesFrom
    (prior names : List String) :
    (sourceDVPairWitnessesFrom prior names).map SourceDVPairWitness.pair =
      allDistinctPairsFrom prior names := by
  induction names generalizing prior with
  | nil => rfl
  | cons current rest induction =>
      rw [sourceDVPairWitnessesFrom, allDistinctPairsFrom_cons,
        List.map_append, List.map_map, induction]
      rfl

@[simp] theorem pair_projection_sourceDVPairWitnesses
    (names : List String) :
    (sourceDVPairWitnesses names).map SourceDVPairWitness.pair =
      allDistinctPairs names := by
  exact pair_projection_sourceDVPairWitnessesFrom [] names

theorem sourceDVPairWitness_pair_orientation
    (earlier current : String) :
    (sourceDVPairWitness earlier current).pair = (earlier, current) ∨
      (sourceDVPairWitness earlier current).pair = (current, earlier) := by
  simp only [sourceDVPairWitness]
  unfold canonicalDJPair
  split <;> simp

def SourceDVPairPlan.witnesses (plan : SourceDVPairPlan) :
    List SourceDVPairWitness :=
  match plan.statement with
  | .djDecl _ names _ => sourceDVPairWitnesses (names.map (·.name))
  | _ => []

@[simp] theorem sourceDVPairPlan?_djDecl
    (position : Nat) (site terminator : LocatedByteSpan)
    (names : List LocatedName) :
    sourceDVPairPlan? position (.djDecl site names terminator) =
      some
        { position
          statement := .djDecl site names terminator
          pairs := allDistinctPairs (names.map (·.name)) } := by
  rfl

theorem mem_buildSourceDVPairPlansFrom_has_source_dj
    (start : Nat) (statements : List RawStatement)
    (plan : SourceDVPairPlan)
    (member : plan ∈ buildSourceDVPairPlansFrom start statements) :
    ∃ site names terminator,
      RawStatement.djDecl site names terminator ∈ statements ∧
      plan.statement = .djDecl site names terminator ∧
      plan.pairs = allDistinctPairs (names.map (·.name)) := by
  induction statements generalizing start with
  | nil => simp [buildSourceDVPairPlansFrom] at member
  | cons statement statements induction =>
      cases statement with
      | openScope site =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | closeScope site =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | constDecl site names terminator =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | varDecl site names terminator =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | djDecl site names terminator =>
          simp only [buildSourceDVPairPlansFrom, sourceDVPairPlan?,
            List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨site, names, terminator, by simp, rfl, rfl⟩
          · obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
                induction (start := start + 1) member
            exact ⟨sourceSite, sourceNames, sourceTerminator,
              List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | floating site label typecode variableName terminator =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | essential site label typecode body terminator =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | axiomatic site label typecode body terminator =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩
      | provable site label typecode body proof separator terminator =>
          obtain ⟨sourceSite, sourceNames, sourceTerminator,
              sourceMember, statementEq, pairsEq⟩ :=
            induction (start := start + 1) member
          exact ⟨sourceSite, sourceNames, sourceTerminator,
            List.mem_cons_of_mem _ sourceMember, statementEq, pairsEq⟩

/-- Every planned pair is generated by an actual `$d` statement in the exact
source list. -/
theorem pair_mem_buildSourceDVPairPlans_has_source_dj
    (statements : List RawStatement) (plan : SourceDVPairPlan)
    (planMember : plan ∈ buildSourceDVPairPlans statements)
    (pair : DVPair) (pairMember : pair ∈ plan.pairs) :
    ∃ site names terminator,
      RawStatement.djDecl site names terminator ∈ statements ∧
      pair ∈ allDistinctPairs (names.map (·.name)) := by
  obtain ⟨site, names, terminator, sourceMember, _, pairsEq⟩ :=
    mem_buildSourceDVPairPlansFrom_has_source_dj 0 statements plan planMember
  exact ⟨site, names, terminator, sourceMember, pairsEq ▸ pairMember⟩

/-- Every source-built plan's richer witnesses project to exactly the pair
sequence already used by the action planner. -/
theorem SourceDVPairPlan.witness_pair_projection_of_mem_build
    (statements : List RawStatement) (plan : SourceDVPairPlan)
    (member : plan ∈ buildSourceDVPairPlans statements) :
    plan.witnesses.map SourceDVPairWitness.pair = plan.pairs := by
  obtain ⟨site, names, terminator, _, statementEq, pairsEq⟩ :=
    mem_buildSourceDVPairPlansFrom_has_source_dj 0 statements plan member
  rw [SourceDVPairPlan.witnesses, statementEq,
    pair_projection_sourceDVPairWitnesses, pairsEq]

/-! ## A small authored planning GSLT -/

inductive PairPlanTerm where
  | pending (statements : List RawStatement)
  | finished (statements : List RawStatement) (plans : List SourceDVPairPlan)
deriving DecidableEq, Repr

inductive PairPlanStep : PairPlanTerm → PairPlanTerm → Prop where
  | compile (statements : List RawStatement) :
      PairPlanStep (.pending statements)
        (.finished statements (buildSourceDVPairPlans statements))

def pairPlanGSLT : GSLT where
  Term := PairPlanTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := PairPlanStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def pairPlanNTT :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    pairPlanGSLT

theorem pairPlanStep_exact
    (statements sourceStatements : List RawStatement)
    (plans : List SourceDVPairPlan)
    (step : PairPlanStep (.pending statements)
      (.finished sourceStatements plans)) :
    sourceStatements = statements ∧
      plans = buildSourceDVPairPlans statements := by
  cases step
  exact ⟨rfl, rfl⟩

/-- The exact source-derived planning step is classified by the native type
generated through OSLF from the planning GSLT. -/
theorem pairPlan_compile_inhabits_native_type
    (statements : List RawStatement) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF pairPlanGSLT).satisfies
      (.pending statements)
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
        pairPlanGSLT
        (.finished statements (buildSourceDVPairPlans statements))).pred := by
  rw [Mettapedia.OSLF.Framework.GSLTTypeSynthesis.satisfies_exactTargetNativeType_iff_step]
  exact PairPlanStep.compile statements

/-! ## Canonical packet encoding -/

def dvPairAtoms (pairs : List DVPair) : List Atom :=
  pairs.map stringPairAtom

def decodeDVPairAtoms : List Atom → Option (List DVPair)
  | [] => some []
  | atom :: atoms => do
      let pair <- decodeStringPairAtom atom
      let pairs <- decodeDVPairAtoms atoms
      pure (pair :: pairs)

@[simp] theorem decodeDVPairAtoms_dvPairAtoms (pairs : List DVPair) :
    decodeDVPairAtoms (dvPairAtoms pairs) = some pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      change decodeDVPairAtoms
        (stringPairAtom pair :: dvPairAtoms pairs) = some (pair :: pairs)
      simp only [decodeDVPairAtoms, decodeStringPairAtom_stringPairAtom,
        induction]
      rfl

def sourceDVPairPlanAtom (owner : Atom) (plan : SourceDVPairPlan) : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan", owner, natAtom plan.position,
      rawStatementAtom plan.statement, natAtom plan.pairs.length,
      .expression (dvPairAtoms plan.pairs)]

def decodeSourceDVPairPlanAtom (owner : Atom) :
    Atom → Option SourceDVPairPlan
  | .expression
      [.symbol "mm-source-dv-pair-plan", actualOwner, encodedPosition,
        encodedStatement, encodedCount, .expression encodedPairs] => do
      guard (actualOwner == owner)
      let position <- decodeNatAtom encodedPosition
      let statement <- decodeRawStatementAtom encodedStatement
      let expectedCount <- decodeNatAtom encodedCount
      let pairs <- decodeDVPairAtoms encodedPairs
      guard (pairs.length == expectedCount)
      pure { position, statement, pairs }
  | _ => none

@[simp] theorem decodeSourceDVPairPlanAtom_sourceDVPairPlanAtom
    (owner : Atom) (plan : SourceDVPairPlan) :
    decodeSourceDVPairPlanAtom owner (sourceDVPairPlanAtom owner plan) =
      some plan := by
  cases plan
  simp [decodeSourceDVPairPlanAtom, sourceDVPairPlanAtom]

theorem sourceDVPairPlanAtom_injective (owner : Atom) :
    Function.Injective (sourceDVPairPlanAtom owner) := by
  intro left right equal
  have decoded := congrArg (decodeSourceDVPairPlanAtom owner) equal
  simpa using decoded

def sourceDVPairPlanPacketAtom (owner : Atom)
    (plans : List SourceDVPairPlan) : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-packet", owner,
      .expression (plans.map (sourceDVPairPlanAtom owner))]

def decodeSourceDVPairPlanAtoms (owner : Atom) :
    List Atom → Option (List SourceDVPairPlan)
  | [] => some []
  | atom :: atoms => do
      let plan <- decodeSourceDVPairPlanAtom owner atom
      let plans <- decodeSourceDVPairPlanAtoms owner atoms
      pure (plan :: plans)

@[simp] theorem decodeSourceDVPairPlanAtoms_map
    (owner : Atom) (plans : List SourceDVPairPlan) :
    decodeSourceDVPairPlanAtoms owner
      (plans.map (sourceDVPairPlanAtom owner)) = some plans := by
  induction plans with
  | nil => rfl
  | cons plan plans induction =>
      simp [decodeSourceDVPairPlanAtoms, induction]

def decodeSourceDVPairPlanPacketAtom (owner : Atom) :
    Atom → Option (List SourceDVPairPlan)
  | .expression
      [.symbol "mm-source-dv-pair-plan-packet", actualOwner,
        .expression encodedPlans] => do
      guard (actualOwner == owner)
      decodeSourceDVPairPlanAtoms owner encodedPlans
  | _ => none

@[simp] theorem decodeSourceDVPairPlanPacketAtom_encoded
    (owner : Atom) (plans : List SourceDVPairPlan) :
    decodeSourceDVPairPlanPacketAtom owner
      (sourceDVPairPlanPacketAtom owner plans) = some plans := by
  simp [decodeSourceDVPairPlanPacketAtom, sourceDVPairPlanPacketAtom]

theorem sourceDVPairPlanPacketAtom_injective (owner : Atom) :
    Function.Injective (sourceDVPairPlanPacketAtom owner) := by
  intro left right equal
  have decoded := congrArg (decodeSourceDVPairPlanPacketAtom owner) equal
  simpa using decoded

/-! ## Passive linked rows for ordinary MM2 execution -/

def sourceDVPairPlanOwner (owner : Atom) (statementPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-owner", owner,
      natAtom statementPosition]

/-- Stable occurrence identity for one pair inside one source `$d` statement.
It is suitable as an opaque append cursor in both the global occurrence ledger
and the scope-local activity ledger. -/
def sourceDVPairOccurrenceKey (owner : Atom)
    (statementPosition pairPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-occurrence", owner,
      natAtom statementPosition, natAtom pairPosition]

def decodeSourceDVPairOccurrenceKey (owner : Atom) :
    Atom → Option (Nat × Nat)
  | .expression
      [.symbol "mm-source-dv-pair-occurrence", actualOwner,
        encodedStatementPosition, encodedPairPosition] => do
      guard (actualOwner == owner)
      let statementPosition <- decodeNatAtom encodedStatementPosition
      let pairPosition <- decodeNatAtom encodedPairPosition
      pure (statementPosition, pairPosition)
  | _ => none

@[simp] theorem decodeSourceDVPairOccurrenceKey_encoded
    (owner : Atom) (statementPosition pairPosition : Nat) :
    decodeSourceDVPairOccurrenceKey owner
      (sourceDVPairOccurrenceKey owner statementPosition pairPosition) =
        some (statementPosition, pairPosition) := by
  simp [decodeSourceDVPairOccurrenceKey, sourceDVPairOccurrenceKey]

theorem sourceDVPairOccurrenceKey_injective (owner : Atom) :
    Function.Injective fun positions : Nat × Nat =>
      sourceDVPairOccurrenceKey owner positions.1 positions.2 := by
  intro left right equal
  have decoded := congrArg (decodeSourceDVPairOccurrenceKey owner) equal
  simpa using decoded

def decodeSourceDVPairPlanOwner (owner : Atom) : Atom → Option Nat
  | .expression
      [.symbol "mm-source-dv-pair-plan-owner", actualOwner,
        encodedPosition] => do
      guard (actualOwner == owner)
      decodeNatAtom encodedPosition
  | _ => none

@[simp] theorem decodeSourceDVPairPlanOwner_encoded
    (owner : Atom) (statementPosition : Nat) :
    decodeSourceDVPairPlanOwner owner
      (sourceDVPairPlanOwner owner statementPosition) =
        some statementPosition := by
  simp [decodeSourceDVPairPlanOwner, sourceDVPairPlanOwner]

def sourceDVPairPlanHeaderAtom (owner : Atom)
    (plan : SourceDVPairPlan) : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-header", owner,
      natAtom plan.position, rawStatementAtom plan.statement,
      natAtom plan.pairs.length]

def sourceDVPairPlanLinkAtom (owner : Atom) (statementPosition pairPosition : Nat)
    (pair : DVPair) : Atom :=
  .expression
    [.symbol "mm-linked-row",
      sourceDVPairPlanOwner owner statementPosition,
      .symbol "source-dv-pair-plan", natAtom pairPosition,
      natAtom (pairPosition + 1), stringPairAtom pair]

def sourceDVPairPlanFrontierAtom (owner : Atom)
    (statementPosition pairPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-plan-frontier",
      sourceDVPairPlanOwner owner statementPosition, natAtom pairPosition]

def sourceDVPairWitnessAtom (witness : SourceDVPairWitness) : Atom :=
  .expression
    [.symbol "mm-source-dv-pair-witness", stringAtom witness.earlier,
      stringAtom witness.current, stringPairAtom witness.pair]

def decodeSourceDVPairWitnessAtom : Atom → Option SourceDVPairWitness
  | .expression
      [.symbol "mm-source-dv-pair-witness", encodedEarlier,
        encodedCurrent, encodedPair] => do
      let earlier <- decodeStringAtom encodedEarlier
      let current <- decodeStringAtom encodedCurrent
      let pair <- decodeStringPairAtom encodedPair
      pure { earlier, current, pair }
  | _ => none

@[simp] theorem decodeSourceDVPairWitnessAtom_encoded
    (witness : SourceDVPairWitness) :
    decodeSourceDVPairWitnessAtom (sourceDVPairWitnessAtom witness) =
      some witness := by
  cases witness
  simp [decodeSourceDVPairWitnessAtom, sourceDVPairWitnessAtom]

def sourceDVPairWitnessLinkAtom (owner : Atom)
    (statementPosition pairPosition : Nat)
    (witness : SourceDVPairWitness) : Atom :=
  .expression
    [.symbol "mm-linked-row",
      sourceDVPairPlanOwner owner statementPosition,
      .symbol "source-dv-pair-witness", natAtom pairPosition,
      natAtom (pairPosition + 1), sourceDVPairWitnessAtom witness]

def sourceDVPairWitnessRowsFrom (owner : Atom) (statementPosition : Nat) :
    Nat → List SourceDVPairWitness → List Atom
  | _, [] => []
  | pairPosition, witness :: witnesses =>
      sourceDVPairWitnessLinkAtom owner statementPosition pairPosition
          witness ::
        sourceDVPairWitnessRowsFrom owner statementPosition
          (pairPosition + 1) witnesses

def SourceDVPairPlan.witnessRows (owner : Atom)
    (plan : SourceDVPairPlan) : List Atom :=
  sourceDVPairWitnessRowsFrom owner plan.position 0 plan.witnesses

def decodeSourceDVPairWitnessLinkAtom (owner : Atom)
    (statementPosition pairPosition : Nat) :
    Atom → Option SourceDVPairWitness
  | .expression
      [.symbol "mm-linked-row", actualPlanOwner,
        .symbol "source-dv-pair-witness", encodedPosition, encodedNext,
        encodedWitness] => do
      guard (actualPlanOwner == sourceDVPairPlanOwner owner statementPosition)
      guard (encodedPosition == natAtom pairPosition)
      guard (encodedNext == natAtom (pairPosition + 1))
      decodeSourceDVPairWitnessAtom encodedWitness
  | _ => none

@[simp] theorem decodeSourceDVPairWitnessLinkAtom_encoded
    (owner : Atom) (statementPosition pairPosition : Nat)
    (witness : SourceDVPairWitness) :
    decodeSourceDVPairWitnessLinkAtom owner statementPosition pairPosition
      (sourceDVPairWitnessLinkAtom owner statementPosition pairPosition
        witness) = some witness := by
  simp [decodeSourceDVPairWitnessLinkAtom, sourceDVPairWitnessLinkAtom]

@[simp] theorem sourceDVPairWitnessRowsFrom_length (owner : Atom)
    (statementPosition pairPosition : Nat)
    (witnesses : List SourceDVPairWitness) :
    (sourceDVPairWitnessRowsFrom owner statementPosition pairPosition
      witnesses).length = witnesses.length := by
  induction witnesses generalizing pairPosition with
  | nil => rfl
  | cons witness witnesses induction =>
      simp [sourceDVPairWitnessRowsFrom, induction]

@[simp] theorem SourceDVPairPlan.witnessRows_length (owner : Atom)
    (plan : SourceDVPairPlan) :
    (plan.witnessRows owner).length = plan.witnesses.length := by
  exact sourceDVPairWitnessRowsFrom_length owner plan.position 0 plan.witnesses

@[simp] theorem sourceDVPairWitnessRowsFrom_all_proofNeutral
    (owner : Atom) (statementPosition pairPosition : Nat)
    (witnesses : List SourceDVPairWitness) :
    (sourceDVPairWitnessRowsFrom owner statementPosition pairPosition
      witnesses).all isProofNeutralInitialAtom = true := by
  induction witnesses generalizing pairPosition with
  | nil => rfl
  | cons witness witnesses induction =>
      simp [sourceDVPairWitnessRowsFrom, sourceDVPairWitnessLinkAtom,
        sourceDVPairPlanOwner, sourceDVPairWitnessAtom,
        isProofNeutralInitialAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
        isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
        induction]

@[simp] theorem SourceDVPairPlan.witnessRows_all_proofNeutral
    (owner : Atom) (plan : SourceDVPairPlan) :
    (plan.witnessRows owner).all isProofNeutralInitialAtom = true := by
  exact sourceDVPairWitnessRowsFrom_all_proofNeutral owner plan.position 0
    plan.witnesses

def sourceDVPairPlanRowsFrom (owner : Atom) (statementPosition : Nat) :
    Nat → List DVPair → List Atom
  | pairPosition, [] =>
      [sourceDVPairPlanFrontierAtom owner statementPosition pairPosition]
  | pairPosition, pair :: pairs =>
      sourceDVPairPlanLinkAtom owner statementPosition pairPosition pair ::
        sourceDVPairPlanRowsFrom owner statementPosition
          (pairPosition + 1) pairs

def decodeSourceDVPairPlanLinkAtom (owner : Atom)
    (statementPosition pairPosition : Nat) : Atom → Option DVPair
  | .expression
      [.symbol "mm-linked-row", actualPlanOwner,
        .symbol "source-dv-pair-plan", encodedPosition, encodedNext,
        encodedPair] => do
      guard (actualPlanOwner == sourceDVPairPlanOwner owner statementPosition)
      guard (encodedPosition == natAtom pairPosition)
      guard (encodedNext == natAtom (pairPosition + 1))
      decodeStringPairAtom encodedPair
  | _ => none

@[simp] theorem decodeSourceDVPairPlanLinkAtom_encoded
    (owner : Atom) (statementPosition pairPosition : Nat) (pair : DVPair) :
    decodeSourceDVPairPlanLinkAtom owner statementPosition pairPosition
      (sourceDVPairPlanLinkAtom owner statementPosition pairPosition pair) =
        some pair := by
  simp [decodeSourceDVPairPlanLinkAtom, sourceDVPairPlanLinkAtom]

def decodeSourceDVPairPlanLinkAtomAny (owner : Atom) :
    Atom → Option (Nat × Nat × DVPair)
  | .expression
      [.symbol "mm-linked-row", encodedPlanOwner,
        .symbol "source-dv-pair-plan", encodedPosition, encodedNext,
        encodedPair] => do
      let statementPosition <- decodeSourceDVPairPlanOwner owner encodedPlanOwner
      let pairPosition <- decodeNatAtom encodedPosition
      guard (encodedNext == natAtom (pairPosition + 1))
      let pair <- decodeStringPairAtom encodedPair
      pure (statementPosition, pairPosition, pair)
  | _ => none

@[simp] theorem decodeSourceDVPairPlanLinkAtomAny_encoded
    (owner : Atom) (statementPosition pairPosition : Nat) (pair : DVPair) :
    decodeSourceDVPairPlanLinkAtomAny owner
      (sourceDVPairPlanLinkAtom owner statementPosition pairPosition pair) =
        some (statementPosition, pairPosition, pair) := by
  simp [decodeSourceDVPairPlanLinkAtomAny, sourceDVPairPlanLinkAtom]

def SourceDVPairPlan.rows (owner : Atom) (plan : SourceDVPairPlan) :
    List Atom :=
  sourceDVPairPlanHeaderAtom owner plan ::
    sourceDVPairPlanRowsFrom owner plan.position 0 plan.pairs

@[simp] theorem sourceDVPairPlanRowsFrom_all_proofNeutral
    (owner : Atom) (statementPosition pairPosition : Nat)
    (pairs : List DVPair) :
    (sourceDVPairPlanRowsFrom owner statementPosition pairPosition pairs).all
      isProofNeutralInitialAtom = true := by
  induction pairs generalizing pairPosition with
  | nil =>
      simp [sourceDVPairPlanRowsFrom, sourceDVPairPlanFrontierAtom,
        sourceDVPairPlanOwner, isProofNeutralInitialAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
        isVerifierTerminalObservation, isVerifierOwnedInternalRowShape]
  | cons pair pairs induction =>
      simp [sourceDVPairPlanRowsFrom, sourceDVPairPlanLinkAtom,
        sourceDVPairPlanOwner, isProofNeutralInitialAtom,
        Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
        isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
        induction]

@[simp] theorem SourceDVPairPlan.rows_all_proofNeutral
    (owner : Atom) (plan : SourceDVPairPlan) :
    (plan.rows owner).all isProofNeutralInitialAtom = true := by
  simp [SourceDVPairPlan.rows, sourceDVPairPlanHeaderAtom,
    isProofNeutralInitialAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape]

theorem mem_sourceDVPairPlanRowsFrom_link_has_pair
    (owner : Atom)
    (rowStatementPosition statementPosition start pairPosition : Nat)
    (pairs : List DVPair) (pair : DVPair)
    (member :
      sourceDVPairPlanLinkAtom owner rowStatementPosition pairPosition pair ∈
        sourceDVPairPlanRowsFrom owner statementPosition start pairs) :
    pair ∈ pairs := by
  induction pairs generalizing start with
  | nil =>
      simp [sourceDVPairPlanRowsFrom, sourceDVPairPlanLinkAtom,
        sourceDVPairPlanFrontierAtom, sourceDVPairPlanOwner] at member
  | cons next pairs induction =>
      simp only [sourceDVPairPlanRowsFrom, List.mem_cons] at member
      rcases member with same | later
      · have decoded := congrArg
          (decodeSourceDVPairPlanLinkAtomAny owner) same
        simp only [decodeSourceDVPairPlanLinkAtomAny_encoded,
          Option.some.injEq] at decoded
        have pairEq : pair = next :=
          congrArg (fun value : Nat × Nat × DVPair => value.2.2) decoded
        exact List.mem_cons.mpr (Or.inl pairEq)
      · exact List.mem_cons_of_mem next (induction (start := start + 1) later)

def sourceDVPairPlanRows (owner : Atom)
    (plans : List SourceDVPairPlan) : List Atom :=
  plans.flatMap (SourceDVPairPlan.rows owner)

def sourceDVPairPlanWitnessRows (owner : Atom)
    (plans : List SourceDVPairPlan) : List Atom :=
  plans.flatMap (SourceDVPairPlan.witnessRows owner)

@[simp] theorem sourceDVPairPlanRows_all_proofNeutral
    (owner : Atom) (plans : List SourceDVPairPlan) :
    (sourceDVPairPlanRows owner plans).all isProofNeutralInitialAtom = true := by
  induction plans with
  | nil => rfl
  | cons plan plans _ =>
      simp [sourceDVPairPlanRows]

/-! ## Source-relative admission -/

/-- Pair plans are admitted only beside a successful authored source fold. -/
structure AdmittedSourceDVPairPlans (owner : Atom)
    (statements : List RawStatement) where
  source : AdmittedSourceActionPlans owner statements
  plans : List SourceDVPairPlan
  exact : plans = buildSourceDVPairPlans statements

def admitSourceDVPairPlans {owner : Atom} {statements : List RawStatement}
    (source : AdmittedSourceActionPlans owner statements) :
    AdmittedSourceDVPairPlans owner statements :=
  { source
    plans := buildSourceDVPairPlans statements
    exact := rfl }

inductive SourceDVPairPlanInputError where
  | encoding
  | notSourceDerived
deriving DecidableEq, Repr

/-- Representation decoding does not grant authority.  An accepted packet is
discarded in favor of the exact plans recomputed from the admitted source. -/
def admitSourceDVPairPlanPacket {owner : Atom}
    {statements : List RawStatement}
    (source : AdmittedSourceActionPlans owner statements) (packet : Atom) :
    Except SourceDVPairPlanInputError
      (AdmittedSourceDVPairPlans owner statements) :=
  match decodeSourceDVPairPlanPacketAtom owner packet with
  | none => .error .encoding
  | some decoded =>
      if decoded = buildSourceDVPairPlans statements then
        .ok (admitSourceDVPairPlans source)
      else
        .error .notSourceDerived

def AdmittedSourceDVPairPlans.packet {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) : Atom :=
  sourceDVPairPlanPacketAtom owner input.plans

def AdmittedSourceDVPairPlans.rows {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) : List Atom :=
  sourceDVPairPlanRows owner input.plans

def AdmittedSourceDVPairPlans.witnessRows {owner : Atom}
    {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) : List Atom :=
  sourceDVPairPlanWitnessRows owner input.plans

@[simp] theorem AdmittedSourceDVPairPlans.rows_all_proofNeutral
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) :
    input.rows.all isProofNeutralInitialAtom = true := by
  exact sourceDVPairPlanRows_all_proofNeutral owner input.plans

@[simp] theorem sourceDVPairPlanWitnessRows_all_proofNeutral
    (owner : Atom) (plans : List SourceDVPairPlan) :
    (sourceDVPairPlanWitnessRows owner plans).all
      isProofNeutralInitialAtom = true := by
  induction plans with
  | nil => rfl
  | cons plan plans _ =>
      simp [sourceDVPairPlanWitnessRows]

@[simp] theorem AdmittedSourceDVPairPlans.witnessRows_all_proofNeutral
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements) :
    input.witnessRows.all isProofNeutralInitialAtom = true := by
  exact sourceDVPairPlanWitnessRows_all_proofNeutral owner input.plans

@[simp] theorem admitSourceDVPairPlanPacket_canonical
    {owner : Atom} {statements : List RawStatement}
    (source : AdmittedSourceActionPlans owner statements) :
    admitSourceDVPairPlanPacket source
      (sourceDVPairPlanPacketAtom owner
        (buildSourceDVPairPlans statements)) =
      .ok (admitSourceDVPairPlans source) := by
  simp [admitSourceDVPairPlanPacket]

/-- A decoded packet that differs from the source-derived plan is rejected,
even when every atom in the packet is representationally canonical. -/
theorem admitSourceDVPairPlanPacket_rejects_non_source
    {owner : Atom} {statements : List RawStatement}
    (source : AdmittedSourceActionPlans owner statements)
    (packet : Atom) (decoded : List SourceDVPairPlan)
    (decodes : decodeSourceDVPairPlanPacketAtom owner packet = some decoded)
    (different : decoded ≠ buildSourceDVPairPlans statements) :
    admitSourceDVPairPlanPacket source packet =
      .error .notSourceDerived := by
  simp [admitSourceDVPairPlanPacket, decodes, different]

/-- Every pair row exposed by the admitted target packet reconstructs a pair
from an actual source `$d` occurrence. -/
theorem AdmittedSourceDVPairPlans.link_mem_rows_has_source_dj
    {owner : Atom} {statements : List RawStatement}
    (input : AdmittedSourceDVPairPlans owner statements)
    (statementPosition pairPosition : Nat) (pair : DVPair)
    (member :
      sourceDVPairPlanLinkAtom owner statementPosition pairPosition pair ∈
        input.rows) :
    ∃ site names terminator,
      RawStatement.djDecl site names terminator ∈ statements ∧
      pair ∈ allDistinctPairs (names.map (·.name)) := by
  simp only [AdmittedSourceDVPairPlans.rows, sourceDVPairPlanRows,
    List.mem_flatMap] at member
  obtain ⟨plan, planMember, rowMember⟩ := member
  simp only [SourceDVPairPlan.rows, List.mem_cons] at rowMember
  rcases rowMember with headerEqual | rowMember
  · simp [sourceDVPairPlanHeaderAtom, sourceDVPairPlanLinkAtom,
      sourceDVPairPlanOwner] at headerEqual
  · have pairMember :=
      mem_sourceDVPairPlanRowsFrom_link_has_pair owner statementPosition
        plan.position 0 pairPosition plan.pairs pair rowMember
    rw [input.exact] at planMember
    exact pair_mem_buildSourceDVPairPlans_has_source_dj statements plan
      planMember pair pairMember

/-! ## Positive and negative controls -/

private def canarySpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "pair-plan.mm", start, stop }

private def canaryName (name : String) (start : Nat) : LocatedName :=
  { span := canarySpan start (start + 1), name }

private def canaryStatement : RawStatement :=
  .djDecl (canarySpan 0 2)
    [canaryName "x" 3, canaryName "y" 5, canaryName "z" 7]
    (canarySpan 9 11)

private def canaryPlan : SourceDVPairPlan :=
  { position := 0
    statement := canaryStatement
    pairs := [("x", "y"), ("x", "z"), ("y", "z")] }

example : buildSourceDVPairPlans [canaryStatement] = [canaryPlan] := by
  decide +kernel

example (owner : Atom) :
    decodeSourceDVPairPlanPacketAtom owner
      (sourceDVPairPlanPacketAtom owner [canaryPlan]) = some [canaryPlan] := by
  simp

/-- A well-encoded fabricated plan is representationally valid.  The separate
source-relative comparison in `admitSourceDVPairPlanPacket` is therefore
substantive rather than a disguised decoder round trip. -/
theorem fabricated_plan_decodes_without_source_authority (owner : Atom) :
    decodeSourceDVPairPlanPacketAtom owner
      (sourceDVPairPlanPacketAtom owner
        [{ position := 41
           statement := canaryStatement
           pairs := [("ghost", "pair")] }]) =
      some
        [{ position := 41
           statement := canaryStatement
           pairs := [("ghost", "pair")] }] := by
  simp

/-- Owner substitution is rejected before any plan is exposed. -/
theorem packet_rejects_wrong_owner (owner other : Atom)
    (different : other ≠ owner) :
    decodeSourceDVPairPlanPacketAtom owner
      (sourceDVPairPlanPacketAtom other [canaryPlan]) = none := by
  simp [decodeSourceDVPairPlanPacketAtom, sourceDVPairPlanPacketAtom,
    different]

section AxiomAudit

#print axioms mem_buildSourceDVPairPlansFrom_has_source_dj
#print axioms pair_mem_buildSourceDVPairPlans_has_source_dj
#print axioms pair_projection_sourceDVPairWitnesses
#print axioms sourceDVPairWitness_pair_orientation
#print axioms SourceDVPairPlan.witness_pair_projection_of_mem_build
#print axioms pairPlanStep_exact
#print axioms pairPlan_compile_inhabits_native_type
#print axioms decodeSourceDVPairPlanAtom_sourceDVPairPlanAtom
#print axioms sourceDVPairPlanAtom_injective
#print axioms decodeSourceDVPairPlanPacketAtom_encoded
#print axioms sourceDVPairPlanPacketAtom_injective
#print axioms mem_sourceDVPairPlanRowsFrom_link_has_pair
#print axioms decodeSourceDVPairOccurrenceKey_encoded
#print axioms sourceDVPairOccurrenceKey_injective
#print axioms decodeSourceDVPairWitnessAtom_encoded
#print axioms decodeSourceDVPairWitnessLinkAtom_encoded
#print axioms SourceDVPairPlan.witnessRows_all_proofNeutral
#print axioms AdmittedSourceDVPairPlans.rows_all_proofNeutral
#print axioms AdmittedSourceDVPairPlans.witnessRows_all_proofNeutral
#print axioms admitSourceDVPairPlanPacket_canonical
#print axioms admitSourceDVPairPlanPacket_rejects_non_source
#print axioms AdmittedSourceDVPairPlans.link_mem_rows_has_source_dj
#print axioms fabricated_plan_decodes_without_source_authority
#print axioms packet_rejects_wrong_owner

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
