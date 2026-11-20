import Mettapedia.Languages.MeTTa.PrimeCandidates.Strategies.NativeWeightedHandler

/-!
# The weighted history handler on a concrete 161-event run

Kernel-checked checkpoints of the actual `Cursor.resume` computation for the
weighted current-data/history handler, with the observation readouts folded
through the existing suffix-concatenation law. Each checkpoint equality is
admitted by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.History.Controls

open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.LanguageDef
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

abbrev required := RetainedInvocation.Examples.OwnData.required
abbrev needed := RetainedInvocation.Examples.OwnData.needed
abbrev context := RetainedInvocation.Examples.OwnData.context

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (action : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (required action point.world)) :=
  RetainedInvocation.Examples.OwnData.permissionDecision point action

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  RetainedInvocation.Examples.OwnData.admissionDecision point

abbrev act := CurrentData.Controls.act
abbrev number := Weighted.Controls.number

/-- The rich outer callback actually invokes an authored score service. Its
nested coefficient is zero, rather than an absent production. -/
def annotation (production : AuthoredProduction) : Option Coefficient :=
  if production.head = "choose" then
    some (.rich ⟨0, 0, 0,
      .emit 5 (.call (.source Weighted.Controls.scoreProgram []) (.head (.expression [.symbol "score"]))),
      ids, Fin.elim0, Fin.elim0⟩)
  else if production.head = "score" then some (.authored (Weighted.Controls.integer 0)) else none

abbrev source := CurrentData.sourceProvider annotation number revocationWorlds required needed act 407
abbrev target := CurrentData.targetProvider annotation number revocationWorlds required needed act 407
abbrev charge : Cursor.Charge source := CurrentData.sourceCharge annotation number revocationWorlds required needed act 407
abbrev reader := SourceProducerCardinality.CallingModes.client .direct Provider.Item
abbrev notice : OperationCostProtocol.Indexed.Notice (NativeControlCursor.protocol Provider.Item)
    RetainedInvocation.OwnData.Refused := CurrentData.notice
abbrev client := OperationCostProtocol.Indexed.client reader notice
abbrev Saved := Nat × Cursor.Outcome source client ()

def packet := CurrentData.modePacket annotation number revocationWorlds required needed act .direct 407
  (Provider.initial Weighted.Controls.roots, context) (OperationCostProtocol.initial CurrentData.profile 1000)

def run (fuel : Nat := 400) : Saved := Cursor.advance source client charge fuel packet

def history (fuel : Nat := 400) := NativeControlCursor.ProtocolHistory.advanceHistory source client charge fuel packet

def factorSummary (factor : Factor) : String × Nat × Int :=
  (factor.production.head, factor.production.row.index,
    match factor.value with | .grounded (.int number) => number | _ => -1)

def factors (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 factorValue fuel (0, .paused packet)).toList.map factorSummary

def effects (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 effectValue fuel (0, .paused packet)).toList

def caches (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 cacheValue fuel (0, .paused packet)).toList

def ledger (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 (ledgerBlock 407) fuel (0, .paused packet)).toList

def word (fuel : Nat := 400) :=
  (PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice
    407 FreeMonoid.of fuel (0, .paused packet)).toList

def rowsAt (saved : Saved) : Option (List Provider.Item) :=
  match saved.2 with | .done ⟨(), .inl rows, _⟩ => some rows | _ => none

def wordsAt (saved : Saved) := (rowsAt saved).map fun rows =>
  rows.map fun (item : Provider.Item) => item.1.2.toList.map factorSummary

def rows := rowsAt (run 400)
def words := wordsAt (run 400)

def stateOf (saved : Saved) : Provider.Inventory × CurrentData.Context revocationWorlds (Entry := Nat) (width := 3) :=
  match saved.2 with | .paused packet => packet.2.2.1 | .done result => result.2.2.1

def tag : View → Nat
  | .inert => 0
  | .finish => 1
  | .refused _ => 2
  | .accepted _ _ none => 3
  | .accepted _ _ (some inspected) =>
      if !inspected.factors.toList.isEmpty then 4 else
      match inspected.completed with
      | some completed => match completed.kind with | .production => 5 | .delivery => 6
      | none => if inspected.effect.isSome then 7 else if inspected.returned.isSome then 8
          else if inspected.firings.isEmpty then 9 else 10

def recorded (fuel capacity : Nat) :=
  (observedAdvance annotation number revocationWorlds required needed act reader notice 407 fuel packet
    (some (Recording.Prefix.initial capacity))).2


/-! The fixture certificates use the existing cursor transitions. Data fields
are materialized once; function closures stay shared. Their generated terms and
local equality proofs are checked by Lean's ordinary kernel. -/

open Lean Meta in
private partial def normalizeCutData (input : Expr) : MetaM Expr := do
  let rec visit (expression : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache expression fun _ => Core.withIncRecDepth do
      if (← isType expression) || (← isProof expression) then return expression
      let expression ← whnf expression
      match expression with
      | .lam .. | .forallE .. => return expression
      | .app .. =>
          let head := expression.getAppFn
          let mut arguments := expression.getAppArgs
          let info ← getFunInfoNArgs head arguments.size
          for index in [:arguments.size] do
            if index >= info.paramInfo.size || info.paramInfo[index]!.isExplicit then
              arguments ← arguments.modifyM index visit
          return mkAppN head arguments
      | .proj owner field value => return mkProj owner field (← visit value)
      | _ => return expression
  visit input |>.run

open Lean Meta Elab Term in
elab "normalized_cursor_cut% " value:term : term <= expected => do
  let expression ← elabTerm value expected
  Term.synthesizeSyntheticMVarsNoPostponing
  normalizeCutData (← instantiateMVars expression)

private noncomputable def cut0 : Saved := normalized_cursor_cut% (0, .paused packet)

open Lean Meta Elab Tactic in
elab "checked_cut_rfl" : tactic => withMainContext do
  match ← getGoals with
  | [] => return
  | goal :: _ =>
      let target ← whnf (← instantiateMVars (← goal.getType))
      unless target.isAppOfArity ``Eq 3 do
        throwError "an equality is required, got {target}"
      goal.assign (← mkEqRefl target.getAppArgs[2]!)
      replaceMainGoal []
private noncomputable def cut1 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut0)
private theorem step1 : Cursor.resume source client charge 1 cut0 = cut1 := by checked_cut_rfl
private noncomputable def cut2 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut1)
private theorem step2 : Cursor.resume source client charge 1 cut1 = cut2 := by checked_cut_rfl
private noncomputable def cut3 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut2)
private theorem step3 : Cursor.resume source client charge 1 cut2 = cut3 := by checked_cut_rfl
private noncomputable def cut4 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut3)
private theorem step4 : Cursor.resume source client charge 1 cut3 = cut4 := by checked_cut_rfl
private noncomputable def cut5 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut4)
private theorem step5 : Cursor.resume source client charge 1 cut4 = cut5 := by checked_cut_rfl
private noncomputable def cut6 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut5)
private theorem step6 : Cursor.resume source client charge 1 cut5 = cut6 := by checked_cut_rfl
private noncomputable def cut7 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut6)
private theorem step7 : Cursor.resume source client charge 1 cut6 = cut7 := by checked_cut_rfl
private noncomputable def cut8 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut7)
private theorem step8 : Cursor.resume source client charge 1 cut7 = cut8 := by checked_cut_rfl
private noncomputable def cut9 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut8)
private theorem step9 : Cursor.resume source client charge 1 cut8 = cut9 := by checked_cut_rfl
private noncomputable def cut10 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut9)
private theorem step10 : Cursor.resume source client charge 1 cut9 = cut10 := by checked_cut_rfl
private noncomputable def cut11 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut10)
private theorem step11 : Cursor.resume source client charge 1 cut10 = cut11 := by checked_cut_rfl
private noncomputable def cut12 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut11)
private theorem step12 : Cursor.resume source client charge 1 cut11 = cut12 := by checked_cut_rfl
private noncomputable def cut13 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut12)
private theorem step13 : Cursor.resume source client charge 1 cut12 = cut13 := by checked_cut_rfl
private noncomputable def cut14 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut13)
private theorem step14 : Cursor.resume source client charge 1 cut13 = cut14 := by checked_cut_rfl
private noncomputable def cut15 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut14)
private theorem step15 : Cursor.resume source client charge 1 cut14 = cut15 := by checked_cut_rfl
private noncomputable def cut16 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut15)
private theorem step16 : Cursor.resume source client charge 1 cut15 = cut16 := by checked_cut_rfl
private noncomputable def cut17 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut16)
private theorem step17 : Cursor.resume source client charge 1 cut16 = cut17 := by checked_cut_rfl
private noncomputable def cut18 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut17)
private theorem step18 : Cursor.resume source client charge 1 cut17 = cut18 := by checked_cut_rfl
private noncomputable def cut19 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut18)
private theorem step19 : Cursor.resume source client charge 1 cut18 = cut19 := by checked_cut_rfl
private noncomputable def cut20 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut19)
private theorem step20 : Cursor.resume source client charge 1 cut19 = cut20 := by checked_cut_rfl
private noncomputable def cut21 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut20)
private theorem step21 : Cursor.resume source client charge 1 cut20 = cut21 := by checked_cut_rfl
private noncomputable def cut22 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut21)
private theorem step22 : Cursor.resume source client charge 1 cut21 = cut22 := by checked_cut_rfl
private noncomputable def cut23 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut22)
private theorem step23 : Cursor.resume source client charge 1 cut22 = cut23 := by checked_cut_rfl
private noncomputable def cut24 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut23)
private theorem step24 : Cursor.resume source client charge 1 cut23 = cut24 := by checked_cut_rfl
private noncomputable def cut25 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut24)
private theorem step25 : Cursor.resume source client charge 1 cut24 = cut25 := by checked_cut_rfl
private noncomputable def cut26 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut25)
private theorem step26 : Cursor.resume source client charge 1 cut25 = cut26 := by checked_cut_rfl
private noncomputable def cut27 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut26)
private theorem step27 : Cursor.resume source client charge 1 cut26 = cut27 := by checked_cut_rfl
private noncomputable def cut28 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut27)
private theorem step28 : Cursor.resume source client charge 1 cut27 = cut28 := by checked_cut_rfl
private noncomputable def cut29 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut28)
private theorem step29 : Cursor.resume source client charge 1 cut28 = cut29 := by checked_cut_rfl
private noncomputable def cut30 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut29)
private theorem step30 : Cursor.resume source client charge 1 cut29 = cut30 := by checked_cut_rfl
private noncomputable def cut31 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut30)
private theorem step31 : Cursor.resume source client charge 1 cut30 = cut31 := by checked_cut_rfl
private noncomputable def cut32 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut31)
private theorem step32 : Cursor.resume source client charge 1 cut31 = cut32 := by checked_cut_rfl
private noncomputable def cut33 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut32)
private theorem step33 : Cursor.resume source client charge 1 cut32 = cut33 := by checked_cut_rfl
private noncomputable def cut34 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut33)
private theorem step34 : Cursor.resume source client charge 1 cut33 = cut34 := by checked_cut_rfl
private noncomputable def cut35 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut34)
private theorem step35 : Cursor.resume source client charge 1 cut34 = cut35 := by checked_cut_rfl
private noncomputable def cut36 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut35)
private theorem step36 : Cursor.resume source client charge 1 cut35 = cut36 := by checked_cut_rfl
private noncomputable def cut37 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut36)
private theorem step37 : Cursor.resume source client charge 1 cut36 = cut37 := by checked_cut_rfl
private noncomputable def cut38 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut37)
private theorem step38 : Cursor.resume source client charge 1 cut37 = cut38 := by checked_cut_rfl
private noncomputable def cut39 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut38)
private theorem step39 : Cursor.resume source client charge 1 cut38 = cut39 := by checked_cut_rfl
private noncomputable def cut40 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut39)
private theorem step40 : Cursor.resume source client charge 1 cut39 = cut40 := by checked_cut_rfl
private noncomputable def cut41 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut40)
private theorem step41 : Cursor.resume source client charge 1 cut40 = cut41 := by checked_cut_rfl
private noncomputable def cut42 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut41)
private theorem step42 : Cursor.resume source client charge 1 cut41 = cut42 := by checked_cut_rfl
private noncomputable def cut43 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut42)
private theorem step43 : Cursor.resume source client charge 1 cut42 = cut43 := by checked_cut_rfl
private noncomputable def cut44 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut43)
private theorem step44 : Cursor.resume source client charge 1 cut43 = cut44 := by checked_cut_rfl
private noncomputable def cut45 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut44)
private theorem step45 : Cursor.resume source client charge 1 cut44 = cut45 := by checked_cut_rfl
private noncomputable def cut46 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut45)
private theorem step46 : Cursor.resume source client charge 1 cut45 = cut46 := by checked_cut_rfl
private noncomputable def cut47 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut46)
private theorem step47 : Cursor.resume source client charge 1 cut46 = cut47 := by checked_cut_rfl
private noncomputable def cut48 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut47)
private theorem step48 : Cursor.resume source client charge 1 cut47 = cut48 := by checked_cut_rfl
private noncomputable def cut49 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut48)
private theorem step49 : Cursor.resume source client charge 1 cut48 = cut49 := by checked_cut_rfl
private noncomputable def cut50 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut49)
private theorem step50 : Cursor.resume source client charge 1 cut49 = cut50 := by checked_cut_rfl
private noncomputable def cut51 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut50)
private theorem step51 : Cursor.resume source client charge 1 cut50 = cut51 := by checked_cut_rfl
private noncomputable def cut52 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut51)
private theorem step52 : Cursor.resume source client charge 1 cut51 = cut52 := by checked_cut_rfl
private noncomputable def cut53 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut52)
private theorem step53 : Cursor.resume source client charge 1 cut52 = cut53 := by checked_cut_rfl
private noncomputable def cut54 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut53)
private theorem step54 : Cursor.resume source client charge 1 cut53 = cut54 := by checked_cut_rfl
private noncomputable def cut55 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut54)
private theorem step55 : Cursor.resume source client charge 1 cut54 = cut55 := by checked_cut_rfl
private noncomputable def cut56 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut55)
private theorem step56 : Cursor.resume source client charge 1 cut55 = cut56 := by checked_cut_rfl
private noncomputable def cut57 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut56)
private theorem step57 : Cursor.resume source client charge 1 cut56 = cut57 := by checked_cut_rfl
private noncomputable def cut58 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut57)
private theorem step58 : Cursor.resume source client charge 1 cut57 = cut58 := by checked_cut_rfl
private noncomputable def cut59 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut58)
private theorem step59 : Cursor.resume source client charge 1 cut58 = cut59 := by checked_cut_rfl
private noncomputable def cut60 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut59)
private theorem step60 : Cursor.resume source client charge 1 cut59 = cut60 := by checked_cut_rfl
private noncomputable def cut61 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut60)
private theorem step61 : Cursor.resume source client charge 1 cut60 = cut61 := by checked_cut_rfl
private noncomputable def cut62 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut61)
private theorem step62 : Cursor.resume source client charge 1 cut61 = cut62 := by checked_cut_rfl
private noncomputable def cut63 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut62)
private theorem step63 : Cursor.resume source client charge 1 cut62 = cut63 := by checked_cut_rfl
private noncomputable def cut64 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut63)
private theorem step64 : Cursor.resume source client charge 1 cut63 = cut64 := by checked_cut_rfl
private noncomputable def cut65 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut64)
private theorem step65 : Cursor.resume source client charge 1 cut64 = cut65 := by checked_cut_rfl
private noncomputable def cut66 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut65)
private theorem step66 : Cursor.resume source client charge 1 cut65 = cut66 := by checked_cut_rfl
private noncomputable def cut67 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut66)
private theorem step67 : Cursor.resume source client charge 1 cut66 = cut67 := by checked_cut_rfl
private noncomputable def cut68 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut67)
private theorem step68 : Cursor.resume source client charge 1 cut67 = cut68 := by checked_cut_rfl
private noncomputable def cut69 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut68)
private theorem step69 : Cursor.resume source client charge 1 cut68 = cut69 := by checked_cut_rfl
private noncomputable def cut70 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut69)
private theorem step70 : Cursor.resume source client charge 1 cut69 = cut70 := by checked_cut_rfl
private noncomputable def cut71 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut70)
private theorem step71 : Cursor.resume source client charge 1 cut70 = cut71 := by checked_cut_rfl
private noncomputable def cut72 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut71)
private theorem step72 : Cursor.resume source client charge 1 cut71 = cut72 := by checked_cut_rfl
private noncomputable def cut73 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut72)
private theorem step73 : Cursor.resume source client charge 1 cut72 = cut73 := by checked_cut_rfl
private noncomputable def cut74 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut73)
private theorem step74 : Cursor.resume source client charge 1 cut73 = cut74 := by checked_cut_rfl
private noncomputable def cut75 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut74)
private theorem step75 : Cursor.resume source client charge 1 cut74 = cut75 := by checked_cut_rfl
private noncomputable def cut76 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut75)
private theorem step76 : Cursor.resume source client charge 1 cut75 = cut76 := by checked_cut_rfl
private noncomputable def cut77 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut76)
private theorem step77 : Cursor.resume source client charge 1 cut76 = cut77 := by checked_cut_rfl
private noncomputable def cut78 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut77)
private theorem step78 : Cursor.resume source client charge 1 cut77 = cut78 := by checked_cut_rfl
private noncomputable def cut79 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut78)
private theorem step79 : Cursor.resume source client charge 1 cut78 = cut79 := by checked_cut_rfl
private noncomputable def cut80 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut79)
private theorem step80 : Cursor.resume source client charge 1 cut79 = cut80 := by checked_cut_rfl
private noncomputable def cut81 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut80)
private theorem step81 : Cursor.resume source client charge 1 cut80 = cut81 := by checked_cut_rfl
private noncomputable def cut82 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut81)
private theorem step82 : Cursor.resume source client charge 1 cut81 = cut82 := by checked_cut_rfl
private noncomputable def cut83 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut82)
private theorem step83 : Cursor.resume source client charge 1 cut82 = cut83 := by checked_cut_rfl
private noncomputable def cut84 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut83)
private theorem step84 : Cursor.resume source client charge 1 cut83 = cut84 := by checked_cut_rfl
private noncomputable def cut85 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut84)
private theorem step85 : Cursor.resume source client charge 1 cut84 = cut85 := by checked_cut_rfl
private noncomputable def cut86 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut85)
private theorem step86 : Cursor.resume source client charge 1 cut85 = cut86 := by checked_cut_rfl
private noncomputable def cut87 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut86)
private theorem step87 : Cursor.resume source client charge 1 cut86 = cut87 := by checked_cut_rfl
private noncomputable def cut88 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut87)
private theorem step88 : Cursor.resume source client charge 1 cut87 = cut88 := by checked_cut_rfl
private noncomputable def cut89 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut88)
private theorem step89 : Cursor.resume source client charge 1 cut88 = cut89 := by checked_cut_rfl
private noncomputable def cut90 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut89)
private theorem step90 : Cursor.resume source client charge 1 cut89 = cut90 := by checked_cut_rfl
private noncomputable def cut91 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut90)
private theorem step91 : Cursor.resume source client charge 1 cut90 = cut91 := by checked_cut_rfl
private noncomputable def cut92 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut91)
private theorem step92 : Cursor.resume source client charge 1 cut91 = cut92 := by checked_cut_rfl
private noncomputable def cut93 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut92)
private theorem step93 : Cursor.resume source client charge 1 cut92 = cut93 := by checked_cut_rfl
private noncomputable def cut94 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut93)
private theorem step94 : Cursor.resume source client charge 1 cut93 = cut94 := by checked_cut_rfl
private noncomputable def cut95 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut94)
private theorem step95 : Cursor.resume source client charge 1 cut94 = cut95 := by checked_cut_rfl
private noncomputable def cut96 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut95)
private theorem step96 : Cursor.resume source client charge 1 cut95 = cut96 := by checked_cut_rfl
private noncomputable def cut97 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut96)
private theorem step97 : Cursor.resume source client charge 1 cut96 = cut97 := by checked_cut_rfl
private noncomputable def cut98 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut97)
private theorem step98 : Cursor.resume source client charge 1 cut97 = cut98 := by checked_cut_rfl
private noncomputable def cut99 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut98)
private theorem step99 : Cursor.resume source client charge 1 cut98 = cut99 := by checked_cut_rfl
private noncomputable def cut100 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut99)
private theorem step100 : Cursor.resume source client charge 1 cut99 = cut100 := by checked_cut_rfl
private noncomputable def cut101 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut100)
private theorem step101 : Cursor.resume source client charge 1 cut100 = cut101 := by checked_cut_rfl
private noncomputable def cut102 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut101)
private theorem step102 : Cursor.resume source client charge 1 cut101 = cut102 := by checked_cut_rfl
private noncomputable def cut103 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut102)
private theorem step103 : Cursor.resume source client charge 1 cut102 = cut103 := by checked_cut_rfl
private noncomputable def cut104 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut103)
private theorem step104 : Cursor.resume source client charge 1 cut103 = cut104 := by checked_cut_rfl
private noncomputable def cut105 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut104)
private theorem step105 : Cursor.resume source client charge 1 cut104 = cut105 := by checked_cut_rfl
private noncomputable def cut106 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut105)
private theorem step106 : Cursor.resume source client charge 1 cut105 = cut106 := by checked_cut_rfl
private noncomputable def cut107 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut106)
private theorem step107 : Cursor.resume source client charge 1 cut106 = cut107 := by checked_cut_rfl
private noncomputable def cut108 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut107)
private theorem step108 : Cursor.resume source client charge 1 cut107 = cut108 := by checked_cut_rfl
private noncomputable def cut109 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut108)
private theorem step109 : Cursor.resume source client charge 1 cut108 = cut109 := by checked_cut_rfl
private noncomputable def cut110 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut109)
private theorem step110 : Cursor.resume source client charge 1 cut109 = cut110 := by checked_cut_rfl
private noncomputable def cut111 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut110)
private theorem step111 : Cursor.resume source client charge 1 cut110 = cut111 := by checked_cut_rfl
private noncomputable def cut112 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut111)
private theorem step112 : Cursor.resume source client charge 1 cut111 = cut112 := by checked_cut_rfl
private noncomputable def cut113 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut112)
private theorem step113 : Cursor.resume source client charge 1 cut112 = cut113 := by checked_cut_rfl
private noncomputable def cut114 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut113)
private theorem step114 : Cursor.resume source client charge 1 cut113 = cut114 := by checked_cut_rfl
private noncomputable def cut115 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut114)
private theorem step115 : Cursor.resume source client charge 1 cut114 = cut115 := by checked_cut_rfl
private noncomputable def cut116 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut115)
private theorem step116 : Cursor.resume source client charge 1 cut115 = cut116 := by checked_cut_rfl
private noncomputable def cut117 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut116)
private theorem step117 : Cursor.resume source client charge 1 cut116 = cut117 := by checked_cut_rfl
private noncomputable def cut118 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut117)
private theorem step118 : Cursor.resume source client charge 1 cut117 = cut118 := by checked_cut_rfl
private noncomputable def cut119 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut118)
private theorem step119 : Cursor.resume source client charge 1 cut118 = cut119 := by checked_cut_rfl
private noncomputable def cut120 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut119)
private theorem step120 : Cursor.resume source client charge 1 cut119 = cut120 := by checked_cut_rfl
private noncomputable def cut121 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut120)
private theorem step121 : Cursor.resume source client charge 1 cut120 = cut121 := by checked_cut_rfl
private noncomputable def cut122 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut121)
private theorem step122 : Cursor.resume source client charge 1 cut121 = cut122 := by checked_cut_rfl
private noncomputable def cut123 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut122)
private theorem step123 : Cursor.resume source client charge 1 cut122 = cut123 := by checked_cut_rfl
private noncomputable def cut124 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut123)
private theorem step124 : Cursor.resume source client charge 1 cut123 = cut124 := by checked_cut_rfl
private noncomputable def cut125 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut124)
private theorem step125 : Cursor.resume source client charge 1 cut124 = cut125 := by checked_cut_rfl
private noncomputable def cut126 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut125)
private theorem step126 : Cursor.resume source client charge 1 cut125 = cut126 := by checked_cut_rfl
private noncomputable def cut127 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut126)
private theorem step127 : Cursor.resume source client charge 1 cut126 = cut127 := by checked_cut_rfl
private noncomputable def cut128 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut127)
private theorem step128 : Cursor.resume source client charge 1 cut127 = cut128 := by checked_cut_rfl
private noncomputable def cut129 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut128)
private theorem step129 : Cursor.resume source client charge 1 cut128 = cut129 := by checked_cut_rfl
private noncomputable def cut130 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut129)
private theorem step130 : Cursor.resume source client charge 1 cut129 = cut130 := by checked_cut_rfl
private noncomputable def cut131 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut130)
private theorem step131 : Cursor.resume source client charge 1 cut130 = cut131 := by checked_cut_rfl
private noncomputable def cut132 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut131)
private theorem step132 : Cursor.resume source client charge 1 cut131 = cut132 := by checked_cut_rfl
private noncomputable def cut133 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut132)
private theorem step133 : Cursor.resume source client charge 1 cut132 = cut133 := by checked_cut_rfl
private noncomputable def cut134 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut133)
private theorem step134 : Cursor.resume source client charge 1 cut133 = cut134 := by checked_cut_rfl
private noncomputable def cut135 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut134)
private theorem step135 : Cursor.resume source client charge 1 cut134 = cut135 := by checked_cut_rfl
private noncomputable def cut136 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut135)
private theorem step136 : Cursor.resume source client charge 1 cut135 = cut136 := by checked_cut_rfl
private noncomputable def cut137 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut136)
private theorem step137 : Cursor.resume source client charge 1 cut136 = cut137 := by checked_cut_rfl
private noncomputable def cut138 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut137)
private theorem step138 : Cursor.resume source client charge 1 cut137 = cut138 := by checked_cut_rfl
private noncomputable def cut139 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut138)
private theorem step139 : Cursor.resume source client charge 1 cut138 = cut139 := by checked_cut_rfl
private noncomputable def cut140 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut139)
private theorem step140 : Cursor.resume source client charge 1 cut139 = cut140 := by checked_cut_rfl
private noncomputable def cut141 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut140)
private theorem step141 : Cursor.resume source client charge 1 cut140 = cut141 := by checked_cut_rfl
private noncomputable def cut142 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut141)
private theorem step142 : Cursor.resume source client charge 1 cut141 = cut142 := by checked_cut_rfl
private noncomputable def cut143 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut142)
private theorem step143 : Cursor.resume source client charge 1 cut142 = cut143 := by checked_cut_rfl
private noncomputable def cut144 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut143)
private theorem step144 : Cursor.resume source client charge 1 cut143 = cut144 := by checked_cut_rfl
private noncomputable def cut145 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut144)
private theorem step145 : Cursor.resume source client charge 1 cut144 = cut145 := by checked_cut_rfl
private noncomputable def cut146 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut145)
private theorem step146 : Cursor.resume source client charge 1 cut145 = cut146 := by checked_cut_rfl
private noncomputable def cut147 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut146)
private theorem step147 : Cursor.resume source client charge 1 cut146 = cut147 := by checked_cut_rfl
private noncomputable def cut148 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut147)
private theorem step148 : Cursor.resume source client charge 1 cut147 = cut148 := by checked_cut_rfl
private noncomputable def cut149 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut148)
private theorem step149 : Cursor.resume source client charge 1 cut148 = cut149 := by checked_cut_rfl
private noncomputable def cut150 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut149)
private theorem step150 : Cursor.resume source client charge 1 cut149 = cut150 := by checked_cut_rfl
private noncomputable def cut151 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut150)
private theorem step151 : Cursor.resume source client charge 1 cut150 = cut151 := by checked_cut_rfl
private noncomputable def cut152 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut151)
private theorem step152 : Cursor.resume source client charge 1 cut151 = cut152 := by checked_cut_rfl
private noncomputable def cut153 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut152)
private theorem step153 : Cursor.resume source client charge 1 cut152 = cut153 := by checked_cut_rfl
private noncomputable def cut154 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut153)
private theorem step154 : Cursor.resume source client charge 1 cut153 = cut154 := by checked_cut_rfl
private noncomputable def cut155 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut154)
private theorem step155 : Cursor.resume source client charge 1 cut154 = cut155 := by checked_cut_rfl
private noncomputable def cut156 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut155)
private theorem step156 : Cursor.resume source client charge 1 cut155 = cut156 := by checked_cut_rfl
private noncomputable def cut157 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut156)
private theorem step157 : Cursor.resume source client charge 1 cut156 = cut157 := by checked_cut_rfl
private noncomputable def cut158 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut157)
private theorem step158 : Cursor.resume source client charge 1 cut157 = cut158 := by checked_cut_rfl
private noncomputable def cut159 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut158)
private theorem step159 : Cursor.resume source client charge 1 cut158 = cut159 := by checked_cut_rfl
private noncomputable def cut160 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut159)
private theorem step160 : Cursor.resume source client charge 1 cut159 = cut160 := by checked_cut_rfl
private noncomputable def cut161 : Saved := normalized_cursor_cut% (Cursor.resume source client charge 1 cut160)
private theorem step161 : Cursor.resume source client charge 1 cut160 = cut161 := by checked_cut_rfl
private theorem actual_paid : cut161.1 = 159 := by checked_cut_rfl
private theorem actual_done : (match cut161.2 with | .done _ => true | _ => false) = true := by checked_cut_rfl

private theorem at0 : run 0 = cut0 := by checked_cut_rfl

private theorem extend_cut (fuel : Nat) (before after : Saved)
    (earlier : run fuel = before) (next : Cursor.resume source client charge 1 before = after) :
    run (fuel + 1) = after := by
  have split : run (fuel + 1) = Cursor.resume source client charge 1 (run fuel) :=
    Cursor.advance_add source client charge fuel 1 packet
  exact split.trans ((congrArg (fun saved => Cursor.resume source client charge 1 saved) earlier).trans next)

private theorem at1 : run 1 = cut1 := extend_cut 0 cut0 cut1 at0 step1
private theorem at2 : run 2 = cut2 := extend_cut 1 cut1 cut2 at1 step2
private theorem at3 : run 3 = cut3 := extend_cut 2 cut2 cut3 at2 step3
private theorem at4 : run 4 = cut4 := extend_cut 3 cut3 cut4 at3 step4
private theorem at5 : run 5 = cut5 := extend_cut 4 cut4 cut5 at4 step5
private theorem at6 : run 6 = cut6 := extend_cut 5 cut5 cut6 at5 step6
private theorem at7 : run 7 = cut7 := extend_cut 6 cut6 cut7 at6 step7
private theorem at8 : run 8 = cut8 := extend_cut 7 cut7 cut8 at7 step8
private theorem at9 : run 9 = cut9 := extend_cut 8 cut8 cut9 at8 step9
private theorem at10 : run 10 = cut10 := extend_cut 9 cut9 cut10 at9 step10
private theorem at11 : run 11 = cut11 := extend_cut 10 cut10 cut11 at10 step11
private theorem at12 : run 12 = cut12 := extend_cut 11 cut11 cut12 at11 step12
private theorem at13 : run 13 = cut13 := extend_cut 12 cut12 cut13 at12 step13
private theorem at14 : run 14 = cut14 := extend_cut 13 cut13 cut14 at13 step14
private theorem at15 : run 15 = cut15 := extend_cut 14 cut14 cut15 at14 step15
private theorem at16 : run 16 = cut16 := extend_cut 15 cut15 cut16 at15 step16
private theorem at17 : run 17 = cut17 := extend_cut 16 cut16 cut17 at16 step17
private theorem at18 : run 18 = cut18 := extend_cut 17 cut17 cut18 at17 step18
private theorem at19 : run 19 = cut19 := extend_cut 18 cut18 cut19 at18 step19
private theorem at20 : run 20 = cut20 := extend_cut 19 cut19 cut20 at19 step20
private theorem at21 : run 21 = cut21 := extend_cut 20 cut20 cut21 at20 step21
private theorem at22 : run 22 = cut22 := extend_cut 21 cut21 cut22 at21 step22
private theorem at23 : run 23 = cut23 := extend_cut 22 cut22 cut23 at22 step23
private theorem at24 : run 24 = cut24 := extend_cut 23 cut23 cut24 at23 step24
private theorem at25 : run 25 = cut25 := extend_cut 24 cut24 cut25 at24 step25
private theorem at26 : run 26 = cut26 := extend_cut 25 cut25 cut26 at25 step26
private theorem at27 : run 27 = cut27 := extend_cut 26 cut26 cut27 at26 step27
private theorem at28 : run 28 = cut28 := extend_cut 27 cut27 cut28 at27 step28
private theorem at29 : run 29 = cut29 := extend_cut 28 cut28 cut29 at28 step29
private theorem at30 : run 30 = cut30 := extend_cut 29 cut29 cut30 at29 step30
private theorem at31 : run 31 = cut31 := extend_cut 30 cut30 cut31 at30 step31
private theorem at32 : run 32 = cut32 := extend_cut 31 cut31 cut32 at31 step32
private theorem at33 : run 33 = cut33 := extend_cut 32 cut32 cut33 at32 step33
private theorem at34 : run 34 = cut34 := extend_cut 33 cut33 cut34 at33 step34
private theorem at35 : run 35 = cut35 := extend_cut 34 cut34 cut35 at34 step35
private theorem at36 : run 36 = cut36 := extend_cut 35 cut35 cut36 at35 step36
private theorem at37 : run 37 = cut37 := extend_cut 36 cut36 cut37 at36 step37
private theorem at38 : run 38 = cut38 := extend_cut 37 cut37 cut38 at37 step38
private theorem at39 : run 39 = cut39 := extend_cut 38 cut38 cut39 at38 step39
private theorem at40 : run 40 = cut40 := extend_cut 39 cut39 cut40 at39 step40
private theorem at41 : run 41 = cut41 := extend_cut 40 cut40 cut41 at40 step41
private theorem at42 : run 42 = cut42 := extend_cut 41 cut41 cut42 at41 step42
private theorem at43 : run 43 = cut43 := extend_cut 42 cut42 cut43 at42 step43
private theorem at44 : run 44 = cut44 := extend_cut 43 cut43 cut44 at43 step44
private theorem at45 : run 45 = cut45 := extend_cut 44 cut44 cut45 at44 step45
private theorem at46 : run 46 = cut46 := extend_cut 45 cut45 cut46 at45 step46
private theorem at47 : run 47 = cut47 := extend_cut 46 cut46 cut47 at46 step47
private theorem at48 : run 48 = cut48 := extend_cut 47 cut47 cut48 at47 step48
private theorem at49 : run 49 = cut49 := extend_cut 48 cut48 cut49 at48 step49
private theorem at50 : run 50 = cut50 := extend_cut 49 cut49 cut50 at49 step50
private theorem at51 : run 51 = cut51 := extend_cut 50 cut50 cut51 at50 step51
private theorem at52 : run 52 = cut52 := extend_cut 51 cut51 cut52 at51 step52
private theorem at53 : run 53 = cut53 := extend_cut 52 cut52 cut53 at52 step53
private theorem at54 : run 54 = cut54 := extend_cut 53 cut53 cut54 at53 step54
private theorem at55 : run 55 = cut55 := extend_cut 54 cut54 cut55 at54 step55
private theorem at56 : run 56 = cut56 := extend_cut 55 cut55 cut56 at55 step56
private theorem at57 : run 57 = cut57 := extend_cut 56 cut56 cut57 at56 step57
private theorem at58 : run 58 = cut58 := extend_cut 57 cut57 cut58 at57 step58
private theorem at59 : run 59 = cut59 := extend_cut 58 cut58 cut59 at58 step59
private theorem at60 : run 60 = cut60 := extend_cut 59 cut59 cut60 at59 step60
private theorem at61 : run 61 = cut61 := extend_cut 60 cut60 cut61 at60 step61
private theorem at62 : run 62 = cut62 := extend_cut 61 cut61 cut62 at61 step62
private theorem at63 : run 63 = cut63 := extend_cut 62 cut62 cut63 at62 step63
private theorem at64 : run 64 = cut64 := extend_cut 63 cut63 cut64 at63 step64
private theorem at65 : run 65 = cut65 := extend_cut 64 cut64 cut65 at64 step65
private theorem at66 : run 66 = cut66 := extend_cut 65 cut65 cut66 at65 step66
private theorem at67 : run 67 = cut67 := extend_cut 66 cut66 cut67 at66 step67
private theorem at68 : run 68 = cut68 := extend_cut 67 cut67 cut68 at67 step68
private theorem at69 : run 69 = cut69 := extend_cut 68 cut68 cut69 at68 step69
private theorem at70 : run 70 = cut70 := extend_cut 69 cut69 cut70 at69 step70
private theorem at71 : run 71 = cut71 := extend_cut 70 cut70 cut71 at70 step71
private theorem at72 : run 72 = cut72 := extend_cut 71 cut71 cut72 at71 step72
private theorem at73 : run 73 = cut73 := extend_cut 72 cut72 cut73 at72 step73
private theorem at74 : run 74 = cut74 := extend_cut 73 cut73 cut74 at73 step74
private theorem at75 : run 75 = cut75 := extend_cut 74 cut74 cut75 at74 step75
private theorem at76 : run 76 = cut76 := extend_cut 75 cut75 cut76 at75 step76
private theorem at77 : run 77 = cut77 := extend_cut 76 cut76 cut77 at76 step77
private theorem at78 : run 78 = cut78 := extend_cut 77 cut77 cut78 at77 step78
private theorem at79 : run 79 = cut79 := extend_cut 78 cut78 cut79 at78 step79
private theorem at80 : run 80 = cut80 := extend_cut 79 cut79 cut80 at79 step80
private theorem at81 : run 81 = cut81 := extend_cut 80 cut80 cut81 at80 step81
private theorem at82 : run 82 = cut82 := extend_cut 81 cut81 cut82 at81 step82
private theorem at83 : run 83 = cut83 := extend_cut 82 cut82 cut83 at82 step83
private theorem at84 : run 84 = cut84 := extend_cut 83 cut83 cut84 at83 step84
private theorem at85 : run 85 = cut85 := extend_cut 84 cut84 cut85 at84 step85
private theorem at86 : run 86 = cut86 := extend_cut 85 cut85 cut86 at85 step86
private theorem at87 : run 87 = cut87 := extend_cut 86 cut86 cut87 at86 step87
private theorem at88 : run 88 = cut88 := extend_cut 87 cut87 cut88 at87 step88
private theorem at89 : run 89 = cut89 := extend_cut 88 cut88 cut89 at88 step89
private theorem at90 : run 90 = cut90 := extend_cut 89 cut89 cut90 at89 step90
private theorem at91 : run 91 = cut91 := extend_cut 90 cut90 cut91 at90 step91
private theorem at92 : run 92 = cut92 := extend_cut 91 cut91 cut92 at91 step92
private theorem at93 : run 93 = cut93 := extend_cut 92 cut92 cut93 at92 step93
private theorem at94 : run 94 = cut94 := extend_cut 93 cut93 cut94 at93 step94
private theorem at95 : run 95 = cut95 := extend_cut 94 cut94 cut95 at94 step95
private theorem at96 : run 96 = cut96 := extend_cut 95 cut95 cut96 at95 step96
private theorem at97 : run 97 = cut97 := extend_cut 96 cut96 cut97 at96 step97
private theorem at98 : run 98 = cut98 := extend_cut 97 cut97 cut98 at97 step98
private theorem at99 : run 99 = cut99 := extend_cut 98 cut98 cut99 at98 step99
private theorem at100 : run 100 = cut100 := extend_cut 99 cut99 cut100 at99 step100
private theorem at101 : run 101 = cut101 := extend_cut 100 cut100 cut101 at100 step101
private theorem at102 : run 102 = cut102 := extend_cut 101 cut101 cut102 at101 step102
private theorem at103 : run 103 = cut103 := extend_cut 102 cut102 cut103 at102 step103
private theorem at104 : run 104 = cut104 := extend_cut 103 cut103 cut104 at103 step104
private theorem at105 : run 105 = cut105 := extend_cut 104 cut104 cut105 at104 step105
private theorem at106 : run 106 = cut106 := extend_cut 105 cut105 cut106 at105 step106
private theorem at107 : run 107 = cut107 := extend_cut 106 cut106 cut107 at106 step107
private theorem at108 : run 108 = cut108 := extend_cut 107 cut107 cut108 at107 step108
private theorem at109 : run 109 = cut109 := extend_cut 108 cut108 cut109 at108 step109
private theorem at110 : run 110 = cut110 := extend_cut 109 cut109 cut110 at109 step110
private theorem at111 : run 111 = cut111 := extend_cut 110 cut110 cut111 at110 step111
private theorem at112 : run 112 = cut112 := extend_cut 111 cut111 cut112 at111 step112
private theorem at113 : run 113 = cut113 := extend_cut 112 cut112 cut113 at112 step113
private theorem at114 : run 114 = cut114 := extend_cut 113 cut113 cut114 at113 step114
private theorem at115 : run 115 = cut115 := extend_cut 114 cut114 cut115 at114 step115
private theorem at116 : run 116 = cut116 := extend_cut 115 cut115 cut116 at115 step116
private theorem at117 : run 117 = cut117 := extend_cut 116 cut116 cut117 at116 step117
private theorem at118 : run 118 = cut118 := extend_cut 117 cut117 cut118 at117 step118
private theorem at119 : run 119 = cut119 := extend_cut 118 cut118 cut119 at118 step119
private theorem at120 : run 120 = cut120 := extend_cut 119 cut119 cut120 at119 step120
private theorem at121 : run 121 = cut121 := extend_cut 120 cut120 cut121 at120 step121
private theorem at122 : run 122 = cut122 := extend_cut 121 cut121 cut122 at121 step122
private theorem at123 : run 123 = cut123 := extend_cut 122 cut122 cut123 at122 step123
private theorem at124 : run 124 = cut124 := extend_cut 123 cut123 cut124 at123 step124
private theorem at125 : run 125 = cut125 := extend_cut 124 cut124 cut125 at124 step125
private theorem at126 : run 126 = cut126 := extend_cut 125 cut125 cut126 at125 step126
private theorem at127 : run 127 = cut127 := extend_cut 126 cut126 cut127 at126 step127
private theorem at128 : run 128 = cut128 := extend_cut 127 cut127 cut128 at127 step128
private theorem at129 : run 129 = cut129 := extend_cut 128 cut128 cut129 at128 step129
private theorem at130 : run 130 = cut130 := extend_cut 129 cut129 cut130 at129 step130
private theorem at131 : run 131 = cut131 := extend_cut 130 cut130 cut131 at130 step131
private theorem at132 : run 132 = cut132 := extend_cut 131 cut131 cut132 at131 step132
private theorem at133 : run 133 = cut133 := extend_cut 132 cut132 cut133 at132 step133
private theorem at134 : run 134 = cut134 := extend_cut 133 cut133 cut134 at133 step134
private theorem at135 : run 135 = cut135 := extend_cut 134 cut134 cut135 at134 step135
private theorem at136 : run 136 = cut136 := extend_cut 135 cut135 cut136 at135 step136
private theorem at137 : run 137 = cut137 := extend_cut 136 cut136 cut137 at136 step137
private theorem at138 : run 138 = cut138 := extend_cut 137 cut137 cut138 at137 step138
private theorem at139 : run 139 = cut139 := extend_cut 138 cut138 cut139 at138 step139
private theorem at140 : run 140 = cut140 := extend_cut 139 cut139 cut140 at139 step140
private theorem at141 : run 141 = cut141 := extend_cut 140 cut140 cut141 at140 step141
private theorem at142 : run 142 = cut142 := extend_cut 141 cut141 cut142 at141 step142
private theorem at143 : run 143 = cut143 := extend_cut 142 cut142 cut143 at142 step143
private theorem at144 : run 144 = cut144 := extend_cut 143 cut143 cut144 at143 step144
private theorem at145 : run 145 = cut145 := extend_cut 144 cut144 cut145 at144 step145
private theorem at146 : run 146 = cut146 := extend_cut 145 cut145 cut146 at145 step146
private theorem at147 : run 147 = cut147 := extend_cut 146 cut146 cut147 at146 step147
private theorem at148 : run 148 = cut148 := extend_cut 147 cut147 cut148 at147 step148
private theorem at149 : run 149 = cut149 := extend_cut 148 cut148 cut149 at148 step149
private theorem at150 : run 150 = cut150 := extend_cut 149 cut149 cut150 at149 step150
private theorem at151 : run 151 = cut151 := extend_cut 150 cut150 cut151 at150 step151
private theorem at152 : run 152 = cut152 := extend_cut 151 cut151 cut152 at151 step152
private theorem at153 : run 153 = cut153 := extend_cut 152 cut152 cut153 at152 step153
private theorem at154 : run 154 = cut154 := extend_cut 153 cut153 cut154 at153 step154
private theorem at155 : run 155 = cut155 := extend_cut 154 cut154 cut155 at154 step155
private theorem at156 : run 156 = cut156 := extend_cut 155 cut155 cut156 at155 step156
private theorem at157 : run 157 = cut157 := extend_cut 156 cut156 cut157 at156 step157
private theorem at158 : run 158 = cut158 := extend_cut 157 cut157 cut158 at157 step158
private theorem at159 : run 159 = cut159 := extend_cut 158 cut158 cut159 at158 step159
private theorem at160 : run 160 = cut160 := extend_cut 159 cut159 cut160 at159 step160
private theorem at161 : run 161 = cut161 := extend_cut 160 cut160 cut161 at160 step161

private theorem done_resume (fuel : Nat) : Cursor.resume source client charge fuel cut161 = cut161 := by
  checked_cut_rfl

private theorem whole_at17 : run 17 = cut17 := at17
private theorem whole_at161 : run 161 = cut161 := at161
private theorem at_zero : run 0 = cut0 := at0

private theorem whole : run 400 = cut161 := by
  have split : run 400 = Cursor.resume source client charge 239 (run 161) :=
    Cursor.advance_add source client charge 161 239 packet
  exact split.trans ((congrArg (fun saved => Cursor.resume source client charge 239 saved) at161).trans (done_resume 239))

local notation "Read" => PassiveReader.readSuffix annotation number revocationWorlds required needed act reader notice 407
local notation "Observe" => sourceView annotation number revocationWorlds required needed act reader notice 407

private theorem fold_step {Result : Type} [Monoid Result] (value : View → Result)
    {fuel : Nat} {before after : Saved} {head tail total : Result}
    (step : Cursor.resume source client charge 1 before = after)
    (one : Read value 1 before = head) (rest : Read value fuel after = tail)
    (product : head * tail = total) : Read value (1 + fuel) before = total :=
  (PassiveReader.readSuffix_add annotation number revocationWorlds required needed act reader notice
    407 value 1 fuel before).trans
      ((congrArg₂ (fun left right : Result => left * right) one
        ((congrArg (Read value fuel) step).trans rest)).trans product)

private noncomputable def view0 : View := normalized_cursor_cut% (Observe cut0.2)
private theorem view_eq0 : Observe cut0.2 = view0 := by checked_cut_rfl
private theorem read_one0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut0 = value (Observe cut0.2) := by
  change value (Observe cut0.2) * 1 = value (Observe cut0.2)
  exact mul_one _
private theorem one0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut0 = value view0 :=
  (read_one0 value).trans (congrArg value view_eq0)
private noncomputable def view1 : View := normalized_cursor_cut% (Observe cut1.2)
private theorem view_eq1 : Observe cut1.2 = view1 := by checked_cut_rfl
private theorem read_one1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut1 = value (Observe cut1.2) := by
  change value (Observe cut1.2) * 1 = value (Observe cut1.2)
  exact mul_one _
private theorem one1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut1 = value view1 :=
  (read_one1 value).trans (congrArg value view_eq1)
private noncomputable def view2 : View := normalized_cursor_cut% (Observe cut2.2)
private theorem view_eq2 : Observe cut2.2 = view2 := by checked_cut_rfl
private theorem read_one2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut2 = value (Observe cut2.2) := by
  change value (Observe cut2.2) * 1 = value (Observe cut2.2)
  exact mul_one _
private theorem one2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut2 = value view2 :=
  (read_one2 value).trans (congrArg value view_eq2)
private noncomputable def view3 : View := normalized_cursor_cut% (Observe cut3.2)
private theorem view_eq3 : Observe cut3.2 = view3 := by checked_cut_rfl
private theorem read_one3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut3 = value (Observe cut3.2) := by
  change value (Observe cut3.2) * 1 = value (Observe cut3.2)
  exact mul_one _
private theorem one3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut3 = value view3 :=
  (read_one3 value).trans (congrArg value view_eq3)
private noncomputable def view4 : View := normalized_cursor_cut% (Observe cut4.2)
private theorem view_eq4 : Observe cut4.2 = view4 := by checked_cut_rfl
private theorem read_one4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut4 = value (Observe cut4.2) := by
  change value (Observe cut4.2) * 1 = value (Observe cut4.2)
  exact mul_one _
private theorem one4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut4 = value view4 :=
  (read_one4 value).trans (congrArg value view_eq4)
private noncomputable def view5 : View := normalized_cursor_cut% (Observe cut5.2)
private theorem view_eq5 : Observe cut5.2 = view5 := by checked_cut_rfl
private theorem read_one5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut5 = value (Observe cut5.2) := by
  change value (Observe cut5.2) * 1 = value (Observe cut5.2)
  exact mul_one _
private theorem one5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut5 = value view5 :=
  (read_one5 value).trans (congrArg value view_eq5)
private noncomputable def view6 : View := normalized_cursor_cut% (Observe cut6.2)
private theorem view_eq6 : Observe cut6.2 = view6 := by checked_cut_rfl
private theorem read_one6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut6 = value (Observe cut6.2) := by
  change value (Observe cut6.2) * 1 = value (Observe cut6.2)
  exact mul_one _
private theorem one6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut6 = value view6 :=
  (read_one6 value).trans (congrArg value view_eq6)
private noncomputable def view7 : View := normalized_cursor_cut% (Observe cut7.2)
private theorem view_eq7 : Observe cut7.2 = view7 := by checked_cut_rfl
private theorem read_one7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut7 = value (Observe cut7.2) := by
  change value (Observe cut7.2) * 1 = value (Observe cut7.2)
  exact mul_one _
private theorem one7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut7 = value view7 :=
  (read_one7 value).trans (congrArg value view_eq7)
private noncomputable def view8 : View := normalized_cursor_cut% (Observe cut8.2)
private theorem view_eq8 : Observe cut8.2 = view8 := by checked_cut_rfl
private theorem read_one8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut8 = value (Observe cut8.2) := by
  change value (Observe cut8.2) * 1 = value (Observe cut8.2)
  exact mul_one _
private theorem one8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut8 = value view8 :=
  (read_one8 value).trans (congrArg value view_eq8)
private noncomputable def view9 : View := normalized_cursor_cut% (Observe cut9.2)
private theorem view_eq9 : Observe cut9.2 = view9 := by checked_cut_rfl
private theorem read_one9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut9 = value (Observe cut9.2) := by
  change value (Observe cut9.2) * 1 = value (Observe cut9.2)
  exact mul_one _
private theorem one9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut9 = value view9 :=
  (read_one9 value).trans (congrArg value view_eq9)
private noncomputable def view10 : View := normalized_cursor_cut% (Observe cut10.2)
private theorem view_eq10 : Observe cut10.2 = view10 := by checked_cut_rfl
private theorem read_one10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut10 = value (Observe cut10.2) := by
  change value (Observe cut10.2) * 1 = value (Observe cut10.2)
  exact mul_one _
private theorem one10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut10 = value view10 :=
  (read_one10 value).trans (congrArg value view_eq10)
private noncomputable def view11 : View := normalized_cursor_cut% (Observe cut11.2)
private theorem view_eq11 : Observe cut11.2 = view11 := by checked_cut_rfl
private theorem read_one11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut11 = value (Observe cut11.2) := by
  change value (Observe cut11.2) * 1 = value (Observe cut11.2)
  exact mul_one _
private theorem one11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut11 = value view11 :=
  (read_one11 value).trans (congrArg value view_eq11)
private noncomputable def view12 : View := normalized_cursor_cut% (Observe cut12.2)
private theorem view_eq12 : Observe cut12.2 = view12 := by checked_cut_rfl
private theorem read_one12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut12 = value (Observe cut12.2) := by
  change value (Observe cut12.2) * 1 = value (Observe cut12.2)
  exact mul_one _
private theorem one12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut12 = value view12 :=
  (read_one12 value).trans (congrArg value view_eq12)
private noncomputable def view13 : View := normalized_cursor_cut% (Observe cut13.2)
private theorem view_eq13 : Observe cut13.2 = view13 := by checked_cut_rfl
private theorem read_one13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut13 = value (Observe cut13.2) := by
  change value (Observe cut13.2) * 1 = value (Observe cut13.2)
  exact mul_one _
private theorem one13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut13 = value view13 :=
  (read_one13 value).trans (congrArg value view_eq13)
private noncomputable def view14 : View := normalized_cursor_cut% (Observe cut14.2)
private theorem view_eq14 : Observe cut14.2 = view14 := by checked_cut_rfl
private theorem read_one14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut14 = value (Observe cut14.2) := by
  change value (Observe cut14.2) * 1 = value (Observe cut14.2)
  exact mul_one _
private theorem one14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut14 = value view14 :=
  (read_one14 value).trans (congrArg value view_eq14)
private noncomputable def view15 : View := normalized_cursor_cut% (Observe cut15.2)
private theorem view_eq15 : Observe cut15.2 = view15 := by checked_cut_rfl
private theorem read_one15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut15 = value (Observe cut15.2) := by
  change value (Observe cut15.2) * 1 = value (Observe cut15.2)
  exact mul_one _
private theorem one15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut15 = value view15 :=
  (read_one15 value).trans (congrArg value view_eq15)
private noncomputable def view16 : View := normalized_cursor_cut% (Observe cut16.2)
private theorem view_eq16 : Observe cut16.2 = view16 := by checked_cut_rfl
private theorem read_one16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut16 = value (Observe cut16.2) := by
  change value (Observe cut16.2) * 1 = value (Observe cut16.2)
  exact mul_one _
private theorem one16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut16 = value view16 :=
  (read_one16 value).trans (congrArg value view_eq16)
private noncomputable def view17 : View := normalized_cursor_cut% (Observe cut17.2)
private theorem view_eq17 : Observe cut17.2 = view17 := by checked_cut_rfl
private theorem read_one17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut17 = value (Observe cut17.2) := by
  change value (Observe cut17.2) * 1 = value (Observe cut17.2)
  exact mul_one _
private theorem one17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut17 = value view17 :=
  (read_one17 value).trans (congrArg value view_eq17)
private noncomputable def view18 : View := normalized_cursor_cut% (Observe cut18.2)
private theorem view_eq18 : Observe cut18.2 = view18 := by checked_cut_rfl
private theorem read_one18 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut18 = value (Observe cut18.2) := by
  change value (Observe cut18.2) * 1 = value (Observe cut18.2)
  exact mul_one _
private theorem one18 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut18 = value view18 :=
  (read_one18 value).trans (congrArg value view_eq18)
private noncomputable def view19 : View := normalized_cursor_cut% (Observe cut19.2)
private theorem view_eq19 : Observe cut19.2 = view19 := by checked_cut_rfl
private theorem read_one19 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut19 = value (Observe cut19.2) := by
  change value (Observe cut19.2) * 1 = value (Observe cut19.2)
  exact mul_one _
private theorem one19 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut19 = value view19 :=
  (read_one19 value).trans (congrArg value view_eq19)
private noncomputable def view20 : View := normalized_cursor_cut% (Observe cut20.2)
private theorem view_eq20 : Observe cut20.2 = view20 := by checked_cut_rfl
private theorem read_one20 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut20 = value (Observe cut20.2) := by
  change value (Observe cut20.2) * 1 = value (Observe cut20.2)
  exact mul_one _
private theorem one20 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut20 = value view20 :=
  (read_one20 value).trans (congrArg value view_eq20)
private noncomputable def view21 : View := normalized_cursor_cut% (Observe cut21.2)
private theorem view_eq21 : Observe cut21.2 = view21 := by checked_cut_rfl
private theorem read_one21 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut21 = value (Observe cut21.2) := by
  change value (Observe cut21.2) * 1 = value (Observe cut21.2)
  exact mul_one _
private theorem one21 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut21 = value view21 :=
  (read_one21 value).trans (congrArg value view_eq21)
private noncomputable def view22 : View := normalized_cursor_cut% (Observe cut22.2)
private theorem view_eq22 : Observe cut22.2 = view22 := by checked_cut_rfl
private theorem read_one22 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut22 = value (Observe cut22.2) := by
  change value (Observe cut22.2) * 1 = value (Observe cut22.2)
  exact mul_one _
private theorem one22 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut22 = value view22 :=
  (read_one22 value).trans (congrArg value view_eq22)
private noncomputable def view23 : View := normalized_cursor_cut% (Observe cut23.2)
private theorem view_eq23 : Observe cut23.2 = view23 := by checked_cut_rfl
private theorem read_one23 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut23 = value (Observe cut23.2) := by
  change value (Observe cut23.2) * 1 = value (Observe cut23.2)
  exact mul_one _
private theorem one23 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut23 = value view23 :=
  (read_one23 value).trans (congrArg value view_eq23)
private noncomputable def view24 : View := normalized_cursor_cut% (Observe cut24.2)
private theorem view_eq24 : Observe cut24.2 = view24 := by checked_cut_rfl
private theorem read_one24 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut24 = value (Observe cut24.2) := by
  change value (Observe cut24.2) * 1 = value (Observe cut24.2)
  exact mul_one _
private theorem one24 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut24 = value view24 :=
  (read_one24 value).trans (congrArg value view_eq24)
private noncomputable def view25 : View := normalized_cursor_cut% (Observe cut25.2)
private theorem view_eq25 : Observe cut25.2 = view25 := by checked_cut_rfl
private theorem read_one25 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut25 = value (Observe cut25.2) := by
  change value (Observe cut25.2) * 1 = value (Observe cut25.2)
  exact mul_one _
private theorem one25 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut25 = value view25 :=
  (read_one25 value).trans (congrArg value view_eq25)
private noncomputable def view26 : View := normalized_cursor_cut% (Observe cut26.2)
private theorem view_eq26 : Observe cut26.2 = view26 := by checked_cut_rfl
private theorem read_one26 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut26 = value (Observe cut26.2) := by
  change value (Observe cut26.2) * 1 = value (Observe cut26.2)
  exact mul_one _
private theorem one26 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut26 = value view26 :=
  (read_one26 value).trans (congrArg value view_eq26)
private noncomputable def view27 : View := normalized_cursor_cut% (Observe cut27.2)
private theorem view_eq27 : Observe cut27.2 = view27 := by checked_cut_rfl
private theorem read_one27 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut27 = value (Observe cut27.2) := by
  change value (Observe cut27.2) * 1 = value (Observe cut27.2)
  exact mul_one _
private theorem one27 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut27 = value view27 :=
  (read_one27 value).trans (congrArg value view_eq27)
private noncomputable def view28 : View := normalized_cursor_cut% (Observe cut28.2)
private theorem view_eq28 : Observe cut28.2 = view28 := by checked_cut_rfl
private theorem read_one28 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut28 = value (Observe cut28.2) := by
  change value (Observe cut28.2) * 1 = value (Observe cut28.2)
  exact mul_one _
private theorem one28 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut28 = value view28 :=
  (read_one28 value).trans (congrArg value view_eq28)
private noncomputable def view29 : View := normalized_cursor_cut% (Observe cut29.2)
private theorem view_eq29 : Observe cut29.2 = view29 := by checked_cut_rfl
private theorem read_one29 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut29 = value (Observe cut29.2) := by
  change value (Observe cut29.2) * 1 = value (Observe cut29.2)
  exact mul_one _
private theorem one29 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut29 = value view29 :=
  (read_one29 value).trans (congrArg value view_eq29)
private noncomputable def view30 : View := normalized_cursor_cut% (Observe cut30.2)
private theorem view_eq30 : Observe cut30.2 = view30 := by checked_cut_rfl
private theorem read_one30 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut30 = value (Observe cut30.2) := by
  change value (Observe cut30.2) * 1 = value (Observe cut30.2)
  exact mul_one _
private theorem one30 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut30 = value view30 :=
  (read_one30 value).trans (congrArg value view_eq30)
private noncomputable def view31 : View := normalized_cursor_cut% (Observe cut31.2)
private theorem view_eq31 : Observe cut31.2 = view31 := by checked_cut_rfl
private theorem read_one31 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut31 = value (Observe cut31.2) := by
  change value (Observe cut31.2) * 1 = value (Observe cut31.2)
  exact mul_one _
private theorem one31 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut31 = value view31 :=
  (read_one31 value).trans (congrArg value view_eq31)
private noncomputable def view32 : View := normalized_cursor_cut% (Observe cut32.2)
private theorem view_eq32 : Observe cut32.2 = view32 := by checked_cut_rfl
private theorem read_one32 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut32 = value (Observe cut32.2) := by
  change value (Observe cut32.2) * 1 = value (Observe cut32.2)
  exact mul_one _
private theorem one32 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut32 = value view32 :=
  (read_one32 value).trans (congrArg value view_eq32)
private noncomputable def view33 : View := normalized_cursor_cut% (Observe cut33.2)
private theorem view_eq33 : Observe cut33.2 = view33 := by checked_cut_rfl
private theorem read_one33 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut33 = value (Observe cut33.2) := by
  change value (Observe cut33.2) * 1 = value (Observe cut33.2)
  exact mul_one _
private theorem one33 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut33 = value view33 :=
  (read_one33 value).trans (congrArg value view_eq33)
private noncomputable def view34 : View := normalized_cursor_cut% (Observe cut34.2)
private theorem view_eq34 : Observe cut34.2 = view34 := by checked_cut_rfl
private theorem read_one34 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut34 = value (Observe cut34.2) := by
  change value (Observe cut34.2) * 1 = value (Observe cut34.2)
  exact mul_one _
private theorem one34 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut34 = value view34 :=
  (read_one34 value).trans (congrArg value view_eq34)
private noncomputable def view35 : View := normalized_cursor_cut% (Observe cut35.2)
private theorem view_eq35 : Observe cut35.2 = view35 := by checked_cut_rfl
private theorem read_one35 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut35 = value (Observe cut35.2) := by
  change value (Observe cut35.2) * 1 = value (Observe cut35.2)
  exact mul_one _
private theorem one35 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut35 = value view35 :=
  (read_one35 value).trans (congrArg value view_eq35)
private noncomputable def view36 : View := normalized_cursor_cut% (Observe cut36.2)
private theorem view_eq36 : Observe cut36.2 = view36 := by checked_cut_rfl
private theorem read_one36 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut36 = value (Observe cut36.2) := by
  change value (Observe cut36.2) * 1 = value (Observe cut36.2)
  exact mul_one _
private theorem one36 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut36 = value view36 :=
  (read_one36 value).trans (congrArg value view_eq36)
private noncomputable def view37 : View := normalized_cursor_cut% (Observe cut37.2)
private theorem view_eq37 : Observe cut37.2 = view37 := by checked_cut_rfl
private theorem read_one37 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut37 = value (Observe cut37.2) := by
  change value (Observe cut37.2) * 1 = value (Observe cut37.2)
  exact mul_one _
private theorem one37 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut37 = value view37 :=
  (read_one37 value).trans (congrArg value view_eq37)
private noncomputable def view38 : View := normalized_cursor_cut% (Observe cut38.2)
private theorem view_eq38 : Observe cut38.2 = view38 := by checked_cut_rfl
private theorem read_one38 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut38 = value (Observe cut38.2) := by
  change value (Observe cut38.2) * 1 = value (Observe cut38.2)
  exact mul_one _
private theorem one38 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut38 = value view38 :=
  (read_one38 value).trans (congrArg value view_eq38)
private noncomputable def view39 : View := normalized_cursor_cut% (Observe cut39.2)
private theorem view_eq39 : Observe cut39.2 = view39 := by checked_cut_rfl
private theorem read_one39 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut39 = value (Observe cut39.2) := by
  change value (Observe cut39.2) * 1 = value (Observe cut39.2)
  exact mul_one _
private theorem one39 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut39 = value view39 :=
  (read_one39 value).trans (congrArg value view_eq39)
private noncomputable def view40 : View := normalized_cursor_cut% (Observe cut40.2)
private theorem view_eq40 : Observe cut40.2 = view40 := by checked_cut_rfl
private theorem read_one40 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut40 = value (Observe cut40.2) := by
  change value (Observe cut40.2) * 1 = value (Observe cut40.2)
  exact mul_one _
private theorem one40 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut40 = value view40 :=
  (read_one40 value).trans (congrArg value view_eq40)
private noncomputable def view41 : View := normalized_cursor_cut% (Observe cut41.2)
private theorem view_eq41 : Observe cut41.2 = view41 := by checked_cut_rfl
private theorem read_one41 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut41 = value (Observe cut41.2) := by
  change value (Observe cut41.2) * 1 = value (Observe cut41.2)
  exact mul_one _
private theorem one41 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut41 = value view41 :=
  (read_one41 value).trans (congrArg value view_eq41)
private noncomputable def view42 : View := normalized_cursor_cut% (Observe cut42.2)
private theorem view_eq42 : Observe cut42.2 = view42 := by checked_cut_rfl
private theorem read_one42 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut42 = value (Observe cut42.2) := by
  change value (Observe cut42.2) * 1 = value (Observe cut42.2)
  exact mul_one _
private theorem one42 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut42 = value view42 :=
  (read_one42 value).trans (congrArg value view_eq42)
private noncomputable def view43 : View := normalized_cursor_cut% (Observe cut43.2)
private theorem view_eq43 : Observe cut43.2 = view43 := by checked_cut_rfl
private theorem read_one43 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut43 = value (Observe cut43.2) := by
  change value (Observe cut43.2) * 1 = value (Observe cut43.2)
  exact mul_one _
private theorem one43 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut43 = value view43 :=
  (read_one43 value).trans (congrArg value view_eq43)
private noncomputable def view44 : View := normalized_cursor_cut% (Observe cut44.2)
private theorem view_eq44 : Observe cut44.2 = view44 := by checked_cut_rfl
private theorem read_one44 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut44 = value (Observe cut44.2) := by
  change value (Observe cut44.2) * 1 = value (Observe cut44.2)
  exact mul_one _
private theorem one44 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut44 = value view44 :=
  (read_one44 value).trans (congrArg value view_eq44)
private noncomputable def view45 : View := normalized_cursor_cut% (Observe cut45.2)
private theorem view_eq45 : Observe cut45.2 = view45 := by checked_cut_rfl
private theorem read_one45 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut45 = value (Observe cut45.2) := by
  change value (Observe cut45.2) * 1 = value (Observe cut45.2)
  exact mul_one _
private theorem one45 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut45 = value view45 :=
  (read_one45 value).trans (congrArg value view_eq45)
private noncomputable def view46 : View := normalized_cursor_cut% (Observe cut46.2)
private theorem view_eq46 : Observe cut46.2 = view46 := by checked_cut_rfl
private theorem read_one46 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut46 = value (Observe cut46.2) := by
  change value (Observe cut46.2) * 1 = value (Observe cut46.2)
  exact mul_one _
private theorem one46 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut46 = value view46 :=
  (read_one46 value).trans (congrArg value view_eq46)
private noncomputable def view47 : View := normalized_cursor_cut% (Observe cut47.2)
private theorem view_eq47 : Observe cut47.2 = view47 := by checked_cut_rfl
private theorem read_one47 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut47 = value (Observe cut47.2) := by
  change value (Observe cut47.2) * 1 = value (Observe cut47.2)
  exact mul_one _
private theorem one47 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut47 = value view47 :=
  (read_one47 value).trans (congrArg value view_eq47)
private noncomputable def view48 : View := normalized_cursor_cut% (Observe cut48.2)
private theorem view_eq48 : Observe cut48.2 = view48 := by checked_cut_rfl
private theorem read_one48 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut48 = value (Observe cut48.2) := by
  change value (Observe cut48.2) * 1 = value (Observe cut48.2)
  exact mul_one _
private theorem one48 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut48 = value view48 :=
  (read_one48 value).trans (congrArg value view_eq48)
private noncomputable def view49 : View := normalized_cursor_cut% (Observe cut49.2)
private theorem view_eq49 : Observe cut49.2 = view49 := by checked_cut_rfl
private theorem read_one49 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut49 = value (Observe cut49.2) := by
  change value (Observe cut49.2) * 1 = value (Observe cut49.2)
  exact mul_one _
private theorem one49 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut49 = value view49 :=
  (read_one49 value).trans (congrArg value view_eq49)
private noncomputable def view50 : View := normalized_cursor_cut% (Observe cut50.2)
private theorem view_eq50 : Observe cut50.2 = view50 := by checked_cut_rfl
private theorem read_one50 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut50 = value (Observe cut50.2) := by
  change value (Observe cut50.2) * 1 = value (Observe cut50.2)
  exact mul_one _
private theorem one50 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut50 = value view50 :=
  (read_one50 value).trans (congrArg value view_eq50)
private noncomputable def view51 : View := normalized_cursor_cut% (Observe cut51.2)
private theorem view_eq51 : Observe cut51.2 = view51 := by checked_cut_rfl
private theorem read_one51 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut51 = value (Observe cut51.2) := by
  change value (Observe cut51.2) * 1 = value (Observe cut51.2)
  exact mul_one _
private theorem one51 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut51 = value view51 :=
  (read_one51 value).trans (congrArg value view_eq51)
private noncomputable def view52 : View := normalized_cursor_cut% (Observe cut52.2)
private theorem view_eq52 : Observe cut52.2 = view52 := by checked_cut_rfl
private theorem read_one52 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut52 = value (Observe cut52.2) := by
  change value (Observe cut52.2) * 1 = value (Observe cut52.2)
  exact mul_one _
private theorem one52 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut52 = value view52 :=
  (read_one52 value).trans (congrArg value view_eq52)
private noncomputable def view53 : View := normalized_cursor_cut% (Observe cut53.2)
private theorem view_eq53 : Observe cut53.2 = view53 := by checked_cut_rfl
private theorem read_one53 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut53 = value (Observe cut53.2) := by
  change value (Observe cut53.2) * 1 = value (Observe cut53.2)
  exact mul_one _
private theorem one53 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut53 = value view53 :=
  (read_one53 value).trans (congrArg value view_eq53)
private noncomputable def view54 : View := normalized_cursor_cut% (Observe cut54.2)
private theorem view_eq54 : Observe cut54.2 = view54 := by checked_cut_rfl
private theorem read_one54 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut54 = value (Observe cut54.2) := by
  change value (Observe cut54.2) * 1 = value (Observe cut54.2)
  exact mul_one _
private theorem one54 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut54 = value view54 :=
  (read_one54 value).trans (congrArg value view_eq54)
private noncomputable def view55 : View := normalized_cursor_cut% (Observe cut55.2)
private theorem view_eq55 : Observe cut55.2 = view55 := by checked_cut_rfl
private theorem read_one55 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut55 = value (Observe cut55.2) := by
  change value (Observe cut55.2) * 1 = value (Observe cut55.2)
  exact mul_one _
private theorem one55 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut55 = value view55 :=
  (read_one55 value).trans (congrArg value view_eq55)
private noncomputable def view56 : View := normalized_cursor_cut% (Observe cut56.2)
private theorem view_eq56 : Observe cut56.2 = view56 := by checked_cut_rfl
private theorem read_one56 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut56 = value (Observe cut56.2) := by
  change value (Observe cut56.2) * 1 = value (Observe cut56.2)
  exact mul_one _
private theorem one56 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut56 = value view56 :=
  (read_one56 value).trans (congrArg value view_eq56)
private noncomputable def view57 : View := normalized_cursor_cut% (Observe cut57.2)
private theorem view_eq57 : Observe cut57.2 = view57 := by checked_cut_rfl
private theorem read_one57 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut57 = value (Observe cut57.2) := by
  change value (Observe cut57.2) * 1 = value (Observe cut57.2)
  exact mul_one _
private theorem one57 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut57 = value view57 :=
  (read_one57 value).trans (congrArg value view_eq57)
private noncomputable def view58 : View := normalized_cursor_cut% (Observe cut58.2)
private theorem view_eq58 : Observe cut58.2 = view58 := by checked_cut_rfl
private theorem read_one58 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut58 = value (Observe cut58.2) := by
  change value (Observe cut58.2) * 1 = value (Observe cut58.2)
  exact mul_one _
private theorem one58 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut58 = value view58 :=
  (read_one58 value).trans (congrArg value view_eq58)
private noncomputable def view59 : View := normalized_cursor_cut% (Observe cut59.2)
private theorem view_eq59 : Observe cut59.2 = view59 := by checked_cut_rfl
private theorem read_one59 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut59 = value (Observe cut59.2) := by
  change value (Observe cut59.2) * 1 = value (Observe cut59.2)
  exact mul_one _
private theorem one59 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut59 = value view59 :=
  (read_one59 value).trans (congrArg value view_eq59)
private noncomputable def view60 : View := normalized_cursor_cut% (Observe cut60.2)
private theorem view_eq60 : Observe cut60.2 = view60 := by checked_cut_rfl
private theorem read_one60 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut60 = value (Observe cut60.2) := by
  change value (Observe cut60.2) * 1 = value (Observe cut60.2)
  exact mul_one _
private theorem one60 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut60 = value view60 :=
  (read_one60 value).trans (congrArg value view_eq60)
private noncomputable def view61 : View := normalized_cursor_cut% (Observe cut61.2)
private theorem view_eq61 : Observe cut61.2 = view61 := by checked_cut_rfl
private theorem read_one61 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut61 = value (Observe cut61.2) := by
  change value (Observe cut61.2) * 1 = value (Observe cut61.2)
  exact mul_one _
private theorem one61 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut61 = value view61 :=
  (read_one61 value).trans (congrArg value view_eq61)
private noncomputable def view62 : View := normalized_cursor_cut% (Observe cut62.2)
private theorem view_eq62 : Observe cut62.2 = view62 := by checked_cut_rfl
private theorem read_one62 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut62 = value (Observe cut62.2) := by
  change value (Observe cut62.2) * 1 = value (Observe cut62.2)
  exact mul_one _
private theorem one62 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut62 = value view62 :=
  (read_one62 value).trans (congrArg value view_eq62)
private noncomputable def view63 : View := normalized_cursor_cut% (Observe cut63.2)
private theorem view_eq63 : Observe cut63.2 = view63 := by checked_cut_rfl
private theorem read_one63 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut63 = value (Observe cut63.2) := by
  change value (Observe cut63.2) * 1 = value (Observe cut63.2)
  exact mul_one _
private theorem one63 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut63 = value view63 :=
  (read_one63 value).trans (congrArg value view_eq63)
private noncomputable def view64 : View := normalized_cursor_cut% (Observe cut64.2)
private theorem view_eq64 : Observe cut64.2 = view64 := by checked_cut_rfl
private theorem read_one64 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut64 = value (Observe cut64.2) := by
  change value (Observe cut64.2) * 1 = value (Observe cut64.2)
  exact mul_one _
private theorem one64 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut64 = value view64 :=
  (read_one64 value).trans (congrArg value view_eq64)
private noncomputable def view65 : View := normalized_cursor_cut% (Observe cut65.2)
private theorem view_eq65 : Observe cut65.2 = view65 := by checked_cut_rfl
private theorem read_one65 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut65 = value (Observe cut65.2) := by
  change value (Observe cut65.2) * 1 = value (Observe cut65.2)
  exact mul_one _
private theorem one65 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut65 = value view65 :=
  (read_one65 value).trans (congrArg value view_eq65)
private noncomputable def view66 : View := normalized_cursor_cut% (Observe cut66.2)
private theorem view_eq66 : Observe cut66.2 = view66 := by checked_cut_rfl
private theorem read_one66 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut66 = value (Observe cut66.2) := by
  change value (Observe cut66.2) * 1 = value (Observe cut66.2)
  exact mul_one _
private theorem one66 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut66 = value view66 :=
  (read_one66 value).trans (congrArg value view_eq66)
private noncomputable def view67 : View := normalized_cursor_cut% (Observe cut67.2)
private theorem view_eq67 : Observe cut67.2 = view67 := by checked_cut_rfl
private theorem read_one67 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut67 = value (Observe cut67.2) := by
  change value (Observe cut67.2) * 1 = value (Observe cut67.2)
  exact mul_one _
private theorem one67 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut67 = value view67 :=
  (read_one67 value).trans (congrArg value view_eq67)
private noncomputable def view68 : View := normalized_cursor_cut% (Observe cut68.2)
private theorem view_eq68 : Observe cut68.2 = view68 := by checked_cut_rfl
private theorem read_one68 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut68 = value (Observe cut68.2) := by
  change value (Observe cut68.2) * 1 = value (Observe cut68.2)
  exact mul_one _
private theorem one68 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut68 = value view68 :=
  (read_one68 value).trans (congrArg value view_eq68)
private noncomputable def view69 : View := normalized_cursor_cut% (Observe cut69.2)
private theorem view_eq69 : Observe cut69.2 = view69 := by checked_cut_rfl
private theorem read_one69 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut69 = value (Observe cut69.2) := by
  change value (Observe cut69.2) * 1 = value (Observe cut69.2)
  exact mul_one _
private theorem one69 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut69 = value view69 :=
  (read_one69 value).trans (congrArg value view_eq69)
private noncomputable def view70 : View := normalized_cursor_cut% (Observe cut70.2)
private theorem view_eq70 : Observe cut70.2 = view70 := by checked_cut_rfl
private theorem read_one70 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut70 = value (Observe cut70.2) := by
  change value (Observe cut70.2) * 1 = value (Observe cut70.2)
  exact mul_one _
private theorem one70 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut70 = value view70 :=
  (read_one70 value).trans (congrArg value view_eq70)
private noncomputable def view71 : View := normalized_cursor_cut% (Observe cut71.2)
private theorem view_eq71 : Observe cut71.2 = view71 := by checked_cut_rfl
private theorem read_one71 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut71 = value (Observe cut71.2) := by
  change value (Observe cut71.2) * 1 = value (Observe cut71.2)
  exact mul_one _
private theorem one71 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut71 = value view71 :=
  (read_one71 value).trans (congrArg value view_eq71)
private noncomputable def view72 : View := normalized_cursor_cut% (Observe cut72.2)
private theorem view_eq72 : Observe cut72.2 = view72 := by checked_cut_rfl
private theorem read_one72 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut72 = value (Observe cut72.2) := by
  change value (Observe cut72.2) * 1 = value (Observe cut72.2)
  exact mul_one _
private theorem one72 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut72 = value view72 :=
  (read_one72 value).trans (congrArg value view_eq72)
private noncomputable def view73 : View := normalized_cursor_cut% (Observe cut73.2)
private theorem view_eq73 : Observe cut73.2 = view73 := by checked_cut_rfl
private theorem read_one73 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut73 = value (Observe cut73.2) := by
  change value (Observe cut73.2) * 1 = value (Observe cut73.2)
  exact mul_one _
private theorem one73 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut73 = value view73 :=
  (read_one73 value).trans (congrArg value view_eq73)
private noncomputable def view74 : View := normalized_cursor_cut% (Observe cut74.2)
private theorem view_eq74 : Observe cut74.2 = view74 := by checked_cut_rfl
private theorem read_one74 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut74 = value (Observe cut74.2) := by
  change value (Observe cut74.2) * 1 = value (Observe cut74.2)
  exact mul_one _
private theorem one74 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut74 = value view74 :=
  (read_one74 value).trans (congrArg value view_eq74)
private noncomputable def view75 : View := normalized_cursor_cut% (Observe cut75.2)
private theorem view_eq75 : Observe cut75.2 = view75 := by checked_cut_rfl
private theorem read_one75 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut75 = value (Observe cut75.2) := by
  change value (Observe cut75.2) * 1 = value (Observe cut75.2)
  exact mul_one _
private theorem one75 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut75 = value view75 :=
  (read_one75 value).trans (congrArg value view_eq75)
private noncomputable def view76 : View := normalized_cursor_cut% (Observe cut76.2)
private theorem view_eq76 : Observe cut76.2 = view76 := by checked_cut_rfl
private theorem read_one76 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut76 = value (Observe cut76.2) := by
  change value (Observe cut76.2) * 1 = value (Observe cut76.2)
  exact mul_one _
private theorem one76 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut76 = value view76 :=
  (read_one76 value).trans (congrArg value view_eq76)
private noncomputable def view77 : View := normalized_cursor_cut% (Observe cut77.2)
private theorem view_eq77 : Observe cut77.2 = view77 := by checked_cut_rfl
private theorem read_one77 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut77 = value (Observe cut77.2) := by
  change value (Observe cut77.2) * 1 = value (Observe cut77.2)
  exact mul_one _
private theorem one77 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut77 = value view77 :=
  (read_one77 value).trans (congrArg value view_eq77)
private noncomputable def view78 : View := normalized_cursor_cut% (Observe cut78.2)
private theorem view_eq78 : Observe cut78.2 = view78 := by checked_cut_rfl
private theorem read_one78 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut78 = value (Observe cut78.2) := by
  change value (Observe cut78.2) * 1 = value (Observe cut78.2)
  exact mul_one _
private theorem one78 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut78 = value view78 :=
  (read_one78 value).trans (congrArg value view_eq78)
private noncomputable def view79 : View := normalized_cursor_cut% (Observe cut79.2)
private theorem view_eq79 : Observe cut79.2 = view79 := by checked_cut_rfl
private theorem read_one79 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut79 = value (Observe cut79.2) := by
  change value (Observe cut79.2) * 1 = value (Observe cut79.2)
  exact mul_one _
private theorem one79 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut79 = value view79 :=
  (read_one79 value).trans (congrArg value view_eq79)
private noncomputable def view80 : View := normalized_cursor_cut% (Observe cut80.2)
private theorem view_eq80 : Observe cut80.2 = view80 := by checked_cut_rfl
private theorem read_one80 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut80 = value (Observe cut80.2) := by
  change value (Observe cut80.2) * 1 = value (Observe cut80.2)
  exact mul_one _
private theorem one80 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut80 = value view80 :=
  (read_one80 value).trans (congrArg value view_eq80)
private noncomputable def view81 : View := normalized_cursor_cut% (Observe cut81.2)
private theorem view_eq81 : Observe cut81.2 = view81 := by checked_cut_rfl
private theorem read_one81 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut81 = value (Observe cut81.2) := by
  change value (Observe cut81.2) * 1 = value (Observe cut81.2)
  exact mul_one _
private theorem one81 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut81 = value view81 :=
  (read_one81 value).trans (congrArg value view_eq81)
private noncomputable def view82 : View := normalized_cursor_cut% (Observe cut82.2)
private theorem view_eq82 : Observe cut82.2 = view82 := by checked_cut_rfl
private theorem read_one82 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut82 = value (Observe cut82.2) := by
  change value (Observe cut82.2) * 1 = value (Observe cut82.2)
  exact mul_one _
private theorem one82 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut82 = value view82 :=
  (read_one82 value).trans (congrArg value view_eq82)
private noncomputable def view83 : View := normalized_cursor_cut% (Observe cut83.2)
private theorem view_eq83 : Observe cut83.2 = view83 := by checked_cut_rfl
private theorem read_one83 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut83 = value (Observe cut83.2) := by
  change value (Observe cut83.2) * 1 = value (Observe cut83.2)
  exact mul_one _
private theorem one83 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut83 = value view83 :=
  (read_one83 value).trans (congrArg value view_eq83)
private noncomputable def view84 : View := normalized_cursor_cut% (Observe cut84.2)
private theorem view_eq84 : Observe cut84.2 = view84 := by checked_cut_rfl
private theorem read_one84 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut84 = value (Observe cut84.2) := by
  change value (Observe cut84.2) * 1 = value (Observe cut84.2)
  exact mul_one _
private theorem one84 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut84 = value view84 :=
  (read_one84 value).trans (congrArg value view_eq84)
private noncomputable def view85 : View := normalized_cursor_cut% (Observe cut85.2)
private theorem view_eq85 : Observe cut85.2 = view85 := by checked_cut_rfl
private theorem read_one85 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut85 = value (Observe cut85.2) := by
  change value (Observe cut85.2) * 1 = value (Observe cut85.2)
  exact mul_one _
private theorem one85 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut85 = value view85 :=
  (read_one85 value).trans (congrArg value view_eq85)
private noncomputable def view86 : View := normalized_cursor_cut% (Observe cut86.2)
private theorem view_eq86 : Observe cut86.2 = view86 := by checked_cut_rfl
private theorem read_one86 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut86 = value (Observe cut86.2) := by
  change value (Observe cut86.2) * 1 = value (Observe cut86.2)
  exact mul_one _
private theorem one86 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut86 = value view86 :=
  (read_one86 value).trans (congrArg value view_eq86)
private noncomputable def view87 : View := normalized_cursor_cut% (Observe cut87.2)
private theorem view_eq87 : Observe cut87.2 = view87 := by checked_cut_rfl
private theorem read_one87 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut87 = value (Observe cut87.2) := by
  change value (Observe cut87.2) * 1 = value (Observe cut87.2)
  exact mul_one _
private theorem one87 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut87 = value view87 :=
  (read_one87 value).trans (congrArg value view_eq87)
private noncomputable def view88 : View := normalized_cursor_cut% (Observe cut88.2)
private theorem view_eq88 : Observe cut88.2 = view88 := by checked_cut_rfl
private theorem read_one88 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut88 = value (Observe cut88.2) := by
  change value (Observe cut88.2) * 1 = value (Observe cut88.2)
  exact mul_one _
private theorem one88 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut88 = value view88 :=
  (read_one88 value).trans (congrArg value view_eq88)
private noncomputable def view89 : View := normalized_cursor_cut% (Observe cut89.2)
private theorem view_eq89 : Observe cut89.2 = view89 := by checked_cut_rfl
private theorem read_one89 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut89 = value (Observe cut89.2) := by
  change value (Observe cut89.2) * 1 = value (Observe cut89.2)
  exact mul_one _
private theorem one89 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut89 = value view89 :=
  (read_one89 value).trans (congrArg value view_eq89)
private noncomputable def view90 : View := normalized_cursor_cut% (Observe cut90.2)
private theorem view_eq90 : Observe cut90.2 = view90 := by checked_cut_rfl
private theorem read_one90 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut90 = value (Observe cut90.2) := by
  change value (Observe cut90.2) * 1 = value (Observe cut90.2)
  exact mul_one _
private theorem one90 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut90 = value view90 :=
  (read_one90 value).trans (congrArg value view_eq90)
private noncomputable def view91 : View := normalized_cursor_cut% (Observe cut91.2)
private theorem view_eq91 : Observe cut91.2 = view91 := by checked_cut_rfl
private theorem read_one91 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut91 = value (Observe cut91.2) := by
  change value (Observe cut91.2) * 1 = value (Observe cut91.2)
  exact mul_one _
private theorem one91 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut91 = value view91 :=
  (read_one91 value).trans (congrArg value view_eq91)
private noncomputable def view92 : View := normalized_cursor_cut% (Observe cut92.2)
private theorem view_eq92 : Observe cut92.2 = view92 := by checked_cut_rfl
private theorem read_one92 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut92 = value (Observe cut92.2) := by
  change value (Observe cut92.2) * 1 = value (Observe cut92.2)
  exact mul_one _
private theorem one92 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut92 = value view92 :=
  (read_one92 value).trans (congrArg value view_eq92)
private noncomputable def view93 : View := normalized_cursor_cut% (Observe cut93.2)
private theorem view_eq93 : Observe cut93.2 = view93 := by checked_cut_rfl
private theorem read_one93 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut93 = value (Observe cut93.2) := by
  change value (Observe cut93.2) * 1 = value (Observe cut93.2)
  exact mul_one _
private theorem one93 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut93 = value view93 :=
  (read_one93 value).trans (congrArg value view_eq93)
private noncomputable def view94 : View := normalized_cursor_cut% (Observe cut94.2)
private theorem view_eq94 : Observe cut94.2 = view94 := by checked_cut_rfl
private theorem read_one94 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut94 = value (Observe cut94.2) := by
  change value (Observe cut94.2) * 1 = value (Observe cut94.2)
  exact mul_one _
private theorem one94 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut94 = value view94 :=
  (read_one94 value).trans (congrArg value view_eq94)
private noncomputable def view95 : View := normalized_cursor_cut% (Observe cut95.2)
private theorem view_eq95 : Observe cut95.2 = view95 := by checked_cut_rfl
private theorem read_one95 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut95 = value (Observe cut95.2) := by
  change value (Observe cut95.2) * 1 = value (Observe cut95.2)
  exact mul_one _
private theorem one95 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut95 = value view95 :=
  (read_one95 value).trans (congrArg value view_eq95)
private noncomputable def view96 : View := normalized_cursor_cut% (Observe cut96.2)
private theorem view_eq96 : Observe cut96.2 = view96 := by checked_cut_rfl
private theorem read_one96 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut96 = value (Observe cut96.2) := by
  change value (Observe cut96.2) * 1 = value (Observe cut96.2)
  exact mul_one _
private theorem one96 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut96 = value view96 :=
  (read_one96 value).trans (congrArg value view_eq96)
private noncomputable def view97 : View := normalized_cursor_cut% (Observe cut97.2)
private theorem view_eq97 : Observe cut97.2 = view97 := by checked_cut_rfl
private theorem read_one97 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut97 = value (Observe cut97.2) := by
  change value (Observe cut97.2) * 1 = value (Observe cut97.2)
  exact mul_one _
private theorem one97 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut97 = value view97 :=
  (read_one97 value).trans (congrArg value view_eq97)
private noncomputable def view98 : View := normalized_cursor_cut% (Observe cut98.2)
private theorem view_eq98 : Observe cut98.2 = view98 := by checked_cut_rfl
private theorem read_one98 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut98 = value (Observe cut98.2) := by
  change value (Observe cut98.2) * 1 = value (Observe cut98.2)
  exact mul_one _
private theorem one98 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut98 = value view98 :=
  (read_one98 value).trans (congrArg value view_eq98)
private noncomputable def view99 : View := normalized_cursor_cut% (Observe cut99.2)
private theorem view_eq99 : Observe cut99.2 = view99 := by checked_cut_rfl
private theorem read_one99 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut99 = value (Observe cut99.2) := by
  change value (Observe cut99.2) * 1 = value (Observe cut99.2)
  exact mul_one _
private theorem one99 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut99 = value view99 :=
  (read_one99 value).trans (congrArg value view_eq99)
private noncomputable def view100 : View := normalized_cursor_cut% (Observe cut100.2)
private theorem view_eq100 : Observe cut100.2 = view100 := by checked_cut_rfl
private theorem read_one100 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut100 = value (Observe cut100.2) := by
  change value (Observe cut100.2) * 1 = value (Observe cut100.2)
  exact mul_one _
private theorem one100 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut100 = value view100 :=
  (read_one100 value).trans (congrArg value view_eq100)
private noncomputable def view101 : View := normalized_cursor_cut% (Observe cut101.2)
private theorem view_eq101 : Observe cut101.2 = view101 := by checked_cut_rfl
private theorem read_one101 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut101 = value (Observe cut101.2) := by
  change value (Observe cut101.2) * 1 = value (Observe cut101.2)
  exact mul_one _
private theorem one101 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut101 = value view101 :=
  (read_one101 value).trans (congrArg value view_eq101)
private noncomputable def view102 : View := normalized_cursor_cut% (Observe cut102.2)
private theorem view_eq102 : Observe cut102.2 = view102 := by checked_cut_rfl
private theorem read_one102 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut102 = value (Observe cut102.2) := by
  change value (Observe cut102.2) * 1 = value (Observe cut102.2)
  exact mul_one _
private theorem one102 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut102 = value view102 :=
  (read_one102 value).trans (congrArg value view_eq102)
private noncomputable def view103 : View := normalized_cursor_cut% (Observe cut103.2)
private theorem view_eq103 : Observe cut103.2 = view103 := by checked_cut_rfl
private theorem read_one103 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut103 = value (Observe cut103.2) := by
  change value (Observe cut103.2) * 1 = value (Observe cut103.2)
  exact mul_one _
private theorem one103 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut103 = value view103 :=
  (read_one103 value).trans (congrArg value view_eq103)
private noncomputable def view104 : View := normalized_cursor_cut% (Observe cut104.2)
private theorem view_eq104 : Observe cut104.2 = view104 := by checked_cut_rfl
private theorem read_one104 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut104 = value (Observe cut104.2) := by
  change value (Observe cut104.2) * 1 = value (Observe cut104.2)
  exact mul_one _
private theorem one104 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut104 = value view104 :=
  (read_one104 value).trans (congrArg value view_eq104)
private noncomputable def view105 : View := normalized_cursor_cut% (Observe cut105.2)
private theorem view_eq105 : Observe cut105.2 = view105 := by checked_cut_rfl
private theorem read_one105 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut105 = value (Observe cut105.2) := by
  change value (Observe cut105.2) * 1 = value (Observe cut105.2)
  exact mul_one _
private theorem one105 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut105 = value view105 :=
  (read_one105 value).trans (congrArg value view_eq105)
private noncomputable def view106 : View := normalized_cursor_cut% (Observe cut106.2)
private theorem view_eq106 : Observe cut106.2 = view106 := by checked_cut_rfl
private theorem read_one106 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut106 = value (Observe cut106.2) := by
  change value (Observe cut106.2) * 1 = value (Observe cut106.2)
  exact mul_one _
private theorem one106 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut106 = value view106 :=
  (read_one106 value).trans (congrArg value view_eq106)
private noncomputable def view107 : View := normalized_cursor_cut% (Observe cut107.2)
private theorem view_eq107 : Observe cut107.2 = view107 := by checked_cut_rfl
private theorem read_one107 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut107 = value (Observe cut107.2) := by
  change value (Observe cut107.2) * 1 = value (Observe cut107.2)
  exact mul_one _
private theorem one107 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut107 = value view107 :=
  (read_one107 value).trans (congrArg value view_eq107)
private noncomputable def view108 : View := normalized_cursor_cut% (Observe cut108.2)
private theorem view_eq108 : Observe cut108.2 = view108 := by checked_cut_rfl
private theorem read_one108 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut108 = value (Observe cut108.2) := by
  change value (Observe cut108.2) * 1 = value (Observe cut108.2)
  exact mul_one _
private theorem one108 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut108 = value view108 :=
  (read_one108 value).trans (congrArg value view_eq108)
private noncomputable def view109 : View := normalized_cursor_cut% (Observe cut109.2)
private theorem view_eq109 : Observe cut109.2 = view109 := by checked_cut_rfl
private theorem read_one109 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut109 = value (Observe cut109.2) := by
  change value (Observe cut109.2) * 1 = value (Observe cut109.2)
  exact mul_one _
private theorem one109 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut109 = value view109 :=
  (read_one109 value).trans (congrArg value view_eq109)
private noncomputable def view110 : View := normalized_cursor_cut% (Observe cut110.2)
private theorem view_eq110 : Observe cut110.2 = view110 := by checked_cut_rfl
private theorem read_one110 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut110 = value (Observe cut110.2) := by
  change value (Observe cut110.2) * 1 = value (Observe cut110.2)
  exact mul_one _
private theorem one110 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut110 = value view110 :=
  (read_one110 value).trans (congrArg value view_eq110)
private noncomputable def view111 : View := normalized_cursor_cut% (Observe cut111.2)
private theorem view_eq111 : Observe cut111.2 = view111 := by checked_cut_rfl
private theorem read_one111 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut111 = value (Observe cut111.2) := by
  change value (Observe cut111.2) * 1 = value (Observe cut111.2)
  exact mul_one _
private theorem one111 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut111 = value view111 :=
  (read_one111 value).trans (congrArg value view_eq111)
private noncomputable def view112 : View := normalized_cursor_cut% (Observe cut112.2)
private theorem view_eq112 : Observe cut112.2 = view112 := by checked_cut_rfl
private theorem read_one112 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut112 = value (Observe cut112.2) := by
  change value (Observe cut112.2) * 1 = value (Observe cut112.2)
  exact mul_one _
private theorem one112 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut112 = value view112 :=
  (read_one112 value).trans (congrArg value view_eq112)
private noncomputable def view113 : View := normalized_cursor_cut% (Observe cut113.2)
private theorem view_eq113 : Observe cut113.2 = view113 := by checked_cut_rfl
private theorem read_one113 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut113 = value (Observe cut113.2) := by
  change value (Observe cut113.2) * 1 = value (Observe cut113.2)
  exact mul_one _
private theorem one113 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut113 = value view113 :=
  (read_one113 value).trans (congrArg value view_eq113)
private noncomputable def view114 : View := normalized_cursor_cut% (Observe cut114.2)
private theorem view_eq114 : Observe cut114.2 = view114 := by checked_cut_rfl
private theorem read_one114 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut114 = value (Observe cut114.2) := by
  change value (Observe cut114.2) * 1 = value (Observe cut114.2)
  exact mul_one _
private theorem one114 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut114 = value view114 :=
  (read_one114 value).trans (congrArg value view_eq114)
private noncomputable def view115 : View := normalized_cursor_cut% (Observe cut115.2)
private theorem view_eq115 : Observe cut115.2 = view115 := by checked_cut_rfl
private theorem read_one115 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut115 = value (Observe cut115.2) := by
  change value (Observe cut115.2) * 1 = value (Observe cut115.2)
  exact mul_one _
private theorem one115 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut115 = value view115 :=
  (read_one115 value).trans (congrArg value view_eq115)
private noncomputable def view116 : View := normalized_cursor_cut% (Observe cut116.2)
private theorem view_eq116 : Observe cut116.2 = view116 := by checked_cut_rfl
private theorem read_one116 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut116 = value (Observe cut116.2) := by
  change value (Observe cut116.2) * 1 = value (Observe cut116.2)
  exact mul_one _
private theorem one116 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut116 = value view116 :=
  (read_one116 value).trans (congrArg value view_eq116)
private noncomputable def view117 : View := normalized_cursor_cut% (Observe cut117.2)
private theorem view_eq117 : Observe cut117.2 = view117 := by checked_cut_rfl
private theorem read_one117 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut117 = value (Observe cut117.2) := by
  change value (Observe cut117.2) * 1 = value (Observe cut117.2)
  exact mul_one _
private theorem one117 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut117 = value view117 :=
  (read_one117 value).trans (congrArg value view_eq117)
private noncomputable def view118 : View := normalized_cursor_cut% (Observe cut118.2)
private theorem view_eq118 : Observe cut118.2 = view118 := by checked_cut_rfl
private theorem read_one118 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut118 = value (Observe cut118.2) := by
  change value (Observe cut118.2) * 1 = value (Observe cut118.2)
  exact mul_one _
private theorem one118 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut118 = value view118 :=
  (read_one118 value).trans (congrArg value view_eq118)
private noncomputable def view119 : View := normalized_cursor_cut% (Observe cut119.2)
private theorem view_eq119 : Observe cut119.2 = view119 := by checked_cut_rfl
private theorem read_one119 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut119 = value (Observe cut119.2) := by
  change value (Observe cut119.2) * 1 = value (Observe cut119.2)
  exact mul_one _
private theorem one119 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut119 = value view119 :=
  (read_one119 value).trans (congrArg value view_eq119)
private noncomputable def view120 : View := normalized_cursor_cut% (Observe cut120.2)
private theorem view_eq120 : Observe cut120.2 = view120 := by checked_cut_rfl
private theorem read_one120 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut120 = value (Observe cut120.2) := by
  change value (Observe cut120.2) * 1 = value (Observe cut120.2)
  exact mul_one _
private theorem one120 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut120 = value view120 :=
  (read_one120 value).trans (congrArg value view_eq120)
private noncomputable def view121 : View := normalized_cursor_cut% (Observe cut121.2)
private theorem view_eq121 : Observe cut121.2 = view121 := by checked_cut_rfl
private theorem read_one121 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut121 = value (Observe cut121.2) := by
  change value (Observe cut121.2) * 1 = value (Observe cut121.2)
  exact mul_one _
private theorem one121 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut121 = value view121 :=
  (read_one121 value).trans (congrArg value view_eq121)
private noncomputable def view122 : View := normalized_cursor_cut% (Observe cut122.2)
private theorem view_eq122 : Observe cut122.2 = view122 := by checked_cut_rfl
private theorem read_one122 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut122 = value (Observe cut122.2) := by
  change value (Observe cut122.2) * 1 = value (Observe cut122.2)
  exact mul_one _
private theorem one122 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut122 = value view122 :=
  (read_one122 value).trans (congrArg value view_eq122)
private noncomputable def view123 : View := normalized_cursor_cut% (Observe cut123.2)
private theorem view_eq123 : Observe cut123.2 = view123 := by checked_cut_rfl
private theorem read_one123 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut123 = value (Observe cut123.2) := by
  change value (Observe cut123.2) * 1 = value (Observe cut123.2)
  exact mul_one _
private theorem one123 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut123 = value view123 :=
  (read_one123 value).trans (congrArg value view_eq123)
private noncomputable def view124 : View := normalized_cursor_cut% (Observe cut124.2)
private theorem view_eq124 : Observe cut124.2 = view124 := by checked_cut_rfl
private theorem read_one124 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut124 = value (Observe cut124.2) := by
  change value (Observe cut124.2) * 1 = value (Observe cut124.2)
  exact mul_one _
private theorem one124 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut124 = value view124 :=
  (read_one124 value).trans (congrArg value view_eq124)
private noncomputable def view125 : View := normalized_cursor_cut% (Observe cut125.2)
private theorem view_eq125 : Observe cut125.2 = view125 := by checked_cut_rfl
private theorem read_one125 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut125 = value (Observe cut125.2) := by
  change value (Observe cut125.2) * 1 = value (Observe cut125.2)
  exact mul_one _
private theorem one125 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut125 = value view125 :=
  (read_one125 value).trans (congrArg value view_eq125)
private noncomputable def view126 : View := normalized_cursor_cut% (Observe cut126.2)
private theorem view_eq126 : Observe cut126.2 = view126 := by checked_cut_rfl
private theorem read_one126 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut126 = value (Observe cut126.2) := by
  change value (Observe cut126.2) * 1 = value (Observe cut126.2)
  exact mul_one _
private theorem one126 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut126 = value view126 :=
  (read_one126 value).trans (congrArg value view_eq126)
private noncomputable def view127 : View := normalized_cursor_cut% (Observe cut127.2)
private theorem view_eq127 : Observe cut127.2 = view127 := by checked_cut_rfl
private theorem read_one127 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut127 = value (Observe cut127.2) := by
  change value (Observe cut127.2) * 1 = value (Observe cut127.2)
  exact mul_one _
private theorem one127 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut127 = value view127 :=
  (read_one127 value).trans (congrArg value view_eq127)
private noncomputable def view128 : View := normalized_cursor_cut% (Observe cut128.2)
private theorem view_eq128 : Observe cut128.2 = view128 := by checked_cut_rfl
private theorem read_one128 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut128 = value (Observe cut128.2) := by
  change value (Observe cut128.2) * 1 = value (Observe cut128.2)
  exact mul_one _
private theorem one128 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut128 = value view128 :=
  (read_one128 value).trans (congrArg value view_eq128)
private noncomputable def view129 : View := normalized_cursor_cut% (Observe cut129.2)
private theorem view_eq129 : Observe cut129.2 = view129 := by checked_cut_rfl
private theorem read_one129 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut129 = value (Observe cut129.2) := by
  change value (Observe cut129.2) * 1 = value (Observe cut129.2)
  exact mul_one _
private theorem one129 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut129 = value view129 :=
  (read_one129 value).trans (congrArg value view_eq129)
private noncomputable def view130 : View := normalized_cursor_cut% (Observe cut130.2)
private theorem view_eq130 : Observe cut130.2 = view130 := by checked_cut_rfl
private theorem read_one130 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut130 = value (Observe cut130.2) := by
  change value (Observe cut130.2) * 1 = value (Observe cut130.2)
  exact mul_one _
private theorem one130 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut130 = value view130 :=
  (read_one130 value).trans (congrArg value view_eq130)
private noncomputable def view131 : View := normalized_cursor_cut% (Observe cut131.2)
private theorem view_eq131 : Observe cut131.2 = view131 := by checked_cut_rfl
private theorem read_one131 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut131 = value (Observe cut131.2) := by
  change value (Observe cut131.2) * 1 = value (Observe cut131.2)
  exact mul_one _
private theorem one131 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut131 = value view131 :=
  (read_one131 value).trans (congrArg value view_eq131)
private noncomputable def view132 : View := normalized_cursor_cut% (Observe cut132.2)
private theorem view_eq132 : Observe cut132.2 = view132 := by checked_cut_rfl
private theorem read_one132 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut132 = value (Observe cut132.2) := by
  change value (Observe cut132.2) * 1 = value (Observe cut132.2)
  exact mul_one _
private theorem one132 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut132 = value view132 :=
  (read_one132 value).trans (congrArg value view_eq132)
private noncomputable def view133 : View := normalized_cursor_cut% (Observe cut133.2)
private theorem view_eq133 : Observe cut133.2 = view133 := by checked_cut_rfl
private theorem read_one133 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut133 = value (Observe cut133.2) := by
  change value (Observe cut133.2) * 1 = value (Observe cut133.2)
  exact mul_one _
private theorem one133 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut133 = value view133 :=
  (read_one133 value).trans (congrArg value view_eq133)
private noncomputable def view134 : View := normalized_cursor_cut% (Observe cut134.2)
private theorem view_eq134 : Observe cut134.2 = view134 := by checked_cut_rfl
private theorem read_one134 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut134 = value (Observe cut134.2) := by
  change value (Observe cut134.2) * 1 = value (Observe cut134.2)
  exact mul_one _
private theorem one134 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut134 = value view134 :=
  (read_one134 value).trans (congrArg value view_eq134)
private noncomputable def view135 : View := normalized_cursor_cut% (Observe cut135.2)
private theorem view_eq135 : Observe cut135.2 = view135 := by checked_cut_rfl
private theorem read_one135 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut135 = value (Observe cut135.2) := by
  change value (Observe cut135.2) * 1 = value (Observe cut135.2)
  exact mul_one _
private theorem one135 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut135 = value view135 :=
  (read_one135 value).trans (congrArg value view_eq135)
private noncomputable def view136 : View := normalized_cursor_cut% (Observe cut136.2)
private theorem view_eq136 : Observe cut136.2 = view136 := by checked_cut_rfl
private theorem read_one136 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut136 = value (Observe cut136.2) := by
  change value (Observe cut136.2) * 1 = value (Observe cut136.2)
  exact mul_one _
private theorem one136 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut136 = value view136 :=
  (read_one136 value).trans (congrArg value view_eq136)
private noncomputable def view137 : View := normalized_cursor_cut% (Observe cut137.2)
private theorem view_eq137 : Observe cut137.2 = view137 := by checked_cut_rfl
private theorem read_one137 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut137 = value (Observe cut137.2) := by
  change value (Observe cut137.2) * 1 = value (Observe cut137.2)
  exact mul_one _
private theorem one137 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut137 = value view137 :=
  (read_one137 value).trans (congrArg value view_eq137)
private noncomputable def view138 : View := normalized_cursor_cut% (Observe cut138.2)
private theorem view_eq138 : Observe cut138.2 = view138 := by checked_cut_rfl
private theorem read_one138 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut138 = value (Observe cut138.2) := by
  change value (Observe cut138.2) * 1 = value (Observe cut138.2)
  exact mul_one _
private theorem one138 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut138 = value view138 :=
  (read_one138 value).trans (congrArg value view_eq138)
private noncomputable def view139 : View := normalized_cursor_cut% (Observe cut139.2)
private theorem view_eq139 : Observe cut139.2 = view139 := by checked_cut_rfl
private theorem read_one139 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut139 = value (Observe cut139.2) := by
  change value (Observe cut139.2) * 1 = value (Observe cut139.2)
  exact mul_one _
private theorem one139 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut139 = value view139 :=
  (read_one139 value).trans (congrArg value view_eq139)
private noncomputable def view140 : View := normalized_cursor_cut% (Observe cut140.2)
private theorem view_eq140 : Observe cut140.2 = view140 := by checked_cut_rfl
private theorem read_one140 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut140 = value (Observe cut140.2) := by
  change value (Observe cut140.2) * 1 = value (Observe cut140.2)
  exact mul_one _
private theorem one140 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut140 = value view140 :=
  (read_one140 value).trans (congrArg value view_eq140)
private noncomputable def view141 : View := normalized_cursor_cut% (Observe cut141.2)
private theorem view_eq141 : Observe cut141.2 = view141 := by checked_cut_rfl
private theorem read_one141 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut141 = value (Observe cut141.2) := by
  change value (Observe cut141.2) * 1 = value (Observe cut141.2)
  exact mul_one _
private theorem one141 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut141 = value view141 :=
  (read_one141 value).trans (congrArg value view_eq141)
private noncomputable def view142 : View := normalized_cursor_cut% (Observe cut142.2)
private theorem view_eq142 : Observe cut142.2 = view142 := by checked_cut_rfl
private theorem read_one142 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut142 = value (Observe cut142.2) := by
  change value (Observe cut142.2) * 1 = value (Observe cut142.2)
  exact mul_one _
private theorem one142 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut142 = value view142 :=
  (read_one142 value).trans (congrArg value view_eq142)
private noncomputable def view143 : View := normalized_cursor_cut% (Observe cut143.2)
private theorem view_eq143 : Observe cut143.2 = view143 := by checked_cut_rfl
private theorem read_one143 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut143 = value (Observe cut143.2) := by
  change value (Observe cut143.2) * 1 = value (Observe cut143.2)
  exact mul_one _
private theorem one143 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut143 = value view143 :=
  (read_one143 value).trans (congrArg value view_eq143)
private noncomputable def view144 : View := normalized_cursor_cut% (Observe cut144.2)
private theorem view_eq144 : Observe cut144.2 = view144 := by checked_cut_rfl
private theorem read_one144 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut144 = value (Observe cut144.2) := by
  change value (Observe cut144.2) * 1 = value (Observe cut144.2)
  exact mul_one _
private theorem one144 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut144 = value view144 :=
  (read_one144 value).trans (congrArg value view_eq144)
private noncomputable def view145 : View := normalized_cursor_cut% (Observe cut145.2)
private theorem view_eq145 : Observe cut145.2 = view145 := by checked_cut_rfl
private theorem read_one145 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut145 = value (Observe cut145.2) := by
  change value (Observe cut145.2) * 1 = value (Observe cut145.2)
  exact mul_one _
private theorem one145 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut145 = value view145 :=
  (read_one145 value).trans (congrArg value view_eq145)
private noncomputable def view146 : View := normalized_cursor_cut% (Observe cut146.2)
private theorem view_eq146 : Observe cut146.2 = view146 := by checked_cut_rfl
private theorem read_one146 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut146 = value (Observe cut146.2) := by
  change value (Observe cut146.2) * 1 = value (Observe cut146.2)
  exact mul_one _
private theorem one146 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut146 = value view146 :=
  (read_one146 value).trans (congrArg value view_eq146)
private noncomputable def view147 : View := normalized_cursor_cut% (Observe cut147.2)
private theorem view_eq147 : Observe cut147.2 = view147 := by checked_cut_rfl
private theorem read_one147 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut147 = value (Observe cut147.2) := by
  change value (Observe cut147.2) * 1 = value (Observe cut147.2)
  exact mul_one _
private theorem one147 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut147 = value view147 :=
  (read_one147 value).trans (congrArg value view_eq147)
private noncomputable def view148 : View := normalized_cursor_cut% (Observe cut148.2)
private theorem view_eq148 : Observe cut148.2 = view148 := by checked_cut_rfl
private theorem read_one148 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut148 = value (Observe cut148.2) := by
  change value (Observe cut148.2) * 1 = value (Observe cut148.2)
  exact mul_one _
private theorem one148 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut148 = value view148 :=
  (read_one148 value).trans (congrArg value view_eq148)
private noncomputable def view149 : View := normalized_cursor_cut% (Observe cut149.2)
private theorem view_eq149 : Observe cut149.2 = view149 := by checked_cut_rfl
private theorem read_one149 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut149 = value (Observe cut149.2) := by
  change value (Observe cut149.2) * 1 = value (Observe cut149.2)
  exact mul_one _
private theorem one149 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut149 = value view149 :=
  (read_one149 value).trans (congrArg value view_eq149)
private noncomputable def view150 : View := normalized_cursor_cut% (Observe cut150.2)
private theorem view_eq150 : Observe cut150.2 = view150 := by checked_cut_rfl
private theorem read_one150 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut150 = value (Observe cut150.2) := by
  change value (Observe cut150.2) * 1 = value (Observe cut150.2)
  exact mul_one _
private theorem one150 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut150 = value view150 :=
  (read_one150 value).trans (congrArg value view_eq150)
private noncomputable def view151 : View := normalized_cursor_cut% (Observe cut151.2)
private theorem view_eq151 : Observe cut151.2 = view151 := by checked_cut_rfl
private theorem read_one151 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut151 = value (Observe cut151.2) := by
  change value (Observe cut151.2) * 1 = value (Observe cut151.2)
  exact mul_one _
private theorem one151 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut151 = value view151 :=
  (read_one151 value).trans (congrArg value view_eq151)
private noncomputable def view152 : View := normalized_cursor_cut% (Observe cut152.2)
private theorem view_eq152 : Observe cut152.2 = view152 := by checked_cut_rfl
private theorem read_one152 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut152 = value (Observe cut152.2) := by
  change value (Observe cut152.2) * 1 = value (Observe cut152.2)
  exact mul_one _
private theorem one152 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut152 = value view152 :=
  (read_one152 value).trans (congrArg value view_eq152)
private noncomputable def view153 : View := normalized_cursor_cut% (Observe cut153.2)
private theorem view_eq153 : Observe cut153.2 = view153 := by checked_cut_rfl
private theorem read_one153 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut153 = value (Observe cut153.2) := by
  change value (Observe cut153.2) * 1 = value (Observe cut153.2)
  exact mul_one _
private theorem one153 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut153 = value view153 :=
  (read_one153 value).trans (congrArg value view_eq153)
private noncomputable def view154 : View := normalized_cursor_cut% (Observe cut154.2)
private theorem view_eq154 : Observe cut154.2 = view154 := by checked_cut_rfl
private theorem read_one154 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut154 = value (Observe cut154.2) := by
  change value (Observe cut154.2) * 1 = value (Observe cut154.2)
  exact mul_one _
private theorem one154 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut154 = value view154 :=
  (read_one154 value).trans (congrArg value view_eq154)
private noncomputable def view155 : View := normalized_cursor_cut% (Observe cut155.2)
private theorem view_eq155 : Observe cut155.2 = view155 := by checked_cut_rfl
private theorem read_one155 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut155 = value (Observe cut155.2) := by
  change value (Observe cut155.2) * 1 = value (Observe cut155.2)
  exact mul_one _
private theorem one155 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut155 = value view155 :=
  (read_one155 value).trans (congrArg value view_eq155)
private noncomputable def view156 : View := normalized_cursor_cut% (Observe cut156.2)
private theorem view_eq156 : Observe cut156.2 = view156 := by checked_cut_rfl
private theorem read_one156 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut156 = value (Observe cut156.2) := by
  change value (Observe cut156.2) * 1 = value (Observe cut156.2)
  exact mul_one _
private theorem one156 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut156 = value view156 :=
  (read_one156 value).trans (congrArg value view_eq156)
private noncomputable def view157 : View := normalized_cursor_cut% (Observe cut157.2)
private theorem view_eq157 : Observe cut157.2 = view157 := by checked_cut_rfl
private theorem read_one157 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut157 = value (Observe cut157.2) := by
  change value (Observe cut157.2) * 1 = value (Observe cut157.2)
  exact mul_one _
private theorem one157 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut157 = value view157 :=
  (read_one157 value).trans (congrArg value view_eq157)
private noncomputable def view158 : View := normalized_cursor_cut% (Observe cut158.2)
private theorem view_eq158 : Observe cut158.2 = view158 := by checked_cut_rfl
private theorem read_one158 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut158 = value (Observe cut158.2) := by
  change value (Observe cut158.2) * 1 = value (Observe cut158.2)
  exact mul_one _
private theorem one158 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut158 = value view158 :=
  (read_one158 value).trans (congrArg value view_eq158)
private noncomputable def view159 : View := normalized_cursor_cut% (Observe cut159.2)
private theorem view_eq159 : Observe cut159.2 = view159 := by checked_cut_rfl
private theorem read_one159 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut159 = value (Observe cut159.2) := by
  change value (Observe cut159.2) * 1 = value (Observe cut159.2)
  exact mul_one _
private theorem one159 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut159 = value view159 :=
  (read_one159 value).trans (congrArg value view_eq159)
private noncomputable def view160 : View := normalized_cursor_cut% (Observe cut160.2)
private theorem view_eq160 : Observe cut160.2 = view160 := by checked_cut_rfl
private theorem read_one160 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut160 = value (Observe cut160.2) := by
  change value (Observe cut160.2) * 1 = value (Observe cut160.2)
  exact mul_one _
private theorem one160 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut160 = value view160 :=
  (read_one160 value).trans (congrArg value view_eq160)

private noncomputable def tail161 : List View := []
private noncomputable def tail160 : List View := view160 :: tail161
private noncomputable def tail159 : List View := view159 :: tail160
private noncomputable def tail158 : List View := view158 :: tail159
private noncomputable def tail157 : List View := view157 :: tail158
private noncomputable def tail156 : List View := view156 :: tail157
private noncomputable def tail155 : List View := view155 :: tail156
private noncomputable def tail154 : List View := view154 :: tail155
private noncomputable def tail153 : List View := view153 :: tail154
private noncomputable def tail152 : List View := view152 :: tail153
private noncomputable def tail151 : List View := view151 :: tail152
private noncomputable def tail150 : List View := view150 :: tail151
private noncomputable def tail149 : List View := view149 :: tail150
private noncomputable def tail148 : List View := view148 :: tail149
private noncomputable def tail147 : List View := view147 :: tail148
private noncomputable def tail146 : List View := view146 :: tail147
private noncomputable def tail145 : List View := view145 :: tail146
private noncomputable def tail144 : List View := view144 :: tail145
private noncomputable def tail143 : List View := view143 :: tail144
private noncomputable def tail142 : List View := view142 :: tail143
private noncomputable def tail141 : List View := view141 :: tail142
private noncomputable def tail140 : List View := view140 :: tail141
private noncomputable def tail139 : List View := view139 :: tail140
private noncomputable def tail138 : List View := view138 :: tail139
private noncomputable def tail137 : List View := view137 :: tail138
private noncomputable def tail136 : List View := view136 :: tail137
private noncomputable def tail135 : List View := view135 :: tail136
private noncomputable def tail134 : List View := view134 :: tail135
private noncomputable def tail133 : List View := view133 :: tail134
private noncomputable def tail132 : List View := view132 :: tail133
private noncomputable def tail131 : List View := view131 :: tail132
private noncomputable def tail130 : List View := view130 :: tail131
private noncomputable def tail129 : List View := view129 :: tail130
private noncomputable def tail128 : List View := view128 :: tail129
private noncomputable def tail127 : List View := view127 :: tail128
private noncomputable def tail126 : List View := view126 :: tail127
private noncomputable def tail125 : List View := view125 :: tail126
private noncomputable def tail124 : List View := view124 :: tail125
private noncomputable def tail123 : List View := view123 :: tail124
private noncomputable def tail122 : List View := view122 :: tail123
private noncomputable def tail121 : List View := view121 :: tail122
private noncomputable def tail120 : List View := view120 :: tail121
private noncomputable def tail119 : List View := view119 :: tail120
private noncomputable def tail118 : List View := view118 :: tail119
private noncomputable def tail117 : List View := view117 :: tail118
private noncomputable def tail116 : List View := view116 :: tail117
private noncomputable def tail115 : List View := view115 :: tail116
private noncomputable def tail114 : List View := view114 :: tail115
private noncomputable def tail113 : List View := view113 :: tail114
private noncomputable def tail112 : List View := view112 :: tail113
private noncomputable def tail111 : List View := view111 :: tail112
private noncomputable def tail110 : List View := view110 :: tail111
private noncomputable def tail109 : List View := view109 :: tail110
private noncomputable def tail108 : List View := view108 :: tail109
private noncomputable def tail107 : List View := view107 :: tail108
private noncomputable def tail106 : List View := view106 :: tail107
private noncomputable def tail105 : List View := view105 :: tail106
private noncomputable def tail104 : List View := view104 :: tail105
private noncomputable def tail103 : List View := view103 :: tail104
private noncomputable def tail102 : List View := view102 :: tail103
private noncomputable def tail101 : List View := view101 :: tail102
private noncomputable def tail100 : List View := view100 :: tail101
private noncomputable def tail99 : List View := view99 :: tail100
private noncomputable def tail98 : List View := view98 :: tail99
private noncomputable def tail97 : List View := view97 :: tail98
private noncomputable def tail96 : List View := view96 :: tail97
private noncomputable def tail95 : List View := view95 :: tail96
private noncomputable def tail94 : List View := view94 :: tail95
private noncomputable def tail93 : List View := view93 :: tail94
private noncomputable def tail92 : List View := view92 :: tail93
private noncomputable def tail91 : List View := view91 :: tail92
private noncomputable def tail90 : List View := view90 :: tail91
private noncomputable def tail89 : List View := view89 :: tail90
private noncomputable def tail88 : List View := view88 :: tail89
private noncomputable def tail87 : List View := view87 :: tail88
private noncomputable def tail86 : List View := view86 :: tail87
private noncomputable def tail85 : List View := view85 :: tail86
private noncomputable def tail84 : List View := view84 :: tail85
private noncomputable def tail83 : List View := view83 :: tail84
private noncomputable def tail82 : List View := view82 :: tail83
private noncomputable def tail81 : List View := view81 :: tail82
private noncomputable def tail80 : List View := view80 :: tail81
private noncomputable def tail79 : List View := view79 :: tail80
private noncomputable def tail78 : List View := view78 :: tail79
private noncomputable def tail77 : List View := view77 :: tail78
private noncomputable def tail76 : List View := view76 :: tail77
private noncomputable def tail75 : List View := view75 :: tail76
private noncomputable def tail74 : List View := view74 :: tail75
private noncomputable def tail73 : List View := view73 :: tail74
private noncomputable def tail72 : List View := view72 :: tail73
private noncomputable def tail71 : List View := view71 :: tail72
private noncomputable def tail70 : List View := view70 :: tail71
private noncomputable def tail69 : List View := view69 :: tail70
private noncomputable def tail68 : List View := view68 :: tail69
private noncomputable def tail67 : List View := view67 :: tail68
private noncomputable def tail66 : List View := view66 :: tail67
private noncomputable def tail65 : List View := view65 :: tail66
private noncomputable def tail64 : List View := view64 :: tail65
private noncomputable def tail63 : List View := view63 :: tail64
private noncomputable def tail62 : List View := view62 :: tail63
private noncomputable def tail61 : List View := view61 :: tail62
private noncomputable def tail60 : List View := view60 :: tail61
private noncomputable def tail59 : List View := view59 :: tail60
private noncomputable def tail58 : List View := view58 :: tail59
private noncomputable def tail57 : List View := view57 :: tail58
private noncomputable def tail56 : List View := view56 :: tail57
private noncomputable def tail55 : List View := view55 :: tail56
private noncomputable def tail54 : List View := view54 :: tail55
private noncomputable def tail53 : List View := view53 :: tail54
private noncomputable def tail52 : List View := view52 :: tail53
private noncomputable def tail51 : List View := view51 :: tail52
private noncomputable def tail50 : List View := view50 :: tail51
private noncomputable def tail49 : List View := view49 :: tail50
private noncomputable def tail48 : List View := view48 :: tail49
private noncomputable def tail47 : List View := view47 :: tail48
private noncomputable def tail46 : List View := view46 :: tail47
private noncomputable def tail45 : List View := view45 :: tail46
private noncomputable def tail44 : List View := view44 :: tail45
private noncomputable def tail43 : List View := view43 :: tail44
private noncomputable def tail42 : List View := view42 :: tail43
private noncomputable def tail41 : List View := view41 :: tail42
private noncomputable def tail40 : List View := view40 :: tail41
private noncomputable def tail39 : List View := view39 :: tail40
private noncomputable def tail38 : List View := view38 :: tail39
private noncomputable def tail37 : List View := view37 :: tail38
private noncomputable def tail36 : List View := view36 :: tail37
private noncomputable def tail35 : List View := view35 :: tail36
private noncomputable def tail34 : List View := view34 :: tail35
private noncomputable def tail33 : List View := view33 :: tail34
private noncomputable def tail32 : List View := view32 :: tail33
private noncomputable def tail31 : List View := view31 :: tail32
private noncomputable def tail30 : List View := view30 :: tail31
private noncomputable def tail29 : List View := view29 :: tail30
private noncomputable def tail28 : List View := view28 :: tail29
private noncomputable def tail27 : List View := view27 :: tail28
private noncomputable def tail26 : List View := view26 :: tail27
private noncomputable def tail25 : List View := view25 :: tail26
private noncomputable def tail24 : List View := view24 :: tail25
private noncomputable def tail23 : List View := view23 :: tail24
private noncomputable def tail22 : List View := view22 :: tail23
private noncomputable def tail21 : List View := view21 :: tail22
private noncomputable def tail20 : List View := view20 :: tail21
private noncomputable def tail19 : List View := view19 :: tail20
private noncomputable def tail18 : List View := view18 :: tail19
private noncomputable def tail17 : List View := view17 :: tail18
private noncomputable def tail16 : List View := view16 :: tail17
private noncomputable def tail15 : List View := view15 :: tail16
private noncomputable def tail14 : List View := view14 :: tail15
private noncomputable def tail13 : List View := view13 :: tail14
private noncomputable def tail12 : List View := view12 :: tail13
private noncomputable def tail11 : List View := view11 :: tail12
private noncomputable def tail10 : List View := view10 :: tail11
private noncomputable def tail9 : List View := view9 :: tail10
private noncomputable def tail8 : List View := view8 :: tail9
private noncomputable def tail7 : List View := view7 :: tail8
private noncomputable def tail6 : List View := view6 :: tail7
private noncomputable def tail5 : List View := view5 :: tail6
private noncomputable def tail4 : List View := view4 :: tail5
private noncomputable def tail3 : List View := view3 :: tail4
private noncomputable def tail2 : List View := view2 :: tail3
private noncomputable def tail1 : List View := view1 :: tail2
private noncomputable def tail0 : List View := view0 :: tail1

private theorem tail_read161 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 239 cut161 = (tail161.map value).prod := by checked_cut_rfl
private theorem tail_read160 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 240 cut160 = (tail160.map value).prod :=
  fold_step value step161 (one160 value) (tail_read161 value) rfl
private theorem tail_read159 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 241 cut159 = (tail159.map value).prod :=
  fold_step value step160 (one159 value) (tail_read160 value) rfl
private theorem tail_read158 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 242 cut158 = (tail158.map value).prod :=
  fold_step value step159 (one158 value) (tail_read159 value) rfl
private theorem tail_read157 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 243 cut157 = (tail157.map value).prod :=
  fold_step value step158 (one157 value) (tail_read158 value) rfl
private theorem tail_read156 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 244 cut156 = (tail156.map value).prod :=
  fold_step value step157 (one156 value) (tail_read157 value) rfl
private theorem tail_read155 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 245 cut155 = (tail155.map value).prod :=
  fold_step value step156 (one155 value) (tail_read156 value) rfl
private theorem tail_read154 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 246 cut154 = (tail154.map value).prod :=
  fold_step value step155 (one154 value) (tail_read155 value) rfl
private theorem tail_read153 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 247 cut153 = (tail153.map value).prod :=
  fold_step value step154 (one153 value) (tail_read154 value) rfl
private theorem tail_read152 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 248 cut152 = (tail152.map value).prod :=
  fold_step value step153 (one152 value) (tail_read153 value) rfl
private theorem tail_read151 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 249 cut151 = (tail151.map value).prod :=
  fold_step value step152 (one151 value) (tail_read152 value) rfl
private theorem tail_read150 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 250 cut150 = (tail150.map value).prod :=
  fold_step value step151 (one150 value) (tail_read151 value) rfl
private theorem tail_read149 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 251 cut149 = (tail149.map value).prod :=
  fold_step value step150 (one149 value) (tail_read150 value) rfl
private theorem tail_read148 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 252 cut148 = (tail148.map value).prod :=
  fold_step value step149 (one148 value) (tail_read149 value) rfl
private theorem tail_read147 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 253 cut147 = (tail147.map value).prod :=
  fold_step value step148 (one147 value) (tail_read148 value) rfl
private theorem tail_read146 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 254 cut146 = (tail146.map value).prod :=
  fold_step value step147 (one146 value) (tail_read147 value) rfl
private theorem tail_read145 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 255 cut145 = (tail145.map value).prod :=
  fold_step value step146 (one145 value) (tail_read146 value) rfl
private theorem tail_read144 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 256 cut144 = (tail144.map value).prod :=
  fold_step value step145 (one144 value) (tail_read145 value) rfl
private theorem tail_read143 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 257 cut143 = (tail143.map value).prod :=
  fold_step value step144 (one143 value) (tail_read144 value) rfl
private theorem tail_read142 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 258 cut142 = (tail142.map value).prod :=
  fold_step value step143 (one142 value) (tail_read143 value) rfl
private theorem tail_read141 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 259 cut141 = (tail141.map value).prod :=
  fold_step value step142 (one141 value) (tail_read142 value) rfl
private theorem tail_read140 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 260 cut140 = (tail140.map value).prod :=
  fold_step value step141 (one140 value) (tail_read141 value) rfl
private theorem tail_read139 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 261 cut139 = (tail139.map value).prod :=
  fold_step value step140 (one139 value) (tail_read140 value) rfl
private theorem tail_read138 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 262 cut138 = (tail138.map value).prod :=
  fold_step value step139 (one138 value) (tail_read139 value) rfl
private theorem tail_read137 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 263 cut137 = (tail137.map value).prod :=
  fold_step value step138 (one137 value) (tail_read138 value) rfl
private theorem tail_read136 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 264 cut136 = (tail136.map value).prod :=
  fold_step value step137 (one136 value) (tail_read137 value) rfl
private theorem tail_read135 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 265 cut135 = (tail135.map value).prod :=
  fold_step value step136 (one135 value) (tail_read136 value) rfl
private theorem tail_read134 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 266 cut134 = (tail134.map value).prod :=
  fold_step value step135 (one134 value) (tail_read135 value) rfl
private theorem tail_read133 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 267 cut133 = (tail133.map value).prod :=
  fold_step value step134 (one133 value) (tail_read134 value) rfl
private theorem tail_read132 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 268 cut132 = (tail132.map value).prod :=
  fold_step value step133 (one132 value) (tail_read133 value) rfl
private theorem tail_read131 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 269 cut131 = (tail131.map value).prod :=
  fold_step value step132 (one131 value) (tail_read132 value) rfl
private theorem tail_read130 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 270 cut130 = (tail130.map value).prod :=
  fold_step value step131 (one130 value) (tail_read131 value) rfl
private theorem tail_read129 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 271 cut129 = (tail129.map value).prod :=
  fold_step value step130 (one129 value) (tail_read130 value) rfl
private theorem tail_read128 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 272 cut128 = (tail128.map value).prod :=
  fold_step value step129 (one128 value) (tail_read129 value) rfl
private theorem tail_read127 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 273 cut127 = (tail127.map value).prod :=
  fold_step value step128 (one127 value) (tail_read128 value) rfl
private theorem tail_read126 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 274 cut126 = (tail126.map value).prod :=
  fold_step value step127 (one126 value) (tail_read127 value) rfl
private theorem tail_read125 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 275 cut125 = (tail125.map value).prod :=
  fold_step value step126 (one125 value) (tail_read126 value) rfl
private theorem tail_read124 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 276 cut124 = (tail124.map value).prod :=
  fold_step value step125 (one124 value) (tail_read125 value) rfl
private theorem tail_read123 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 277 cut123 = (tail123.map value).prod :=
  fold_step value step124 (one123 value) (tail_read124 value) rfl
private theorem tail_read122 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 278 cut122 = (tail122.map value).prod :=
  fold_step value step123 (one122 value) (tail_read123 value) rfl
private theorem tail_read121 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 279 cut121 = (tail121.map value).prod :=
  fold_step value step122 (one121 value) (tail_read122 value) rfl
private theorem tail_read120 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 280 cut120 = (tail120.map value).prod :=
  fold_step value step121 (one120 value) (tail_read121 value) rfl
private theorem tail_read119 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 281 cut119 = (tail119.map value).prod :=
  fold_step value step120 (one119 value) (tail_read120 value) rfl
private theorem tail_read118 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 282 cut118 = (tail118.map value).prod :=
  fold_step value step119 (one118 value) (tail_read119 value) rfl
private theorem tail_read117 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 283 cut117 = (tail117.map value).prod :=
  fold_step value step118 (one117 value) (tail_read118 value) rfl
private theorem tail_read116 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 284 cut116 = (tail116.map value).prod :=
  fold_step value step117 (one116 value) (tail_read117 value) rfl
private theorem tail_read115 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 285 cut115 = (tail115.map value).prod :=
  fold_step value step116 (one115 value) (tail_read116 value) rfl
private theorem tail_read114 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 286 cut114 = (tail114.map value).prod :=
  fold_step value step115 (one114 value) (tail_read115 value) rfl
private theorem tail_read113 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 287 cut113 = (tail113.map value).prod :=
  fold_step value step114 (one113 value) (tail_read114 value) rfl
private theorem tail_read112 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 288 cut112 = (tail112.map value).prod :=
  fold_step value step113 (one112 value) (tail_read113 value) rfl
private theorem tail_read111 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 289 cut111 = (tail111.map value).prod :=
  fold_step value step112 (one111 value) (tail_read112 value) rfl
private theorem tail_read110 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 290 cut110 = (tail110.map value).prod :=
  fold_step value step111 (one110 value) (tail_read111 value) rfl
private theorem tail_read109 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 291 cut109 = (tail109.map value).prod :=
  fold_step value step110 (one109 value) (tail_read110 value) rfl
private theorem tail_read108 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 292 cut108 = (tail108.map value).prod :=
  fold_step value step109 (one108 value) (tail_read109 value) rfl
private theorem tail_read107 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 293 cut107 = (tail107.map value).prod :=
  fold_step value step108 (one107 value) (tail_read108 value) rfl
private theorem tail_read106 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 294 cut106 = (tail106.map value).prod :=
  fold_step value step107 (one106 value) (tail_read107 value) rfl
private theorem tail_read105 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 295 cut105 = (tail105.map value).prod :=
  fold_step value step106 (one105 value) (tail_read106 value) rfl
private theorem tail_read104 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 296 cut104 = (tail104.map value).prod :=
  fold_step value step105 (one104 value) (tail_read105 value) rfl
private theorem tail_read103 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 297 cut103 = (tail103.map value).prod :=
  fold_step value step104 (one103 value) (tail_read104 value) rfl
private theorem tail_read102 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 298 cut102 = (tail102.map value).prod :=
  fold_step value step103 (one102 value) (tail_read103 value) rfl
private theorem tail_read101 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 299 cut101 = (tail101.map value).prod :=
  fold_step value step102 (one101 value) (tail_read102 value) rfl
private theorem tail_read100 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 300 cut100 = (tail100.map value).prod :=
  fold_step value step101 (one100 value) (tail_read101 value) rfl
private theorem tail_read99 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 301 cut99 = (tail99.map value).prod :=
  fold_step value step100 (one99 value) (tail_read100 value) rfl
private theorem tail_read98 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 302 cut98 = (tail98.map value).prod :=
  fold_step value step99 (one98 value) (tail_read99 value) rfl
private theorem tail_read97 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 303 cut97 = (tail97.map value).prod :=
  fold_step value step98 (one97 value) (tail_read98 value) rfl
private theorem tail_read96 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 304 cut96 = (tail96.map value).prod :=
  fold_step value step97 (one96 value) (tail_read97 value) rfl
private theorem tail_read95 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 305 cut95 = (tail95.map value).prod :=
  fold_step value step96 (one95 value) (tail_read96 value) rfl
private theorem tail_read94 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 306 cut94 = (tail94.map value).prod :=
  fold_step value step95 (one94 value) (tail_read95 value) rfl
private theorem tail_read93 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 307 cut93 = (tail93.map value).prod :=
  fold_step value step94 (one93 value) (tail_read94 value) rfl
private theorem tail_read92 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 308 cut92 = (tail92.map value).prod :=
  fold_step value step93 (one92 value) (tail_read93 value) rfl
private theorem tail_read91 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 309 cut91 = (tail91.map value).prod :=
  fold_step value step92 (one91 value) (tail_read92 value) rfl
private theorem tail_read90 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 310 cut90 = (tail90.map value).prod :=
  fold_step value step91 (one90 value) (tail_read91 value) rfl
private theorem tail_read89 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 311 cut89 = (tail89.map value).prod :=
  fold_step value step90 (one89 value) (tail_read90 value) rfl
private theorem tail_read88 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 312 cut88 = (tail88.map value).prod :=
  fold_step value step89 (one88 value) (tail_read89 value) rfl
private theorem tail_read87 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 313 cut87 = (tail87.map value).prod :=
  fold_step value step88 (one87 value) (tail_read88 value) rfl
private theorem tail_read86 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 314 cut86 = (tail86.map value).prod :=
  fold_step value step87 (one86 value) (tail_read87 value) rfl
private theorem tail_read85 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 315 cut85 = (tail85.map value).prod :=
  fold_step value step86 (one85 value) (tail_read86 value) rfl
private theorem tail_read84 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 316 cut84 = (tail84.map value).prod :=
  fold_step value step85 (one84 value) (tail_read85 value) rfl
private theorem tail_read83 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 317 cut83 = (tail83.map value).prod :=
  fold_step value step84 (one83 value) (tail_read84 value) rfl
private theorem tail_read82 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 318 cut82 = (tail82.map value).prod :=
  fold_step value step83 (one82 value) (tail_read83 value) rfl
private theorem tail_read81 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 319 cut81 = (tail81.map value).prod :=
  fold_step value step82 (one81 value) (tail_read82 value) rfl
private theorem tail_read80 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 320 cut80 = (tail80.map value).prod :=
  fold_step value step81 (one80 value) (tail_read81 value) rfl
private theorem tail_read79 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 321 cut79 = (tail79.map value).prod :=
  fold_step value step80 (one79 value) (tail_read80 value) rfl
private theorem tail_read78 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 322 cut78 = (tail78.map value).prod :=
  fold_step value step79 (one78 value) (tail_read79 value) rfl
private theorem tail_read77 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 323 cut77 = (tail77.map value).prod :=
  fold_step value step78 (one77 value) (tail_read78 value) rfl
private theorem tail_read76 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 324 cut76 = (tail76.map value).prod :=
  fold_step value step77 (one76 value) (tail_read77 value) rfl
private theorem tail_read75 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 325 cut75 = (tail75.map value).prod :=
  fold_step value step76 (one75 value) (tail_read76 value) rfl
private theorem tail_read74 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 326 cut74 = (tail74.map value).prod :=
  fold_step value step75 (one74 value) (tail_read75 value) rfl
private theorem tail_read73 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 327 cut73 = (tail73.map value).prod :=
  fold_step value step74 (one73 value) (tail_read74 value) rfl
private theorem tail_read72 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 328 cut72 = (tail72.map value).prod :=
  fold_step value step73 (one72 value) (tail_read73 value) rfl
private theorem tail_read71 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 329 cut71 = (tail71.map value).prod :=
  fold_step value step72 (one71 value) (tail_read72 value) rfl
private theorem tail_read70 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 330 cut70 = (tail70.map value).prod :=
  fold_step value step71 (one70 value) (tail_read71 value) rfl
private theorem tail_read69 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 331 cut69 = (tail69.map value).prod :=
  fold_step value step70 (one69 value) (tail_read70 value) rfl
private theorem tail_read68 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 332 cut68 = (tail68.map value).prod :=
  fold_step value step69 (one68 value) (tail_read69 value) rfl
private theorem tail_read67 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 333 cut67 = (tail67.map value).prod :=
  fold_step value step68 (one67 value) (tail_read68 value) rfl
private theorem tail_read66 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 334 cut66 = (tail66.map value).prod :=
  fold_step value step67 (one66 value) (tail_read67 value) rfl
private theorem tail_read65 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 335 cut65 = (tail65.map value).prod :=
  fold_step value step66 (one65 value) (tail_read66 value) rfl
private theorem tail_read64 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 336 cut64 = (tail64.map value).prod :=
  fold_step value step65 (one64 value) (tail_read65 value) rfl
private theorem tail_read63 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 337 cut63 = (tail63.map value).prod :=
  fold_step value step64 (one63 value) (tail_read64 value) rfl
private theorem tail_read62 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 338 cut62 = (tail62.map value).prod :=
  fold_step value step63 (one62 value) (tail_read63 value) rfl
private theorem tail_read61 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 339 cut61 = (tail61.map value).prod :=
  fold_step value step62 (one61 value) (tail_read62 value) rfl
private theorem tail_read60 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 340 cut60 = (tail60.map value).prod :=
  fold_step value step61 (one60 value) (tail_read61 value) rfl
private theorem tail_read59 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 341 cut59 = (tail59.map value).prod :=
  fold_step value step60 (one59 value) (tail_read60 value) rfl
private theorem tail_read58 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 342 cut58 = (tail58.map value).prod :=
  fold_step value step59 (one58 value) (tail_read59 value) rfl
private theorem tail_read57 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 343 cut57 = (tail57.map value).prod :=
  fold_step value step58 (one57 value) (tail_read58 value) rfl
private theorem tail_read56 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 344 cut56 = (tail56.map value).prod :=
  fold_step value step57 (one56 value) (tail_read57 value) rfl
private theorem tail_read55 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 345 cut55 = (tail55.map value).prod :=
  fold_step value step56 (one55 value) (tail_read56 value) rfl
private theorem tail_read54 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 346 cut54 = (tail54.map value).prod :=
  fold_step value step55 (one54 value) (tail_read55 value) rfl
private theorem tail_read53 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 347 cut53 = (tail53.map value).prod :=
  fold_step value step54 (one53 value) (tail_read54 value) rfl
private theorem tail_read52 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 348 cut52 = (tail52.map value).prod :=
  fold_step value step53 (one52 value) (tail_read53 value) rfl
private theorem tail_read51 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 349 cut51 = (tail51.map value).prod :=
  fold_step value step52 (one51 value) (tail_read52 value) rfl
private theorem tail_read50 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 350 cut50 = (tail50.map value).prod :=
  fold_step value step51 (one50 value) (tail_read51 value) rfl
private theorem tail_read49 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 351 cut49 = (tail49.map value).prod :=
  fold_step value step50 (one49 value) (tail_read50 value) rfl
private theorem tail_read48 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 352 cut48 = (tail48.map value).prod :=
  fold_step value step49 (one48 value) (tail_read49 value) rfl
private theorem tail_read47 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 353 cut47 = (tail47.map value).prod :=
  fold_step value step48 (one47 value) (tail_read48 value) rfl
private theorem tail_read46 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 354 cut46 = (tail46.map value).prod :=
  fold_step value step47 (one46 value) (tail_read47 value) rfl
private theorem tail_read45 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 355 cut45 = (tail45.map value).prod :=
  fold_step value step46 (one45 value) (tail_read46 value) rfl
private theorem tail_read44 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 356 cut44 = (tail44.map value).prod :=
  fold_step value step45 (one44 value) (tail_read45 value) rfl
private theorem tail_read43 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 357 cut43 = (tail43.map value).prod :=
  fold_step value step44 (one43 value) (tail_read44 value) rfl
private theorem tail_read42 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 358 cut42 = (tail42.map value).prod :=
  fold_step value step43 (one42 value) (tail_read43 value) rfl
private theorem tail_read41 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 359 cut41 = (tail41.map value).prod :=
  fold_step value step42 (one41 value) (tail_read42 value) rfl
private theorem tail_read40 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 360 cut40 = (tail40.map value).prod :=
  fold_step value step41 (one40 value) (tail_read41 value) rfl
private theorem tail_read39 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 361 cut39 = (tail39.map value).prod :=
  fold_step value step40 (one39 value) (tail_read40 value) rfl
private theorem tail_read38 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 362 cut38 = (tail38.map value).prod :=
  fold_step value step39 (one38 value) (tail_read39 value) rfl
private theorem tail_read37 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 363 cut37 = (tail37.map value).prod :=
  fold_step value step38 (one37 value) (tail_read38 value) rfl
private theorem tail_read36 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 364 cut36 = (tail36.map value).prod :=
  fold_step value step37 (one36 value) (tail_read37 value) rfl
private theorem tail_read35 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 365 cut35 = (tail35.map value).prod :=
  fold_step value step36 (one35 value) (tail_read36 value) rfl
private theorem tail_read34 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 366 cut34 = (tail34.map value).prod :=
  fold_step value step35 (one34 value) (tail_read35 value) rfl
private theorem tail_read33 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 367 cut33 = (tail33.map value).prod :=
  fold_step value step34 (one33 value) (tail_read34 value) rfl
private theorem tail_read32 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 368 cut32 = (tail32.map value).prod :=
  fold_step value step33 (one32 value) (tail_read33 value) rfl
private theorem tail_read31 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 369 cut31 = (tail31.map value).prod :=
  fold_step value step32 (one31 value) (tail_read32 value) rfl
private theorem tail_read30 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 370 cut30 = (tail30.map value).prod :=
  fold_step value step31 (one30 value) (tail_read31 value) rfl
private theorem tail_read29 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 371 cut29 = (tail29.map value).prod :=
  fold_step value step30 (one29 value) (tail_read30 value) rfl
private theorem tail_read28 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 372 cut28 = (tail28.map value).prod :=
  fold_step value step29 (one28 value) (tail_read29 value) rfl
private theorem tail_read27 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 373 cut27 = (tail27.map value).prod :=
  fold_step value step28 (one27 value) (tail_read28 value) rfl
private theorem tail_read26 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 374 cut26 = (tail26.map value).prod :=
  fold_step value step27 (one26 value) (tail_read27 value) rfl
private theorem tail_read25 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 375 cut25 = (tail25.map value).prod :=
  fold_step value step26 (one25 value) (tail_read26 value) rfl
private theorem tail_read24 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 376 cut24 = (tail24.map value).prod :=
  fold_step value step25 (one24 value) (tail_read25 value) rfl
private theorem tail_read23 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 377 cut23 = (tail23.map value).prod :=
  fold_step value step24 (one23 value) (tail_read24 value) rfl
private theorem tail_read22 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 378 cut22 = (tail22.map value).prod :=
  fold_step value step23 (one22 value) (tail_read23 value) rfl
private theorem tail_read21 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 379 cut21 = (tail21.map value).prod :=
  fold_step value step22 (one21 value) (tail_read22 value) rfl
private theorem tail_read20 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 380 cut20 = (tail20.map value).prod :=
  fold_step value step21 (one20 value) (tail_read21 value) rfl
private theorem tail_read19 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 381 cut19 = (tail19.map value).prod :=
  fold_step value step20 (one19 value) (tail_read20 value) rfl
private theorem tail_read18 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 382 cut18 = (tail18.map value).prod :=
  fold_step value step19 (one18 value) (tail_read19 value) rfl
private theorem tail_read17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 383 cut17 = (tail17.map value).prod :=
  fold_step value step18 (one17 value) (tail_read18 value) rfl
private theorem tail_read16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 384 cut16 = (tail16.map value).prod :=
  fold_step value step17 (one16 value) (tail_read17 value) rfl
private theorem tail_read15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 385 cut15 = (tail15.map value).prod :=
  fold_step value step16 (one15 value) (tail_read16 value) rfl
private theorem tail_read14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 386 cut14 = (tail14.map value).prod :=
  fold_step value step15 (one14 value) (tail_read15 value) rfl
private theorem tail_read13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 387 cut13 = (tail13.map value).prod :=
  fold_step value step14 (one13 value) (tail_read14 value) rfl
private theorem tail_read12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 388 cut12 = (tail12.map value).prod :=
  fold_step value step13 (one12 value) (tail_read13 value) rfl
private theorem tail_read11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 389 cut11 = (tail11.map value).prod :=
  fold_step value step12 (one11 value) (tail_read12 value) rfl
private theorem tail_read10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 390 cut10 = (tail10.map value).prod :=
  fold_step value step11 (one10 value) (tail_read11 value) rfl
private theorem tail_read9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 391 cut9 = (tail9.map value).prod :=
  fold_step value step10 (one9 value) (tail_read10 value) rfl
private theorem tail_read8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 392 cut8 = (tail8.map value).prod :=
  fold_step value step9 (one8 value) (tail_read9 value) rfl
private theorem tail_read7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 393 cut7 = (tail7.map value).prod :=
  fold_step value step8 (one7 value) (tail_read8 value) rfl
private theorem tail_read6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 394 cut6 = (tail6.map value).prod :=
  fold_step value step7 (one6 value) (tail_read7 value) rfl
private theorem tail_read5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 395 cut5 = (tail5.map value).prod :=
  fold_step value step6 (one5 value) (tail_read6 value) rfl
private theorem tail_read4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 396 cut4 = (tail4.map value).prod :=
  fold_step value step5 (one4 value) (tail_read5 value) rfl
private theorem tail_read3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 397 cut3 = (tail3.map value).prod :=
  fold_step value step4 (one3 value) (tail_read4 value) rfl
private theorem tail_read2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 398 cut2 = (tail2.map value).prod :=
  fold_step value step3 (one2 value) (tail_read3 value) rfl
private theorem tail_read1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 399 cut1 = (tail1.map value).prod :=
  fold_step value step2 (one1 value) (tail_read2 value) rfl
private theorem tail_read0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 400 cut0 = (tail0.map value).prod :=
  fold_step value step1 (one0 value) (tail_read1 value) rfl

private noncomputable def prefix17 : List View := []
private noncomputable def prefix16 : List View := view16 :: prefix17
private noncomputable def prefix15 : List View := view15 :: prefix16
private noncomputable def prefix14 : List View := view14 :: prefix15
private noncomputable def prefix13 : List View := view13 :: prefix14
private noncomputable def prefix12 : List View := view12 :: prefix13
private noncomputable def prefix11 : List View := view11 :: prefix12
private noncomputable def prefix10 : List View := view10 :: prefix11
private noncomputable def prefix9 : List View := view9 :: prefix10
private noncomputable def prefix8 : List View := view8 :: prefix9
private noncomputable def prefix7 : List View := view7 :: prefix8
private noncomputable def prefix6 : List View := view6 :: prefix7
private noncomputable def prefix5 : List View := view5 :: prefix6
private noncomputable def prefix4 : List View := view4 :: prefix5
private noncomputable def prefix3 : List View := view3 :: prefix4
private noncomputable def prefix2 : List View := view2 :: prefix3
private noncomputable def prefix1 : List View := view1 :: prefix2
private noncomputable def prefix0 : List View := view0 :: prefix1

private theorem prefix_read17 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 0 cut17 = (prefix17.map value).prod := by rfl
private theorem prefix_read16 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 1 cut16 = (prefix16.map value).prod :=
  fold_step value step17 (one16 value) (prefix_read17 value) rfl
private theorem prefix_read15 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 2 cut15 = (prefix15.map value).prod :=
  fold_step value step16 (one15 value) (prefix_read16 value) rfl
private theorem prefix_read14 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 3 cut14 = (prefix14.map value).prod :=
  fold_step value step15 (one14 value) (prefix_read15 value) rfl
private theorem prefix_read13 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 4 cut13 = (prefix13.map value).prod :=
  fold_step value step14 (one13 value) (prefix_read14 value) rfl
private theorem prefix_read12 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 5 cut12 = (prefix12.map value).prod :=
  fold_step value step13 (one12 value) (prefix_read13 value) rfl
private theorem prefix_read11 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 6 cut11 = (prefix11.map value).prod :=
  fold_step value step12 (one11 value) (prefix_read12 value) rfl
private theorem prefix_read10 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 7 cut10 = (prefix10.map value).prod :=
  fold_step value step11 (one10 value) (prefix_read11 value) rfl
private theorem prefix_read9 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 8 cut9 = (prefix9.map value).prod :=
  fold_step value step10 (one9 value) (prefix_read10 value) rfl
private theorem prefix_read8 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 9 cut8 = (prefix8.map value).prod :=
  fold_step value step9 (one8 value) (prefix_read9 value) rfl
private theorem prefix_read7 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 10 cut7 = (prefix7.map value).prod :=
  fold_step value step8 (one7 value) (prefix_read8 value) rfl
private theorem prefix_read6 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 11 cut6 = (prefix6.map value).prod :=
  fold_step value step7 (one6 value) (prefix_read7 value) rfl
private theorem prefix_read5 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 12 cut5 = (prefix5.map value).prod :=
  fold_step value step6 (one5 value) (prefix_read6 value) rfl
private theorem prefix_read4 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 13 cut4 = (prefix4.map value).prod :=
  fold_step value step5 (one4 value) (prefix_read5 value) rfl
private theorem prefix_read3 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 14 cut3 = (prefix3.map value).prod :=
  fold_step value step4 (one3 value) (prefix_read4 value) rfl
private theorem prefix_read2 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 15 cut2 = (prefix2.map value).prod :=
  fold_step value step3 (one2 value) (prefix_read3 value) rfl
private theorem prefix_read1 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 16 cut1 = (prefix1.map value).prod :=
  fold_step value step2 (one1 value) (prefix_read2 value) rfl
private theorem prefix_read0 {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 17 cut0 = (prefix0.map value).prod :=
  fold_step value step1 (one0 value) (prefix_read1 value) rfl

private theorem initial_saved : (0, Cursor.Outcome.paused packet) = cut0 := by checked_cut_rfl

private theorem read_whole {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 400 (0, .paused packet) = (tail0.map value).prod :=
  (congrArg (Read value 400) initial_saved).trans (tail_read0 value)

private theorem read_prefix {Result : Type} [Monoid Result] (value : View → Result) :
    Read value 17 (0, .paused packet) = (prefix0.map value).prod :=
  (congrArg (Read value 17) initial_saved).trans (prefix_read0 value)

private theorem word_literal : word 400 = tail0 := by
  have moved := congrArg FreeMonoid.toList (read_whole FreeMonoid.of)
  have literal : ((tail0.map FreeMonoid.of).prod).toList = tail0 := by checked_cut_rfl
  exact moved.trans literal

private theorem factors_literal :
    factors 400 = [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] := by
  have moved := congrArg (fun word : Word => word.toList.map factorSummary) (read_whole factorValue)
  have literal : ((tail0.map factorValue).prod).toList.map factorSummary =
      [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] := by checked_cut_rfl
  exact moved.trans literal

private theorem paid_literal : (run 400).1 = 159 :=
  (congrArg Prod.fst whole).trans actual_paid

private theorem effects_literal : effects 400 = [5, 5, 7, 7] := by
  have moved := congrArg FreeMonoid.toList (read_whole effectValue)
  have literal : ((tail0.map effectValue).prod).toList = [5, 5, 7, 7] := by checked_cut_rfl
  exact moved.trans literal

private theorem caches_count_literal :
    ((caches 400).filter fun completed => completed.2 = .delivery).length = 2 := by
  have moved := congrArg (fun word : FreeMonoid (CellId × NeedCacheLaws.CompletedReceiptKind) =>
    (word.toList.filter fun completed => completed.2 = .delivery).length) (read_whole cacheValue)
  have literal : (((tail0.map cacheValue).prod).toList.filter fun completed => completed.2 = .delivery).length = 2 := by
    checked_cut_rfl
  exact moved.trans literal

private theorem store_literal :
    OrderedDependencyStore.query (stateOf (run 400)).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  have moved := congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0) whole
  have literal : OrderedDependencyStore.query (stateOf cut161).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
    checked_cut_rfl
  exact moved.trans literal

private theorem recorded_eq (fuel capacity : Nat) :
    recorded fuel capacity = some ((Recording.Prefix.initial capacity).append (word fuel)) := by rfl

private theorem word_length : (word 400).length = 161 := by
  have moved := congrArg List.length word_literal
  have literal : tail0.length = 161 := by checked_cut_rfl
  exact moved.trans literal

theorem branch_words_literal :
    words = some [[("score", 0, 0), ("choose", 0, 2)], [("score", 0, 0), ("choose", 1, 2)]] := by
  have literal : wordsAt cut161 =
      some [[("score", 0, 0), ("choose", 0, 2)], [("score", 0, 0), ("choose", 1, 2)]] := by checked_cut_rfl
  exact (congrArg wordsAt whole).trans literal

theorem chronological_factors_literal :
    factors 400 = [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] := by
  exact factors_literal

theorem observed_ledger_identities_literal :
    Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400) =
      [4285307, 4674651, 32490407, 34246311] := by
  have moved := congrArg (fun word : FreeMonoid (Mettapedia.Algebra.SharedCoefficientLedger.Factor Nat CellId Factor) =>
    Mettapedia.Algebra.SharedCoefficientLedger.identities word.toList) (read_whole (ledgerBlock 407))
  have literal : Mettapedia.Algebra.SharedCoefficientLedger.identities ((tail0.map (ledgerBlock 407)).prod).toList =
      [4285307, 4674651, 32490407, 34246311] := by checked_cut_rfl
  exact moved.trans literal

/-- The same execution has two branch-local ordered words and one global
chronological observation. Neither the zero factors nor equal-valued rows
collapse, and the global word is not either answer's coefficient word. -/
theorem nested_zero_words_remain_per_answer :
    words = some [[("score", 0, 0), ("choose", 0, 2)], [("score", 0, 0), ("choose", 1, 2)]] ∧
      factors 400 = [("score", 0, 0), ("score", 0, 0), ("choose", 0, 2), ("choose", 1, 2)] ∧
      factors 400 ≠ (factors 400).reverse := by
  refine ⟨branch_words_literal, chronological_factors_literal, ?_⟩
  rw [chronological_factors_literal]
  decide +kernel

/-- Cache delivery, real effects and source coefficient production are
independent observations of this invocation. Both branches use their own
cached producer; the selected external handler serializes their effects. -/
theorem cached_delivery_adds_no_source_factor_or_effect :
    ((caches 400).filter fun completed => completed.2 = .delivery).length = 2 ∧
      (factors 400).length = 4 ∧ effects 400 = [5, 5, 7, 7] ∧
      OrderedDependencyStore.query (stateOf (run 400)).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  refine ⟨caches_count_literal, ?_, effects_literal, store_literal⟩
  rw [chronological_factors_literal]
  rfl

/-- These are physical observation occurrences, not a fold combining the
answer worlds. Copying their descriptions would repeat identities; claiming
this retained interval observes it at most once. -/
theorem chronological_ledger_keeps_occurrences_and_scope_claims :
    Mettapedia.Algebra.SharedCoefficientLedger.Valid (ledger 400) ∧
      ¬ Mettapedia.Algebra.SharedCoefficientLedger.Valid (ledger 400 ++ ledger 400) ∧
      Mettapedia.Algebra.SharedCoefficientLedger.Scoped.selected 0
        (Mettapedia.Algebra.SharedCoefficientLedger.Scoped.handle 0 17
          ⟨ledger 400, fun _ => none⟩) = [] := by
  refine ⟨?_, ?_, ?_⟩
  · change (Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400)).Nodup
    rw [observed_ledger_identities_literal]
    decide +kernel
  · change ¬ (Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400 ++ ledger 400)).Nodup
    simp only [Mettapedia.Algebra.SharedCoefficientLedger.identities, List.map_append]
    change ¬ (Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400) ++
      Mettapedia.Algebra.SharedCoefficientLedger.identities (ledger 400)).Nodup
    rw [observed_ledger_identities_literal]
    decide +kernel
  · exact Mettapedia.Algebra.SharedCoefficientLedger.Scoped.selected_after_handle _ _ _

/-- Polling work counts accepted provider requests; finishing inspections and
source/cache roles are not silently billed as additional source firings. -/
theorem enabled_history_and_poll_invoice_are_separate :
    (run 400).1 = 159 ∧ (word 400).length = 161 ∧
      (recorded 400 1000).map (fun record => (record.items.length, record.omitted)) = some (161, 0) ∧
      ((recorded 400 1000).bind Recording.Prefix.complete?).isSome = true := by
  refine ⟨paid_literal, word_length, ?_, ?_⟩
  · rw [recorded_eq, word_literal]
    checked_cut_rfl
  · rw [recorded_eq, word_literal]
    checked_cut_rfl

/-- Recording capacity bounds only captured history. The omitted suffix is
never presented as a complete history or an empty semantic contribution. -/
theorem bounded_history_refuses_false_completeness :
    (recorded 400 2).map (fun record => (record.items.length, record.omitted)) = some (2, 159) ∧
      (recorded 400 2).bind Recording.Prefix.complete? = none := by
  rw [recorded_eq, word_literal]
  constructor <;> checked_cut_rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

open Lean Meta Elab Tactic in
elab "checked_control_rfl" : tactic => withMainContext do
  match ← getGoals with
  | [] => return
  | goal :: _ =>
      let target ← whnf (← instantiateMVars (← goal.getType))
      unless target.isAppOfArity ``Eq 3 do
        throwError "an equality is required, got {target}"
      goal.assign (← mkEqRefl target.getAppArgs[2]!)
      replaceMainGoal []

open Lean Meta Elab Tactic Term in
elab "checked_control_exact " proof:term : tactic => withMainContext do
  let goal ← getMainGoal
  let expression ← Term.elabTerm proof none
  Term.synthesizeSyntheticMVarsNoPostponing
  goal.assign (← instantiateMVars expression)
  replaceMainGoal []


private def suffixValue {Result : Type} [Monoid Result]
    (value : View → Result) (fuel : Nat) (earlier : Saved) : Result :=
  (sourceAccount annotation number revocationWorlds required needed act reader notice 407 () value).of
    (NativeControlCursor.ProtocolHistory.resumeHistory source client charge fuel earlier)

private theorem suffix_exact {Result : Type} [Monoid Result]
    (value : View → Result) (fuel : Nat) (earlier : Saved) :
    suffixValue value fuel earlier = Read value fuel earlier :=
  PassiveReader.exact_account annotation number revocationWorlds required needed act reader notice
    407 value fuel earlier

private theorem resumed_whole : Cursor.resume source client charge 383 (run 17) = run 400 :=
  (Cursor.advance_add source client charge 17 383 packet).symm

private theorem completed_inert (allowance : Nat) :
    Cursor.resume source client charge allowance (run 400) = run 400 := by
  have literal : Cursor.resume source client charge allowance cut161 = cut161 := by checked_control_rfl
  exact (congrArg (Cursor.resume source client charge allowance) whole).trans (literal.trans whole.symm)

private theorem resume_initial (fuel : Nat) :
    Cursor.resume source client charge fuel (0, .paused packet) = run fuel := by
  simpa only [Nat.zero_add, Cursor.advance_zero, run] using
    (Cursor.advance_add source client charge 0 fuel packet).symm

private theorem suffix_word : (Read FreeMonoid.of 383 (run 17)).toList = tail17 := by
  have moved := congrArg (fun saved => (Read FreeMonoid.of 383 saved).toList) whole_at17
  have folded := congrArg FreeMonoid.toList (tail_read17 FreeMonoid.of)
  have literal : ((tail17.map FreeMonoid.of).prod).toList = tail17 := by checked_control_rfl
  exact moved.trans (folded.trans literal)

private theorem prefix_word : word 17 = prefix0 := by
  have moved := congrArg FreeMonoid.toList (read_prefix FreeMonoid.of)
  have literal : ((prefix0.map FreeMonoid.of).prod).toList = prefix0 := by checked_control_rfl
  exact moved.trans literal

private theorem observed_erasure (fuel : Nat) (earlier : Saved) (record : Option (Recording.Prefix View)) :
    (observedResume annotation number revocationWorlds required needed act reader notice 407 fuel earlier record).1 =
      Cursor.resume source client charge fuel earlier := rfl

private theorem observed_record_eq (fuel : Nat) (earlier : Saved) (record : Recording.Prefix View) :
    (observedResume annotation number revocationWorlds required needed act reader notice 407 fuel earlier (some record)).2 =
      some (record.append (Read FreeMonoid.of fuel earlier).toList) := rfl

private theorem factors_split :
    factors 17 ++ (Read factorValue 383 (run 17)).toList.map factorSummary = factors 400 := by
  have split := PassiveReader.readSuffix_add annotation number revocationWorlds required needed act reader notice
    407 factorValue 17 383 (0, .paused packet)
  have moved := congrArg (fun word : Word => word.toList.map factorSummary) split
  simpa only [factors, resume_initial, FreeMonoid.toList_mul, List.map_append] using moved.symm

/-- Starting at this real paid cut observes only the later interval. Its
suffix factors concatenate with the prefix in actual callback order. -/
theorem start_recording_at_paid_cut_keeps_the_real_suffix :
    let first := run 17
    let suffixFactors := (suffixValue factorValue 383 first).toList.map factorSummary
    let observed := observedResume annotation number revocationWorlds required needed act reader notice
      407 383 first (some (Recording.Prefix.initial 1000))
    factors 17 ++ suffixFactors = factors 400 ∧ observed.1.1 = (run 400).1 ∧
      (observed.2.map fun record => record.items.length) = some 144 ∧
      OrderedDependencyStore.query (stateOf observed.1).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  have account := suffix_exact factorValue 383 (run 17)
  have described := congrArg (fun word : Word => word.toList.map factorSummary) account
  refine ⟨?_, ?_, ?_, ?_⟩
  · checked_control_exact (congrArg (fun later => factors 17 ++ later) described).trans factors_split
  · checked_control_exact (congrArg Prod.fst (observed_erasure 383 (run 17) (some (Recording.Prefix.initial 1000)))).trans (congrArg Prod.fst resumed_whole)
  · rw [observed_record_eq, suffix_word]
    checked_control_rfl
  · checked_control_exact (congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0)
      ((observed_erasure 383 (run 17) (some (Recording.Prefix.initial 1000))).trans resumed_whole)).trans store_literal

/-- Stopping preserves the selected prefix while the actual computation
continues; forgetting it disables future recording without restarting work. -/
theorem stop_and_forget_never_reissue_the_paid_prefix :
    let first := run 17
    let captured := (Recording.Prefix.initial 1000).append (word 17)
    let stopped := stopAndResume annotation number revocationWorlds required needed act reader notice
      407 383 first captured
    let forgotten := observedResume annotation number revocationWorlds required needed act reader notice
      407 10 stopped.1 (forgetRecording (some stopped.2))
    stopped.1.1 = (run 400).1 ∧ (stopped.2.map tag).items.length = 17 ∧
      forgotten.2 = none ∧ forgotten.1.1 = (run 400).1 ∧
      (stateOf forgotten.1).1 = (stateOf (run 400)).1 ∧
      OrderedDependencyStore.query (stateOf forgotten.1).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  dsimp only
  rw [stop_preserves_prefix annotation number revocationWorlds required needed act reader notice 407 383 (run 17) ((Recording.Prefix.initial 1000).append (word 17)), resumed_whole]
  change (run 400).1 = (run 400).1 ∧
    (((Recording.Prefix.initial 1000).append (word 17)).map tag).items.length = 17 ∧
    (observedResume annotation number revocationWorlds required needed act reader notice 407 10 (run 400) none).2 = none ∧
    (observedResume annotation number revocationWorlds required needed act reader notice 407 10 (run 400) none).1.1 = (run 400).1 ∧
    (stateOf (observedResume annotation number revocationWorlds required needed act reader notice 407 10 (run 400) none).1).1 =
      (stateOf (run 400)).1 ∧ _
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩
  · rw [prefix_word]
    checked_control_rfl
  · checked_control_exact congrArg Prod.fst ((observed_erasure 10 (run 400) none).trans (completed_inert 10))
  · checked_control_exact congrArg (fun saved => (stateOf saved).1) ((observed_erasure 10 (run 400) none).trans (completed_inert 10))
  · checked_control_exact (congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0)
      ((observed_erasure 10 (run 400) none).trans (completed_inert 10))).trans store_literal

/-- A rejected observation decoder does not filter the missing evidence.
Rechecking the same complete retained interval changes neither source state
nor the already accepted effects; it is not native execution authority. -/
theorem qualified_readback_is_passive_and_missing_payload_refuses :
    let captured := (Recording.Prefix.initial 1000).append (word 400)
    let reread := Recording.Prefix.project? (fun event => some (tag event)) captured
    let resumed := observedResume annotation number revocationWorlds required needed act reader notice
      407 10 (run 400) (some captured)
    Recording.Prefix.project? (fun (_ : View) => (none : Option Nat)) captured = none ∧
      reread.map List.length = some 161 ∧
      (resumed.2.map (fun record => record.items.length)) = some 161 ∧
      resumed.1.1 = (run 400).1 ∧
      (stateOf resumed.1).1 = (stateOf (run 400)).1 ∧
      OrderedDependencyStore.query (stateOf resumed.1).2.live.store 0 = [7, 7, 5, 5, 7, 7] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [word_literal]
    checked_control_rfl
  · rw [word_literal]
    checked_control_rfl
  · rw [observed_record_eq]
    have quiet : Read FreeMonoid.of 10 (run 400) = 1 := by
      have moved := congrArg (Read FreeMonoid.of 10) whole
      have literal : Read FreeMonoid.of 10 cut161 = 1 := by checked_control_rfl
      exact moved.trans literal
    rw [quiet, word_literal]
    checked_control_rfl
  · checked_control_exact congrArg Prod.fst ((observed_erasure 10 (run 400) (some ((Recording.Prefix.initial 1000).append (word 400)))).trans (completed_inert 10))
  · checked_control_exact congrArg (fun saved => (stateOf saved).1) ((observed_erasure 10 (run 400) (some ((Recording.Prefix.initial 1000).append (word 400)))).trans (completed_inert 10))
  · checked_control_exact (congrArg (fun saved => OrderedDependencyStore.query (stateOf saved).2.live.store 0)
      ((observed_erasure 10 (run 400) (some ((Recording.Prefix.initial 1000).append (word 400)))).trans (completed_inert 10))).trans store_literal

def revoke (saved : Saved) : Saved :=
  (saved.1, Cursor.Outcome.mapState client (source := source) (target := source)
    (fun state => ((state.1.1, { state.1.2 with live := { state.1.2.live with
      point := Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked } }), state.2)) saved.2)

def denied := Cursor.resume source client charge 10 (revoke (run 17))
def deniedHistory := NativeControlCursor.ProtocolHistory.resumeHistory source client charge 10 (revoke (run 17))

private noncomputable def deniedCut : Saved := normalized_cursor_cut% (Cursor.resume source client charge 10 (revoke cut17))
private theorem denied_step : Cursor.resume source client charge 10 (revoke cut17) = deniedCut := by checked_control_rfl
private theorem denied_eq : denied = deniedCut :=
  (congrArg (Cursor.resume source client charge 10) (congrArg revoke whole_at17)).trans denied_step

private theorem denied_account {Result : Type} [Monoid Result] (value : View → Result) :
    suffixValue value 10 (revoke (run 17)) = Read value 10 (revoke cut17) :=
  (suffix_exact value 10 (revoke (run 17))).trans
    (congrArg (Read value 10) (congrArg revoke whole_at17))

/-- Revocation adds an honest refused inspection to history, then the client
finishes that refusal. It emits no factor or effect and changes neither the
paid account nor the complete retained branch frontier. -/
theorem current_refusal_has_no_semantic_history_contribution :
    (suffixValue FreeMonoid.of 10 (revoke (run 17))).toList.map tag = [2, 1] ∧
      (suffixValue factorValue 10 (revoke (run 17))).toList = [] ∧
      (suffixValue effectValue 10 (revoke (run 17))).toList = [] ∧
      denied.1 = 17 ∧ (stateOf denied).1 = (stateOf (run 17)).1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have moved := congrArg (fun word : FreeMonoid View => word.toList.map tag) (denied_account FreeMonoid.of)
    have literal : (Read FreeMonoid.of 10 (revoke cut17)).toList.map tag = [2, 1] := by checked_control_rfl
    checked_control_exact moved.trans literal
  · have moved := congrArg FreeMonoid.toList (denied_account factorValue)
    have literal : (Read factorValue 10 (revoke cut17)).toList = [] := by checked_control_rfl
    checked_control_exact moved.trans literal
  · have moved := congrArg FreeMonoid.toList (denied_account effectValue)
    have literal : (Read effectValue 10 (revoke cut17)).toList = [] := by checked_control_rfl
    checked_control_exact moved.trans literal
  · have literal : deniedCut.1 = 17 := by checked_control_rfl
    checked_control_exact (congrArg Prod.fst denied_eq).trans literal
  · have literal : (stateOf deniedCut).1 = (stateOf cut17).1 := by checked_control_rfl
    checked_control_exact (congrArg (fun saved => (stateOf saved).1) denied_eq).trans
      (literal.trans (congrArg (fun saved => (stateOf saved).1) whole_at17.symm))

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler.SharedSource.Weighted.History.Controls
