import Mettapedia.Computability.WordTemplateMachine
import Mettapedia.Computability.StackMachineComposition
import Mettapedia.Computability.WordEqualityMachine

/-!
# Physical reconstruction and strict word-length checking

The four input fields are rebuilt, feature, residual and original words. An
ordered symbol comparison checks reconstruction. One unary marker per feature
or residual bit is debited by original bits, so strict shortening does not use
a growing natural register. The output carries a Boolean and both candidate
words; a completed false result is distinct from unfinished computation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedCompressionCheck

open Turing StateTransition Turing.TM2.Stmt WordTemplateMachine

inductive Capture where
  | rebuilt | feature | residual
  deriving DecidableEq, Fintype

inductive Stack where
  | input | buffer (kind : Capture) | saved | credit | result
  deriving DecidableEq, Fintype

inductive Phase where
  | capture (kind : Capture) | restore | compare | drainInput | drainTemporary
  | drainSaved | drainCredit | emitFeature | emitResidual | finish
  deriving DecidableEq, Fintype

structure Registers where
  current : Option (Option Bool)
  saved : Option Bool
  marker : Option Unit
  equalFlag : Bool
  shortFlag : Bool
  deriving DecidableEq, Fintype

def clean (equalFlag shortFlag : Bool) : Registers := ⟨none, none, none, equalFlag, shortFlag⟩

abbrev Alphabet : Stack → Type
  | .input | .result => Option Bool
  | .credit => Unit
  | .buffer _ | .saved => Bool

def charged : Capture → Bool
  | .rebuilt => false
  | .feature | .residual => true

def following : Capture → Phase
  | .rebuilt => .restore
  | .feature => .capture .residual
  | .residual => .compare

def program : Phase → TM2.Stmt Alphabet Phase Registers
  | .capture kind => pop .input (fun state cell => { state with current := cell })
      (branch (fun state => state.current.isSome)
        (branch (fun state => state.current.join.isSome)
          (push (.buffer kind) (fun state => state.current.join.getD false)
            (if charged kind then
              push .credit (fun _ => ())
                (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .capture kind))
            else load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .capture kind)))
          (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => following kind)))
        (load (fun state => clean false state.shortFlag) (goto fun _ => .drainInput)))
  | .restore => pop (.buffer .rebuilt) (fun state cell => { state with saved := cell })
      (branch (fun state => state.saved.isSome)
        (push .saved (fun state => state.saved.getD false)
          (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .restore)))
        (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .capture .feature)))
  | .compare => pop .input (fun state cell => { state with current := cell })
      (branch (fun state => state.current.isSome)
        (branch (fun state => state.current.join.isSome)
          (pop .saved (fun state cell => { state with saved := cell })
            (pop .credit (fun state cell => { state with marker := cell })
              (load (fun state => clean
                  (state.equalFlag && decide (state.saved = state.current.join))
                  (state.shortFlag || state.marker.isNone))
                (goto fun _ => .compare))))
          (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .drainInput)))
        (load (fun state => clean false state.shortFlag) (goto fun _ => .drainInput)))
  | .drainInput => pop .input (fun state cell => { state with current := cell })
      (branch (fun state => state.current.isSome)
        (load (fun state => clean false state.shortFlag) (goto fun _ => .drainInput))
        (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .drainTemporary)))
  | .drainTemporary => pop (.buffer .rebuilt) (fun state cell => { state with saved := cell })
      (branch (fun state => state.saved.isSome)
        (load (fun state => clean false state.shortFlag) (goto fun _ => .drainTemporary))
        (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .drainSaved)))
  | .drainSaved => pop .saved (fun state cell => { state with saved := cell })
      (branch (fun state => state.saved.isSome)
        (load (fun state => clean false state.shortFlag) (goto fun _ => .drainSaved))
        (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .drainCredit)))
  | .drainCredit => pop .credit (fun state cell => { state with marker := cell })
      (branch (fun state => state.marker.isSome)
        (load (fun state => clean state.equalFlag false) (goto fun _ => .drainCredit))
        (push .result (fun _ => none)
          (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .emitFeature))))
  | .emitFeature => pop (.buffer .feature) (fun state cell => { state with saved := cell })
      (branch (fun state => state.saved.isSome)
        (push .result (fun state => some (state.saved.getD false))
          (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .emitFeature)))
        (push .result (fun _ => none)
          (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .emitResidual))))
  | .emitResidual => pop (.buffer .residual) (fun state cell => { state with saved := cell })
      (branch (fun state => state.saved.isSome)
        (push .result (fun state => some (state.saved.getD false))
          (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .emitResidual)))
        (load (fun state => clean state.equalFlag state.shortFlag) (goto fun _ => .finish)))
  | .finish => push .result (fun state => some (state.equalFlag && state.shortFlag))
      (load (fun _ => clean true false) halt)

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet
  Λ := Phase
  main := .capture .rebuilt
  σ := Registers
  initialState := clean true false
  m := program

def config (phase : Option Phase) (equalFlag shortFlag : Bool) (input : List (Option Bool))
    (buffers : Capture → List Bool) (saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.Cfg where
  l := phase
  var := clean equalFlag shortFlag
  stk key := match (show Stack from key) with
    | .input => input | .buffer kind => buffers kind | .saved => saved | .credit => credit | .result => result

def paired (feature residual : List Bool) : Capture → List Bool
  | .rebuilt => []
  | .feature => feature
  | .residual => residual

def equalityFrom : Bool → List Bool → List Bool → Bool
  | flag, left, [] => flag && left.isEmpty
  | flag, left, bit :: rest => equalityFrom (flag && decide (left.head? = some bit)) left.tail rest

theorem equalityFrom_eq (flag : Bool) (left right : List Bool) :
    equalityFrom flag left right = (flag && decide (left = right)) := by
  induction right generalizing flag left with
  | nil => cases left <;> simp [equalityFrom]
  | cons bit rest ih =>
      cases left with
      | nil => simp [equalityFrom, ih]
      | cons head tail => simp [equalityFrom, ih, Bool.and_assoc]

def shorterFrom : Bool → List Unit → List Bool → Bool
  | flag, credit, [] => flag && credit.isEmpty
  | flag, credit, _bit :: rest => shorterFrom (flag || credit.isEmpty) credit.tail rest

theorem shorterFrom_eq (flag : Bool) (credit : List Unit) (word : List Bool) :
    shorterFrom flag credit word =
      (decide (credit.length ≤ word.length) && (flag || decide (credit.length < word.length))) := by
  induction word generalizing flag credit with
  | nil => cases credit <;> simp [shorterFrom]
  | cons bit rest ih => cases credit <;> simp [shorterFrom, ih]

theorem shorterFrom_false (credit : List Unit) (word : List Bool) :
    shorterFrom false credit word = decide (credit.length < word.length) := by
  rw [shorterFrom_eq]
  by_cases less : credit.length < word.length
  · simp [less, Nat.le_of_lt less]
  · simp [less]

local macro "check_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, clean, paired, charged, following, haltList, TM2.step, TM2.stepAux]
  all_goals funext key
  all_goals cases key with
    | buffer kind => cases kind <;> simp [Function.update, paired]
    | _ => simp [Function.update]))

theorem capture_symbol (kind : Capture) (equalFlag shortFlag : Bool) (bit : Bool)
    (input : List (Option Bool)) (buffers : Capture → List Bool) (saved : List Bool)
    (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some (.capture kind)) equalFlag shortFlag (some bit :: input) buffers saved credit result) =
      some (config (some (.capture kind)) equalFlag shortFlag input
        (Function.update buffers kind (bit :: buffers kind)) saved
        (if charged kind then () :: credit else credit) result) := by
  cases kind <;> simp only [charged] <;> check_step

theorem capture_delimiter (kind : Capture) (equalFlag shortFlag : Bool)
    (input : List (Option Bool)) (buffers : Capture → List Bool) (saved : List Bool)
    (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some (.capture kind)) equalFlag shortFlag (none :: input) buffers saved credit result) =
      some (config (some (following kind)) equalFlag shortFlag input buffers saved credit result) := by
  cases kind <;> check_step

theorem restore_symbol (equalFlag shortFlag : Bool) (bit : Bool) (temporary : List Bool)
    (input : List (Option Bool)) (feature residual saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .restore) equalFlag shortFlag input
      (Function.update (paired feature residual) .rebuilt (bit :: temporary)) saved credit result) =
      some (config (some .restore) equalFlag shortFlag input
        (Function.update (paired feature residual) .rebuilt temporary) (bit :: saved) credit result) := by check_step

theorem restore_end (equalFlag shortFlag : Bool) (input : List (Option Bool))
    (feature residual saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .restore) equalFlag shortFlag input (paired feature residual) saved credit result) =
      some (config (some (.capture .feature)) equalFlag shortFlag input (paired feature residual) saved credit result) := by check_step

theorem compare_symbol (equalFlag shortFlag : Bool) (bit : Bool) (input : List (Option Bool))
    (feature residual saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .compare) equalFlag shortFlag (some bit :: input)
      (paired feature residual) saved credit result) =
      some (config (some .compare) (equalFlag && decide (saved.head? = some bit))
        (shortFlag || credit.isEmpty) input (paired feature residual) saved.tail credit.tail result) := by
  cases saved <;> cases credit <;> check_step

theorem compare_delimiter (equalFlag shortFlag : Bool) (input : List (Option Bool))
    (feature residual saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .compare) equalFlag shortFlag (none :: input)
      (paired feature residual) saved credit result) =
      some (config (some .drainInput) equalFlag shortFlag input (paired feature residual) saved credit result) := by check_step

theorem drain_input_end (equalFlag shortFlag : Bool)
    (feature residual saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .drainInput) equalFlag shortFlag [] (paired feature residual) saved credit result) =
      some (config (some .drainTemporary) equalFlag shortFlag [] (paired feature residual) saved credit result) := by check_step

theorem drain_temporary_end (equalFlag shortFlag : Bool)
    (feature residual saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .drainTemporary) equalFlag shortFlag [] (paired feature residual) saved credit result) =
      some (config (some .drainSaved) equalFlag shortFlag [] (paired feature residual) saved credit result) := by check_step

theorem paired_update_feature (feature residual value : List Bool) :
    Function.update (paired feature residual) .feature value = paired value residual := by
  funext kind
  cases kind <;> rfl

theorem paired_update_residual (feature residual value : List Bool) :
    Function.update (paired feature residual) .residual value = paired feature value := by
  funext kind
  cases kind <;> rfl

theorem paired_update_rebuilt_empty (feature residual : List Bool) :
    Function.update (paired feature residual) .rebuilt [] = paired feature residual := by
  funext kind
  cases kind <;> rfl

def capture_run (kind : Capture) (word : List Bool) (tail : List (Option Bool))
    (buffers : Capture → List Bool) (saved : List Bool) (credit : List Unit) (result : List (Option Bool))
    (equalFlag shortFlag : Bool) :
    EvalsToInTime machine.step
      (config (some (.capture kind)) equalFlag shortFlag (word.map some ++ none :: tail) buffers saved credit result)
      (some (config (some (following kind)) equalFlag shortFlag tail
        (Function.update buffers kind (word.reverse ++ buffers kind)) saved
        (List.replicate (if charged kind then word.length else 0) () ++ credit) result)) (word.length + 1) := by
  induction word generalizing buffers credit with
  | nil =>
      simpa using StackMachineComposition.oneStep
        (capture_delimiter kind equalFlag shortFlag tail buffers saved credit result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep
        (capture_symbol kind equalFlag shortFlag bit (rest.map some ++ none :: tail) buffers saved credit result)
      have finish := ih (Function.update buffers kind (bit :: buffers kind))
        (if charged kind then () :: credit else credit)
      have joined := EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish
      cases kind <;> simpa [charged, List.reverse_cons, List.append_assoc, List.replicate_succ',
        Function.update_idem] using joined

def restore_run (temporary saved : List Bool) (input : List (Option Bool))
    (feature residual : List Bool) (credit : List Unit) (result : List (Option Bool))
    (equalFlag shortFlag : Bool) :
    EvalsToInTime machine.step
      (config (some .restore) equalFlag shortFlag input
        (Function.update (paired feature residual) .rebuilt temporary) saved credit result)
      (some (config (some (.capture .feature)) equalFlag shortFlag input (paired feature residual)
        (temporary.reverse ++ saved) credit result)) (temporary.length + 1) := by
  induction temporary generalizing saved with
  | nil => simpa only [paired_update_rebuilt_empty, List.reverse_nil, List.nil_append,
      List.length_nil, Nat.zero_add] using
      StackMachineComposition.oneStep (restore_end equalFlag shortFlag input feature residual saved credit result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep
        (restore_symbol equalFlag shortFlag bit rest input feature residual saved credit result)
      have finish := ih (bit :: saved)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

theorem drain_saved_symbol (equalFlag shortFlag : Bool) (bit : Bool)
    (feature residual saved : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .drainSaved) equalFlag shortFlag [] (paired feature residual) (bit :: saved) credit result) =
      some (config (some .drainSaved) false shortFlag [] (paired feature residual) saved credit result) := by check_step

theorem drain_saved_end (equalFlag shortFlag : Bool)
    (feature residual : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .drainSaved) equalFlag shortFlag [] (paired feature residual) [] credit result) =
      some (config (some .drainCredit) equalFlag shortFlag [] (paired feature residual) [] credit result) := by check_step

theorem drain_credit_symbol (equalFlag shortFlag : Bool)
    (feature residual : List Bool) (credit : List Unit) (result : List (Option Bool)) :
    machine.step (config (some .drainCredit) equalFlag shortFlag [] (paired feature residual) [] (() :: credit) result) =
      some (config (some .drainCredit) equalFlag false [] (paired feature residual) [] credit result) := by check_step

theorem drain_credit_end (equalFlag shortFlag : Bool) (feature residual : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .drainCredit) equalFlag shortFlag [] (paired feature residual) [] [] result) =
      some (config (some .emitFeature) equalFlag shortFlag [] (paired feature residual) [] [] (none :: result)) := by check_step

theorem emit_feature_symbol (equalFlag shortFlag : Bool) (bit : Bool)
    (feature residual : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .emitFeature) equalFlag shortFlag [] (paired (bit :: feature) residual) [] [] result) =
      some (config (some .emitFeature) equalFlag shortFlag [] (paired feature residual) [] [] (some bit :: result)) := by check_step

theorem emit_feature_end (equalFlag shortFlag : Bool) (residual : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .emitFeature) equalFlag shortFlag [] (paired [] residual) [] [] result) =
      some (config (some .emitResidual) equalFlag shortFlag [] (paired [] residual) [] [] (none :: result)) := by check_step

theorem emit_residual_symbol (equalFlag shortFlag : Bool) (bit : Bool)
    (residual : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .emitResidual) equalFlag shortFlag [] (paired [] (bit :: residual)) [] [] result) =
      some (config (some .emitResidual) equalFlag shortFlag [] (paired [] residual) [] [] (some bit :: result)) := by check_step

theorem emit_residual_end (equalFlag shortFlag : Bool) (result : List (Option Bool)) :
    machine.step (config (some .emitResidual) equalFlag shortFlag [] (paired [] []) [] [] result) =
      some (config (some .finish) equalFlag shortFlag [] (paired [] []) [] [] result) := by check_step

theorem finish_step (equalFlag shortFlag : Bool) (result : List (Option Bool)) :
    machine.step (config (some .finish) equalFlag shortFlag [] (paired [] []) [] [] result) =
      some (haltList machine (some (equalFlag && shortFlag) :: result)) := by check_step

def drain_saved_run (saved : List Bool) (feature residual : List Bool) (credit : List Unit)
    (result : List (Option Bool)) (equalFlag shortFlag : Bool) :
    EvalsToInTime machine.step
      (config (some .drainSaved) equalFlag shortFlag [] (paired feature residual) saved credit result)
      (some (config (some .drainCredit) (equalFlag && saved.isEmpty) shortFlag []
        (paired feature residual) [] credit result)) (saved.length + 1) := by
  induction saved generalizing equalFlag with
  | nil => simpa using StackMachineComposition.oneStep (drain_saved_end equalFlag shortFlag feature residual credit result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (drain_saved_symbol equalFlag shortFlag bit feature residual rest credit result)
      have finish := ih false
      simpa using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

def drain_credit_run (credit : List Unit) (feature residual : List Bool)
    (result : List (Option Bool)) (equalFlag shortFlag : Bool) :
    EvalsToInTime machine.step
      (config (some .drainCredit) equalFlag shortFlag [] (paired feature residual) [] credit result)
      (some (config (some .emitFeature) equalFlag (shortFlag && credit.isEmpty) []
        (paired feature residual) [] [] (none :: result))) (credit.length + 1) := by
  induction credit generalizing shortFlag with
  | nil => simpa using StackMachineComposition.oneStep (drain_credit_end equalFlag shortFlag feature residual result)
  | cons marker rest ih =>
      cases marker
      have first := StackMachineComposition.oneStep (drain_credit_symbol equalFlag shortFlag feature residual rest result)
      have finish := ih false
      simpa using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first finish

def emit_residual_run (residual : List Bool) (result : List (Option Bool)) (equalFlag shortFlag : Bool) :
    EvalsToInTime machine.step
      (config (some .emitResidual) equalFlag shortFlag [] (paired [] residual) [] [] result)
      (some (haltList machine (some (equalFlag && shortFlag) :: (residual.reverse.map some ++ result))))
      (residual.length + 2) := by
  induction residual generalizing result with
  | nil =>
      have first := StackMachineComposition.oneStep (emit_residual_end equalFlag shortFlag result)
      have finish := StackMachineComposition.oneStep (finish_step equalFlag shortFlag result)
      simpa using EvalsToInTime.trans _ 1 1 _ _ _ first finish
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (emit_residual_symbol equalFlag shortFlag bit rest result)
      have finish := ih (some bit :: result)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 2) _ _ _ first finish

def emit_feature_run (feature residual : List Bool) (result : List (Option Bool)) (equalFlag shortFlag : Bool) :
    EvalsToInTime machine.step
      (config (some .emitFeature) equalFlag shortFlag [] (paired feature residual) [] [] result)
      (some (haltList machine (some (equalFlag && shortFlag) ::
        (residual.reverse.map some ++ none :: (feature.reverse.map some ++ result)))))
      (feature.length + residual.length + 3) := by
  induction feature generalizing result with
  | nil =>
      have first := StackMachineComposition.oneStep (emit_feature_end equalFlag shortFlag residual result)
      have finish := emit_residual_run residual (none :: result) equalFlag shortFlag
      simpa using EvalsToInTime.trans _ 1 (residual.length + 2) _ _ _ first finish
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (emit_feature_symbol equalFlag shortFlag bit rest residual result)
      have finish := ih (some bit :: result)
      simpa [List.reverse_cons, List.map_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (rest.length + residual.length + 3) _ _ _ first finish

def response (accepted : Bool) (residual feature : List Bool) : List (Option Bool) :=
  some accepted :: Indexed.frame [residual, feature]

def compare_run (saved original : List Bool) (credit : List Unit) (feature residual : List Bool)
    (equalFlag shortFlag : Bool) :
    EvalsToInTime machine.step
      (config (some .compare) equalFlag shortFlag (original.map some ++ [none])
        (paired feature residual) saved credit [])
      (some (haltList machine (response
        (equalityFrom equalFlag saved original && shorterFrom shortFlag credit original)
        residual.reverse feature.reverse)))
      (saved.length + credit.length + original.length + feature.length + residual.length + 8) := by
  induction original generalizing saved credit equalFlag shortFlag with
  | nil =>
      have a := StackMachineComposition.oneStep (compare_delimiter equalFlag shortFlag [] feature residual saved credit [])
      have b := StackMachineComposition.oneStep (drain_input_end equalFlag shortFlag feature residual saved credit [])
      have c := StackMachineComposition.oneStep (drain_temporary_end equalFlag shortFlag feature residual saved credit [])
      have d := drain_saved_run saved feature residual credit [] equalFlag shortFlag
      have e := drain_credit_run credit feature residual [] (equalFlag && saved.isEmpty) shortFlag
      have f := emit_feature_run feature residual [none] (equalFlag && saved.isEmpty) (shortFlag && credit.isEmpty)
      have ab := EvalsToInTime.trans _ _ _ _ _ _ a b
      have abc := EvalsToInTime.trans _ _ _ _ _ _ ab c
      have abcd := EvalsToInTime.trans _ _ _ _ _ _ abc d
      have abcde := EvalsToInTime.trans _ _ _ _ _ _ abcd e
      have joined := EvalsToInTime.trans _ _ _ _ _ _ abcde f
      simpa [equalityFrom, shorterFrom, response, Indexed.frame, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (compare_symbol equalFlag shortFlag bit
        (rest.map some ++ [none]) feature residual saved credit [])
      have finish := ih saved.tail credit.tail (equalFlag && decide (saved.head? = some bit))
        (shortFlag || credit.isEmpty)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first finish
      have widened := WordEqualityMachine.within joined
        (show _ ≤ saved.length + credit.length + (bit :: rest).length + feature.length + residual.length + 8 from by
          have savedLength : saved.tail.length ≤ saved.length := by cases saved <;> simp
          have creditLength : credit.tail.length ≤ credit.length := by cases credit <;> simp
          simp only [List.length_cons]
          omega)
      simpa only [equalityFrom, shorterFrom, List.map_cons, List.cons_append] using widened

def packet (rebuilt feature residual original : List Bool) : List (Option Bool) :=
  Indexed.frame [rebuilt, feature, residual, original]

def verdict (rebuilt feature residual original : List Bool) : Bool :=
  decide (rebuilt = original) && decide (feature.length + residual.length < original.length)

theorem verdict_true_iff (rebuilt feature residual original : List Bool) :
    verdict rebuilt feature residual original = true ↔
      rebuilt = original ∧ feature.length + residual.length < original.length := by simp [verdict]

theorem initial_agrees (input : List (Option Bool)) :
    initList machine input = config (some (.capture .rebuilt)) true false input (paired [] []) [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | buffer kind => cases kind <;> simp [paired]
  | _ => simp

theorem packet_length (rebuilt feature residual original : List Bool) :
    (packet rebuilt feature residual original).length =
      rebuilt.length + feature.length + residual.length + original.length + 4 := by
  simp [packet, Indexed.frame]
  omega

/-- A completed check returns both candidate words and exactly the independent
reconstruction/strict-shortening decision. All reads and cleanup are counted. -/
def outputs (rebuilt feature residual original : List Bool) :
    TM2OutputsInTime machine (packet rebuilt feature residual original)
      (some (response (verdict rebuilt feature residual original) residual feature))
      (4 * ((packet rebuilt feature residual original).length + 1)) := by
  have a := capture_run .rebuilt rebuilt (Indexed.frame [feature, residual, original])
    (paired [] []) [] [] [] true false
  simp [following, charged, paired] at a
  have b := restore_run rebuilt.reverse [] (Indexed.frame [feature, residual, original]) [] [] [] [] true false
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at b
  have c := capture_run .feature feature (Indexed.frame [residual, original]) (paired [] []) rebuilt [] [] true false
  simp [following, charged, paired_update_feature, paired] at c
  have d := capture_run .residual residual (Indexed.frame [original]) (paired feature.reverse []) rebuilt
    (List.replicate feature.length ()) [] true false
  simp [following, charged, paired_update_residual, paired] at d
  have e := compare_run rebuilt original
    (List.replicate (residual.length + feature.length) ()) feature.reverse residual.reverse true false
  simp only [Indexed.frame, List.flatMap_cons, List.flatMap_nil, List.append_assoc,
    List.singleton_append, List.append_nil] at a b c d e
  have ab := EvalsToInTime.trans _ _ _ _ _ _ a b
  have abc := EvalsToInTime.trans _ _ _ _ _ _ ab c
  have abcd := EvalsToInTime.trans _ _ _ _ _ _ abc d
  have joined := EvalsToInTime.trans _ _ _ _ _ _ abcd e
  have widened := WordEqualityMachine.within joined
    (show _ ≤ 4 * ((packet rebuilt feature residual original).length + 1) from by
      simp only [List.length_reverse, List.length_replicate, packet_length]
      omega)
  change EvalsToInTime machine.step (initList machine _) (some (haltList machine _)) _
  rw [initial_agrees]
  simpa [packet, Indexed.frame, equalityFrom_eq, shorterFrom_false, verdict,
    List.reverse_reverse, List.append_assoc, Nat.add_comm] using widened

end Mettapedia.Computability.FramedCompressionCheck
