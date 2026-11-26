import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicExecution

/-!
# Compiling the ports of a symbolic firing

Each port reads the ordinal of a live occurrence, not its value
code. The emitted p1 MATCH only checks resource use and records
the equation. Different occurrences with equal labels can still
take different slots; reads may share a live occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPortCode

open Mettapedia.Logic.LP
open Derivation (Role Match)
open Derivation.SymbolicFiring (LiveWorld)
open SymbolicExecution (Work Equations Code Frame profile storeOf)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

abbrev Port (σ : LPSignature) := Term σ × ℕ

def indexReg : P1Source.Reg := 0
def passReg : P1Source.Reg := 1

def emit (available : List ℕ) (role : Role) (level : ℕ) :
    List (Port σ) → Code σ → Code σ
  | [], next => next
  | port :: later, next =>
    .seq (.instruction (.immediate .u64 indexReg (.ofNat 64 (available.idxOf port.2)))) <|
      .seq (.instruction (.transform (.premise role port.1 level indexReg passReg))) <|
        .branch passReg (emit available role (level + 1) later next) (.ret .refused passReg)

def extend (label : ℕ → Term σ) (role : Role) (entry : Match (Term σ) (Work σ)) (port : Port σ) :
    Match (Term σ) (Work σ) :=
  entry.select role port.2 (entry.bindings.extend (port.1, label port.2))

def extendAll (label : ℕ → Term σ) (role : Role) : List (Port σ) →
    Match (Term σ) (Work σ) → Match (Term σ) (Work σ)
  | [], entry => entry
  | p :: ps, entry => extendAll label role ps (extend label role entry p)

@[simp] theorem extendAll_problem (base : Equations σ) (label : ℕ → Term σ) (role : Role)
    (ports : List (Port σ)) (entry : Match (Term σ) (Work σ)) :
    (extendAll label role ports entry).bindings.problem base =
      entry.bindings.problem base ++ ports.map (fun p => (p.1, label p.2)) := by
  induction ports generalizing entry with
  | nil => simp [extendAll]
  | cons q tail ih =>
    rw [extendAll, ih]
    cases role <;> simp [extend, Match.select, Work.extend_problem, List.append_assoc]

@[simp] theorem extendAll_take (label : ℕ → Term σ) (ports : List (Port σ))
    (entry : Match (Term σ) (Work σ)) :
    (extendAll label .take ports entry).taken = entry.taken ++ ports.map Prod.snd ∧
      (extendAll label .take ports entry).read = entry.read := by
  induction ports generalizing entry with
  | nil => simp [extendAll]
  | cons q tail ih =>
    rw [extendAll]
    obtain ⟨taken, read⟩ := ih (extend label .take entry q)
    refine ⟨?_, read⟩
    rw [taken]
    simp [extend, Match.select, List.append_assoc]

@[simp] theorem extendAll_read (label : ℕ → Term σ) (ports : List (Port σ))
    (entry : Match (Term σ) (Work σ)) :
    (extendAll label .read ports entry).read = entry.read ++ ports.map Prod.snd ∧
      (extendAll label .read ports entry).taken = entry.taken := by
  induction ports generalizing entry with
  | nil => simp [extendAll]
  | cons q tail ih =>
    rw [extendAll]
    obtain ⟨read, taken⟩ := ih (extend label .read entry q)
    refine ⟨?_, taken⟩
    rw [read]
    simp [extend, Match.select, List.append_assoc]

theorem extendAll_no_outputs (label : ℕ → Term σ) (role : Role) (ports : List (Port σ))
    (entry : Match (Term σ) (Work σ)) :
    (extendAll label role ports entry).seen = entry.seen ∧ (extendAll label role ports entry).made = entry.made := by
  induction ports generalizing entry with
  | nil => exact ⟨rfl, rfl⟩
  | cons q tail ih =>
    obtain ⟨seen, made⟩ := ih (extend label role entry q)
    rw [extendAll, seen, made]
    cases role <;> exact ⟨rfl, rfl⟩

inductive Ready (world : LiveWorld σ) (role : Role) :
    Match (Term σ) (Work σ) → List (Port σ) → Prop where
  | nil (entry) : Ready world role entry []
  | cons {entry : Match (Term σ) (Work σ)} {port : Port σ} {later : List (Port σ)}
      (live : port.2 ∈ world.live) (usable : role.allows entry port.2 = true)
      (tail : Ready world role (extend world.state.label role entry port) later) :
      Ready world role entry (port :: later)

theorem Ready.takes (world : LiveWorld σ) (entry : Match (Term σ) (Work σ)) (ports : List (Port σ))
    (live : ∀ port ∈ ports, port.2 ∈ world.live)
    (distinct : (entry.taken ++ ports.map Prod.snd).Nodup)
    (apart : ∀ port ∈ ports, port.2 ∉ entry.read) : Ready world .take entry ports := by
  induction ports generalizing entry with
  | nil => exact .nil _
  | cons first later ih =>
    have outside : first.2 ∉ entry.taken := by
      have separate := (List.nodup_append.mp distinct).2.2
      intro inTake
      exact separate _ inTake _ (List.mem_map.mpr ⟨first, List.mem_cons_self, rfl⟩) rfl
    have readable := apart first List.mem_cons_self
    refine .cons (live first List.mem_cons_self) (by simp [Role.allows, outside, readable]) ?_
    exact ih _ (fun port member => live port (List.mem_cons_of_mem _ member))
      (by simpa [extend, Match.select, List.append_assoc] using distinct)
      (fun port member => apart port (List.mem_cons_of_mem _ member))

theorem Ready.reads (world : LiveWorld σ) (entry : Match (Term σ) (Work σ)) (ports : List (Port σ))
    (live : ∀ port ∈ ports, port.2 ∈ world.live)
    (apart : ∀ port ∈ ports, port.2 ∉ entry.taken) : Ready world .read entry ports := by
  induction ports generalizing entry with
  | nil => exact .nil _
  | cons first later ih =>
    refine .cons (live first List.mem_cons_self) (by simp [Role.allows, apart first List.mem_cons_self]) ?_
    exact ih _ (fun port member => live port (List.mem_cons_of_mem _ member))
      (fun port member => apart port (List.mem_cons_of_mem _ member))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem execute_matches (base : Equations σ) (world : LiveWorld σ) (role : Role)
    (fits : world.live.length < 2 ^ 64) (later : Code σ) (start : ℕ)
    {state : Frame σ} (resident : state.store = storeOf world) {ports : List (Port σ)}
    (ready : Ready world role (state.levels start) ports) :
    ∃ next : Frame σ, next.store = state.store ∧ SameFuel state next ∧
      next.levels (start + ports.length) = extendAll world.state.label role ports (state.levels start) ∧
      SymbolicExecution.execute base state (emit world.live role start ports later) =
        SymbolicExecution.execute base next later := by
  generalize starts : state.levels start = entry at ready
  induction ready generalizing state start with
  | nil =>
    exact ⟨state, rfl, ⟨rfl, rfl⟩, starts, rfl⟩
  | @cons entry port rest live usable subsequent ih =>
    let ordinal := world.live.idxOf port.2
    have bound : ordinal < world.live.length := List.idxOf_lt_length_iff.mpr live
    have word : (BitVec.ofNat 64 ordinal).toNat = ordinal := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bound.trans fits)]
    have indexed : world.live[ordinal]? = some port.2 := by
      rw [List.getElem?_eq_getElem bound]
      exact congrArg some (List.getElem_idxOf bound)
    let seeded := state.write indexReg (.ofNat 64 ordinal)
    let extended := extend world.state.label role entry port
    let advanced := (seeded.setLevel (start + 1) extended).write passReg 1
    have actual : seeded.store.occurrences[(seeded.machine.registers indexReg).toNat]? =
        some (port.2, world.state.label port.2) := by
      change state.store.occurrences[(Function.update state.machine.registers indexReg (.ofNat 64 ordinal) indexReg).toNat]? = _
      rw [Function.update_self, word, resident]
      simp only [storeOf, List.getElem?_map, indexed, Option.map_some]
    have entered : SymbolicExecution.execute base state
        (.instruction (.immediate .u64 indexReg (.ofNat 64 ordinal))) = .continuing seeded := rfl
    have chosen : SymbolicExecution.propose role port.1 (seeded.levels start) (port.2, world.state.label port.2) = some extended := by
      change SymbolicExecution.propose role port.1 (state.levels start) (port.2, world.state.label port.2) = _
      rw [starts, SymbolicExecution.propose, if_pos usable]
      rfl
    have tried : SymbolicExecution.execute base seeded (.instruction (.transform (.premise role port.1 start indexReg passReg))) =
        .continuing advanced := by
      simp only [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, actual, profile, chosen]
      exact rfl
    have active : advanced.levels (start + 1) = extended := by
      simp [advanced, StoreInstructions.State.write, StoreInstructions.State.setLevel]
    have passed : advanced.machine.registers passReg = 1 := by simp [advanced, StoreInstructions.State.write, P1WordExecution.State.write]
    obtain ⟨next, sameStore, sameFuel, readyLevel, code⟩ := ih (state := advanced) (start := start + 1) resident active
    refine ⟨next, sameStore, SameFuel.trans (show SameFuel state advanced from ⟨rfl, rfl⟩) sameFuel, ?_, ?_⟩
    · rw [show start + (port :: rest).length = start + 1 + rest.length by simp; omega, readyLevel]
      rfl
    · simp only [emit, executeWith_seq]
      change (SymbolicExecution.execute base state (.instruction (.immediate .u64 indexReg (.ofNat 64 ordinal)))).thenContinue
        (fun seed => (SymbolicExecution.execute base seed (.instruction (.transform (.premise role port.1 start indexReg passReg)))).thenContinue
          (fun updated => SymbolicExecution.execute base updated (.branch passReg
            (emit world.live role (start + 1) rest later) (.ret .refused passReg)))) = _
      rw [entered, Flow.thenContinue, tried, Flow.thenContinue]
      simpa only [executeWith, passed, if_true] using code

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPortCode
