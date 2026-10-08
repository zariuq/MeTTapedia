import Mettapedia.GSLT.LanguageDef.NativeOpsCScalarRead

/-!
# Source-body identity scans and independent list membership

The retained loop tests its UInt32 position and current Boolean before each
read. Its actual assignment evaluates the supplied array and identity operand.
The specification is membership in the remaining initialized list. Operand
contracts supply only immutable typed reads, not the scan's conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.IdentityScan

open ScalarRead

variable {Ptr : Type} [DecidableEq Ptr]

def counter : Name := "j".toList
def flag : Name := "present".toList

def locals (base : Environment Ptr) (index : UInt32) (seen : Bool) : Environment Ptr :=
  fun name => if name = counter then some (.unsigned index)
    else if name = flag then some (.boolean seen) else base name

omit [DecidableEq Ptr] in
theorem locals_are_scoped_updates (base : Environment Ptr) (index : UInt32) (seen : Bool) :
    locals base index seen = Function.update
      (Function.update base flag (some (.boolean seen))) counter (some (.unsigned index)) := by
  funext name
  by_cases isCounter : name = counter
  · subst name
    simp [locals]
  · by_cases isFlag : name = flag
    · subst name
      simp [locals, counter, flag]
    · simp [locals, isCounter, isFlag]

omit [DecidableEq Ptr] in
theorem update_flag (base : Environment Ptr) (index : UInt32) (seen value : Bool) :
    Function.update (locals base index seen) flag (some (.boolean value)) =
      locals base index value := by
  funext name
  by_cases isCounter : name = counter
  · subst name
    simp [locals, flag, counter]
  · by_cases isFlag : name = flag
    · subst name
      simp [locals, flag, counter]
    · simp [locals, isCounter, isFlag]

omit [DecidableEq Ptr] in
theorem update_counter (base : Environment Ptr) (index value : UInt32) (seen : Bool) :
    Function.update (locals base index seen) counter (some (.unsigned value)) =
      locals base value seen := by
  funext name
  by_cases isCounter : name = counter
  · subst name
    simp [locals]
  · simp [locals, isCounter]

def condition (limit : CExpr) : CExpr :=
  .binary .and (.binary .lt (.identifier counter) limit) (.unary .not (.identifier flag))

def step : CExpr := .postIncrement (.identifier counter)

def body (array needle : CExpr) : List CStatement :=
  [.assign (.identifier flag)
    (.binary .eq (.index array (.identifier counter)) needle)]

structure Operands (base : Environment Ptr) (fields : FieldReader Ptr)
    (array limit needle : CExpr) (values : List (Option Ptr)) (bound : UInt32)
    (target : Option Ptr) : Prop where
  arrayRead : ∀ index seen, expression (locals base index seen) fields array =
    some (.identities values)
  boundRead : ∀ index seen, expression (locals base index seen) fields limit =
    some (.unsigned bound)
  targetRead : ∀ index seen, expression (locals base index seen) fields needle =
    some (.identity target)

theorem condition_read {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} {values : List (Option Ptr)} {bound : UInt32}
    {target : Option Ptr} (operands : Operands base fields array limit needle values bound target)
    (index : UInt32) (seen : Bool) :
    (expression (locals base index seen) fields (condition limit)).bind truth? =
      some (decide (index < bound) && !seen) := by
  by_cases live : index < bound <;>
    simp [condition, expression, numericBinary, operands.boundRead, locals, truth?,
      flag, counter, live]

theorem body_read {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} {values : List (Option Ptr)} {bound : UInt32}
    {target entry : Option Ptr}
    (operands : Operands base fields array limit needle values bound target)
    (index : UInt32) (seen : Bool) (loaded : values[index.toNat]? = some entry) :
    statements fields (locals base index seen) (body array needle) =
      some (locals base index (decide (entry = target))) := by
  simpa [body, statements, assignment, expression, operands.arrayRead, operands.targetRead,
    locals, flag, counter, loaded, equal?, assignValue?, truth?] using
    congrArg some (update_flag base index seen (decide (entry = target)))

omit [DecidableEq Ptr] in
theorem increment_read (base : Environment Ptr) (index : UInt32) (seen : Bool) :
    increment (locals base index seen) step = some (locals base (index + 1) seen) := by
  change some (Function.update (locals base index seen) counter
    (some (.unsigned (index + 1)))) = _
  exact congrArg some (update_counter base index (index + 1) seen)

/-- Exact UInt32 progression is derived from the remaining input extent, not
assumed for an unconditional increment. The loop's stopping index is retained. -/
theorem run_refines_initialized {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} {bound : UInt32} {target : Option Ptr}
    (prior remaining spare : List (Option Ptr))
    (operands : Operands base fields array limit needle ((prior ++ remaining) ++ spare) bound target)
    (index : UInt32) (seen : Bool) (fuel : Nat)
    (position : index.toNat = prior.length)
    (extent : bound.toNat = (prior ++ remaining).length)
    (enough : remaining.length ≤ fuel) :
    ∃ stopped, run fields (condition limit) step (body array needle) fuel
      (locals base index seen) =
      .finished (some (locals base stopped (decide (seen = true ∨ target ∈ remaining)))) := by
  induction remaining generalizing prior index seen fuel with
  | nil =>
    have halted : ¬ index < bound := by
      rw [UInt32.lt_iff_toNat_lt]
      simpa [position] using extent.le
    refine ⟨index, ?_⟩
    rw [run.eq_def, condition_read operands, decide_eq_false halted]
    cases seen <;> simp
  | cons entry rest ih =>
    cases seen with
    | true =>
      refine ⟨index, ?_⟩
      rw [run.eq_def, condition_read operands]
      simp
    | false =>
      have live : index < bound := by
        rw [UInt32.lt_iff_toNat_lt]
        simp only [List.length_append, List.length_cons] at extent
        omega
      have exactIncrement : (index + 1).toNat = index.toNat + 1 := by
        rw [UInt32.toNat_add]
        apply Nat.mod_eq_of_lt
        have upper := bound.toNat_lt
        have before := UInt32.lt_iff_toNat_lt.mp live
        change index.toNat + 1 < 2 ^ 32
        omega
      have loaded : ((prior ++ entry :: rest) ++ spare)[index.toNat]? = some entry := by
        rw [List.append_assoc, position, List.getElem?_append_right (Nat.le_refl _)]
        simp
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
        have followingOperands : Operands base fields array limit needle
            (((prior ++ [entry]) ++ rest) ++ spare) bound target := by
          simpa only [List.append_assoc, List.singleton_append] using operands
        have nextPosition : (index + 1).toNat = (prior ++ [entry]).length := by
          simp [exactIncrement, position]
        have nextExtent : bound.toNat = ((prior ++ [entry]) ++ rest).length := by
          simpa [List.append_assoc] using extent
        obtain ⟨stopped, following⟩ := ih (prior ++ [entry]) followingOperands
          (index + 1) (decide (entry = target)) fuel nextPosition nextExtent (by simpa using enough)
        refine ⟨stopped, ?_⟩
        rw [run.eq_def, condition_read operands, decide_eq_true live]
        simp only [Bool.not_false, Bool.and_true]
        rw [body_read operands index false loaded]
        dsimp only
        rw [increment_read]
        dsimp only
        simpa [eq_comm] using following

theorem run_refines_remaining {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} {bound : UInt32} {target : Option Ptr}
    (prior remaining : List (Option Ptr))
    (operands : Operands base fields array limit needle (prior ++ remaining) bound target)
    (index : UInt32) (seen : Bool) (fuel : Nat)
    (position : index.toNat = prior.length)
    (extent : bound.toNat = (prior ++ remaining).length)
    (enough : remaining.length ≤ fuel) :
    ∃ stopped, run fields (condition limit) step (body array needle) fuel
      (locals base index seen) =
      .finished (some (locals base stopped (decide (seen = true ∨ target ∈ remaining)))) := by
  exact run_refines_initialized prior remaining [] (by simpa using operands)
    index seen fuel position extent enough

def scanStatement (array limit needle : CExpr) : CStatement :=
  .forLoop ⟨"uint32_t".toList, 0⟩ counter (.unsignedInteger 0)
    (condition limit) step (body array needle)

/-- The previous counter binding survives its local declaration. The observed
Boolean is exactly the old flag or membership, including empty arrays. -/
theorem counted_scan_refines_initialized {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} {initialized spare : List (Option Ptr)} {bound : UInt32}
    {target : Option Ptr}
    (operands : Operands base fields array limit needle (initialized ++ spare) bound target)
    (exactExtent : bound.toNat = initialized.length) (savedCounter : UInt32) (seen : Bool) :
    countedLoop fields initialized.length (locals base savedCounter seen)
      (scanStatement array limit needle) = some (.finished (some
        (locals base savedCounter (decide (seen = true ∨ target ∈ initialized))))) := by
  have initialOperands : Operands base fields array limit needle
      (([] ++ initialized) ++ spare) bound target :=
    operands
  obtain ⟨stopped, completed⟩ := run_refines_initialized [] initialized spare initialOperands
    0 seen initialized.length rfl exactExtent (Nat.le_refl _)
  change some (restore (run fields (condition limit) step (body array needle)
    initialized.length (Function.update (locals base savedCounter seen) counter
      (some (.unsigned 0)))) counter (some (.unsigned savedCounter))) = _
  rw [update_counter, completed]
  change some (Result.finished (some (Function.update
    (locals base stopped (decide (seen = true ∨ target ∈ initialized))) counter
      (some (.unsigned savedCounter))))) = _
  rw [update_counter]

/-- The local counter may have no outer binding, or an outer value of another
type. Its declaration restores that exact binding; only the supplied Boolean
flag is changed by the initialized scan. -/
theorem counted_scan_refines_outer_scope {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} {initialized spare : List (Option Ptr)} {bound : UInt32}
    {target : Option Ptr}
    (operands : Operands base fields array limit needle (initialized ++ spare) bound target)
    (exactExtent : bound.toNat = initialized.length) (seen : Bool) :
    countedLoop fields initialized.length (Function.update base flag (some (.boolean seen)))
      (scanStatement array limit needle) = some (.finished (some
        (Function.update base flag (some (.boolean
          (decide (seen = true ∨ target ∈ initialized))))))) := by
  obtain ⟨stopped, completed⟩ := run_refines_initialized [] initialized spare
    (by simpa using operands) 0 seen initialized.length rfl exactExtent (Nat.le_refl _)
  change some (restore (run fields (condition limit) step (body array needle)
    initialized.length (Function.update (Function.update base flag (some (.boolean seen)))
      counter (some (.unsigned 0)))) counter
      ((Function.update base flag (some (.boolean seen))) counter)) = _
  rw [← locals_are_scoped_updates, completed]
  change some (Result.finished (some (Function.update
    (locals base stopped (decide (seen = true ∨ target ∈ initialized))) counter
      ((Function.update base flag (some (.boolean seen))) counter)))) = _
  rw [Function.update_of_ne (by decide : counter ≠ flag), locals_are_scoped_updates,
    Function.update_idem]
  rw [Function.update_comm (by decide : flag ≠ counter), Function.update_eq_self]

theorem counted_scan_refines_membership {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} {values : List (Option Ptr)} {bound : UInt32}
    {target : Option Ptr} (operands : Operands base fields array limit needle values bound target)
    (exactExtent : bound.toNat = values.length) (savedCounter : UInt32) (seen : Bool) :
    countedLoop fields values.length (locals base savedCounter seen)
      (scanStatement array limit needle) = some (.finished (some
        (locals base savedCounter (decide (seen = true ∨ target ∈ values))))) := by
  exact counted_scan_refines_initialized (spare := []) (by simpa using operands)
    exactExtent savedCounter seen

/-- Array capacity is not the initialized identity extent. The scanner keeps
the complete slot provider while observing only the UInt32-counted prefix. -/
theorem counted_scan_refines_pointer_slots {base : Environment Ptr} {fields : FieldReader Ptr}
    {array limit needle : CExpr} (slots : PostIndex.Array32 Ptr) (target : Ptr)
    (operands : Operands base fields array limit needle (slots.slots.map some)
      slots.count (some target))
    (liveCount : slots.count.toNat ≤ slots.slots.length) (savedCounter : UInt32) (seen : Bool) :
    countedLoop fields slots.count.toNat (locals base savedCounter seen)
      (scanStatement array limit needle) = some (.finished (some
        (locals base savedCounter (decide (seen = true ∨ target ∈ slots.active))))) := by
  let initialized := (slots.slots.take slots.count.toNat).map some
  let spare := (slots.slots.drop slots.count.toNat).map some
  have splitSlots : initialized ++ spare = slots.slots.map some := by
    dsimp [initialized, spare]
    rw [← List.map_append, List.take_append_drop]
  have reads : Operands base fields array limit needle (initialized ++ spare)
      slots.count (some target) := by
    rw [splitSlots]
    exact operands
  have exactCount : slots.count.toNat = initialized.length := by
    simp [initialized, List.length_take, Nat.min_eq_left liveCount]
  have membership : some target ∈ initialized ↔ target ∈ slots.active := by
    change some target ∈ (slots.slots.take slots.count.toNat).map some ↔
      target ∈ slots.slots.take slots.count.toNat
    constructor
    · intro included
      obtain ⟨value, included, equal⟩ := List.mem_map.mp included
      exact (Option.some.inj equal) ▸ included
    · intro included
      exact List.mem_map.mpr ⟨target, included, rfl⟩
  have result := counted_scan_refines_initialized reads exactCount savedCounter seen
  rw [← exactCount] at result
  simpa only [membership] using result

#print axioms update_flag
#print axioms locals_are_scoped_updates
#print axioms counted_scan_refines_outer_scope
#print axioms update_counter
#print axioms condition_read
#print axioms body_read
#print axioms increment_read
#print axioms run_refines_initialized
#print axioms run_refines_remaining
#print axioms counted_scan_refines_initialized
#print axioms counted_scan_refines_membership
#print axioms counted_scan_refines_pointer_slots

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.IdentityScan
