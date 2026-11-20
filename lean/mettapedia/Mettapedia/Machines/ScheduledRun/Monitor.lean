import Mettapedia.Machines.ScheduledRun.PeriodTracker

/-!
# A prefix evaluator for the runner's period-reset visit record

The probe is made before learning the current successor count. Afterwards the
visit is retained if the period stays unchanged, or the record is cleared if
it grows. This is the shared runner's visit/expand/learn order, not a different
learn-before-visit algorithm. Evaluation after the first claim is only a total
prefix model; a runner may stop at that first claim.

Finite sets abstract the hash table. Natural periods and logical step turns
abstract bounded arithmetic, budgets, allocation failure and mutable decoders.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

structure VisitRecord (S : Type u) where
  period : Nat
  seen : Finset (S × Nat)

def initialRecord : VisitRecord S := ⟨1, ∅⟩

variable [DecidableEq S]

def recordStep (next : S → List S) (mode : Mode) (turn : Nat) (observation : Option S)
    (record : VisitRecord S) : VisitRecord S :=
  match observation with
  | none => record
  | some state =>
    let period := updatePeriod mode record.period (next state).length
    if period = record.period then ⟨record.period, insert (state, turn % record.period) record.seen⟩
    else ⟨period, ∅⟩

def recordPrefix (next : S → List S) (mode : Mode) (trace : Nat → Option S) : Nat → VisitRecord S
  | 0 => initialRecord
  | turn + 1 => recordStep next mode turn (trace turn) (recordPrefix next mode trace turn)

def claimsAt (next : S → List S) (mode : Mode) (trace : Nat → Option S) (turn : Nat) : Bool :=
  match trace turn with
  | none => false
  | some state => decide ((state, turn % (recordPrefix next mode trace turn).period) ∈
      (recordPrefix next mode trace turn).seen)

theorem updatePeriod_zero (mode : Mode) (period : Nat) : updatePeriod mode period 0 = period := by
  cases mode <;> rfl

theorem recordStep_period (next : S → List S) (mode : Mode) (turn : Nat) (observation : Option S)
    (record : VisitRecord S) : (recordStep next mode turn observation record).period =
      updatePeriod mode record.period (observedArity next observation) := by
  cases observation with
  | none => exact (updatePeriod_zero mode record.period).symm
  | some state =>
    by_cases same : updatePeriod mode record.period (next state).length = record.period
    · simp [recordStep, same, observedArity]
    · simp [recordStep, same, observedArity]

theorem recordPrefix_period (next : S → List S) (mode : Mode) (trace : Nat → Option S) (turn : Nat) :
    (recordPrefix next mode trace turn).period = prefixPeriod next mode trace turn := by
  induction turn with
  | zero => rfl
  | succ turn ih => rw [recordPrefix, recordStep_period, ih]; rfl

theorem recordPrefix_witness (next : S → List S) (mode : Mode) (trace : Nat → Option S) :
    ∀ turn key, key ∈ (recordPrefix next mode trace turn).seen →
      ∃ earlier, earlier < turn ∧ trace earlier = some key.1 ∧
        earlier % (recordPrefix next mode trace turn).period = key.2 := by
  intro turn
  induction turn with
  | zero => intro key member; exact False.elim (Finset.notMem_empty key member)
  | succ turn ih =>
    intro key member
    cases observed : trace turn with
    | none =>
      have same : recordPrefix next mode trace (turn + 1) = recordPrefix next mode trace turn := by
        simp [recordPrefix, observed, recordStep]
      rw [same] at member ⊢
      obtain ⟨earlier, before, present, phase⟩ := ih key member
      exact ⟨earlier, by omega, present, phase⟩
    | some state =>
      by_cases unchanged : updatePeriod mode (recordPrefix next mode trace turn).period (next state).length =
          (recordPrefix next mode trace turn).period
      · have same : recordPrefix next mode trace (turn + 1) =
            ⟨(recordPrefix next mode trace turn).period,
              insert (state, turn % (recordPrefix next mode trace turn).period)
                (recordPrefix next mode trace turn).seen⟩ := by
          simp [recordPrefix, observed, recordStep, unchanged]
        rw [same] at member ⊢
        rcases Finset.mem_insert.mp member with rfl | old
        · exact ⟨turn, Nat.lt_succ_self _, observed, rfl⟩
        · obtain ⟨earlier, before, present, phase⟩ := ih key old
          exact ⟨earlier, by omega, present, phase⟩
      · have empty : (recordPrefix next mode trace (turn + 1)).seen = ∅ := by
          simp [recordPrefix, observed, recordStep, unchanged]
        rw [empty] at member
        exact False.elim (Finset.notMem_empty key member)

theorem claimsAt_iff (next : S → List S) (mode : Mode) (trace : Nat → Option S) (turn : Nat) :
    claimsAt next mode trace turn = true ↔
      ∃ state, trace turn = some state ∧
        (state, turn % (recordPrefix next mode trace turn).period) ∈ (recordPrefix next mode trace turn).seen := by
  cases observed : trace turn <;> simp [claimsAt, observed]

theorem claimsAt_sound (next : S → List S) (mode : Mode) (initial : S) (turn : Nat)
    (claim : claimsAt next mode (run next mode.schedule initial) turn = true) :
    Nonterminating next mode.schedule initial := by
  obtain ⟨state, current, member⟩ := (claimsAt_iff next mode _ turn).mp claim
  obtain ⟨earlier, order, previous, phase⟩ := recordPrefix_witness next mode _ turn _ member
  cases mode with
  | canonical => exact (canonical_return_periodic next initial order state previous current).1
  | rotating =>
    refine (return_mod_common_period next initial order state previous current phase ?_).1
    intro before _ upper value present
    rw [recordPrefix_period]
    exact arity_dvd_prefixPeriod next _ upper present
      (nonterminal_before_present next rotating initial upper present current)

theorem ended_never_reports (next : S → List S) (mode : Mode) (initial : S)
    {ending : Nat} (ended : EndsAt next mode.schedule initial ending) (turn : Nat) :
    claimsAt next mode (run next mode.schedule initial) turn = false := by
  cases result : claimsAt next mode (run next mode.schedule initial) turn with
  | false => rfl
  | true => exact False.elim (ended_not_nonterminating next mode.schedule initial ended
      (claimsAt_sound next mode initial turn result))

end Mettapedia.Machines.ScheduledRun
