import Mettapedia.GSLT.Core.WriterGSLT
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Generic self-modelling of reserves

A self-model of budgets is a *reading* of the `spendLift` writer, not a
second evaluator and not a Cost LanguageDef.

The subject fibre is first projection (`π`).  The ledger fibre is second
projection.  Neither recovers the pair:

* observational bisimilarity ignores the ledger (the reading is not a
  GSLT observation);
* the ledger projection is not injective (the reading does not recover
  the subject).

Inspection of one fibre is therefore weaker than authority over the
writer.  That is the staging law.  Token flavours are coordinates of the
ledger; a step that spends one flavour need not spend another (no
arbitrage).

A round trip that returns the same subject while the ledger strictly
grows is a spend cycle.  It is *uninformative* when a declared policy
of the ledger is unchanged, and *informative* when that policy flips.
The negative control is the same cycle under a policy that does flip.

Separation is a step that leaves a declared home invariant; formation
is a step that restores it.  A coarser observer that identifies the
home with its complement erases that distinction: the readout does not
descend.

The content of a goal or invariant may be written in any hosted language
(GSLT-IL as IR; DTT, HOTG, set theory, HOL as vocabularies).  This
module is the reading, independent of that vocabulary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReservesSelfModel

open Mettapedia.GSLT
open Mettapedia.GSLT.WriterGSLT
open Mettapedia.GSLT.IndexedOperational

universe u v

/-- Two token flavours.  The ledger is a pair of additive counters, not
the multiplicative `Pi` monoid on `Nat`. -/
@[ext]
structure Reserves where
  flavour : Fin 2 → Nat

instance : Monoid Reserves where
  mul a b := ⟨fun i => a.flavour i + b.flavour i⟩
  mul_assoc := by
    intro a b c
    ext i
    exact Nat.add_assoc _ _ _
  one := ⟨fun _ => 0⟩
  one_mul := by
    intro a
    ext i
    exact Nat.zero_add _
  mul_one := by
    intro a
    ext i
    exact Nat.add_zero _

def flavour0 (r : Reserves) : Nat := r.flavour 0
def flavour1 (r : Reserves) : Nat := r.flavour 1

def e0 : Reserves := ⟨fun i => if i = 0 then 1 else 0⟩
def e1 : Reserves := ⟨fun i => if i = 1 then 1 else 0⟩

@[simp] theorem e0_flavour0 : flavour0 e0 = 1 := rfl
@[simp] theorem e0_flavour1 : flavour1 e0 = 0 := rfl
@[simp] theorem e1_flavour0 : flavour0 e1 = 0 := rfl
@[simp] theorem e1_flavour1 : flavour1 e1 = 1 := rfl
@[simp] theorem one_flavour0 : flavour0 (1 : Reserves) = 0 := rfl
@[simp] theorem one_flavour1 : flavour1 (1 : Reserves) = 0 := rfl

theorem mul_flavour0 (a b : Reserves) :
    flavour0 (a * b) = flavour0 a + flavour0 b :=
  rfl

theorem mul_flavour1 (a b : Reserves) :
    flavour1 (a * b) = flavour1 a + flavour1 b :=
  rfl

/-- Signed per-flavour distance from a held goal.  Positive means the
spent coordinate has passed the goal. -/
def deficit (spent goal : Reserves) (i : Fin 2) : Int :=
  (spent.flavour i : Int) - (goal.flavour i : Int)

/-! ## Subject theory: a two-cycle -/

def pingPong : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source ≠ target
  rewrites_resp_left := by
    intro source source' target equivalent step
    subst equivalent
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    subst equivalent
    exact step

theorem pingPong_out : pingPong.Step false true :=
  Bool.false_ne_true

theorem pingPong_back : pingPong.Step true false :=
  Bool.false_ne_true.symm

/-- Every authentic step spends one unit of flavour 0 and nothing of
flavour 1. -/
def flavourTick : pingPong.StepSpend Reserves where
  graded := fun source target value =>
    pingPong.Step source target ∧ value = e0
  sound := And.left
  resp_left := by
    intro source source' target value equivalent ⟨step, valueEq⟩
    subst equivalent
    exact ⟨target, ⟨step, valueEq⟩, rfl⟩
  resp_right := by
    intro source target target' value ⟨step, valueEq⟩ equivalent
    subst equivalent
    exact ⟨step, valueEq⟩

theorem flavourTick_total : flavourTick.Total := by
  intro source target step
  exact ⟨e0, step, rfl⟩

def writer : GSLT := pingPong.spendLift flavourTick

/-! ## Readings -/

def subject (state : Bool × Reserves) : Bool := state.1
def ledger (state : Bool × Reserves) : Reserves := state.2

theorem reading_eq_ledger (state : Bool × Reserves) :
    ledger state = state.2 :=
  rfl

theorem erase_eq_subject (state : Bool × Reserves) :
    (eraseMorphism flavourTick flavourTick_total).toFun state = subject state :=
  rfl

/-- The ledger is the coordinate `π` forgets.  Distinct spends of one
subject are one bisimilarity class. -/
theorem reserves_not_observational (term : Bool) (first second : Reserves) :
    writer.Bisimilar (term, first) (term, second) :=
  history_not_observational flavourTick flavourTick_total term first second

/-- The ledger projection does not recover the subject. -/
theorem ledger_projection_not_injective :
    ∃ a b : Bool × Reserves,
      subject a ≠ subject b ∧ ledger a = ledger b :=
  ⟨(false, 1), (true, 1), Bool.false_ne_true, rfl⟩

/-- `η` lands on the zero spend.  A genuine tick is therefore not an
`η`-image of a base step. -/
theorem embed_does_not_record_spend :
    ¬ writer.Step
        ((embedMorphism flavourTick flavourTick_total).toFun false)
        ((embedMorphism flavourTick flavourTick_total).toFun true) := by
  rintro ⟨grade, ⟨_, gradeEq⟩, accumulated⟩
  subst gradeEq
  have h0 : flavour0 ((1 : Reserves) * e0) = flavour0 (1 : Reserves) :=
    congrArg flavour0 accumulated.symm
  have h1 : flavour0 ((1 : Reserves) * e0) = 1 := by
    rw [mul_flavour0, one_flavour0, e0_flavour0]
  exact Nat.succ_ne_zero 0 (h1.symm.trans h0)

theorem embed_section_of_erase :
    GSLT.Morphism.comp (eraseMorphism flavourTick flavourTick_total)
        (embedMorphism flavourTick flavourTick_total) =
      GSLT.Morphism.id pingPong :=
  erase_comp_embed flavourTick flavourTick_total

theorem embed_then_erase_forgets_spend :
    GSLT.Morphism.comp (embedMorphism flavourTick flavourTick_total)
        (eraseMorphism flavourTick flavourTick_total) ≠
      GSLT.Morphism.id writer := by
  intro equal
  have hleft :
      (GSLT.Morphism.comp (embedMorphism flavourTick flavourTick_total)
          (eraseMorphism flavourTick flavourTick_total)).toFun (false, e0) =
        (false, (1 : Reserves)) :=
    rfl
  have h := congrFun (congrArg GSLT.Morphism.toFun equal) (false, e0)
  rw [hleft] at h
  injection h with _ hsnd
  have hfl := congrArg flavour0 hsnd
  exact Nat.succ_ne_zero 0 (e0_flavour0.symm.trans hfl.symm)

/-! ## Ledger fibre and the observer translation -/

def ledgerTheory : GSLT where
  Term := Reserves
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    ∃ (s t : Bool), pingPong.Step s t ∧ target = source * e0
  rewrites_resp_left := by
    intro source source' target equivalent step
    subst equivalent
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    subst equivalent
    exact step

/-- Observer route: read the ledger coordinate.  This is the GSLT-IL
`via` of observer kind, compiled to an operational translation. -/
def ledgerProjection : OperationalTranslation writer ledgerTheory where
  mapTerm := Prod.snd
  mapEquiv := by
    intro left right equivalent
    exact equivalent.2
  mapStep := by
    intro source target ⟨grade, ⟨step, gradeEq⟩, accumulated⟩
    subst gradeEq
    exact ⟨source.1, target.1, step, accumulated⟩

theorem ledgerProjection_is_the_reading (state : Bool × Reserves) :
    ledgerProjection.mapTerm state = ledger state :=
  rfl

/-! ## Value conflict: flavour 1 is silent -/

theorem tick_from (start : Bool × Reserves) {stop : Bool}
    (hstep : pingPong.Step start.1 stop) :
    writer.Step start (stop, start.2 * e0) :=
  ⟨e0, ⟨hstep, rfl⟩, rfl⟩

theorem flavour1_silent (start : Bool × Reserves) {stop : Bool}
    (_hstep : pingPong.Step start.1 stop) :
    flavour1 (start.2 * e0) = flavour1 start.2 := by
  rw [mul_flavour1, e0_flavour1, Nat.add_zero]

theorem no_arbitrage_on_a_tick (start : Bool × Reserves) {stop : Bool}
    (hstep : pingPong.Step start.1 stop) :
    flavour0 (start.2 * e0) = flavour0 start.2 + 1 ∧
      flavour1 (start.2 * e0) = flavour1 start.2 :=
  ⟨by simp [mul_flavour0], flavour1_silent start hstep⟩

theorem deficit_flavour1_unchanged (spent goal : Reserves) :
    deficit (spent * e0) goal 1 = deficit spent goal 1 := by
  unfold deficit
  have h : (spent * e0).flavour 1 = spent.flavour 1 := by
    change flavour1 (spent * e0) = flavour1 spent
    rw [mul_flavour1, e0_flavour1, Nat.add_zero]
  rw [h]

/-! ## Separation, formation, and erased distinction -/

def home (t : Bool) : Prop := t = false

def breaksHome {source target : Bool} (_step : pingPong.Step source target) :
    Prop :=
  home source ∧ ¬ home target

def restoresHome {source target : Bool} (_step : pingPong.Step source target) :
    Prop :=
  ¬ home source ∧ home target

theorem out_is_separation : breaksHome pingPong_out :=
  ⟨rfl, fun h => Bool.false_ne_true h.symm⟩

theorem back_is_formation : restoresHome pingPong_back :=
  ⟨fun h => Bool.false_ne_true h.symm, rfl⟩

/-- A coarser observer that identifies every subject erases the home
distinction, so the separation readout does not descend. -/
def coarse : GSLT where
  Term := Unit
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

def forgetSubject : Bool → Unit := fun _ => ()

theorem distinction_erased :
    forgetSubject false = forgetSubject true :=
  rfl

theorem separation_does_not_descend :
    ¬ ∃ source target : Unit, source ≠ target := by
  intro ⟨source, target, hne⟩
  cases source
  cases target
  exact hne rfl

/-! ## Informative vs uninformative spend cycles -/

def stuckPolicy (_ : Reserves) : Bool := true

def budgetPolicy (r : Reserves) : Bool := decide (flavour0 r < 2)

structure RoundTrip (start mid target : Bool × Reserves) : Prop where
  out : writer.Step start mid
  back : writer.Step mid target
  home : target.1 = start.1

def spendsFlavour0 (start target : Bool × Reserves) : Prop :=
  flavour0 start.2 < flavour0 target.2

def uninformative (policy : Reserves → Bool)
    (start target : Bool × Reserves) : Prop :=
  policy start.2 = policy target.2

def UninformativeSpend (policy : Reserves → Bool)
    (start mid target : Bool × Reserves) : Prop :=
  RoundTrip start mid target ∧
    spendsFlavour0 start target ∧
    uninformative policy start target

def zero : Reserves := 1

theorem zero_flavour0 : flavour0 zero = 0 := rfl

theorem two_ticks_flavour0 (r : Reserves) :
    flavour0 (r * e0 * e0) = flavour0 r + 2 := by
  rw [mul_flavour0, mul_flavour0, e0_flavour0, Nat.add_assoc]

theorem round_trip_from_zero :
    RoundTrip (false, zero) (true, zero * e0) (false, zero * e0 * e0) where
  out := tick_from (false, zero) pingPong_out
  back := tick_from (true, zero * e0) pingPong_back
  home := rfl

theorem round_trip_spends :
    spendsFlavour0 (false, zero) (false, zero * e0 * e0) := by
  unfold spendsFlavour0
  rw [two_ticks_flavour0, zero_flavour0]
  exact Nat.succ_pos 1

theorem stuck_round_trip_uninformative :
    UninformativeSpend stuckPolicy
      (false, zero) (true, zero * e0) (false, zero * e0 * e0) :=
  ⟨round_trip_from_zero, round_trip_spends, rfl⟩

theorem budget_flips_on_round_trip :
    ¬ uninformative budgetPolicy
        (false, zero) (false, zero * e0 * e0) := by
  intro h
  unfold uninformative budgetPolicy at h
  rw [two_ticks_flavour0, zero_flavour0] at h
  have htrue : decide ((0 : Nat) < 2) = true := rfl
  have hfalse : decide ((2 : Nat) < 2) = false := rfl
  rw [htrue, hfalse] at h
  exact Bool.false_ne_true h.symm

/-- Negative control: the same cycle, under a policy that reads the
ledger, is not an uninformative spend. -/
theorem informative_round_trip_not_uninformative :
    ¬ UninformativeSpend budgetPolicy
        (false, zero) (true, zero * e0) (false, zero * e0 * e0) := by
  intro h
  exact budget_flips_on_round_trip h.2.2

#print axioms reading_eq_ledger
#print axioms reserves_not_observational
#print axioms ledger_projection_not_injective
#print axioms embed_does_not_record_spend
#print axioms embed_section_of_erase
#print axioms embed_then_erase_forgets_spend
#print axioms no_arbitrage_on_a_tick
#print axioms out_is_separation
#print axioms back_is_formation
#print axioms separation_does_not_descend
#print axioms stuck_round_trip_uninformative
#print axioms informative_round_trip_not_uninformative

end Mettapedia.GSLT.ReservesSelfModel
