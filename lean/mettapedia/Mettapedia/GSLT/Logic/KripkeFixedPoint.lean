import Mathlib.Data.Set.Insert
import Mettapedia.TypeTheory.Authority
import Mettapedia.Logic.Diagonal.Lawvere

/-!
# The partial escape: Kripke's least fixed point in the knowledge order

Judgments may speak about the truth of judgments.  Each judgment has a
specification, a strong Kleene formula over base facts and over the truth of
judgments.  A *valuation* is a three-valued assignment, presented as the set of
judgments held and the set of judgments failed; valuations are ordered by
inclusion of both sets, the *knowledge order* (undetermined below determined).
The *jump* evaluates every specification in a valuation.

* The jump is monotone (`jump_mono`), and the least fixed point exists as the
  intersection of all pre-fixed points (`least`, `jump_least_le`,
  `le_jump_least`, `least_le`), built without choice.
* **Duality** (`jump_dual_le`): the dual of a sound valuation (swap the two
  sets and complement them) is a pre-fixed point.  Hence the least fixed point
  lies below its own dual, which is consistency (`least_consistent`).
* **The diagonal stays undetermined** (`liar_undetermined`): a judgment whose
  specification is the negation of its own truth is neither held nor failed by
  any sound, consistent valuation, in particular by the least fixed point.
* **Leastness matters** (`truthTeller_not_mem_least`): a judgment specifying
  only its own truth is undetermined in the least fixed point; the concrete
  system below shows it held in one fixed point and failed in another.
* **Tarski** (`no_two_valued_fixedPoint`): with a liar, no two-valued valuation
  satisfies every specification; Boolean negation has no fixed point, while
  strong Kleene negation fixes `none` (`kleeneNot_none`,
  `liar_status_eq_none`).  This is the Lawvere obstruction and its escape.

**Outcomes.**  The verdict of a valuation is an `Outcome`: `established` on
held judgments, `refuted` on failed ones, `outsideFragment` (ungrounded)
elsewhere.  The least fixed point's verdicts are sound for the authority of
grounded truth (`groundedAuthority`), knowledge-below the verdicts of every
consistent pre-fixed valuation (`verdict_least_knowledgeLE`), and the liar's
verdict is `outsideFragment` (`verdict_liar_outside`).  Authority refinement is
a special case of the knowledge order (`knowledgeLE_of_authorityRefines`).

Base facts are three-valued too (`baseHolds`, `baseFails`, disjoint), so a
bubble's own budgeted verdicts can ground the system.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.KripkeTruth

open Mettapedia.TypeTheory.AuthorityTheory

universe u v

/-- Strong Kleene formulas over base facts and the truth of judgments. -/
inductive Formula (Judgment : Type u) (Base : Type v) where
  | base (fact : Base)
  | truth (judgment : Judgment)
  | neg (formula : Formula Judgment Base)
  | conj (first second : Formula Judgment Base)
  | disj (first second : Formula Judgment Base)

/-- A three-valued valuation: the judgments held and the judgments failed. -/
structure Valuation (Judgment : Type u) where
  holds : Set Judgment
  fails : Set Judgment

namespace Valuation

variable {Judgment : Type u}

/-- **The knowledge order**: everything determined stays determined the same
way. -/
def Le (first second : Valuation Judgment) : Prop :=
  first.holds ⊆ second.holds ∧ first.fails ⊆ second.fails

theorem le_refl (valuation : Valuation Judgment) : valuation.Le valuation :=
  ⟨fun _ member => member, fun _ member => member⟩

theorem le_trans {first second third : Valuation Judgment} (h : first.Le second)
    (h' : second.Le third) : first.Le third :=
  ⟨fun _ member => h'.1 (h.1 member), fun _ member => h'.2 (h.2 member)⟩

/-- No judgment is both held and failed. -/
def Consistent (valuation : Valuation Judgment) : Prop :=
  ∀ judgment, judgment ∈ valuation.holds → judgment ∉ valuation.fails

/-- The dual valuation: hold what is not failed, fail what is not held. -/
def dual (valuation : Valuation Judgment) : Valuation Judgment :=
  ⟨{judgment | judgment ∉ valuation.fails}, {judgment | judgment ∉ valuation.holds}⟩

/-- A valuation is consistent exactly when it lies below its dual. -/
theorem consistent_iff_le_dual (valuation : Valuation Judgment) :
    valuation.Consistent ↔ valuation.Le valuation.dual :=
  ⟨fun consistent => ⟨fun judgment held => consistent judgment held,
      fun judgment failed held => consistent judgment held failed⟩,
    fun le _ held failed => le.1 held failed⟩

end Valuation

/-- A system of self-referential judgments over three-valued base facts. -/
structure System (Judgment : Type u) (Base : Type v) where
  spec : Judgment → Formula Judgment Base
  baseHolds : Base → Prop
  baseFails : Base → Prop
  base_consistent : ∀ fact, baseHolds fact → ¬ baseFails fact

namespace System

variable {Judgment : Type u} {Base : Type v}

/-- Strong Kleene evaluation, as the pair (holds, fails). -/
def eval (system : System Judgment Base) (valuation : Valuation Judgment) :
    Formula Judgment Base → Prop × Prop
  | .base fact => (system.baseHolds fact, system.baseFails fact)
  | .truth judgment => (judgment ∈ valuation.holds, judgment ∈ valuation.fails)
  | .neg formula => ((eval system valuation formula).2, (eval system valuation formula).1)
  | .conj first second =>
      ((eval system valuation first).1 ∧ (eval system valuation second).1,
        (eval system valuation first).2 ∨ (eval system valuation second).2)
  | .disj first second =>
      ((eval system valuation first).1 ∨ (eval system valuation second).1,
        (eval system valuation first).2 ∧ (eval system valuation second).2)

/-- Evaluation is monotone in the knowledge order. -/
theorem eval_mono (system : System Judgment Base) {first second : Valuation Judgment}
    (le : first.Le second) :
    ∀ formula : Formula Judgment Base,
      ((system.eval first formula).1 → (system.eval second formula).1) ∧
        ((system.eval first formula).2 → (system.eval second formula).2)
  | .base _ => ⟨id, id⟩
  | .truth _ => ⟨fun held => le.1 held, fun failed => le.2 failed⟩
  | .neg formula =>
      let ih := eval_mono system le formula
      ⟨ih.2, ih.1⟩
  | .conj first second =>
      let ihFirst := eval_mono system le first
      let ihSecond := eval_mono system le second
      ⟨fun held => ⟨ihFirst.1 held.1, ihSecond.1 held.2⟩,
        fun failed => failed.elim (fun f => Or.inl (ihFirst.2 f)) (fun f => Or.inr (ihSecond.2 f))⟩
  | .disj first second =>
      let ihFirst := eval_mono system le first
      let ihSecond := eval_mono system le second
      ⟨fun held => held.elim (fun h => Or.inl (ihFirst.1 h)) (fun h => Or.inr (ihSecond.1 h)),
        fun failed => ⟨ihFirst.2 failed.1, ihSecond.2 failed.2⟩⟩

/-- **Duality of evaluation**: what holds in the dual does not fail in the
valuation, and what fails in the dual does not hold in it. -/
theorem eval_dual (system : System Judgment Base) (valuation : Valuation Judgment) :
    ∀ formula : Formula Judgment Base,
      ((system.eval valuation.dual formula).1 → ¬ (system.eval valuation formula).2) ∧
        ((system.eval valuation.dual formula).2 → ¬ (system.eval valuation formula).1)
  | .base fact =>
      ⟨fun held failed => system.base_consistent fact held failed,
        fun failed held => system.base_consistent fact held failed⟩
  | .truth _ => ⟨fun held => held, fun failed => failed⟩
  | .neg formula =>
      let ih := eval_dual system valuation formula
      ⟨ih.2, ih.1⟩
  | .conj first second =>
      let ihFirst := eval_dual system valuation first
      let ihSecond := eval_dual system valuation second
      ⟨fun held failed => failed.elim (ihFirst.1 held.1) (ihSecond.1 held.2),
        fun failed held => failed.elim (fun f => ihFirst.2 f held.1)
          (fun f => ihSecond.2 f held.2)⟩
  | .disj first second =>
      let ihFirst := eval_dual system valuation first
      let ihSecond := eval_dual system valuation second
      ⟨fun held failed => held.elim (fun h => ihFirst.1 h failed.1)
          (fun h => ihSecond.1 h failed.2),
        fun failed held => held.elim (ihFirst.2 failed.1) (ihSecond.2 failed.2)⟩

variable (system : System Judgment Base)

/-- **The jump**: evaluate every specification. -/
def jump (valuation : Valuation Judgment) : Valuation Judgment :=
  ⟨{judgment | (system.eval valuation (system.spec judgment)).1},
    {judgment | (system.eval valuation (system.spec judgment)).2}⟩

theorem jump_mono {first second : Valuation Judgment} (le : first.Le second) :
    (system.jump first).Le (system.jump second) :=
  ⟨fun judgment held => (system.eval_mono le (system.spec judgment)).1 held,
    fun judgment failed => (system.eval_mono le (system.spec judgment)).2 failed⟩

/-- A valuation is sound when everything it determines is confirmed by the
jump. -/
def Sound (valuation : Valuation Judgment) : Prop :=
  valuation.Le (system.jump valuation)

/-- **The dual of a sound valuation is a pre-fixed point.** -/
theorem jump_dual_le {valuation : Valuation Judgment} (sound : system.Sound valuation) :
    (system.jump valuation.dual).Le valuation.dual :=
  ⟨fun judgment held failed =>
      (system.eval_dual valuation (system.spec judgment)).1 held (sound.2 failed),
    fun judgment failed held =>
      (system.eval_dual valuation (system.spec judgment)).2 failed (sound.1 held)⟩

/-! ## The least fixed point -/

/-- **The least fixed point**: what every pre-fixed valuation holds, and what
every pre-fixed valuation fails. -/
def least : Valuation Judgment :=
  ⟨{judgment | ∀ valuation : Valuation Judgment, (system.jump valuation).Le valuation →
      judgment ∈ valuation.holds},
    {judgment | ∀ valuation : Valuation Judgment, (system.jump valuation).Le valuation →
      judgment ∈ valuation.fails}⟩

/-- The least fixed point lies below every pre-fixed valuation. -/
theorem least_le {valuation : Valuation Judgment} (pre : (system.jump valuation).Le valuation) :
    system.least.Le valuation :=
  ⟨fun _ held => held valuation pre, fun _ failed => failed valuation pre⟩

theorem jump_least_le : (system.jump system.least).Le system.least :=
  ⟨fun _ held _ pre => pre.1 ((system.jump_mono (system.least_le pre)).1 held),
    fun _ failed _ pre => pre.2 ((system.jump_mono (system.least_le pre)).2 failed)⟩

theorem le_jump_least : system.least.Le (system.jump system.least) :=
  system.least_le (system.jump_mono system.jump_least_le)

/-- The least fixed point is sound. -/
theorem least_sound : system.Sound system.least := system.le_jump_least

/-- **Consistency of the least fixed point**, from duality. -/
theorem least_consistent : system.least.Consistent :=
  (Valuation.consistent_iff_le_dual _).mpr
    (system.least_le (system.jump_dual_le system.least_sound))

/-! ## The diagonal and the truth-teller -/

/-- **The diagonal stays undetermined**: a judgment whose specification negates
its own truth is neither held nor failed by any sound, consistent valuation. -/
theorem liar_undetermined {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar))
    {valuation : Valuation Judgment} (sound : system.Sound valuation)
    (consistent : valuation.Consistent) :
    liar ∉ valuation.holds ∧ liar ∉ valuation.fails := by
  constructor
  · intro held
    have jumped := sound.1 held
    change (system.eval valuation (system.spec liar)).1 at jumped
    rw [isLiar] at jumped
    exact consistent liar held jumped
  · intro failed
    have jumped := sound.2 failed
    change (system.eval valuation (system.spec liar)).2 at jumped
    rw [isLiar] at jumped
    exact consistent liar jumped failed

theorem liar_not_mem_least {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar)) :
    liar ∉ system.least.holds ∧ liar ∉ system.least.fails :=
  system.liar_undetermined isLiar system.least_sound system.least_consistent

/-- **A truth-teller is ungrounded**: undetermined in the least fixed point. -/
theorem truthTeller_not_mem_least {teller : Judgment}
    (isTeller : system.spec teller = .truth teller) :
    teller ∉ system.least.holds ∧ teller ∉ system.least.fails := by
  let removed : Valuation Judgment :=
    ⟨{judgment | judgment ∈ system.least.holds ∧ judgment ≠ teller},
      {judgment | judgment ∈ system.least.fails ∧ judgment ≠ teller}⟩
  have below : removed.Le system.least := ⟨fun _ held => held.1, fun _ failed => failed.1⟩
  have pre : (system.jump removed).Le removed := by
    constructor
    · intro judgment held
      refine ⟨system.jump_least_le.1 ((system.jump_mono below).1 held), ?_⟩
      rintro rfl
      change (system.eval removed (system.spec judgment)).1 at held
      rw [isTeller] at held
      exact held.2 rfl
    · intro judgment failed
      refine ⟨system.jump_least_le.2 ((system.jump_mono below).2 failed), ?_⟩
      rintro rfl
      change (system.eval removed (system.spec judgment)).2 at failed
      rw [isTeller] at failed
      exact failed.2 rfl
  have le := system.least_le pre
  exact ⟨fun held => (le.1 held).2 rfl, fun failed => (le.2 failed).2 rfl⟩

/-! ## Two values: Tarski, and the Kleene escape -/

/-- Two-valued evaluation, given Boolean truth values of base facts. -/
def evalBool (baseValue : Base → Bool) (valuation : Judgment → Bool) :
    Formula Judgment Base → Bool
  | .base fact => baseValue fact
  | .truth judgment => valuation judgment
  | .neg formula => !(evalBool baseValue valuation formula)
  | .conj first second => evalBool baseValue valuation first && evalBool baseValue valuation second
  | .disj first second => evalBool baseValue valuation first || evalBool baseValue valuation second

/-- **Tarski's undefinability**: with a liar, no two-valued valuation satisfies
every specification, because Boolean negation has no fixed point. -/
theorem no_two_valued_fixedPoint {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar))
    (baseValue : Base → Bool) :
    ¬ ∃ valuation : Judgment → Bool,
      ∀ judgment, valuation judgment = evalBool baseValue valuation (system.spec judgment) := by
  rintro ⟨valuation, fixed⟩
  have atLiar := fixed liar
  rw [isLiar] at atLiar
  exact Mettapedia.Logic.Diagonal.bool_not_fixedPointFree (valuation liar) atLiar.symm

end System

/-- Strong Kleene negation on statuses. -/
def kleeneNot : Option Bool → Option Bool
  | some value => some (!value)
  | none => none

/-- **Strong Kleene negation has a fixed point**, the undetermined status. -/
theorem kleeneNot_none : kleeneNot none = none := rfl

/-- It is the only one. -/
theorem kleeneNot_fixed_iff (status : Option Bool) : kleeneNot status = status ↔ status = none := by
  cases status with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some value => cases value <;> simp [kleeneNot]

/-- The status of a judgment in a valuation. -/
def status {Judgment : Type u} (valuation : Valuation Judgment)
    [DecidablePred (· ∈ valuation.holds)]
    [DecidablePred (· ∈ valuation.fails)] (judgment : Judgment) : Option Bool :=
  if judgment ∈ valuation.holds then some true
  else if judgment ∈ valuation.fails then some false else none

/-- The liar's status in a sound consistent valuation is the Kleene fixed point
`none`. -/
theorem liar_status_eq_none {Judgment : Type u} {Base : Type v} (system : System Judgment Base)
    {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar))
    {valuation : Valuation Judgment} [DecidablePred (· ∈ valuation.holds)]
    [DecidablePred (· ∈ valuation.fails)] (sound : system.Sound valuation)
    (consistent : valuation.Consistent) : status valuation liar = none := by
  obtain ⟨notHeld, notFailed⟩ := system.liar_undetermined isLiar sound consistent
  simp [status, notHeld, notFailed]

/-! ## Verdicts as outcomes -/

section Outcomes

variable {Established : Sort u} {Refuted : Sort v} {Boundary : Type u} {Incomplete : Type v}

/-- **The knowledge order on outcomes**: every decided answer is kept. -/
def KnowledgeLE {Established' Refuted' : Sort*} {Boundary' Incomplete' : Type*}
    (first : Outcome Established Refuted Boundary Incomplete)
    (second : Outcome Established' Refuted' Boundary' Incomplete') : Prop :=
  ∀ answer, first.asBool = some answer → second.asBool = some answer

/-- Refinement by a stronger authority is a knowledge increase. -/
theorem knowledgeLE_of_authorityRefines
    {first second : Outcome Established Refuted Boundary Incomplete}
    (refines : Outcome.AuthorityRefines first second) : KnowledgeLE first second := by
  intro answer decided
  cases refines <;> simp_all [Outcome.asBool]

end Outcomes

namespace System

variable {Judgment : Type u} {Base : Type v} (system : System Judgment Base)

/-- **The authority of grounded truth**: a judgment holds when the least fixed
point holds it; evidence is membership in the held set, obstruction membership
in the failed set, sound by consistency. -/
def groundedAuthority : Authority.{u, 0, 0} Judgment where
  Holds judgment := judgment ∈ system.least.holds
  Evidence judgment := judgment ∈ system.least.holds
  Obstruction judgment := judgment ∈ system.least.fails
  evidenceSound _ held := held
  obstructionSound judgment failed held := system.least_consistent judgment held failed

/-- The verdict of a valuation on a judgment.  Membership in a valuation is
not decidable in general, so the case split is classical. -/
noncomputable def verdict (valuation : Valuation Judgment) (judgment : Judgment) :
    Outcome (judgment ∈ valuation.holds) (judgment ∈ valuation.fails) Unit Empty := by
  classical
  exact if held : judgment ∈ valuation.holds then .established held
    else if failed : judgment ∈ valuation.fails then .refuted failed
    else .outsideFragment ()

/-- The least fixed point's verdict is an authorised outcome of grounded
truth. -/
noncomputable def groundedVerdict (judgment : Judgment) :
    AuthorizedOutcome system.groundedAuthority Unit Empty judgment :=
  verdict system.least judgment

theorem verdict_asBool_eq_some_true {valuation : Valuation Judgment} {judgment : Judgment} :
    (verdict valuation judgment).asBool = some true ↔ judgment ∈ valuation.holds := by
  unfold verdict
  by_cases held : judgment ∈ valuation.holds
  · simp [held, Outcome.asBool]
  · by_cases failed : judgment ∈ valuation.fails
    · simp [held, failed, Outcome.asBool]
    · simp [held, failed, Outcome.asBool]

theorem verdict_asBool_eq_some_false {valuation : Valuation Judgment} {judgment : Judgment}
    (consistent : valuation.Consistent) :
    (verdict valuation judgment).asBool = some false ↔ judgment ∈ valuation.fails := by
  unfold verdict
  by_cases held : judgment ∈ valuation.holds
  · simp [held, Outcome.asBool, consistent judgment held]
  · by_cases failed : judgment ∈ valuation.fails
    · simp [held, failed, Outcome.asBool]
    · simp [held, failed, Outcome.asBool]

/-- **The least fixed point is knowledge-below every consistent pre-fixed
valuation**, verdict by verdict. -/
theorem verdict_least_knowledgeLE {valuation : Valuation Judgment}
    (pre : (system.jump valuation).Le valuation) (consistent : valuation.Consistent)
    (judgment : Judgment) :
    KnowledgeLE (verdict system.least judgment) (verdict valuation judgment) := by
  intro answer decided
  cases answer with
  | true =>
      exact verdict_asBool_eq_some_true.mpr ((system.least_le pre).1
        (verdict_asBool_eq_some_true.mp decided))
  | false =>
      exact (verdict_asBool_eq_some_false consistent).mpr ((system.least_le pre).2
        ((verdict_asBool_eq_some_false system.least_consistent).mp decided))

/-- **The diagonal's verdict is `outsideFragment`.** -/
theorem verdict_liar_outside {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar)) :
    verdict system.least liar = .outsideFragment () := by
  obtain ⟨notHeld, notFailed⟩ := system.liar_not_mem_least isLiar
  unfold verdict
  simp [notHeld, notFailed]

end System

/-! ## A concrete system -/

namespace Example

/-- Judgments: a grounded fact, its ascriptions, a liar, a truth-teller, and
strong Kleene compounds mixing them. -/
inductive Sentence where
  | fact
  | factTrue
  | factTrueTrue
  | liar
  | teller
  | liarOrFact
  | liarAndNotFact
  | liarOrNotFact
  deriving DecidableEq

/-- The base: one true fact. -/
def system : System Sentence Unit where
  spec
    | .fact => .base ()
    | .factTrue => .truth .fact
    | .factTrueTrue => .truth .factTrue
    | .liar => .neg (.truth .liar)
    | .teller => .truth .teller
    | .liarOrFact => .disj (.truth .liar) (.truth .fact)
    | .liarAndNotFact => .conj (.truth .liar) (.neg (.truth .fact))
    | .liarOrNotFact => .disj (.truth .liar) (.neg (.truth .fact))
  baseHolds _ := True
  baseFails _ := False
  base_consistent _ _ failed := failed

/-- The grounded part: held and failed judgments of the least fixed point. -/
def groundedHolds : Set Sentence := {.fact, .factTrue, .factTrueTrue, .liarOrFact}

def groundedFails : Set Sentence := {.liarAndNotFact}

/-- The grounded valuation is a fixed point. -/
theorem grounded_fixed :
    (system.jump ⟨groundedHolds, groundedFails⟩).Le ⟨groundedHolds, groundedFails⟩ ∧
      system.Sound ⟨groundedHolds, groundedFails⟩ := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro sentence <;> cases sentence <;>
    simp [System.jump, System.eval, system, groundedHolds,
      groundedFails, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- A grounded judgment is established by the least fixed point: the base
fact, its iterated ascriptions, and a disjunction whose other disjunct is the
liar. -/
theorem fact_chain_held :
    Sentence.factTrueTrue ∈ system.least.holds ∧ Sentence.liarOrFact ∈ system.least.holds := by
  constructor
  · intro valuation pre
    have fact : Sentence.fact ∈ valuation.holds := pre.1 (by
      change (system.eval valuation (system.spec .fact)).1
      exact trivial)
    have factTrue : Sentence.factTrue ∈ valuation.holds := pre.1 fact
    exact pre.1 factTrue
  · intro valuation pre
    have fact : Sentence.fact ∈ valuation.holds := pre.1 (by
      change (system.eval valuation (system.spec .fact)).1
      exact trivial)
    exact pre.1 (Or.inr fact)

/-- A conjunction with a failed conjunct is refuted even though its other
conjunct is the liar. -/
theorem liarAndNotFact_failed : Sentence.liarAndNotFact ∈ system.least.fails := by
  intro valuation pre
  have fact : Sentence.fact ∈ valuation.holds := pre.1 (by
    change (system.eval valuation (system.spec .fact)).1
    exact trivial)
  exact pre.2 (Or.inr fact)

/-- The least fixed point is exactly the grounded valuation. -/
theorem least_eq_grounded :
    system.least.holds = groundedHolds ∧ system.least.fails = groundedFails := by
  have le := system.least_le grounded_fixed.1
  have ge : (⟨groundedHolds, groundedFails⟩ : Valuation Sentence).Le system.least := by
    obtain ⟨chain, disjunction⟩ := fact_chain_held
    constructor
    · intro sentence member
      simp only [groundedHolds, Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact fun valuation pre => pre.1 (by
          change (system.eval valuation (system.spec .fact)).1
          exact trivial)
      · exact fun valuation pre => pre.1 (pre.1 (by
          change (system.eval valuation (system.spec .fact)).1
          exact trivial))
      · exact chain
      · exact disjunction
    · intro sentence member
      simp only [groundedFails, Set.mem_singleton_iff] at member
      subst member
      exact liarAndNotFact_failed
  exact ⟨Set.Subset.antisymm le.1 ge.1, Set.Subset.antisymm le.2 ge.2⟩

/-- The truth-teller held, over the grounded valuation. -/
def tellerHeld : Valuation Sentence := ⟨insert .teller groundedHolds, groundedFails⟩

/-- The truth-teller failed, over the grounded valuation. -/
def tellerFailed : Valuation Sentence := ⟨groundedHolds, insert .teller groundedFails⟩

/-- **The truth-teller is held in one fixed point and failed in another**: the
choice is not grounded, and the least fixed point leaves it undetermined. -/
theorem teller_both_ways :
    ((system.jump tellerHeld).Le tellerHeld ∧ system.Sound tellerHeld ∧
        tellerHeld.Consistent ∧ Sentence.teller ∈ tellerHeld.holds) ∧
      ((system.jump tellerFailed).Le tellerFailed ∧ system.Sound tellerFailed ∧
        tellerFailed.Consistent ∧ Sentence.teller ∈ tellerFailed.fails) := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩⟩ <;>
    first
    | (intro sentence; cases sentence <;>
        simp [System.jump, System.eval, system, tellerHeld, tellerFailed, groundedHolds,
          groundedFails, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff])
    | simp [tellerHeld, tellerFailed, groundedHolds, groundedFails, Set.mem_insert_iff,
        Set.mem_singleton_iff]

/-- The liar's verdict is `outsideFragment`, while the grounded fact is
established. -/
theorem verdicts :
    System.verdict system.least Sentence.liar = .outsideFragment () ∧
      (System.verdict system.least Sentence.factTrueTrue).asBool = some true ∧
      (System.verdict system.least Sentence.liarAndNotFact).asBool = some false ∧
      Sentence.teller ∉ system.least.holds ∧ Sentence.teller ∉ system.least.fails ∧
      Sentence.liarOrNotFact ∉ system.least.holds ∧
      Sentence.liarOrNotFact ∉ system.least.fails := by
  obtain ⟨holdsEq, failsEq⟩ := least_eq_grounded
  refine ⟨system.verdict_liar_outside rfl,
    System.verdict_asBool_eq_some_true.mpr fact_chain_held.1,
    (System.verdict_asBool_eq_some_false system.least_consistent).mpr liarAndNotFact_failed,
    ?_, ?_, ?_, ?_⟩ <;> simp [holdsEq, failsEq, groundedHolds, groundedFails]

end Example

end Mettapedia.GSLT.KripkeTruth
