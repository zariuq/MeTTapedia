import Mettapedia.OSLF.Framework.ObserverExtension
import Mettapedia.OSLF.Framework.KSUnificationSketch

/-!
# What the observer's instruments change, and where they change nothing

`ObserverExtension` proves that the extended presentation rewrites a term headed
by an authored operation exactly as the authored presentation does.  That is a
statement about *successors*.  It is not yet a statement about behaviour: more
transitions add both obligations to match and ways of matching, so no inclusion
between the two bisimilarities follows from rule inclusion, and the module said
so rather than claiming otherwise.

This module closes that gap, and the way it closes it is worth stating: the two
step relations are not merely related on the authored fragment, they are **the
same relation** there.  Everything defined from the step relation therefore
agrees — bisimilarity included — and the agreement is an equality rather than a
monotonicity.

**The index is carried.**  Every statement below names the instrument set it is
about.  Agreement holds *for that instrument set*, on terms headed by authored
operations, given that the set's administrative vocabulary is fresh.  An
adequacy claim without its instrument index is exactly what this module exists
to avoid making.

**Where agreement stops.**  The future modality stays inside a step-closed
fragment; the past modality does not, since a term's predecessors need not lie
in the fragment at all.  So the conservativity theorem for formulas is stated
for the fragment of the logic without the past modality and without generators,
and the boundary is named rather than crossed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ObserverBisimilarity

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.ObserverExtension
open Mettapedia.OSLF.Framework.KSUnificationSketch

/-! ## The setting -/

/-- Everything `rewriteAt_eq_of_authored_head` asks for, bundled: a
presentation, an instrument set, the authored vocabulary the fragment is headed
by, and the two conditions — the instruments' administrative vocabulary is
fresh, and the authored rules call only within the vocabulary. -/
structure Setting where
  /-- The authored presentation. -/
  lang : LanguageDef
  /-- The collection kind the opening request uses. -/
  cut : CollType
  /-- The instrument set: which declared constructors the observer may open. -/
  opened : List String
  /-- The authored vocabulary the fragment is headed by. -/
  names : List String
  /-- Every name of it is declared. -/
  namesAuthored : ∀ name ∈ names, name ∈ lang.terms.map GrammarRule.label
  /-- The instruments adjoin nothing the presentation already declares. -/
  fresh : AdministrativeFresh lang opened
  /-- And the authored rules call only within the vocabulary. -/
  callsWithin : ∀ rule ∈ lang.rewrites, CallsWithin names rule.premises

/-- The engine's one-step relation at a fixed fuel: a successor is one the
engine computes. -/
def computedStep (base : BasePremiseEvaluator) (lang : LanguageDef) (fuel : Nat)
    (source target : Pattern) : Prop :=
  target ∈ rewriteAt base lang fuel source

/-- The authored theory's step relation. -/
def authoredStep (setting : Setting) (base : BasePremiseEvaluator) (fuel : Nat) :
    Pattern → Pattern → Prop :=
  computedStep base setting.lang fuel

/-- The instrumented theory's step relation, at this instrument set. -/
def instrumentedStep (setting : Setting) (base : BasePremiseEvaluator) (fuel : Nat) :
    Pattern → Pattern → Prop :=
  computedStep base (observerExtension setting.lang setting.cut setting.opened) fuel

/-! ## The relations agree -/

/-- **The two step relations are the same relation on authored-headed terms.**
Not an inclusion in one direction: the successor lists are equal, so the
relations are. -/
theorem steps_agree (setting : Setting) (base₁ base₂ : BasePremiseEvaluator) (fuel : Nat)
    {source : Pattern} (head : HasOperationHead setting.names source) (target : Pattern) :
    authoredStep setting base₁ fuel source target ↔
      instrumentedStep setting base₂ fuel source target := by
  unfold authoredStep instrumentedStep computedStep
  rw [rewriteAt_eq_of_authored_head setting.lang setting.cut setting.opened
    setting.namesAuthored setting.fresh setting.callsWithin base₁ base₂ fuel head]

/-! ## A fragment on which two relations agree

The theorems below need one thing: two step relations that coincide on a set of
terms closed under them.  Stating them at that level rather than at the observer
extension is not generality for its own sake — the observer is one way to get
such a fragment, and a presentation whose rules consult an oracle is another,
since `CallsWithin` refuses a `relationQuery` premise (correctly: it makes no
recursive call, so the closed-subsystem argument has nothing to say about it)
while computation settles agreement directly. -/

/-- A set of terms on which two step relations agree, closed under them. -/
structure AgreeingFragment (first second : Pattern → Pattern → Prop) where
  /-- Membership. -/
  Mem : Pattern → Prop
  /-- The two relations coincide there. -/
  agree : ∀ term, Mem term → ∀ next, first term next ↔ second term next
  /-- And steps stay inside. -/
  closed : ∀ term, Mem term → ∀ next, first term next → Mem next

/-- Closure under the second relation follows from closure under the first. -/
theorem AgreeingFragment.closed_second {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) {term : Pattern}
    (member : fragment.Mem term) {next : Pattern} (step : second term next) :
    fragment.Mem next :=
  fragment.closed term member next ((fragment.agree term member next).mpr step)

/-- **The observer supplies one.**  On terms headed by the authored vocabulary
the two relations are equal, by conservativity. -/
def Setting.agreeingFragment (setting : Setting) (base : BasePremiseEvaluator) (fuel : Nat)
    (Mem : Pattern → Prop)
    (authored : ∀ term, Mem term → HasOperationHead setting.names term)
    (closed : ∀ term, Mem term → ∀ next,
      authoredStep setting base fuel term next → Mem next) :
    AgreeingFragment (authoredStep setting base fuel) (instrumentedStep setting base fuel) where
  Mem := Mem
  agree := fun term member next =>
    steps_agree setting base base fuel (authored term member) next
  closed := closed

/-! ## Bisimilarity is unchanged there -/

/-- A relation cut down to the fragment. -/
def restrict {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) (relation : Pattern → Pattern → Prop) :
    Pattern → Pattern → Prop :=
  fun left right => fragment.Mem left ∧ fragment.Mem right ∧ relation left right

/-- A bisimulation for the second relation restricts to one for the first. -/
theorem stepBisimulation_first_of_second {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) {relation : Pattern → Pattern → Prop}
    (bisimulation : StepBisimulation second relation) :
    StepBisimulation first (restrict fragment relation) := by
  obtain ⟨forward, backward⟩ := bisimulation
  constructor
  · rintro left right ⟨memLeft, memRight, related⟩ next step
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      forward left right related next ((fragment.agree left memLeft next).mp step)
    exact ⟨matched, (fragment.agree right memRight matched).mpr matchedStep,
      fragment.closed left memLeft next step,
      fragment.closed_second memRight matchedStep, matchedRelated⟩
  · rintro left right ⟨memLeft, memRight, related⟩ next step
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      backward left right related next ((fragment.agree right memRight next).mp step)
    exact ⟨matched, (fragment.agree left memLeft matched).mpr matchedStep,
      fragment.closed_second memLeft matchedStep,
      fragment.closed right memRight next step, matchedRelated⟩

/-- And conversely. -/
theorem stepBisimulation_second_of_first {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) {relation : Pattern → Pattern → Prop}
    (bisimulation : StepBisimulation first relation) :
    StepBisimulation second (restrict fragment relation) := by
  obtain ⟨forward, backward⟩ := bisimulation
  constructor
  · rintro left right ⟨memLeft, memRight, related⟩ next step
    have firstStep := (fragment.agree left memLeft next).mpr step
    obtain ⟨matched, matchedStep, matchedRelated⟩ := forward left right related next firstStep
    exact ⟨matched, (fragment.agree right memRight matched).mp matchedStep,
      fragment.closed left memLeft next firstStep,
      fragment.closed right memRight matched matchedStep, matchedRelated⟩
  · rintro left right ⟨memLeft, memRight, related⟩ next step
    have firstStep := (fragment.agree right memRight next).mpr step
    obtain ⟨matched, matchedStep, matchedRelated⟩ := backward left right related next firstStep
    exact ⟨matched, (fragment.agree left memLeft matched).mp matchedStep,
      fragment.closed left memLeft matched matchedStep,
      fragment.closed right memRight next firstStep, matchedRelated⟩

/-- **Bisimilarity is unchanged on the fragment.**  This is the monotonicity the
observer construction needed, and it holds as an equality because the relations
do. -/
theorem bisimilar_iff {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) {left right : Pattern}
    (memLeft : fragment.Mem left) (memRight : fragment.Mem right) :
    Bisimilar first left right ↔ Bisimilar second left right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨restrict fragment relation,
      stepBisimulation_second_of_first fragment bisimulation, memLeft, memRight, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨restrict fragment relation,
      stepBisimulation_first_of_second fragment bisimulation, memLeft, memRight, related⟩

/-! ## And so is the logic, on the fragment of it that stays inside

A formula reads the step relation through its modalities.  The future modality
reads successors, which the fragment keeps; the past modality reads
predecessors, which it does not.  So the reading agrees on the formulas that do
not look backwards.

The structural connectives are excluded for a second and independent reason:
they read a formula at the *parts* of a term, and a fragment closed under steps
need not be closed under decomposition.  So the statements below range over the
modal fragment, and say so. -/

/-- Formulas that do not look backwards. -/
def boxFree : OSLFFormula → Bool
  | .top => true
  | .bot => true
  | .atom _ => true
  | .var _ => true
  | .and φ ψ => boxFree φ && boxFree ψ
  | .or φ ψ => boxFree φ && boxFree ψ
  | .imp φ ψ => boxFree φ && boxFree ψ
  | .dia φ => boxFree φ
  | .box _ => false
  | .mu φ => boxFree φ
  | .emptyColl _ => true
  | .cut _ φ ψ => boxFree φ && boxFree ψ
  | .headed _ φ => boxFree φ

/-- **The two readings agree on the fragment**, for every formula of the modal
fragment that does not look backwards. -/
theorem semEnv_agree {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) (I : AtomSem) (env : ScopeEnv)
    (φ : OSLFFormula) (modalFragment : φ.modalOnly = true) (forwardOnly : boxFree φ = true)
    {term : Pattern} (member : fragment.Mem term) :
    semEnv first fullFrame I env φ term ↔ semEnv second fullFrame I env φ term := by
  induction φ generalizing term with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | atom _ => exact Iff.rfl
  | and left right leftIH rightIH =>
      simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at modalFragment
      simp only [boxFree, Bool.and_eq_true] at forwardOnly
      exact and_congr (leftIH modalFragment.1 forwardOnly.1 member)
        (rightIH modalFragment.2 forwardOnly.2 member)
  | or left right leftIH rightIH =>
      simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at modalFragment
      simp only [boxFree, Bool.and_eq_true] at forwardOnly
      exact or_congr (leftIH modalFragment.1 forwardOnly.1 member)
        (rightIH modalFragment.2 forwardOnly.2 member)
  | imp left right leftIH rightIH =>
      simp only [OSLFFormula.modalOnly, Bool.and_eq_true] at modalFragment
      simp only [boxFree, Bool.and_eq_true] at forwardOnly
      exact imp_congr (leftIH modalFragment.1 forwardOnly.1 member)
        (rightIH modalFragment.2 forwardOnly.2 member)
  | dia body bodyIH =>
      simp only [OSLFFormula.modalOnly] at modalFragment
      simp only [boxFree] at forwardOnly
      constructor
      · rintro ⟨next, step, holds⟩
        exact ⟨next, (fragment.agree term member next).mp step,
          (bodyIH modalFragment forwardOnly (fragment.closed term member next step)).mp holds⟩
      · rintro ⟨next, step, holds⟩
        have inside := fragment.closed_second member step
        exact ⟨next, (fragment.agree term member next).mpr step,
          (bodyIH modalFragment forwardOnly inside).mpr holds⟩
  | box _ _ => simp [boxFree] at forwardOnly
  | var _ => simp [OSLFFormula.modalOnly] at modalFragment
  | mu _ _ => simp [OSLFFormula.modalOnly] at modalFragment
  | emptyColl _ => simp [OSLFFormula.modalOnly] at modalFragment
  | cut _ _ _ _ _ => simp [OSLFFormula.modalOnly] at modalFragment
  | headed _ _ _ => simp [OSLFFormula.modalOnly] at modalFragment

/-- The closed-formula form. -/
theorem sem_agree {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) (I : AtomSem)
    (φ : OSLFFormula) (modalFragment : φ.modalOnly = true) (forwardOnly : boxFree φ = true)
    {term : Pattern} (member : fragment.Mem term) :
    sem first I φ term ↔ sem second I φ term :=
  semEnv_agree fragment I ScopeEnv.empty φ modalFragment forwardOnly member

/-- **Adequacy, carrying its instrument index.**  A formula separates two terms
of the fragment in one reading exactly when it separates them in the other — at
*this* instrument set, on this fragment, and for the modal-fragment formulas
that do not look backwards.  Every one of those qualifications is load-bearing,
and the statement names all of them. -/
theorem separates_iff {first second : Pattern → Pattern → Prop}
    (fragment : AgreeingFragment first second) (I : AtomSem)
    (φ : OSLFFormula) (modalFragment : φ.modalOnly = true) (forwardOnly : boxFree φ = true)
    {left right : Pattern}
    (memLeft : fragment.Mem left) (memRight : fragment.Mem right) :
    (sem first I φ left ∧ ¬ sem first I φ right) ↔
      (sem second I φ left ∧ ¬ sem second I φ right) :=
  and_congr (sem_agree fragment I φ modalFragment forwardOnly memLeft)
    (not_congr (sem_agree fragment I φ modalFragment forwardOnly memRight))

/-- **And the boundary is where it is said to be.** -/
theorem box_not_forwardOnly (φ : OSLFFormula) : boxFree (.box φ) = false := rfl

/-! ## An instance, so that none of the above is carried and never met

A presentation with two nullary formers and one rule between them, an instrument
set that opens the first, and the fragment consisting of those two terms.  Every
condition of the setting is decided by the presentation itself. -/

namespace Instance

open Mettapedia.GSLT.LanguageDef

/-- The first former. -/
def aRule : GrammarRule where
  label := "A"
  category := "P"
  params := []
  syntaxPattern := [.terminal "A"]

/-- The second. -/
def bRule : GrammarRule where
  label := "B"
  category := "P"
  params := []
  syntaxPattern := [.terminal "B"]

/-- The one rule: the first becomes the second. -/
def abRule : RewriteRule where
  name := "ab"
  typeContext := []
  premises := []
  left := .apply "A" []
  right := .apply "B" []

/-- The presentation. -/
def language : LanguageDef where
  name := "AB"
  types := [TypeDecl.plain "P"]
  terms := [aRule, bRule]
  equations := []
  rewrites := [abRule]

/-- The term that steps, and the term it steps to. -/
def stepper : Pattern := .apply "A" []
def stuck : Pattern := .apply "B" []

/-- The evaluator. -/
def evaluator : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

theorem stepper_successors : rewriteAt evaluator language 3 stepper = [stuck] := by
  decide +kernel

theorem stuck_successors : rewriteAt evaluator language 3 stuck = [] := by
  decide +kernel

/-- **The setting**, with every condition discharged by the presentation. -/
def setting : Setting where
  lang := language
  cut := .hashBag
  opened := ["A"]
  names := ["A", "B"]
  namesAuthored := by decide
  fresh := by decide
  callsWithin := by decide

/-- **The fragment**: the two terms, which is closed because the second is
stuck. -/
def fragment :
    AgreeingFragment (authoredStep setting evaluator 3) (instrumentedStep setting evaluator 3) :=
  Setting.agreeingFragment setting evaluator 3
    (fun term => term = stepper ∨ term = stuck)
    (by
      rintro term (rfl | rfl) <;>
        simp [HasOperationHead, stepper, stuck, setting])
    (by
      rintro term (rfl | rfl) next step
      · rw [authoredStep, computedStep, show setting.lang = language from rfl,
          stepper_successors] at step
        simp only [List.mem_singleton] at step
        exact Or.inr step
      · rw [authoredStep, computedStep, show setting.lang = language from rfl,
          stuck_successors] at step
        exact absurd step (List.not_mem_nil))

theorem stepper_mem : fragment.Mem stepper := Or.inl rfl

theorem stuck_mem : fragment.Mem stuck := Or.inr rfl

/-- The formula that asks whether anything happens: generator-free and forward
only. -/
def canStep : OSLFFormula := .dia .top

theorem canStep_modalFragment : canStep.modalOnly = true := rfl

theorem canStep_forwardOnly : boxFree canStep = true := rfl

/-- **The two readings agree at both terms**, which is `sem_agree` met rather
than carried. -/
theorem readings_agree (I : AtomSem) :
    (sem (authoredStep setting evaluator 3) I canStep stepper ↔
        sem (instrumentedStep setting evaluator 3) I canStep stepper) ∧
      (sem (authoredStep setting evaluator 3) I canStep stuck ↔
        sem (instrumentedStep setting evaluator 3) I canStep stuck) :=
  ⟨sem_agree fragment I canStep canStep_modalFragment
      canStep_forwardOnly stepper_mem,
    sem_agree fragment I canStep canStep_modalFragment
      canStep_forwardOnly stuck_mem⟩

/-- And the formula is not idle: it holds at the stepper and fails at the stuck
term, so the agreement is between two readings that both say something. -/
theorem canStep_separates (I : AtomSem) :
    sem (authoredStep setting evaluator 3) I canStep stepper ∧
      ¬ sem (authoredStep setting evaluator 3) I canStep stuck := by
  constructor
  · refine ⟨stuck, ?_, trivial⟩
    rw [authoredStep, computedStep, show setting.lang = language from rfl,
      stepper_successors]
    simp
  · rintro ⟨next, step, -⟩
    rw [authoredStep, computedStep, show setting.lang = language from rfl,
      stuck_successors] at step
    exact absurd step (List.not_mem_nil)

/-- **So the separation survives the instruments**, at this instrument set. -/
theorem canStep_separates_instrumented (I : AtomSem) :
    sem (instrumentedStep setting evaluator 3) I canStep stepper ∧
      ¬ sem (instrumentedStep setting evaluator 3) I canStep stuck :=
  (separates_iff fragment I canStep canStep_modalFragment
    canStep_forwardOnly stepper_mem stuck_mem).mp (canStep_separates I)

end Instance

end Mettapedia.OSLF.Framework.ObserverBisimilarity
