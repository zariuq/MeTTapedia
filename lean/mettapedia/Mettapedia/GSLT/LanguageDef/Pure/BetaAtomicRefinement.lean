/-
# Beta-conversion atomic refinement for Pure

The policy-visible action remains exactly `Refine(hole, head)`.  Lambda
introduction and dependent-spine construction remain deterministic elaborator
effects.  Every conversion query is delegated to the proved, fuel-bounded
decision path in `BetaConversion`; its exhaustion verdict is preserved.
-/

import Mettapedia.GSLT.LanguageDef.Pure.AtomicRefinement
import Mettapedia.GSLT.LanguageDef.Pure.BetaConversion

namespace Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement

open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureRefinement
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBeta

/-- Classified outcome shared by inference, elaboration, and authentication. -/
inductive CheckResult (α : Type) where
  | ok : α → CheckResult α
  | rejected : CheckResult α
  | conversionFuelExhausted : CheckResult α
  deriving DecidableEq, Repr

namespace CheckResult

def toOption : CheckResult α → Option α
  | .ok value => some value
  | .rejected | .conversionFuelExhausted => none

def isOk : CheckResult α → Bool
  | .ok _ => true
  | .rejected | .conversionFuelExhausted => false

end CheckResult

/-- Atomicity has the same explicit exhaustion boundary as convertibility. -/
inductive AtomicityVerdict where
  | atomic
  | nonAtomic
  | conversionFuelExhausted
  deriving DecidableEq, Repr

def atomicityVerdict (fuel : Nat) (type : Expr) : AtomicityVerdict :=
  match normalize fuel type with
  | .normalized reduced =>
      if reduced.atomic then .atomic else .nonAtomic
  | .conversionFuelExhausted => .conversionFuelExhausted

theorem atomicityVerdict_sound {fuel : Nat} {type : Expr}
    (hatomic : atomicityVerdict fuel type = .atomic) : BetaAtomic type := by
  unfold atomicityVerdict at hatomic
  cases hnormalize : normalize fuel type with
  | conversionFuelExhausted => simp [hnormalize] at hatomic
  | normalized reduced =>
      by_cases hbool : reduced.atomic = true
      · exact
          ⟨reduced, normalize_sound hnormalize,
            (Expr.atomic_eq_true_iff reduced).mp hbool⟩
      · simp [hnormalize, hbool] at hatomic

mutual
/-- The finite, executable fragment of the declarative beta typing judgment. -/
inductive CheckedHasType : Ctx → Nf → Expr → Prop where
  | lam {context domain body bodyType} :
      CheckedHasType (domain :: context) body bodyType →
      CheckedHasType context (.lam domain body) (.pi domain bodyType)
  | head {context index headType arguments resultType} :
      ctxLookup context index = some headType →
      CheckedSpineHasType context headType arguments resultType →
      atomicityVerdict normalizationFuel resultType = .atomic →
      CheckedHasType context (.head index arguments) resultType

/-- Checked dependent spines record every successful bounded conversion query. -/
inductive CheckedSpineHasType : Ctx → Expr → List Nf → Expr → Prop where
  | nil {context headType} : CheckedSpineHasType context headType [] headType
  | cons {context domain body argument actualType rest resultType} :
      CheckedHasType context argument actualType →
      conversionVerdict normalizationFuel actualType domain = .convertible →
      CheckedSpineHasType context (Expr.subst0 argument.erase body) rest resultType →
      CheckedSpineHasType context (.pi domain body) (argument :: rest) resultType
end

mutual
/-- Checked typing is sound for the declarative conversion-inclusive statics. -/
theorem checkedHasType_sound : ∀ {context term type},
    CheckedHasType context term type →
      Mettapedia.GSLT.LanguageDef.PureBeta.HasType context term type
  | _, _, _, .lam hbody => .lam (checkedHasType_sound hbody)
  | _, _, _, .head hlookup hspine hatomic =>
      .head hlookup (checkedSpineHasType_sound hspine)
        (atomicityVerdict_sound hatomic)

/-- Checked spine typing is sound for declarative beta spine typing. -/
theorem checkedSpineHasType_sound : ∀ {context headType arguments resultType},
    CheckedSpineHasType context headType arguments resultType →
      Mettapedia.GSLT.LanguageDef.PureBeta.SpineHasType
        context headType arguments resultType
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hargument hconversion hrest =>
      .cons (checkedHasType_sound hargument)
        (conversionVerdict_sound hconversion)
        (checkedSpineHasType_sound hrest)
end

mutual
/-- Fuelled inference with classified conversion exhaustion. -/
def inferNfFuel : Nat → Ctx → Nf → CheckResult Expr
  | 0, _, _ => .rejected
  | fuel + 1, context, .lam domain body =>
      match inferNfFuel fuel (domain :: context) body with
      | .ok bodyType => .ok (.pi domain bodyType)
      | .rejected => .rejected
      | .conversionFuelExhausted => .conversionFuelExhausted
  | fuel + 1, context, .head index arguments =>
      match ctxLookup context index with
      | none => .rejected
      | some headType =>
          match inferSpineFuel fuel context headType arguments with
          | .rejected => .rejected
          | .conversionFuelExhausted => .conversionFuelExhausted
          | .ok resultType =>
              match atomicityVerdict normalizationFuel resultType with
              | .atomic => .ok resultType
              | .nonAtomic => .rejected
              | .conversionFuelExhausted => .conversionFuelExhausted

/-- Fuelled ordered-spine inference with beta conversion at argument slots. -/
def inferSpineFuel : Nat → Ctx → Expr → List Nf → CheckResult Expr
  | 0, _, _, _ => .rejected
  | _fuel + 1, _, headType, [] => .ok headType
  | fuel + 1, context, .pi domain body, argument :: rest =>
      match inferNfFuel fuel context argument with
      | .rejected => .rejected
      | .conversionFuelExhausted => .conversionFuelExhausted
      | .ok actualType =>
          match conversionVerdict normalizationFuel actualType domain with
          | .convertible =>
              inferSpineFuel fuel context
                (Expr.subst0 argument.erase body) rest
          | .normalFormsDiffer => .rejected
          | .conversionFuelExhausted => .conversionFuelExhausted
  | _fuel + 1, _, _, _ :: _ => .rejected
end

def inferNf (context : Ctx) (term : Nf) : CheckResult Expr :=
  inferNfFuel (term.weight + 1) context term

def inferSpine (context : Ctx) (headType : Expr)
    (arguments : List Nf) : CheckResult Expr :=
  inferSpineFuel (Nf.listWeight arguments + 1) context headType arguments

mutual
/-- Simultaneous soundness of classified term and spine inference. -/
theorem inferFuel_sound : ∀ fuel,
    (∀ context term type,
      inferNfFuel fuel context term = .ok type →
        CheckedHasType context term type) ∧
    (∀ context headType arguments resultType,
      inferSpineFuel fuel context headType arguments = .ok resultType →
        CheckedSpineHasType context headType arguments resultType) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intro <;> simp [inferNfFuel, inferSpineFuel] at *
  | succ fuel ih =>
      constructor
      · intro context term type hinfer
        cases term with
        | lam domain body =>
            simp only [inferNfFuel] at hinfer
            cases hbody : inferNfFuel fuel (domain :: context) body with
            | rejected => simp [hbody] at hinfer
            | conversionFuelExhausted => simp [hbody] at hinfer
            | ok bodyType =>
                simp [hbody] at hinfer
                subst type
                exact CheckedHasType.lam (ih.1 _ _ _ hbody)
        | head index arguments =>
            simp only [inferNfFuel] at hinfer
            cases hlookup : ctxLookup context index with
            | none => simp [hlookup] at hinfer
            | some headType =>
                cases hspine : inferSpineFuel fuel context headType arguments with
                | rejected => simp [hlookup, hspine] at hinfer
                | conversionFuelExhausted => simp [hlookup, hspine] at hinfer
                | ok resultType =>
                    cases hatomic : atomicityVerdict normalizationFuel resultType with
                    | nonAtomic => simp [hlookup, hspine, hatomic] at hinfer
                    | conversionFuelExhausted =>
                        simp [hlookup, hspine, hatomic] at hinfer
                    | atomic =>
                        simp [hlookup, hspine, hatomic] at hinfer
                        subst type
                        exact CheckedHasType.head hlookup (ih.2 _ _ _ _ hspine) hatomic
      · intro context headType arguments resultType hinfer
        cases arguments with
        | nil =>
            simp only [inferSpineFuel, CheckResult.ok.injEq] at hinfer
            subst resultType
            exact CheckedSpineHasType.nil
        | cons argument rest =>
            cases headType with
            | pi domain body =>
                simp only [inferSpineFuel] at hinfer
                cases hargument : inferNfFuel fuel context argument with
                | rejected => simp [hargument] at hinfer
                | conversionFuelExhausted => simp [hargument] at hinfer
                | ok actualType =>
                    cases hconversion :
                        conversionVerdict normalizationFuel actualType domain with
                    | normalFormsDiffer => simp [hargument, hconversion] at hinfer
                    | conversionFuelExhausted =>
                        simp [hargument, hconversion] at hinfer
                    | convertible =>
                        simp [hargument, hconversion] at hinfer
                        exact CheckedSpineHasType.cons
                          (ih.1 _ _ _ hargument) hconversion
                          (ih.2 _ _ _ _ hinfer)
            | sort => simp [inferSpineFuel] at hinfer
            | bvar index => simp [inferSpineFuel] at hinfer
            | lam domain body => simp [inferSpineFuel] at hinfer
            | app fn argument => simp [inferSpineFuel] at hinfer
end

mutual
/-- Simultaneous bounded completeness for the explicitly checkable judgments. -/
theorem inferFuel_complete : ∀ fuel,
    (∀ context term type,
      term.weight < fuel → CheckedHasType context term type →
        inferNfFuel fuel context term = .ok type) ∧
    (∀ context headType arguments resultType,
      Nf.listWeight arguments < fuel →
      CheckedSpineHasType context headType arguments resultType →
        inferSpineFuel fuel context headType arguments = .ok resultType) := by
  intro fuel
  induction fuel with
  | zero => constructor <;> intro <;> omega
  | succ fuel ih =>
      constructor
      · intro context term type hweight htype
        cases htype with
        | lam hbody =>
            simp only [Nf.weight] at hweight
            simp [inferNfFuel, ih.1 _ _ _ (by omega) hbody]
        | head hlookup hspine hatomic =>
            simp only [Nf.weight] at hweight
            simp [inferNfFuel, hlookup,
              ih.2 _ _ _ _ (by omega) hspine, hatomic]
      · intro context headType arguments resultType hweight htype
        cases htype with
        | nil => simp [inferSpineFuel]
        | cons hargument hconversion hrest =>
            simp only [Nf.listWeight] at hweight
            simp [inferSpineFuel,
              ih.1 _ _ _ (by omega) hargument, hconversion,
              ih.2 _ _ _ _ (by omega) hrest]
end

theorem inferNf_sound {context : Ctx} {term : Nf} {type : Expr}
    (hinfer : inferNf context term = .ok type) :
    CheckedHasType context term type :=
  (inferFuel_sound (term.weight + 1)).1 _ _ _ hinfer

theorem inferNf_complete {context : Ctx} {term : Nf} {type : Expr}
    (htype : CheckedHasType context term type) :
    inferNf context term = .ok type :=
  (inferFuel_complete (term.weight + 1)).1 _ _ _ (by omega) htype

/-- Apply one bounded conversion query while preserving its three distinct outcomes. -/
def matchTypeWithFuel (fuel : Nat) (actual expected : Expr) : CheckResult Unit :=
  match conversionVerdict fuel actual expected with
  | .convertible => .ok ()
  | .normalFormsDiffer => .rejected
  | .conversionFuelExhausted => .conversionFuelExhausted

/-- The root conversion query at its manifest-pinned fuel bound. -/
def matchType (actual expected : Expr) : CheckResult Unit :=
  matchTypeWithFuel normalizationFuel actual expected

theorem matchTypeWithFuel_sound {fuel : Nat} {actual expected : Expr}
    (hmatch : matchTypeWithFuel fuel actual expected = .ok ()) :
    Conv actual expected := by
  unfold matchTypeWithFuel at hmatch
  cases hverdict : conversionVerdict fuel actual expected <;>
    simp [hverdict] at hmatch
  exact conversionVerdict_sound hverdict

theorem matchType_sound {actual expected : Expr}
    (hmatch : matchType actual expected = .ok ()) : Conv actual expected := by
  exact matchTypeWithFuel_sound hmatch

/-- Deliver one completed argument through deterministic elaborator frames. -/
def deliver : Nf → List Frame → CheckResult Core
  | term, [] => .ok (.done term)
  | term, .lambda domain :: rest => deliver (.lam domain term) rest
  | term, .spine context head arguments body expected :: rest =>
      let arguments := arguments ++ [term]
      let application := Nf.head head arguments
      let nextType := Expr.subst0 term.erase body
      match conversionVerdict normalizationFuel nextType expected with
      | .convertible => deliver application rest
      | .conversionFuelExhausted => .conversionFuelExhausted
      | .normalFormsDiffer =>
          match nextType with
          | .pi domain nextBody =>
              .ok (prepare 0 context domain
                (.spine context head arguments nextBody expected :: rest))
          | _ => .rejected

/-- Begin the deterministic dependent spine for one selected head. -/
def startSpine (context : Ctx) (expected : Expr) (frames : List Frame)
    (head : Nat) (arguments : List Nf) : Expr → CheckResult Core
  | .pi domain body =>
      .ok (prepare 0 context domain
        (.spine context head arguments body expected :: frames))
  | headType =>
      match conversionVerdict normalizationFuel headType expected with
      | .convertible => deliver (.head head arguments) frames
      | .normalFormsDiffer => .rejected
      | .conversionFuelExhausted => .conversionFuelExhausted

/-- One classified beta-aware `Refine(hole, head)` elaborator transition. -/
def rawRefineResult (core : Core) (action : AtomicAction) : CheckResult Core :=
  match core with
  | .needHole hole context expected frames =>
      if action.hole != hole then .rejected
      else
        match ctxLookup context action.head with
        | none => .rejected
        | some headType => startSpine context expected frames action.head [] headType
  | _ => .rejected

/-- Interface view: exhaustion and rejection are both non-success, never acceptance. -/
def rawRefine? (core : Core) (action : AtomicAction) : Option Core :=
  (rawRefineResult core action).toOption

def rawRunResult : List AtomicAction → Core → CheckResult Core
  | [], core => .ok core
  | action :: rest, core =>
      match rawRefineResult core action with
      | .ok next => rawRunResult rest next
      | .rejected => .rejected
      | .conversionFuelExhausted => .conversionFuelExhausted

/-- Continue a trace from an already classified elaborator result. -/
def runFromResult (trace : List AtomicAction) : CheckResult Core → CheckResult Core
  | .ok core => rawRunResult trace core
  | .rejected => .rejected
  | .conversionFuelExhausted => .conversionFuelExhausted

theorem rawRunResult_append (first second : List AtomicAction) (core : Core) :
    rawRunResult (first ++ second) core =
      runFromResult second (rawRunResult first core) := by
  induction first generalizing core with
  | nil => rfl
  | cons action rest ih =>
      simp only [List.cons_append, rawRunResult]
      cases hstep : rawRefineResult core action with
      | rejected => rfl
      | conversionFuelExhausted => rfl
      | ok next => exact ih next

def rawRunAtomic (trace : List AtomicAction) (core : Core) : Option Core :=
  (rawRunResult trace core).toOption

/-- Independent terminal checking, including its classified conversion result. -/
def terminalResult (goal : Expr) : Core → CheckResult Nf
  | .done term =>
      match inferNf [] term with
      | .rejected => .rejected
      | .conversionFuelExhausted => .conversionFuelExhausted
      | .ok inferred =>
          match conversionVerdict normalizationFuel inferred goal with
          | .convertible => .ok term
          | .normalFormsDiffer => .rejected
          | .conversionFuelExhausted => .conversionFuelExhausted
  | _ => .rejected

def coreTerminal (goal : Expr) (core : Core) : Prop :=
  (terminalResult goal core).isOk = true

instance coreTerminalDecidable (goal : Expr) (core : Core) :
    Decidable (coreTerminal goal core) := by
  unfold coreTerminal
  infer_instance

def decodeResult (goal : Expr) (trace : List AtomicAction) : CheckResult Nf :=
  match rawRunResult trace (prepare 0 [] goal []) with
  | .ok core => terminalResult goal core
  | .rejected => .rejected
  | .conversionFuelExhausted => .conversionFuelExhausted

def decode (goal : Expr) (trace : List AtomicAction) : Option Nf :=
  (decodeResult goal trace).toOption

/-- Successful terminal checking exposes the finite evidence used by the checker. -/
theorem terminalResult_checked {goal : Expr} {core : Core} {term : Nf}
    (hterminal : terminalResult goal core = .ok term) :
    ∃ inferred,
      CheckedHasType [] term inferred ∧
        conversionVerdict normalizationFuel inferred goal = .convertible := by
  unfold terminalResult at hterminal
  cases core with
  | needHole hole context expected frames => simp at hterminal
  | needHead hole context expected frames => simp at hterminal
  | needSpine hole context expected frames head headType => simp at hterminal
  | finished finalTerm => simp at hterminal
  | done finalTerm =>
      cases hinfer : inferNf [] finalTerm with
      | rejected => simp [hinfer] at hterminal
      | conversionFuelExhausted => simp [hinfer] at hterminal
      | ok inferred =>
          cases hconversion : conversionVerdict normalizationFuel inferred goal with
          | normalFormsDiffer => simp [hinfer, hconversion] at hterminal
          | conversionFuelExhausted => simp [hinfer, hconversion] at hterminal
          | convertible =>
              simp [hinfer, hconversion] at hterminal
              subst term
              exact ⟨inferred, inferNf_sound hinfer, hconversion⟩

/-- Successful trace decoding exposes the same finite checker evidence. -/
theorem decodeResult_checked {goal : Expr} {trace : List AtomicAction} {term : Nf}
    (hdecode : decodeResult goal trace = .ok term) :
    ∃ inferred,
      CheckedHasType [] term inferred ∧
        conversionVerdict normalizationFuel inferred goal = .convertible := by
  unfold decodeResult at hdecode
  cases hrun : rawRunResult trace (prepare 0 [] goal []) with
  | rejected => simp [hrun] at hdecode
  | conversionFuelExhausted => simp [hrun] at hdecode
  | ok core => exact terminalResult_checked (by simpa [hrun] using hdecode)

/-- Accepted traces independently check as inhabitants in declarative beta statics. -/
theorem terminalResult_sound {goal : Expr} {core : Core} {term : Nf}
    (hterminal : terminalResult goal core = .ok term) :
    Mettapedia.GSLT.LanguageDef.PureBeta.HasType [] term goal := by
  unfold terminalResult at hterminal
  cases core with
  | needHole hole context expected frames => simp at hterminal
  | needHead hole context expected frames => simp at hterminal
  | needSpine hole context expected frames head headType => simp at hterminal
  | finished finalTerm => simp at hterminal
  | done finalTerm =>
      cases hinfer : inferNf [] finalTerm with
      | rejected => simp [hinfer] at hterminal
      | conversionFuelExhausted => simp [hinfer] at hterminal
      | ok inferred =>
          cases hconversion : conversionVerdict normalizationFuel inferred goal with
          | normalFormsDiffer => simp [hinfer, hconversion] at hterminal
          | conversionFuelExhausted => simp [hinfer, hconversion] at hterminal
          | convertible =>
              simp [hinfer, hconversion] at hterminal
              subst term
              exact Mettapedia.GSLT.LanguageDef.PureBeta.HasType.conv
                (checkedHasType_sound (inferNf_sound hinfer))
                (conversionVerdict_sound hconversion)

theorem decodeResult_sound {goal : Expr} {trace : List AtomicAction} {term : Nf}
    (hdecode : decodeResult goal trace = .ok term) :
    Mettapedia.GSLT.LanguageDef.PureBeta.HasType [] term goal := by
  unfold decodeResult at hdecode
  cases hrun : rawRunResult trace (prepare 0 [] goal []) with
  | rejected => simp [hrun] at hdecode
  | conversionFuelExhausted => simp [hrun] at hdecode
  | ok core => exact terminalResult_sound (by simpa [hrun] using hdecode)

/-- The complete atomic successor remains a deterministic elaborator effect. -/
theorem rawRefine_successor_deterministic {core first second : Core}
    {action : AtomicAction}
    (hfirst : rawRefine? core action = some first)
    (hsecond : rawRefine? core action = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

/-! ## Executable boundary fixtures -/

def betaIdentityGoal : Expr :=
  .pi .sort (.app (.lam .sort (.bvar 0)) (.bvar 0))

example : matchType (.app (.lam .sort (.bvar 0)) .sort) .sort = .ok () := by decide

example : matchType (.bvar 0) .sort = .rejected := by decide

example : matchTypeWithFuel 8 wrongMotiveBetaFixture .sort = .rejected := by decide

example : matchTypeWithFuel 1 fuelExhaustionFixture fuelExhaustionFixture =
    .conversionFuelExhausted := by decide

#print axioms checkedHasType_sound
#print axioms matchTypeWithFuel_sound
#print axioms inferNf_sound
#print axioms terminalResult_checked
#print axioms decodeResult_checked
#print axioms terminalResult_sound
#print axioms decodeResult_sound
#print axioms rawRefine_successor_deterministic

end Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement
