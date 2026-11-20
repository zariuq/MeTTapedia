import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.CoreLaws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Acceptance

/-!
# The weakening law for result types

**The law** (`KeepsWeakening`). Along the line of computation types, `Number` and `Bool`, then
`Proc`, then `%Undefined%` and type variables (`LineWeaker`), replacing a function's declared
result type by a weaker one changes no answer of a run that refused nothing: the same fuel gives
the same answers.

* `weakening`: the law holds for every design in which held parameters run under both result
  types alike (`heldRunsAt D (D.heldUnder R) = heldRunsAt D (D.heldUnder R')`). The elaborations
  of the two programs then differ only in the dropped result check (`progWeaker_setResult`), and
  the core's `exec_weaker` does the rest.
* `keepsWeakening_of`: hence every design that does not hold under `Proc` while running under the
  other types, and every design in which held parameters never run, keeps the law:
  Hyperon Experimental, by-name, code value and the Prime draft (`he_keeps_weakening`, ...).
* `hybrid_breaks_weakening`: the withdrawn hybrid breaks it on `(: g (-> Atom R)) (= (g $x) $x)`,
  `!(g (f a))`: `5` under `Number`, `(f a)` under `Proc`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Acceptance

namespace Weakening

/-- Change the declared result type of a function (an undeclared function stays undeclared). -/
def withResult (R : Ty) (fn : Fn) : Fn :=
  match fn.decl with
  | some (ps, _) => { fn with decl := some (ps, R) }
  | none => fn

/-- Change the declared result type of every function with this head. -/
def setResult (P : SProg) (g : String) (R : Ty) : SProg :=
  P.map fun fn => if fn.head = g then withResult R fn else fn

/-- The line of computation types: `Number` and `Bool`, then `Proc`, then `%Undefined%` and type
variables. -/
def lineRank : Ty → Option Nat
  | .number => some 0
  | .bool => some 0
  | .proc => some 1
  | .undef => some 2
  | .tvar => some 2
  | _ => none

/-- `R'` is `R` or weaker, on the line of computation types. -/
structure LineWeaker (R R' : Ty) : Prop where
  rank : ∃ a b, lineRank R = some a ∧ lineRank R' = some b ∧ a ≤ b
  check : R'.check = none ∨ R'.check = R.check

/-- A query's run in a design's elaboration of a program. -/
def runQ (D : Design) (P : SProg) (n : Nat) (q : Atom) : Option (List Ans) :=
  exec (elabProg D P) n (.comp [] (elabQuery D (modesOf P) q))

theorem modesOf_map (P : SProg) (f : Fn → Fn) (hhead : ∀ fn, (f fn).head = fn.head)
    (harity : ∀ fn, (f fn).arity = fn.arity) (hparams : ∀ fn, (f fn).params = fn.params) :
    modesOf (P.map f) = modesOf P := by
  funext h n
  unfold modesOf
  rw [List.find?_map]
  have hp : ((fun fn : Fn => fn.head == h && fn.arity == n) ∘ f) =
      fun fn : Fn => fn.head == h && fn.arity == n := by
    funext fn
    simp only [Function.comp_apply, hhead, harity]
  rw [hp]
  cases P.find? (fun fn : Fn => fn.head == h && fn.arity == n) with
  | none => rfl
  | some fn => simp [hparams]

theorem withResult_head (R : Ty) (fn : Fn) : (withResult R fn).head = fn.head := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => rfl

theorem withResult_arity (R : Ty) (fn : Fn) : (withResult R fn).arity = fn.arity := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => obtain ⟨ps, r⟩ := p; rfl

theorem withResult_params (R : Ty) (fn : Fn) : (withResult R fn).params = fn.params := by
  obtain ⟨h, decl, eqns⟩ := fn
  cases decl with
  | none => rfl
  | some p => obtain ⟨ps, r⟩ := p; rfl

theorem modesOf_setResult (P : SProg) (g : String) (R : Ty) :
    modesOf (setResult P g R) = modesOf P := by
  apply modesOf_map
  · intro fn; split <;> simp [withResult_head]
  · intro fn; split <;> simp [withResult_arity]
  · intro fn; split <;> simp [withResult_params]

theorem elabBody_line (D : Design) (ms : Modes) (held : List String) {R : Ty} {a : Nat}
    (hR : lineRank R = some a) (body : Atom) :
    elabBody D ms held R body = elabC D ms held (heldRunsAt D (D.heldUnder R)) true body := by
  cases R <;> simp_all [lineRank, elabBody]

theorem defWeaker_withResult (D : Design) (ms : Modes) {R R' : Ty} (line : LineWeaker R R')
    (same : heldRunsAt D (D.heldUnder R) = heldRunsAt D (D.heldUnder R')) (fn : Fn) :
    DefWeaker (elabFn D ms (withResult R fn)) (elabFn D ms (withResult R' fn)) := by
  obtain ⟨⟨a, b, ha, hb, _⟩, hcheck⟩ := line
  unfold withResult
  cases hd : fn.decl with
  | none => exact DefWeaker.refl _
  | some p =>
      obtain ⟨ps, r⟩ := p
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · simp only [elabFn, Fn.params, Fn.result]
        apply List.map_congr_left
        intro e _
        rw [elabBody_line D ms _ ha, elabBody_line D ms _ hb, same]
      · simpa [elabFn, Fn.result] using hcheck

theorem forall2_setResult (D : Design) (ms : Modes) {R R' : Ty} (line : LineWeaker R R')
    (same : heldRunsAt D (D.heldUnder R) = heldRunsAt D (D.heldUnder R')) (g : String) :
    ∀ P : SProg, List.Forall₂ DefWeaker ((setResult P g R).map (elabFn D ms))
      ((setResult P g R').map (elabFn D ms))
  | [] => .nil
  | fn :: rest => by
      show List.Forall₂ DefWeaker
        (elabFn D ms (if fn.head = g then withResult R fn else fn) ::
          (setResult rest g R).map (elabFn D ms))
        (elabFn D ms (if fn.head = g then withResult R' fn else fn) ::
          (setResult rest g R').map (elabFn D ms))
      refine .cons ?_ (forall2_setResult D ms line same g rest)
      by_cases h : fn.head = g
      · rw [if_pos h, if_pos h]
        exact defWeaker_withResult D ms line same fn
      · rw [if_neg h, if_neg h]
        exact DefWeaker.refl _

theorem progWeaker_setResult (D : Design) {R R' : Ty} (line : LineWeaker R R')
    (same : heldRunsAt D (D.heldUnder R) = heldRunsAt D (D.heldUnder R')) (P : SProg)
    (g : String) :
    ProgWeaker (elabProg D (setResult P g R)) (elabProg D (setResult P g R')) := by
  refine ⟨?_, ?_⟩
  · show elabQuery D (modesOf (setResult P g R')) = elabQuery D (modesOf (setResult P g R))
    rw [modesOf_setResult, modesOf_setResult]
  · show List.Forall₂ DefWeaker ((setResult P g R).map (elabFn D (modesOf (setResult P g R))))
      ((setResult P g R').map (elabFn D (modesOf (setResult P g R'))))
    rw [modesOf_setResult, modesOf_setResult]
    exact forall2_setResult D (modesOf P) line same g P

/-- **Weakening a result type** changes no run that refused nothing, in every design where held
parameters run alike under the two types. -/
theorem weakening (D : Design) {R R' : Ty} (line : LineWeaker R R')
    (same : heldRunsAt D (D.heldUnder R) = heldRunsAt D (D.heldUnder R')) (P : SProg)
    (g : String) (q : Atom) (n : Nat) (L : List Ans)
    (strong : runQ D (setResult P g R) n q = some L) (noRefusal : allVal L = true) :
    runQ D (setResult P g R') n q = some L := by
  unfold runQ at strong ⊢
  rw [modesOf_setResult] at strong ⊢
  exact exec_weaker (progWeaker_setResult D line same P g) n _ L strong noRefusal

/-- The weakening law, for a design. -/
def KeepsWeakening (D : Design) : Prop :=
  ∀ (P : SProg) (g : String) (R R' : Ty) (q : Atom) (n : Nat) (L : List Ans), LineWeaker R R' →
    runQ D (setResult P g R) n q = some L → allVal L = true → runQ D (setResult P g R') n q = some L

theorem heldUnder_line (D : Design) (hp : D.holdsUnderProc = false) {R : Ty} {a : Nat}
    (hR : lineRank R = some a) : D.heldUnder R = true := by
  cases R <;> simp_all [lineRank, Design.heldUnder]

/-- Designs that run held parameters under every computation type alike, or never, keep the law. -/
theorem keepsWeakening_of (D : Design) (h : D.holdsUnderProc = false ∨ D.held = .never) :
    KeepsWeakening D := by
  intro P g R R' q n L line strong noRefusal
  apply weakening D line _ P g q n L strong noRefusal
  rcases h with hp | hn
  · obtain ⟨⟨a, b, ha, hb, _⟩, _⟩ := line
    rw [heldUnder_line D hp ha, heldUnder_line D hp hb]
  · funext r
    simp [heldRunsAt, hn]

theorem he_keeps_weakening : KeepsWeakening he := keepsWeakening_of he (.inl rfl)
theorem byName_keeps_weakening : KeepsWeakening byName := keepsWeakening_of byName (.inl rfl)
theorem codeValue_keeps_weakening : KeepsWeakening codeValue :=
  keepsWeakening_of codeValue (.inl rfl)
theorem primeToday_keeps_weakening : KeepsWeakening primeToday :=
  keepsWeakening_of primeToday (.inl rfl)

/-- `Number` to `Proc` is a weakening. -/
theorem number_proc : LineWeaker .number .proc := ⟨⟨0, 1, rfl, rfl, by omega⟩, .inl rfl⟩

/-- `Proc` to `%Undefined%` is a weakening. -/
theorem proc_undef : LineWeaker .proc .undef := ⟨⟨1, 2, rfl, rfl, by omega⟩, .inl rfl⟩

/-- `Number` to `%Undefined%` is a weakening. -/
theorem number_undef : LineWeaker .number .undef := ⟨⟨0, 2, rfl, rfl, by omega⟩, .inl rfl⟩

/-- The weakening law's hypothesis is met (the law is not vacuous): the held identity under
`Number` runs `(f a)` to `5` with no refusal, in the by-name design, and the law carries it to
`Proc` and `%Undefined%`. -/
theorem byName_witness :
    runQ byName (setResult (rangeProg .number) "g" .number) F qRange =
        some [(.val (N 5), ["g", "f"])] ∧
      allVal [(.val (N 5), ["g", "f"])] = true ∧
      runQ byName (setResult (rangeProg .number) "g" .proc) F qRange =
        some [(.val (N 5), ["g", "f"])] ∧
      runQ byName (setResult (rangeProg .number) "g" .undef) F qRange =
        some [(.val (N 5), ["g", "f"])] := by
  decide +kernel

/-- **The withdrawn hybrid breaks the weakening law**: `5` under `Number`, `(f a)` under `Proc`. -/
theorem hybrid_breaks_weakening : ¬ KeepsWeakening hybrid := by
  intro h
  have strong : runQ hybrid (setResult (rangeProg .number) "g" .number) F qRange =
      some [(.val (N 5), ["g", "f"])] := by decide +kernel
  have weak := h (rangeProg .number) "g" .number .proc qRange F _ number_proc strong (by decide)
  have actual : runQ hybrid (setResult (rangeProg .number) "g" .proc) F qRange =
      some [(.val callFA, ["g"])] := by decide +kernel
  rw [actual] at weak
  exact absurd weak (by decide +kernel)

end Weakening

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
