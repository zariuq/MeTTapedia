import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedReduction

/-!
# Separating examples for the corrected MeTTa-calculus step

The examples are computed by the kernel; the exclusion of the capturing
reduct under the variable convention is proved by induction on derivations
(`capture_not_conventional_step`). The old executable is
`MeTTaCalculus.step` with the unifier `unifyPattern?`; the corrected one is
`Corrected.cstep` with `Corrected.unify`.

* An occurs-check defeated by a triangular binding list: the old unifier
  accepts a pair of patterns that has no unifier, and the old step fires that
  COMM. The corrected unifier refuses it, and no substitution unifies it.
* The triangular one-pass reading: with the two inputs' variables apart, the
  old step reads `@Y | 0` where every unifier reads `@a | 0`.
* Capture: the canary reduces to `@0 | a`, and so does its alpha-variant. The
  literal relational rule `ReflectionClosure.Step` admits the capturing reduct
  even with a principal unifier and alpha-equivalence; the corrected relational
  semantics does not, under the variable convention alone.
* No renaming: `for(X <- @0)X | for(f(X) <- @0)0` now reduces.
* Nested reflection now has a result, and the naive reading's COMM-only
  lookahead misses that step of the corrected relational semantics.
* The manuscript's alpha side condition alone would identify processes with
  different reducts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm (psubst PSubst)

def v (name : String) : Pattern := .fvar name
def a : Pattern := .apply "a" []
def f (args : List Pattern) : Pattern := .apply "f" args
def g (arg : Pattern) : Pattern := .apply "g" [arg]

/-! ## The old occurs check is defeated by triangular bindings -/

/-- `f(X, g(Z), Z, X)` against `f(f(Y), Y, W, W)`: the variables of the two
patterns are apart, and the equations force `X = f(g(X))`. -/
def cycleLeft : Pattern := f [v "X", g (v "Z"), v "Z", v "X"]
def cycleRight : Pattern := f [f [v "Y"], v "Y", v "W", v "W"]

theorem old_unifier_accepts_cycle :
    unifyPattern? cycleLeft cycleRight =
      some [("W", f [v "Y"]), ("Z", v "W"), ("Y", g (v "Z")), ("X", f [v "Y"])] := by
  decide +kernel

theorem corrected_unifier_refuses_cycle : Corrected.unify cycleLeft cycleRight = none := by
  decide +kernel

theorem cycle_has_no_unifier : ¬ ∃ τ, psubst τ cycleLeft = psubst τ cycleRight :=
  (Corrected.unify_eq_none_iff cycleLeft cycleRight).mp corrected_unifier_refuses_cycle

/-- The old step fires a COMM whose patterns have no unifier at all. -/
def cycleComm : Proc := par (pFor cycleLeft demoChan pZero) (pFor cycleRight demoChan pZero)

theorem old_step_fires_without_unifier : step cycleComm ≠ [] := by decide +kernel

theorem corrected_step_refuses_without_unifier : Corrected.cstep cycleComm = [] := by decide +kernel

/-! ## Triangular bindings read in one pass -/

/-- `for(f(X,X) <- @0) X | for(f(Y,a) <- @0) 0`: the inputs' variables are apart. -/
def triangularApart : Proc :=
  par (pFor (f [v "X", v "X"]) demoChan (v "X")) (pFor (f [v "Y", a]) demoChan pZero)

theorem old_unifier_triangular_apart :
    unifyPattern? (f [v "X", v "X"]) (f [v "Y", a]) = some [("Y", a), ("X", v "Y")] := by
  decide +kernel

theorem old_step_reads_unbound : par (nQuote (v "Y")) pZero ∈ step triangularApart := by decide +kernel

theorem corrected_unifier_final :
    Corrected.unify (f [v "X", v "X"]) (f [v "Y", a]) = some [("X", a), ("Y", a)] := by
  decide +kernel

theorem corrected_triangular_apart : Corrected.cstep triangularApart = [par (nQuote a) pZero] := by
  decide +kernel

/-- Every substitution unifying the patterns reads the continuation `X` as `@a`. -/
theorem every_unifier_reads_a (τ : PSubst)
    (solves : psubst τ (f [v "X", v "X"]) = psubst τ (f [v "Y", a])) :
    psubst τ (v "X") = a := by
  simp only [f, v, a, psubst, psubst.psubstList, Pattern.apply.injEq, List.cons.injEq, true_and,
    and_true] at solves
  exact solves.2

/-- R17's triangular source shares the name `Y` between the two inputs. Opened
apart, its first input's `X` meets the second input's `Y`, which nothing binds:
the reduct reads a fresh residual name. -/
def triangularShared : Proc :=
  par (pFor (f [v "X", v "Y"]) demoChan (v "X")) (pFor (f [v "Y", a]) demoChan pZero)

theorem corrected_triangular_shared :
    Corrected.cstep triangularShared = [par (nQuote (v "###")) pZero] := by
  decide +kernel

def triangularRenamed : Proc :=
  par (pFor (f [v "X", v "W"]) demoChan (v "X")) (pFor (f [v "Y", a]) demoChan pZero)

/-- Renaming the first input's `Y` is an instance of the manuscript's alpha
rule; the corrected step gives both sources the same reduct. -/
theorem triangular_shared_alpha : Corrected.Alpha triangularShared triangularRenamed := by
  have pat : Corrected.rename (Corrected.swapTo "Y" "W") (f [v "X", v "Y"]) = f [v "X", v "W"] := by
    decide +kernel
  have body : Corrected.rename (Corrected.swapTo "Y" "W") (v "X") = v "X" := by decide +kernel
  have rule := Corrected.AlphaRule.rename (f [v "X", v "Y"]) demoChan (v "X") "Y" "W"
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [pat, body] at rule
  exact Corrected.Alpha.collection .hashBag [] [pFor (f [v "Y", a]) demoChan pZero] none (.rule rule)

theorem triangular_same_reducts : Corrected.cstep triangularShared = Corrected.cstep triangularRenamed :=
  Corrected.cstep_alpha_rule_invariant triangular_shared_alpha

/-- The old step distinguishes the two alpha-variants. -/
theorem old_step_triangular_variants :
    par (nQuote (v "Y")) pZero ∈ step triangularShared ∧
      par (nQuote (v "Y")) pZero ∈ step triangularRenamed ∧
      par (nQuote a) pZero ∉ step triangularShared := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Capture -/

/-- `for(a1 <- @0) a1 | for(0 <- @0) a`, the canary with its bound name renamed. -/
def canaryRenamed : Proc := par (pFor (v "a1") demoChan (v "a1")) (pFor pZero demoChan (v "a"))

theorem corrected_canary : Corrected.cstep demoCommSource = [par (nQuote pZero) (v "a")] := by
  decide +kernel

theorem corrected_canary_renamed : Corrected.cstep canaryRenamed = [par (nQuote pZero) (v "a")] := by
  decide +kernel

theorem canary_alpha : Corrected.Alpha demoCommSource canaryRenamed := by
  have rule := Corrected.AlphaRule.rename (v "a") demoChan (v "a") "a" "a1"
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have pat : Corrected.rename (Corrected.swapTo "a" "a1") (v "a") = v "a1" := by decide +kernel
  rw [pat] at rule
  exact Corrected.Alpha.collection .hashBag [] [pFor pZero demoChan (v "a")] none (.rule rule)

/-- The old canary target `@0 | @0` is not alpha-equivalent to the corrected reduct. -/
theorem capture_not_alpha : ¬ Corrected.AlphaEq demoCommCapture (par (nQuote pZero) (v "a")) := by
  decide +kernel

/-- The literal relational rule `ReflectionClosure.Step`, even with a principal
unifier and alpha-equivalence as its premises, relates the canary to the
capturing reduct `@0 | @0`: what excludes the capture is the variable
convention, not the choice of unifier. -/
theorem literal_rule_admits_capture :
    ReflectionClosure.Step (fun t u bs => Corrected.Principal t u bs) Corrected.AlphaEq
      demoCommSource demoCommCapture := by
  have found : Corrected.unify (v "a") pZero = some [("a", pZero)] := by decide +kernel
  have root := ReflectionClosure.Step.comm (unifies := fun t u bs => Corrected.Principal t u bs)
    (equivalent := Corrected.AlphaEq) (v "a") pZero demoChan (v "a") (v "a") [("a", pZero)]
    (Corrected.unify_principal found)
  have target :
      par (applyDot [("a", pZero)] (v "a")) (applyDot [("a", pZero)] (v "a")) = demoCommCapture := by
    decide +kernel
  rw [target] at root
  exact root

/-- The capturing reduct `@0 | @0`, which the literal relational rule admits
(`literal_rule_admits_capture`), is not a step of the corrected relational
semantics on the closing fragment. -/
theorem capture_not_closing_step : ¬ Corrected.Step Corrected.closing demoCommSource demoCommCapture := by
  intro relational
  obtain ⟨Q', member, alpha⟩ := Corrected.cstep_complete relational
  rw [corrected_canary, List.mem_singleton] at member
  subst member
  exact capture_not_alpha alpha.symm

/-- A process whose closed form is a guard has no step. -/
theorem step_source_not_guard {admit : Corrected.Admission} {source target : Pattern}
    (step : Corrected.Step admit source target) (t x k : Pattern) :
    Corrected.close source ≠ pFor t x k := by
  induction step with
  | comm t u x A B bs _ _ =>
      intro guard
      unfold Corrected.close at guard
      rw [Corrected.closeIn_par] at guard
      simp [par, pPar, pFor] at guard
  | parallel surrounding _ _ =>
      intro guard
      unfold Corrected.close at guard
      rw [Corrected.closeIn_par] at guard
      simp [par, pPar, pFor] at guard
  | congruence before _ _ ih =>
      exact fun guard => ih ((show Corrected.close _ = Corrected.close _ from before).symm.trans guard)
  | reflect x _ _ =>
      intro guard
      unfold Corrected.close at guard
      rw [Corrected.closeIn_pReflect] at guard
      simp [pReflect, pFor] at guard

/-- Only the inert process closes to the inert process. -/
theorem eq_pZero_of_closeIn {env : List (List String)} {u : Pattern}
    (closed : Corrected.closeIn env u = pZero) : u = pZero := by
  cases u with
  | fvar x =>
      unfold Corrected.closeIn at closed
      split at closed <;> simp [Corrected.boundCode, pZero] at closed
  | bvar n => simp [Corrected.closeIn, pZero] at closed
  | apply c args =>
      cases args with
      | nil =>
          simp only [Corrected.closeIn, pZero, Pattern.apply.injEq] at closed
          rw [closed.1]; rfl
      | cons a rest =>
          simp only [Corrected.closeIn, pZero, Pattern.apply.injEq] at closed
          obtain ⟨rfl, emptied⟩ := closed
          simp [Corrected.closeList] at emptied
  | lambda nm body => simp [Corrected.closeIn, pZero] at closed
  | multiLambda n nms body => simp [Corrected.closeIn, pZero] at closed
  | subst body repl => simp [Corrected.closeIn, pZero] at closed
  | collection ct elems rest => simp [Corrected.closeIn, pZero] at closed

/-- Only a free variable closes to a free variable. -/
theorem eq_fvar_of_closeIn {env : List (List String)} {B : Pattern} {name : String}
    (closed : Corrected.closeIn env B = .fvar name) : B = .fvar name := by
  cases B with
  | fvar x =>
      unfold Corrected.closeIn at closed
      split at closed
      · simp [Corrected.boundCode] at closed
      · exact closed
  | bvar n => simp [Corrected.closeIn] at closed
  | apply c args => simp [Corrected.closeIn] at closed
  | lambda nm body => simp [Corrected.closeIn] at closed
  | multiLambda n nms body => simp [Corrected.closeIn] at closed
  | subst body repl => simp [Corrected.closeIn] at closed
  | collection ct elems rest => simp [Corrected.closeIn] at closed

/-- Every relational step from the canary, under the variable convention,
keeps the second continuation's free `a`: the unifier's keys are pattern
variables, and the convention keeps them out of that continuation. -/
theorem canary_steps_keep_a {source target : Pattern}
    (step : Corrected.Step Corrected.conventional source target) :
    Corrected.close source = Corrected.close demoCommSource →
      Corrected.close target ≠ Corrected.close demoCommCapture := by
  induction step with
  | comm t u x A B bs principal admitted =>
      intro same
      have canaryClosed : Corrected.close demoCommSource =
          par (Corrected.close (pFor (v "a") demoChan (v "a")))
            (pFor pZero demoChan (v "a")) := by decide +kernel
      unfold Corrected.close at same canaryClosed
      rw [canaryClosed, Corrected.closeIn_par, Corrected.closeIn_pFor [] u x B] at same
      simp only [par, pPar, pFor, Pattern.collection.injEq, List.cons.injEq, Pattern.apply.injEq,
        and_true, true_and] at same
      obtain ⟨-, closedU, -, closedB⟩ := same
      have uZero := eq_pZero_of_closeIn closedU
      subst uZero
      have bA := eq_fvar_of_closeIn closedB
      subst bA
      have notKey : ∀ entry ∈ bs, entry.1 ≠ "a" := by
        intro entry member same
        have key := principal.keys entry member
        rw [same] at key
        have inT : "a" ∈ Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.pvars t := by
          simpa [pZero, Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.pvars,
            Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.pvars.pvarsList] using key
        exact admitted.leftOutside "a" inT (by
          simp [Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm.pvars])
      have kept : applyDot bs (.fvar "a") = .fvar "a" := by
        have none : (dotBindings bs).find? (fun entry => entry.1 == "a") = none := by
          rw [List.find?_eq_none]
          intro entry member
          simp only [dotBindings, List.mem_map] at member
          obtain ⟨original, inBs, rfl⟩ := member
          simpa using notKey original inBs
        simp [applyDot, Mettapedia.OSLF.MeTTaIL.Match.applyBindings, none]
      intro captured
      unfold Corrected.close at captured
      rw [Corrected.closeIn_par, kept] at captured
      have : Corrected.closeIn [] demoCommCapture =
          par (nQuote pZero) (nQuote pZero) := by decide +kernel
      rw [this] at captured
      simp [par, pPar, nQuote, Corrected.closeIn, Corrected.lookupBound] at captured
  | parallel surrounding inner _ =>
      intro same
      unfold Corrected.close at same
      have canaryClosed : Corrected.closeIn [] demoCommSource =
          par (Corrected.closeIn [] (pFor (v "a") demoChan (v "a")))
            (Corrected.closeIn [] (pFor pZero demoChan (v "a"))) := by decide +kernel
      rw [canaryClosed, Corrected.closeIn_par] at same
      simp only [par, pPar, Pattern.collection.injEq, List.cons.injEq, and_true, true_and] at same
      rw [Corrected.closeIn_pFor] at same
      exact absurd same.1 (step_source_not_guard inner _ _ _)
  | congruence before _ after ih =>
      intro same captured
      exact ih ((show Corrected.close _ = Corrected.close _ from before).symm.trans same)
        ((show Corrected.close _ = Corrected.close _ from after).trans captured)
  | reflect x _ _ =>
      intro same
      unfold Corrected.close at same
      rw [Corrected.closeIn_pReflect] at same
      have canaryClosed : Corrected.closeIn [] demoCommSource =
          par (Corrected.closeIn [] (pFor (v "a") demoChan (v "a")))
            (Corrected.closeIn [] (pFor pZero demoChan (v "a"))) := by decide +kernel
      rw [canaryClosed] at same
      simp [pReflect, par, pPar] at same

/-- **The capturing reduct is not a step of the corrected relational
semantics**, under the variable convention alone, not only on the closing
fragment. -/
theorem capture_not_conventional_step :
    ¬ Corrected.Step Corrected.conventional demoCommSource demoCommCapture :=
  fun step => canary_steps_keep_a step rfl rfl

/-! ## No renaming -/

/-- `for(X <- @0)X | for(f(X) <- @0)0`, with one name shared by both inputs. -/
def sharedName : Proc := par (pFor (v "X") demoChan (v "X")) (pFor (f [v "X"]) demoChan pZero)

theorem old_step_refuses_shared : step sharedName = [] := by decide +kernel

/-- Opened apart, the first input's `X` receives `f` of the second input's
variable, which stays a fresh residual name. -/
theorem corrected_shared : Corrected.cstep sharedName = [par (nQuote (f [v "##"])) pZero] := by
  decide +kernel

/-! ## Nested reflection -/

/-- `@0?(@0?(for(a <- @0)a | for(0 <- @0)a))`: a reflection whose premise is
itself a reflection. -/
def nestedSource : Proc := pReflect demoChan demoReflectSource

/-- The naive reading's COMM-only lookahead has no nested result. -/
theorem old_step_no_nested : step nestedSource = [] := by decide +kernel

/-- The corrected step has the nested reflection result, with the
capture-avoiding inner reduct. -/
theorem corrected_nested :
    Corrected.cstep nestedSource =
      [pFor (tProc (pFor (tProc (par (nQuote pZero) (v "a"))) demoChan pZero)) demoChan pZero] := by
  decide +kernel

theorem corrected_nested_sound :
    Corrected.Step Corrected.conventional nestedSource
      (pFor (tProc (pFor (tProc (par (nQuote pZero) (v "a"))) demoChan pZero)) demoChan pZero) :=
  Corrected.cstep_sound (by decide +kernel) (by rw [corrected_nested]; exact List.mem_singleton_self _)

/-- The naive reading's COMM-only lookahead does not implement recursive
reflection: it misses a step of the corrected relational semantics. -/
theorem naive_step_misses_nested_reflection :
    ¬ ∀ source target, Corrected.Step Corrected.conventional source target → target ∈ step source := by
  intro simulation
  have result := simulation _ _ corrected_nested_sound
  rw [old_step_no_nested] at result
  exact List.not_mem_nil result

/-! ## The manuscript's alpha side condition -/

/-- `for(f(y, z) <- @0)0` renamed by `{z/y}` under the manuscript's side
condition alone (`z ∉ FN(0)`) becomes `for(f(z, z) <- @0)0`. -/
def twoVariables : Proc := pFor (f [v "y", v "z"]) demoChan pZero
def merged : Proc := pFor (f [v "z", v "z"]) demoChan pZero

def partner : Proc := pFor (f [a, .apply "b" []]) demoChan pZero

theorem alpha_side_condition_needed :
    ¬ Corrected.AlphaEq twoVariables merged ∧
      Corrected.cstep (par twoVariables partner) = [par pZero pZero] ∧
      Corrected.cstep (par merged partner) = [] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Agreement where the naive reading is right -/

/-- Patterns that do not unify: neither step fires. -/
theorem both_refuse_blocked : step demoBlocked = [] ∧ Corrected.cstep demoBlocked = [] := by
  constructor <;> decide +kernel

/-- A capture-free reflection: both steps give the same listener. -/
def captureFreeReflect : Proc :=
  pReflect demoChan (par (pFor (v "a") demoChan (v "a")) (pFor pZero demoChan pZero))

theorem both_agree_capture_free :
    Corrected.cstep captureFreeReflect = [pFor (tProc (par (nQuote pZero) pZero)) demoChan pZero] ∧
      pFor (tProc (par (nQuote pZero) pZero)) demoChan pZero ∈ step captureFreeReflect := by
  constructor <;> decide +kernel

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected.Controls
