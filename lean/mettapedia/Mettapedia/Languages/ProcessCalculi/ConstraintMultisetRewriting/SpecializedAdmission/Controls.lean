import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Correctness

/-!
# Controls

* **Micromath's `substitute1`** (four reads whose side conditions are repeated locals, one make):
  admitted on four theorems that meet the side conditions, with the theorem it derives made under
  the next identity; refused as unsolvable when one side condition fails.
* **Guards**: an absence whose pattern has a guard-only local refuses when some present label
  matches it and admits otherwise; a count of a determined pattern; a fresh name in a make.
* **Planted faults the theorems forbid**:
  - `skipRepeated`: the program without the equality tests of repeated locals admits the failing
    `substitute1`, while the step refuses it (`skipRepeated_forbidden`);
  - `takeEarly`: the program that takes before deciding the guards refuses with the state changed,
    while a refusal of the specialized program changes nothing (`takeEarly_forbidden`).
* **Rules just outside the class** are handed to the generic route: a local left unbound in a
  make, a told disequation, a host guard; and an in-class rule at a frame with a variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Controls

open Tm

/-- Micromath's theorem fact `thm(out, f, x, y)`; symbol `0` has arity 4. -/
def thm (a b c d : Tm) : Tm := .app 0 [a, b, c, d]

/-- `substitute1` of `micromath.tcs`, with its locals numbered as the reader numbers them:
`X T U W U1 A B W1 X1` are `0 .. 8`. -/
def substitute1 : Rule where
  nparams := 0
  fresh := 0
  takes := []
  reads := [thm (loc 0) (loc 1) (loc 2) (loc 3), thm (loc 4) (loc 2) (loc 5) (loc 6),
    thm (loc 7) (loc 3) (loc 5) (loc 6), thm (loc 8) (loc 0) (loc 5) (loc 6)]
  makes := [thm (loc 8) (loc 1) (loc 4) (loc 7)]
  tells := []
  aparts := []
  guards := []

/-- Four theorems that meet the side conditions (symbols are codes `10 .. 18`). -/
def good : St where
  vars := 0
  diseqs := 0
  names := 2
  nextId := 5
  present := [⟨1, thm (code 10) (code 11) (code 12) (code 13)⟩, ⟨2, thm (code 14) (code 12) (code 15) (code 16)⟩,
    ⟨3, thm (code 17) (code 13) (code 15) (code 16)⟩, ⟨4, thm (code 18) (code 10) (code 15) (code 16)⟩]

/-- The same, with the second premise over `(a, a)` instead of `(a, b)`. -/
def bad : St := { good with
  present := [⟨1, thm (code 10) (code 11) (code 12) (code 13)⟩, ⟨2, thm (code 14) (code 12) (code 15) (code 15)⟩,
    ⟨3, thm (code 17) (code 13) (code 15) (code 16)⟩, ⟨4, thm (code 18) (code 10) (code 15) (code 16)⟩] }

def premises : Ctx := ⟨[], [1, 2, 3, 4]⟩

theorem substitute1_inClass : InClass substitute1 := (inClassB_iff _).mp (by decide +kernel)

/-- Positive: admitted; the derived theorem `thm(x1, t, u1, w1)` is made with identity `5`. -/
example : ((compile substitute1).admits premises good).1 = .admitted := by decide +kernel
example : (compile substitute1).fire premises good =
    (.admitted,
      { good with
        nextId := 6
        present := good.present ++ [⟨5, thm (code 18) (code 11) (code 14) (code 17)⟩] }, [5]) := by
  decide +kernel

/-- Negative: refused as unsolvable, and the state is unchanged. -/
example : (compile substitute1).fire premises bad = (.refused .unsolvable, bad, []) := by decide +kernel

/-- The step's verdict on `bad`, read off the theorem. -/
theorem bad_refused (host : String → List Tm → Prop) :
    RefVerdict substitute1 bad [] [1, 2, 3, 4] host (.refused .unsolvable) := by
  have h := (specialized_admission substitute1 substitute1_inClass bad [] [1, 2, 3, 4] host).1
  have hv : ((compile substitute1).admits ⟨[], [1, 2, 3, 4]⟩ bad).1 = .refused .unsolvable := by decide +kernel
  rw [hv] at h
  exact h

/-! ## Planted faults -/

/-- Fault 1 of the C specializer's list: skip the equality of a repeated local. -/
def skipRepeated (P : Prog) : Prog :=
  { P with checks := P.checks.filter fun i => match i with
      | .test (.eqReg _ _) .unsolvable => false
      | _ => true }

theorem skipRepeated_admits_bad :
    ((skipRepeated (compile substitute1)).admits premises bad).1 = .admitted := by decide +kernel

/-- **The theorem forbids fault 1**: its verdict on `bad` is not the step's. -/
theorem skipRepeated_forbidden (host : String → List Tm → Prop) :
    ¬ RefVerdict substitute1 bad [] [1, 2, 3, 4] host
      ((skipRepeated (compile substitute1)).admits premises bad).1 := by
  rw [skipRepeated_admits_bad]
  intro h
  exact (bad_refused host).2.2 h.2.2.1

/-- A rule with a guard: take `p(X)` unless some `q(X, Z)` is present. -/
def guarded : Rule where
  nparams := 0
  fresh := 0
  takes := [.app 1 [loc 0]]
  reads := []
  makes := [.app 3 [loc 0]]
  tells := []
  aparts := []
  guards := [.absent (.app 2 [loc 0, loc 1])]

def blocked : St where
  vars := 0
  diseqs := 0
  names := 0
  nextId := 3
  present := [⟨1, .app 1 [code 7]⟩, ⟨2, .app 2 [code 7, code 9]⟩]

def free : St := { blocked with present := [⟨1, .app 1 [code 7]⟩, ⟨2, .app 2 [code 8, code 9]⟩] }

/-- Positive and negative for an absence with a guard-only local. -/
example : (compile guarded).fire ⟨[], [1]⟩ blocked = (.refused (.guard 0), blocked, []) := by decide +kernel
example : (compile guarded).fire ⟨[], [1]⟩ free =
    (.admitted,
      { free with
        nextId := 4
        present := [⟨2, .app 2 [code 8, code 9]⟩, ⟨3, .app 3 [code 7]⟩] }, [3]) := by decide +kernel

/-- Fault 7 of the C specializer's list: the take leaves before the guards are decided. -/
def isGuardTest : Instr → Bool
  | .scanNone _ _ (.guard _) => true
  | .countEq _ _ (.guard _) => true
  | .test _ (.guard _) => true
  | .fail (.guard _) => true
  | _ => false

def takeEarly (P : Prog) : Prog :=
  { checks := P.checks.takeWhile (fun i => !isGuardTest i) ++
      Instr.remove 0 :: P.checks.dropWhile (fun i => !isGuardTest i)
    commit := P.commit.filter fun i => match i with
      | .remove _ => false
      | _ => true }

theorem takeEarly_trace :
    ((takeEarly (compile guarded)).admits ⟨[], [1]⟩ blocked).1 = .refused (.guard 0) ∧
    ((takeEarly (compile guarded)).admits ⟨[], [1]⟩ blocked).2.1 ≠ blocked := by decide +kernel

/-- **The theorem forbids fault 7**: a refusal of the specialized program leaves the state. -/
theorem takeEarly_forbidden :
    ((compile guarded).admits ⟨[], [1]⟩ blocked).2.1 = blocked ∧
    ((takeEarly (compile guarded)).admits ⟨[], [1]⟩ blocked).2.1 ≠ blocked :=
  ⟨(specialized_admission guarded ((inClassB_iff _).mp (by decide +kernel)) blocked [] [1] (fun _ _ => True)).2.1,
   takeEarly_trace.2⟩

/-- A count of a determined pattern: exactly two `q(X, 9)`. -/
def counted : Rule := { guarded with guards := [.count (.app 2 [loc 0, code 9]) 2] }

def twice : St :=
  { blocked with
    nextId := 4
    present := [⟨1, .app 1 [code 7]⟩, ⟨2, .app 2 [code 7, code 9]⟩, ⟨3, .app 2 [code 7, code 9]⟩] }

example : ((compile counted).admits ⟨[], [1]⟩ twice).1 = .admitted := by decide +kernel
example : ((compile counted).admits ⟨[], [1]⟩ blocked).1 = .refused (.guard 0) := by decide +kernel

/-- A count of a nonzero number whose pattern has a guard-only local: it fails even where exactly
one label matches, since a solution can give the local a value no label contains. -/
def countedFree : Rule := { guarded with guards := [.count (.app 2 [loc 0, loc 1]) 1] }

example : (specialize countedFree).isSome = true := by decide +kernel
example : ((compile countedFree).admits ⟨[], [1]⟩ blocked).1 = .refused (.guard 0) := by decide +kernel
theorem countedFree_fails (host : String → List Tm → Prop) :
    ¬ Entails countedFree blocked [] [1] host (.count (.app 2 [loc 0, loc 1]) 1) := by
  have h := (specialized_admission countedFree ((inClassB_iff _).mp (by decide +kernel)) blocked [] [1]
    host).1
  have hv : ((compile countedFree).admits ⟨[], [1]⟩ blocked).1 = .refused (.guard 0) := by decide +kernel
  rw [hv] at h
  obtain ⟨-, -, -, g, hg, hno, -⟩ := h
  simp only [countedFree, guarded, List.getElem?_cons_zero, Option.some.injEq] at hg
  subst hg
  exact hno

/-- A fresh name in a make: the made label carries the name the firing mints. -/
def minting : Rule where
  nparams := 1
  fresh := 1
  takes := []
  reads := []
  makes := [.app 3 [loc 0, fresh 0]]
  tells := []
  aparts := []
  guards := []

example : (compile minting).fire ⟨[code 4], []⟩ blocked =
    (.admitted,
      { blocked with
        names := 1
        nextId := 4
        present := blocked.present ++ [⟨3, .app 3 [code 4, name 0]⟩] }, [3]) := by decide +kernel
/-- A parameter that names an unminted name is refused by shapes. -/
example : ((compile minting).admits ⟨[name 5], []⟩ blocked).1 = .refused .shapes := by decide +kernel

/-! ## Rules just outside the class -/

/-- A local left unbound in a make (the result would gain a frame variable). -/
def unboundMake : Rule := { guarded with guards := [], makes := [.app 3 [loc 1]] }
/-- A told disequation. -/
def toldApart : Rule := { guarded with guards := [], aparts := [(loc 0, code 7)] }
/-- A host guard. -/
def hosted : Rule := { guarded with guards := [.host "gt1" [loc 0]] }

example : (specialize unboundMake).isSome = false := by decide +kernel
example : (specialize toldApart).isSome = false := by decide +kernel
example : (specialize hosted).isSome = false := by decide +kernel
example : (specialize guarded).isSome = true := by decide +kernel

theorem unboundMake_generic : dispatch unboundMake blocked [] = .generic :=
  (dispatch_generic_iff _ _ _).mpr fun h => absurd ((inClassB_iff _).mpr h.1) (by decide +kernel)

/-- An in-class rule at a frame with a variable goes to the generic route too. -/
theorem variable_frame_generic : dispatch guarded { blocked with vars := 1 } [] = .generic :=
  (dispatch_generic_iff _ _ _).mpr fun h => absurd h.2.1 (by decide +kernel)

#print axioms bad_refused
#print axioms countedFree_fails
#print axioms skipRepeated_forbidden
#print axioms takeEarly_forbidden
#print axioms unboundMake_generic
#print axioms variable_frame_generic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Controls
