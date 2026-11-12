import Mettapedia.Machines.Cursor.LetEffectProfilesNesting

/-!
# Distinguishing effect and nesting disciplines

These controls execute the actual adaptive programs and services. They separate
late refusal from an unreached prefix, buffered events from immediate events,
pre-state from overlay reads, and a child receipt from an outer receipt.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetEffectProfilesControls

open LetEffectProfiles LetEffectProfilesNesting

def initial : World Nat Nat String := ⟨fun _ => 0, []⟩

def markRefuse : Code Nat Nat String Unit String :=
  .read (.perform (.record "visited")) fun _ =>
    .read (.perform (.put 0 9)) fun _ => .pure .refused

def markError : Code Nat Nat String Unit String :=
  .read (.perform (.record "visited")) fun _ => .pure (.error "late-error")

def overlayRefused := publish true true initial (prepared .overlay markRefuse initial)
def declarativeRefused := publish true true initial (prepared .preState markRefuse initial)

example : (ambient markRefuse initial).answer = .refused ∧
    (ambient markRefuse initial).state.store 0 = 9 ∧
    (ambient markRefuse initial).state.events = ["visited"] := by decide

example : overlayRefused.result = .refused ∧ overlayRefused.world.store 0 = 0 ∧
    overlayRefused.world.events = [] ∧ overlayRefused.receipt = none ∧
    overlayRefused.published = false := by decide

example : declarativeRefused.world.store 0 = 0 ∧ declarativeRefused.world.events = [] ∧
    declarativeRefused.receipt = none := by decide

/-- No prefix reaches the effectful expression, which differs from reaching
it and obtaining zero finally admitted firings. -/
example :
    (ambient (.pure (.refused : Result Unit String) : Code Nat Nat String Unit String) initial).reads = [] ∧
    (ambient (.pure (.refused : Result Unit String) : Code Nat Nat String Unit String) initial).state.events = [] ∧
    (ambient markRefuse initial).reads.length = 2 ∧
    (ambient markRefuse initial).state.events = ["visited"] := by decide

example : (ambient markError initial).answer = .error "late-error" ∧
    (ambient markError initial).state.events = ["visited"] := by decide

example :
    let result := publish true true initial (prepared .overlay markError initial)
    result.result = .error "late-error" ∧ result.world.events = [] ∧ result.receipt = none := by decide

def writeAndRead : Code Nat Nat String (Option Nat) String := writeRead 0 7

example : (prepared .overlay writeAndRead initial).answer = .answer (some 7) ∧
    (prepared .preState writeAndRead initial).answer = .answer (some 0) := by decide

example :
    let one := publish true true initial (prepared .overlay writeAndRead initial)
    let two := publish true true initial (prepared .preState writeAndRead initial)
    one.published = true ∧ two.published = true ∧ one.world.store 0 = 7 ∧ two.world.store 0 = 7 ∧
      one.result ≠ two.result := by decide

def writeThenGuard : Code Nat Nat String Unit String :=
  .read (.perform (.put 0 1)) fun _ =>
    .read (.load 0) fun value =>
      .pure (if value = some 1 then .answer () else .refused)

/-- Internal read discipline can change admission, not only the returned
value: one atomic profile commits and the other refuses the same source code. -/
example :
    let overlay := publish true true initial (prepared .overlay writeThenGuard initial)
    let snapshot := publish true true initial (prepared .preState writeThenGuard initial)
    overlay.result = .answer () ∧ overlay.published = true ∧ overlay.world.store 0 = 1 ∧
      snapshot.result = .refused ∧ snapshot.published = false ∧ snapshot.world.store 0 = 0 := by decide

/-- A successful private computation can still be refused by later admission. -/
example :
    let preparedCode := prepared .overlay writeAndRead initial
    let result := publish true false initial preparedCode
    preparedCode.answer = .answer (some 7) ∧ result.result = .refused ∧
      result.world.store 0 = 0 ∧ result.receipt = none := by decide

/-- Optional recording does not change publication into a refusal. -/
example :
    let result := publish false true initial (prepared .overlay writeAndRead initial)
    result.published = true ∧ result.world.store 0 = 7 ∧ result.receipt = none := by decide

def currentWithUnrelatedWrite : World Nat Nat String := ⟨fun key => if key = 2 then 99 else 0, []⟩

example :
    let result := publish false true currentWithUnrelatedWrite (prepared .overlay writeAndRead initial)
    result.world.store 0 = 7 ∧ result.world.store 2 = 99 := by decide

def child : Code Nat Nat String Unit String :=
  .read (.perform (.put 0 5)) fun _ => .pure (.answer ())

def refuseParent (_ : Unit) : Code Nat Nat String Unit String := .pure .refused

def openResult := openNested .overlay true true child refuseParent initial
def closedResult := closedNested .overlay true child refuseParent initial

example : openResult.world.store 0 = 5 ∧ openResult.childPublished = true ∧
    openResult.parentPublished = false ∧
    openResult.childReceipt = some ⟨(), [.put 0 5]⟩ ∧ openResult.parentReceipt = none := by decide

example : closedResult.world.store 0 = 0 ∧ closedResult.published = false ∧
    closedResult.receipt = none := by decide

def readParent (_ : Unit) : Code Nat Nat String (Option Nat) String :=
  .read (.load 0) fun value => .pure (.answer value)

example :
    let result := closedNested .overlay true child readParent initial
    result.result = .answer (some 5) ∧ result.published = true ∧ result.world.store 0 = 5 ∧
      result.receipt = some ⟨some 5, [.put 0 5]⟩ := by decide

example :
    let result := closedNested .preState true child readParent initial
    result.result = .answer (some 0) ∧ result.published = true ∧ result.world.store 0 = 5 := by decide

end Mettapedia.Machines.Cursor.LetEffectProfilesControls
