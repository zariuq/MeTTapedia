import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BoundedConversion
import Mettapedia.GSLT.GraphTheory.ReflectiveBetaBubble

/-!
# Proof by reflection: a carved fragment comes with its decision procedure

A *reflective decision* is an internal procedure on codes together with its
soundness theorem: a computation on a code that answers `true` proves the
judgment the code denotes, and one that answers `false` refutes it
(`ReflectiveDecision.prove`, `ReflectiveDecision.refute`).  The judgment
itself is an inductive relation that no computation inspects; the procedure
replaces it, on the fragment, by evaluation.

**The instance.**  The candidate's native simple fragment: codes are pairs of
intrinsically typed simple terms with a fuel bound, the procedure is the
existing bounded normalise-and-compare (`BoundedConversion.compareWithin`),
and soundness is `compareWithin_established` / `compareWithin_refuted`
(`conversionDecision`).  It is complete (`conversionDecision_complete`: some
fuel decides every pair, by strong normalisation), and on the simple image it
decides the strong tower conversion itself, as a carve-out in the sense of
`FragmentDecision` whose fragment is every simple term (`towerDecision`).

**Reflective proofs.**  `two_plus_two` proves the β-conversion of Church
`2 + 2` and `4` by a kernel computation on their codes, and
`two_plus_two_denote` turns it into a theorem about every carrier and every
function: `add 2 2` denotes four-fold iteration.  `two_ne_three` refutes a
conversion the same way.

**Controls.**
* Too little fuel yields no answer, never a wrong one (`two_plus_two_needs_fuel`).
* The simple fragment is not reflexive: it has no self-application at all.
  Its reflexive neighbour, the untyped λ-calculus, has no internal decision of
  its conversion (`untyped_contrast`, from the diagonal), and there the default
  observer stays incomplete on `Ω = Ω` at every budget.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ProofByReflection

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BoundedConversion
open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.GSLT.ObserverBubble

universe u v

/-- **An internal decision procedure on codes, with its soundness theorem.** -/
structure ReflectiveDecision (Code : Type u) (Judgment : Code → Prop) where
  /-- The procedure: a computation on codes, possibly without an answer. -/
  run : Code → Option Bool
  sound_true : ∀ code, run code = some true → Judgment code
  sound_false : ∀ code, run code = some false → ¬ Judgment code

namespace ReflectiveDecision

variable {Code : Type u} {Judgment : Code → Prop} (decision : ReflectiveDecision Code Judgment)

/-- **Proof by reflection**: a computation answering `true` proves the
judgment. -/
theorem prove {code : Code} (computed : decision.run code = some true) : Judgment code :=
  decision.sound_true code computed

/-- A computation answering `false` refutes it. -/
theorem refute {code : Code} (computed : decision.run code = some false) : ¬ Judgment code :=
  decision.sound_false code computed

/-- The procedure's answer as an evidence-bearing outcome. -/
def verdict (code : Code) : Outcome (Judgment code) (¬ Judgment code) Empty Unit :=
  match computed : decision.run code with
  | some true => .established (decision.sound_true code computed)
  | some false => .refuted (decision.sound_false code computed)
  | none => .incomplete ()

theorem verdict_asBool (code : Code) : (decision.verdict code).asBool = decision.run code := by
  unfold verdict
  split <;> simp_all [Outcome.asBool]

end ReflectiveDecision

/-! ## The simple fragment -/

variable {Γ : List Ty} {A : Ty}

/-- A code for a conversion question: a fuel bound and two simple terms. -/
structure ConversionCode (Γ : List Ty) (A : Ty) where
  fuel : ℕ
  left : Term Γ A
  right : Term Γ A

/-- **The simple fragment's reflective decision**: bounded normalisation and
comparison of normal forms, sound by the existing theorems. -/
def conversionDecision (Γ : List Ty) (A : Ty) :
    ReflectiveDecision (ConversionCode Γ A) fun code => BetaConv code.left code.right where
  run code := compareWithin code.fuel code.left code.right
  sound_true _ computed := compareWithin_established computed
  sound_false _ computed := compareWithin_refuted computed

/-- **Completeness**: some fuel decides every pair. -/
theorem conversionDecision_complete (left right : Term Γ A) :
    ∃ fuel, (conversionDecision Γ A).run ⟨fuel, left, right⟩ = some (decideConversion left right) :=
  compareWithin_eventually left right

/-- The strong judgment on the simple image: conversion of the erasures in
the sealed tower. -/
def TowerConv (left right : Term Γ A) : Prop :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Conv
    Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.HeadEq
    (TowerDTT.eraseTerm left) (TowerDTT.eraseTerm right)

/-- **The carve-out with its decision procedure**: the strong tower conversion,
restricted to the simple image, decided on every simple term. -/
def towerDecision (Γ : List Ty) (A : Ty) : FragmentDecision (@TowerConv Γ A) where
  Fragment _ := True
  fragmentDecidable _ := isTrue trivial
  answer left right _ _ := decideConversion left right
  answer_exact left right _ _ :=
    (decideConversion_correct left right).trans (towerConv_iff_betaConv left right).symm

/-! ## Church arithmetic by reflection -/

/-- Church numerals over the atom. -/
abbrev numeralType : Ty := .arr (.arr .atom .atom) (.arr .atom .atom)

/-- `f (f (… x))`, with `n` applications. -/
def iterateApplication : ℕ → Term (.atom :: .arr .atom .atom :: Γ) .atom
  | 0 => .var .zero
  | n + 1 => .app (.var (.succ .zero)) (iterateApplication n)

/-- The Church numeral `n`. -/
def numeral (n : ℕ) : Term Γ numeralType := .lam (.lam (iterateApplication n))

/-- Church addition, `λ m n f x. m f (n f x)`. -/
def add : Term Γ (.arr numeralType (.arr numeralType numeralType)) :=
  .lam (.lam (.lam (.lam
    (.app (.app (.var (.succ (.succ (.succ .zero)))) (.var (.succ .zero)))
      (.app (.app (.var (.succ (.succ .zero))) (.var (.succ .zero))) (.var .zero))))))

/-- `2 + 2`, as a code. -/
def twoPlusTwo : Term [] numeralType := .app (.app add (numeral 2)) (numeral 2)

/-- **`2 + 2` converts to `4`, by computation on codes.** -/
theorem two_plus_two : BetaConv twoPlusTwo (numeral 4) :=
  (conversionDecision [] numeralType).prove (code := ⟨40, twoPlusTwo, numeral 4⟩) (by decide)

/-- The empty environment. -/
def emptyEnvironment (Ground : Type u) : Environment Ground [] :=
  ⟨fun typedVar => nomatch typedVar⟩

/-- **A theorem about every carrier and function, proved by reflection**:
`add 2 2` denotes four-fold iteration. -/
theorem two_plus_two_denote (Ground : Type u) (f : Ground → Ground) (x : Ground) :
    twoPlusTwo.denote (emptyEnvironment Ground) f x = f (f (f (f x))) := by
  rw [two_plus_two.denote (emptyEnvironment Ground)]
  rfl

/-- **Refutation by reflection**: `2` and `3` are not convertible. -/
theorem two_ne_three : ¬ BetaConv (numeral 2 : Term [] numeralType) (numeral 3) :=
  (conversionDecision [] numeralType).refute (code := ⟨10, numeral 2, numeral 3⟩) (by decide)

/-- **Control**: with too little fuel the procedure answers nothing, never a
wrong answer. -/
theorem two_plus_two_needs_fuel :
    (conversionDecision [] numeralType).run ⟨2, twoPlusTwo, numeral 4⟩ = none := by decide

/-! ## The reflexive contrast -/

open Mettapedia.GSLT.GraphTheory Mettapedia.GSLT.GraphTheory.BudgetedBeta
  Mettapedia.GSLT.GraphTheory.ReflectiveBeta in
/-- **The untyped contrast**: no λ-term decides β-conversion, and the default
observer is incomplete on `Ω = Ω` at every budget, although the equation
holds. -/
theorem untyped_contrast :
    (∀ decider : LambdaTerm, ¬ lambdaReflexive.DecidesEquiv decider) ∧
      (∀ fuel, betaObserver.verdict (fun _ => True) LambdaTerm.Omega LambdaTerm.Omega fuel =
        .incomplete ()) :=
  ⟨no_lambda_decides_betaConv, unrestricted_omega_incomplete⟩

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ProofByReflection
