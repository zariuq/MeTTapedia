import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision

/-!
# Proposition codes with an accessibility recursor: syntax

Terms are the intrinsically typed simple terms of the one-ground calculus
`SingleBaseSTLC.IntrinsicSTT.Term`.  The ground type is read as the type of
proposition codes, `prop`.  Every data context `Γ` sits above a fixed
signature, so a term over `Γ` is a term over `Γ ++ signature A P`, for a
carrier type `A` and a result type `P`.  The signature declares

* the accessibility recursor `rec : (A → A → prop) → (A → (A → P) → P) → A → P`,
  which receives its relation explicitly;
* implication `imp : prop → prop → prop`;
* quantifiers of type `(σ → prop) → prop` for `σ` among `prop`, `A`,
  `A → prop`, `A → P` and `P → prop`.

Every symbol is an ordinary variable of the signature part of the context.
With no computation rule for `rec`, the symbols are exactly extra variables,
so conversion is beta conversion of the one-ground calculus.

The derived codes are:

* `falsum := ∀p : prop. p`;
* Leibniz equality at `P`, `resultEq u v := ∀Q : P → prop. Q u → Q v`;
* the impredicative accessibility code
  `accCode R a := ∀X : A → prop. (∀x. (∀y. R y x → X y) → X x) → X a`,
  where `R y x` reads "`y` is below `x`";
* the respect code
  `respCode R F := ∀x g g'. (∀y. R y x → g y = g' y) → F x g = F x g'`,
  stating that `F x` reads its recursive argument only below `x`;
* the unfolding `unfoldTerm R F a := F a (λb. rec R F b)` of `recTerm R F a`.

The recursive call receives no accessibility proof: the requirement that
`F` call it only below its argument is the extrinsic `respCode`, stated in the
logic, rather than a proof argument of the call.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

/-- The ground type, read as the type of proposition codes. -/
abbrev prop : Ty := .atom

/-- The type of a quantifier over `σ`. -/
abbrev quantTy (σ : Ty) : Ty := .arr (.arr σ prop) prop

/-- Binary relations on `A`, applied as `R y x` for "`y` is below `x`". -/
abbrev relTy (A : Ty) : Ty := .arr A (.arr A prop)

/-- Recursion steps: a point and a recursive call give a result. -/
abbrev stepTy (A P : Ty) : Ty := .arr A (.arr (.arr A P) P)

/-- The type of the accessibility recursor. -/
abbrev recTy (A P : Ty) : Ty := .arr (relTy A) (.arr (stepTy A P) (.arr A P))

/-- The type of implication. -/
abbrev impTy : Ty := .arr prop (.arr prop prop)

/-- The signature below every data context. -/
abbrev signature (A P : Ty) : List Ty :=
  [recTy A P, impTy, quantTy prop, quantTy A, quantTy (.arr A prop), quantTy (.arr A P),
    quantTy (.arr P prop)]

/-- Terms over the data context `Γ`, with the signature below it. -/
abbrev Tm (A P : Ty) (Γ : List Ty) (T : Ty) : Type := Term (Γ ++ signature A P) T

section Symbols

variable (A P : Ty)

/-- The accessibility recursor. -/
def recSymbol : Var (signature A P) (recTy A P) := .zero

/-- Implication. -/
def impSymbol : Var (signature A P) impTy := .succ .zero

/-- Quantification over proposition codes. -/
def allProp : Var (signature A P) (quantTy prop) := .succ (.succ .zero)

/-- Quantification over the carrier. -/
def allCarrier : Var (signature A P) (quantTy A) := .succ (.succ (.succ .zero))

/-- Quantification over predicates on the carrier. -/
def allPredicate : Var (signature A P) (quantTy (.arr A prop)) :=
  .succ (.succ (.succ (.succ .zero)))

/-- Quantification over functions from the carrier to results. -/
def allFunction : Var (signature A P) (quantTy (.arr A P)) :=
  .succ (.succ (.succ (.succ (.succ .zero))))

/-- Quantification over predicates on results. -/
def allResult : Var (signature A P) (quantTy (.arr P prop)) :=
  .succ (.succ (.succ (.succ (.succ (.succ .zero)))))

end Symbols

/-- A signature variable, above a data context. -/
def liftSymbol {S : List Ty} {T : Ty} : (Γ : List Ty) → Var S T → Var (Γ ++ S) T
  | [], symbol => symbol
  | _ :: Γ, symbol => .succ (liftSymbol Γ symbol)

variable {A P : Ty}

/-- A signature symbol as a term over the data context `Γ`. -/
def sym (Γ : List Ty) {T : Ty} (symbol : Var (signature A P) T) : Tm A P Γ T :=
  .var (liftSymbol Γ symbol)

/-- Weakening by one data variable. -/
def wk {Γ : List Ty} {B T : Ty} (term : Tm A P Γ T) : Tm A P (B :: Γ) T :=
  term.rename weakening

/-- Instantiation of the newest data variable. -/
def inst {Γ : List Ty} {B T : Ty} (body : Tm A P (B :: Γ) T) (argument : Tm A P Γ B) :
    Tm A P Γ T :=
  Term.instantiateNewest body argument

@[simp] theorem wk_sym {Γ : List Ty} {B T : Ty} (symbol : Var (signature A P) T) :
    wk (B := B) (sym Γ symbol) = sym (B :: Γ) symbol := rfl

@[simp] theorem inst_sym {Γ : List Ty} {B T : Ty} (symbol : Var (signature A P) T)
    (argument : Tm A P Γ B) : inst (sym (B :: Γ) symbol) argument = sym Γ symbol := rfl

/-! ## Codes -/

/-- Implication. -/
def imp {Γ : List Ty} (premise conclusion : Tm A P Γ prop) : Tm A P Γ prop :=
  .app (.app (sym Γ (impSymbol A P)) premise) conclusion

/-- Quantification through a quantifier symbol. -/
def all {Γ : List Ty} {σ : Ty} (quantifier : Var (signature A P) (quantTy σ))
    (body : Tm A P Γ (.arr σ prop)) : Tm A P Γ prop :=
  .app (sym Γ quantifier) body

/-- `Falsum := ∀p : prop. p`. -/
def falsum {Γ : List Ty} : Tm A P Γ prop :=
  all (allProp A P) (.lam (.var .zero))

/-- Leibniz equality of results: `∀Q : P → prop. Q u → Q v`. -/
def resultEq {Γ : List Ty} (left right : Tm A P Γ P) : Tm A P Γ prop :=
  all (allResult A P)
    (.lam (imp (Γ := .arr P prop :: Γ) (.app (.var .zero) (wk left))
      (.app (.var .zero) (wk right))))

/-- The impredicative accessibility code
`∀X : A → prop. (∀x. (∀y. R y x → X y) → X x) → X a`. -/
def accCode {Γ : List Ty} (R : Tm A P Γ (relTy A)) (point : Tm A P Γ A) : Tm A P Γ prop :=
  all (allPredicate A P) (.lam
    (imp (Γ := .arr A prop :: Γ)
      (all (allCarrier A P) (.lam
        (imp (Γ := A :: .arr A prop :: Γ)
          (all (allCarrier A P) (.lam
            (imp (Γ := A :: A :: .arr A prop :: Γ)
              (.app (.app (wk (wk (wk R))) (.var .zero)) (.var (.succ .zero)))
              (.app (.var (.succ (.succ .zero))) (.var .zero)))))
          (.app (.var (.succ .zero)) (.var .zero)))))
      (.app (.var .zero) (wk point))))

/-- The respect code
`∀x g g'. (∀y. R y x → g y = g' y) → F x g = F x g'`. -/
def respCode {Γ : List Ty} (R : Tm A P Γ (relTy A)) (F : Tm A P Γ (stepTy A P)) :
    Tm A P Γ prop :=
  all (allCarrier A P) (.lam
    (all (allFunction A P) (.lam
      (all (allFunction A P) (.lam
        (imp (Γ := .arr A P :: .arr A P :: A :: Γ)
          (all (allCarrier A P) (.lam
            (imp (Γ := A :: .arr A P :: .arr A P :: A :: Γ)
              (.app (.app (wk (wk (wk (wk R)))) (.var .zero)) (.var (.succ (.succ (.succ .zero)))))
              (resultEq (.app (.var (.succ (.succ .zero))) (.var .zero))
                (.app (.var (.succ .zero)) (.var .zero))))))
          (resultEq (.app (.app (wk (wk (wk F))) (.var (.succ (.succ .zero)))) (.var (.succ .zero)))
            (.app (.app (wk (wk (wk F))) (.var (.succ (.succ .zero)))) (.var .zero)))))))))

/-- The recursor applied to a relation, a step and a point. -/
def recTerm {Γ : List Ty} (R : Tm A P Γ (relTy A)) (F : Tm A P Γ (stepTy A P))
    (point : Tm A P Γ A) : Tm A P Γ P :=
  .app (.app (.app (sym Γ (recSymbol A P)) R) F) point

/-- One unfolding of the recursor: `F a (λb. rec R F b)`. -/
def unfoldTerm {Γ : List Ty} (R : Tm A P Γ (relTy A)) (F : Tm A P Γ (stepTy A P))
    (point : Tm A P Γ A) : Tm A P Γ P :=
  .app (.app F point) (.lam (recTerm (wk R) (wk F) (.var .zero)))

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
