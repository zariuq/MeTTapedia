import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents

/-!
# The noncommutative monoid equation rung

The source's monoid presentation is instantiated as a one-sorted signature
with an empty metavariable family, three genuinely authored axioms, and no
operational rules. Its quotient is the initial binding-clone model of those
axioms; its closed and open fibres carry the expected monoid operation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MonoidEquationRung

open CategoryTheory.Limits

inductive Srt where
  | element
  deriving DecidableEq

inductive Op : Srt → Type where
  | unit : Op .element
  | mul : Op .element

def sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} op => match op with
    | .unit => []
    | .mul => [([], .element), ([], .element)]

abbrev metas : List (MetaArity sig) := []
abbrev schemaSig := withMetas sig metas

def unitT {Γ : Ctx sig} : Term sig Γ .element :=
  .op .unit .nil

def mulT {Γ : Ctx sig}
    (left right : Term sig Γ .element) : Term sig Γ .element :=
  .op .mul (.cons left (.cons right .nil))

private def schemaUnit {Γ : Ctx schemaSig} :
    Term schemaSig Γ .element :=
  .op (Sum.inl Op.unit) .nil

private def schemaMul {Γ : Ctx schemaSig}
    (left right : Term schemaSig Γ .element) :
    Term schemaSig Γ .element :=
  .op (Sum.inl Op.mul) (.cons left (.cons right .nil))

private def x : Term schemaSig [.element, .element, .element] .element :=
  .var .zero
private def y : Term schemaSig [.element, .element, .element] .element :=
  .var (.succ .zero)
private def z : Term schemaSig [.element, .element, .element] .element :=
  .var (.succ (.succ .zero))
private def u : Term schemaSig [.element] .element := .var .zero

def assoc : EqAxiom sig metas where
  ctx := [.element, .element, .element]
  sort := .element
  lhs := schemaMul (schemaMul x y) z
  rhs := schemaMul x (schemaMul y z)

def leftUnit : EqAxiom sig metas where
  ctx := [.element]
  sort := .element
  lhs := schemaMul schemaUnit u
  rhs := u

def rightUnit : EqAxiom sig metas where
  ctx := [.element]
  sort := .element
  lhs := schemaMul u schemaUnit
  rhs := u

def monoidE : List (EqAxiom sig metas) :=
  [assoc, leftUnit, rightUnit]

private def threeClose {Γ : Ctx sig}
    (a b c : Term sig Γ .element) :
    Sub sig [.element, .element, .element] Γ
  | _, .zero => a
  | _, .succ .zero => b
  | _, .succ (.succ .zero) => c
  | _, .succ (.succ (.succ old)) => nomatch old

private def oneClose {Γ : Ctx sig}
    (a : Term sig Γ .element) : Sub sig [.element] Γ
  | _, .zero => a
  | _, .succ old => nomatch old

theorem raw_assoc {Γ : Ctx sig}
    (a b c : Term sig Γ .element) :
    EqClosure monoidE (mulT (mulT a b) c) (mulT a (mulT b c)) := by
  simpa [monoidE, assoc, schemaMul, x, y, z, threeClose,
    instantiate, instantiateArgs, bind, bindArgs, liftSub, mulT] using
    (EqClosure.ax (E := monoidE) (i := ⟨0, by decide⟩)
      (fun i => Fin.elim0 i) (threeClose a b c))

theorem raw_left_unit {Γ : Ctx sig} (a : Term sig Γ .element) :
    EqClosure monoidE (mulT unitT a) a := by
  simpa [monoidE, leftUnit, schemaMul, schemaUnit, u, oneClose,
    instantiate, instantiateArgs, bind, bindArgs, liftSub, mulT, unitT] using
    (EqClosure.ax (E := monoidE) (i := ⟨1, by decide⟩)
      (fun i => Fin.elim0 i) (oneClose a))

theorem raw_right_unit {Γ : Ctx sig} (a : Term sig Γ .element) :
    EqClosure monoidE (mulT a unitT) a := by
  simpa [monoidE, rightUnit, schemaMul, schemaUnit, u, oneClose,
    instantiate, instantiateArgs, bind, bindArgs, liftSub, mulT, unitT] using
    (EqClosure.ax (E := monoidE) (i := ⟨2, by decide⟩)
      (fun i => Fin.elim0 i) (oneClose a))

/-- Every sorted context has an equation-class monoid operation. -/
def mulQ {Γ : Ctx sig}
    (a b : TermQ monoidE Γ .element) : TermQ monoidE Γ .element :=
  Quotient.liftOn₂ a b
    (fun x y => Quotient.mk _ (mulT x y))
    (by
      intro x x' y y' hx hy
      change EqClosure monoidE x y at hx
      change EqClosure monoidE x' y' at hy
      exact Quotient.sound
        (show EqClosure monoidE (mulT x x') (mulT y y') from by
          change EqClosure monoidE
            (Term.op Op.mul (Args.cons x (Args.cons x' Args.nil)))
            (Term.op Op.mul (Args.cons y (Args.cons y' Args.nil)))
          exact EqClosure.cong (E := monoidE) Op.mul
            (EqArgs.cons hx (EqArgs.cons hy .nil))))

def unitQ {Γ : Ctx sig} : TermQ monoidE Γ .element :=
  Quotient.mk _ unitT

@[simp] theorem mulQ_mk {Γ : Ctx sig}
    (a b : Term sig Γ .element) :
    mulQ (Quotient.mk _ a) (Quotient.mk _ b) =
      (Quotient.mk _ (mulT a b) : TermQ monoidE Γ .element) := rfl

theorem mulQ_assoc {Γ : Ctx sig}
    (a b c : TermQ monoidE Γ .element) :
    mulQ (mulQ a b) c = mulQ a (mulQ b c) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      induction c using Quotient.inductionOn with
      | _ c =>
        exact Quotient.sound (raw_assoc a b c)

theorem unitQ_mulQ {Γ : Ctx sig}
    (a : TermQ monoidE Γ .element) : mulQ unitQ a = a := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (raw_left_unit a)

theorem mulQ_unitQ {Γ : Ctx sig}
    (a : TermQ monoidE Γ .element) : mulQ a unitQ = a := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (raw_right_unit a)

/-- The generic binding-equation model universal property applies to the
actual three-axiom, noncommutative monoid presentation. -/
noncomputable def modelInitial :
    IsInitial (FreeBindingEquationModel.presented monoidE) :=
  FreeBindingEquationModel.presentedIsInitial monoidE

def noRewritePresentation : UnpositionedPresentation sig where
  metas := metas
  eqs := monoidE
  rules := []

theorem no_reduction {sort : Srt}
    (source target : Term sig [] sort) :
    ¬ noRewritePresentation.StepModE source target := by
  rintro ⟨ruleIndex, _⟩
  exact ruleIndex.elim0

/-! ## A word model distinguishes multiplication order -/

/-- De Bruijn position of a free variable in its context. -/
def variableIndex : {Γ : Ctx sig} → {sort : Srt} → Var Γ sort → Nat
  | _, _, .zero => 0
  | _, _, .succ v => variableIndex v + 1

mutual
/-- Read a term as a word of variable positions. The signature itself has
no binders, so multiplication concatenates words without scope adjustment. -/
def word : {Γ : Ctx sig} → {sort : Srt} → Term sig Γ sort → List Nat
  | _, _, .var v => [variableIndex v]
  | _, _, .op _ args => wordArgs args

def wordArgs : {arity : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Args sig arity Γ → List Nat
  | _, _, .nil => []
  | _, _, .cons head tail => word head ++ wordArgs tail
end

/-- Every authored monoid axiom preserves the word under arbitrary closing
substitution; this is the noncommutative word model of the presentation. -/
theorem word_axiom : ∀ (i : Fin monoidE.length) {Γ : Ctx sig}
    (body : (k : Fin metas.length) → Term sig (metas.get k).1 (metas.get k).2)
    (close : Sub sig (monoidE.get i).ctx Γ),
    word (bind close (instantiate body (monoidE.get i).lhs)) =
      word (bind close (instantiate body (monoidE.get i).rhs))
  | ⟨0, _⟩, _, body, close => by
      show word (bind close (instantiate body assoc.lhs)) =
        word (bind close (instantiate body assoc.rhs))
      simp [assoc, schemaMul, x, y, z, instantiate, instantiateArgs,
        bind, bindArgs, liftSub, word, wordArgs, List.append_assoc]
  | ⟨1, _⟩, _, body, close => by
      show word (bind close (instantiate body leftUnit.lhs)) =
        word (bind close (instantiate body leftUnit.rhs))
      simp [leftUnit, schemaMul, schemaUnit, u, instantiate, instantiateArgs,
        bind, bindArgs, liftSub, word, wordArgs]
  | ⟨2, _⟩, _, body, close => by
      show word (bind close (instantiate body rightUnit.lhs)) =
        word (bind close (instantiate body rightUnit.rhs))
      simp [rightUnit, schemaMul, schemaUnit, u, instantiate, instantiateArgs,
        bind, bindArgs, liftSub, word, wordArgs]
  | ⟨_ + 3, h⟩, _, _, _ => by simp [monoidE] at h

mutual
theorem word_eqClosure : ∀ {Γ : Ctx sig} {sort : Srt}
    {left right : Term sig Γ sort},
    EqClosure monoidE left right → word left = word right
  | _, _, _, _, .ax i body close => word_axiom i body close
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (word_eqClosure h).symm
  | _, _, _, _, .trans h h' => (word_eqClosure h).trans (word_eqClosure h')
  | _, _, _, _, .cong _ h => by
      simp only [word, wordArgs_eqClosure h]

theorem wordArgs_eqClosure : ∀ {arity : List (List Srt × Srt)}
    {Γ : Ctx sig} {left right : Args sig arity Γ},
    EqArgs monoidE left right → wordArgs left = wordArgs right
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => by
      simp only [wordArgs, word_eqClosure head,
        wordArgs_eqClosure tail]
end

/-- Associativity and units do not impose commutativity: the two open
variable words remain distinct in the quotient. -/
theorem mul_variables_not_commutative :
    ¬ EqClosure monoidE
      (mulT (Term.var (Var.zero : Var [Srt.element, Srt.element] Srt.element))
        (Term.var (Var.succ Var.zero)))
      (mulT (Term.var (Var.succ Var.zero)) (Term.var Var.zero)) := by
  intro h
  have hw := word_eqClosure h
  simp [mulT, word, wordArgs, variableIndex] at hw

/-- The corresponding equation classes are distinct in the initial model. -/
theorem mulQ_variables_not_commutative :
    mulQ
      (Quotient.mk _ (Term.var (Var.zero : Var [Srt.element, Srt.element] Srt.element)))
      (Quotient.mk _ (Term.var (Var.succ Var.zero))) ≠
    mulQ
      (Quotient.mk _ (Term.var (Var.succ Var.zero)))
      (Quotient.mk _ (Term.var Var.zero)) := by
  intro h
  apply mul_variables_not_commutative
  exact Quotient.exact h

end Mettapedia.OSLF.Binding.MonoidEquationRung
