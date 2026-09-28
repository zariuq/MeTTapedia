import Mettapedia.Logic.HOL.ProofSyntaxModulo

/-!
# The facts a hosted proof library publishes, as source formulas

A proof library that links its proofs publishes facts it can realize:

* reflexivity at a type, `∀x. x = x` (`reflexivityFormula`);
* substitution at a type, `∀P x y. x = y ⇒ P x ⇒ P y` (`substitutionFormula`);
* η at a function type, `∀f. (λx. f x) = f` (`etaFormula`);
* the universal closure of a defining equation, `∀x⃗. l = r`
  (`DefiningEquation.closedFormula`);
* the induction principle of a simple inductive sort, whose constructors take
  recursive fields and fields of other types (`inductionFormula`): for each
  constructor the case `∀x⃗. P r₁ ⇒ ⋯ ⇒ P rₖ ⇒ P (c x⃗)`, with one hypothesis
  per recursive field in field order, and the conclusion `∀t. P t`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- `∀x : τ. x = x`. -/
def reflexivityFormula (τ : Ty Base) : Formula Const [] :=
  .all (σ := τ) (.eq (.var .vz) (.var .vz))

/-- `∀P : τ → prop. ∀x y : τ. x = y ⇒ P x ⇒ P y`. -/
def substitutionFormula (τ : Ty Base) : Formula Const [] :=
  .all (σ := .arr τ .prop) (.all (σ := τ) (.all (σ := τ)
    (.imp (.eq (.var (.vs .vz)) (.var .vz))
      (.imp (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))))

/-- `∀f : σ → τ. (λx. f x) = f`. -/
def etaFormula (σ τ : Ty Base) : Formula Const [] :=
  .all (σ := .arr σ τ) (.eq (.lam (.app (.var (.vs .vz)) (.var .vz))) (.var .vz))

/-- The universal closure of a formula over a context, the oldest variable
outermost. -/
def closeAll : (Θ : Ctx Base) → Formula Const Θ → Formula Const []
  | [], φ => φ
  | τ :: Θ, φ => closeAll Θ (.all (σ := τ) φ)

/-- The universal closure `∀x⃗. l = r` of a defining equation. -/
def DefiningEquation.closedFormula (equation : DefiningEquation Const) : Formula Const [] :=
  closeAll equation.context (.eq equation.left equation.right)

/-- `p₁ ⇒ p₂ ⇒ ⋯ ⇒ q`. -/
def hypChain {Γ : Ctx Base} : List (Formula Const Γ) → Formula Const Γ → Formula Const Γ
  | [], q => q
  | p :: ps, q => .imp p (hypChain ps q)

/-! ## Simple inductive sorts -/

/-- The type of a constructor of `sort` with the given fields: a field is
recursive (`none`) or of a type (`some σ`). -/
def ctorType (sort : Base) : List (Option (Ty Base)) → Ty Base
  | [] => .base sort
  | none :: fields => .arr (.base sort) (ctorType sort fields)
  | some σ :: fields => .arr σ (ctorType sort fields)

/-- A constructor of a simple inductive sort: its fields and its constant. -/
structure InductiveCtor (Const : Ty Base → Type v) (sort : Base) where
  fields : List (Option (Ty Base))
  symbol : Const (ctorType sort fields)

/-- The case of a constructor at the motive `p`: the remaining fields are
quantified, the recursive ones among all fields give hypotheses `p r`, and the
conclusion is `p` at the constructor applied to all fields. -/
def caseFormula (sort : Base) : (fields : List (Option (Ty Base))) → {Γ : Ctx Base} →
    Term Const Γ (.arr (.base sort) .prop) → Term Const Γ (ctorType sort fields) →
    List (Term Const Γ (.base sort)) → Formula Const Γ
  | [], _, p, head, recs => hypChain (recs.map (.app p)) (.app p head)
  | none :: fields, _, p, head, recs =>
      .all (σ := .base sort) (caseFormula sort fields (weaken p) (.app (weaken head) (.var .vz))
        (recs.map weaken ++ [.var .vz]))
  | some σ :: fields, _, p, head, recs =>
      .all (σ := σ) (caseFormula sort fields (weaken p) (.app (weaken head) (.var .vz))
        (recs.map weaken))

/-- The cases of the constructors at `p`, then `∀t. p t`. -/
def inductionChain (sort : Base) (ctors : List (InductiveCtor Const sort)) {Γ : Ctx Base}
    (p : Term Const Γ (.arr (.base sort) .prop)) : Formula Const Γ :=
  hypChain (ctors.map fun c => caseFormula sort c.fields p (.const c.symbol) [])
    (.all (σ := .base sort) (.app (weaken p) (.var .vz)))

/-- The induction principle of a simple inductive sort:
`∀P. case₁ ⇒ ⋯ ⇒ caseₖ ⇒ ∀t. P t`. -/
def inductionFormula (sort : Base) (ctors : List (InductiveCtor Const sort)) : Formula Const [] :=
  .all (σ := .arr (.base sort) .prop) (inductionChain sort ctors (.var .vz))

end Mettapedia.Logic.HOL
