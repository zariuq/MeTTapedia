import Mettapedia.OSLF.Syntax.PatternAsBindingSignature
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# The explicit substitution former, with its evaluation

Presenting `subst` as an operator says what it is, not what it does.  This
module supplies what it does, as an axiom of the second component rather than by
collapsing the former into the meta-level substitution -- which would change
which terms are values, and would erase an observation the calculus makes.

The axiom is the expected one,

    subst(x. B, R)  =  B[R/x],

and it needs no machinery beyond what adjoining metavariables already provides:
`B` is declared with arity one, so an occurrence of it is *applied* to an
argument, and instantiating a metavariable applied to an argument is exactly
substituting that argument into its body.  The right-hand side is therefore `B`
applied to `R`, and the equation is a statement about the signature rather than
a new definition.

Because the equational theory is closed under substitution -- proved once, for
every signature -- the closed axiom generates the open instances: an instance at
the empty context transports to any context by the same descent that makes the
quotient a presheaf.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Binding.PatternPresentation

set_option autoImplicit false

namespace PatternSubst

/-- `B` may depend on the variable the explicit substitution binds; `R` may not.
That is the whole binding content of the former, and it is declared here rather
than implemented in a traversal. -/
abbrev substMetas : List (MetaArity patSig) :=
  [([PatSrt.pat], PatSrt.pat), ([], PatSrt.pat)]

abbrev eqSig : Signature := withMetas patSig substMetas

/-- The two metavariables, pinned at the sort they produce. -/
def metaB : MetaOp substMetas PatSrt.pat := MetaOp.mk ⟨0, by decide⟩

def metaR : MetaOp substMetas PatSrt.pat := MetaOp.mk ⟨1, by decide⟩

/-- `subst(x. B[x], R)`. -/
def substLhs : Term eqSig [] PatSrt.pat :=
  Term.op (S := eqSig) (Sum.inl PatOp.substOp)
    (.cons
      (Term.op (S := eqSig) (Sum.inr metaB)
        (.cons (Term.var Var.zero) .nil))
      (.cons (Term.op (S := eqSig) (Sum.inr metaR) .nil) .nil))

/-- `B[R]`: the same metavariable, applied to the replacement instead. -/
def substRhs : Term eqSig [] PatSrt.pat :=
  Term.op (S := eqSig) (Sum.inr metaB)
    (.cons (Term.op (S := eqSig) (Sum.inr metaR) .nil) .nil)

/-- The evaluation rule, as the second component of the language definition. -/
def substAxiom : EqAxiom patSig substMetas where
  ctx := []
  sort := PatSrt.pat
  lhs := substLhs
  rhs := substRhs

abbrev patE : List (EqAxiom patSig substMetas) := [substAxiom]

/-! ## A worked instance in which the binder bites

The body uses the variable the explicit substitution binds, and uses it *under a
further binder*, so the replacement has to be carried past that binder. The
generic substitution explicitly uses its binder-preserving lift to do this;
scope indices alone do not uniquely determine that lift. -/

/-- `lambda q. x`, where `x` is the variable the explicit substitution binds. -/
def bodyB : Term patSig [PatSrt.pat] PatSrt.pat :=
  Term.op (S := patSig) (PatOp.lamOp (some "q"))
    (.cons (Term.var (Var.succ Var.zero)) .nil)

/-- A closed replacement. -/
def replR : Term patSig [] PatSrt.pat :=
  Term.op (S := patSig) (PatOp.applyOp "R" 0) .nil

def bodies : (i : Fin substMetas.length) →
    Term patSig (substMetas.get i).1 (substMetas.get i).2
  | ⟨0, _⟩ => bodyB
  | ⟨1, _⟩ => replR
  | ⟨_ + 2, h⟩ => by simp [substMetas] at h

/-- There are no variables to close over. -/
def emptySub : Sub patSig [] [] := fun _ v => nomatch v

/-- The redex: the explicit substitution node itself. -/
def redexTerm : Term patSig [] PatSrt.pat :=
  Term.op (S := patSig) PatOp.substOp (.cons bodyB (.cons replR .nil))

/-- The contractum: the body with the replacement substituted, computed by the
signature's own substitution. -/
def contractum : Term patSig [] PatSrt.pat :=
  bind (argsToSub (Args.cons replR Args.nil)) bodyB

/-- The instance of the axiom really is that pair. -/
theorem instance_is_the_redex_pair :
    bind emptySub (instantiate bodies substLhs) = redexTerm
      ∧ bind emptySub (instantiate bodies substRhs) = contractum := by
  constructor
  · rfl
  · rfl

/-- **The equation holds of that pair**, as an instance of the authored axiom. -/
theorem subst_evaluates : EqClosure patE redexTerm contractum := by
  have h := EqClosure.ax_closed (E := patE) (Γ := []) ⟨0, by decide⟩ bodies emptySub
  exact h

/-! ## Agreement with the existing evaluation

The presentation is faithful as a semantics, not only as a syntax: erasing the
contractum gives exactly what the language-definition layer's own
binder-eliminating substitution produces from the erased parts. -/

theorem erase_redex :
    erase redexTerm = .subst (.lambda (some "q") (.bvar 1)) (.apply "R" []) := rfl

/-- **The signature's substitution is the existing one, after erasure.**  The
replacement is carried under the inner binder on both sides. -/
theorem erase_contractum_agrees :
    erase contractum = instantiateBVar (erase replR) (erase bodyB) := by
  decide +kernel

/-- And the value it produces is the expected one. -/
theorem contractum_value :
    erase contractum = .lambda (some "q") (.apply "R" []) := rfl

/-- **The equation has content**: the two sides are different terms, related only
by the theory. -/
theorem redex_ne_contractum : redexTerm ≠ contractum := by
  intro h
  have he := congrArg erase h
  rw [erase_redex, contractum_value] at he
  exact absurd he (by decide)

/-! ## The closed axiom generates the open instances

Nothing further is authored for terms in a context: the equational theory is
closed under substitution, proved once for every signature, so an instance at
the empty context transports. -/

theorem subst_evaluates_everywhere {Γ : Ctx patSig} (sigma : Sub patSig [] Γ) :
    EqClosure patE (bind sigma redexTerm) (bind sigma contractum) :=
  eqClosure_bind sigma subst_evaluates

/-! ## Agreement, for every term

The instance above is now a special case.  The signature's substitution and the
language-definition layer's binder-eliminating one are the same operation after
erasure -- not on a checked example, but for all bodies and all replacements. -/

theorem argsToSub_single_eq_extend (R : Term patSig [] PatSrt.pat) :
    argsToSub (Args.cons R Args.nil) = extend R := by
  funext s v
  cases v with
  | zero => rfl
  | succ w => exact nomatch w

/-- **The explicit substitution's evaluation is the existing one, always.** -/
theorem erase_contractum_general (B : Term patSig [PatSrt.pat] PatSrt.pat)
    (R : Term patSig [] PatSrt.pat) :
    erase (bind (argsToSub (Args.cons R Args.nil)) B)
      = instantiateBVar (erase R) (erase B) := by
  rw [argsToSub_single_eq_extend]
  exact erase_bind_extend R B

/-- The checked instance is the general theorem at one point. -/
theorem erase_contractum_agrees' :
    erase contractum = instantiateBVar (erase replR) (erase bodyB) :=
  erase_contractum_general bodyB replR

end PatternSubst

end Mettapedia.OSLF.Binding
