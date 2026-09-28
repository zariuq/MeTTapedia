import Mettapedia.OSLF.Syntax.ContextualLinearSubstitution

/-!
# The context-indexed lambda reduction rung

The four rules in Finding Mind 7.10 are beta, left and right application
congruence, and abstraction congruence. The last rule relates bodies in the
context extended by the abstraction's bound variable. The existing closed
`Step` relation cannot itself state that premise; this relation records the
context in its index and reuses the intrinsic binder-aware substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaContextualRung

inductive Srt where
  | term
  deriving DecidableEq

inductive Op : Srt → Type where
  | app : Op .term
  | lam : Op .term

def sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} op => match op with
    | .app => [([], .term), ([], .term)]
    | .lam => [([.term], .term)]

def appT {Γ : Ctx sig} (funTerm arg : Term sig Γ .term) :
    Term sig Γ .term :=
  .op .app (.cons funTerm (.cons arg .nil))

def lamT {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) :
    Term sig Γ .term :=
  .op .lam (.cons body .nil)

@[simp] theorem bind_appT {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (funTerm arg : Term sig Γ .term) :
    bind sigma (appT funTerm arg) =
      appT (bind sigma funTerm) (bind sigma arg) := rfl

@[simp] theorem bind_lamT {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (body : Term sig (.term :: Γ) .term) :
    bind sigma (lamT body) =
      lamT (bind (liftSub sigma [.term]) body) := rfl

/-- The least four-rule relation over terms in an explicit sorted context.
`lamCong` invokes the relation in the context extended by the binder. -/
inductive Step : (Γ : Ctx sig) → Term sig Γ .term →
    Term sig Γ .term → Prop where
  | beta {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term)
      (arg : Term sig Γ .term) :
      Step Γ (appT (lamT body) arg) (inst body arg)
  | appCongL {Γ : Ctx sig} {source target : Term sig Γ .term}
      (arg : Term sig Γ .term) :
      Step Γ source target →
      Step Γ (appT source arg) (appT target arg)
  | appCongR {Γ : Ctx sig} {source target : Term sig Γ .term}
      (funTerm : Term sig Γ .term) :
      Step Γ source target →
      Step Γ (appT funTerm source) (appT funTerm target)
  | lamCong {Γ : Ctx sig}
      {source target : Term sig (.term :: Γ) .term} :
      Step (.term :: Γ) source target →
      Step Γ (lamT source) (lamT target)

/-- Every source rule remains valid after an arbitrary simultaneous
substitution of its ambient variables. The beta case uses the actual
binder-aware plug/substitution interchange law. -/
theorem substitute {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ) :
    ∀ {source target : Term sig Γ .term},
      Step Γ source target →
      Step Δ (bind sigma source) (bind sigma target)
  | _, _, .beta body arg => by
      have commuting :
          bind sigma (inst body arg) =
            inst (bind (liftSub sigma [.term]) body) (bind sigma arg) :=
        ContextualLinearSubstitution.bind_inst sigma body arg
      rw [bind_appT, bind_lamT, commuting]
      exact Step.beta (Γ := Δ)
        (bind (liftSub sigma [.term]) body) (bind sigma arg)
  | _, _, .appCongL arg step => by
      simpa only [bind_appT] using
        (Step.appCongL (bind sigma arg) (substitute sigma step))
  | _, _, .appCongR funTerm step => by
      simpa only [bind_appT] using
        (Step.appCongR (bind sigma funTerm) (substitute sigma step))
  | _, _, .lamCong step => by
      rw [bind_lamT, bind_lamT]
      exact Step.lamCong (Γ := Δ)
        (substitute (liftSub sigma [.term]) step)

/-- A beta redex in an abstraction body may consume the abstraction's bound
variable. The result still names that binder, rather than closing or capturing
it at the outer root. -/
theorem open_beta_uses_bound_variable :
    Step [.term]
      (appT (lamT (.var .zero)) (.var .zero))
      (.var .zero) := by
  have hplug :
      inst (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
          (Term.var (Var.zero : Var [Srt.term] Srt.term)) =
        (Term.var Var.zero : Term sig [Srt.term] Srt.term) :=
    inst_hole _
  have firing := Step.beta (Γ := [.term])
    (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
    (Term.var (Var.zero : Var [Srt.term] Srt.term))
  rw [hplug] at firing
  exact firing

/-- The LamCong rule closes the preceding open premise into a closed step. -/
theorem closed_step_from_open_body :
    Step []
      (lamT (appT (lamT (.var .zero)) (.var .zero)))
      (lamT (.var .zero)) :=
  Step.lamCong open_beta_uses_bound_variable

/-- Variables alone are inert in this four-rule reduction relation. -/
theorem variable_has_no_step {Γ : Ctx sig} (v : Var Γ .term)
    {target : Term sig Γ .term} : ¬ Step Γ (.var v) target := by
  intro h
  cases h

/-- The open premise is nontrivial: its redex and reduct have different
constructors even though both live in the same binder context. -/
theorem open_beta_changes_term :
    appT (lamT (.var (.zero : Var [Srt.term, Srt.term] Srt.term)))
        (.var (.zero : Var [Srt.term] Srt.term)) ≠
      (.var (.zero : Var [Srt.term] Srt.term) : Term sig [Srt.term] Srt.term) := by
  intro equal
  cases equal

/-- The target of the LamCong premise really depends on the surrounding
binder. It cannot be supplied as a weakened closed root term. -/
theorem bound_result_not_closed :
    ¬ ∃ closed : Term sig [] .term,
      weaken closed = (.var .zero : Term sig [.term] .term) := by
  rintro ⟨closed, equality⟩
  have count := holeCount_weaken (c := Srt.term) closed
  rw [equality] at count
  exact Nat.zero_ne_one count.symm

end Mettapedia.OSLF.Binding.LambdaContextualRung
