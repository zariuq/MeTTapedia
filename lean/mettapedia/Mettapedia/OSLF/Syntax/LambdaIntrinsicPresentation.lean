import Mettapedia.OSLF.Syntax.LambdaContextualRung
import Mettapedia.OSLF.Syntax.ContextualRootEvents

/-!
# Lambda beta as an intrinsic rewrite presentation

The Chapter 7 lambda relation contains an unconditional beta schema and
three closure rules. This module expresses beta in the existing binding
signature presentation, with a continuation metavariable of arity one and an
argument metavariable of arity zero. The comparison with the four-rule
contextual relation is made on actual open beta instances. The generic
unpositioned presentation's old `Step` remains closed-term-only and is not
identified with LamCong on open bodies.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaIntrinsicPresentation

open Mettapedia.OSLF.Binding.LambdaContextualRung

abbrev metas : List (MetaArity sig) :=
  [([Srt.term], Srt.term), ([], Srt.term)]

abbrev schemaSig : Signature := withMetas sig metas

private def schemaApp {Γ : Ctx schemaSig}
    (funTerm arg : Term schemaSig Γ .term) : Term schemaSig Γ .term :=
  .op (Sum.inl Op.app) (.cons funTerm (.cons arg .nil))

private def schemaLam {Γ : Ctx schemaSig}
    (body : Term schemaSig (.term :: Γ) .term) : Term schemaSig Γ .term :=
  .op (Sum.inl Op.lam) (.cons body .nil)

/-- The body metavariable is applied to its allowed bound argument. -/
private def bodyAt {Γ : Ctx schemaSig} (arg : Term schemaSig Γ .term) :
    Term schemaSig Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 0)) (.cons arg .nil)

/-- The application argument is a metavariable with no bound dependencies. -/
private def argAt {Γ : Ctx schemaSig} : Term schemaSig Γ .term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 1)) .nil

/-- `App (Lam (F x)) A` -- both metavariable arities are explicit. -/
def betaLhs : Term schemaSig [] .term :=
  schemaApp (schemaLam (bodyAt (.var .zero))) argAt

/-- `F A`; instantiation performs capture-avoiding substitution. -/
def betaRhs : Term schemaSig [] .term :=
  bodyAt argAt

def betaRule : UnpositionedRewrite schemaSig where
  ctx := []
  sort := .term
  lhs := betaLhs
  rhs := betaRhs

def betaPresentation : UnpositionedPresentation sig where
  metas := metas
  eqs := []
  rules := [betaRule]

/-- Give the two metavariables actual intrinsic bodies. -/
def assignment (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    (i : Fin metas.length) → Term sig (metas.get i).1 (metas.get i).2
  | ⟨0, _⟩ => body
  | ⟨1, _⟩ => arg
  | ⟨_ + 2, impossible⟩ => by simp [metas] at impossible

private theorem assignment_zero (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    assignment body arg (0 : Fin metas.length) = body := by rfl

private theorem assignment_one (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    assignment body arg (1 : Fin metas.length) = arg := by rfl

private theorem bind_closed (sigma : Sub sig [] [])
    (t : Term sig [] .term) : bind sigma t = t := by
  have h : sigma = (fun _ v => .var v) := by
    funext r v
    nomatch v
  rw [h]
  exact bind_id t

private theorem bind_single_identity (body : Term sig [Srt.term] .term) :
    bind (argsToSub (Args.cons (Term.var Var.zero) Args.nil)) body = body := by
  have h : argsToSub (Args.cons (Term.var Var.zero) Args.nil) =
      (fun _ v => .var v : Sub sig [Srt.term] [Srt.term]) := by
    funext r v
    cases v with
    | zero => rfl
    | succ v => nomatch v
  rw [h]
  exact bind_id body

/-- The generic schema's left endpoint is exactly lambda application. -/
theorem instantiate_beta_lhs (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    instantiate (assignment body arg) betaLhs = appT (lamT body) arg := by
  simp only [betaLhs, schemaApp, schemaLam, bodyAt, argAt,
    instantiate, instantiateArgs, assignment_zero, assignment_one]
  rw [bind_single_identity, bind_closed]
  rfl

/-- Its right endpoint is the same capture-avoiding plug used in the
context-indexed beta rule. -/
theorem instantiate_beta_rhs (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    instantiate (assignment body arg) betaRhs = inst body arg := by
  simp only [betaRhs, bodyAt, argAt,
    instantiate, instantiateArgs, assignment_zero, assignment_one]
  rw [bind_closed]
  have h : argsToSub (Args.cons arg Args.nil) = extend arg := by
    funext s v
    cases v with
    | zero => rfl
    | succ v => nomatch v
  rw [h]
  rfl

/-- Every closed beta instance of the four-rule relation is an authored
root firing of the intrinsic unconditional presentation. -/
theorem beta_root_instance (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    betaRule.RootStep (appT (lamT body) arg) (inst body arg) := by
  refine ⟨assignment body arg, (fun _ v => nomatch v), ?_, ?_⟩
  · exact (bind_closed _ _).trans (instantiate_beta_lhs body arg)
  · exact (bind_closed _ _).trans (instantiate_beta_rhs body arg)

/-- The same source and target satisfy the textbook beta rule. -/
theorem beta_scoped_instance (body : Term sig [Srt.term] .term)
    (arg : Term sig [] .term) :
    LambdaContextualRung.Step [] (appT (lamT body) arg) (inst body arg) :=
  .beta body arg

/-- Every closed firing of this intrinsic beta schema, and only such a
firing, has the textbook beta source and its capture-avoiding target. -/
theorem beta_root_iff (source target : Term sig [] .term) :
    betaRule.RootStep source target ↔
      ∃ (body : Term sig [Srt.term] .term) (arg : Term sig [] .term),
        source = appT (lamT body) arg ∧ target = inst body arg := by
  constructor
  · rintro ⟨supplied, close, hsource, htarget⟩
    change Sub sig [] [] at close
    change bind close (instantiate supplied betaLhs) = source at hsource
    change bind close (instantiate supplied betaRhs) = target at htarget
    have hsupplied : supplied = assignment (supplied 0) (supplied 1) := by
      funext i
      fin_cases i
      · exact (assignment_zero (supplied 0) (supplied 1)).symm
      · exact (assignment_one (supplied 0) (supplied 1)).symm
    refine ⟨supplied 0, supplied 1, ?_, ?_⟩
    · rw [bind_closed, hsupplied, instantiate_beta_lhs] at hsource
      exact hsource.symm
    · rw [bind_closed, hsupplied, instantiate_beta_rhs] at htarget
      exact htarget.symm
  · rintro ⟨body, arg, rfl, rfl⟩
    exact beta_root_instance body arg

/-- A generic closed beta firing is one rule of the least contextual
lambda relation; the latter also contains its congruence closure. -/
theorem beta_root_to_contextual {source target : Term sig [] .term}
    (firing : betaRule.RootStep source target) :
    LambdaContextualRung.Step [] source target := by
  obtain ⟨body, arg, rfl, rfl⟩ := (beta_root_iff source target).mp firing
  exact beta_scoped_instance body arg

end Mettapedia.OSLF.Binding.LambdaIntrinsicPresentation
