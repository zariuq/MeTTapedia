import Mettapedia.Languages.Agda.Intrinsic.Rules

/-!
# Interpreting the authored Agda schemas in the free binding clone

These equations compute the endpoints and premise contexts of arbitrary
open rule instances. In particular, a binder-dependent metavariable receives
the newly opened variable while retaining its ambient dependencies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Authored

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

abbrev algebra := BindingCloneAlgebra.terms sig
abbrev Val (Γ : Ctx sig) := Valuation (M := metas) algebra Γ

def emptyClose (Γ : Ctx sig) : Sub sig [] Γ := fun _ v => nomatch v

def eval0 {Γ : Ctx sig} (v : Val Γ) (t : STm []) : Tm Γ :=
  interpretSchema algebra v (fun _ x => .var x) (emptyClose Γ) t

def eval1 {Γ : Ctx sig} (v : Val Γ) (t : STm [.term]) : Tm (.term :: Γ) :=
  interpretSchema algebra v
    (weakenEnvironment algebra [.term] (fun _ x => .var x))
    (algebra.substitution.liftEnvironment (emptyClose Γ) [.term]) t

@[simp] theorem eval0_m0 {Γ : Ctx sig} (v : Val Γ) :
    eval0 v m0 = v 2 := bind_id _
@[simp] theorem eval0_m1 {Γ : Ctx sig} (v : Val Γ) :
    eval0 v m1 = v 3 := bind_id _
@[simp] theorem eval0_m2 {Γ : Ctx sig} (v : Val Γ) :
    eval0 v m2 = v 4 := bind_id _
@[simp] theorem eval0_m3 {Γ : Ctx sig} (v : Val Γ) :
    eval0 v m3 = v 5 := bind_id _
@[simp] theorem eval0_m4 {Γ : Ctx sig} (v : Val Γ) :
    eval0 v m4 = v 6 := bind_id _
@[simp] theorem eval0_m5 {Γ : Ctx sig} (v : Val Γ) :
    eval0 v m5 = v 7 := bind_id _

@[simp] theorem eval1_b0 {Γ : Ctx sig} (v : Val Γ) :
    eval1 v (b0 (.var .zero)) = v 0 := by
  change bind _ (v 0) = v 0
  trans bind (fun _ x => Term.var x) (v 0)
  · congr 1
    funext s x
    cases x <;> rfl
  · exact bind_id _

@[simp] theorem eval0_b0 {Γ : Ctx sig} (v : Val Γ) (arg : STm []) :
    eval0 v (b0 arg) = inst (v 0) (eval0 v arg) := by
  change bind _ (v 0) = bind (extend (eval0 v arg)) (v 0)
  congr 1
  funext s x
  cases x <;> rfl

@[simp] theorem eval1_b1 {Γ : Ctx sig} (v : Val Γ) :
    eval1 v (b1 (.var .zero)) = v 1 := by
  change bind _ (v 1) = v 1
  trans bind (fun _ x => Term.var x) (v 1)
  · congr 1
    funext s x
    cases x <;> rfl
  · exact bind_id _

@[simp] theorem eval0_b1 {Γ : Ctx sig} (v : Val Γ) (arg : STm []) :
    eval0 v (b1 arg) = inst (v 1) (eval0 v arg) := by
  change bind _ (v 1) = bind (extend (eval0 v arg)) (v 1)
  congr 1
  funext s x
  cases x <;> rfl

@[simp] theorem eval0_pi {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) (x1 : STm [.term]) :
    eval0 v (piS x0 x1) =
      pi (eval0 v x0) (eval1 v x1) := rfl

@[simp] theorem eval0_lam {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm [.term]) :
    eval0 v (lamS x0) =
      lam (eval1 v x0) := rfl

@[simp] theorem eval0_app {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) (x1 : STm []) :
    eval0 v (appS x0 x1) =
      app (eval0 v x0) (eval0 v x1) := rfl

@[simp] theorem eval0_ann {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) (x1 : STm []) :
    eval0 v (annS x0 x1) =
      ann (eval0 v x0) (eval0 v x1) := rfl

@[simp] theorem eval0_sigma {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) (x1 : STm [.term]) :
    eval0 v (sigmaS x0 x1) =
      sigma (eval0 v x0) (eval1 v x1) := rfl

@[simp] theorem eval0_pair {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) (x1 : STm []) :
    eval0 v (pairS x0 x1) =
      pair (eval0 v x0) (eval0 v x1) := rfl

@[simp] theorem eval0_fst {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) :
    eval0 v (fstS x0) =
      fst (eval0 v x0) := rfl

@[simp] theorem eval0_snd {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) :
    eval0 v (sndS x0) =
      snd (eval0 v x0) := rfl

@[simp] theorem eval0_suc {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) :
    eval0 v (sucS x0) =
      suc (eval0 v x0) := rfl

@[simp] theorem eval0_natrec {Γ : Ctx sig} (v : Val Γ)
    (x0 : STm []) (x1 : STm []) (x2 : STm []) (x3 : STm []) (x4 : STm []) :
    eval0 v (natrecS x0 x1 x2 x3 x4) =
      natrec (eval0 v x0) (eval0 v x1) (eval0 v x2) (eval0 v x3) (eval0 v x4) := rfl

@[simp] theorem eval0_zero {Γ : Ctx sig} (v : Val Γ)
     :
    eval0 v (zeroS ) =
      zero  := rfl

@[simp] theorem eval0_natSuc {Γ : Ctx sig} (v : Val Γ)
     :
    eval0 v (natSucS ) =
      natSuc  := rfl

/-- The ordinary empty context has exactly one closing environment. -/
theorem close_unique {Γ : Ctx sig} (close : Sub sig [] Γ) :
    close = emptyClose Γ := by
  funext s x
  nomatch x

def occurrence {Γ : Ctx sig} (i : Fin rules.length) (v : Val Γ) :
    Instance rules algebra where
  index := i
  ambient := Γ
  valuation := v
  close := by
    have h : (rules.get i).conclusion.ctx = [] := by
      fin_cases i <;> rfl
    rw [h]
    exact emptyClose Γ

theorem occurrence_complete (o : Instance rules algebra) :
    o = occurrence o.index o.valuation := by
  rcases o with ⟨i, Γ, v, close⟩
  have h : (rules.get i).conclusion.ctx = [] := by
    fin_cases i <;> rfl
  congr 1
  funext s x
  have impossible : Var ([] : List Srt) s := h ▸ x
  nomatch impossible

end Mettapedia.Languages.Agda.Intrinsic.Authored
