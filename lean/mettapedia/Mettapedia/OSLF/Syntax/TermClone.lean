import Mettapedia.OSLF.Syntax.SyntacticCategory
import Mettapedia.GSLT.LanguageDef.MultiSortedClone

/-!
# Terms of a binding signature are a multisorted clone

The unit and associativity of substitution were proved for their own sake and
then read again as the laws of a category of contexts.  They are also exactly
the laws of a *multisorted clone*, which this project already had: an abstract
operation with an ordered context of input sorts and one output sort, with
positional variables and simultaneous substitution.  Rather than let the two
developments sit beside each other, the terms of a binding signature are made an
instance of the existing structure here, so everything proved about clones
applies to them.

The one thing that has to be reconciled is how a variable is named.  A clone
indexes its inputs positionally, by a `Fin` into the context together with the
sort that position carries; this development indexes them by a typed de Bruijn
index, which is the same information arranged so that the sort is a parameter
rather than a projection.  The translation between the two is definitional in
one direction and structural in the other, and it is arranged here so that no
transport appears anywhere: the recursion peels the context and the `Fin`
together, so each clause's sort equation holds by reduction.
-/

namespace Mettapedia.OSLF.Binding

open Mettapedia.GSLT.LanguageDef

set_option autoImplicit false

variable {S : Signature}

/-! ## Positional and typed names for a variable -/

/-- The position a typed variable occupies. -/
def varIdx {Γ : Ctx S} {s : S.Srt} : Var Γ s → Fin Γ.length
  | .zero => ⟨0, Nat.succ_pos _⟩
  | .succ w => (varIdx w).succ

/-- The sort at that position is the variable's own sort. -/
theorem get_varIdx {Γ : Ctx S} {s : S.Srt} : ∀ (v : Var Γ s), Γ.get (varIdx v) = s
  | .zero => rfl
  | .succ w => get_varIdx w

/-- The typed variable at a position. -/
def varOfIdx : (Γ : Ctx S) → (i : Fin Γ.length) → Var Γ (Γ.get i)
  | _ :: _, ⟨0, _⟩ => .zero
  | _ :: Γ, ⟨_ + 1, h⟩ => .succ (varOfIdx Γ ⟨_, Nat.lt_of_succ_lt_succ h⟩)

theorem varIdx_varOfIdx : ∀ (Γ : Ctx S) (i : Fin Γ.length), varIdx (varOfIdx Γ i) = i
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: Γ, ⟨k + 1, h⟩ => by
      show (varIdx (varOfIdx Γ ⟨k, _⟩)).succ = _
      rw [varIdx_varOfIdx Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩]
      rfl

/-! ## Simultaneous substitution from a positional environment

Defined by peeling the context and the position together, so that every clause's
sort equation holds by reduction and no transport is needed. -/

/-- Read a positional environment as a substitution. -/
def substVar {Γ Δ : Ctx S} (env : (i : Fin Γ.length) → Term S Δ (Γ.get i)) :
    (s : S.Srt) → Var Γ s → Term S Δ s :=
  match Γ, env with
  | [], _ => fun _ v => nomatch v
  | _ :: _, env => fun _ v =>
      match v with
      | .zero => env ⟨0, Nat.succ_pos _⟩
      | .succ w => substVar (fun i => env i.succ) _ w

/-- At a position, the substitution returns what the environment said. -/
theorem substVar_varOfIdx : ∀ (Γ : Ctx S) {Δ : Ctx S}
    (env : (i : Fin Γ.length) → Term S Δ (Γ.get i)) (i : Fin Γ.length),
    substVar env _ (varOfIdx Γ i) = env i
  | _ :: _, _, _, ⟨0, _⟩ => rfl
  | _ :: Γ, _, env, ⟨k + 1, h⟩ => by
      show substVar (fun i => env i.succ) _ (varOfIdx Γ ⟨k, _⟩) = _
      rw [substVar_varOfIdx Γ (fun i => env i.succ) ⟨k, Nat.lt_of_succ_lt_succ h⟩]
      rfl

/-- Every substitution is read off its own positional environment, so the two
descriptions of a substitution carry the same information. -/
theorem substVar_of_sub : ∀ {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) {s : S.Srt}
    (v : Var Γ s), substVar (fun i => sigma _ (varOfIdx Γ i)) s v = sigma s v
  | _ :: _, _, _, _, .zero => rfl
  | _ :: Γ, _, sigma, _, .succ w =>
      substVar_of_sub (Γ := Γ) (fun s v => sigma s (Var.succ v)) w

/-- Substituting into an environment is substituting into what it denotes. -/
theorem substVar_bind : ∀ {Γ Δ Θ : Ctx S}
    (env : (i : Fin Γ.length) → Term S Δ (Γ.get i)) (sigma : Sub S Δ Θ)
    {s : S.Srt} (v : Var Γ s),
    substVar (fun i => bind sigma (env i)) s v = bind sigma (substVar env s v)
  | _ :: _, _, _, _, _, _, .zero => rfl
  | _ :: Γ, _, _, env, sigma, _, .succ w =>
      substVar_bind (Γ := Γ) (fun i => env i.succ) sigma w

/-! ## The instance -/

/-- **Terms of a binding signature are a multisorted clone.**  Its operations at
a context are the terms of that context, its variables are the positional
projections, and its simultaneous substitution is substitution.  The three laws
are `bind_id`, `bind_comp` and the variable clause of `bind`. -/
def termClone (S : Signature) : MultiSortedClone S.Srt where
  Hom Γ s := Term S Γ s
  project i := Term.var (varOfIdx _ i)
  substitute t env := bind (substVar env) t
  substitute_project env i := by
    show bind (substVar env) (Term.var (varOfIdx _ i)) = env i
    rw [bind]
    exact substVar_varOfIdx _ env i
  substitute_projects t := by
    show bind (substVar (fun i => Term.var (varOfIdx _ i))) t = t
    rw [show substVar (fun i => Term.var (varOfIdx _ i))
        = (fun _ v => Term.var v : Sub S _ _) from
      funext fun s => funext fun v => substVar_of_sub (fun _ w => Term.var w) v]
    exact bind_id t
  substitute_assoc t first second := by
    show bind (substVar second) (bind (substVar first) t)
      = bind (substVar (fun i => bind (substVar second) (first i))) t
    rw [bind_comp]
    exact congrArg (fun sigma => bind sigma t)
      (funext fun s => funext fun v => (substVar_bind first (substVar second) v).symm)

@[simp] theorem termClone_Hom (S : Signature) (Γ : Ctx S) (s : S.Srt) :
    (termClone S).Hom Γ s = Term S Γ s := rfl

@[simp] theorem termClone_substitute {Γ Δ : Ctx S} {s : S.Srt} (t : Term S Γ s)
    (env : (i : Fin Γ.length) → Term S Δ (Γ.get i)) :
    (termClone S).substitute t env = bind (substVar env) t := rfl

/-! ## The two presentations of the category of contexts agree

The clone comes with its own category of contexts, whose morphisms are
positional environments.  This development's category of contexts has typed
substitutions as morphisms.  They are the same category: the hom-sets are in
bijection, and the bijection takes identities to identities and composition to
composition.  So neither presentation is a duplicate of the other -- one is the
instance of the abstract structure and the other is the form the rest of this
development uses. -/

/-- A positional environment is a substitution, and conversely. -/
def envEquivSub (S : Signature) (Γ Δ : Ctx S) :
    ((termClone S).Environment Δ Γ) ≃ Sub S Γ Δ where
  toFun env := substVar env
  invFun sigma i := sigma _ (varOfIdx Γ i)
  left_inv env := by
    funext i
    exact substVar_varOfIdx Γ env i
  right_inv sigma := by
    funext s v
    exact substVar_of_sub sigma v

/-- The bijection takes the clone's identity to the identity substitution. -/
theorem envEquivSub_id (S : Signature) (Γ : Ctx S) :
    envEquivSub S Γ Γ (fun i => (termClone S).project i)
      = (fun _ v => Term.var v : Sub S Γ Γ) :=
  funext fun _ => funext fun v => substVar_of_sub (fun _ w => Term.var w) v

/-- And composition to composition. -/
theorem envEquivSub_comp (S : Signature) {Γ Δ Θ : Ctx S}
    (later : (termClone S).Environment Δ Γ)
    (earlier : (termClone S).Environment Θ Δ) :
    envEquivSub S Γ Θ (fun i => (termClone S).substitute (later i) earlier)
      = (fun s v => bind (envEquivSub S Δ Θ earlier) (envEquivSub S Γ Δ later s v)) := by
  funext s v
  exact substVar_bind later (substVar earlier) v

end Mettapedia.OSLF.Binding
