import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Judgment

/-!
# Weak-head steps of annotated terms, with root steps and scrutinee steps

`CWhStepR P roles` is one weak-head step of annotated terms, for an annotated rule
package `P` and the roles of its constants:

* β, and the projections of a pair;
* a declared annotated root step;
* a step in the function position of an application, or under a projection;
* a step at the argument that a computing constant inspects, when its skeleton is
  one constructor inspection and the constant is applied to exactly its arity
  (`scrutinee`).

**Erasure** (`CWhStepR.erase`): a step erases to a weak-head step of the rule
package. So an annotated term whose erasure is a weak-head normal form takes no
step (`CWhStepR.not_of_whnf`).

**Determinism** (`CWhStepR.deterministic`): when the rule package has root shape
and its annotated root steps are deterministic, a term takes at most one step. Two
different rules never apply to one term: an abstraction, a pair, a spine of a
computing constant below its arity and an accepted scrutinee are weak-head normal
forms of the rule package, and that is read off the erasures.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (Roles Inspection InspectTree WhStep RootShape Whnf)

variable {Head : Type}

/-! ## Spines of constants -/

namespace CTm

/-- The head of an annotated term and its arguments. -/
def headArgs : {n : Nat} → CTm Head n → CTm Head n × List (CTm Head n)
  | _, .app f a => ((headArgs f).1, (headArgs f).2 ++ [a])
  | _, t => (t, [])

theorem headArgs_appSpine_const {n : Nat} (c : DeclName) (as : List (CTm Head n)) :
    headArgs (appSpine (.const c) as) = (.const c, as) := by
  induction as using List.reverseRecOn with
  | nil => rfl
  | append_singleton as a ih =>
      rw [appSpine_concat]
      show ((headArgs (appSpine (.const c) as)).1, (headArgs (appSpine (.const c) as)).2 ++ [a]) = _
      rw [ih]

/-- Two spines of constants are equal only at one constant and equal arguments. -/
theorem appSpine_const_injective {n : Nat} {c c' : DeclName} {as bs : List (CTm Head n)}
    (equal : appSpine (.const c) as = appSpine (.const c') bs) : c = c' ∧ as = bs := by
  have h := congrArg headArgs equal
  rw [headArgs_appSpine_const, headArgs_appSpine_const] at h
  injection h with h₁ h₂
  injection h₁ with _ h₁
  exact ⟨h₁, h₂⟩

theorem appSpine_const_ne_lamApp {n : Nat} {c : DeclName} {as : List (CTm Head n)}
    {A a : CTm Head n} {body : CTm Head (n + 1)} :
    appSpine (.const c) as ≠ .app (.lam A body) a := fun h =>
  Normalization.appSpine_const_ne_lam (by have e := congrArg erase h; rwa [erase_appSpine] at e)

theorem appSpine_const_ne_fst {n : Nat} {c : DeclName} {as : List (CTm Head n)}
    {p : CTm Head n} : appSpine (.const c) as ≠ .fst p := fun h =>
  Normalization.appSpine_const_ne_fst (by have e := congrArg erase h; rwa [erase_appSpine] at e)

theorem appSpine_const_ne_snd {n : Nat} {c : DeclName} {as : List (CTm Head n)}
    {p : CTm Head n} : appSpine (.const c) as ≠ .snd p := fun h =>
  Normalization.appSpine_const_ne_snd (by have e := congrArg erase h; rwa [erase_appSpine] at e)

end CTm

/-! ## The steps -/

variable {R : Rules Head}

/-- One weak-head step of annotated terms: β, the projections of a pair, a declared
root step, a step in the function position of an application or under a
projection, and a step at the argument that a computing constant with a single
constructor inspection inspects, the constant being applied to exactly its
arity. -/
inductive CWhStepR (P : ChurchRules R) (roles : Roles Head) :
    {n : Nat} → CTm Head n → CTm Head n → Prop
  | beta {n : Nat} (A : CTm Head n) (body : CTm Head (n + 1)) (a : CTm Head n) :
      CWhStepR P roles (.app (.lam A body) a) (CTm.inst0 a body)
  | fstPair {n : Nat} (a b : CTm Head n) : CWhStepR P roles (.fst (.pair a b)) a
  | sndPair {n : Nat} (a b : CTm Head n) : CWhStepR P roles (.snd (.pair a b)) b
  | root {n : Nat} {t u : CTm Head n} : P.computation.step t u → CWhStepR P roles t u
  | appFun {n : Nat} {f f' a : CTm Head n} :
      CWhStepR P roles f f' → CWhStepR P roles (.app f a) (.app f' a)
  | fst {n : Nat} {p p' : CTm Head n} :
      CWhStepR P roles p p' → CWhStepR P roles (.fst p) (.fst p')
  | snd {n : Nat} {p p' : CTm Head n} :
      CWhStepR P roles p p' → CWhStepR P roles (.snd p) (.snd p')
  | scrutinee {n : Nat} {c : DeclName} {arity : Nat} {before after : List (CTm Head n)}
      {a a' : CTm Head n} :
      roles c = .computes arity (.split before.length .constructor fun _ => .leaf) →
      before.length + 1 + after.length = arity →
      CWhStepR P roles a a' →
      CWhStepR P roles (CTm.appSpine (.const c) (before ++ a :: after))
        (CTm.appSpine (.const c) (before ++ a' :: after))

section Erasure

variable {P : ChurchRules R} {roles : Roles Head}

/-- **Erasure**: an annotated step erases to a weak-head step of the rule package. -/
theorem CWhStepR.erase {n : Nat} {t u : CTm Head n} (step : CWhStepR P roles t u) :
    WhStep R roles t.erase u.erase := by
  induction step with
  | beta A body a =>
      rw [CTm.erase_inst0]
      exact .beta _ _
  | fstPair a b => exact .fstPair _ _
  | sndPair a b => exact .sndPair _ _
  | root s => exact .root (P.erase_step s)
  | appFun _ ih => exact .appFun ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | @scrutinee c arity before after a a' role length _ ih =>
      rw [CTm.erase_appSpine, CTm.erase_appSpine, List.map_append, List.map_append,
        List.map_cons, List.map_cons]
      have role' : roles c = .computes arity
          (.split (before.map CTm.erase).length .constructor fun _ => .leaf) := by
        rw [List.length_map]
        exact role
      exact Normalization.WhStep.scrutinee_single role'
        (by rw [List.length_map, List.length_map]; exact length) ih

/-- An annotated term whose erasure is a weak-head normal form takes no step. -/
theorem CWhStepR.not_of_whnf {n : Nat} {t : CTm Head n} (normal : Whnf R roles t.erase)
    (u : CTm Head n) : ¬ CWhStepR P roles t u :=
  fun step => normal _ step.erase

end Erasure

/-! ## Determinism -/

section Determinism

variable {P : ChurchRules R} {roles : Roles Head} (shape : RootShape R roles)
include shape

/-- The erasure of a root redex is a spine of a constant. -/
theorem CWhStepR.root_constSpine {n : Nat} {t u : CTm Head n} (step : P.computation.step t u) :
    ∃ c args, t.erase = Normalization.appSpine (.const c) args := by
  obtain ⟨c, _, _, args, _, e, _⟩ := shape.spine (P.erase_step step)
  exact ⟨c, args, e⟩

/-- The function of an application whose erasure is a spine of a computing constant
of exact arity takes no step: it is a spine below the arity. -/
theorem CWhStepR.not_fun_of_exact {n : Nat} {f a : CTm Head n} {c : DeclName} {arity : Nat}
    {inspect : InspectTree} (role : roles c = .computes arity inspect)
    {args : List (Tm Head n)} (e : (CTm.app f a).erase = Normalization.appSpine (.const c) args)
    (length : args.length = arity) (f' : CTm Head n) : ¬ CWhStepR P roles f f' := by
  intro step
  obtain ⟨init, rfl, hf⟩ := Normalization.appSpine_const_eq_app e.symm
  have short : init.length < arity := by
    rw [← length, List.length_append, List.length_singleton]
    exact Nat.lt_succ_self _
  exact Normalization.partialSpine_whnf shape role short _ (hf ▸ step.erase)

/-- The function of a root redex that is an application takes no step. -/
theorem CWhStepR.not_fun_of_root {n : Nat} {f a u : CTm Head n}
    (root : P.computation.step (.app f a) u) (f' : CTm Head n) : ¬ CWhStepR P roles f f' := by
  obtain ⟨c, arity, inspect, args, role, e, length, _⟩ := shape.spine (P.erase_step root)
  exact CWhStepR.not_fun_of_exact shape role e length f'

/-- The function of a spine of a computing constant of exact arity takes no step. -/
theorem CWhStepR.not_fun_of_spine {n : Nat} {c : DeclName} {arity : Nat}
    {inspect : InspectTree} (role : roles c = .computes arity inspect)
    {args : List (CTm Head n)} (length : args.length = arity) {f a : CTm Head n}
    (e : CTm.appSpine (.const c) args = .app f a) (f' : CTm Head n) :
    ¬ CWhStepR P roles f f' := by
  have e' : (CTm.app f a).erase = Normalization.appSpine (.const c) (args.map CTm.erase) := by
    rw [← e, CTm.erase_appSpine]
    rfl
  exact CWhStepR.not_fun_of_exact shape role e' (by rw [List.length_map]; exact length) f'

/-- The inspected argument of a root redex takes no step: the root step's
erasure accepts it, and what an inspection accepts is a weak-head normal form. -/
theorem CWhStepR.not_scrutinee_of_root {n : Nat} {c : DeclName} {arity : Nat}
    {before after : List (CTm Head n)} {x u : CTm Head n}
    (role : roles c = .computes arity (.split before.length .constructor fun _ => .leaf))
    (root : P.computation.step (CTm.appSpine (.const c) (before ++ x :: after)) u)
    (x' : CTm Head n) : ¬ CWhStepR P roles x x' := by
  intro step
  obtain ⟨c', arity', inspect', args', role', e, _, accepts⟩ := shape.spine (P.erase_step root)
  rw [CTm.erase_appSpine] at e
  obtain ⟨hc, hargs⟩ := Normalization.appSpine_const_injective e
  subst hc hargs
  rw [role] at role'
  injection role' with _ hinspect
  subst hinspect
  rw [List.map_append, List.map_cons] at accepts
  have focus : (InspectTree.split before.length .constructor fun _ => .leaf).Focus roles
      (before.map CTm.erase ++ x.erase :: after.map CTm.erase)
      (before.map CTm.erase ++ x.erase :: after.map CTm.erase) .constructor x.erase x.erase :=
    .here (List.length_map _)
  exact Inspection.Accepts.whnf shape (focus.accepted accepts) _ step.erase

variable (rootDet : ∀ {n : Nat} {t u u' : CTm Head n}, P.computation.step t u →
  P.computation.step t u' → u = u')
include rootDet

/-- **Determinism**: when the rule package has root shape and the annotated root
steps are deterministic, an annotated term takes at most one weak-head step. -/
theorem CWhStepR.deterministic {n : Nat} {t u : CTm Head n} (first : CWhStepR P roles t u) :
    ∀ {u' : CTm Head n}, CWhStepR P roles t u' → u' = u := by
  induction first with
  | beta A body a =>
      intro u' second
      generalize hterm : CTm.app (.lam A body) a = term at second
      cases second with
      | beta => cases hterm; rfl
      | appFun inner =>
          cases hterm
          exact absurd inner (CWhStepR.not_of_whnf (Normalization.lam_whnf shape _) _)
      | root step =>
          subst hterm
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_lam
      | scrutinee => exact absurd hterm.symm CTm.appSpine_const_ne_lamApp
      | fstPair => cases hterm
      | sndPair => cases hterm
      | fst => cases hterm
      | snd => cases hterm
  | fstPair a b =>
      intro u' second
      generalize hterm : CTm.fst (.pair a b) = term at second
      cases second with
      | fstPair => cases hterm; rfl
      | fst inner =>
          cases hterm
          exact absurd inner (CWhStepR.not_of_whnf (Normalization.pair_whnf shape _ _) _)
      | root step =>
          subst hterm
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_fst
      | scrutinee => exact absurd hterm.symm CTm.appSpine_const_ne_fst
      | beta => cases hterm
      | sndPair => cases hterm
      | appFun => cases hterm
      | snd => cases hterm
  | sndPair a b =>
      intro u' second
      generalize hterm : CTm.snd (.pair a b) = term at second
      cases second with
      | sndPair => cases hterm; rfl
      | snd inner =>
          cases hterm
          exact absurd inner (CWhStepR.not_of_whnf (Normalization.pair_whnf shape _ _) _)
      | root step =>
          subst hterm
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_snd
      | scrutinee => exact absurd hterm.symm CTm.appSpine_const_ne_snd
      | beta => cases hterm
      | fstPair => cases hterm
      | appFun => cases hterm
      | fst => cases hterm
  | @root t u step =>
      intro u' second
      cases second with
      | root step' => exact rootDet step' step
      | appFun inner => exact absurd inner (CWhStepR.not_fun_of_root shape step _)
      | scrutinee role _ inner =>
          exact absurd inner (CWhStepR.not_scrutinee_of_root shape role step _)
      | beta =>
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_lam
      | fstPair =>
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_fst
      | sndPair =>
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_snd
      | fst =>
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_fst
      | snd =>
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_snd
  | @appFun f f' a inner ih =>
      intro u' second
      generalize hterm : CTm.app f a = term at second
      cases second with
      | appFun inner' =>
          cases hterm
          rw [ih inner']
      | beta =>
          cases hterm
          exact absurd inner (CWhStepR.not_of_whnf (Normalization.lam_whnf shape _) _)
      | root step =>
          subst hterm
          exact absurd inner (CWhStepR.not_fun_of_root shape step _)
      | scrutinee role length _ =>
          exact absurd inner (CWhStepR.not_fun_of_spine shape role
            (by rw [List.length_append, List.length_cons]; omega) hterm.symm _)
      | fstPair => cases hterm
      | sndPair => cases hterm
      | fst => cases hterm
      | snd => cases hterm
  | @fst p p' inner ih =>
      intro u' second
      generalize hterm : CTm.fst p = term at second
      cases second with
      | fst inner' =>
          cases hterm
          rw [ih inner']
      | fstPair =>
          cases hterm
          exact absurd inner (CWhStepR.not_of_whnf (Normalization.pair_whnf shape _ _) _)
      | root step =>
          subst hterm
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_fst
      | scrutinee => exact absurd hterm.symm CTm.appSpine_const_ne_fst
      | beta => cases hterm
      | sndPair => cases hterm
      | appFun => cases hterm
      | snd => cases hterm
  | @snd p p' inner ih =>
      intro u' second
      generalize hterm : CTm.snd p = term at second
      cases second with
      | snd inner' =>
          cases hterm
          rw [ih inner']
      | sndPair =>
          cases hterm
          exact absurd inner (CWhStepR.not_of_whnf (Normalization.pair_whnf shape _ _) _)
      | root step =>
          subst hterm
          obtain ⟨c, args, e⟩ := CWhStepR.root_constSpine shape step
          exact absurd e.symm Normalization.appSpine_const_ne_snd
      | scrutinee => exact absurd hterm.symm CTm.appSpine_const_ne_snd
      | beta => cases hterm
      | fstPair => cases hterm
      | appFun => cases hterm
      | fst => cases hterm
  | @scrutinee c arity before after x x' role length inner ih =>
      intro u' second
      generalize hterm : CTm.appSpine (.const c) (before ++ x :: after) = term at second
      cases second with
      | @scrutinee c₂ arity₂ before₂ after₂ y y' role₂ length₂ inner₂ =>
          obtain ⟨rfl, hlist⟩ := CTm.appSpine_const_injective hterm
          rw [role] at role₂
          injection role₂ with _ hinspect
          injection hinspect with hpos
          obtain ⟨rfl, rfl, rfl⟩ := Normalization.appendCons_inj hlist hpos
          rw [ih inner₂]
      | root step =>
          subst hterm
          exact absurd inner (CWhStepR.not_scrutinee_of_root shape role step _)
      | appFun inner' =>
          exact absurd inner' (CWhStepR.not_fun_of_spine shape role
            (by rw [List.length_append, List.length_cons]; omega) hterm _)
      | beta => exact absurd hterm CTm.appSpine_const_ne_lamApp
      | fstPair => exact absurd hterm CTm.appSpine_const_ne_fst
      | sndPair => exact absurd hterm CTm.appSpine_const_ne_snd
      | fst => exact absurd hterm CTm.appSpine_const_ne_fst
      | snd => exact absurd hterm CTm.appSpine_const_ne_snd

end Determinism

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
