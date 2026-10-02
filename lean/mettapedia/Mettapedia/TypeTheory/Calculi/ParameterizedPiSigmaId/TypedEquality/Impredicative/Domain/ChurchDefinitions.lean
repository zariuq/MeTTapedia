import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Erasure

/-!
# Readings that agree on a term, and constants defined by one equation

**Agreement.** The interpretation of an annotated term reads only the heads and the
constants the term mentions (`termConsts`): two readings that agree on these
interpret it alike (`cinterp_congr`). The interpretation of an application spine is
the iterated application of the interpretations (`cinterp_appSpine`).

**Abstraction over a context.** `lamsCtx Θ E` abstracts `E` over the annotated
context `Θ`, its first entry outermost, and `pisCtx Θ T` is the dependent function
type of `T` over `Θ`. The environment of a list of arguments (`Env.ofArgs`) has the
first argument as its oldest variable. For every list of arguments:

* the instantiation of `pisCtx Θ T` at the arguments is the interpretation of `T`
  at the arguments projected onto their parameter types (`instPi_cinterp_pisCtx`);
* the interpretation of `lamsCtx Θ E` applied to the arguments is the interpretation
  of `E` there (`appSpine_cinterp_lamsCtx`).

**A constant defined by one equation** `f x₁ ⋯ x_k ⟶ E`, declared at `pisCtx Θ T`,
is read as the abstraction of `E` over `Θ` projected onto its declared type
(`defConst`). At arguments that are elements of their parameter types it is `E`
there, projected onto `T` there (`appSpine_defConst`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

open Annotated (CTm CCtx)
open Ideal

variable {Head : Type}

/-! ## The rigid types -/

namespace Ideal

/-- A ground type: its only element is the least one. -/
def groundI : Ideal := principal Elem.ground

theorem typeGenerated_natI : TypeGenerated natI := typeGenerated_principal nat_type

theorem typeGenerated_groundI : TypeGenerated groundI :=
  typeGenerated_principal (Elem.ty_tag (k := .ground) trivial Elem.isUniv_univ)

theorem typeGenerated_codesIdeal : TypeGenerated codesIdeal :=
  typeGenerated_principal (Elem.ty_tag (k := .codes) trivial Elem.isUniv_univ)

theorem typeGenerated_univIdeal : TypeGenerated univIdeal :=
  typeGenerated_principal Elem.ty_univ_univ

end Ideal

/-! ## Agreement of readings -/

/-- The constants an annotated term mentions. -/
def termConsts : {n : Nat} → CTm Head n → List DeclName
  | _, .var _ => []
  | _, .const c => [c]
  | _, .head _ => []
  | _, .pi A B => termConsts A ++ termConsts B
  | _, .sigma A B => termConsts A ++ termConsts B
  | _, .id A a b => termConsts A ++ (termConsts a ++ termConsts b)
  | _, .lam A b => termConsts A ++ termConsts b
  | _, .app f a => termConsts f ++ termConsts a
  | _, .pair a b => termConsts a ++ termConsts b
  | _, .fst p => termConsts p
  | _, .snd p => termConsts p
  | _, .refl a => termConsts a

/-- **The interpretation of a term reads only the heads and the constants the term
mentions.** -/
theorem cinterp_congr {Rd Rd' : Reading Head} (heads : Rd.head = Rd'.head) :
    ∀ {n : Nat} (t : CTm Head n), (∀ c ∈ termConsts t, Rd.const c = Rd'.const c) →
      cinterp Rd t = cinterp Rd' t := by
  intro n t
  induction t with
  | var i => exact fun _ => rfl
  | const c =>
      intro h
      funext ρ
      exact h c List.mem_cons_self
  | head h =>
      intro _
      funext ρ
      show principal (Rd.head h) = principal (Rd'.head h)
      rw [heads]
  | pi A B ihA ihB =>
      intro h
      have eA := ihA fun c hc => h c (List.mem_append_left _ hc)
      have eB := ihB fun c hc => h c (List.mem_append_right _ hc)
      funext ρ
      show cpi (cinterp Rd A ρ) (fun y => cinterp Rd B (Env.cons y ρ)) =
        cpi (cinterp Rd' A ρ) (fun y => cinterp Rd' B (Env.cons y ρ))
      rw [eA, eB]
  | sigma A B ihA ihB =>
      intro h
      have eA := ihA fun c hc => h c (List.mem_append_left _ hc)
      have eB := ihB fun c hc => h c (List.mem_append_right _ hc)
      funext ρ
      show csigma (cinterp Rd A ρ) (fun y => cinterp Rd B (Env.cons y ρ)) =
        csigma (cinterp Rd' A ρ) (fun y => cinterp Rd' B (Env.cons y ρ))
      rw [eA, eB]
  | id A a b ihA iha ihb =>
      intro h
      have eA := ihA fun c hc => h c (List.mem_append_left _ hc)
      have ea := iha fun c hc => h c (List.mem_append_right _ (List.mem_append_left _ hc))
      have eb := ihb fun c hc => h c (List.mem_append_right _ (List.mem_append_right _ hc))
      funext ρ
      show ident (cinterp Rd A ρ) (cinterp Rd a ρ) (cinterp Rd b ρ) =
        ident (cinterp Rd' A ρ) (cinterp Rd' a ρ) (cinterp Rd' b ρ)
      rw [eA, ea, eb]
  | lam A b ihA ihb =>
      intro h
      have eA := ihA fun c hc => h c (List.mem_append_left _ hc)
      have eb := ihb fun c hc => h c (List.mem_append_right _ hc)
      funext ρ
      show clam (cinterp Rd A ρ) (fun y => cinterp Rd b (Env.cons y ρ)) =
        clam (cinterp Rd' A ρ) (fun y => cinterp Rd' b (Env.cons y ρ))
      rw [eA, eb]
  | app f a ihf iha =>
      intro h
      have ef := ihf fun c hc => h c (List.mem_append_left _ hc)
      have ea := iha fun c hc => h c (List.mem_append_right _ hc)
      funext ρ
      show app (cinterp Rd f ρ) (cinterp Rd a ρ) = app (cinterp Rd' f ρ) (cinterp Rd' a ρ)
      rw [ef, ea]
  | pair a b iha ihb =>
      intro h
      have ea := iha fun c hc => h c (List.mem_append_left _ hc)
      have eb := ihb fun c hc => h c (List.mem_append_right _ hc)
      funext ρ
      show pair (cinterp Rd a ρ) (cinterp Rd b ρ) = pair (cinterp Rd' a ρ) (cinterp Rd' b ρ)
      rw [ea, eb]
  | fst p ih =>
      intro h
      have e := ih h
      funext ρ
      show fst (cinterp Rd p ρ) = fst (cinterp Rd' p ρ)
      rw [e]
  | snd p ih =>
      intro h
      have e := ih h
      funext ρ
      show snd (cinterp Rd p ρ) = snd (cinterp Rd' p ρ)
      rw [e]
  | refl a ih =>
      intro h
      have e := ih h
      funext ρ
      show refl (cinterp Rd a ρ) = refl (cinterp Rd' a ρ)
      rw [e]

/-- The interpretation of an application spine is the iterated application of the
interpretations. -/
theorem cinterp_appSpine (Rd : Reading Head) {n : Nat} (ρ : Env n) :
    ∀ (f : CTm Head n) (args : List (CTm Head n)),
      cinterp Rd (CTm.appSpine f args) ρ = appSpine (cinterp Rd f ρ) (args.map (cinterp Rd · ρ))
  | _, [] => rfl
  | f, a :: as => cinterp_appSpine Rd ρ (.app f a) as

/-- Substitution into an application spine. -/
theorem csubst_appSpine {n m : Nat} (σ : Annotated.CSub Head n m) :
    ∀ (f : CTm Head n) (args : List (CTm Head n)),
      (CTm.appSpine f args).subst σ = CTm.appSpine (f.subst σ) (args.map (CTm.subst σ))
  | _, [] => rfl
  | f, a :: as => csubst_appSpine σ (.app f a) as

@[simp] theorem cinterp_const (Rd : Reading Head) {n : Nat} (c : DeclName) (ρ : Env n) :
    cinterp Rd (.const c : CTm Head n) ρ = Rd.const c := rfl

/-! ## Environments of arguments -/

/-- The environment of a list of arguments: the first argument is the oldest
variable. -/
def Env.ofArgs (k : Nat) (args : List Ideal) : Env k := fun i => args.getD (k - 1 - i.val) bot

theorem Env.ofArgs_zero (args : List Ideal) : Env.ofArgs 0 args = Env.nil :=
  funext fun i => i.elim0

/-- Two environments of no variable are equal. -/
theorem Env.eq_nil (f g : Env 0) : f = g := funext fun i => i.elim0

/-- Two environments are equal when they agree at the newest variable and at the others. -/
theorem Env.eq_cons {n : Nat} {f g : Env (n + 1)} (h0 : f 0 = g 0)
    (hs : (fun i : Fin n => f i.succ) = fun i => g i.succ) : f = g :=
  funext fun i => Fin.cases h0 (fun j => congrFun hs j) i

/-- One more argument is the newest variable. -/
theorem Env.ofArgs_snoc {k : Nat} {args : List Ideal} (hlen : args.length = k) (a : Ideal) :
    Env.ofArgs (k + 1) (args ++ [a]) = Env.cons a (Env.ofArgs k args) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show (args ++ [a]).getD (k + 1 - 1 - 0) bot = a
    rw [show k + 1 - 1 - 0 = args.length by omega, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · show (args ++ [a]).getD (k + 1 - 1 - (j.val + 1)) bot = args.getD (k - 1 - j.val) bot
    have hj := j.isLt
    rw [show k + 1 - 1 - (j.val + 1) = k - 1 - j.val by omega, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]

/-! ## Projected arguments -/

theorem length_projArgs :
    ∀ (T : Ideal) (args : List Ideal), (projArgs T args).length = args.length
  | _, [] => rfl
  | _, _ :: ys => congrArg (· + 1) (length_projArgs _ ys)

theorem projArgs_singleton (T a : Ideal) : projArgs T [a] = [projT (dom .pi T) a] := rfl

theorem projArgs_append :
    ∀ (T : Ideal) (xs ys : List Ideal),
      projArgs T (xs ++ ys) = projArgs T xs ++ projArgs (instPi T xs) ys
  | _, [], _ => rfl
  | T, x :: xs, ys => by
      show projT (dom .pi T) x :: projArgs (fam .pi T (projT (dom .pi T) x)) (xs ++ ys) =
        projT (dom .pi T) x :: (projArgs (fam .pi T (projT (dom .pi T) x)) xs ++
          projArgs (instPi (fam .pi T (projT (dom .pi T) x)) xs) ys)
      rw [projArgs_append]

/-! ## Abstraction over a context -/

/-- The abstraction of a body over an annotated context, its first entry outermost. -/
def lamsCtx : {k : Nat} → CCtx Head k → CTm Head k → CTm Head 0
  | _, .nil, E => E
  | _, .snoc Θ A, E => lamsCtx Θ (.lam A E)

/-- The dependent function type of a body over an annotated context. -/
def pisCtx : {k : Nat} → CCtx Head k → CTm Head k → CTm Head 0
  | _, .nil, T => T
  | _, .snoc Θ A, T => pisCtx Θ (.pi A T)

theorem piArity_pisCtx : ∀ {k : Nat} (Θ : CCtx Head k) (T : CTm Head k),
    piArity (pisCtx Θ T) = k + piArity T
  | _, .nil, T => (Nat.zero_add _).symm
  | _, .snoc Θ A, T => by
      show piArity (pisCtx Θ (.pi A T)) = _
      rw [piArity_pisCtx Θ (.pi A T)]
      show _ + (piArity T + 1) = _
      omega

/-- **The dependent function type over a context, instantiated at arguments**, is its
body at the arguments projected onto their parameter types. -/
theorem instPi_cinterp_pisCtx (Rd : Reading Head) :
    ∀ {k : Nat} (Θ : CCtx Head k) (T : CTm Head k) (args : List Ideal), args.length = k →
      instPi (cinterp Rd (pisCtx Θ T) Env.nil) args =
        cinterp Rd T (Env.ofArgs k (projArgs (cinterp Rd (pisCtx Θ T) Env.nil) args))
  | _, .nil, T, args, hlen => by
      rw [List.eq_nil_of_length_eq_zero hlen, Env.ofArgs_zero]
      rfl
  | k + 1, .snoc Θ A, T, args, hlen => by
      rcases List.eq_nil_or_concat args with rfl | ⟨xs, a, rfl⟩
      · exact absurd hlen (Ne.symm (Nat.succ_ne_zero k))
      rw [List.concat_eq_append] at hlen ⊢
      have hxs : xs.length = k := by simpa using hlen
      show instPi (cinterp Rd (pisCtx Θ (.pi A T)) Env.nil) (xs ++ [a]) =
        cinterp Rd T (Env.ofArgs (k + 1)
          (projArgs (cinterp Rd (pisCtx Θ (.pi A T)) Env.nil) (xs ++ [a])))
      have ih := instPi_cinterp_pisCtx Rd Θ (.pi A T) xs hxs
      rw [instPi_append, ih, projArgs_append, ih, projArgs_singleton,
        Env.ofArgs_snoc (by rw [length_projArgs, hxs]), instPi_cinterp_pi, dom_cinterp_pi]
      rfl

/-- **The abstraction over a context, applied to arguments**, is its body at the
arguments projected onto their parameter types. -/
theorem appSpine_cinterp_lamsCtx (Rd : Reading Head) :
    ∀ {k : Nat} (Θ : CCtx Head k) (E T : CTm Head k) (args : List Ideal), args.length = k →
      appSpine (cinterp Rd (lamsCtx Θ E) Env.nil) args =
        cinterp Rd E (Env.ofArgs k (projArgs (cinterp Rd (pisCtx Θ T) Env.nil) args))
  | _, .nil, E, _, args, hlen => by
      rw [List.eq_nil_of_length_eq_zero hlen, Env.ofArgs_zero]
      rfl
  | k + 1, .snoc Θ A, E, T, args, hlen => by
      rcases List.eq_nil_or_concat args with rfl | ⟨xs, a, rfl⟩
      · exact absurd hlen (Ne.symm (Nat.succ_ne_zero k))
      rw [List.concat_eq_append] at hlen ⊢
      have hxs : xs.length = k := by simpa using hlen
      show appSpine (cinterp Rd (lamsCtx Θ (.lam A E)) Env.nil) (xs ++ [a]) =
        cinterp Rd E (Env.ofArgs (k + 1)
          (projArgs (cinterp Rd (pisCtx Θ (.pi A T)) Env.nil) (xs ++ [a])))
      rw [appSpine_append, appSpine_cinterp_lamsCtx Rd Θ (.lam A E) (.pi A T) xs hxs,
        projArgs_append, instPi_cinterp_pisCtx Rd Θ (.pi A T) xs hxs, projArgs_singleton,
        Env.ofArgs_snoc (by rw [length_projArgs, hxs]), dom_cinterp_pi]
      exact app_cinterp_lam Rd A E _ a

/-! ## Constants defined by one equation -/

/-- **The Church constant of a definition by one equation** `f x₁ ⋯ x_k ⟶ E` declared at
`pisCtx Θ T`: the abstraction of `E` over `Θ`, projected onto the declared type. -/
def defConst (Rd : Reading Head) {k : Nat} (Θ : CCtx Head k) (T E : CTm Head k) : Ideal :=
  projT (cinterp Rd (pisCtx Θ T) Env.nil) (cinterp Rd (lamsCtx Θ E) Env.nil)

/-- **A definition by one equation computes**: at arguments that are elements of their
parameter types, it is its right side at the arguments, projected onto the declared
codomain there. -/
theorem appSpine_defConst (Rd : Reading Head) {k : Nat} (Θ : CCtx Head k) (T E : CTm Head k)
    {args : List Ideal} (hlen : args.length = k)
    (spine : SpineTyped (cinterp Rd (pisCtx Θ T) Env.nil) args) :
    appSpine (defConst Rd Θ T E) args =
      projT (cinterp Rd T (Env.ofArgs k args)) (cinterp Rd E (Env.ofArgs k args)) := by
  have hT := churchTele_cinterp Rd (pisCtx Θ T) Env.nil
  rw [defConst, appSpine_churchConst _ hT (by rw [piArity_pisCtx]; omega) spine,
    instPi_cinterp_pisCtx Rd Θ T args hlen, appSpine_cinterp_lamsCtx Rd Θ E T args hlen,
    projArgs_of_spineTyped spine]

/-- The instantiation of the declared type of a definition at arguments that are
elements of their parameter types. -/
theorem instPi_pisCtx_of_spineTyped (Rd : Reading Head) {k : Nat} (Θ : CCtx Head k)
    (T : CTm Head k) {args : List Ideal} (hlen : args.length = k)
    (spine : SpineTyped (cinterp Rd (pisCtx Θ T) Env.nil) args) :
    instPi (cinterp Rd (pisCtx Θ T) Env.nil) args = cinterp Rd T (Env.ofArgs k args) := by
  rw [instPi_cinterp_pisCtx Rd Θ T args hlen, projArgs_of_spineTyped spine]

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
