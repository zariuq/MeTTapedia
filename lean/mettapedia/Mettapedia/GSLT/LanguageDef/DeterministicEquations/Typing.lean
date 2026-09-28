import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Termination

/-!
# Typed programs return values of their sorts

A typing of a program gives each sort of values its meaning, a predicate on
values, and gives heads at an arity a signature: argument sorts and a result
sort. Right sides are typed under the sorts of the variables in scope. A
program is well typed when:

* every call of a typed head that some equation defines at that arity, on
  arguments of its argument sorts, is taken by some equation (coverage);
* every equation of a typed head types its right side at the result sort,
  under sorts its left side binds soundly: matching arguments of the argument
  sorts binds each variable to a value of its sort;
* a typed head that is defined only at other arities is not called;
* a typed head no equation defines is answered by the host, or is a
  constructor, with a value of the result sort.

Then no typed call fails: with any fuel, a call of a typed head on arguments
of its argument sorts runs out of fuel or returns a value of its result sort
(`apply_typed`). Termination is separate: under a descent certificate some
fuel ends the call (`apply_terminates`), so it returns a value of its result
sort (`apply_returns`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-- A typing of values and heads. -/
structure Typing where
  /-- The sorts of values. -/
  sorts : Type
  /-- The values of a sort. -/
  holds : sorts → Term → Prop
  /-- The signature of a head at an arity, if it is typed. -/
  sig : String → Nat → Option (List sorts × sorts)

namespace Typing

variable (T : Typing)

/-- Sorts of the variables in scope, the newest first. -/
abbrev Ctx := List (String × T.sorts)

/-- The sort a variable has in scope. -/
def Ctx.lookup {T : Typing} (Γ : T.Ctx) (x : String) : Option T.sorts :=
  (List.find? (fun b => b.1 == x) Γ).map (·.2)

mutual

/-- A right side has a sort under the sorts in scope. -/
inductive HasType : T.Ctx → Term → T.sorts → Prop where
  | var (Γ : T.Ctx) (x : String) (S : T.sorts) (h : Γ.lookup x = some S) :
      HasType Γ (.var x) S
  | sym (Γ : T.Ctx) (s : String) (S : T.sorts) (h : T.holds S (.sym s)) :
      HasType Γ (.sym s) S
  | lit (Γ : T.Ctx) (s : String) (S : T.sorts) (h : T.holds S (.lit s)) :
      HasType Γ (.lit s) S
  | unit (Γ : T.Ctx) (S : T.sorts) (h : T.holds S (.expr [])) : HasType Γ (.expr []) S
  | bind (Γ : T.Ctx) (x : String) (e b : Term) (S₁ S : T.sorts) (he : HasType Γ e S₁)
      (hb : HasType ((x, S₁) :: Γ) b S) :
      HasType Γ (.expr [.sym "let", .var x, e, b]) S
  | nullary (Γ : T.Ctx) (s : String) (S : T.sorts) (h : T.holds S (.expr [.sym s])) :
      HasType Γ (.expr [.sym "metta-nullary", .sym s]) S
  | call (Γ : T.Ctx) (f : String) (args : List Term) (Ss : List T.sorts) (S : T.sorts)
      (hs : ¬ Special f args) (hsig : T.sig f args.length = some (Ss, S))
      (ha : HasTypes Γ args Ss) : HasType Γ (.expr (.sym f :: args)) S
  | tuple (Γ : T.Ctx) (hd : Term) (items : List Term) (Ss : List T.sorts) (S : T.sorts)
      (hh : ∀ s, hd ≠ .sym s) (ha : HasTypes Γ (hd :: items) Ss)
      (hS : ∀ vs, List.Forall₂ T.holds Ss vs → T.holds S (.expr vs)) :
      HasType Γ (.expr (hd :: items)) S
  | list (Γ : T.Ctx) (items : List Term) (Ss : List T.sorts) (S : T.sorts)
      (ha : HasTypes Γ items Ss)
      (hS : ∀ vs, List.Forall₂ T.holds Ss vs → T.holds S (.list vs)) :
      HasType Γ (.list items) S

/-- Terms have sorts in order. -/
inductive HasTypes : T.Ctx → List Term → List T.sorts → Prop where
  | nil (Γ : T.Ctx) : HasTypes Γ [] []
  | cons (Γ : T.Ctx) (t : Term) (ts : List Term) (S : T.sorts) (Ss : List T.sorts)
      (h : HasType Γ t S) (hs : HasTypes Γ ts Ss) : HasTypes Γ (t :: ts) (S :: Ss)

end

/-- Bindings give each variable in scope a value of its sort. -/
def Sat (ρ : Env) (Γ : T.Ctx) : Prop :=
  ∀ x S, Γ.lookup x = some S → ∃ v, ρ.lookup x = some v ∧ T.holds S v

end Typing

open Typing

/-- A program is well typed under a typing and a host. -/
structure WellTyped (T : Typing) (P : Program) (H : Host) : Prop where
  covers : ∀ f Ss S vs, T.sig f vs.length = some (Ss, S) → List.Forall₂ T.holds Ss vs →
    P.definesAt f vs.length = true → (P.select f vs).isSome
  bodies : ∀ e ∈ P, ∀ Ss S, T.sig e.head e.params.length = some (Ss, S) →
    ∃ Γ, HasType T Γ e.body S ∧
      ∀ vs σ, List.Forall₂ T.holds Ss vs → matchTerms e.params vs = some σ → Sat T σ Γ
  arity : ∀ f n Ss S, T.sig f n = some (Ss, S) → P.definesAt f n = false → P.defines f = false
  host : ∀ f Ss S vs, T.sig f vs.length = some (Ss, S) → List.Forall₂ T.holds Ss vs →
    P.defines f = false →
    (H.primitive f vs = .unhandled ∧ T.holds S (.expr (.sym f :: vs))) ∨
      ∃ v, H.primitive f vs = .value v ∧ T.holds S v

/-- An outcome that is fuel exhaustion or a value of a sort. -/
def Ends (T : Typing) (S : T.sorts) (o : Outcome) : Prop :=
  o = .exhausted ∨ ∃ v, o = .value v ∧ T.holds S v

theorem Ctx.lookup_cons_self {T : Typing} (x : String) (S : T.sorts) (Γ : T.Ctx) :
    Typing.Ctx.lookup ((x, S) :: Γ) x = some S := by
  have h : (fun b : String × T.sorts => b.1 == x) (x, S) = true := string_beq_self x
  unfold Typing.Ctx.lookup
  rw [List.find?_cons_of_pos (p := fun b : String × T.sorts => b.1 == x) (a := (x, S)) h]
  rfl

theorem Ctx.lookup_cons_ne {T : Typing} {x y : String} (S : T.sorts) (Γ : T.Ctx) (h : x ≠ y) :
    Typing.Ctx.lookup ((x, S) :: Γ) y = Typing.Ctx.lookup Γ y := by
  have hb : (x == y) = false := by simpa using h
  simp [Typing.Ctx.lookup, hb]

theorem Typing.Sat.extend {T : Typing} {ρ : Env} {Γ : T.Ctx} (h : Sat T ρ Γ) (x : String) {S : T.sorts}
    {v : Term} (hv : T.holds S v) : Sat T ((x, v) :: ρ) ((x, S) :: Γ) := by
  intro y S' hy
  by_cases hxy : x = y
  · subst hxy
    rw [Ctx.lookup_cons_self] at hy
    cases hy
    exact ⟨v, Env.lookup_cons_self x v ρ, hv⟩
  · rw [Ctx.lookup_cons_ne S Γ hxy] at hy
    obtain ⟨u, hu, hsu⟩ := h y S' hy
    exact ⟨u, by rw [Env.lookup_cons_ne v ρ hxy]; exact hu, hsu⟩

section Soundness

variable {T : Typing} {P : Program} {H : Host}

/-- Terms of sorts, each evaluated by an evaluation that ends in values of
their sorts, evaluate in order to values of the sorts or stop on exhaustion. -/
theorem items_typed {ev : Env → Term → Outcome} {ρ : Env} {Γ : T.Ctx}
    (hev : ∀ t S, HasType T Γ t S → Ends T S (ev ρ t)) :
    ∀ {ts : List Term} {Ss : List T.sorts}, HasTypes T Γ ts Ss →
      evalItemsWith ev ρ ts = .stop .exhausted ∨
        ∃ vs, evalItemsWith ev ρ ts = .values vs ∧ List.Forall₂ T.holds Ss vs
  | [], [], _ => .inr ⟨[], rfl, .nil⟩
  | t :: ts, S :: Ss, h => by
    cases h with
    | cons _ _ _ _ _ ht hts =>
      rcases hev t S ht with hx | ⟨v, hv, hsv⟩
      · left
        simp [evalItemsWith, hx]
      · rcases items_typed hev hts with hstop | ⟨vs, hvs, hsvs⟩
        · left
          simp [evalItemsWith, hv, hstop]
        · right
          exact ⟨v :: vs, by simp [evalItemsWith, hv, hvs], .cons hsv hsvs⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- A call of a typed head on arguments of its sorts, with bodies evaluated by
an evaluation that ends in values of their sorts, ends in a value of the
result sort. -/
theorem applyWith_typed (hT : WellTyped T P H) {ev : Env → Term → Outcome}
    (hev : ∀ σ Γ t S, HasType T Γ t S → Sat T σ Γ → Ends T S (ev σ t))
    {f : String} {vs : List Term} {Ss : List T.sorts} {S : T.sorts}
    (hsig : T.sig f vs.length = some (Ss, S)) (hvs : List.Forall₂ T.holds Ss vs) :
    Ends T S (applyWith P H ev f vs) := by
  cases hdef : P.definesAt f vs.length with
  | true =>
    obtain ⟨⟨e, σ⟩, hsel⟩ := Option.isSome_iff_exists.1 (hT.covers f Ss S vs hsig hvs hdef)
    obtain ⟨he, hhead, hmatch⟩ := select_spec hsel
    have hlen := matchTerms_length hmatch
    obtain ⟨Γ, hbody, hbind⟩ := hT.bodies e he Ss S (by rw [hhead, hlen]; exact hsig)
    have hres : applyWith P H ev f vs = ev σ e.body := by
      simp only [applyWith, hdef, if_true, hsel]
    rw [hres]
    exact hev σ Γ e.body S hbody (hbind vs σ hvs hmatch)
  | false =>
    have hnd := hT.arity f vs.length Ss S hsig hdef
    rw [applyWith_primitive hdef hnd]
    rcases hT.host f Ss S vs hsig hvs hnd with ⟨hu, hs⟩ | ⟨v, hv, hs⟩
    · rw [hu]
      exact .inr ⟨_, rfl, hs⟩
    · rw [hv]
      exact .inr ⟨v, rfl, hs⟩

/-- Typed right sides never fail: with any fuel they run out of fuel or return
a value of their sort. -/
theorem eval_typed (hT : WellTyped T P H) :
    ∀ (n : Nat) (ρ : Env) (Γ : T.Ctx) (t : Term) (S : T.sorts), HasType T Γ t S → Sat T ρ Γ →
      Ends T S (eval P H n ρ t) := by
  intro n
  induction n with
  | zero =>
    intro ρ Γ t S _ _
    exact .inl rfl
  | succ n ih =>
    intro ρ Γ t S ht hρ
    have hev : ∀ t' S', HasType T Γ t' S' → Ends T S' (eval P H n ρ t') :=
      fun t' S' h' => ih ρ Γ t' S' h' hρ
    show Ends T S (evalStep (eval P H n) (applyWith P H (eval P H n)) ρ t)
    cases ht with
    | var _ x _ hx =>
      obtain ⟨v, hv, hs⟩ := hρ x S hx
      exact .inr ⟨v, by simp [evalStep, hv], hs⟩
    | sym _ s _ h => exact .inr ⟨_, by simp [evalStep], h⟩
    | lit _ s _ h => exact .inr ⟨_, by simp [evalStep], h⟩
    | unit _ _ h => exact .inr ⟨_, by simp [evalStep], h⟩
    | bind _ x e b S₁ _ he hb =>
      rcases ih ρ Γ e S₁ he hρ with hx | ⟨v, hv, hs⟩
      · left
        simp [evalStep, hx]
      · have := ih ((x, v) :: ρ) ((x, S₁) :: Γ) b S hb (hρ.extend x hs)
        simpa [evalStep, hv] using this
    | nullary _ s _ h => exact .inr ⟨_, by simp [evalStep], h⟩
    | call _ f args Ss _ hs hsig ha =>
      rw [evalStep_head hs]
      rcases items_typed hev ha with hstop | ⟨vs, hvs, hsvs⟩
      · rw [hstop]
        exact .inl rfl
      · rw [hvs]
        have hlen : vs.length = args.length := (evalItemsWith_forall₂ hvs).length_eq.symm
        exact applyWith_typed hT (fun σ Γ' t' S' h' hσ => ih σ Γ' t' S' h' hσ)
          (by rw [hlen]; exact hsig) hsvs
    | tuple _ hd items Ss _ hh ha hS =>
      rw [evalStep_items hh]
      rcases items_typed hev ha with hstop | ⟨vs, hvs, hsvs⟩
      · rw [hstop]
        exact .inl rfl
      · rw [hvs]
        exact .inr ⟨_, rfl, hS vs hsvs⟩
    | list _ items Ss _ ha hS =>
      show Ends T S (match evalItemsWith (eval P H n) ρ items with
        | .values vs => .value (.list vs)
        | .stop o => o)
      rcases items_typed hev ha with hstop | ⟨vs, hvs, hsvs⟩
      · rw [hstop]
        exact .inl rfl
      · rw [hvs]
        exact .inr ⟨_, rfl, hS vs hsvs⟩

/-- No typed call fails: with any fuel, a call of a typed head on arguments of
its argument sorts runs out of fuel or returns a value of its result sort. -/
theorem apply_typed (hT : WellTyped T P H) (n : Nat) {f : String} {vs : List Term}
    {Ss : List T.sorts} {S : T.sorts} (hsig : T.sig f vs.length = some (Ss, S))
    (hvs : List.Forall₂ T.holds Ss vs) : Ends T S (apply P H n f vs) :=
  applyWith_typed hT (fun σ Γ t S h hσ => eval_typed hT n σ Γ t S h hσ) hsig hvs

/-- A typed call of a descending program on arguments of its argument sorts
returns a value of its result sort. -/
theorem apply_returns {V : Vocabulary} {c : Certificate} (hD : Descends P V c) (hK : Keeps V H)
    (hT : WellTyped T P H) {f : String} {vs : List Term} {Ss : List T.sorts} {S : T.sorts}
    (hsig : T.sig f vs.length = some (Ss, S)) (hvs : List.Forall₂ T.holds Ss vs) :
    ∃ n v, apply P H n f vs = .value v ∧ T.holds S v := by
  obtain ⟨n, hn⟩ := apply_terminates hD hK f vs
  rcases apply_typed hT n hsig hvs with hx | ⟨v, hv, hs⟩
  · exact absurd hx hn
  · exact ⟨n, v, hv, hs⟩

end Soundness

/-! ## Examples

`double` on unary numbers is well typed: `zero` is a number and `succ` of a
number is one, and each call of `double` on a number returns a number. A right
side that names a variable its left side does not bind has no type, and its
call fails. -/

namespace TypingExamples

/-- Unary numbers as values. -/
inductive IsNat : Term → Prop where
  | zero : IsNat (.sym "zero")
  | succ (n : Term) (h : IsNat n) : IsNat (.expr [.sym "succ", n])

def doubleZero : Equation := ⟨"double-zero", "double", [.sym "zero"], .sym "zero"⟩
def doubleSucc : Equation :=
  ⟨"double-succ", "double", [.expr [.sym "succ", .var "x"]],
    .expr [.sym "succ", .expr [.sym "succ", .expr [.sym "double", .var "x"]]]⟩
def doubling : Program := [doubleZero, doubleSucc]

/-- A host with no primitives: `succ` is a constructor. -/
def noPrimitives : Host := ⟨fun _ _ => .unhandled⟩

abbrev natTyping : Typing where
  sorts := Unit
  holds _ v := IsNat v
  sig f n := if (f = "double" ∨ f = "succ") ∧ n = 1 then some ([()], ()) else none

theorem natTyping_sig {f : String} {n : Nat} {Ss : List Unit} {S : Unit}
    (h : natTyping.sig f n = some (Ss, S)) : (f = "double" ∨ f = "succ") ∧ n = 1 ∧ Ss = [()] := by
  change (if (f = "double" ∨ f = "succ") ∧ n = 1 then some ([()], ()) else none) = some (Ss, S) at h
  by_cases hc : (f = "double" ∨ f = "succ") ∧ n = 1
  · rw [if_pos hc] at h
    cases h
    exact ⟨hc.1, hc.2, rfl⟩
  · rw [if_neg hc] at h
    cases h

theorem doubling_wellTyped : WellTyped natTyping doubling noPrimitives where
  covers := by
    intro f Ss S vs hsig hvs hdef
    obtain ⟨hf, hn, rfl⟩ := natTyping_sig hsig
    cases hvs with
    | cons hv hnil =>
      cases hnil
      rcases hf with rfl | rfl
      · cases hv with
        | zero => exact rfl
        | succ n _ => exact rfl
      · change doubling.definesAt "succ" 1 = true at hdef
        exact absurd hdef (by decide)
  bodies := by
    intro e he Ss S hsig
    simp only [doubling, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · refine ⟨[], .sym [] "zero" S .zero, fun vs σ _ _ => ?_⟩
      intro x S' hx
      cases hx
    · obtain ⟨_, _, rfl⟩ := natTyping_sig hsig
      refine ⟨[("x", ())], ?_, ?_⟩
      · refine HasType.call (T := natTyping) _ "succ" _ [()] S (by decide) rfl
          (HasTypes.cons (T := natTyping) _ _ _ () [] ?_ (HasTypes.nil (T := natTyping) _))
        refine HasType.call (T := natTyping) _ "succ" _ [()] () (by decide) rfl
          (HasTypes.cons (T := natTyping) _ _ _ () [] ?_ (HasTypes.nil (T := natTyping) _))
        exact HasType.call (T := natTyping) _ "double" _ [()] () (by decide) rfl
          (HasTypes.cons (T := natTyping) _ _ _ () []
            (HasType.var (T := natTyping) _ "x" () (Ctx.lookup_cons_self (T := natTyping) "x" () []))
            (HasTypes.nil (T := natTyping) _))
      · intro vs σ hvs hm y S' hy
        cases hvs with
        | cons hv hnil =>
          cases hnil
          cases hv with
          | zero => simp [doubleSucc, matchTerms, matchTerm] at hm
          | succ n hn =>
            have hσ : σ = [("x", n)] := by
              simp [doubleSucc, matchTerms, matchTerm] at hm
              exact hm.symm
            subst hσ
            by_cases hxy : "x" = y
            · subst hxy
              exact ⟨n, Env.lookup_cons_self "x" n [], hn⟩
            · rw [Ctx.lookup_cons_ne (T := natTyping) () [] hxy] at hy
              cases hy
  arity := by
    intro f n Ss S hsig hdef
    obtain ⟨hf, rfl, rfl⟩ := natTyping_sig hsig
    rcases hf with rfl | rfl
    · change doubling.definesAt "double" 1 = false at hdef
      exact absurd hdef (by decide)
    · decide
  host := by
    intro f Ss S vs hsig hvs hnd
    obtain ⟨hf, _, rfl⟩ := natTyping_sig hsig
    cases hvs with
    | cons hv hnil =>
      cases hnil
      rcases hf with rfl | rfl
      · exact absurd hnd (by decide)
      · exact .inl ⟨rfl, .succ _ hv⟩

/-- No call of `double` on a number fails. -/
theorem double_ends (n : Nat) {v : Term} (hv : IsNat v) :
    Ends natTyping () (apply doubling noPrimitives n "double" [v]) :=
  apply_typed doubling_wellTyped n (Ss := [()]) rfl (.cons hv .nil)

theorem double_one : apply doubling noPrimitives 10 "double" [.expr [.sym "succ", .sym "zero"]] =
    .value (.expr [.sym "succ", .expr [.sym "succ", .sym "zero"]]) := by rfl

/-- A right side naming a variable its left side does not bind. -/
def unbound : Program := [⟨"unbound", "unbound", [.sym "zero"], .var "y"⟩]

theorem unbound_untyped (S : natTyping.sorts) : ¬ HasType natTyping [] (.var "y") S := by
  intro h
  cases h with
  | var _ _ _ hx => cases hx

theorem unbound_fails : apply unbound noPrimitives 5 "unbound" [.sym "zero"] = .failure := by
  rfl

end TypingExamples

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
#print axioms Mettapedia.GSLT.LanguageDef.DeterministicEquations.apply_returns
#print axioms Mettapedia.GSLT.LanguageDef.DeterministicEquations.eval_typed
#print axioms Mettapedia.GSLT.LanguageDef.DeterministicEquations.TypingExamples.doubling_wellTyped
#print axioms Mettapedia.GSLT.LanguageDef.DeterministicEquations.TypingExamples.double_one
#print axioms Mettapedia.GSLT.LanguageDef.DeterministicEquations.TypingExamples.unbound_fails
