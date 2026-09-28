import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CheckingAlgorithm

/-!
# Recursive calls abstracted to variables

The kernel checks a right-hand side of a structural recursion with the defined
constant `f` declared and not computing; each recursive call is `f` applied to
variables. The semantic theorem for the recursion takes the right-hand side
with each call replaced by a variable, its recursive hypothesis. This module
proves that the kernel's checking of the first is a checking of the second.

A call substitution sends each variable to a variable or to a call of `f` on
`k ≥ 1` variables, distinct variables to distinct terms. Over terms without
`f`, its images determine the terms: a subterm of an image headed by `f` is the
image of a variable. When the root computations of the rule package reflect
along call substitutions and none of them rewrites a call of `f`, then

* reduction of an image is the image of a reduction;
* the conversion algorithm, the subtype test, and synthesis and checking on
  images are the images of derivations on the terms themselves, with `f`
  undeclared.

A synthesized type reflects up to reduction: a call of `f` synthesizes a
reduct of the type its declared type assigns after the arguments, and the
variable it abstracts has that type unreduced.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

/-! ## Terms without a constant -/

/-- The constant `f` does not occur in `t`. -/
def ConstFree (f : DeclName) : {n : Nat} → Tm Head n → Prop
  | _, .var _ => True
  | _, .const c => c ≠ f
  | _, .head _ => True
  | _, .pi A B => ConstFree f A ∧ ConstFree f B
  | _, .sigma A B => ConstFree f A ∧ ConstFree f B
  | _, .id A a b => ConstFree f A ∧ ConstFree f a ∧ ConstFree f b
  | _, .lam b => ConstFree f b
  | _, .app g a => ConstFree f g ∧ ConstFree f a
  | _, .pair a b => ConstFree f a ∧ ConstFree f b
  | _, .fst p => ConstFree f p
  | _, .snd p => ConstFree f p
  | _, .refl a => ConstFree f a

section ConstFree

variable {f : DeclName}

theorem ConstFree.rename {n : Nat} {t : Tm Head n} (free : ConstFree f t) :
    ∀ {m : Nat} (ρ : Ren n m), ConstFree f (Presentation.rename ρ t) := by
  induction t with
  | var i => intro m ρ; trivial
  | const c => intro m ρ; exact free
  | head h => intro m ρ; trivial
  | pi A B ihA ihB => intro m ρ; exact ⟨ihA free.1 ρ, ihB free.2 (liftRen ρ)⟩
  | sigma A B ihA ihB => intro m ρ; exact ⟨ihA free.1 ρ, ihB free.2 (liftRen ρ)⟩
  | id A a b ihA iha ihb => intro m ρ; exact ⟨ihA free.1 ρ, iha free.2.1 ρ, ihb free.2.2 ρ⟩
  | lam b ih => intro m ρ; exact ih free (liftRen ρ)
  | app g a ihg iha => intro m ρ; exact ⟨ihg free.1 ρ, iha free.2 ρ⟩
  | pair a b iha ihb => intro m ρ; exact ⟨iha free.1 ρ, ihb free.2 ρ⟩
  | fst p ih => intro m ρ; exact ih free ρ
  | snd p ih => intro m ρ; exact ih free ρ
  | refl a ih => intro m ρ; exact ih free ρ

theorem ConstFree.subst {n : Nat} {t : Tm Head n} (free : ConstFree f t) :
    ∀ {m : Nat} {σ : Sub Head n m}, (∀ i, ConstFree f (σ i)) →
      ConstFree f (Presentation.subst σ t) := by
  induction t with
  | var i => intro m σ hσ; exact hσ i
  | const c => intro m σ _; exact free
  | head h => intro m σ _; trivial
  | pi A B ihA ihB =>
      intro m σ hσ
      refine ⟨ihA free.1 hσ, ihB free.2 fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · trivial
      · exact (hσ j).rename wk
  | sigma A B ihA ihB =>
      intro m σ hσ
      refine ⟨ihA free.1 hσ, ihB free.2 fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · trivial
      · exact (hσ j).rename wk
  | id A a b ihA iha ihb => intro m σ hσ; exact ⟨ihA free.1 hσ, iha free.2.1 hσ, ihb free.2.2 hσ⟩
  | lam b ih =>
      intro m σ hσ
      refine ih free fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · trivial
      · exact (hσ j).rename wk
  | app g a ihg iha => intro m σ hσ; exact ⟨ihg free.1 hσ, iha free.2 hσ⟩
  | pair a b iha ihb => intro m σ hσ; exact ⟨iha free.1 hσ, ihb free.2 hσ⟩
  | fst p ih => intro m σ hσ; exact ih free hσ
  | snd p ih => intro m σ hσ; exact ih free hσ
  | refl a ih => intro m σ hσ; exact ih free hσ

theorem ConstFree.inst0 {n : Nat} {a : Tm Head n} {b : Tm Head (n + 1)} (freeA : ConstFree f a)
    (freeB : ConstFree f b) : ConstFree f (inst0 a b) := by
  refine freeB.subst fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact freeA
  · trivial

theorem ConstFree.liftClosed {n : Nat} {t : Tm Head 0} (free : ConstFree f t) :
    ConstFree f (liftClosed t : Tm Head n) :=
  free.rename Fin.elim0

end ConstFree

/-! ## Renaming by an injective renaming is injective -/

theorem liftRen_injective {n m : Nat} {ρ : Ren n m} (injective : Function.Injective ρ) :
    Function.Injective (liftRen ρ) := by
  intro i j h
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
  · rfl
  · exact absurd h (by simp [liftRen]; exact (Fin.succ_ne_zero _).symm)
  · exact absurd h (by simp [liftRen])
  · simp only [liftRen, Fin.cases_succ] at h
    rw [injective (Fin.succ_injective _ h)]

theorem rename_injective {n : Nat} {t t' : Tm Head n} :
    ∀ {m : Nat} {ρ : Ren n m}, Function.Injective ρ →
      Presentation.rename ρ t = Presentation.rename ρ t' → t = t' := by
  induction t with
  | var i =>
      intro m ρ inj h
      cases t' <;> simp [Presentation.rename] at h
      exact congrArg _ (inj h)
  | const c => intro m ρ inj h; cases t' <;> simp_all [Presentation.rename]
  | head c => intro m ρ inj h; cases t' <;> simp_all [Presentation.rename]
  | pi A B ihA ihB =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.pi.injEq] at h
      rw [ihA inj h.1, ihB (liftRen_injective inj) h.2]
  | sigma A B ihA ihB =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.sigma.injEq] at h
      rw [ihA inj h.1, ihB (liftRen_injective inj) h.2]
  | id A a b ihA iha ihb =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.id.injEq] at h
      rw [ihA inj h.1, iha inj h.2.1, ihb inj h.2.2]
  | lam b ih =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.lam.injEq] at h
      rw [ih (liftRen_injective inj) h]
  | app g a ihg iha =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.app.injEq] at h
      rw [ihg inj h.1, iha inj h.2]
  | pair a b iha ihb =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.pair.injEq] at h
      rw [iha inj h.1, ihb inj h.2]
  | fst p ih =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.fst.injEq] at h
      rw [ih inj h]
  | snd p ih =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.snd.injEq] at h
      rw [ih inj h]
  | refl a ih =>
      intro m ρ inj h
      cases t' <;> simp only [Presentation.rename, reduceCtorEq, Tm.refl.injEq] at h
      rw [ih inj h]

/-! ## Call substitutions -/

/-- A call of `f` on `k` variables. -/
def IsCall (f : DeclName) (k : Nat) {m : Nat} (t : Tm Head m) : Prop :=
  ∃ xs : List (Fin m), xs.length = k ∧ t = appSpine (.const f) (xs.map .var)

/-- A call substitution for `f` at arity `k ≥ 1`: every variable goes to a
variable or to a call of `f` on `k` variables, distinct variables to distinct
terms. -/
structure CallSub (f : DeclName) (k : Nat) {n m : Nat} (τ : Sub Head n m) : Prop where
  pos : 0 < k
  shape : ∀ i, (∃ j, τ i = .var j) ∨ IsCall f k (τ i)
  injective : ∀ {i i' : Fin n}, τ i = τ i' → i = i'

section Calls

variable {f : DeclName} {k : Nat}

theorem IsCall.rename {m m' : Nat} {t : Tm Head m} (call : IsCall f k t) (ρ : Ren m m') :
    IsCall f k (Presentation.rename ρ t) := by
  obtain ⟨xs, hl, rfl⟩ := call
  refine ⟨xs.map ρ, by simp [hl], ?_⟩
  rw [rename_appSpine]
  simp [Presentation.rename, List.map_map, Function.comp_def]

/-- A call on at least one variable is an application. -/
theorem IsCall.app (pos : 0 < k) {m : Nat} {t : Tm Head m} (call : IsCall f k t) :
    ∃ g a, t = .app g a := by
  obtain ⟨xs, hl, rfl⟩ := call
  refine appSpine_ne_nil_eq_app ?_
  intro h
  rw [List.map_eq_nil_iff] at h
  subst h
  simp at hl
  omega

theorem CallSub.var_or_app {n m : Nat} {τ : Sub Head n m} (call : CallSub f k τ) (i : Fin n) :
    (∃ j, τ i = .var j) ∨ ∃ g a, τ i = .app g a := by
  rcases call.shape i with h | h
  · exact .inl h
  · exact .inr (h.app call.pos)

/-- The images of a call substitution's variables are no abstraction, pair,
projection, reflexivity proof, head, constant or type former. -/
theorem CallSub.image_cases {n m : Nat} {τ : Sub Head n m} (call : CallSub f k τ) (i : Fin n)
    {P : Prop} (hvar : ∀ j, τ i = .var j → P) (happ : ∀ g a, τ i = .app g a → P) : P := by
  rcases call.var_or_app i with ⟨j, hj⟩ | ⟨g, a, h⟩
  · exact hvar j hj
  · exact happ g a h

theorem CallSub.lift {n m : Nat} {τ : Sub Head n m} (call : CallSub f k τ) :
    CallSub f k (liftSub τ) where
  pos := call.pos
  shape := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .inl ⟨0, rfl⟩
    · rcases call.shape j with ⟨x, hx⟩ | h
      · exact .inl ⟨x.succ, by simp [liftSub, hx, Presentation.rename, wk]⟩
      · exact .inr (by simpa [liftSub] using h.rename wk)
  injective := by
    intro i i' h
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨j', rfl⟩
    · rfl
    · exfalso
      simp only [liftSub, Fin.cases_zero, Fin.cases_succ] at h
      refine call.image_cases j' (fun x hx => ?_) (fun g a hx => ?_)
      · rw [hx] at h; simp [Presentation.rename, wk] at h
        exact (Fin.succ_ne_zero x) h.symm
      · rw [hx] at h; simp [Presentation.rename] at h
    · exfalso
      simp only [liftSub, Fin.cases_zero, Fin.cases_succ] at h
      refine call.image_cases j (fun x hx => ?_) (fun g a hx => ?_)
      · rw [hx] at h; simp [Presentation.rename, wk] at h
      · rw [hx] at h; simp [Presentation.rename] at h
    · simp only [liftSub, Fin.cases_succ] at h
      rw [call.injective (rename_injective (Fin.succ_injective _) h)]

/-! ## Images of terms under a call substitution -/

variable {n m : Nat} {τ : Sub Head n m}

theorem subst_eq_var {t : Tm Head n} {j : Fin m}
    (h : Presentation.subst τ t = .var j) : ∃ i, t = .var i ∧ τ i = .var j := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq] at h
  case var i => exact ⟨i, rfl, h⟩

theorem subst_eq_const (call : CallSub f k τ) {t : Tm Head n} {c : DeclName}
    (h : Presentation.subst τ t = .const c) : t = .const c := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case const c' => rw [Tm.const.inj h]

theorem subst_eq_head (call : CallSub f k τ) {t : Tm Head n} {h' : Head}
    (h : Presentation.subst τ t = .head h') : t = .head h' := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case head c' => rw [Tm.head.inj h]

theorem subst_eq_pi (call : CallSub f k τ) {t : Tm Head n} {A : Tm Head m} {B : Tm Head (m + 1)}
    (h : Presentation.subst τ t = .pi A B) :
    ∃ A' B', t = .pi A' B' ∧ Presentation.subst τ A' = A ∧ Presentation.subst (liftSub τ) B' = B := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.pi.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case pi A' B' => exact ⟨A', B', rfl, h.1, h.2⟩

theorem subst_eq_sigma (call : CallSub f k τ) {t : Tm Head n} {A : Tm Head m}
    {B : Tm Head (m + 1)} (h : Presentation.subst τ t = .sigma A B) :
    ∃ A' B', t = .sigma A' B' ∧ Presentation.subst τ A' = A ∧
      Presentation.subst (liftSub τ) B' = B := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.sigma.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case sigma A' B' => exact ⟨A', B', rfl, h.1, h.2⟩

theorem subst_eq_id (call : CallSub f k τ) {t : Tm Head n} {A a b : Tm Head m}
    (h : Presentation.subst τ t = .id A a b) :
    ∃ A' a' b', t = .id A' a' b' ∧ Presentation.subst τ A' = A ∧ Presentation.subst τ a' = a ∧
      Presentation.subst τ b' = b := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.id.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case id A' a' b' => exact ⟨A', a', b', rfl, h.1, h.2.1, h.2.2⟩

theorem subst_eq_lam (call : CallSub f k τ) {t : Tm Head n} {b : Tm Head (m + 1)}
    (h : Presentation.subst τ t = .lam b) :
    ∃ b', t = .lam b' ∧ Presentation.subst (liftSub τ) b' = b := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.lam.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case lam b' => exact ⟨b', rfl, h⟩

theorem subst_eq_pair (call : CallSub f k τ) {t : Tm Head n} {a b : Tm Head m}
    (h : Presentation.subst τ t = .pair a b) :
    ∃ a' b', t = .pair a' b' ∧ Presentation.subst τ a' = a ∧ Presentation.subst τ b' = b := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.pair.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case pair a' b' => exact ⟨a', b', rfl, h.1, h.2⟩

theorem subst_eq_fst (call : CallSub f k τ) {t : Tm Head n} {p : Tm Head m}
    (h : Presentation.subst τ t = .fst p) : ∃ p', t = .fst p' ∧ Presentation.subst τ p' = p := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.fst.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case fst p' => exact ⟨p', rfl, h⟩

theorem subst_eq_snd (call : CallSub f k τ) {t : Tm Head n} {p : Tm Head m}
    (h : Presentation.subst τ t = .snd p) : ∃ p', t = .snd p' ∧ Presentation.subst τ p' = p := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.snd.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case snd p' => exact ⟨p', rfl, h⟩

theorem subst_eq_refl (call : CallSub f k τ) {t : Tm Head n} {a : Tm Head m}
    (h : Presentation.subst τ t = .refl a) : ∃ a', t = .refl a' ∧ Presentation.subst τ a' = a := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.refl.injEq] at h
  case var i =>
    exact call.image_cases i (fun j hj => by rw [hj] at h; cases h)
      (fun g a ha => by rw [ha] at h; cases h)
  case refl a' => exact ⟨a', rfl, h⟩

theorem subst_eq_app {t : Tm Head n} {g a : Tm Head m} (h : Presentation.subst τ t = .app g a) :
    (∃ g' a', t = .app g' a' ∧ Presentation.subst τ g' = g ∧ Presentation.subst τ a' = a) ∨
      ∃ i, t = .var i ∧ τ i = .app g a := by
  cases t <;> simp only [Presentation.subst, reduceCtorEq, Tm.app.injEq] at h
  case var i => exact .inr ⟨i, rfl, h⟩
  case app g' a' => exact .inl ⟨g', a', rfl, h.1, h.2⟩

/-- The image of a term without `f` headed by `f` is a call applied to further
arguments: at least `k` of them. -/
theorem subst_eq_spine (call : CallSub f k τ) {t : Tm Head n} (free : ConstFree f t) :
    ∀ {as : List (Tm Head m)}, Presentation.subst τ t = appSpine (.const f) as → k ≤ as.length := by
  induction t with
  | var i =>
      intro as h
      rcases call.shape i with ⟨j, hj⟩ | ⟨xs, hl, hx⟩
      · simp only [Presentation.subst, hj] at h
        exact absurd h.symm appSpine_const_ne_var
      · simp only [Presentation.subst, hx] at h
        rw [← (appSpine_const_injective h).2, List.length_map, hl]
  | const c =>
      intro as h
      simp only [Presentation.subst] at h
      rcases List.eq_nil_or_concat as with rfl | ⟨init, last, rfl⟩
      · exact absurd (Tm.const.inj h) free
      · rw [List.concat_eq_append, appSpine_concat] at h
        cases h
  | app g a ihg _ =>
      intro as h
      simp only [Presentation.subst] at h
      obtain ⟨init, rfl, hg⟩ := appSpine_const_eq_app h.symm
      have := ihg call free.1 hg
      simp only [List.length_append, List.length_singleton]
      omega
  | head c =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | pi A B _ _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | sigma A B _ _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | id A a b _ _ _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | lam b _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | pair a b _ _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | fst p _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | snd p _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h
  | refl a _ =>
      intro as h
      rcases appSpine_const_cases f as with h' | ⟨g, a, h'⟩ <;>
        · rw [h'] at h; simp [Presentation.subst] at h

end Calls

/-! ## Reduction of images -/

section Reduction

variable {R : Rules Head} {f : DeclName} {k : Nat}

/-- The root computations of `R` rewrite applications of constants other than
`f`. -/
def CallsInert (R : Rules Head) (f : DeclName) : Prop :=
  ∀ {n : Nat} {t u : Tm Head n}, R.computation.step t u →
    ∃ c args, c ≠ f ∧ t = appSpine (.const c) args

/-- The root computations of `R` reflect along call substitutions for `f`: a
root step of the image of a term without `f` is the image of a root step of
the term, to a term without `f`. -/
def RootReflects (R : Rules Head) (f : DeclName) (k : Nat) : Prop :=
  ∀ {n m : Nat} {τ : Sub Head n m}, CallSub f k τ → ∀ {t : Tm Head n} {w : Tm Head m},
    ConstFree f t → R.computation.step (Presentation.subst τ t) w →
      ∃ w', R.computation.step t w' ∧ w = Presentation.subst τ w' ∧ ConstFree f w'

theorem StepCore.not_var (inert : CallsInert R f) {n : Nat} {x : Fin n} {w : Tm Head n} :
    ¬ StepCore R.computation R.headEq (.var x) w := by
  intro step
  cases step with
  | root step =>
      obtain ⟨c, args, _, h⟩ := inert step
      exact appSpine_const_ne_var h.symm

/-- The parts of a call applied to its last argument. -/
theorem call_app_parts {n : Nat} {xs : List (Fin n)} {g a : Tm Head n}
    (h : appSpine (.const f) (xs.map .var) = .app g a) :
    ∃ ys x, xs = ys ++ [x] ∧ g = appSpine (.const f) (ys.map .var) ∧ a = .var x := by
  obtain ⟨init, hxs, hg⟩ := appSpine_const_eq_app h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp hxs
  obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp h₂
  exact ⟨l₁, x, rfl, by rw [hg, h₁], hx.symm⟩

/-- A call of `f` on variables does not step. -/
theorem StepCore.not_call (inert : CallsInert R f) {n : Nat} :
    ∀ {xs : List (Fin n)} {w : Tm Head n},
      ¬ StepCore R.computation R.headEq (appSpine (.const f) (xs.map .var)) w := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
      intro w step
      cases step with
      | root step =>
          obtain ⟨c, args, hc, h⟩ := inert step
          exact hc (appSpine_const_injective (show appSpine (.const f) [] = _ from h)).1.symm
  | append_singleton init x ih =>
      intro w step
      rw [List.map_append, List.map_singleton, appSpine_concat] at step
      generalize hg : appSpine (.const f) (init.map .var) = g at step
      cases step with
      | betaPi body a => exact appSpine_const_ne_lam' hg
      | root step =>
          obtain ⟨c, args, hc, h⟩ := inert step
          rw [← hg, ← appSpine_concat] at h
          exact hc (appSpine_const_injective h).1.symm
      | congAppFun step => exact ih (hg ▸ step)
      | congAppArg step => exact StepCore.not_var inert step

/-- A step of the image of a term without `f` is the image of a step of the
term. -/
theorem StepCore.reflect (inert : CallsInert R f) (reflects : RootReflects R f k)
    {m : Nat} {s w : Tm Head m} (step : StepCore R.computation R.headEq s w) :
    ∀ {n : Nat} {τ : Sub Head n m} {t : Tm Head n}, CallSub f k τ → ConstFree f t →
      Presentation.subst τ t = s →
        ∃ w', StepCore R.computation R.headEq t w' ∧ w = Presentation.subst τ w' ∧
          ConstFree f w' := by
  induction step with
  | betaPi body a =>
      intro n τ t call free image
      rcases subst_eq_app image with ⟨g', a', rfl, hg, ha⟩ | ⟨i, rfl, hi⟩
      · obtain ⟨b', rfl, hb⟩ := subst_eq_lam call hg
        refine ⟨inst0 a' b', .betaPi b' a', ?_, ConstFree.inst0 free.2 free.1⟩
        rw [subst_inst0, hb, ha]
      · exfalso
        rcases call.shape i with ⟨j, hj⟩ | ⟨xs, _, hx⟩
        · rw [hj] at hi; cases hi
        · rw [hx] at hi; exact appSpine_const_ne_lam hi
  | betaSigmaFst a b =>
      intro n τ t call free image
      obtain ⟨p', rfl, hp⟩ := subst_eq_fst call image
      obtain ⟨a', b', rfl, ha, _⟩ := subst_eq_pair call hp
      exact ⟨a', .betaSigmaFst a' b', ha.symm, free.1⟩
  | betaSigmaSnd a b =>
      intro n τ t call free image
      obtain ⟨p', rfl, hp⟩ := subst_eq_snd call image
      obtain ⟨a', b', rfl, _, hb⟩ := subst_eq_pair call hp
      exact ⟨b', .betaSigmaSnd a' b', hb.symm, free.2⟩
  | head equality =>
      intro n τ t call free image
      rw [subst_eq_head call image]
      exact ⟨_, .head equality, rfl, trivial⟩
  | root step =>
      intro n τ t call free image
      subst image
      obtain ⟨w', step', rfl, free'⟩ := reflects call free step
      exact ⟨w', .root step', rfl, free'⟩
  | congPiDom _ ih =>
      intro n τ t call free image
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_pi call image
      obtain ⟨A'', step, rfl, free'⟩ := ih call free.1 hA
      exact ⟨.pi A'' B', .congPiDom step, by rw [← hB]; rfl, free', free.2⟩
  | congPiCod _ ih =>
      intro n τ t call free image
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_pi call image
      obtain ⟨B'', step, rfl, free'⟩ := ih call.lift free.2 hB
      exact ⟨.pi A' B'', .congPiCod step, by rw [← hA]; rfl, free.1, free'⟩
  | congSigmaDom _ ih =>
      intro n τ t call free image
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_sigma call image
      obtain ⟨A'', step, rfl, free'⟩ := ih call free.1 hA
      exact ⟨.sigma A'' B', .congSigmaDom step, by rw [← hB]; rfl, free', free.2⟩
  | congSigmaCod _ ih =>
      intro n τ t call free image
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_sigma call image
      obtain ⟨B'', step, rfl, free'⟩ := ih call.lift free.2 hB
      exact ⟨.sigma A' B'', .congSigmaCod step, by rw [← hA]; rfl, free.1, free'⟩
  | congIdTy _ ih =>
      intro n τ t call free image
      obtain ⟨A', a', b', rfl, hA, ha, hb⟩ := subst_eq_id call image
      obtain ⟨A'', step, rfl, free'⟩ := ih call free.1 hA
      exact ⟨.id A'' a' b', .congIdTy step, by rw [← ha, ← hb]; rfl, free', free.2⟩
  | congIdLeft _ ih =>
      intro n τ t call free image
      obtain ⟨A', a', b', rfl, hA, ha, hb⟩ := subst_eq_id call image
      obtain ⟨a'', step, rfl, free'⟩ := ih call free.2.1 ha
      exact ⟨.id A' a'' b', .congIdLeft step, by rw [← hA, ← hb]; rfl, free.1, free', free.2.2⟩
  | congIdRight _ ih =>
      intro n τ t call free image
      obtain ⟨A', a', b', rfl, hA, ha, hb⟩ := subst_eq_id call image
      obtain ⟨b'', step, rfl, free'⟩ := ih call free.2.2 hb
      exact ⟨.id A' a' b'', .congIdRight step, by rw [← hA, ← ha]; rfl, free.1, free.2.1, free'⟩
  | congLam _ ih =>
      intro n τ t call free image
      obtain ⟨b', rfl, hb⟩ := subst_eq_lam call image
      obtain ⟨b'', step, rfl, free'⟩ := ih (t := b') call.lift free hb
      exact ⟨.lam b'', .congLam step, rfl, free'⟩
  | congAppFun hstep ih =>
      intro n τ t call free image
      rcases subst_eq_app image with ⟨x', y', rfl, hx, hy⟩ | ⟨i, rfl, hi⟩
      · obtain ⟨x'', step, rfl, free'⟩ := ih call free.1 hx
        exact ⟨.app x'' y', .congAppFun step, by rw [← hy]; rfl, free', free.2⟩
      · exfalso
        rcases call.shape i with ⟨j, hj⟩ | ⟨xs, _, hx⟩
        · rw [hj] at hi; cases hi
        · rw [hx] at hi
          obtain ⟨ys, _, _, rfl, _⟩ := call_app_parts hi
          exact StepCore.not_call inert hstep
  | congAppArg hstep ih =>
      intro n τ t call free image
      rcases subst_eq_app image with ⟨x', y', rfl, hx, hy⟩ | ⟨i, rfl, hi⟩
      · obtain ⟨y'', step, rfl, free'⟩ := ih call free.2 hy
        exact ⟨.app x' y'', .congAppArg step, by rw [← hx]; rfl, free.1, free'⟩
      · exfalso
        rcases call.shape i with ⟨j, hj⟩ | ⟨xs, _, hx⟩
        · rw [hj] at hi; cases hi
        · rw [hx] at hi
          obtain ⟨_, _, _, _, rfl⟩ := call_app_parts hi
          exact StepCore.not_var inert hstep
  | congPairFst _ ih =>
      intro n τ t call free image
      obtain ⟨a', b', rfl, ha, hb⟩ := subst_eq_pair call image
      obtain ⟨a'', step, rfl, free'⟩ := ih call free.1 ha
      exact ⟨.pair a'' b', .congPairFst step, by rw [← hb]; rfl, free', free.2⟩
  | congPairSnd _ ih =>
      intro n τ t call free image
      obtain ⟨a', b', rfl, ha, hb⟩ := subst_eq_pair call image
      obtain ⟨b'', step, rfl, free'⟩ := ih call free.2 hb
      exact ⟨.pair a' b'', .congPairSnd step, by rw [← ha]; rfl, free.1, free'⟩
  | congFst _ ih =>
      intro n τ t call free image
      obtain ⟨p', rfl, hp⟩ := subst_eq_fst call image
      obtain ⟨p'', step, rfl, free'⟩ := ih (t := p') call free hp
      exact ⟨.fst p'', .congFst step, rfl, free'⟩
  | congSnd _ ih =>
      intro n τ t call free image
      obtain ⟨p', rfl, hp⟩ := subst_eq_snd call image
      obtain ⟨p'', step, rfl, free'⟩ := ih (t := p') call free hp
      exact ⟨.snd p'', .congSnd step, rfl, free'⟩
  | congRefl _ ih =>
      intro n τ t call free image
      obtain ⟨a', rfl, ha⟩ := subst_eq_refl call image
      obtain ⟨a'', step, rfl, free'⟩ := ih (t := a') call free ha
      exact ⟨.refl a'', .congRefl step, rfl, free'⟩

/-- A reduction of the image of a term without `f` is the image of a reduction
of the term. -/
theorem Reduces.reflect (inert : CallsInert R f) (reflects : RootReflects R f k)
    {n m : Nat} {τ : Sub Head n m} (call : CallSub f k τ) {t : Tm Head n} (free : ConstFree f t)
    {w : Tm Head m} (red : Reduces R (Presentation.subst τ t) w) :
    ∃ w', Reduces R t w' ∧ w = Presentation.subst τ w' ∧ ConstFree f w' := by
  induction red with
  | refl => exact ⟨t, .refl, rfl, free⟩
  | tail _ step ih =>
      obtain ⟨w₁, red₁, rfl, free₁⟩ := ih
      obtain ⟨w', step', rfl, free'⟩ := StepCore.reflect inert reflects step call free₁ rfl
      exact ⟨w', red₁.tail step', rfl, free'⟩

/-- Reduction of a dependent function type reduces its parts. -/
theorem Reduces.pi_inv (inert : CallsInert R f) {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)}
    {X : Tm Head n} (red : Reduces R (.pi A B) X) :
    ∃ A' B', X = .pi A' B' ∧ Reduces R A A' ∧ Reduces R B B' := by
  induction red with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨A', B', rfl, rA, rB⟩ := ih
      cases step with
      | root step =>
          obtain ⟨c, args, _, h⟩ := inert step
          rcases appSpine_const_cases c args with h' | ⟨g, a, h'⟩ <;> rw [h'] at h <;> cases h
      | congPiDom step => exact ⟨_, B', rfl, rA.tail step, rB⟩
      | congPiCod step => exact ⟨A', _, rfl, rA, rB.tail step⟩

/-- Reduction is stable under substitution. -/
theorem Reduces.substitute {n m : Nat} {a b : Tm Head n} (red : Reduces R a b) (σ : Sub Head n m) :
    Reduces R (Presentation.subst σ a) (Presentation.subst σ b) :=
  Reduces.congr (f := Presentation.subst σ) (fun step => StepCore.substitute step σ) red

/-- Reduction is stable under renaming. -/
theorem Reduces.rename' {n m : Nat} {a b : Tm Head n} (red : Reduces R a b) (ρ : Ren n m) :
    Reduces R (Presentation.rename ρ a) (Presentation.rename ρ b) :=
  Reduces.congr (f := Presentation.rename ρ) (fun step => StepCore.renameTerms step ρ) red

theorem Reduces.of_eq {n : Nat} {a b : Tm Head n} (e : a = b) : Reduces R a b := e ▸ .refl

end Reduction

/-! ## Variable heads -/

/-- A term whose head, under applications and projections, is the variable
`x`. -/
inductive VarHeaded {n : Nat} (x : Fin n) : Tm Head n → Prop where
  | var : VarHeaded x (.var x)
  | app {g a : Tm Head n} : VarHeaded x g → VarHeaded x (.app g a)
  | fst {p : Tm Head n} : VarHeaded x p → VarHeaded x (.fst p)
  | snd {p : Tm Head n} : VarHeaded x p → VarHeaded x (.snd p)

section VarHeads

variable {R : Rules Head} {f : DeclName}

theorem VarHeaded.rename {n m : Nat} {x : Fin n} {t : Tm Head n} (h : VarHeaded x t)
    (ρ : Ren n m) : VarHeaded (ρ x) (Presentation.rename ρ t) := by
  induction h with
  | var => exact .var
  | app _ ih => exact .app ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

theorem VarHeaded.not_constSpine {n : Nat} {x : Fin n} {t : Tm Head n} (h : VarHeaded x t) :
    ∀ {c : DeclName} {args : List (Tm Head n)}, t ≠ appSpine (.const c) args := by
  induction h with
  | var => intro c args e; exact appSpine_const_ne_var e.symm
  | app _ ih =>
      intro c args e
      obtain ⟨init, _, hg⟩ := appSpine_const_eq_app e.symm
      exact ih hg
  | fst _ => intro c args e; exact appSpine_const_ne_fst e.symm
  | snd _ => intro c args e; exact appSpine_const_ne_snd e.symm

theorem StepCore.varHeaded (inert : CallsInert R f) {n : Nat} {t w : Tm Head n} {x : Fin n}
    (h : VarHeaded x t) (step : StepCore R.computation R.headEq t w) : VarHeaded x w := by
  induction h generalizing w with
  | var => exact absurd step (StepCore.not_var inert)
  | @app g a hg ih =>
      cases step with
      | betaPi body a => cases hg
      | root step =>
          obtain ⟨c, args, _, e⟩ := inert step
          exact absurd e (VarHeaded.app hg).not_constSpine
      | congAppFun step => exact .app (ih step)
      | congAppArg _ => exact .app hg
  | @fst p hp ih =>
      cases step with
      | betaSigmaFst a b => cases hp
      | root step =>
          obtain ⟨c, args, _, e⟩ := inert step
          exact absurd e (VarHeaded.fst hp).not_constSpine
      | congFst step => exact .fst (ih step)
  | @snd p hp ih =>
      cases step with
      | betaSigmaSnd a b => cases hp
      | root step =>
          obtain ⟨c, args, _, e⟩ := inert step
          exact absurd e (VarHeaded.snd hp).not_constSpine
      | congSnd step => exact .snd (ih step)

theorem VarHeaded.reduces (inert : CallsInert R f) {n : Nat} {t w : Tm Head n} {x : Fin n}
    (h : VarHeaded x t) (red : Reduces R t w) : VarHeaded x w := by
  induction red with
  | refl => exact h
  | tail _ step ih => exact StepCore.varHeaded inert ih step

/-- Two sides the conversion algorithm relates that are headed by variables are
headed by the same variable. -/
def SameVarHead : AlgorithmStatement Head → Prop
  | .compare _ a b _ => ∀ {x y}, VarHeaded x a → VarHeaded y b → x = y
  | .neutral _ a b _ => ∀ {x y}, VarHeaded x a → VarHeaded y b → x = y
  | .types _ a b => ∀ {x y}, VarHeaded x a → VarHeaded y b → x = y

theorem Algorithm.sameVarHead (inert : CallsInert R f) {st : AlgorithmStatement Head}
    (derivation : Algorithm R st) : SameVarHead st := by
  induction derivation with
  | pi _ _ ih =>
      intro x y hx hy
      exact Fin.succ_injective _ (ih (VarHeaded.app (hx.rename wk)) (VarHeaded.app (hy.rename wk)))
  | sigma _ _ _ ih₁ _ => intro x y hx hy; exact ih₁ hx.fst hy.fst
  | sort _ _ _ ih => intro x y hx hy; exact ih hx hy
  | reflexivity _ ra _ _ _ =>
      intro x y hx _
      cases hx.reduces inert ra
  | neutralAt ra rb _ ih =>
      intro x y hx hy
      exact ih (hx.reduces inert ra) (hy.reduces inert rb)
  | var i => intro x y hx hy; cases hx; cases hy; rfl
  | const _ => intro x y hx; cases hx
  | app _ _ _ ihf _ =>
      intro x y hx hy
      cases hx with
      | app hg => cases hy with
        | app hg' => exact ihf hg hg'
  | fst _ _ ih =>
      intro x y hx hy
      cases hx with
      | fst hp => cases hy with
        | fst hq => exact ih hp hq
  | snd _ _ ih =>
      intro x y hx hy
      cases hx with
      | snd hp => cases hy with
        | snd hq => exact ih hp hq
  | heads rA _ _ =>
      intro x y hx _
      cases hx.reduces inert rA
  | piTypes rA _ _ _ _ _ =>
      intro x y hx _
      cases hx.reduces inert rA
  | sigmaTypes rA _ _ _ _ _ =>
      intro x y hx _
      cases hx.reduces inert rA
  | idTypes rA _ _ _ _ _ _ _ =>
      intro x y hx _
      cases hx.reduces inert rA
  | neutralTypes rA rB _ ih =>
      intro x y hx hy
      exact ih (hx.reduces inert rA) (hy.reduces inert rB)

/-- Two variables the conversion algorithm relates are the same variable. -/
theorem Algorithm.var_eq (inert : CallsInert R f) {n : Nat} {Γ : Ctx Head n} {x y : Fin n}
    {T : Tm Head n} (derivation : Algorithm R (.compare Γ (.var x) (.var y) T)) : x = y :=
  Algorithm.sameVarHead inert derivation .var .var

end VarHeads

/-! ## Neutral spines of a constant -/

/-- The conversion algorithm relates a neutral application of a constant only
to an application of the same constant to as many arguments. -/
def ConstSkeleton : AlgorithmStatement Head → Prop
  | .neutral _ a b _ => (∀ {c : DeclName} {as}, a = appSpine (.const c) as →
      ∃ bs, b = appSpine (.const c) bs ∧ bs.length = as.length) ∧
    (∀ {c : DeclName} {bs}, b = appSpine (.const c) bs →
      ∃ as, a = appSpine (.const c) as ∧ as.length = bs.length)
  | _ => True

theorem Algorithm.constSkeleton {R : Rules Head} {st : AlgorithmStatement Head}
    (derivation : Algorithm R st) : ConstSkeleton st := by
  induction derivation with
  | var i =>
      exact ⟨fun h => absurd h.symm appSpine_const_ne_var, fun h => absurd h.symm appSpine_const_ne_var⟩
  | const _ =>
      refine ⟨fun {c as} h => ?_, fun {c bs} h => ?_⟩
      · obtain ⟨rfl, rfl⟩ := appSpine_const_injective (show appSpine (.const _) [] = _ from h)
        exact ⟨[], rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := appSpine_const_injective (show appSpine (.const _) [] = _ from h)
        exact ⟨[], rfl, rfl⟩
  | app _ _ _ ihf _ =>
      refine ⟨fun {c as} h => ?_, fun {c bs} h => ?_⟩
      · obtain ⟨init, rfl, hf⟩ := appSpine_const_eq_app h.symm
        obtain ⟨bs, hg, hl⟩ := ihf.1 hf
        subst hg
        exact ⟨bs ++ [_], (appSpine_concat _ _ _).symm, by simp [hl]⟩
      · obtain ⟨init, rfl, hg⟩ := appSpine_const_eq_app h.symm
        obtain ⟨as, hf, hl⟩ := ihf.2 hg
        subst hf
        exact ⟨as ++ [_], (appSpine_concat _ _ _).symm, by simp [hl]⟩
  | fst _ _ _ =>
      exact ⟨fun h => absurd h.symm appSpine_const_ne_fst, fun h => absurd h.symm appSpine_const_ne_fst⟩
  | snd _ _ _ =>
      exact ⟨fun h => absurd h.symm appSpine_const_ne_snd, fun h => absurd h.symm appSpine_const_ne_snd⟩
  | pi => trivial
  | sigma => trivial
  | sort => trivial
  | reflexivity => trivial
  | neutralAt => trivial
  | heads => trivial
  | piTypes => trivial
  | sigmaTypes => trivial
  | idTypes => trivial
  | neutralTypes => trivial

/-! ## The type a declared constant assigns after its arguments -/

/-- The type a head of type `T` assigns after the arguments `as`: each leading
dependent function type instantiated at the next argument. -/
def peel {n : Nat} : Tm Head n → List (Tm Head n) → Tm Head n
  | T, [] => T
  | .pi _ B, a :: as => peel (inst0 a B) as
  | T, _ :: _ => T

/-- `T` has a leading dependent function type for each of the arguments. -/
def Peels {n : Nat} : Tm Head n → List (Tm Head n) → Prop
  | _, [] => True
  | .pi _ B, a :: as => Peels (inst0 a B) as
  | _, _ :: _ => False

theorem peel_concat {n : Nat} {a : Tm Head n} :
    ∀ {as : List (Tm Head n)} {T : Tm Head n}, Peels T (as ++ [a]) →
      Peels T as ∧ ∃ D B, peel T as = .pi D B ∧ peel T (as ++ [a]) = inst0 a B := by
  intro as
  induction as with
  | nil =>
      intro T h
      cases T <;> simp [Peels] at h
      case pi D B => exact ⟨trivial, D, B, rfl, rfl⟩
  | cons b as ih =>
      intro T h
      cases T <;> simp [Peels] at h
      case pi D B =>
        obtain ⟨hp, D', B', e₁, e₂⟩ := ih h
        exact ⟨hp, D', B', e₁, e₂⟩

theorem rename_peel {n m : Nat} (ρ : Ren n m) :
    ∀ (as : List (Tm Head n)) (T : Tm Head n),
      Presentation.rename ρ (peel T as) = peel (Presentation.rename ρ T) (as.map (Presentation.rename ρ))
  | [], T => rfl
  | a :: as, T => by
      cases T <;> simp only [peel, Presentation.rename, List.map_cons]
      case pi D B =>
        rw [rename_peel ρ as (inst0 a B), rename_inst0]

theorem Peels.rename {n m : Nat} (ρ : Ren n m) :
    ∀ {as : List (Tm Head n)} {T : Tm Head n}, Peels T as →
      Peels (Presentation.rename ρ T) (as.map (Presentation.rename ρ))
  | [], _, _ => trivial
  | a :: as, T, h => by
      cases T <;> simp only [Peels] at h
      case pi D B =>
        show Peels (inst0 (Presentation.rename ρ a) (Presentation.rename (liftRen ρ) B))
          (as.map (Presentation.rename ρ))
        rw [← rename_inst0]
        exact Peels.rename ρ h

section CallSpines

variable {R : Rules Head} {f : DeclName} {A : Tm Head 0}

/-- What the conversion algorithm says about two calls of `f` on variables:
they are the same call, at a reduct of the type the declared type assigns. -/
def CallNeutral (R : Rules Head) (f : DeclName) (A : Tm Head 0) : AlgorithmStatement Head → Prop
  | .neutral (n := n) _ a b U => ∀ {xs ys : List (Fin n)}, a = appSpine (.const f) (xs.map .var) →
      b = appSpine (.const f) (ys.map .var) → Peels (liftClosed A) (xs.map .var) →
        xs = ys ∧ Reduces R (peel (liftClosed A) (xs.map .var)) U
  | _ => True

theorem Algorithm.callNeutral (inert : CallsInert R f) (declared : R.constantType f = some A)
    {st : AlgorithmStatement Head} (derivation : Algorithm R st) : CallNeutral R f A st := by
  induction derivation with
  | var i => intro xs ys h; exact absurd h.symm appSpine_const_ne_var
  | const declared' =>
      intro xs ys ha hb _
      obtain ⟨rfl, hxs⟩ := appSpine_const_injective (show appSpine (.const _) [] = _ from ha)
      obtain ⟨_, hys⟩ := appSpine_const_injective (show appSpine (.const _) [] = _ from hb)
      rw [declared] at declared'
      cases declared'
      have ex := List.map_eq_nil_iff.mp hxs.symm
      have ey := List.map_eq_nil_iff.mp hys.symm
      subst ex; subst ey
      exact ⟨rfl, .refl⟩
  | @app n Γ g₁ g₂ a₁ b₁ U₁ A₀ B₀ _ red d₂ ih₁ _ =>
      intro xs ys ha hb peels
      obtain ⟨xs₀, x, rfl, hg₁, rfl⟩ := call_app_parts ha.symm
      obtain ⟨ys₀, y, rfl, hg₂, rfl⟩ := call_app_parts hb.symm
      rw [List.map_append, List.map_singleton] at peels
      obtain ⟨peels₀, D, B', e₁, e₂⟩ := peel_concat peels
      obtain ⟨rfl, red₀⟩ := ih₁ hg₁ hg₂ peels₀
      obtain rfl := Algorithm.var_eq inert d₂
      refine ⟨rfl, ?_⟩
      rw [List.map_append, List.map_singleton, e₂]
      rw [e₁] at red₀
      obtain ⟨_, _, e, _, rB⟩ := Reduces.pi_inv inert (red₀.trans red)
      cases e
      exact Reduces.substitute rB _
  | fst _ _ _ => intro xs ys h; exact absurd h.symm appSpine_const_ne_fst
  | snd _ _ _ => intro xs ys h; exact absurd h.symm appSpine_const_ne_snd
  | pi => trivial
  | sigma => trivial
  | sort => trivial
  | reflexivity => trivial
  | neutralAt => trivial
  | heads => trivial
  | piTypes => trivial
  | sigmaTypes => trivial
  | idTypes => trivial
  | neutralTypes => trivial

/-- What synthesis says about an application of `f`: its type is a reduct of
the type the declared type assigns after the arguments. -/
def CallSynth (R : Rules Head) (f : DeclName) (A : Tm Head 0) :
    Mode → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Prop
  | .synth, _, _, t, T => ∀ {as}, t = appSpine (.const f) as → Peels (liftClosed A) as →
      Reduces R (peel (liftClosed A) as) T
  | .check, _, _, _, _ => True

theorem appSpine_const_ne_former {n : Nat} {c : DeclName} {as : List (Tm Head n)}
    {t : Tm Head n} (former : (∃ h, t = .head h) ∨ (∃ A B, t = .pi A B) ∨ (∃ A B, t = .sigma A B) ∨
      (∃ A a b, t = .id A a b)) : appSpine (.const c) as ≠ t := by
  intro e
  rcases appSpine_const_cases c as with h | ⟨g, a, h⟩ <;> rw [h] at e <;> subst e <;>
    rcases former with ⟨_, h'⟩ | ⟨_, _, h'⟩ | ⟨_, _, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'

theorem CheckingAlgorithm.callSynth (inert : CallsInert R f) (declared : R.constantType f = some A)
    {mode : Mode} {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
    (derivation : CheckingAlgorithm R mode Γ t T) : CallSynth R f A mode Γ t T := by
  induction derivation with
  | var i => intro as h; exact absurd h.symm appSpine_const_ne_var
  | const declared' =>
      intro as h _
      obtain ⟨rfl, has⟩ := appSpine_const_injective (show appSpine (.const _) [] = _ from h)
      rw [declared] at declared'
      cases declared'
      subst has
      exact .refl
  | head _ => intro as h; exact absurd h.symm (appSpine_const_ne_former (.inl ⟨_, rfl⟩))
  | pi => intro as h; exact absurd h.symm (appSpine_const_ne_former (.inr (.inl ⟨_, _, rfl⟩)))
  | sigma =>
      intro as h; exact absurd h.symm (appSpine_const_ne_former (.inr (.inr (.inl ⟨_, _, rfl⟩))))
  | id =>
      intro as h
      exact absurd h.symm (appSpine_const_ne_former (.inr (.inr (.inr ⟨_, _, _, rfl⟩))))
  | refl => intro as h; exact absurd h.symm appSpine_const_ne_refl
  | @app n Γ g a F A₀ B₀ _ red _ ihg _ =>
      intro as h peels
      obtain ⟨init, rfl, hg⟩ := appSpine_const_eq_app h.symm
      obtain ⟨peels₀, D, B', e₁, e₂⟩ := peel_concat peels
      have red₀ := ihg hg peels₀
      rw [e₂]
      rw [e₁] at red₀
      obtain ⟨_, _, e, _, rB⟩ := Reduces.pi_inv inert (red₀.trans red)
      cases e
      exact Reduces.substitute rB _
  | fst => intro as h; exact absurd h.symm appSpine_const_ne_fst
  | snd => intro as h; exact absurd h.symm appSpine_const_ne_snd
  | redex => intro as h; exact absurd h.symm appSpine_const_ne_lam
  | lamCheck => trivial
  | pairCheck => trivial
  | reflCheck => trivial
  | switch => trivial

end CallSpines

/-! ## Contexts of a call substitution -/

/-- `R` is `R'` with the constant `f` declared: they agree on universes, heads,
computation and every other constant, and no type `R'` declares mentions `f`. -/
structure DeclaresCall (R R' : Rules Head) (f : DeclName) : Prop where
  headTyping : ∀ {h u : Head}, R.headTyping h u → R'.headTyping h u
  isUniverse : ∀ {u : Head}, R.isUniverse u → R'.isUniverse u
  join : ∀ {u v w : Head}, R.join u v w → R'.join u v w
  cumulative : ∀ {u v : Head}, R.cumulative u v → R'.cumulative u v
  headEq : ∀ {h h' : Head}, R.headEq h h' → R'.headEq h h'
  computation : ∀ {n : Nat} {t u : Tm Head n}, R.computation.step t u → R'.computation.step t u
  constantType : ∀ {c : DeclName} {type : Tm Head 0}, c ≠ f → R.constantType c = some type →
    R'.constantType c = some type
  typesFree : ∀ {c : DeclName} {type : Tm Head 0}, R'.constantType c = some type →
    ConstFree f type

section Declares

variable {R R' : Rules Head} {f : DeclName}

theorem DeclaresCall.step (d : DeclaresCall R R' f) {n : Nat} {t u : Tm Head n}
    (step : StepCore R.computation R.headEq t u) : StepCore R'.computation R'.headEq t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head e => exact .head (d.headEq e)
  | root s => exact .root (d.computation s)
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

theorem DeclaresCall.reduces (d : DeclaresCall R R' f) {n : Nat} {t u : Tm Head n}
    (red : Reduces R t u) : Reduces R' t u := by
  induction red with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (d.step step)

end Declares

/-- The contexts of a call substitution `τ` from `Δ` to `Γ`, for `f` declared
at `A`: the image of each entry of `Δ` at a variable sent to a variable reduces
to the entry of `Γ` there, and a variable sent to a call has, as image of its
type, the type `A` assigns after the call's arguments. No entry of `Δ` mentions
`f`. -/
structure CallContexts (R : Rules Head) (f : DeclName) (k : Nat) (A : Tm Head 0) {n m : Nat}
    (τ : Sub Head n m) (Δ : Ctx Head n) (Γ : Ctx Head m) : Prop where
  sub : CallSub f k τ
  var : ∀ {i j}, τ i = .var j →
    Reduces R (Presentation.subst τ (Ctx.lookup Δ i)) (Ctx.lookup Γ j)
  call : ∀ {i} {xs : List (Fin m)}, τ i = appSpine (.const f) (xs.map .var) →
    Peels (liftClosed A) (xs.map .var) ∧
      Presentation.subst τ (Ctx.lookup Δ i) = peel (liftClosed A) (xs.map .var)
  free : ∀ i, ConstFree f (Ctx.lookup Δ i)

section Contexts

variable {R : Rules Head} {f : DeclName} {k : Nat} {A : Tm Head 0}

/-- A variable sent to an application is sent to a call. -/
theorem CallSub.call_of_app {n m : Nat} {τ : Sub Head n m} (call : CallSub f k τ) {i : Fin n}
    {g a : Tm Head m} (h : τ i = .app g a) :
    ∃ xs : List (Fin m), xs.length = k ∧ τ i = appSpine (.const f) (xs.map .var) := by
  rcases call.shape i with ⟨j, hj⟩ | c
  · rw [hj] at h; cases h
  · exact c

theorem CallContexts.lift {n m : Nat} {τ : Sub Head n m} {Δ : Ctx Head n} {Γ : Ctx Head m}
    (ctx : CallContexts R f k A τ Δ Γ) {D' : Tm Head n} {D : Tm Head m} (free : ConstFree f D')
    (red : Reduces R (Presentation.subst τ D') D) :
    CallContexts R f k A (liftSub τ) (.snoc Δ D') (.snoc Γ D) where
  sub := ctx.sub.lift
  var := by
    intro i j h
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · simp only [liftSub, Fin.cases_zero, Tm.var.injEq] at h
      subst h
      show Reduces R (Presentation.subst (liftSub τ) (Presentation.rename wk D'))
        (Presentation.rename wk D)
      rw [subst_liftSub_wk]
      exact Reduces.rename' red wk
    · simp only [liftSub, Fin.cases_succ] at h
      rcases ctx.sub.shape i' with ⟨j', hj'⟩ | ⟨xs, _, hx⟩
      · rw [hj'] at h
        simp only [Presentation.rename, wk, Tm.var.injEq] at h
        subst h
        show Reduces R (Presentation.subst (liftSub τ) (Presentation.rename wk (Ctx.lookup Δ i')))
          (Presentation.rename wk (Ctx.lookup Γ j'))
        rw [subst_liftSub_wk]
        exact Reduces.rename' (ctx.var hj') wk
      · exfalso
        rw [hx, rename_appSpine] at h
        exact appSpine_const_ne_var h
  call := by
    intro i xs h
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · simp only [liftSub, Fin.cases_zero] at h
      exact absurd h.symm appSpine_const_ne_var
    · simp only [liftSub, Fin.cases_succ] at h
      rcases ctx.sub.shape i' with ⟨j', hj'⟩ | ⟨ys, _, hy⟩
      · rw [hj'] at h
        simp only [Presentation.rename] at h
        exact absurd h.symm appSpine_const_ne_var
      · rw [hy, rename_appSpine] at h
        have e := (appSpine_const_injective h).2
        obtain ⟨peels, hpeel⟩ := ctx.call hy
        refine ⟨?_, ?_⟩
        · rw [← e]
          simpa using peels.rename wk
        · show Presentation.subst (liftSub τ) (Presentation.rename wk (Ctx.lookup Δ i')) = _
          rw [subst_liftSub_wk, hpeel, rename_peel, rename_liftClosed, e]
  free := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact free.rename wk
    · exact (ctx.free i').rename wk

end Contexts

/-! ## The conversion algorithm on images -/

/-- What a derivation of the conversion algorithm between images gives for the
terms themselves. -/
def AlgorithmReflects (R R' : Rules Head) (f : DeclName) (k : Nat) (A : Tm Head 0) :
    AlgorithmStatement Head → Prop
  | .compare (n := m) Γ a b T => ∀ {n : Nat} {Δ : Ctx Head n} {τ : Sub Head n m}
      {a' b' T' : Tm Head n}, CallContexts R f k A τ Δ Γ → ConstFree f a' → ConstFree f b' →
      ConstFree f T' → Presentation.subst τ a' = a → Presentation.subst τ b' = b →
      Presentation.subst τ T' = T → Algorithm R' (.compare Δ a' b' T')
  | .neutral (n := m) Γ a b U => ∀ {n : Nat} {Δ : Ctx Head n} {τ : Sub Head n m}
      {a' b' : Tm Head n}, CallContexts R f k A τ Δ Γ → ConstFree f a' → ConstFree f b' →
      Presentation.subst τ a' = a → Presentation.subst τ b' = b →
        ∃ U', Algorithm R' (.neutral Δ a' b' U') ∧ Reduces R (Presentation.subst τ U') U ∧
          ConstFree f U'
  | .types (n := m) Γ X Y => ∀ {n : Nat} {Δ : Ctx Head n} {τ : Sub Head n m}
      {X' Y' : Tm Head n}, CallContexts R f k A τ Δ Γ → ConstFree f X' → ConstFree f Y' →
      Presentation.subst τ X' = X → Presentation.subst τ Y' = Y → Algorithm R' (.types Δ X' Y')

section Reflection

variable {R R' : Rules Head} {f : DeclName} {k : Nat} {A : Tm Head 0}
  (d : DeclaresCall R R' f) (inert : CallsInert R f) (reflects : RootReflects R f k)
  (declared : R.constantType f = some A)
include d inert reflects declared

theorem Algorithm.reflect {st : AlgorithmStatement Head} (derivation : Algorithm R st) :
    AlgorithmReflects R R' f k A st := by
  induction derivation with
  | @pi m Γ a b T A₀ B₀ red _ ih =>
      intro n Δ τ a' b' T' ctx fa fb fT ha hb hT
      subst hT
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fT red
      obtain ⟨A₀', B₀', rfl, hA, hB⟩ := subst_eq_pi ctx.sub eW.symm
      have ctx' := ctx.lift fW.1 (Reduces.of_eq hA)
      refine .pi (d.reduces redW) (ih ctx' (a' := .app (Presentation.rename wk a') (.var 0))
        (b' := .app (Presentation.rename wk b') (.var 0)) ⟨fa.rename wk, trivial⟩
        ⟨fb.rename wk, trivial⟩ fW.2 ?_ ?_ hB)
      · simp only [Presentation.subst, subst_liftSub_wk, ha]; rfl
      · simp only [Presentation.subst, subst_liftSub_wk, hb]; rfl
  | @sigma m Γ a b T A₀ B₀ red _ _ ih₁ ih₂ =>
      intro n Δ τ a' b' T' ctx fa fb fT ha hb hT
      subst hT
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fT red
      obtain ⟨A₀', B₀', rfl, hA, hB⟩ := subst_eq_sigma ctx.sub eW.symm
      refine .sigma (d.reduces redW) (ih₁ ctx (a' := .fst a') (b' := .fst b') fa fb fW.1
        (by simp only [Presentation.subst, ha]) (by simp only [Presentation.subst, hb]) hA)
        (ih₂ ctx (a' := .snd a') (b' := .snd b') (T' := inst0 (.fst a') B₀') fa fb
          (ConstFree.inst0 fa fW.2) (by simp only [Presentation.subst, ha])
          (by simp only [Presentation.subst, hb]) ?_)
      rw [subst_inst0, hB]
      simp only [Presentation.subst, ha]
  | @sort m Γ a b T u red hu _ ih =>
      intro n Δ τ a' b' T' ctx fa fb fT ha hb hT
      subst hT
      obtain ⟨W, redW, eW, _⟩ := Reduces.reflect inert reflects ctx.sub fT red
      rw [subst_eq_head ctx.sub eW.symm] at redW
      exact .sort (d.reduces redW) (d.isUniverse hu) (ih ctx fa fb ha hb)
  | @reflexivity m Γ a b T C x y a₀ b₀ red ra rb _ ih =>
      intro n Δ τ a' b' T' ctx fa fb fT ha hb hT
      subst hT ha hb
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fT red
      obtain ⟨C', x', y', rfl, hC, _, _⟩ := subst_eq_id ctx.sub eW.symm
      obtain ⟨Wa, redA, eA, fA⟩ := Reduces.reflect inert reflects ctx.sub fa ra
      obtain ⟨a₀', rfl, ha₀⟩ := subst_eq_refl ctx.sub eA.symm
      obtain ⟨Wb, redB, eB, fB⟩ := Reduces.reflect inert reflects ctx.sub fb rb
      obtain ⟨b₀', rfl, hb₀⟩ := subst_eq_refl ctx.sub eB.symm
      exact .reflexivity (d.reduces redW) (d.reduces redA) (d.reduces redB)
        (ih ctx fA fB fW.1 ha₀ hb₀ hC)
  | @neutralAt m Γ a b T a₀ b₀ U ra rb _ ih =>
      intro n Δ τ a' b' T' ctx fa fb fT ha hb hT
      subst ha hb
      obtain ⟨Wa, redA, rfl, fA⟩ := Reduces.reflect inert reflects ctx.sub fa ra
      obtain ⟨Wb, redB, rfl, fB⟩ := Reduces.reflect inert reflects ctx.sub fb rb
      obtain ⟨U', dn, _, _⟩ := ih ctx fA fB rfl rfl
      exact .neutralAt (d.reduces redA) (d.reduces redB) dn
  | var j =>
      intro n Δ τ a' b' ctx fa fb ha hb
      obtain ⟨i, rfl, hi⟩ := subst_eq_var ha
      obtain ⟨i', rfl, hi'⟩ := subst_eq_var hb
      obtain rfl := ctx.sub.injective (hi.trans hi'.symm)
      exact ⟨Ctx.lookup Δ i, .var i, ctx.var hi, ctx.free i⟩
  | @const m Γ name type declared' =>
      intro n Δ τ a' b' ctx fa fb ha hb
      rw [subst_eq_const ctx.sub ha] at fa ⊢
      rw [subst_eq_const ctx.sub hb]
      have typeFree := d.typesFree (d.constantType fa declared')
      exact ⟨liftClosed type, .const (d.constantType fa declared'), by rw [subst_liftClosed],
        typeFree.liftClosed⟩
  | @app m Γ g₁ g₂ a₁ b₁ U₁ A₀ B₀ d₁ red d₂ ih₁ ih₂ =>
      intro n Δ τ a' b' ctx fa fb ha hb
      rcases subst_eq_app ha with ⟨x', y', rfl, hx, hy⟩ | ⟨i, rfl, hi⟩ <;>
        rcases subst_eq_app hb with ⟨x'', y'', rfl, hx', hy'⟩ | ⟨i'', rfl, hi''⟩
      · obtain ⟨U₁', dn, redU, fU⟩ := ih₁ ctx fa.1 fb.1 hx hx'
        obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fU (redU.trans red)
        obtain ⟨A₀', B₀', rfl, hA, hB⟩ := subst_eq_pi ctx.sub eW.symm
        refine ⟨inst0 y' B₀', .app dn (d.reduces redW) (ih₂ ctx fa.2 fb.2 fW.1 hy hy' hA), ?_,
          ConstFree.inst0 fa.2 fW.2⟩
        rw [subst_inst0, hy, hB]
      · exfalso
        obtain ⟨ys, hl, hys⟩ := ctx.sub.call_of_app hi''
        rw [hys] at hi''
        obtain ⟨ys₀, y, rfl, hg₂, rfl⟩ := call_app_parts hi''
        obtain ⟨as, hg₁, hlen⟩ := (Algorithm.constSkeleton d₁).2 hg₂
        have := subst_eq_spine ctx.sub fa.1 (hx.trans hg₁)
        simp at hl hlen
        omega
      · exfalso
        obtain ⟨xs, hl, hxs⟩ := ctx.sub.call_of_app hi
        rw [hxs] at hi
        obtain ⟨xs₀, x, rfl, hg₁, rfl⟩ := call_app_parts hi
        obtain ⟨bs, hg₂, hlen⟩ := (Algorithm.constSkeleton d₁).1 hg₁
        have := subst_eq_spine ctx.sub fb.1 (hx'.trans hg₂)
        simp at hl hlen
        omega
      · obtain ⟨xs, _, hxs⟩ := ctx.sub.call_of_app hi
        obtain ⟨ys, _, hys⟩ := ctx.sub.call_of_app hi''
        obtain ⟨peels, hpeel⟩ := ctx.call hxs
        have whole : Algorithm R (.neutral Γ (.app g₁ a₁) (.app g₂ b₁) (inst0 a₁ B₀)) :=
          .app d₁ red d₂
        obtain ⟨rfl, redU⟩ := Algorithm.callNeutral inert declared whole (hi.symm.trans hxs)
          (hi''.symm.trans hys) peels
        obtain rfl := ctx.sub.injective (hxs.trans hys.symm)
        exact ⟨Ctx.lookup Δ i, .var i, by rw [hpeel]; exact redU, ctx.free i⟩
  | @fst m Γ p q U A₀ B₀ _ red ih =>
      intro n Δ τ a' b' ctx fa fb ha hb
      obtain ⟨p', rfl, hp⟩ := subst_eq_fst ctx.sub ha
      obtain ⟨q', rfl, hq⟩ := subst_eq_fst ctx.sub hb
      obtain ⟨U', dn, redU, fU⟩ := ih (a' := p') (b' := q') ctx fa fb hp hq
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fU (redU.trans red)
      obtain ⟨A₀', B₀', rfl, hA, _⟩ := subst_eq_sigma ctx.sub eW.symm
      exact ⟨A₀', .fst dn (d.reduces redW), by rw [hA], fW.1⟩
  | @snd m Γ p q U A₀ B₀ _ red ih =>
      intro n Δ τ a' b' ctx fa fb ha hb
      obtain ⟨p', rfl, hp⟩ := subst_eq_snd ctx.sub ha
      obtain ⟨q', rfl, hq⟩ := subst_eq_snd ctx.sub hb
      obtain ⟨U', dn, redU, fU⟩ := ih (a' := p') (b' := q') ctx fa fb hp hq
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fU (redU.trans red)
      obtain ⟨A₀', B₀', rfl, _, hB⟩ := subst_eq_sigma ctx.sub eW.symm
      refine ⟨inst0 (.fst p') B₀', .snd dn (d.reduces redW), ?_, ConstFree.inst0 fa fW.2⟩
      rw [subst_inst0, hB]
      simp only [Presentation.subst, hp]
      exact .refl
  | @heads m Γ X Y h h' rX rY same =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, e₁, _⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨W₂, red₂, e₂, _⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      rw [subst_eq_head ctx.sub e₁.symm] at red₁
      rw [subst_eq_head ctx.sub e₂.symm] at red₂
      exact .heads (d.reduces red₁) (d.reduces red₂) (same.imp id d.headEq)
  | @piTypes m Γ X Y A₁ A₂ B₁ B₂ rX rY _ _ ih₁ ih₂ =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, e₁, f₁⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨A₁', B₁', rfl, hA₁, hB₁⟩ := subst_eq_pi ctx.sub e₁.symm
      obtain ⟨W₂, red₂, e₂, f₂⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      obtain ⟨A₂', B₂', rfl, hA₂, hB₂⟩ := subst_eq_pi ctx.sub e₂.symm
      exact .piTypes (d.reduces red₁) (d.reduces red₂) (ih₁ ctx f₁.1 f₂.1 hA₁ hA₂)
        (ih₂ (ctx.lift f₁.1 (Reduces.of_eq hA₁)) f₁.2 f₂.2 hB₁ hB₂)
  | @sigmaTypes m Γ X Y A₁ A₂ B₁ B₂ rX rY _ _ ih₁ ih₂ =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, e₁, f₁⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨A₁', B₁', rfl, hA₁, hB₁⟩ := subst_eq_sigma ctx.sub e₁.symm
      obtain ⟨W₂, red₂, e₂, f₂⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      obtain ⟨A₂', B₂', rfl, hA₂, hB₂⟩ := subst_eq_sigma ctx.sub e₂.symm
      exact .sigmaTypes (d.reduces red₁) (d.reduces red₂) (ih₁ ctx f₁.1 f₂.1 hA₁ hA₂)
        (ih₂ (ctx.lift f₁.1 (Reduces.of_eq hA₁)) f₁.2 f₂.2 hB₁ hB₂)
  | @idTypes m Γ X Y C C' x x' y y' rX rY _ _ _ ihC ihx ihy =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, e₁, f₁⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨C₁, x₁, y₁, rfl, hC₁, hx₁, hy₁⟩ := subst_eq_id ctx.sub e₁.symm
      obtain ⟨W₂, red₂, e₂, f₂⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      obtain ⟨C₂, x₂, y₂, rfl, hC₂, hx₂, hy₂⟩ := subst_eq_id ctx.sub e₂.symm
      exact .idTypes (d.reduces red₁) (d.reduces red₂) (ihC ctx f₁.1 f₂.1 hC₁ hC₂)
        (ihx ctx f₁.2.1 f₂.2.1 f₁.1 hx₁ hx₂ hC₁) (ihy ctx f₁.2.2 f₂.2.2 f₁.1 hy₁ hy₂ hC₁)
  | @neutralTypes m Γ X Y X₀ Y₀ U rX rY _ ih =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, rfl, f₁⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨W₂, red₂, rfl, f₂⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      obtain ⟨U', dn, _, _⟩ := ih ctx f₁ f₂ rfl rfl
      exact .neutralTypes (d.reduces red₁) (d.reduces red₂) dn

end Reflection

/-- The subtype test holds from further up on the left. -/
theorem BelowAlgorithm.expand_left {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {T₀ T E : Tm Head n}
    (red : Reduces R T₀ T) (below : BelowAlgorithm R Γ T E) : BelowAlgorithm R Γ T₀ E := by
  cases below with
  | conv dd => exact .conv ((Algorithm.expands dd) red .refl)
  | universes rT rE c => exact .universes (red.trans rT) rE c
  | pi rT rE dA dB => exact .pi (red.trans rT) rE dA dB
  | sigma rT rE dA dB => exact .sigma (red.trans rT) rE dA dB

/-- What a derivation of the checking algorithm on images gives for the terms
themselves: a synthesized type reflects up to reduction. -/
def CheckingReflects (R R' : Rules Head) (f : DeclName) (k : Nat) (A : Tm Head 0) :
    Mode → {m : Nat} → Ctx Head m → Tm Head m → Tm Head m → Prop
  | .synth, m, Γ, t, T => ∀ {n : Nat} {Δ : Ctx Head n} {τ : Sub Head n m} {t' : Tm Head n},
      CallContexts R f k A τ Δ Γ → ConstFree f t' → Presentation.subst τ t' = t →
        ∃ T', CheckingAlgorithm R' .synth Δ t' T' ∧ Reduces R (Presentation.subst τ T') T ∧
          ConstFree f T'
  | .check, m, Γ, t, E => ∀ {n : Nat} {Δ : Ctx Head n} {τ : Sub Head n m} {t' E' : Tm Head n},
      CallContexts R f k A τ Δ Γ → ConstFree f t' → ConstFree f E' →
        Presentation.subst τ t' = t → Presentation.subst τ E' = E →
          CheckingAlgorithm R' .check Δ t' E'

section CheckingReflection

variable {R R' : Rules Head} {f : DeclName} {k : Nat} {A : Tm Head 0}
  (d : DeclaresCall R R' f) (inert : CallsInert R f) (reflects : RootReflects R f k)
  (declared : R.constantType f = some A)
include d inert reflects declared

theorem BelowAlgorithm.reflect {m : Nat} {Γ : Ctx Head m} {X Y : Tm Head m}
    (below : BelowAlgorithm R Γ X Y) :
    ∀ {n : Nat} {Δ : Ctx Head n} {τ : Sub Head n m} {X' Y' : Tm Head n},
      CallContexts R f k A τ Δ Γ → ConstFree f X' → ConstFree f Y' →
        Presentation.subst τ X' = X → Presentation.subst τ Y' = Y → BelowAlgorithm R' Δ X' Y' := by
  induction below with
  | conv dd =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      exact .conv (Algorithm.reflect d inert reflects declared dd ctx fX fY hX hY)
  | universes rX rY c =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, e₁, _⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨W₂, red₂, e₂, _⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      rw [subst_eq_head ctx.sub e₁.symm] at red₁
      rw [subst_eq_head ctx.sub e₂.symm] at red₂
      exact .universes (d.reduces red₁) (d.reduces red₂) (d.cumulative c)
  | pi rX rY dA _ ih =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, e₁, f₁⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨A₁', B₁', rfl, hA₁, hB₁⟩ := subst_eq_pi ctx.sub e₁.symm
      obtain ⟨W₂, red₂, e₂, f₂⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      obtain ⟨A₂', B₂', rfl, hA₂, hB₂⟩ := subst_eq_pi ctx.sub e₂.symm
      exact .pi (d.reduces red₁) (d.reduces red₂)
        (Algorithm.reflect d inert reflects declared dA ctx f₁.1 f₂.1 hA₁ hA₂)
        (ih (ctx.lift f₁.1 (Reduces.of_eq hA₁)) f₁.2 f₂.2 hB₁ hB₂)
  | sigma rX rY _ _ ihA ihB =>
      intro n Δ τ X' Y' ctx fX fY hX hY
      subst hX hY
      obtain ⟨W₁, red₁, e₁, f₁⟩ := Reduces.reflect inert reflects ctx.sub fX rX
      obtain ⟨A₁', B₁', rfl, hA₁, hB₁⟩ := subst_eq_sigma ctx.sub e₁.symm
      obtain ⟨W₂, red₂, e₂, f₂⟩ := Reduces.reflect inert reflects ctx.sub fY rY
      obtain ⟨A₂', B₂', rfl, hA₂, hB₂⟩ := subst_eq_sigma ctx.sub e₂.symm
      exact .sigma (d.reduces red₁) (d.reduces red₂) (ihA ctx f₁.1 f₂.1 hA₁ hA₂)
        (ihB (ctx.lift f₁.1 (Reduces.of_eq hA₁)) f₁.2 f₂.2 hB₁ hB₂)

/-- The kernel's checking of an image with `f` declared is the checking of the
term itself, with `f` undeclared: for a synthesized type up to reduction. -/
theorem CheckingAlgorithm.reflect {mode : Mode} {m : Nat} {Γ : Ctx Head m} {t T : Tm Head m}
    (derivation : CheckingAlgorithm R mode Γ t T) : CheckingReflects R R' f k A mode Γ t T := by
  induction derivation with
  | var j =>
      intro n Δ τ t' ctx ft ht
      obtain ⟨i, rfl, hi⟩ := subst_eq_var ht
      exact ⟨Ctx.lookup Δ i, .var i, ctx.var hi, ctx.free i⟩
  | @const m Γ name type known =>
      intro n Δ τ t' ctx ft ht
      rw [subst_eq_const ctx.sub ht] at ft ⊢
      exact ⟨liftClosed type, .const (d.constantType ft known), by rw [subst_liftClosed],
        (d.typesFree (d.constantType ft known)).liftClosed⟩
  | head typing =>
      intro n Δ τ t' ctx ft ht
      rw [subst_eq_head ctx.sub ht]
      exact ⟨_, .head (d.headTyping typing), .refl, trivial⟩
  | pi _ rA hu _ rB hv join ihA ihB =>
      intro n Δ τ t' ctx ft ht
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_pi ctx.sub ht
      obtain ⟨TA', sA, redA, fA⟩ := ihA ctx ft.1 hA
      obtain ⟨WA, rA', eA, _⟩ := Reduces.reflect inert reflects ctx.sub fA (redA.trans rA)
      rw [subst_eq_head ctx.sub eA.symm] at rA'
      obtain ⟨TB', sB, redB, fB⟩ := ihB (ctx.lift ft.1 (Reduces.of_eq hA)) ft.2 hB
      obtain ⟨WB, rB', eB, _⟩ := Reduces.reflect inert reflects ctx.sub.lift fB (redB.trans rB)
      rw [subst_eq_head ctx.sub.lift eB.symm] at rB'
      exact ⟨_, .pi sA (d.reduces rA') (d.isUniverse hu) sB (d.reduces rB') (d.isUniverse hv)
        (d.join join), .refl, trivial⟩
  | sigma _ rA hu _ rB hv join ihA ihB =>
      intro n Δ τ t' ctx ft ht
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_sigma ctx.sub ht
      obtain ⟨TA', sA, redA, fA⟩ := ihA ctx ft.1 hA
      obtain ⟨WA, rA', eA, _⟩ := Reduces.reflect inert reflects ctx.sub fA (redA.trans rA)
      rw [subst_eq_head ctx.sub eA.symm] at rA'
      obtain ⟨TB', sB, redB, fB⟩ := ihB (ctx.lift ft.1 (Reduces.of_eq hA)) ft.2 hB
      obtain ⟨WB, rB', eB, _⟩ := Reduces.reflect inert reflects ctx.sub.lift fB (redB.trans rB)
      rw [subst_eq_head ctx.sub.lift eB.symm] at rB'
      exact ⟨_, .sigma sA (d.reduces rA') (d.isUniverse hu) sB (d.reduces rB') (d.isUniverse hv)
        (d.join join), .refl, trivial⟩
  | id _ rA hu _ _ ihA iha ihb =>
      intro n Δ τ t' ctx ft ht
      obtain ⟨A', a', b', rfl, hA, ha, hb⟩ := subst_eq_id ctx.sub ht
      obtain ⟨TA', sA, redA, fA⟩ := ihA ctx ft.1 hA
      obtain ⟨WA, rA', eA, _⟩ := Reduces.reflect inert reflects ctx.sub fA (redA.trans rA)
      rw [subst_eq_head ctx.sub eA.symm] at rA'
      exact ⟨_, .id sA (d.reduces rA') (d.isUniverse hu) (iha ctx ft.2.1 ft.1 ha hA)
        (ihb ctx ft.2.2 ft.1 hb hA), .refl, trivial⟩
  | @refl m Γ a A₀ _ ih =>
      intro n Δ τ t' ctx ft ht
      obtain ⟨a', rfl, ha⟩ := subst_eq_refl ctx.sub ht
      obtain ⟨A', sa, redA, fA⟩ := ih (t' := a') ctx ft ha
      refine ⟨.id A' a' a', .refl sa, ?_, fA, ft, ft⟩
      show Reduces R (.id (Presentation.subst τ A') (Presentation.subst τ a')
        (Presentation.subst τ a')) (.id A₀ a a)
      rw [ha]
      exact Reduces.congr (f := fun X => Tm.id X a a) (fun s => .congIdTy s) redA
  | @app m Γ g a F A₀ B₀ dg red da ihg iha =>
      intro n Δ τ t' ctx ft ht
      rcases subst_eq_app ht with ⟨x', y', rfl, hx, hy⟩ | ⟨i, rfl, hi⟩
      · obtain ⟨F', sf, redF, fF⟩ := ihg ctx ft.1 hx
        obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fF (redF.trans red)
        obtain ⟨A₀', B₀', rfl, hA, hB⟩ := subst_eq_pi ctx.sub eW.symm
        refine ⟨inst0 y' B₀', .app sf (d.reduces redW) (iha ctx ft.2 fW.1 hy hA), ?_,
          ConstFree.inst0 ft.2 fW.2⟩
        rw [subst_inst0, hy, hB]
      · obtain ⟨xs, _, hxs⟩ := ctx.sub.call_of_app hi
        obtain ⟨peels, hpeel⟩ := ctx.call hxs
        have whole : CheckingAlgorithm R .synth Γ (.app g a) (inst0 a B₀) := .app dg red da
        have red' := CheckingAlgorithm.callSynth inert declared whole (hi.symm.trans hxs) peels
        exact ⟨Ctx.lookup Δ i, .var i, by rw [hpeel]; exact red', ctx.free i⟩
  | fst _ red ih =>
      intro n Δ τ t' ctx ft ht
      obtain ⟨p', rfl, hp⟩ := subst_eq_fst ctx.sub ht
      obtain ⟨P', sp, redP, fP⟩ := ih (t' := p') ctx ft hp
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fP (redP.trans red)
      obtain ⟨A₀', B₀', rfl, hA, _⟩ := subst_eq_sigma ctx.sub eW.symm
      exact ⟨A₀', .fst sp (d.reduces redW), Reduces.of_eq hA, fW.1⟩
  | @snd m Γ p P A₀ B₀ _ red ih =>
      intro n Δ τ t' ctx ft ht
      obtain ⟨p', rfl, hp⟩ := subst_eq_snd ctx.sub ht
      obtain ⟨P', sp, redP, fP⟩ := ih (t' := p') ctx ft hp
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fP (redP.trans red)
      obtain ⟨A₀', B₀', rfl, _, hB⟩ := subst_eq_sigma ctx.sub eW.symm
      refine ⟨inst0 (.fst p') B₀', .snd sp (d.reduces redW), ?_, ConstFree.inst0 ft fW.2⟩
      rw [subst_inst0, hB]
      simp only [Presentation.subst, hp]
      exact .refl
  | @redex m Γ a A₀ b B₀ _ _ iha ihb =>
      intro n Δ τ t' ctx ft ht
      rcases subst_eq_app ht with ⟨x', y', rfl, hx, hy⟩ | ⟨i, rfl, hi⟩
      · obtain ⟨b', rfl, hb⟩ := subst_eq_lam ctx.sub hx
        obtain ⟨A', sa, redA, fA⟩ := iha ctx ft.2 hy
        obtain ⟨B', sb, redB, fB⟩ := ihb (t' := b') (ctx.lift fA redA) ft.1 hb
        refine ⟨inst0 y' B', .redex sa sb, ?_, ConstFree.inst0 ft.2 fB⟩
        rw [subst_inst0, hy]
        exact Reduces.substitute redB (subst0 a)
      · exfalso
        obtain ⟨xs, _, hxs⟩ := ctx.sub.call_of_app hi
        rw [hxs] at hi
        exact appSpine_const_ne_lam hi
  | lamCheck red _ ih =>
      intro n Δ τ t' E' ctx ft fE ht hE
      obtain ⟨b', rfl, hb⟩ := subst_eq_lam ctx.sub ht
      subst hE
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fE red
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_pi ctx.sub eW.symm
      exact .lamCheck (d.reduces redW) (ih (ctx.lift fW.1 (Reduces.of_eq hA)) ft fW.2 hb hB)
  | pairCheck red _ _ iha ihb =>
      intro n Δ τ t' E' ctx ft fE ht hE
      obtain ⟨a', b', rfl, ha, hb⟩ := subst_eq_pair ctx.sub ht
      subst hE
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fE red
      obtain ⟨A', B', rfl, hA, hB⟩ := subst_eq_sigma ctx.sub eW.symm
      exact .pairCheck (d.reduces redW) (iha ctx ft.1 fW.1 ha hA)
        (ihb ctx ft.2 (ConstFree.inst0 ft.1 fW.2) hb (by rw [subst_inst0, ha, hB]))
  | reflCheck red _ dxa dxb ih =>
      intro n Δ τ t' E' ctx ft fE ht hE
      obtain ⟨x', rfl, hx⟩ := subst_eq_refl ctx.sub ht
      subst hE
      obtain ⟨W, redW, eW, fW⟩ := Reduces.reflect inert reflects ctx.sub fE red
      obtain ⟨A', a', b', rfl, hA, ha, hb⟩ := subst_eq_id ctx.sub eW.symm
      exact .reflCheck (d.reduces redW) (ih (t' := x') ctx ft fW.1 hx hA)
        (Algorithm.reflect d inert reflects declared dxa ctx ft fW.2.1 fW.1 hx ha hA)
        (Algorithm.reflect d inert reflects declared dxb ctx ft fW.2.2 fW.1 hx hb hA)
  | switch _ le ih =>
      intro n Δ τ t' E' ctx ft fE ht hE
      obtain ⟨T', st, redT, fT⟩ := ih ctx ft ht
      exact .switch st (BelowAlgorithm.reflect d inert reflects declared
        (BelowAlgorithm.expand_left redT le) ctx fT fE rfl hE)

end CheckingReflection

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
