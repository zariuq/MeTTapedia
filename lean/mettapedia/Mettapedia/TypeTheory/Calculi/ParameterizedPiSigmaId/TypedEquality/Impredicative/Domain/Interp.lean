import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Operations

/-!
# The interpretation of terms in the domain

Every term of the parameterized calculus is interpreted, in an environment of
ideals, by an ideal (Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand,
Melliès and Weirich, *Definitional Inversion, Without Normalisation*, Fig. 4).
The interpretation of heads and declared constants is a parameter (`Reading`):
a rule package's model supplies it. Variables denote their value in the
environment, and every term former denotes the corresponding operation on
ideals (`Domain/Operations`). A function is interpreted by its graph on all
inputs, since a function term carries no domain.

The laws of the interpretation that do not involve typing:

* it is monotone in the environment (`interp_mono`);
* it commutes with renaming and with simultaneous substitution
  (`interp_rename`, `interp_subst`, the paper's Lemma 2.29);
* it is continuous: every token of the value is produced by finite parts of
  the environment's values (`interp_cont`);
* it validates β for functions and for both projections of pairs
  (`interp_beta`, `interp_fst_pair`, `interp_snd_pair`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

open Ideal

variable {Head : Type}

/-- What the interpretation reads from a rule package: the compact element of
each head, and the ideal of each declared constant. -/
structure Reading (Head : Type) where
  /-- The element of a head. -/
  head : Head → List Tok
  /-- The ideal of a declared constant. -/
  const : DeclName → Ideal

/-- An environment: an ideal for each variable. -/
abbrev Env (n : Nat) := Fin n → Ideal

/-- Extending an environment by a value for the innermost variable. -/
def Env.cons {n : Nat} (I : Ideal) (ρ : Env n) : Env (n + 1) := Fin.cases I ρ

@[simp] theorem Env.cons_zero {n : Nat} (I : Ideal) (ρ : Env n) : Env.cons I ρ 0 = I := rfl

@[simp] theorem Env.cons_succ {n : Nat} (I : Ideal) (ρ : Env n) (i : Fin n) :
    Env.cons I ρ i.succ = ρ i := rfl

/-- The environment of finite approximations. -/
def Env.approx {n : Nat} (X : Fin n → List Tok) : Env n := fun i => principal (X i)

/-- One environment below another, variable by variable. -/
def Env.Le {n : Nat} (ρ ρ' : Env n) : Prop := ∀ i, ρ i ≤ ρ' i

theorem Env.Le.refl {n : Nat} (ρ : Env n) : Env.Le ρ ρ := fun i => le_refl (ρ i)

theorem Env.Le.cons {n : Nat} {I I' : Ideal} {ρ ρ' : Env n} (hI : I ≤ I') (hρ : Env.Le ρ ρ') :
    Env.Le (Env.cons I ρ) (Env.cons I' ρ') := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hI
  · exact hρ j

theorem principal_mono {X X' : List Tok} (h : X ⊑ X') : principal X ≤ principal X' :=
  fun _ ht => ent_cut ht h

/-- The interpretation of a term in an environment. -/
def interp (Rd : Reading Head) : {n : Nat} → Tm Head n → Env n → Ideal
  | _, .var i, ρ => ρ i
  | _, .const c, _ => Rd.const c
  | _, .head h, _ => principal (Rd.head h)
  | _, .pi A B, ρ => former .pi (interp Rd A ρ) fun X => interp Rd B (Env.cons (principal X) ρ)
  | _, .sigma A B, ρ =>
      former .sigma (interp Rd A ρ) fun X => interp Rd B (Env.cons (principal X) ρ)
  | _, .id A a b, ρ => ident (interp Rd A ρ) (interp Rd a ρ) (interp Rd b ρ)
  | _, .lam b, ρ => Ideal.lam fun X => interp Rd b (Env.cons (principal X) ρ)
  | _, .app f a, ρ => Ideal.app (interp Rd f ρ) (interp Rd a ρ)
  | _, .pair a b, ρ => Ideal.pair (interp Rd a ρ) (interp Rd b ρ)
  | _, .fst p, ρ => Ideal.fst (interp Rd p ρ)
  | _, .snd p, ρ => Ideal.snd (interp Rd p ρ)
  | _, .refl a, ρ => Ideal.refl (interp Rd a ρ)

variable (Rd : Reading Head)

/-! ## Monotonicity -/

/-- **The interpretation is monotone in the environment.** -/
theorem interp_mono {n : Nat} (M : Tm Head n) {ρ ρ' : Env n} (h : Env.Le ρ ρ') :
    interp Rd M ρ ≤ interp Rd M ρ' := by
  induction M with
  | var i => exact h i
  | const c => exact le_refl _
  | head hd => exact le_refl _
  | pi A B ihA ihB =>
      exact former_mono (ihA h) fun X => ihB (Env.Le.cons (le_refl _) h)
  | sigma A B ihA ihB =>
      exact former_mono (ihA h) fun X => ihB (Env.Le.cons (le_refl _) h)
  | id A a b ihA iha ihb => exact ident_mono (ihA h) (iha h) (ihb h)
  | lam b ih => exact lam_mono fun X => ih (Env.Le.cons (le_refl _) h)
  | app f a ihf iha => exact app_mono (ihf h) (iha h)
  | pair a b iha ihb => exact pair_mono (iha h) (ihb h)
  | fst p ih => exact fst_mono (ih h)
  | snd p ih => exact snd_mono (ih h)
  | refl a ih => exact refl_mono (ih h)

/-- The family of a binder is monotone in its argument. -/
theorem interp_family_monotone {n : Nat} (B : Tm Head (n + 1)) (ρ : Env n) :
    Ideal.Monotone fun X => interp Rd B (Env.cons (principal X) ρ) :=
  fun h => interp_mono Rd B (Env.Le.cons (principal_mono h) (Env.Le.refl ρ))

/-! ## Renaming and substitution -/

theorem cons_liftRen {n m : Nat} (r : Ren n m) (I : Ideal) (ρ : Env m) :
    (fun i => Env.cons I ρ (liftRen r i)) = Env.cons I (fun i => ρ (r i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- **The interpretation commutes with renaming.** -/
theorem interp_rename {n m : Nat} (r : Ren n m) (M : Tm Head n) (ρ : Env m) :
    interp Rd (rename r M) ρ = interp Rd M fun i => ρ (r i) := by
  induction M generalizing m with
  | var i => rfl
  | const c => rfl
  | head hd => rfl
  | pi A B ihA ihB =>
      simp only [rename, interp, ihA, ihB, cons_liftRen]
  | sigma A B ihA ihB =>
      simp only [rename, interp, ihA, ihB, cons_liftRen]
  | id A a b ihA iha ihb => simp only [rename, interp, ihA, iha, ihb]
  | lam b ih => simp only [rename, interp, ih, cons_liftRen]
  | app f a ihf iha => simp only [rename, interp, ihf, iha]
  | pair a b iha ihb => simp only [rename, interp, iha, ihb]
  | fst p ih => simp only [rename, interp, ih]
  | snd p ih => simp only [rename, interp, ih]
  | refl a ih => simp only [rename, interp, ih]

theorem interp_weaken {n : Nat} (M : Tm Head n) (I : Ideal) (ρ : Env n) :
    interp Rd (rename wk M) (Env.cons I ρ) = interp Rd M ρ := by
  rw [interp_rename]
  rfl

theorem cons_liftSub {n m : Nat} (σ : Sub Head n m) (I : Ideal) (ρ : Env m) :
    (fun i => interp Rd (liftSub σ i) (Env.cons I ρ)) =
      Env.cons I (fun i => interp Rd (σ i) ρ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact interp_weaken Rd (σ j) I ρ

/-- **The interpretation commutes with substitution** (the paper's Lemma 2.29). -/
theorem interp_subst {n m : Nat} (σ : Sub Head n m) (M : Tm Head n) (ρ : Env m) :
    interp Rd (subst σ M) ρ = interp Rd M fun i => interp Rd (σ i) ρ := by
  induction M generalizing m with
  | var i => rfl
  | const c => rfl
  | head hd => rfl
  | pi A B ihA ihB =>
      simp only [subst, interp, ihA, ihB, cons_liftSub]
  | sigma A B ihA ihB =>
      simp only [subst, interp, ihA, ihB, cons_liftSub]
  | id A a b ihA iha ihb => simp only [subst, interp, ihA, iha, ihb]
  | lam b ih => simp only [subst, interp, ih, cons_liftSub]
  | app f a ihf iha => simp only [subst, interp, ihf, iha]
  | pair a b iha ihb => simp only [subst, interp, iha, ihb]
  | fst p ih => simp only [subst, interp, ih]
  | snd p ih => simp only [subst, interp, ih]
  | refl a ih => simp only [subst, interp, ih]

theorem subst0_env {n : Nat} (a : Tm Head n) (ρ : Env n) :
    (fun i => interp Rd (subst0 a i) ρ) = Env.cons (interp Rd a ρ) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Opening a binder is interpreting its body with the argument's value. -/
theorem interp_inst0 {n : Nat} (a : Tm Head n) (b : Tm Head (n + 1)) (ρ : Env n) :
    interp Rd (inst0 a b) ρ = interp Rd b (Env.cons (interp Rd a ρ) ρ) := by
  rw [inst0, interp_subst, subst0_env]

/-! ## Continuity -/

/-- The join of two families of finite approximations. -/
def approxJoin {n : Nat} (X X' : Fin n → List Tok) : Fin n → List Tok := fun i => X i ++ X' i

theorem approx_le_join_left {n : Nat} (X X' : Fin n → List Tok) :
    Env.Le (Env.approx X) (Env.approx (approxJoin X X')) :=
  fun _ => principal_mono (Le.append_left _ _)

theorem approx_le_join_right {n : Nat} (X X' : Fin n → List Tok) :
    Env.Le (Env.approx X') (Env.approx (approxJoin X X')) :=
  fun _ => principal_mono (Le.append_right _ _)

theorem approx_le {n : Nat} {X : Fin n → List Tok} {ρ : Env n} (h : ∀ i, Below (X i) (ρ i)) :
    Env.Le (Env.approx X) ρ :=
  fun i => principal_le_iff.2 (h i)

/-- A finite approximation of an environment. -/
def Approximates {n : Nat} (X : Fin n → List Tok) (ρ : Env n) : Prop := ∀ i, Below (X i) (ρ i)

theorem Approximates.join {n : Nat} {X X' : Fin n → List Tok} {ρ : Env n}
    (h : Approximates X ρ) (h' : Approximates X' ρ) : Approximates (approxJoin X X') ρ :=
  fun i => (h i).append (h' i)

theorem Approximates.nil {n : Nat} (ρ : Env n) : Approximates (fun _ => []) ρ :=
  fun _ _ h => absurd h List.not_mem_nil

/-- A term is continuous at an environment: each token of its value is in the
value at a finite approximation of the environment. -/
def Continuous {n : Nat} (M : Tm Head n) (ρ : Env n) : Prop :=
  ∀ t, (interp Rd M ρ).Mem t → ∃ X, Approximates X ρ ∧ (interp Rd M (Env.approx X)).Mem t

/-- Continuity for finitely many tokens at once. -/
theorem Continuous.below {n : Nat} {M : Tm Head n} {ρ : Env n} (hM : Continuous Rd M ρ)
    {v : List Tok} (hv : Below v (interp Rd M ρ)) :
    ∃ X, Approximates X ρ ∧ Below v (interp Rd M (Env.approx X)) := by
  induction v with
  | nil => exact ⟨fun _ => [], Approximates.nil ρ, fun _ h => absurd h List.not_mem_nil⟩
  | cons t v ih =>
    obtain ⟨X₁, h₁, ht⟩ := hM t (hv t List.mem_cons_self)
    obtain ⟨X₂, h₂, hv₂⟩ := ih fun s hs => hv s (List.mem_cons_of_mem _ hs)
    refine ⟨approxJoin X₁ X₂, h₁.join h₂, fun s hs => ?_⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact interp_mono Rd M (approx_le_join_left X₁ X₂) _ ht
    · exact interp_mono Rd M (approx_le_join_right X₁ X₂) _ (hv₂ s hs)

/-- Continuity under a binder: a token of the body's value at an extended
environment comes from finite approximations of the argument and of the
environment. -/
theorem Continuous.binder {n : Nat} {B : Tm Head (n + 1)} {ρ : Env n} {I : Ideal}
    (hB : Continuous Rd B (Env.cons I ρ)) {v : List Tok} (hv : Below v (interp Rd B (Env.cons I ρ))) :
    ∃ X, Approximates X ρ ∧ ∃ Z, Below Z I ∧
      Below v (interp Rd B (Env.cons (principal Z) (Env.approx X))) := by
  obtain ⟨X, hX, hv'⟩ := hB.below Rd hv
  refine ⟨fun i => X i.succ, fun i => hX i.succ, X 0, hX 0, hv'.mono ?_⟩
  refine interp_mono Rd B fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact le_refl _
  · exact le_refl _

/-- A generated ideal whose generators each come from finite approximations. -/
theorem closure_cont {n : Nat} {P : Env n → Tok → Prop} {ρ : Env n}
    (hmono : ∀ {X X' : Fin n → List Tok}, Env.Le (Env.approx X) (Env.approx X') →
      ∀ s, P (Env.approx X) s → P (Env.approx X') s)
    (hgen : ∀ s, P ρ s → ∃ X, Approximates X ρ ∧ P (Env.approx X) s) {t : Tok}
    (ht : (closure (P ρ)).Mem t) :
    ∃ X, Approximates X ρ ∧ (closure (P (Env.approx X))).Mem t := by
  obtain ⟨v, hv, ht⟩ := ht
  suffices h : ∃ X, Approximates X ρ ∧ ∀ s ∈ v, P (Env.approx X) s by
    obtain ⟨X, hX, hv'⟩ := h
    exact ⟨X, hX, v, hv', ht⟩
  clear ht
  induction v with
  | nil => exact ⟨fun _ => [], Approximates.nil ρ, fun _ h => absurd h List.not_mem_nil⟩
  | cons s v ih =>
    obtain ⟨X₁, h₁, hs⟩ := hgen s (hv s List.mem_cons_self)
    obtain ⟨X₂, h₂, hv₂⟩ := ih fun r hr => hv r (List.mem_cons_of_mem _ hr)
    refine ⟨approxJoin X₁ X₂, h₁.join h₂, fun r hr => ?_⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hmono (approx_le_join_left X₁ X₂) _ hs
    · exact hmono (approx_le_join_right X₁ X₂) _ (hv₂ r hr)

/-- A family's generator from finite approximations: the dependency and the
output of a family entry come from finite approximations of the environment. -/
private theorem family_gen {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {ρ : Env n}
    (hA : ∀ ρ, Continuous Rd A ρ) (hB : ∀ ρ, Continuous Rd B ρ) {D X Y : List Tok}
    (hD : Below D (interp Rd A ρ)) (hY : Below Y (interp Rd B (Env.cons (principal X) ρ))) :
    ∃ Z, Approximates Z ρ ∧ Below D (interp Rd A (Env.approx Z)) ∧
      Below Y (interp Rd B (Env.cons (principal X) (Env.approx Z))) := by
  obtain ⟨Z₁, h₁, hD'⟩ := (hA ρ).below Rd hD
  obtain ⟨Z₂, h₂, W, hW, hY'⟩ := Continuous.binder Rd (hB _) hY
  refine ⟨approxJoin Z₁ Z₂, h₁.join h₂, hD'.mono (interp_mono Rd A
    (approx_le_join_left Z₁ Z₂)), hY'.mono (interp_mono Rd B ?_)⟩
  exact Env.Le.cons (principal_le_iff.2 hW) (approx_le_join_right Z₁ Z₂)

private theorem former_cont {n : Nat} (k : Kind) {A : Tm Head n} {B : Tm Head (n + 1)}
    (hA : ∀ ρ, Continuous Rd A ρ) (hB : ∀ ρ, Continuous Rd B ρ) (ρ : Env n) {t : Tok}
    (ht : (former k (interp Rd A ρ) fun X => interp Rd B (Env.cons (principal X) ρ)).Mem t) :
    ∃ X, Approximates X ρ ∧
      (former k (interp Rd A (Env.approx X)) fun Y =>
        interp Rd B (Env.cons (principal Y) (Env.approx X))).Mem t := by
  refine closure_cont (P := fun ρ s => s = .tag k ∨ (∃ d, s = .arg k 0 [] d ∧ (interp Rd A ρ).Mem d) ∨
      ∃ D X Y, s = .fn k D X Y ∧ Below D (interp Rd A ρ) ∧
        Below Y (interp Rd B (Env.cons (principal X) ρ))) ?_ ?_ ht
  · intro X X' hXX' s hs
    rcases hs with rfl | ⟨d, rfl, hd⟩ | ⟨D, Z, Y, rfl, hD, hY⟩
    · exact .inl rfl
    · exact .inr (.inl ⟨d, rfl, interp_mono Rd A hXX' d hd⟩)
    · exact .inr (.inr ⟨D, Z, Y, rfl, hD.mono (interp_mono Rd A hXX'),
        hY.mono (interp_mono Rd B (Env.Le.cons (le_refl _) hXX'))⟩)
  · intro s hs
    rcases hs with rfl | ⟨d, rfl, hd⟩ | ⟨D, Z, Y, rfl, hD, hY⟩
    · exact ⟨fun _ => [], Approximates.nil ρ, .inl rfl⟩
    · obtain ⟨X, hX, hd'⟩ := hA ρ d hd
      exact ⟨X, hX, .inr (.inl ⟨d, rfl, hd'⟩)⟩
    · obtain ⟨X, hX, hD', hY'⟩ := family_gen Rd hA hB hD hY
      exact ⟨X, hX, .inr (.inr ⟨D, Z, Y, rfl, hD', hY'⟩)⟩

/-- **The interpretation is continuous**: every token of a term's value is in its
value at a finite approximation of the environment. -/
theorem interp_cont {n : Nat} (M : Tm Head n) : ∀ ρ, Continuous Rd M ρ := by
  induction M with
  | @var n i =>
    intro ρ t ht
    refine ⟨fun j => if j = i then [t] else [], fun j => ?_, ?_⟩
    · by_cases h : j = i
      · subst h
        simp only [if_true]
        intro s hs
        rw [List.mem_singleton.1 hs]
        exact ht
      · simp only [h, if_false]
        exact fun _ hs => absurd hs List.not_mem_nil
    · show ent (if i = i then [t] else []) t = true
      simp only [if_true]
      exact ent_of_mem List.mem_cons_self
  | const c =>
    intro ρ t ht
    exact ⟨fun _ => [], Approximates.nil ρ, ht⟩
  | head hd =>
    intro ρ t ht
    exact ⟨fun _ => [], Approximates.nil ρ, ht⟩
  | pi A B ihA ihB =>
    intro ρ t ht
    exact former_cont Rd .pi ihA ihB ρ ht
  | sigma A B ihA ihB =>
    intro ρ t ht
    exact former_cont Rd .sigma ihA ihB ρ ht
  | id A a b ihA iha ihb =>
    intro ρ t ht
    refine closure_cont (P := fun ρ s => s = .tag .ident ∨
        (∃ d, s = .arg .ident 0 [] d ∧ (interp Rd A ρ).Mem d) ∨
        (∃ C r, s = .arg .ident 1 C r ∧ Below C (interp Rd A ρ) ∧ (interp Rd a ρ).Mem r) ∨
        ∃ C r, s = .arg .ident 2 C r ∧ Below C (interp Rd A ρ) ∧ (interp Rd b ρ).Mem r)
      ?_ ?_ ht
    · intro X X' hXX' s hs
      rcases hs with rfl | ⟨d, rfl, hd⟩ | ⟨C, r, rfl, hC, hr⟩ | ⟨C, r, rfl, hC, hr⟩
      · exact .inl rfl
      · exact .inr (.inl ⟨d, rfl, interp_mono Rd A hXX' d hd⟩)
      · exact .inr (.inr (.inl ⟨C, r, rfl, hC.mono (interp_mono Rd A hXX'),
          interp_mono Rd a hXX' r hr⟩))
      · exact .inr (.inr (.inr ⟨C, r, rfl, hC.mono (interp_mono Rd A hXX'),
          interp_mono Rd b hXX' r hr⟩))
    · intro s hs
      rcases hs with rfl | ⟨d, rfl, hd⟩ | ⟨C, r, rfl, hC, hr⟩ | ⟨C, r, rfl, hC, hr⟩
      · exact ⟨fun _ => [], Approximates.nil ρ, .inl rfl⟩
      · obtain ⟨X, hX, hd'⟩ := ihA ρ d hd
        exact ⟨X, hX, .inr (.inl ⟨d, rfl, hd'⟩)⟩
      · obtain ⟨X₁, h₁, hC'⟩ := (ihA ρ).below Rd hC
        obtain ⟨X₂, h₂, hr'⟩ := iha ρ r hr
        exact ⟨approxJoin X₁ X₂, h₁.join h₂, .inr (.inr (.inl ⟨C, r, rfl,
          hC'.mono (interp_mono Rd A (approx_le_join_left X₁ X₂)),
          interp_mono Rd a (approx_le_join_right X₁ X₂) r hr'⟩))⟩
      · obtain ⟨X₁, h₁, hC'⟩ := (ihA ρ).below Rd hC
        obtain ⟨X₂, h₂, hr'⟩ := ihb ρ r hr
        exact ⟨approxJoin X₁ X₂, h₁.join h₂, .inr (.inr (.inr ⟨C, r, rfl,
          hC'.mono (interp_mono Rd A (approx_le_join_left X₁ X₂)),
          interp_mono Rd b (approx_le_join_right X₁ X₂) r hr'⟩))⟩
  | lam b ih =>
    intro ρ t ht
    refine closure_cont (P := fun ρ s => ∃ X Y, s = .fn .lam [] X Y ∧
        Below Y (interp Rd b (Env.cons (principal X) ρ))) ?_ ?_ ht
    · intro X X' hXX' s ⟨Z, Y, e, hY⟩
      exact ⟨Z, Y, e, hY.mono (interp_mono Rd b (Env.Le.cons (le_refl _) hXX'))⟩
    · intro s ⟨Z, Y, e, hY⟩
      obtain ⟨X, hX, W, hW, hY'⟩ := Continuous.binder Rd (ih _) hY
      exact ⟨X, hX, Z, Y, e, hY'.mono (interp_mono Rd b
        (Env.Le.cons (principal_le_iff.2 hW) (Env.Le.refl _)))⟩
  | app f a ihf iha =>
    intro ρ t ht
    obtain ⟨X, Y, hX, hf, hY⟩ := mem_app.1 ht
    obtain ⟨Z₁, h₁, hf'⟩ := ihf ρ _ hf
    obtain ⟨Z₂, h₂, hX'⟩ := (iha ρ).below Rd hX
    refine ⟨approxJoin Z₁ Z₂, h₁.join h₂, mem_app.2 ⟨X, Y, ?_, ?_, hY⟩⟩
    · exact hX'.mono (interp_mono Rd a (approx_le_join_right Z₁ Z₂))
    · exact interp_mono Rd f (approx_le_join_left Z₁ Z₂) _ hf'
  | pair a b iha ihb =>
    intro ρ t ht
    refine closure_cont (P := fun ρ s => (∃ r, s = .arg .pair 0 [] r ∧ (interp Rd a ρ).Mem r) ∨
        ∃ C r, s = .arg .pair 1 C r ∧ Below C (interp Rd a ρ) ∧ (interp Rd b ρ).Mem r) ?_ ?_ ht
    · intro X X' hXX' s hs
      rcases hs with ⟨r, rfl, hr⟩ | ⟨C, r, rfl, hC, hr⟩
      · exact .inl ⟨r, rfl, interp_mono Rd a hXX' r hr⟩
      · exact .inr ⟨C, r, rfl, hC.mono (interp_mono Rd a hXX'), interp_mono Rd b hXX' r hr⟩
    · intro s hs
      rcases hs with ⟨r, rfl, hr⟩ | ⟨C, r, rfl, hC, hr⟩
      · obtain ⟨X, hX, hr'⟩ := iha ρ r hr
        exact ⟨X, hX, .inl ⟨r, rfl, hr'⟩⟩
      · obtain ⟨X₁, h₁, hC'⟩ := (iha ρ).below Rd hC
        obtain ⟨X₂, h₂, hr'⟩ := ihb ρ r hr
        exact ⟨approxJoin X₁ X₂, h₁.join h₂, .inr ⟨C, r, rfl,
          hC'.mono (interp_mono Rd a (approx_le_join_left X₁ X₂)),
          interp_mono Rd b (approx_le_join_right X₁ X₂) r hr'⟩⟩
  | fst p ih =>
    intro ρ t ht
    refine closure_cont (P := fun ρ s => (interp Rd p ρ).Mem (.arg .pair 0 [] s)) ?_ ?_ ht
    · intro X X' hXX' s hs
      exact interp_mono Rd p hXX' _ hs
    · intro s hs
      exact ih ρ _ hs
  | snd p ih =>
    intro ρ t ht
    refine closure_cont (P := fun ρ s => ∃ C, (interp Rd p ρ).Mem (.arg .pair 1 C s)) ?_ ?_ ht
    · intro X X' hXX' s ⟨C, hs⟩
      exact ⟨C, interp_mono Rd p hXX' _ hs⟩
    · intro s ⟨C, hs⟩
      obtain ⟨X, hX, hs'⟩ := ih ρ _ hs
      exact ⟨X, hX, C, hs'⟩
  | refl a ih =>
    intro ρ t ht
    refine closure_cont (P := fun ρ s => s = .tag .refl ∨
        ∃ r, s = .arg .refl 0 [] r ∧ (interp Rd a ρ).Mem r) ?_ ?_ ht
    · intro X X' hXX' s hs
      rcases hs with rfl | ⟨r, rfl, hr⟩
      · exact .inl rfl
      · exact .inr ⟨r, rfl, interp_mono Rd a hXX' r hr⟩
    · intro s hs
      rcases hs with rfl | ⟨r, rfl, hr⟩
      · exact ⟨fun _ => [], Approximates.nil ρ, .inl rfl⟩
      · obtain ⟨X, hX, hr'⟩ := ih ρ r hr
        exact ⟨X, hX, .inr ⟨r, rfl, hr'⟩⟩

/-! ## Computation -/

/-- **β for functions**: applying the interpretation of an abstraction is
interpreting its body with the argument's value. -/
theorem interp_beta {n : Nat} (b : Tm Head (n + 1)) (a : Tm Head n) (ρ : Env n) :
    interp Rd (.app (.lam b) a) ρ = interp Rd (inst0 a b) ρ := by
  rw [interp_inst0]
  apply le_antisymm
  · intro t ht
    obtain ⟨X, Y, hX, hl, hY⟩ := mem_app.1 ht
    have hY' := (mem_lam_fn (interp_family_monotone Rd b ρ)).1 hl
    refine Ideal.closed _ (hY'.mono (interp_mono Rd b ?_)) hY
    exact Env.Le.cons (principal_le_iff.2 hX) (Env.Le.refl ρ)
  · intro t ht
    obtain ⟨X, hX, W, hW, ht'⟩ := Continuous.binder Rd (interp_cont Rd b _)
      (v := [t]) (fun s hs => by rw [List.mem_singleton.1 hs]; exact ht)
    refine mem_app.2 ⟨W, [t], hW, (mem_lam_fn (interp_family_monotone Rd b ρ)).2 ?_,
      ent_of_mem List.mem_cons_self⟩
    exact ht'.mono (interp_mono Rd b (Env.Le.cons (le_refl _) (approx_le hX)))

/-- β for the first projection. -/
theorem interp_fst_pair {n : Nat} (a b : Tm Head n) (ρ : Env n) :
    interp Rd (.fst (.pair a b)) ρ = interp Rd a ρ :=
  Ideal.fst_pair _ _

/-- β for the second projection. -/
theorem interp_snd_pair {n : Nat} (a b : Tm Head n) (ρ : Env n) :
    interp Rd (.snd (.pair a b)) ρ = interp Rd b ρ :=
  Ideal.snd_pair _ _

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
