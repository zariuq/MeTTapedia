import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Continuity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Syntax

/-!
# The interpretation of annotated terms, and constants that carry their declared types

**Dependent types and abstractions that carry their domain.** `Ideal.cpi A G` is the
dependent function type whose family sees its argument through the projection onto
its domain `A` (`Ideal.csigma` for pairs), and `Ideal.clam A G` the function that
sees its argument through that projection. For a continuous family:

* the family at `y` is `G (π_A y)` (`Ideal.fam_cpi`);
* applying the projection of `f` onto `cpi A G` to `y` projects `y` onto `A`, applies
  `f`, and projects the value onto the family there
  (`Ideal.app_projT_cpi`); so an element of `cpi A G` applied to an element of `A`
  is an element of the family's value (`Ideal.semTyped_app`).

**The interpretation** (`cinterp`) of annotated terms (`Annotated.CTm`) reads
dependent types and abstractions this way (Carneiro, Coquand, Frabetti Mathieu,
Lennon-Bertrand, Melliès and Weirich, *Definitional Inversion, Without
Normalisation*, Fig. 4 and §2.5). It is continuous in the environment
(`cinterp_envCont`).

**Constants that carry their declared types.** A type with `n` nested dependent
function types of this kind is a *Church telescope* (`Ideal.ChurchTele`); the
interpretation of every annotated dependent function type is one
(`churchTele_cinterp`). The value of a constant is the projection of a function onto
its declared type. Applied to arguments (`Ideal.appSpine`), it projects each
argument onto its parameter type (`Ideal.projArgs`), applies the function, and
projects the value onto the declared type instantiated at the arguments
(`Ideal.instPi`) (`Ideal.appSpine_projT`). At a spine whose arguments are elements of
their parameter types (`Ideal.SpineTyped`), the argument projections are the
identity (`Ideal.appSpine_churchConst`). So such a constant computes to a contractum
whenever its function computes to it and the contractum is an element of the
instantiated type (`Ideal.churchConst_root`).

**Spine facts.** A spine of a constant of declared type `D` has spine facts at a type
`τ` (`Ideal.SpineFacts`) when `τ` is `D` instantiated at the arguments and each
argument is an element of its parameter type. They are preserved by application to
an element of the domain of the instantiated type, whose value is then an element of
the family there (`Ideal.SpineFacts.snoc`, from `Ideal.spine_snoc` and
`Ideal.spine_app`); arguments with one projection give one instantiated type
(`Ideal.SpineFacts.snoc_congr`); and they are kept by conversion
(`Ideal.SpineFacts.conv`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

open Annotated (CTm)

namespace Ideal

/-! ## Dependent types and functions that carry their domain -/

/-- The dependent function type whose family sees its argument through the
projection onto its domain. -/
def cpi (A : Ideal) (G : Ideal → Ideal) : Ideal := former .pi A fun X => G (projT A (principal X))

/-- The dependent pair type whose family sees its argument through the projection
onto its domain. -/
def csigma (A : Ideal) (G : Ideal → Ideal) : Ideal :=
  former .sigma A fun X => G (projT A (principal X))

/-- The function that sees its argument through the projection onto `A`. -/
def clam (A : Ideal) (G : Ideal → Ideal) : Ideal := lam fun X => G (projT A (principal X))

variable {A : Ideal} {G : Ideal → Ideal}

theorem dom_cpi (A : Ideal) (G : Ideal → Ideal) : dom .pi (cpi A G) = A := dom_former _ _ _

/-- **The family of `cpi A G` at `y` is `G` at the projection of `y`.** -/
theorem fam_cpi (hG : Cont G) (y : Ideal) : fam .pi (cpi A G) y = G (projT A y) :=
  fam_former_principal (k := .pi) A (hG.comp (cont_projT A)) y

/-- **Applying an element projected onto `cpi A G`**: the argument is projected onto
`A`, and the value onto the family there. -/
theorem app_projT_cpi (hG : Cont G) (f y : Ideal) :
    app (projT (cpi A G) f) y = projT (G (projT A y)) (app f (projT A y)) := by
  have hF : Monotone fun X => G (projT A (principal X)) :=
    fun h => hG.mono (projT_mono (principal_mono h))
  have hH : Cont fun z => projT (G (projT A z)) (app f (projT A z)) :=
    cont₂_projT.comp (hG.comp (cont_projT A)) ((cont₂_app.right f).comp (cont_projT A))
  have e : piProj A (fun X => G (projT A (principal X))) f =
      fun X => projT (G (projT A (principal X))) (app f (projT A (principal X))) := by
    funext X
    have h := fam_cpi (A := A) hG (projT A (principal X))
    rw [projT_projT] at h
    exact congrArg (fun T => projT T (app f (projT A (principal X)))) h
  rw [cpi, projT_pi hF, e]
  exact app_lam_principal hH y

/-- An element of `cpi A G` applied to `y` is its value at the projection of `y`,
projected onto the family there. -/
theorem app_of_mem_cpi (hG : Cont G) {f : Ideal} (hf : projT (cpi A G) f = f) (y : Ideal) :
    app f y = projT (G (projT A y)) (app f (projT A y)) := by
  conv_lhs => rw [← hf]
  exact app_projT_cpi hG f y

/-- An element of `cpi A G` sees its argument only through the projection onto `A`. -/
theorem app_projT_arg (hG : Cont G) {f : Ideal} (hf : projT (cpi A G) f = f) (y : Ideal) :
    app f (projT A y) = app f y := by
  rw [app_of_mem_cpi hG hf (projT A y), app_of_mem_cpi hG hf y, projT_projT]

/-- **Semantic application**: an element of `cpi A G` applied to an element of `A` is
an element of the family's value there. -/
theorem semTyped_app (hG : Cont G) {f a : Ideal} (hf : projT (cpi A G) f = f)
    (ha : projT A a = a) : projT (G a) (app f a) = app f a := by
  rw [app_of_mem_cpi hG hf a, ha, projT_projT]

/-! ## Spines -/

/-- Iterated application. -/
def appSpine (f : Ideal) : List Ideal → Ideal
  | [] => f
  | a :: as => appSpine (app f a) as

/-- A dependent function type instantiated at arguments, each projected onto the
domain it is an argument of. -/
def instPi : Ideal → List Ideal → Ideal
  | T, [] => T
  | T, y :: ys => instPi (fam .pi T (projT (dom .pi T) y)) ys

/-- The arguments projected onto their parameter types, along the instantiation. -/
def projArgs : Ideal → List Ideal → List Ideal
  | _, [] => []
  | T, y :: ys => projT (dom .pi T) y :: projArgs (fam .pi T (projT (dom .pi T) y)) ys

/-- **Spine facts**: each argument is an element of its parameter type, the
declared type instantiated at the arguments before it. -/
def SpineTyped : Ideal → List Ideal → Prop
  | _, [] => True
  | T, y :: ys => projT (dom .pi T) y = y ∧ SpineTyped (fam .pi T (projT (dom .pi T) y)) ys

/-- A Church telescope with `n` parameters: `n` nested dependent function types
whose families see their arguments through the projections onto their domains and
are continuous. -/
def ChurchTele : Nat → Ideal → Prop
  | 0, _ => True
  | n + 1, T => ∃ A G, Cont G ∧ T = cpi A G ∧ ∀ y, ChurchTele n (G y)

theorem appSpine_append (f : Ideal) :
    ∀ (args args' : List Ideal), appSpine f (args ++ args') = appSpine (appSpine f args) args'
  | [], _ => rfl
  | a :: as, args' => appSpine_append (app f a) as args'

theorem instPi_append :
    ∀ (T : Ideal) (args args' : List Ideal), instPi T (args ++ args') = instPi (instPi T args) args'
  | _, [], _ => rfl
  | T, y :: ys, args' => instPi_append (fam .pi T (projT (dom .pi T) y)) ys args'

theorem spineTyped_append :
    ∀ {T : Ideal} {args args' : List Ideal},
      SpineTyped T (args ++ args') ↔ SpineTyped T args ∧ SpineTyped (instPi T args) args'
  | _, [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | T, y :: ys, args' => by
      have ih := spineTyped_append (T := fam .pi T (projT (dom .pi T) y)) (args := ys)
        (args' := args')
      constructor
      · rintro ⟨hy, h⟩
        exact ⟨⟨hy, (ih.1 h).1⟩, (ih.1 h).2⟩
      · rintro ⟨⟨hy, h⟩, h'⟩
        exact ⟨hy, ih.2 ⟨h, h'⟩⟩

/-- The projected arguments of a spine with spine facts are its arguments. -/
theorem projArgs_of_spineTyped :
    ∀ {T : Ideal} {args : List Ideal}, SpineTyped T args → projArgs T args = args
  | _, [], _ => rfl
  | _, _ :: _, ⟨hy, hys⟩ => by
      rw [projArgs, projArgs_of_spineTyped hys, hy]

/-- **Applying a constant that carries its declared type**: the arguments are
projected onto their parameter types, and the value onto the instantiated type. -/
theorem appSpine_projT :
    ∀ {n : Nat} {T : Ideal} (f : Ideal) {args : List Ideal}, ChurchTele n T →
      args.length ≤ n → appSpine (projT T f) args = projT (instPi T args) (appSpine f (projArgs T args))
  | _, _, _, [], _, _ => rfl
  | 0, _, _, _ :: _, _, hlen => absurd hlen (by simp)
  | m + 1, _, f, y :: ys, ⟨A, G, hG, rfl, hrest⟩, hlen => by
      have hlen' : ys.length ≤ m := by simpa using hlen
      simp only [appSpine, instPi, projArgs, dom_cpi, fam_cpi hG, projT_projT, app_projT_cpi hG]
      exact appSpine_projT _ (hrest _) hlen'

/-- **At a spine with spine facts**, a constant that carries its declared type
computes by its function, projected onto the instantiated type. -/
theorem appSpine_churchConst {n : Nat} {T : Ideal} (f : Ideal) {args : List Ideal}
    (hT : ChurchTele n T) (hlen : args.length ≤ n) (spine : SpineTyped T args) :
    appSpine (projT T f) args = projT (instPi T args) (appSpine f args) := by
  rw [appSpine_projT f hT hlen, projArgs_of_spineTyped spine]

/-- **Root validity of a constant that carries its declared type**: at a spine with
spine facts, if its function computes to the contractum and the contractum is an
element of the instantiated type, the constant computes to the contractum. -/
theorem churchConst_root {n : Nat} {T f r : Ideal} {args : List Ideal} (hT : ChurchTele n T)
    (hlen : args.length ≤ n) (spine : SpineTyped T args) (body : appSpine f args = r)
    (right : projT (instPi T args) r = r) : appSpine (projT T f) args = r := by
  rw [appSpine_churchConst f hT hlen spine, body, right]

/-! ## Spine facts under application -/

/-- **Spine facts are preserved by application to an element of the domain**: when
the instantiated type is `cpi A G`, the spine extended by an element of `A` has spine
facts, and its instantiated type is the family's value at the argument. -/
theorem spine_snoc {T a : Ideal} {args : List Ideal} (hG : Cont G) (spine : SpineTyped T args)
    (hT : instPi T args = cpi A G) (ha : projT A a = a) :
    SpineTyped T (args ++ [a]) ∧ instPi T (args ++ [a]) = G a := by
  refine ⟨spineTyped_append.2 ⟨spine, ?_⟩, ?_⟩
  · rw [hT]
    exact ⟨by rw [dom_cpi, ha], trivial⟩
  · rw [instPi_append, hT]
    show fam .pi (cpi A G) (projT (dom .pi (cpi A G)) a) = G a
    rw [dom_cpi, fam_cpi hG, projT_projT, ha]

/-- **The semantic application rule at a spine**: an element of the instantiated type
`cpi A G`, applied to an element of `A`, is an element of the type instantiated at
the extended spine. -/
theorem spine_app {T a f : Ideal} {args : List Ideal} (hG : Cont G) (spine : SpineTyped T args)
    (hT : instPi T args = cpi A G) (ha : projT A a = a) (hf : projT (instPi T args) f = f) :
    projT (instPi T (args ++ [a])) (app f a) = app f a := by
  rw [(spine_snoc hG spine hT ha).2]
  rw [hT] at hf
  exact semTyped_app hG hf ha

/-- The instantiated type depends on the last argument only through its projection
onto its parameter type. -/
theorem instPi_snoc_congr {T a a' : Ideal} {args : List Ideal}
    (h : projT (dom .pi (instPi T args)) a = projT (dom .pi (instPi T args)) a') :
    instPi T (args ++ [a]) = instPi T (args ++ [a']) := by
  rw [instPi_append, instPi_append]
  show fam .pi _ (projT _ a) = fam .pi _ (projT _ a')
  rw [h]

/-- **The spine facts** of a spine of a constant of declared type `D` at the type `τ`:
`τ` is `D` instantiated at the arguments, and each argument is an element of its
parameter type. -/
def SpineFacts (D : Ideal) (args : List Ideal) (τ : Ideal) : Prop :=
  instPi D args = τ ∧ SpineTyped D args

/-- A constant has spine facts at its declared type. -/
theorem SpineFacts.nil (D : Ideal) : SpineFacts D [] D := ⟨rfl, trivial⟩

/-- **Spine facts are preserved by application to an element of the domain**: if a
spine has spine facts at `cpi A G` and its value `f` is an element of `cpi A G`,
then, for every element `a` of `A`, the extended spine has spine facts at `G a`,
and the application is an element of `G a`. -/
theorem SpineFacts.snoc {D a f : Ideal} {args : List Ideal} (hG : Cont G)
    (facts : SpineFacts D args (cpi A G)) (ha : projT A a = a) (hf : projT (cpi A G) f = f) :
    SpineFacts D (args ++ [a]) (G a) ∧ projT (G a) (app f a) = app f a := by
  obtain ⟨spine, inst⟩ := spine_snoc hG facts.2 facts.1 ha
  exact ⟨⟨inst, spine⟩, semTyped_app hG hf ha⟩

/-- Related arguments, those with one projection onto the domain, give the extended
spine one instantiated type. -/
theorem SpineFacts.snoc_congr {D a a' τ : Ideal} {args : List Ideal}
    (facts : SpineFacts D args τ) (h : projT (dom .pi τ) a = projT (dom .pi τ) a') :
    instPi D (args ++ [a]) = instPi D (args ++ [a']) :=
  instPi_snoc_congr (by rw [facts.1]; exact h)

/-- Spine facts depend on the type only through its value: they are kept by
conversion. -/
theorem SpineFacts.conv {D τ τ' : Ideal} {args : List Ideal} (facts : SpineFacts D args τ)
    (e : τ = τ') : SpineFacts D args τ' :=
  e ▸ facts

end Ideal

/-! ## Continuity of the operations that carry their domain -/

open Ideal

namespace EnvCont

variable {n : Nat}

/-- A dependent type whose family sees its argument through the projection onto its
domain depends continuously on the environment. -/
theorem cformer (k : Kind) {A : Env n → Ideal} {B : Env (n + 1) → Ideal} (hA : EnvCont A)
    (hB : EnvCont B) :
    EnvCont fun ρ => former k (A ρ) fun X => B (Env.cons (projT (A ρ) (principal X)) ρ) := by
  refine EnvCont.of_closure (P := fun ρ t => t = .tag k ∨ (∃ d, t = .arg k 0 [] d ∧ (A ρ).Mem d) ∨
      ∃ D X Y, t = .fn k D X Y ∧ Ideal.Below D (A ρ) ∧
        Ideal.Below Y (B (Env.cons (projT (A ρ) (principal X)) ρ))) ?_ ?_
  · intro ρ ρ' h t ht
    rcases ht with rfl | ⟨d, rfl, hd⟩ | ⟨D, X, Y, rfl, hD, hY⟩
    · exact .inl rfl
    · exact .inr (.inl ⟨d, rfl, hA.mono h d hd⟩)
    · exact .inr (.inr ⟨D, X, Y, rfl, hD.mono (hA.mono h),
        hY.mono (hB.mono (Env.Le.cons (projT_mono_type (hA.mono h) _) h))⟩)
  · intro ρ t ht
    rcases ht with rfl | ⟨d, rfl, hd⟩ | ⟨D, X, Y, rfl, hD, hY⟩
    · exact ⟨fun _ => [], Approximates.nil ρ, .inl rfl⟩
    · obtain ⟨Z, hZ, hd'⟩ := hA.finite hd
      exact ⟨Z, hZ, .inr (.inl ⟨d, rfl, hd'⟩)⟩
    · have hK : EnvCont fun ρ => B (Env.cons (projT (A ρ) (principal X)) ρ) :=
        hB.subst_cons (EnvCont.comp (cont_projT_type (principal X)) hA)
      obtain ⟨Z₁, h₁, hD'⟩ := hA.below hD
      obtain ⟨Z₂, h₂, hY'⟩ := hK.below hY
      exact ⟨approxJoin Z₁ Z₂, h₁.join h₂, .inr (.inr ⟨D, X, Y, rfl,
        hD'.mono (hA.mono (approx_le_join_left Z₁ Z₂)),
        hY'.mono (hK.mono (approx_le_join_right Z₁ Z₂))⟩)⟩

/-- A function that sees its argument through the projection onto its domain
depends continuously on the environment. -/
theorem clam {A : Env n → Ideal} {B : Env (n + 1) → Ideal} (hA : EnvCont A) (hB : EnvCont B) :
    EnvCont fun ρ => lam fun X => B (Env.cons (projT (A ρ) (principal X)) ρ) := by
  refine EnvCont.of_closure (P := fun ρ t => ∃ X Y, t = .fn .lam [] X Y ∧
      Ideal.Below Y (B (Env.cons (projT (A ρ) (principal X)) ρ))) ?_ ?_
  · intro ρ ρ' h t ⟨X, Y, e, hY⟩
    exact ⟨X, Y, e, hY.mono (hB.mono (Env.Le.cons (projT_mono_type (hA.mono h) _) h))⟩
  · intro ρ t ⟨X, Y, e, hY⟩
    have hK : EnvCont fun ρ => B (Env.cons (projT (A ρ) (principal X)) ρ) :=
      hB.subst_cons (EnvCont.comp (cont_projT_type (principal X)) hA)
    obtain ⟨Z, hZ, hY'⟩ := hK.below hY
    exact ⟨Z, hZ, X, Y, e, hY'⟩

/-- An identity type depends continuously on the environment. -/
theorem ident {A I J : Env n → Ideal} (hA : EnvCont A) (hI : EnvCont I) (hJ : EnvCont J) :
    EnvCont fun ρ => Ideal.ident (A ρ) (I ρ) (J ρ) := by
  refine EnvCont.of_closure (P := fun ρ s => s = .tag .ident ∨
      (∃ d, s = .arg .ident 0 [] d ∧ (A ρ).Mem d) ∨
      (∃ C r, s = .arg .ident 1 C r ∧ Ideal.Below C (A ρ) ∧ (I ρ).Mem r) ∨
      ∃ C r, s = .arg .ident 2 C r ∧ Ideal.Below C (A ρ) ∧ (J ρ).Mem r) ?_ ?_
  · intro ρ ρ' h s hs
    rcases hs with rfl | ⟨d, rfl, hd⟩ | ⟨C, r, rfl, hC, hr⟩ | ⟨C, r, rfl, hC, hr⟩
    · exact .inl rfl
    · exact .inr (.inl ⟨d, rfl, hA.mono h d hd⟩)
    · exact .inr (.inr (.inl ⟨C, r, rfl, hC.mono (hA.mono h), hI.mono h r hr⟩))
    · exact .inr (.inr (.inr ⟨C, r, rfl, hC.mono (hA.mono h), hJ.mono h r hr⟩))
  · intro ρ s hs
    rcases hs with rfl | ⟨d, rfl, hd⟩ | ⟨C, r, rfl, hC, hr⟩ | ⟨C, r, rfl, hC, hr⟩
    · exact ⟨fun _ => [], Approximates.nil ρ, .inl rfl⟩
    · obtain ⟨X, hX, hd'⟩ := hA.finite hd
      exact ⟨X, hX, .inr (.inl ⟨d, rfl, hd'⟩)⟩
    · obtain ⟨X₁, h₁, hC'⟩ := hA.below hC
      obtain ⟨X₂, h₂, hr'⟩ := hI.finite hr
      exact ⟨approxJoin X₁ X₂, h₁.join h₂, .inr (.inr (.inl ⟨C, r, rfl,
        hC'.mono (hA.mono (approx_le_join_left X₁ X₂)), hI.mono (approx_le_join_right X₁ X₂) r hr'⟩))⟩
    · obtain ⟨X₁, h₁, hC'⟩ := hA.below hC
      obtain ⟨X₂, h₂, hr'⟩ := hJ.finite hr
      exact ⟨approxJoin X₁ X₂, h₁.join h₂, .inr (.inr (.inr ⟨C, r, rfl,
        hC'.mono (hA.mono (approx_le_join_left X₁ X₂)), hJ.mono (approx_le_join_right X₁ X₂) r hr'⟩))⟩

end EnvCont

/-! ## The interpretation of annotated terms -/

variable {Head : Type}

/-- The empty environment. -/
def Env.nil : Env 0 := fun i => i.elim0

/-- The interpretation of annotated terms: dependent types and abstractions see
their bound variable through the projection onto its annotated type. -/
def cinterp (Rd : Reading Head) : {n : Nat} → CTm Head n → Env n → Ideal
  | _, .var i, ρ => ρ i
  | _, .const c, _ => Rd.const c
  | _, .head h, _ => principal (Rd.head h)
  | _, .pi A B, ρ => cpi (cinterp Rd A ρ) fun y => cinterp Rd B (Env.cons y ρ)
  | _, .sigma A B, ρ => csigma (cinterp Rd A ρ) fun y => cinterp Rd B (Env.cons y ρ)
  | _, .id A a b, ρ => Ideal.ident (cinterp Rd A ρ) (cinterp Rd a ρ) (cinterp Rd b ρ)
  | _, .lam A b, ρ => clam (cinterp Rd A ρ) fun y => cinterp Rd b (Env.cons y ρ)
  | _, .app f a, ρ => Ideal.app (cinterp Rd f ρ) (cinterp Rd a ρ)
  | _, .pair a b, ρ => Ideal.pair (cinterp Rd a ρ) (cinterp Rd b ρ)
  | _, .fst p, ρ => Ideal.fst (cinterp Rd p ρ)
  | _, .snd p, ρ => Ideal.snd (cinterp Rd p ρ)
  | _, .refl a, ρ => Ideal.refl (cinterp Rd a ρ)

/-- **The interpretation is continuous in the environment** (and so monotone). -/
theorem cinterp_envCont (Rd : Reading Head) {n : Nat} (M : CTm Head n) :
    EnvCont (cinterp Rd M) := by
  induction M with
  | var i => exact EnvCont.var i
  | const c => exact EnvCont.const _
  | head h => exact EnvCont.const _
  | pi A B ihA ihB => exact EnvCont.cformer .pi ihA ihB
  | sigma A B ihA ihB => exact EnvCont.cformer .sigma ihA ihB
  | id A a b ihA iha ihb => exact EnvCont.ident ihA iha ihb
  | lam A b ihA ihb => exact EnvCont.clam ihA ihb
  | app f a ihf iha => exact EnvCont.comp₂ cont₂_app ihf iha
  | pair a b iha ihb => exact EnvCont.comp₂ cont₂_pair iha ihb
  | fst p ih => exact EnvCont.comp cont_fst ih
  | snd p ih => exact EnvCont.comp cont_snd ih
  | refl a ih => exact EnvCont.comp cont_refl ih

/-- The family of a binder is continuous in the bound variable. -/
theorem cinterp_cont_cons (Rd : Reading Head) {n : Nat} (B : CTm Head (n + 1)) (ρ : Env n) :
    Cont fun y => cinterp Rd B (Env.cons y ρ) :=
  (cinterp_envCont Rd B).cons_left ρ

theorem dom_cinterp_pi (Rd : Reading Head) {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1))
    (ρ : Env n) : dom .pi (cinterp Rd (.pi A B) ρ) = cinterp Rd A ρ :=
  dom_cpi _ _

/-- The family of the interpretation of `Π A B` at `y` is the interpretation of `B`
at the projection of `y` onto the interpretation of `A`. -/
theorem fam_cinterp_pi (Rd : Reading Head) {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1))
    (ρ : Env n) (y : Ideal) :
    fam .pi (cinterp Rd (.pi A B) ρ) y = cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) y) ρ) :=
  fam_cpi (cinterp_cont_cons Rd B ρ) y

theorem instPi_cinterp_pi (Rd : Reading Head) {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1))
    (ρ : Env n) (y : Ideal) (ys : List Ideal) :
    instPi (cinterp Rd (.pi A B) ρ) (y :: ys) =
      instPi (cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) y) ρ)) ys := by
  show instPi (fam .pi _ (projT (dom .pi _) y)) ys = _
  rw [dom_cinterp_pi, fam_cinterp_pi, projT_projT]

/-- Applying the projection onto the interpretation of `Π A B`. -/
theorem app_projT_cinterp_pi (Rd : Reading Head) {n : Nat} (A : CTm Head n)
    (B : CTm Head (n + 1)) (ρ : Env n) (f y : Ideal) :
    app (projT (cinterp Rd (.pi A B) ρ) f) y =
      projT (cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) y) ρ))
        (app f (projT (cinterp Rd A ρ) y)) :=
  app_projT_cpi (cinterp_cont_cons Rd B ρ) f y

theorem instPi_cinterp_pi_of (Rd : Reading Head) {n : Nat} {A : CTm Head n}
    {B : CTm Head (n + 1)} {ρ : Env n} {y y' : Ideal} (ys : List Ideal)
    (h : projT (cinterp Rd A ρ) y = y') :
    instPi (cinterp Rd (.pi A B) ρ) (y :: ys) = instPi (cinterp Rd B (Env.cons y' ρ)) ys := by
  rw [instPi_cinterp_pi, h]

theorem projArgs_cinterp_pi (Rd : Reading Head) {n : Nat} (A : CTm Head n)
    (B : CTm Head (n + 1)) (ρ : Env n) (y : Ideal) (ys : List Ideal) :
    projArgs (cinterp Rd (.pi A B) ρ) (y :: ys) =
      projT (cinterp Rd A ρ) y ::
        projArgs (cinterp Rd B (Env.cons (projT (cinterp Rd A ρ) y) ρ)) ys := by
  show projT (dom .pi _) y :: projArgs (fam .pi _ (projT (dom .pi _) y)) ys = _
  rw [dom_cinterp_pi, fam_cinterp_pi, projT_projT]

theorem projArgs_cinterp_pi_of (Rd : Reading Head) {n : Nat} {A : CTm Head n}
    {B : CTm Head (n + 1)} {ρ : Env n} {y y' : Ideal} (ys : List Ideal)
    (h : projT (cinterp Rd A ρ) y = y') :
    projArgs (cinterp Rd (.pi A B) ρ) (y :: ys) = y' :: projArgs (cinterp Rd B (Env.cons y' ρ)) ys := by
  rw [projArgs_cinterp_pi, h]

/-- Spine facts at the interpretation of `Π A B`: the first argument is an element of
the interpretation of `A`, and the rest have spine facts at `B` there. -/
theorem spineTyped_cinterp_pi (Rd : Reading Head) {n : Nat} (A : CTm Head n)
    (B : CTm Head (n + 1)) (ρ : Env n) (y : Ideal) (ys : List Ideal) :
    SpineTyped (cinterp Rd (.pi A B) ρ) (y :: ys) ↔
      projT (cinterp Rd A ρ) y = y ∧ SpineTyped (cinterp Rd B (Env.cons y ρ)) ys := by
  show (projT (dom .pi _) y = y ∧ SpineTyped (fam .pi _ (projT (dom .pi _) y)) ys) ↔ _
  rw [dom_cinterp_pi, fam_cinterp_pi, projT_projT]
  constructor
  · rintro ⟨hy, h⟩
    rw [hy] at h
    exact ⟨hy, h⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    rw [hy]
    exact h

/-- The number of nested dependent function types of an annotated term. -/
def piArity : {n : Nat} → CTm Head n → Nat
  | _, .pi _ B => piArity B + 1
  | _, .var _ => 0
  | _, .const _ => 0
  | _, .head _ => 0
  | _, .sigma _ _ => 0
  | _, .id _ _ _ => 0
  | _, .lam _ _ => 0
  | _, .app _ _ => 0
  | _, .pair _ _ => 0
  | _, .fst _ => 0
  | _, .snd _ => 0
  | _, .refl _ => 0

/-- **The interpretation of an annotated dependent function type is a Church
telescope.** -/
theorem churchTele_cinterp (Rd : Reading Head) :
    ∀ {n : Nat} (M : CTm Head n) (ρ : Env n), ChurchTele (piArity M) (cinterp Rd M ρ)
  | _, .pi A B, ρ => ⟨cinterp Rd A ρ, fun y => cinterp Rd B (Env.cons y ρ),
      cinterp_cont_cons Rd B ρ, rfl, fun y => churchTele_cinterp Rd B (Env.cons y ρ)⟩
  | _, .var _, _ => trivial
  | _, .const _, _ => trivial
  | _, .head _, _ => trivial
  | _, .sigma _ _, _ => trivial
  | _, .id _ _ _, _ => trivial
  | _, .lam _ _, _ => trivial
  | _, .app _ _, _ => trivial
  | _, .pair _ _, _ => trivial
  | _, .fst _, _ => trivial
  | _, .snd _, _ => trivial
  | _, .refl _, _ => trivial

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
