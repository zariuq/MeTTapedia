import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction

/-!
# Generic equality for the normalization model

The model is built over three relations: convertible types, convertible terms
at a type, and convertible head spines. The laws below are what the model uses.
Two instances matter: typed equality itself, which gives injectivity and
preservation, and the conversion algorithm, which gives its completeness.

Head spines are variables and constants followed by applications and
projections. Their relation does not claim the spine is stuck; the model asks
for neutrality separately. That matches the algorithm, which compares a spine
headed by a computing constant, such as a stuck identity elimination, argument
by argument.

A function in weak-head normal form is a lambda, a neutral term, or a constant
spine that still lacks arguments; a pair in weak-head normal form is a pair or
a neutral term.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- The weak-head normal forms of functions. -/
def IsFun (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  (∃ body, t = .lam body) ∨ Neutral roles t ∨
    ∃ c args arity, (roles c = .constructor arity ∨ ∃ scrutinee, roles c = .computes arity scrutinee) ∧
      args.length < arity ∧ t = appSpine (.const c) args

/-- The weak-head normal forms of pairs. -/
def IsPair (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  (∃ a b, t = .pair a b) ∨ Neutral roles t

/-- The weak-head normal forms of types: formers, heads, neutral types and the
type constants of inductive types. -/
def IsTypeForm (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  (∃ h, t = .head h) ∨ (∃ A B, t = .pi A B) ∨ (∃ A B, t = .sigma A B) ∨
    (∃ A a b, t = .id A a b) ∨ Neutral roles t ∨
    ∃ T constructors, roles T = .inductive constructors ∧ t = .const T

theorem IsTypeForm.rename {roles : Roles Head} {n m : Nat} {t : Tm Head n}
    (form : IsTypeForm roles t) (ρ : Ren n m) : IsTypeForm roles (Presentation.rename ρ t) := by
  rcases form with ⟨h, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, a, b, rfl⟩ | neutral |
    ⟨T, constructors, role, rfl⟩
  · exact .inl ⟨h, rfl⟩
  · exact .inr (.inl ⟨_, _, rfl⟩)
  · exact .inr (.inr (.inl ⟨_, _, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl (neutral.rename ρ)))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨T, constructors, role, rfl⟩))))

theorem IsFun.rename {roles : Roles Head} {n m : Nat} {t : Tm Head n}
    (function : IsFun roles t) (ρ : Ren n m) : IsFun roles (Presentation.rename ρ t) := by
  rcases function with ⟨body, rfl⟩ | neutral | ⟨c, args, arity, role, short, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl (neutral.rename ρ))
  · exact .inr (.inr ⟨c, args.map (Presentation.rename ρ), arity, role, by simpa using short,
      by simp [rename_appSpine, Presentation.rename]⟩)

theorem IsPair.rename {roles : Roles Head} {n m : Nat} {t : Tm Head n}
    (pair : IsPair roles t) (ρ : Ren n m) : IsPair roles (Presentation.rename ρ t) := by
  rcases pair with ⟨a, b, rfl⟩ | neutral
  · exact .inl ⟨_, _, rfl⟩
  · exact .inr (neutral.rename ρ)

/-- The head spines whose comparison is a comparison of values: neutral terms,
constructor spines and the type constants of inductive types. -/
def Liftable (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  Neutral roles t ∨ (∃ k arity args, roles k = .constructor arity ∧ t = appSpine (.const k) args) ∨
    ∃ T constructors, roles T = .inductive constructors ∧ t = .const T

/-- Three relations over which the model is built. -/
structure GenericEquality (Head : Type) where
  /-- `Γ ⊢ A ≅ B`: convertible types. -/
  convTy : ∀ {n : Nat}, Ctx Head n → Tm Head n → Tm Head n → Prop
  /-- `Γ ⊢ t ≅ u : A`: convertible terms. -/
  convTm : ∀ {n : Nat}, Ctx Head n → Tm Head n → Tm Head n → Tm Head n → Prop
  /-- `Γ ⊢ t ~ u : A`: convertible head spines. -/
  convNe : ∀ {n : Nat}, Ctx Head n → Tm Head n → Tm Head n → Tm Head n → Prop

/-- The laws the model uses. -/
structure GenericEquality.Laws (E : GenericEquality Head) (R : Rules Head)
    (roles : Roles Head) : Prop where
  convTy_sound : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n},
    E.convTy Γ A B → TypeEq R Γ A B
  convTm_sound : ∀ {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n},
    E.convTm Γ t u A → Equal R Γ t u A
  convNe_sound : ∀ {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n},
    E.convNe Γ t u A → Equal R Γ t u A
  convTy_of_convTm : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head},
    E.convTm Γ A B (.head u) → R.isUniverse u → E.convTy Γ A B
  convTm_of_convNe : ∀ {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n},
    Liftable roles t → Liftable roles u → E.convNe Γ t u A → E.convTm Γ t u A
  convTy_symm : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n},
    E.convTy Γ A B → E.convTy Γ B A
  convTy_trans : ∀ {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n},
    E.convTy Γ A B → E.convTy Γ B C → E.convTy Γ A C
  convTm_symm : ∀ {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n},
    E.convTm Γ t u A → E.convTm Γ u t A
  convTm_trans : ∀ {n : Nat} {Γ : Ctx Head n} {t u v A : Tm Head n},
    E.convTm Γ t u A → E.convTm Γ u v A → E.convTm Γ t v A
  convNe_symm : ∀ {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n},
    E.convNe Γ t u A → E.convNe Γ u t A
  convNe_trans : ∀ {n : Nat} {Γ : Ctx Head n} {t u v A : Tm Head n},
    E.convNe Γ t u A → E.convNe Γ u v A → E.convNe Γ t v A
  convTm_cumul : ∀ {n : Nat} {Γ : Ctx Head n} {t u : Tm Head n} {v w : Head},
    E.convTm Γ t u (.head v) → R.cumulative v w → E.convTm Γ t u (.head w)
  convNe_cumul : ∀ {n : Nat} {Γ : Ctx Head n} {t u : Tm Head n} {v w : Head},
    E.convNe Γ t u (.head v) → R.cumulative v w → E.convNe Γ t u (.head w)
  convTm_below : ∀ {n : Nat} {Γ : Ctx Head n} {t u A B : Tm Head n},
    E.convTm Γ t u A → Below R Γ A B → E.convTm Γ t u B
  convNe_below : ∀ {n : Nat} {Γ : Ctx Head n} {t u A B : Tm Head n},
    E.convNe Γ t u A → Below R Γ A B → E.convNe Γ t u B
  convTm_conv : ∀ {n : Nat} {Γ : Ctx Head n} {t u A B : Tm Head n},
    E.convTm Γ t u A → TypeEq R Γ A B → E.convTm Γ t u B
  convNe_conv : ∀ {n : Nat} {Γ : Ctx Head n} {t u A B : Tm Head n},
    E.convNe Γ t u A → TypeEq R Γ A B → E.convNe Γ t u B
  convTy_rename : ∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {A B : Tm Head n}, CtxRen Γ Δ ρ → CtxFormed R Δ → E.convTy Γ A B →
    E.convTy Δ (Presentation.rename ρ A) (Presentation.rename ρ B)
  convTm_rename : ∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {t u A : Tm Head n}, CtxRen Γ Δ ρ → CtxFormed R Δ → E.convTm Γ t u A →
    E.convTm Δ (Presentation.rename ρ t) (Presentation.rename ρ u) (Presentation.rename ρ A)
  convNe_rename : ∀ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {t u A : Tm Head n}, CtxRen Γ Δ ρ → CtxFormed R Δ → E.convNe Γ t u A →
    E.convNe Δ (Presentation.rename ρ t) (Presentation.rename ρ u) (Presentation.rename ρ A)
  convTy_expand : ∀ {n : Nat} {Γ : Ctx Head n} {A A' B B' : Tm Head n},
    RedTy R roles Γ A A' → RedTy R roles Γ B B' → E.convTy Γ A' B' → E.convTy Γ A B
  convTm_expand : ∀ {n : Nat} {Γ : Ctx Head n} {t t' u u' A : Tm Head n},
    RedTm R roles Γ t t' A → RedTm R roles Γ u u' A → E.convTm Γ t' u' A →
    E.convTm Γ t u A
  convTy_head : ∀ {n : Nat} {Γ : Ctx Head n} {h h' u : Head},
    (h = h' ∨ R.headEq h h') → Typed R Γ (.head h) (.head u) →
    Typed R Γ (.head h') (.head u) → R.isUniverse u → E.convTy Γ (.head h) (.head h')
  convTm_head : ∀ {n : Nat} {Γ : Ctx Head n} {h h' u : Head},
    (h = h' ∨ R.headEq h h') → Typed R Γ (.head h) (.head u) →
    Typed R Γ (.head h') (.head u) → R.isUniverse u →
    E.convTm Γ (.head h) (.head h') (.head u)
  convTy_pi : ∀ {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)},
    IsType R Γ A → E.convTy Γ A A' → E.convTy (.snoc Γ A) B B' →
    E.convTy Γ (.pi A B) (.pi A' B')
  convTy_sigma : ∀ {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)},
    IsType R Γ A → E.convTy Γ A A' → E.convTy (.snoc Γ A) B B' →
    E.convTy Γ (.sigma A B) (.sigma A' B')
  convTy_id : ∀ {n : Nat} {Γ : Ctx Head n} {A A' x x' y y' : Tm Head n},
    E.convTy Γ A A' → E.convTm Γ x x' A → E.convTm Γ y y' A →
    E.convTy Γ (.id A x y) (.id A' x' y')
  convTm_pi : ∀ {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    {u v w : Head}, Typed R Γ A (.head u) → R.isUniverse u →
    E.convTm Γ A A' (.head u) → E.convTm (.snoc Γ A) B B' (.head v) → R.isUniverse v →
    R.join u v w → E.convTm Γ (.pi A B) (.pi A' B') (.head w)
  convTm_sigma : ∀ {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    {u v w : Head}, Typed R Γ A (.head u) → R.isUniverse u →
    E.convTm Γ A A' (.head u) → E.convTm (.snoc Γ A) B B' (.head v) → R.isUniverse v →
    R.join u v w → E.convTm Γ (.sigma A B) (.sigma A' B') (.head w)
  convTm_id : ∀ {n : Nat} {Γ : Ctx Head n} {A A' x x' y y' : Tm Head n} {u : Head},
    E.convTm Γ A A' (.head u) → R.isUniverse u → E.convTm Γ x x' A →
    E.convTm Γ y y' A → E.convTm Γ (.id A x y) (.id A' x' y') (.head u)
  convTm_etaPi : ∀ {n : Nat} {Γ : Ctx Head n} {f g A : Tm Head n} {B : Tm Head (n + 1)},
    IsType R Γ A → IsType R (.snoc Γ A) B →
    Typed R Γ f (.pi A B) → IsFun roles f → Typed R Γ g (.pi A B) → IsFun roles g →
    E.convTm (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk g) (.var 0)) B →
    E.convTm Γ f g (.pi A B)
  convTm_etaSigma : ∀ {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n}
    {B : Tm Head (n + 1)},
    IsType R Γ A → IsType R (.snoc Γ A) B →
    Typed R Γ p (.sigma A B) → IsPair roles p → Typed R Γ q (.sigma A B) → IsPair roles q →
    E.convTm Γ (.fst p) (.fst q) A → E.convTm Γ (.snd p) (.snd q) (inst0 (.fst p) B) →
    E.convTm Γ p q (.sigma A B)
  convTm_refl : ∀ {n : Nat} {Γ : Ctx Head n} {x x' A : Tm Head n},
    E.convTm Γ x x' A → E.convTm Γ (.refl x) (.refl x') (.id A x x)
  convNe_var : ∀ {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (i : Fin n),
    Typed R Γ (.var i) A → E.convNe Γ (.var i) (.var i) A
  convNe_const : ∀ {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (c : DeclName),
    Typed R Γ (.const c) A → E.convNe Γ (.const c) (.const c) A
  convNe_app : ∀ {n : Nat} {Γ : Ctx Head n} {f g a b A : Tm Head n}
    {B : Tm Head (n + 1)}, E.convNe Γ f g (.pi A B) → E.convTm Γ a b A →
    E.convNe Γ (.app f a) (.app g b) (inst0 a B)
  convNe_fst : ∀ {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)},
    E.convNe Γ p q (.sigma A B) → E.convNe Γ (.fst p) (.fst q) A
  convNe_snd : ∀ {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n} {B : Tm Head (n + 1)},
    E.convNe Γ p q (.sigma A B) → E.convNe Γ (.snd p) (.snd q) (inst0 (.fst p) B)

/-! ## The declarative instance -/

theorem headEquality {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {h h' : Head}
    {A : Tm Head n} (same : h = h' ∨ R.headEq h h') (typing : Typed R Γ (.head h) A)
    (typing' : Typed R Γ (.head h') A) : Equal R Γ (.head h) (.head h') A := by
  rcases same with rfl | equal
  · exact .refl typing
  · exact .headEq equal typing typing'


/-- Typed equality as a generic equality. -/
def declarative (R : Rules Head) : GenericEquality Head where
  convTy := fun Γ A B => TypeEq R Γ A B
  convTm := fun Γ t u A => Equal R Γ t u A
  convNe := fun Γ t u A => Equal R Γ t u A

theorem declarative_laws {R : Rules Head} (roles : Roles Head) (levels : LevelModel R L) :
    (declarative R).Laws R roles where
  convTy_sound := id
  convTm_sound := id
  convNe_sound := id
  convTy_of_convTm := fun equal hu => ⟨_, hu, equal⟩
  convTm_of_convNe := fun _ _ equal => equal
  convTy_symm := TypeEq.symm
  convTy_trans := TypeEq.trans levels
  convTm_symm := Derivable.symm
  convTm_trans := Derivable.trans
  convNe_symm := Derivable.symm
  convNe_trans := Derivable.trans
  convTm_cumul := Derivable.cumulEq
  convNe_cumul := Derivable.cumulEq
  convTm_below := Derivable.subEq
  convNe_below := Derivable.subEq
  convTm_conv := Equal.convType
  convNe_conv := Equal.convType
  convTy_rename := fun compatible _ equal => equal.rename compatible
  convTm_rename := fun compatible _ equal => equal.rename compatible
  convNe_rename := fun compatible _ equal => equal.rename compatible
  convTy_expand := fun redA redB equal =>
    TypeEq.trans levels redA.typeEq (TypeEq.trans levels equal redB.typeEq.symm)
  convTm_expand := fun redT redU equal =>
    .trans redT.equal (.trans equal (.symm redU.equal))
  convTy_head := fun same typing typing' hu =>
    ⟨_, hu, headEquality same typing typing'⟩
  convTm_head := fun same typing typing' _ => headEquality same typing typing'
  convTy_pi := fun {_ _ A A' B B'} formed equalA equalB => by
    obtain ⟨u, hu, eA⟩ := equalA
    obtain ⟨v, hv, eB⟩ := equalB
    obtain ⟨w, join⟩ := levels.join_exists hu hv
    exact ⟨w, (levels.join_level join).1, .piCong eA hu eB hv join⟩
  convTy_sigma := fun {_ _ A A' B B'} formed equalA equalB => by
    obtain ⟨u, hu, eA⟩ := equalA
    obtain ⟨v, hv, eB⟩ := equalB
    obtain ⟨w, join⟩ := levels.join_exists hu hv
    exact ⟨w, (levels.join_level join).1, .sigmaCong eA hu eB hv join⟩
  convTy_id := fun equalA equalX equalY => by
    obtain ⟨u, hu, eA⟩ := equalA
    exact ⟨u, hu, .idCong eA hu equalX equalY⟩
  convTm_pi := fun _ hu eA eB hv join => .piCong eA hu eB hv join
  convTm_sigma := fun _ hu eA eB hv join => .sigmaCong eA hu eB hv join
  convTm_id := fun eA hu eX eY => .idCong eA hu eX eY
  convTm_etaPi := fun _ _ tf _ tg _ body => .etaPi tf tg body
  convTm_etaSigma := fun _ _ tp _ tq _ first second => .etaSigma tp tq first second
  convTm_refl := Derivable.reflCong
  convNe_var := fun _ typing => .refl typing
  convNe_const := fun _ typing => .refl typing
  convNe_app := Derivable.appCong
  convNe_fst := Derivable.fstCong
  convNe_snd := Derivable.sndCong

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
