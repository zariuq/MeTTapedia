import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelation

/-!
# The partial-equivalence and conversion laws of the witness-indexed relation

For a token `t` of a term witness typed at a compact type witness `a`, and for a
type token typed at the universe:

* **conversion** (`RT.conv_iff`): terms are related at `A` as far as `t` observes
  iff they are related at `B`, when `A` and `B` are related as types as far as
  every token of `a` observes and are equal as types;
* **symmetry** and **transitivity** of the type relation (`RT.symm_ty`,
  `RT.trans_ty`), and of the term relation at a type related to itself as far as
  `a` observes (`RT.symm`, `RT.trans`).

The five laws are proved together, by induction on the depth of the token. At a
dependent function type, conversion transports the arguments along the domains
and the values along the families; symmetry and transitivity of a family entry
transport the arguments along the domains, which is conversion at a shallower
token. At an identity type, conversion reads the endpoint relation off the type
witness, whose endpoint tokens entail the point of a typed reflexivity token.

At a dependent pair type `Σ D E`, the second projections of two terms are related at
`E` at the first projection of the left one. Symmetry and transitivity move them to
`E` at the first projection of the other, which is conversion along the family,
related to itself as far as `a` observes; this is why the term laws read the
type's relation at `a`. The first projection's class of terms with a common reduct
is closed under head expansion and head reduction, so conversion reads the
family's relation at one argument.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Normalization (LevelModel HeadSame)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head} {P : ChurchRules R} {K : RigidTypes P}
  {H : HeadReduction P K}

/-! ## Typed tokens -/

section Typing

/-- A typed token of a type kind is a type token. -/
theorem tyTok_univ_of_typeKind {t : Tok} (htk : typeKind t.kind = true) {a : List Tok}
    (ht : TyTok a t) : IsUniv a ∧ TyTok Elem.univ t := by
  cases t with
  | tag k =>
      have hk : k.IsFormer := by cases k <;> trivial
      exact ⟨(tyTok_tag_former hk).1 ht, (tyTok_tag_former hk).2 Elem.isUniv_univ⟩
  | arg k i C s =>
      rcases Decidable.em ((k, i) ∈ argSlots) with hs | hother
      swap
      · exact absurd ht (tyTok_arg_other hother)
      simp only [argSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hu, hC, hs⟩ := (tyTok_dom (.inl rfl)).1 ht
        exact ⟨hu, (tyTok_dom (.inl rfl)).2 ⟨Elem.isUniv_univ, hC, hs⟩⟩
      · obtain ⟨hu, hC, hs⟩ := (tyTok_dom (.inr (.inl rfl))).1 ht
        exact ⟨hu, (tyTok_dom (.inr (.inl rfl))).2 ⟨Elem.isUniv_univ, hC, hs⟩⟩
      · obtain ⟨hu, hC, hs⟩ := (tyTok_dom (.inr (.inr rfl))).1 ht
        exact ⟨hu, (tyTok_dom (.inr (.inr rfl))).2 ⟨Elem.isUniv_univ, hC, hs⟩⟩
      · obtain ⟨hu, hC, hs⟩ := (tyTok_endpoint (.inl rfl)).1 ht
        exact ⟨hu, (tyTok_endpoint (.inl rfl)).2 ⟨Elem.isUniv_univ, hC, hs⟩⟩
      · obtain ⟨hu, hC, hs⟩ := (tyTok_endpoint (.inr rfl)).1 ht
        exact ⟨hu, (tyTok_endpoint (.inr rfl)).2 ⟨Elem.isUniv_univ, hC, hs⟩⟩
      all_goals cases htk
  | fn k C X Y =>
      rcases fn_cases k with hk | rfl | hother
      · obtain ⟨hu, hC, hX, hY⟩ := (tyTok_family hk).1 ht
        exact ⟨hu, (tyTok_family hk).2 ⟨Elem.isUniv_univ, hC, hX, hY⟩⟩
      · cases htk
      · exact absurd ht (tyTok_fn_other hother)

/-- A reflexivity token has a single point component. -/
theorem tyTok_reflPoint_succ {a : List Tok} {i : Nat} {C : List Tok} {t : Tok} :
    ¬ TyTok a (.arg .refl (i + 1) C t) := by
  rw [TyTok]
  · exact id
  all_goals intro h₁ h₂; first | exact Kind.noConfusion h₁ | exact Nat.noConfusion h₂

/-- A successor token has a single predecessor component. -/
theorem tyTok_pred_succ {a : List Tok} {i : Nat} {C : List Tok} {t : Tok} :
    ¬ TyTok a (.arg .succ (i + 1) C t) := by
  rw [TyTok]
  · exact id
  all_goals intro h₁ h₂; first | exact Kind.noConfusion h₁ | exact Nat.noConfusion h₂

/-- A dependent function type token has a single domain component. -/
theorem tyTok_argPi_succ {a : List Tok} {i : Nat} {C : List Tok} {t : Tok} :
    ¬ TyTok a (.arg .pi (i + 1) C t) := by
  rw [TyTok]
  · exact id
  all_goals intro h₁ h₂; first | exact Kind.noConfusion h₁ | exact Nat.noConfusion h₂

/-- A dependent pair type token has a single domain component. -/
theorem tyTok_argSigma_succ {a : List Tok} {i : Nat} {C : List Tok} {t : Tok} :
    ¬ TyTok a (.arg .sigma (i + 1) C t) := by
  rw [TyTok]
  · exact id
  all_goals intro h₁ h₂; first | exact Kind.noConfusion h₁ | exact Nat.noConfusion h₂

/-- An identity type token has a carrier and two endpoint components. -/
theorem tyTok_argIdent_high {a : List Tok} {i : Nat} {C : List Tok} {t : Tok} :
    ¬ TyTok a (.arg .ident (i + 3) C t) := by
  rw [TyTok]
  · exact id
  all_goals intro h₁ h₂; first | exact Kind.noConfusion h₁ | omega

/-- A pair token has two components. -/
theorem tyTok_pair_high {a : List Tok} {i : Nat} {C : List Tok} {t : Tok} :
    ¬ TyTok a (.arg .pair (i + 2) C t) := by
  rw [TyTok]
  · exact id
  all_goals intro h₁ h₂; first | exact Kind.noConfusion h₁ | omega

/-- The carrier witnesses of an identity-type witness are types. -/
theorem ty_args_ident {a : List Tok} (ha : Ty a Elem.univ) : Ty (args .ident 0 a) Elem.univ := by
  intro s hs
  rcases mem_args_iff.1 hs with ⟨C, hC⟩ | ⟨-, t, ht, htk, hd⟩
  · exact ((tyTok_dom (.inr (.inr rfl))).1 (ha _ hC)).2.2
  · cases t with
    | tag => cases hd
    | arg k i C d =>
        change k = .ident at htk
        subst htk
        change s ∈ C at hd
        have h := ha _ ht
        match i, h with
        | 0, h =>
            obtain ⟨-, rfl, -⟩ := (tyTok_dom (.inr (.inr rfl))).1 h
            cases hd
        | 1, h => exact ((tyTok_endpoint (.inl rfl)).1 h).2.1 s hd
        | 2, h => exact ((tyTok_endpoint (.inr rfl)).1 h).2.1 s hd
        | i + 3, h => exact absurd h (tyTok_arg_other (by simp [argSlots]))
    | fn k C X Y =>
        change k = .ident at htk
        subst htk
        exact absurd (ha _ ht) (tyTok_fn_other (by simp))

end Typing

/-! ## A type related to itself -/

section Self

variable {n : Nat} {Γ : CCtx Head n}

/-- A type related to itself at a witness with the tag of dependent function types
has, at the dependent function type it reduces to, its components related to
themselves. -/
theorem RT.pi_self {a : List Tok} {T D : CTm Head n} {E : CTm Head (n + 1)}
    (hT : ∀ s ∈ a, RT H Γ false s T T T) (hpi : Tok.tag .pi ∈ a) (hred : CRedTy H Γ T (.pi D E)) :
    PiRed H Γ T T D E D E := by
  obtain ⟨D₁, E₁, D₁', E₁', hp⟩ := RT.ty_pi_iff.1 (hT _ hpi)
  obtain ⟨rfl, rfl⟩ := CRedTy.pi_align hred hp.1
  obtain ⟨rfl, rfl⟩ := CRedTy.pi_align hred hp.2.1
  exact hp

theorem RT.sigma_self {a : List Tok} {T D : CTm Head n} {E : CTm Head (n + 1)}
    (hT : ∀ s ∈ a, RT H Γ false s T T T) (hsig : Tok.tag .sigma ∈ a)
    (hred : CRedTy H Γ T (.sigma D E)) : SigmaRed H Γ T T D E D E := by
  obtain ⟨D₁, E₁, D₁', E₁', hp⟩ := RT.ty_sigma_iff.1 (hT _ hsig)
  obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hred hp.1
  obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hred hp.2.1
  exact hp

theorem RT.ident_self {a : List Tok} {T B x y : CTm Head n}
    (hT : ∀ s ∈ a, RT H Γ false s T T T) (hid : Tok.tag .ident ∈ a)
    (hred : CRedTy H Γ T (.id B x y)) : IdRed H Γ T T B x y B x y := by
  obtain ⟨B₁, x₁, y₁, B₁', x₁', y₁', hi⟩ := RT.ty_ident_iff.1 (hT _ hid)
  obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hred hi.1
  obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hred hi.2.1
  exact hi

/-- The families of a dependent function type related to itself send arguments
related as far as an input observes to types related as far as the outputs of the
entries with that input observe. -/
theorem RT.pi_fam_at {a X : List Tok} {T D N N' : CTm Head n} {E : CTm Head (n + 1)}
    (hp : PiRed H Γ T T D E D E) (hT : ∀ s ∈ a, RT H Γ false s T T T)
    (e : CEqual P Γ N N' D) (hNN : ∀ x ∈ X, RT H Γ true x D N N') :
    ∀ r ∈ fnApp .pi a X, RT H Γ false r (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) := by
  intro r hr
  obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
  rcases RT.pi_fam hp (fun s hs _ => hT s hs) hm with hvac | ⟨hf, -⟩
  · exact RT.of_vacuous (vacuous_out hvac hr')
  · exact (hf N N' e (fun z hz => RT.closed' (hZ' z hz) hNN) r hr').1

theorem RT.sigma_fam_at {a X : List Tok} {T D N N' : CTm Head n} {E : CTm Head (n + 1)}
    (hp : SigmaRed H Γ T T D E D E) (hT : ∀ s ∈ a, RT H Γ false s T T T)
    (e : CEqual P Γ N N' D) (hNN : ∀ x ∈ X, RT H Γ true x D N N') :
    ∀ r ∈ fnApp .sigma a X, RT H Γ false r (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) := by
  intro r hr
  obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
  rcases RT.sigma_fam hp (fun s hs _ => hT s hs) hm with hvac | ⟨hf, -⟩
  · exact RT.of_vacuous (vacuous_out hvac hr')
  · exact (hf N N' e (fun z hz => RT.closed' (hZ' z hz) hNN) r hr').1

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) (formed : CCtxFormed P Γ)
include levels formed

/-- Terms related as far as a token observes stay related when the right one is
replaced by a term with a common reduct. -/
theorem RT.retarget {c : Tok} {D x b N Q : CTm Head n} (tx : CTyped P Γ x D)
    (h : RT H Γ true c D x b) (rb : CRedTm H Γ b Q D) (rN : CRedTm H Γ N Q D) :
    RT H Γ true c D x N :=
  RT.expand levels formed (CRedTm.refl tx) rN (RT.reduce levels formed (CRedTm.refl tx) rb h)

/-- A term with a common reduct with a term related to itself is related to itself. -/
theorem RT.self_of_join {c : Tok} {D x N Q : CTm Head n} (h : RT H Γ true c D x x)
    (rx : CRedTm H Γ x Q D) (rN : CRedTm H Γ N Q D) : RT H Γ true c D N N :=
  RT.expand levels formed rN rN (RT.reduce levels formed rx rx h)

end Self

/-! ## The laws below a depth -/

section Laws

variable {L : Type} [LevelOrder L] {n : Nat} {Γ : CCtx Head n}

variable (H Γ) in
/-- The laws of the relation at the tokens of depth below `N`. Symmetry and
transitivity of terms read the type's relation to itself as far as the type witness
observes. -/
structure LawsBelow (N : Nat) : Prop where
  conv : ∀ {t : Tok}, t.depth < N → ∀ {a : List Tok}, Ty a Elem.univ → TyTok a t →
    ∀ {A B M M' : CTm Head n}, (∀ s ∈ a, RT H Γ false s A A B) → CTypeEq P Γ A B →
      (RT H Γ true t A M M' ↔ RT H Γ true t B M M')
  symmTy : ∀ {t : Tok}, t.depth < N → TyTok Elem.univ t →
    ∀ {A A' : CTm Head n}, RT H Γ false t A A A' → RT H Γ false t A' A' A
  transTy : ∀ {t : Tok}, t.depth < N → TyTok Elem.univ t →
    ∀ {A₁ A₂ A₃ : CTm Head n}, RT H Γ false t A₁ A₁ A₂ → RT H Γ false t A₂ A₂ A₃ →
      RT H Γ false t A₁ A₁ A₃
  symm : ∀ {t : Tok}, t.depth < N → ∀ {a : List Tok}, Ty a Elem.univ → TyTok a t →
    ∀ {T M M' : CTm Head n}, (∀ s ∈ a, RT H Γ false s T T T) →
      RT H Γ true t T M M' → RT H Γ true t T M' M
  trans : ∀ {t : Tok}, t.depth < N → ∀ {a : List Tok}, Ty a Elem.univ → TyTok a t →
    ∀ {T M₁ M₂ M₃ : CTm Head n}, (∀ s ∈ a, RT H Γ false s T T T) →
      RT H Γ true t T M₁ M₂ → RT H Γ true t T M₂ M₃ → RT H Γ true t T M₁ M₃

theorem LawsBelow.zero : LawsBelow H Γ 0 :=
  ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _),
    fun h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _),
    fun h => absurd h (Nat.not_lt_zero _)⟩

end Laws

/-! ## Conversion -/

section Conversion

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
  (formed : CCtxFormed P Γ)

theorem ReflRed.conv {A B M M' B₁ y₁ z₁ B₂ y₂ z₂ r r' : CTm Head n}
    (hi : IdRed H Γ A B B₁ y₁ z₁ B₂ y₂ z₂) (eAB : CTypeEq P Γ A B)
    (hr : ReflRed H Γ A M M' B₁ y₁ z₁ r r') : ReflRed H Γ B M M' B₂ y₂ z₂ r r' := by
  obtain ⟨_, rB, eB, ey, ez⟩ := hi
  obtain ⟨_, rM, rM', e₁, e₂, e₃⟩ := hr
  exact ⟨rB, rM.convType eAB, rM'.convType eAB, CEqual.convType (e₁.trans ey) eB,
    CEqual.convType (e₂.trans ez) eB, e₃.convType eB⟩

theorem ReflRed.conv' {A B M M' B₁ y₁ z₁ B₂ y₂ z₂ r r' : CTm Head n}
    (hi : IdRed H Γ A B B₁ y₁ z₁ B₂ y₂ z₂) (eAB : CTypeEq P Γ A B)
    (hr : ReflRed H Γ B M M' B₂ y₂ z₂ r r') : ReflRed H Γ A M M' B₁ y₁ z₁ r r' := by
  obtain ⟨rA, _, eB, ey, ez⟩ := hi
  obtain ⟨_, rM, rM', e₁, e₂, e₃⟩ := hr
  exact ⟨rA, rM.convType eAB.symm, rM'.convType eAB.symm, (e₁.convType eB.symm).trans ey.symm,
    (e₂.convType eB.symm).trans ez.symm, e₃.convType eB.symm⟩

include levels formed in
/-- **Conversion** at the tokens of depth below `N + 1`, from the laws below `N`. -/
theorem LawsBelow.conv_step {N : Nat} (IH : LawsBelow H Γ N) {t : Tok} (ht : t.depth < N + 1)
    {a : List Tok} (ha : Ty a Elem.univ) (hta : TyTok a t) {A B M M' : CTm Head n}
    (hAB : ∀ s ∈ a, RT H Γ false s A A B) (eAB : CTypeEq P Γ A B) :
    RT H Γ true t A M M' ↔ RT H Γ true t B M M' := by
  have sub : ∀ {s : Tok}, s.depth < t.depth → s.depth < N := fun h => by omega
  cases hv : ent [] t with
  | true => exact ⟨fun _ => RT.of_vacuous hv, fun _ => RT.of_vacuous hv⟩
  | false =>
  cases htk : typeKind t.kind with
  | true =>
      obtain ⟨hU, -⟩ := tyTok_univ_of_typeKind htk hta
      constructor
      · intro h
        rcases (RT.tm_type_iff htk).1 h with hvac | ⟨_, _, hA, hr⟩ | ⟨hA, hr⟩
        · exact RT.of_vacuous hvac
        · rcases hU with hu | hc
          · obtain ⟨_, _, _, r₂, _, u₂, _⟩ := RT.ty_univ_iff.1 (hAB _ hu)
            exact RT.ofType htk u₂ r₂ hr
          · exact (CRedTy.head_ne_prop hA (RT.ty_codes_iff.1 (hAB _ hc)).1).elim
        · rcases hU with hu | hc
          · obtain ⟨_, _, r₁, _, _, _, _⟩ := RT.ty_univ_iff.1 (hAB _ hu)
            exact (CRedTy.head_ne_prop r₁ hA).elim
          · exact RT.ofCodes htk (RT.ty_codes_iff.1 (hAB _ hc)).2 hr
      · intro h
        rcases (RT.tm_type_iff htk).1 h with hvac | ⟨_, _, hB, hr⟩ | ⟨hB, hr⟩
        · exact RT.of_vacuous hvac
        · rcases hU with hu | hc
          · obtain ⟨_, _, r₁, _, u₁, _, _⟩ := RT.ty_univ_iff.1 (hAB _ hu)
            exact RT.ofType htk u₁ r₁ hr
          · exact (CRedTy.head_ne_prop hB (RT.ty_codes_iff.1 (hAB _ hc)).2).elim
        · rcases hU with hu | hc
          · obtain ⟨_, _, _, r₂, _, _, _⟩ := RT.ty_univ_iff.1 (hAB _ hu)
            exact (CRedTy.head_ne_prop r₂ hB).elim
          · exact RT.ofCodes htk (RT.ty_codes_iff.1 (hAB _ hc)).1 hr
  | false =>
  cases t with
  | tag k =>
      cases k
      case refl =>
        have hid : Tok.tag .ident ∈ a := tyTok_tag_refl.1 hta
        obtain ⟨B₁, y₁, z₁, B₂, y₂, z₂, hi⟩ := RT.ty_ident_iff.1 (hAB _ hid)
        constructor
        · intro h
          obtain ⟨B', y', z', r, r', hr⟩ := RT.tm_reflTag_iff.1 h
          obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hi.1 hr.1
          exact RT.tm_reflTag_iff.2 ⟨B₂, y₂, z₂, r, r', hr.conv hi eAB⟩
        · intro h
          obtain ⟨B', y', z', r, r', hr⟩ := RT.tm_reflTag_iff.1 h
          obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hi.2.1 hr.1
          exact RT.tm_reflTag_iff.2 ⟨B₁, y₁, z₁, r, r', hr.conv' hi eAB⟩
      case zero =>
        obtain ⟨rA, rB⟩ := RT.ty_nat_iff.1 (hAB _ (tyTok_tag_zero.1 hta))
        constructor
        · intro h
          obtain ⟨_, r₁, r₂⟩ := RT.tm_zero_iff.1 h
          exact RT.tm_zero_iff.2 ⟨rB, r₁.convType eAB, r₂.convType eAB⟩
        · intro h
          obtain ⟨_, r₁, r₂⟩ := RT.tm_zero_iff.1 h
          exact RT.tm_zero_iff.2 ⟨rA, r₁.convType eAB.symm, r₂.convType eAB.symm⟩
      case succ =>
        obtain ⟨rA, rB⟩ := RT.ty_nat_iff.1 (hAB _ (tyTok_tag_succ.1 hta))
        constructor
        · intro h
          obtain ⟨m, m', _, r₁, r₂, e⟩ := RT.tm_succTag_iff.1 h
          exact RT.tm_succTag_iff.2 ⟨m, m', rB, r₁.convType eAB, r₂.convType eAB, e⟩
        · intro h
          obtain ⟨m, m', _, r₁, r₂, e⟩ := RT.tm_succTag_iff.1 h
          exact RT.tm_succTag_iff.2 ⟨m, m', rA, r₁.convType eAB.symm, r₂.convType eAB.symm, e⟩
      case pair => exact absurd hta tyTok_tag_pair
      all_goals
        exact ⟨fun _ => RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e)
            (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e),
          fun _ => RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e)
            (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)⟩
  | arg k i C d =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk
      · exact ⟨fun _ => RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) (by intro e; cases e)
            (fun e => Tok.noConfusion e) (by intro e; cases e) (by intro e; cases e),
          fun _ => RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) (by intro e; cases e)
            (fun e => Tok.noConfusion e) (by intro e; cases e) (by intro e; cases e)⟩
      · match i, hta with
        | 0, hta =>
          obtain ⟨hid, hC, hsa, h1, h2⟩ := tyTok_reflPoint.1 hta
          subst hC
          obtain ⟨B₁, y₁, z₁, B₂, y₂, z₂, hi⟩ := RT.ty_ident_iff.1 (hAB _ hid)
          have hcar := RT.ident_carrier hi (fun q hq _ => hAB q hq)
          have hends := RT.ident_ends hi (fun q hq _ => hAB q hq)
          have hcarTy := ty_args_ident ha
          have selfB₁ : ∀ r ∈ args .ident 0 a, RT H Γ false r B₁ B₁ B₁ :=
            fun r hr => RT.left (hcar r hr)
          have hd : d.depth < N := sub (depth_lt_arg .refl 0 [] d)
          have convS : ∀ {u u' : CTm Head n}, RT H Γ true d B₁ u u' ↔ RT H Γ true d B₂ u u' :=
            IH.conv hd hcarTy hsa hcar hi.2.2.1
          have endY : RT H Γ true d B₁ y₁ y₂ := RT.closed' h1 hends.1
          have endZ : RT H Γ true d B₁ z₁ z₂ := RT.closed' h2 hends.2
          constructor
          · intro h
            rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B', y', z', r, r', hr, -, hpts⟩
            · exact RT.of_vacuous hvac
            obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hi.1 hr.1
            obtain ⟨p1, p2, p3⟩ := hpts rfl
            refine RT.tm_argRefl_iff.2 (.inr ⟨B₂, y₂, z₂, r, r', hr.conv hi eAB,
              fun c hc => absurd hc List.not_mem_nil, fun _ => ⟨?_, ?_, ?_⟩⟩)
            · exact convS.1 (IH.trans hd hcarTy hsa selfB₁ p1 endY)
            · exact convS.1 (IH.trans hd hcarTy hsa selfB₁ p2 endZ)
            · exact convS.1 p3
          · intro h
            rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B', y', z', r, r', hr, -, hpts⟩
            · exact RT.of_vacuous hvac
            obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hi.2.1 hr.1
            obtain ⟨p1, p2, p3⟩ := hpts rfl
            refine RT.tm_argRefl_iff.2 (.inr ⟨B₁, y₁, z₁, r, r', hr.conv' hi eAB,
              fun c hc => absurd hc List.not_mem_nil, fun _ => ⟨?_, ?_, ?_⟩⟩)
            · exact IH.trans hd hcarTy hsa selfB₁ (convS.2 p1)
                (IH.symm hd hcarTy hsa selfB₁ endY)
            · exact IH.trans hd hcarTy hsa selfB₁ (convS.2 p2)
                (IH.symm hd hcarTy hsa selfB₁ endZ)
            · exact convS.2 p3
        | i + 1, hta => exact absurd hta tyTok_reflPoint_succ
      · match i, hta with
        | 0, hta =>
          obtain ⟨hnat, hC, -⟩ := tyTok_pred.1 hta
          subst hC
          obtain ⟨rA, rB⟩ := RT.ty_nat_iff.1 (hAB _ hnat)
          constructor
          · intro h
            rcases RT.tm_argSucc_iff.1 h with hvac | ⟨m, m', ⟨_, r₁, r₂, e⟩, hc, hd⟩
            · exact RT.of_vacuous hvac
            · exact RT.tm_argSucc_iff.2 (.inr ⟨m, m', ⟨rB, r₁.convType eAB, r₂.convType eAB, e⟩,
                hc, hd⟩)
          · intro h
            rcases RT.tm_argSucc_iff.1 h with hvac | ⟨m, m', ⟨_, r₁, r₂, e⟩, hc, hd⟩
            · exact RT.of_vacuous hvac
            · exact RT.tm_argSucc_iff.2 (.inr ⟨m, m', ⟨rA, r₁.convType eAB.symm,
                r₂.convType eAB.symm, e⟩, hc, hd⟩)
        | i + 1, hta => exact absurd hta tyTok_pred_succ
      · match i, hta with
        | 0, hta =>
          obtain ⟨hsig, hC, hsa⟩ := tyTok_fst.1 hta
          subst hC
          obtain ⟨D₁, E₁, D₂, E₂, hp⟩ := RT.ty_sigma_iff.1 (hAB _ hsig)
          have hdom := RT.sigma_dom hp (fun s hs _ => hAB s hs)
          have hdomTy : Ty (args .sigma 0 a) Elem.univ := Ideal.ty_args_dom (.inr rfl) ha
          have hd : d.depth < N := sub (depth_lt_arg .pair 0 [] d)
          have convD : ∀ {u u' : CTm Head n}, RT H Γ true d D₁ u u' ↔ RT H Γ true d D₂ u u' :=
            IH.conv hd hdomTy hsa hdom hp.2.2.1
          constructor
          · intro h
            rcases RT.tm_argPair_iff.1 h with hvac | hcl
            · exact RT.of_vacuous hvac
            refine RT.tm_argPair_iff.2 (.inr fun D E hB => ?_)
            obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hp.2.1 hB
            obtain ⟨e₀, -, h0, -⟩ := hcl D₁ E₁ hp.1
            exact ⟨e₀.convType hp.2.2.1, fun c hc => absurd hc List.not_mem_nil,
              fun _ => convD.1 (h0 rfl), fun h1 => absurd h1 (by decide)⟩
          · intro h
            rcases RT.tm_argPair_iff.1 h with hvac | hcl
            · exact RT.of_vacuous hvac
            refine RT.tm_argPair_iff.2 (.inr fun D E hA => ?_)
            obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hp.1 hA
            obtain ⟨e₀, -, h0, -⟩ := hcl D₂ E₂ hp.2.1
            exact ⟨e₀.convType hp.2.2.1.symm, fun c hc => absurd hc List.not_mem_nil,
              fun _ => convD.2 (h0 rfl), fun h1 => absurd h1 (by decide)⟩
        | 1, hta =>
          obtain ⟨hsig, hCty, hsa⟩ := tyTok_snd.1 hta
          obtain ⟨D₁, E₁, D₂, E₂, hp⟩ := RT.ty_sigma_iff.1 (hAB _ hsig)
          have hdom := RT.sigma_dom hp (fun s hs _ => hAB s hs)
          have hdomTy : Ty (args .sigma 0 a) Elem.univ := Ideal.ty_args_dom (.inr rfl) ha
          have hfamTy : Ty (fnApp .sigma a C) Elem.univ := Ideal.ty_fnApp (.inr rfl) ha C
          have hd : d.depth < N := sub (depth_lt_arg .pair 1 C d)
          have convC : ∀ c ∈ C, ∀ {u u' : CTm Head n},
              RT H Γ true c D₁ u u' ↔ RT H Γ true c D₂ u u' := fun c hc =>
            IH.conv (sub (Tok.depth_lt_of_mem_dep (t := .arg .pair 1 C d) hc)) hdomTy (hCty c hc)
              hdom hp.2.2.1
          -- the two families at one argument related to itself as far as `C` observes
          have famConv : ∀ {N₁ : CTm Head n}, CTyped P Γ N₁ D₁ →
              (∀ c ∈ C, RT H Γ true c D₁ N₁ N₁) → ∀ {M₁ M₂ : CTm Head n},
                RT H Γ true d (CTm.inst0 N₁ E₁) M₁ M₂ ↔ RT H Γ true d (CTm.inst0 N₁ E₂) M₁ M₂ := by
            intro N₁ tN₁ hN₁ M₁ M₂
            refine IH.conv hd hfamTy hsa ?_ (hp.2.2.2.instantiate tN₁)
            intro r hr
            obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
            rcases RT.sigma_fam hp (fun s hs _ => hAB s hs) hm with hvac | ⟨-, hg⟩
            · exact RT.of_vacuous (vacuous_out hvac hr')
            · exact hg N₁ tN₁ (fun z hz => RT.closed' (hZ' z hz) hN₁) r hr'
          constructor
          · intro h
            rcases RT.tm_argPair_iff.1 h with hvac | hcl
            · exact RT.of_vacuous hvac
            refine RT.tm_argPair_iff.2 (.inr fun D E hB => ?_)
            obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hp.2.1 hB
            obtain ⟨e₀, hC, -, h1⟩ := hcl D₁ E₁ hp.1
            refine ⟨e₀.convType hp.2.2.1, fun c hc => (convC c hc).1 (hC c hc),
              fun h0 => absurd h0 (by decide), fun _ N₁ Q hQ hNQ => ?_⟩
            have hQ₁ : CRedTm H Γ (.fst M) Q D₁ := hQ.convType hp.2.2.1.symm
            have hNQ₁ : CRedTm H Γ N₁ Q D₁ := hNQ.convType hp.2.2.1.symm
            have tN₁ : CTyped P Γ N₁ D₁ := (CEqual.typed levels hNQ₁.2 formed).1
            exact (famConv tN₁ (fun c hc => RT.self_of_join levels formed (RT.left (hC c hc))
              hQ₁ hNQ₁)).1 (h1 rfl N₁ Q hQ₁ hNQ₁)
          · intro h
            rcases RT.tm_argPair_iff.1 h with hvac | hcl
            · exact RT.of_vacuous hvac
            refine RT.tm_argPair_iff.2 (.inr fun D E hA => ?_)
            obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hA hp.1
            obtain ⟨e₀, hC, -, h1⟩ := hcl D₂ E₂ hp.2.1
            have hC₁ : ∀ c ∈ C, RT H Γ true c D₁ (.fst M) (.fst M') := fun c hc =>
              (convC c hc).2 (hC c hc)
            refine ⟨e₀.convType hp.2.2.1.symm, hC₁, fun h0 => absurd h0 (by decide),
              fun _ N₁ Q hQ hNQ => ?_⟩
            have hQ₂ : CRedTm H Γ (.fst M) Q D₂ := hQ.convType hp.2.2.1
            have hNQ₂ : CRedTm H Γ N₁ Q D₂ := hNQ.convType hp.2.2.1
            have tN₁ : CTyped P Γ N₁ D₁ := (CEqual.typed levels hNQ.2 formed).1
            exact (famConv tN₁ (fun c hc => RT.self_of_join levels formed (RT.left (hC₁ c hc))
              hQ hNQ)).2 (h1 rfl N₁ Q hQ₂ hNQ₂)
        | i + 2, hta => exact absurd hta tyTok_pair_high
      · exact ⟨fun _ => RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) hk.2.1
            (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2,
          fun _ => RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) hk.2.1
            (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2⟩
  | fn k C X Y =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk
      · obtain ⟨hpi, -, hX, hY⟩ := tyTok_lam.1 hta
        obtain ⟨D₁, E₁, D₂, E₂, hp⟩ := RT.ty_pi_iff.1 (hAB _ hpi)
        have hdom : ∀ r ∈ args .pi 0 a, RT H Γ false r D₁ D₁ D₂ :=
          RT.pi_dom hp (fun s hs _ => hAB s hs)
        have hdomTy : Ty (args .pi 0 a) Elem.univ := Ideal.ty_args_dom (.inl rfl) ha
        have eD : CTypeEq P Γ D₁ D₂ := hp.2.2.1
        have eE : CTypeEq P (.snoc Γ D₁) E₁ E₂ := hp.2.2.2
        have argConv : ∀ {N₁ N₁' : CTm Head n},
            (∀ x ∈ X, RT H Γ true x D₁ N₁ N₁') ↔ (∀ x ∈ X, RT H Γ true x D₂ N₁ N₁') :=
          ⟨fun h x hx => (IH.conv (sub (depth_lt_fn_left hx)) hdomTy (hX x hx) hdom eD).1 (h x hx),
            fun h x hx => (IH.conv (sub (depth_lt_fn_left hx)) hdomTy (hX x hx) hdom eD).2 (h x hx)⟩
        have famConv : ∀ {N₁ : CTm Head n}, CTyped P Γ N₁ D₁ → (∀ x ∈ X, RT H Γ true x D₁ N₁ N₁) →
            ∀ y ∈ Y, ∀ {M₁ M₂ : CTm Head n},
              RT H Γ true y (CTm.inst0 N₁ E₁) M₁ M₂ ↔ RT H Γ true y (CTm.inst0 N₁ E₂) M₁ M₂ := by
          intro N₁ tN₁ hN₁ y hy M₁ M₂
          refine IH.conv (sub (depth_lt_fn_right hy)) (Ideal.ty_fnApp (.inl rfl) ha X) (hY y hy) ?_
            (eE.instantiate tN₁)
          intro r hr
          obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
          rcases RT.pi_fam hp (fun s hs _ => hAB s hs) hm with hvac | ⟨-, hg⟩
          · exact RT.of_vacuous (vacuous_out hvac hr')
          · exact hg N₁ tN₁ (fun z hz => RT.closed' (hZ' z hz) hN₁) r hr'
        constructor
        · intro h
          rcases RT.tm_lam_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_lam_iff.2 (.inr fun D E hB => ?_)
          obtain ⟨eD2, eE2⟩ := CRedTy.pi_align hp.2.1 hB
          subst eD2 eE2
          obtain ⟨hi, hii⟩ := hcl D₁ E₁ hp.1
          refine ⟨fun N₁ N₁' hNN hX' y hy => ?_, fun N₁ tN₁ hX' y hy => ?_⟩
          · have hNN₁ : CEqual P Γ N₁ N₁' D₁ := hNN.convType eD.symm
            have hX₁ := argConv.2 hX'
            have tN₁ := (CEqual.typed levels hNN₁ formed).1
            have hself : ∀ x ∈ X, RT H Γ true x D₁ N₁ N₁ := fun x hx => RT.left (hX₁ x hx)
            obtain ⟨h1, h2⟩ := hi N₁ N₁' hNN₁ hX₁ y hy
            exact ⟨(famConv tN₁ hself y hy).1 h1, (famConv tN₁ hself y hy).1 h2⟩
          · have tN₁' : CTyped P Γ N₁ D₁ := tN₁.convType eD.symm
            have hX₁ := argConv.2 hX'
            exact (famConv tN₁' hX₁ y hy).1 (hii N₁ tN₁' hX₁ y hy)
        · intro h
          rcases RT.tm_lam_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_lam_iff.2 (.inr fun D E hA => ?_)
          obtain ⟨eD1, eE1⟩ := CRedTy.pi_align hp.1 hA
          subst eD1 eE1
          obtain ⟨hi, hii⟩ := hcl D₂ E₂ hp.2.1
          refine ⟨fun N₁ N₁' hNN hX₁ y hy => ?_, fun N₁ tN₁ hX₁ y hy => ?_⟩
          · have tN₁ := (CEqual.typed levels hNN formed).1
            have hself : ∀ x ∈ X, RT H Γ true x _ N₁ N₁ := fun x hx => RT.left (hX₁ x hx)
            obtain ⟨h1, h2⟩ := hi N₁ N₁' (hNN.convType eD) (argConv.1 hX₁) y hy
            exact ⟨(famConv tN₁ hself y hy).2 h1, (famConv tN₁ hself y hy).2 h2⟩
          · exact (famConv tN₁ hX₁ y hy).2 (hii N₁ (tN₁.convType eD) (argConv.1 hX₁) y hy)
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact ⟨fun _ => RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
            (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2,
          fun _ => RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
            (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2⟩

end Conversion

/-! ## Symmetry and transitivity of the canonical forms -/

section Shapes

variable {L : Type} [LevelOrder L] {n : Nat} {Γ : CCtx Head n}

theorem UnivRed.symm (levels : LevelModel R L) {A A' : CTm Head n} (h : UnivRed H Γ A A') : UnivRed H Γ A' A := by
  obtain ⟨u, u', r, r', hu, hu', e⟩ := h
  exact ⟨u', u, r', r, hu', hu, e.symm levels⟩

theorem UnivRed.trans (levels : LevelModel R L) {A₁ A₂ A₃ : CTm Head n} (h₁ : UnivRed H Γ A₁ A₂)
    (h₂ : UnivRed H Γ A₂ A₃) : UnivRed H Γ A₁ A₃ := by
  obtain ⟨u₁, u₂, r₁, r₂, hu₁, -, e₁⟩ := h₁
  obtain ⟨u₂', u₃, r₂', r₃, -, hu₃, e₂⟩ := h₂
  have e := CRedTy.nf_unique r₂' r₂ (H.normal_head _) (H.normal_head _)
  injection e with _ e
  subst e
  exact ⟨u₁, u₃, r₁, r₃, hu₁, hu₃, e₁.trans levels e₂⟩

theorem PiRed.symm {A A' D D' : CTm Head n} {E E' : CTm Head (n + 1)}
    (h : PiRed H Γ A A' D E D' E') : PiRed H Γ A' A D' E' D E :=
  ⟨h.2.1, h.1, h.2.2.1.symm, (h.2.2.2.ctxConv h.2.2.1).symm⟩

theorem PiRed.trans (levels : LevelModel R L) {A₁ A₂ A₃ D₁ D₂ D₂' D₃ : CTm Head n} {E₁ E₂ E₂' E₃ : CTm Head (n + 1)}
    (h₁ : PiRed H Γ A₁ A₂ D₁ E₁ D₂ E₂) (h₂ : PiRed H Γ A₂ A₃ D₂' E₂' D₃ E₃) :
    PiRed H Γ A₁ A₃ D₁ E₁ D₃ E₃ := by
  obtain ⟨rfl, rfl⟩ := CRedTy.pi_align h₁.2.1 h₂.1
  exact ⟨h₁.1, h₂.2.1, CTypeEq.trans levels h₁.2.2.1 h₂.2.2.1,
    CTypeEq.trans levels h₁.2.2.2 (h₂.2.2.2.ctxConv h₁.2.2.1.symm)⟩

theorem SigmaRed.symm {A A' D D' : CTm Head n} {E E' : CTm Head (n + 1)}
    (h : SigmaRed H Γ A A' D E D' E') : SigmaRed H Γ A' A D' E' D E :=
  ⟨h.2.1, h.1, h.2.2.1.symm, (h.2.2.2.ctxConv h.2.2.1).symm⟩

theorem SigmaRed.trans (levels : LevelModel R L) {A₁ A₂ A₃ D₁ D₂ D₂' D₃ : CTm Head n}
    {E₁ E₂ E₂' E₃ : CTm Head (n + 1)}
    (h₁ : SigmaRed H Γ A₁ A₂ D₁ E₁ D₂ E₂) (h₂ : SigmaRed H Γ A₂ A₃ D₂' E₂' D₃ E₃) :
    SigmaRed H Γ A₁ A₃ D₁ E₁ D₃ E₃ := by
  obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align h₁.2.1 h₂.1
  exact ⟨h₁.1, h₂.2.1, CTypeEq.trans levels h₁.2.2.1 h₂.2.2.1,
    CTypeEq.trans levels h₁.2.2.2 (h₂.2.2.2.ctxConv h₁.2.2.1.symm)⟩

theorem GroundRed.symm {A A' : CTm Head n} (h : GroundRed H Γ A A') : GroundRed H Γ A' A := by
  obtain ⟨g, hg, r, r'⟩ := h
  exact ⟨g, hg, r', r⟩

theorem GroundRed.trans {A₁ A₂ A₃ : CTm Head n} (h₁ : GroundRed H Γ A₁ A₂)
    (h₂ : GroundRed H Γ A₂ A₃) : GroundRed H Γ A₁ A₃ := by
  obtain ⟨g, hg, r₁, r₂⟩ := h₁
  obtain ⟨g', hg', r₂', r₃⟩ := h₂
  exact ⟨g, hg, r₁, CRedTy.ground_align hg hg' r₂ r₂' ▸ r₃⟩

theorem IdRed.symm {A A' B x y B' x' y' : CTm Head n} (h : IdRed H Γ A A' B x y B' x' y') :
    IdRed H Γ A' A B' x' y' B x y :=
  ⟨h.2.1, h.1, h.2.2.1.symm, CEqual.convType (.symm h.2.2.2.1) h.2.2.1,
    CEqual.convType (.symm h.2.2.2.2) h.2.2.1⟩

theorem IdRed.trans (levels : LevelModel R L) {A₁ A₂ A₃ B₁ x₁ y₁ B₂ x₂ y₂ B₂' x₂' y₂' B₃ x₃ y₃ : CTm Head n}
    (h₁ : IdRed H Γ A₁ A₂ B₁ x₁ y₁ B₂ x₂ y₂) (h₂ : IdRed H Γ A₂ A₃ B₂' x₂' y₂' B₃ x₃ y₃) :
    IdRed H Γ A₁ A₃ B₁ x₁ y₁ B₃ x₃ y₃ := by
  obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align h₁.2.1 h₂.1
  exact ⟨h₁.1, h₂.2.1, CTypeEq.trans levels h₁.2.2.1 h₂.2.2.1,
    .trans h₁.2.2.2.1 (CEqual.convType h₂.2.2.2.1 h₁.2.2.1.symm),
    .trans h₁.2.2.2.2 (CEqual.convType h₂.2.2.2.2 h₁.2.2.1.symm)⟩

theorem ReflRed.symm {T M M' B x y r r' : CTm Head n} (h : ReflRed H Γ T M M' B x y r r') :
    ReflRed H Γ T M' M B x y r' r :=
  ⟨h.1, h.2.2.1, h.2.1, .trans (.symm h.2.2.2.2.2) h.2.2.2.1,
    .trans (.symm h.2.2.2.2.2) h.2.2.2.2.1, .symm h.2.2.2.2.2⟩

theorem ReflRed.trans {T M₁ M₂ M₃ B x y B' x' y' r₁ r₂ r₂' r₃ : CTm Head n}
    (h₁ : ReflRed H Γ T M₁ M₂ B x y r₁ r₂) (h₂ : ReflRed H Γ T M₂ M₃ B' x' y' r₂' r₃) :
    ReflRed H Γ T M₁ M₃ B x y r₁ r₃ := by
  obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align h₁.1 h₂.1
  obtain rfl := CRedTm.refl_align h₁.2.2.1 h₂.2.1
  exact ⟨h₁.1, h₁.2.1, h₂.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2.1, .trans h₁.2.2.2.2.2 h₂.2.2.2.2.2⟩

theorem SuccRed.symm {T M M' m m' : CTm Head n} (h : SuccRed H Γ T M M' m m') :
    SuccRed H Γ T M' M m' m :=
  ⟨h.1, h.2.2.1, h.2.1, .symm h.2.2.2⟩

theorem SuccRed.trans {T M₁ M₂ M₃ m₁ m₂ m₂' m₃ : CTm Head n} (h₁ : SuccRed H Γ T M₁ M₂ m₁ m₂)
    (h₂ : SuccRed H Γ T M₂ M₃ m₂' m₃) : SuccRed H Γ T M₁ M₃ m₁ m₃ := by
  obtain rfl := CRedTm.suc_align h₁.2.2.1 h₂.2.1
  exact ⟨h₁.1, h₁.2.1, h₂.2.2.1, .trans h₁.2.2.2 h₂.2.2.2⟩

end Shapes

/-! ## Symmetry and transitivity of the type relation -/

section TypeLaws

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}

/-- The type relation carries no clause at the other tags. -/
private theorem tag_other_ne {k : Kind} (h1 : k ≠ .univ) (h2 : k ≠ .codes) (h3 : k ≠ .nat)
    (h4 : k ≠ .pi) (h5 : k ≠ .ident) (h6 : k ≠ .ground) (h7 : k ≠ .sigma) :
    k ≠ .univ ∧ k ≠ .codes ∧ k ≠ .nat ∧ k ≠ .pi ∧ k ≠ .ident ∧ k ≠ .ground ∧ k ≠ .sigma :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

include levels in
/-- **Symmetry of the type relation** at the tokens of depth below `N + 1`. -/
theorem LawsBelow.symmTy_step {N : Nat} (IH : LawsBelow H Γ N) {t : Tok} (ht : t.depth < N + 1)
    (hty : TyTok Elem.univ t) {A A' : CTm Head n} (h : RT H Γ false t A A A') :
    RT H Γ false t A' A' A := by
  have sub : ∀ {s : Tok}, s.depth < t.depth → s.depth < N := fun h => by omega
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases t with
  | tag k =>
      cases k
      case univ => exact RT.ty_univ_iff.2 (UnivRed.symm levels (RT.ty_univ_iff.1 h))
      case codes =>
        obtain ⟨r, r'⟩ := RT.ty_codes_iff.1 h
        exact RT.ty_codes_iff.2 ⟨r', r⟩
      case nat =>
        obtain ⟨r, r'⟩ := RT.ty_nat_iff.1 h
        exact RT.ty_nat_iff.2 ⟨r', r⟩
      case pi =>
        obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_iff.1 h
        exact RT.ty_pi_iff.2 ⟨D', E', D, E, hp.symm⟩
      case ident =>
        obtain ⟨B, x, y, B', x', y', hi⟩ := RT.ty_ident_iff.1 h
        exact RT.ty_ident_iff.2 ⟨B', x', y', B, x, y, hi.symm⟩
      case ground => exact RT.ty_ground_iff.2 (RT.ty_ground_iff.1 h).symm
      case sigma =>
        obtain ⟨D, E, D', E', hp⟩ := RT.ty_sigma_iff.1 h
        exact RT.ty_sigma_iff.2 ⟨D', E', D, E, hp.symm⟩
      all_goals exact RT.ty_tag_other (tag_other_ne (by intro e; cases e) (by intro e; cases e)
        (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
        (by intro e; cases e))
  | arg k i C d =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | hk
      · match i, hty with
        | 0, hty =>
          obtain ⟨-, rfl, hd⟩ := (tyTok_dom (.inl rfl)).1 hty
          rcases RT.ty_argPi_iff.1 h with hvac | ⟨D, E, D', E', hp, -, hdd⟩
          · exact RT.of_vacuous hvac
          exact RT.ty_argPi_iff.2 (.inr ⟨D', E', D, E, hp.symm,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.symmTy (sub (depth_lt_arg _ _ _ _)) hd (hdd rfl)⟩)
        | i + 1, hty => exact absurd hty tyTok_argPi_succ
      · match i, hty with
        | 0, hty =>
          obtain ⟨-, rfl, hd⟩ := (tyTok_dom (.inr (.inr rfl))).1 hty
          rcases RT.ty_argIdent_iff.1 h with hvac | ⟨B, x, y, B', x', y', hi, -, hdd, -, -⟩
          · exact RT.of_vacuous hvac
          exact RT.ty_argIdent_iff.2 (.inr ⟨B', x', y', B, x, y, hi.symm,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.symmTy (sub (depth_lt_arg _ _ _ _)) hd (hdd rfl),
            fun e => absurd e (by decide), fun e => absurd e (by decide)⟩)
        | 1, hty =>
          obtain ⟨-, hC, hs⟩ := (tyTok_endpoint (.inl rfl)).1 hty
          rcases RT.ty_argIdent_iff.1 h with hvac | ⟨B, x, y, B', x', y', hi, hc, -, hd1, -⟩
          · exact RT.of_vacuous hvac
          have hsd : d.depth < N := sub (depth_lt_arg _ _ _ _)
          have selfB : ∀ c ∈ C, RT H Γ false c B B B := fun c hc' => RT.left (hc c hc')
          exact RT.ty_argIdent_iff.2 (.inr ⟨B', x', y', B, x, y, hi.symm,
            fun c hc' => IH.symmTy (sub (Tok.depth_lt_of_mem_dep (t := .arg .ident 1 C d) hc'))
              (hC c hc') (hc c hc'),
            fun e => absurd e (by decide),
            fun _ => (IH.conv hsd hC hs hc hi.2.2.1).1 (IH.symm hsd hC hs selfB (hd1 rfl)),
            fun e => absurd e (by decide)⟩)
        | 2, hty =>
          obtain ⟨-, hC, hs⟩ := (tyTok_endpoint (.inr rfl)).1 hty
          rcases RT.ty_argIdent_iff.1 h with hvac | ⟨B, x, y, B', x', y', hi, hc, -, -, hd2⟩
          · exact RT.of_vacuous hvac
          have hsd : d.depth < N := sub (depth_lt_arg _ _ _ _)
          have selfB : ∀ c ∈ C, RT H Γ false c B B B := fun c hc' => RT.left (hc c hc')
          exact RT.ty_argIdent_iff.2 (.inr ⟨B', x', y', B, x, y, hi.symm,
            fun c hc' => IH.symmTy (sub (Tok.depth_lt_of_mem_dep (t := .arg .ident 2 C d) hc'))
              (hC c hc') (hc c hc'),
            fun e => absurd e (by decide), fun e => absurd e (by decide),
            fun _ => (IH.conv hsd hC hs hc hi.2.2.1).1 (IH.symm hsd hC hs selfB (hd2 rfl))⟩)
        | i + 3, hty => exact absurd hty tyTok_argIdent_high
      · match i, hty with
        | 0, hty =>
          obtain ⟨-, rfl, hd⟩ := (tyTok_dom (.inr (.inl rfl))).1 hty
          rcases RT.ty_argSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, -, hdd⟩
          · exact RT.of_vacuous hvac
          exact RT.ty_argSigma_iff.2 (.inr ⟨D', E', D, E, hp.symm,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.symmTy (sub (depth_lt_arg _ _ _ _)) hd (hdd rfl)⟩)
        | i + 1, hty => exact absurd hty tyTok_argSigma_succ
      · exact RT.ty_arg_other hk
  | fn k C Z W =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | hk
      · obtain ⟨-, hC, hZ, hW⟩ := (tyTok_family (.inl rfl)).1 hty
        rcases RT.ty_fnPi_iff.1 h with hvac | ⟨D, E, D', E', hp, hc, hf, hg⟩
        · exact RT.of_vacuous hvac
        have hcD : ∀ c ∈ C, RT H Γ false c D' D' D := fun c hc' =>
          IH.symmTy (sub (Tok.depth_lt_of_mem_dep (t := .fn .pi C Z W) hc')) (hC c hc') (hc c hc')
        have eD : CTypeEq P Γ D' D := hp.2.2.1.symm
        have zConv : ∀ {N₁ N₁' : CTm Head n}, (∀ z ∈ Z, RT H Γ true z D' N₁ N₁') →
            ∀ z ∈ Z, RT H Γ true z D N₁ N₁' := fun hz z hzZ =>
          (IH.conv (sub (depth_lt_fn_left hzZ)) hC (hZ z hzZ) hcD eD).1 (hz z hzZ)
        refine RT.ty_fnPi_iff.2 (.inr ⟨D', E', D, E, hp.symm, hcD,
          fun N₁ N₁' hNN hz w hw => ?_, fun N₁ tN hz w hw => ?_⟩)
        · obtain ⟨h1, h2⟩ := hf N₁ N₁' (hNN.convType eD) (zConv hz) w hw
          exact ⟨h2, h1⟩
        · exact IH.symmTy (sub (depth_lt_fn_right hw)) (hW w hw)
            (hg N₁ (tN.convType eD) (zConv hz) w hw)
      · exact absurd hty (tyTok_fn_other (by simp))
      · obtain ⟨-, hC, hZ, hW⟩ := (tyTok_family (.inr rfl)).1 hty
        rcases RT.ty_fnSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, hc, hf, hg⟩
        · exact RT.of_vacuous hvac
        have hcD : ∀ c ∈ C, RT H Γ false c D' D' D := fun c hc' =>
          IH.symmTy (sub (Tok.depth_lt_of_mem_dep (t := .fn .sigma C Z W) hc')) (hC c hc')
            (hc c hc')
        have eD : CTypeEq P Γ D' D := hp.2.2.1.symm
        have zConv : ∀ {N₁ N₁' : CTm Head n}, (∀ z ∈ Z, RT H Γ true z D' N₁ N₁') →
            ∀ z ∈ Z, RT H Γ true z D N₁ N₁' := fun hz z hzZ =>
          (IH.conv (sub (depth_lt_fn_left hzZ)) hC (hZ z hzZ) hcD eD).1 (hz z hzZ)
        refine RT.ty_fnSigma_iff.2 (.inr ⟨D', E', D, E, hp.symm, hcD,
          fun N₁ N₁' hNN hz w hw => ?_, fun N₁ tN hz w hw => ?_⟩)
        · obtain ⟨h1, h2⟩ := hf N₁ N₁' (hNN.convType eD) (zConv hz) w hw
          exact ⟨h2, h1⟩
        · exact IH.symmTy (sub (depth_lt_fn_right hw)) (hW w hw)
            (hg N₁ (tN.convType eD) (zConv hz) w hw)
      · exact RT.ty_fn_other hk

include levels in
/-- **Transitivity of the type relation** at the tokens of depth below `N + 1`. -/
theorem LawsBelow.transTy_step {N : Nat} (IH : LawsBelow H Γ N) {t : Tok} (ht : t.depth < N + 1)
    (hty : TyTok Elem.univ t) {A₁ A₂ A₃ : CTm Head n} (h₁ : RT H Γ false t A₁ A₁ A₂)
    (h₂ : RT H Γ false t A₂ A₂ A₃) : RT H Γ false t A₁ A₁ A₃ := by
  have sub : ∀ {s : Tok}, s.depth < t.depth → s.depth < N := fun h => by omega
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases t with
  | tag k =>
      cases k
      case univ =>
        exact RT.ty_univ_iff.2 (UnivRed.trans levels (RT.ty_univ_iff.1 h₁) (RT.ty_univ_iff.1 h₂))
      case codes => exact RT.ty_codes_iff.2 ⟨(RT.ty_codes_iff.1 h₁).1, (RT.ty_codes_iff.1 h₂).2⟩
      case nat => exact RT.ty_nat_iff.2 ⟨(RT.ty_nat_iff.1 h₁).1, (RT.ty_nat_iff.1 h₂).2⟩
      case pi =>
        obtain ⟨D₁, E₁, D₂, E₂, hp₁⟩ := RT.ty_pi_iff.1 h₁
        obtain ⟨D₂', E₂', D₃, E₃, hp₂⟩ := RT.ty_pi_iff.1 h₂
        exact RT.ty_pi_iff.2 ⟨D₁, E₁, D₃, E₃, PiRed.trans levels hp₁ hp₂⟩
      case ident =>
        obtain ⟨B₁, x₁, y₁, B₂, x₂, y₂, hi₁⟩ := RT.ty_ident_iff.1 h₁
        obtain ⟨B₂', x₂', y₂', B₃, x₃, y₃, hi₂⟩ := RT.ty_ident_iff.1 h₂
        exact RT.ty_ident_iff.2 ⟨B₁, x₁, y₁, B₃, x₃, y₃, IdRed.trans levels hi₁ hi₂⟩
      case ground =>
        exact RT.ty_ground_iff.2 ((RT.ty_ground_iff.1 h₁).trans (RT.ty_ground_iff.1 h₂))
      case sigma =>
        obtain ⟨D₁, E₁, D₂, E₂, hp₁⟩ := RT.ty_sigma_iff.1 h₁
        obtain ⟨D₂', E₂', D₃, E₃, hp₂⟩ := RT.ty_sigma_iff.1 h₂
        exact RT.ty_sigma_iff.2 ⟨D₁, E₁, D₃, E₃, SigmaRed.trans levels hp₁ hp₂⟩
      all_goals exact RT.ty_tag_other (tag_other_ne (by intro e; cases e) (by intro e; cases e)
        (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
        (by intro e; cases e))
  | arg k i C d =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | hk
      · match i, hty with
        | 0, hty =>
          obtain ⟨-, rfl, hd⟩ := (tyTok_dom (.inl rfl)).1 hty
          rcases RT.ty_argPi_iff.1 h₁ with hvac | ⟨D₁, E₁, D₂, E₂, hp₁, -, hd₁⟩
          · exact RT.of_vacuous hvac
          rcases RT.ty_argPi_iff.1 h₂ with hvac | ⟨D₂', E₂', D₃, E₃, hp₂, -, hd₂⟩
          · exact RT.of_vacuous hvac
          obtain ⟨rfl, rfl⟩ := CRedTy.pi_align hp₂.1 hp₁.2.1
          exact RT.ty_argPi_iff.2 (.inr ⟨D₁, E₁, D₃, E₃, PiRed.trans levels hp₁ hp₂,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.transTy (sub (depth_lt_arg _ _ _ _)) hd (hd₁ rfl) (hd₂ rfl)⟩)
        | i + 1, hty => exact absurd hty tyTok_argPi_succ
      · match i, hty with
        | 0, hty =>
          obtain ⟨-, rfl, hd⟩ := (tyTok_dom (.inr (.inr rfl))).1 hty
          rcases RT.ty_argIdent_iff.1 h₁ with hvac | ⟨B₁, x₁, y₁, B₂, x₂, y₂, hi₁, -, hd₁, -, -⟩
          · exact RT.of_vacuous hvac
          rcases RT.ty_argIdent_iff.1 h₂ with hvac |
            ⟨B₂', x₂', y₂', B₃, x₃, y₃, hi₂, -, hd₂, -, -⟩
          · exact RT.of_vacuous hvac
          obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hi₂.1 hi₁.2.1
          exact RT.ty_argIdent_iff.2 (.inr ⟨B₁, x₁, y₁, B₃, x₃, y₃, IdRed.trans levels hi₁ hi₂,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.transTy (sub (depth_lt_arg _ _ _ _)) hd (hd₁ rfl) (hd₂ rfl),
            fun e => absurd e (by decide), fun e => absurd e (by decide)⟩)
        | 1, hty =>
          obtain ⟨-, hC, hs⟩ := (tyTok_endpoint (.inl rfl)).1 hty
          rcases RT.ty_argIdent_iff.1 h₁ with hvac | ⟨B₁, x₁, y₁, B₂, x₂, y₂, hi₁, hc₁, -, hd₁, -⟩
          · exact RT.of_vacuous hvac
          rcases RT.ty_argIdent_iff.1 h₂ with hvac |
            ⟨B₂', x₂', y₂', B₃, x₃, y₃, hi₂, hc₂, -, hd₂, -⟩
          · exact RT.of_vacuous hvac
          obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hi₂.1 hi₁.2.1
          have hsd : d.depth < N := sub (depth_lt_arg _ _ _ _)
          have hcd : ∀ c ∈ C, c.depth < N := fun c hc =>
            sub (Tok.depth_lt_of_mem_dep (t := .arg .ident 1 C d) hc)
          have hc₂₁ : ∀ c ∈ C, RT H Γ false c B₂ B₂ B₁ := fun c hc =>
            IH.symmTy (hcd c hc) (hC c hc) (hc₁ c hc)
          have selfB₁ : ∀ c ∈ C, RT H Γ false c B₁ B₁ B₁ := fun c hc => RT.left (hc₁ c hc)
          exact RT.ty_argIdent_iff.2 (.inr ⟨B₁, x₁, y₁, B₃, x₃, y₃, IdRed.trans levels hi₁ hi₂,
            fun c hc => IH.transTy (hcd c hc) (hC c hc) (hc₁ c hc) (hc₂ c hc),
            fun e => absurd e (by decide),
            fun _ => IH.trans hsd hC hs selfB₁ (hd₁ rfl)
              ((IH.conv hsd hC hs hc₂₁ hi₁.2.2.1.symm).1 (hd₂ rfl)),
            fun e => absurd e (by decide)⟩)
        | 2, hty =>
          obtain ⟨-, hC, hs⟩ := (tyTok_endpoint (.inr rfl)).1 hty
          rcases RT.ty_argIdent_iff.1 h₁ with hvac | ⟨B₁, x₁, y₁, B₂, x₂, y₂, hi₁, hc₁, -, -, hd₁⟩
          · exact RT.of_vacuous hvac
          rcases RT.ty_argIdent_iff.1 h₂ with hvac |
            ⟨B₂', x₂', y₂', B₃, x₃, y₃, hi₂, hc₂, -, -, hd₂⟩
          · exact RT.of_vacuous hvac
          obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hi₂.1 hi₁.2.1
          have hsd : d.depth < N := sub (depth_lt_arg _ _ _ _)
          have hcd : ∀ c ∈ C, c.depth < N := fun c hc =>
            sub (Tok.depth_lt_of_mem_dep (t := .arg .ident 2 C d) hc)
          have hc₂₁ : ∀ c ∈ C, RT H Γ false c B₂ B₂ B₁ := fun c hc =>
            IH.symmTy (hcd c hc) (hC c hc) (hc₁ c hc)
          have selfB₁ : ∀ c ∈ C, RT H Γ false c B₁ B₁ B₁ := fun c hc => RT.left (hc₁ c hc)
          exact RT.ty_argIdent_iff.2 (.inr ⟨B₁, x₁, y₁, B₃, x₃, y₃, IdRed.trans levels hi₁ hi₂,
            fun c hc => IH.transTy (hcd c hc) (hC c hc) (hc₁ c hc) (hc₂ c hc),
            fun e => absurd e (by decide), fun e => absurd e (by decide),
            fun _ => IH.trans hsd hC hs selfB₁ (hd₁ rfl)
              ((IH.conv hsd hC hs hc₂₁ hi₁.2.2.1.symm).1 (hd₂ rfl))⟩)
        | i + 3, hty => exact absurd hty tyTok_argIdent_high
      · match i, hty with
        | 0, hty =>
          obtain ⟨-, rfl, hd⟩ := (tyTok_dom (.inr (.inl rfl))).1 hty
          rcases RT.ty_argSigma_iff.1 h₁ with hvac | ⟨D₁, E₁, D₂, E₂, hp₁, -, hd₁⟩
          · exact RT.of_vacuous hvac
          rcases RT.ty_argSigma_iff.1 h₂ with hvac | ⟨D₂', E₂', D₃, E₃, hp₂, -, hd₂⟩
          · exact RT.of_vacuous hvac
          obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hp₂.1 hp₁.2.1
          exact RT.ty_argSigma_iff.2 (.inr ⟨D₁, E₁, D₃, E₃, SigmaRed.trans levels hp₁ hp₂,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.transTy (sub (depth_lt_arg _ _ _ _)) hd (hd₁ rfl) (hd₂ rfl)⟩)
        | i + 1, hty => exact absurd hty tyTok_argSigma_succ
      · exact RT.ty_arg_other hk
  | fn k C Z W =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | hk
      · obtain ⟨-, hC, hZ, hW⟩ := (tyTok_family (.inl rfl)).1 hty
        rcases RT.ty_fnPi_iff.1 h₁ with hvac | ⟨D₁, E₁, D₂, E₂, hp₁, hc₁, hf₁, hg₁⟩
        · exact RT.of_vacuous hvac
        rcases RT.ty_fnPi_iff.1 h₂ with hvac | ⟨D₂', E₂', D₃, E₃, hp₂, hc₂, hf₂, hg₂⟩
        · exact RT.of_vacuous hvac
        obtain ⟨rfl, rfl⟩ := CRedTy.pi_align hp₂.1 hp₁.2.1
        have eD : CTypeEq P Γ D₁ D₂ := hp₁.2.2.1
        have zConv : ∀ {N₁ N₁' : CTm Head n}, (∀ z ∈ Z, RT H Γ true z D₁ N₁ N₁') →
            ∀ z ∈ Z, RT H Γ true z D₂ N₁ N₁' := fun hz z hzZ =>
          (IH.conv (sub (depth_lt_fn_left hzZ)) hC (hZ z hzZ) hc₁ eD).1 (hz z hzZ)
        exact RT.ty_fnPi_iff.2 (.inr ⟨D₁, E₁, D₃, E₃, PiRed.trans levels hp₁ hp₂,
          fun c hc => IH.transTy (sub (Tok.depth_lt_of_mem_dep (t := .fn .pi C Z W) hc))
            (hC c hc) (hc₁ c hc) (hc₂ c hc),
          fun N₁ N₁' hNN hz w hw => ⟨(hf₁ N₁ N₁' hNN hz w hw).1,
            (hf₂ N₁ N₁' (hNN.convType eD) (zConv hz) w hw).2⟩,
          fun N₁ tN hz w hw => IH.transTy (sub (depth_lt_fn_right hw)) (hW w hw)
            (hg₁ N₁ tN hz w hw) (hg₂ N₁ (tN.convType eD) (zConv hz) w hw)⟩)
      · exact absurd hty (tyTok_fn_other (by simp))
      · obtain ⟨-, hC, hZ, hW⟩ := (tyTok_family (.inr rfl)).1 hty
        rcases RT.ty_fnSigma_iff.1 h₁ with hvac | ⟨D₁, E₁, D₂, E₂, hp₁, hc₁, hf₁, hg₁⟩
        · exact RT.of_vacuous hvac
        rcases RT.ty_fnSigma_iff.1 h₂ with hvac | ⟨D₂', E₂', D₃, E₃, hp₂, hc₂, hf₂, hg₂⟩
        · exact RT.of_vacuous hvac
        obtain ⟨rfl, rfl⟩ := CRedTy.sigma_align hp₂.1 hp₁.2.1
        have eD : CTypeEq P Γ D₁ D₂ := hp₁.2.2.1
        have zConv : ∀ {N₁ N₁' : CTm Head n}, (∀ z ∈ Z, RT H Γ true z D₁ N₁ N₁') →
            ∀ z ∈ Z, RT H Γ true z D₂ N₁ N₁' := fun hz z hzZ =>
          (IH.conv (sub (depth_lt_fn_left hzZ)) hC (hZ z hzZ) hc₁ eD).1 (hz z hzZ)
        exact RT.ty_fnSigma_iff.2 (.inr ⟨D₁, E₁, D₃, E₃, SigmaRed.trans levels hp₁ hp₂,
          fun c hc => IH.transTy (sub (Tok.depth_lt_of_mem_dep (t := .fn .sigma C Z W) hc))
            (hC c hc) (hc₁ c hc) (hc₂ c hc),
          fun N₁ N₁' hNN hz w hw => ⟨(hf₁ N₁ N₁' hNN hz w hw).1,
            (hf₂ N₁ N₁' (hNN.convType eD) (zConv hz) w hw).2⟩,
          fun N₁ tN hz w hw => IH.transTy (sub (depth_lt_fn_right hw)) (hW w hw)
            (hg₁ N₁ tN hz w hw) (hg₂ N₁ (tN.convType eD) (zConv hz) w hw)⟩)
      · exact RT.ty_fn_other hk

end TypeLaws

/-! ## Symmetry and transitivity of the term relation -/

section TermLaws

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
  (formed : CCtxFormed P Γ)

include levels formed in
/-- **Symmetry of the term relation** at the tokens of depth below `N + 1`, at a type
related to itself as far as the type witness observes. -/
theorem LawsBelow.symm_step {N : Nat} (IH : LawsBelow H Γ N) {t : Tok} (ht : t.depth < N + 1)
    {a : List Tok} (ha : Ty a Elem.univ) (hta : TyTok a t) {T M M' : CTm Head n}
    (hT : ∀ s ∈ a, RT H Γ false s T T T) (h : RT H Γ true t T M M') : RT H Γ true t T M' M := by
  have sub : ∀ {s : Tok}, s.depth < t.depth → s.depth < N := fun h => by omega
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases htk : typeKind t.kind with
  | true =>
      have htyU := (tyTok_univ_of_typeKind htk hta).2
      rcases (RT.tm_type_iff htk).1 h with hvac | ⟨u, hu, hT', hr⟩ | ⟨hT', hr⟩
      · exact RT.of_vacuous hvac
      · exact (RT.tm_type_iff htk).2 (.inr (.inl ⟨u, hu, hT', IH.symmTy_step levels ht htyU hr⟩))
      · exact (RT.tm_type_iff htk).2 (.inr (.inr ⟨hT', IH.symmTy_step levels ht htyU hr⟩))
  | false =>
  cases t with
  | tag k =>
      cases k
      case refl =>
        obtain ⟨B, x, y, r, r', hr⟩ := RT.tm_reflTag_iff.1 h
        exact RT.tm_reflTag_iff.2 ⟨B, x, y, r', r, hr.symm⟩
      case zero =>
        obtain ⟨hT', r₁, r₂⟩ := RT.tm_zero_iff.1 h
        exact RT.tm_zero_iff.2 ⟨hT', r₂, r₁⟩
      case succ =>
        obtain ⟨m, m', hs⟩ := RT.tm_succTag_iff.1 h
        exact RT.tm_succTag_iff.2 ⟨m', m, hs.symm⟩
      case pair => exact absurd hta tyTok_tag_pair
      all_goals
        exact RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e)
          (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
  | arg k i C d =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk
      · exact RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) (by intro e; cases e)
          (fun e => Tok.noConfusion e) (by intro e; cases e) (by intro e; cases e)
      · match i, hta with
        | 0, hta =>
          obtain ⟨hid, rfl, hsa, -, -⟩ := tyTok_reflPoint.1 hta
          have hcarTy := ty_args_ident ha
          have hd : d.depth < N := sub (depth_lt_arg .refl 0 [] d)
          rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B, x, y, r, r', hr, -, hpts⟩
          · exact RT.of_vacuous hvac
          have selfB : ∀ q ∈ args .ident 0 a, RT H Γ false q B B B :=
            RT.ident_carrier (RT.ident_self hT hid hr.1) (fun q hq _ => hT q hq)
          obtain ⟨p1, p2, p3⟩ := hpts rfl
          have q : RT H Γ true d B r' r := IH.symm hd hcarTy hsa selfB p3
          exact RT.tm_argRefl_iff.2 (.inr ⟨B, x, y, r', r, hr.symm,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => ⟨IH.trans hd hcarTy hsa selfB q p1, IH.trans hd hcarTy hsa selfB q p2, q⟩⟩)
        | i + 1, hta => exact absurd hta tyTok_reflPoint_succ
      · match i, hta with
        | 0, hta =>
          obtain ⟨-, rfl, hsa⟩ := tyTok_pred.1 hta
          rcases RT.tm_argSucc_iff.1 h with hvac | ⟨m, m', hs, -, hd⟩
          · exact RT.of_vacuous hvac
          have selfNum : ∀ q ∈ a, RT H Γ false q (.const K.num) (.const K.num) (.const K.num) :=
            fun q hq => RT.reduce_ty levels hs.1 hs.1 (hT q hq)
          exact RT.tm_argSucc_iff.2 (.inr ⟨m', m, hs.symm, fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.symm (sub (depth_lt_arg _ _ _ _)) ha hsa selfNum (hd rfl)⟩)
        | i + 1, hta => exact absurd hta tyTok_pred_succ
      · match i, hta with
        | 0, hta =>
          obtain ⟨hsig, rfl, hsa⟩ := tyTok_fst.1 hta
          have hdomTy : Ty (args .sigma 0 a) Elem.univ := Ideal.ty_args_dom (.inr rfl) ha
          have hd : d.depth < N := sub (depth_lt_arg .pair 0 [] d)
          rcases RT.tm_argPair_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_argPair_iff.2 (.inr fun D E hTS => ?_)
          obtain ⟨e₀, -, h0, -⟩ := hcl D E hTS
          have selfD : ∀ q ∈ args .sigma 0 a, RT H Γ false q D D D :=
            RT.sigma_dom (RT.sigma_self hT hsig hTS) (fun q hq _ => hT q hq)
          exact ⟨.symm e₀, fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.symm hd hdomTy hsa selfD (h0 rfl), fun h1 => absurd h1 (by decide)⟩
        | 1, hta =>
          obtain ⟨hsig, hCty, hsa⟩ := tyTok_snd.1 hta
          have hdomTy : Ty (args .sigma 0 a) Elem.univ := Ideal.ty_args_dom (.inr rfl) ha
          have hfamTy : Ty (fnApp .sigma a C) Elem.univ := Ideal.ty_fnApp (.inr rfl) ha C
          have hd : d.depth < N := sub (depth_lt_arg .pair 1 C d)
          have hcd : ∀ c ∈ C, c.depth < N := fun c hc =>
            sub (Tok.depth_lt_of_mem_dep (t := .arg .pair 1 C d) hc)
          rcases RT.tm_argPair_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_argPair_iff.2 (.inr fun D E hTS => ?_)
          obtain ⟨e₀, hC, -, h1⟩ := hcl D E hTS
          have hp := RT.sigma_self hT hsig hTS
          have selfD : ∀ q ∈ args .sigma 0 a, RT H Γ false q D D D :=
            RT.sigma_dom hp (fun q hq _ => hT q hq)
          have hE : CIsType P (.snoc Γ D) E := ((CTypeEq.isType levels hTS.2 formed).2.sigma_parts).2
          obtain ⟨tM, tM'⟩ := CEqual.typed levels e₀ formed
          have hC' : ∀ c ∈ C, RT H Γ true c D (.fst M') (.fst M) := fun c hc =>
            IH.symm (hcd c hc) hdomTy (hCty c hc) selfD (hC c hc)
          refine ⟨.symm e₀, hC', fun h0 => absurd h0 (by decide), fun _ N₁ Q hQ hNQ => ?_⟩
          -- the relation at the family at the left first projection, turned around
          have base := IH.symm hd hfamTy hsa
            (RT.sigma_fam_at hp hT (.refl tM) (fun c hc => RT.left (hC c hc)))
            (h1 rfl (.fst M) (.fst M) (CRedTm.refl tM) (CRedTm.refl tM))
          -- the left first projection is related to the new argument
          have toN : ∀ c ∈ C, RT H Γ true c D (.fst M) N₁ := fun c hc =>
            IH.trans (hcd c hc) hdomTy (hCty c hc) selfD (hC c hc)
              (RT.retarget levels formed tM' (RT.left (hC' c hc)) hQ hNQ)
          have eMN : CEqual P Γ (.fst M) N₁ D := .trans e₀ (.trans hQ.2 (.symm hNQ.2))
          exact (IH.conv hd hfamTy hsa (RT.sigma_fam_at hp hT eMN toN)
            (hE.instantiateEq tM eMN)).1 base
        | i + 2, hta => exact absurd hta tyTok_pair_high
      · exact RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) hk.2.1
          (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2
  | fn k C X Y =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk
      · obtain ⟨hpi, -, -, hY⟩ := tyTok_lam.1 hta
        rcases RT.tm_lam_iff.1 h with hvac | hcl
        · exact RT.of_vacuous hvac
        refine RT.tm_lam_iff.2 (.inr fun D E hB => ?_)
        obtain ⟨hi, hii⟩ := hcl D E hB
        refine ⟨fun N₁ N₁' hNN hx y hy => ?_, fun N₁ tN hx y hy => ?_⟩
        · obtain ⟨h1, h2⟩ := hi N₁ N₁' hNN hx y hy
          exact ⟨h2, h1⟩
        · exact IH.symm (sub (depth_lt_fn_right hy)) (Ideal.ty_fnApp (.inl rfl) ha X) (hY y hy)
            (RT.pi_fam_at (RT.pi_self hT hpi hB) hT (.refl tN) hx) (hii N₁ tN hx y hy)
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
          (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2

include levels formed in
/-- **Transitivity of the term relation** at the tokens of depth below `N + 1`, at a
type related to itself as far as the type witness observes. -/
theorem LawsBelow.trans_step {N : Nat} (IH : LawsBelow H Γ N) {t : Tok} (ht : t.depth < N + 1)
    {a : List Tok} (ha : Ty a Elem.univ) (hta : TyTok a t) {T M₁ M₂ M₃ : CTm Head n}
    (hT : ∀ s ∈ a, RT H Γ false s T T T)
    (h₁ : RT H Γ true t T M₁ M₂) (h₂ : RT H Γ true t T M₂ M₃) : RT H Γ true t T M₁ M₃ := by
  have sub : ∀ {s : Tok}, s.depth < t.depth → s.depth < N := fun h => by omega
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases htk : typeKind t.kind with
  | true =>
      have htyU := (tyTok_univ_of_typeKind htk hta).2
      rcases (RT.tm_type_iff htk).1 h₁ with hvac | ⟨u, hu, hT', hr₁⟩ | ⟨hT', hr₁⟩
      · exact RT.of_vacuous hvac
      · rcases (RT.tm_type_iff htk).1 h₂ with hvac | ⟨_, -, -, hr₂⟩ | ⟨hT'', -⟩
        · exact RT.of_vacuous hvac
        · exact (RT.tm_type_iff htk).2
            (.inr (.inl ⟨u, hu, hT', IH.transTy_step levels ht htyU hr₁ hr₂⟩))
        · exact (CRedTy.head_ne_prop hT' hT'').elim
      · rcases (RT.tm_type_iff htk).1 h₂ with hvac | ⟨_, -, hT'', -⟩ | ⟨-, hr₂⟩
        · exact RT.of_vacuous hvac
        · exact (CRedTy.head_ne_prop hT'' hT').elim
        · exact (RT.tm_type_iff htk).2
            (.inr (.inr ⟨hT', IH.transTy_step levels ht htyU hr₁ hr₂⟩))
  | false =>
  cases t with
  | tag k =>
      cases k
      case refl =>
        obtain ⟨B, x, y, r₁, r₂, hr₁⟩ := RT.tm_reflTag_iff.1 h₁
        obtain ⟨_, _, _, _, r₃, hr₂⟩ := RT.tm_reflTag_iff.1 h₂
        exact RT.tm_reflTag_iff.2 ⟨B, x, y, r₁, r₃, hr₁.trans hr₂⟩
      case zero =>
        obtain ⟨hT', r₁, -⟩ := RT.tm_zero_iff.1 h₁
        obtain ⟨-, -, r₃⟩ := RT.tm_zero_iff.1 h₂
        exact RT.tm_zero_iff.2 ⟨hT', r₁, r₃⟩
      case succ =>
        obtain ⟨m₁, m₂, hs₁⟩ := RT.tm_succTag_iff.1 h₁
        obtain ⟨_, m₃, hs₂⟩ := RT.tm_succTag_iff.1 h₂
        exact RT.tm_succTag_iff.2 ⟨m₁, m₃, hs₁.trans hs₂⟩
      case pair => exact absurd hta tyTok_tag_pair
      all_goals
        exact RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e)
          (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
  | arg k i C d =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk
      · exact RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) (by intro e; cases e)
          (fun e => Tok.noConfusion e) (by intro e; cases e) (by intro e; cases e)
      · match i, hta with
        | 0, hta =>
          obtain ⟨hid, rfl, hsa, -, -⟩ := tyTok_reflPoint.1 hta
          have hcarTy := ty_args_ident ha
          have hd : d.depth < N := sub (depth_lt_arg .refl 0 [] d)
          rcases RT.tm_argRefl_iff.1 h₁ with hvac | ⟨B, x, y, r₁, r₂, hr₁, -, hpts₁⟩
          · exact RT.of_vacuous hvac
          rcases RT.tm_argRefl_iff.1 h₂ with hvac | ⟨B', x', y', r₂', r₃, hr₂, -, hpts₂⟩
          · exact RT.of_vacuous hvac
          obtain ⟨rfl, rfl, rfl⟩ := CRedTy.id_align hr₂.1 hr₁.1
          obtain rfl := CRedTm.refl_align hr₂.2.1 hr₁.2.2.1
          have selfB : ∀ q ∈ args .ident 0 a, RT H Γ false q B B B :=
            RT.ident_carrier (RT.ident_self hT hid hr₁.1) (fun q hq _ => hT q hq)
          obtain ⟨p1, p2, p3⟩ := hpts₁ rfl
          obtain ⟨-, -, q3⟩ := hpts₂ rfl
          exact RT.tm_argRefl_iff.2 (.inr ⟨B, x, y, r₁, r₃, hr₁.trans hr₂,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => ⟨p1, p2, IH.trans hd hcarTy hsa selfB p3 q3⟩⟩)
        | i + 1, hta => exact absurd hta tyTok_reflPoint_succ
      · match i, hta with
        | 0, hta =>
          obtain ⟨-, rfl, hsa⟩ := tyTok_pred.1 hta
          rcases RT.tm_argSucc_iff.1 h₁ with hvac | ⟨m₁, m₂, hs₁, -, hd₁⟩
          · exact RT.of_vacuous hvac
          rcases RT.tm_argSucc_iff.1 h₂ with hvac | ⟨m₂', m₃, hs₂, -, hd₂⟩
          · exact RT.of_vacuous hvac
          obtain rfl := CRedTm.suc_align hs₂.2.1 hs₁.2.2.1
          have selfNum : ∀ q ∈ a, RT H Γ false q (.const K.num) (.const K.num) (.const K.num) :=
            fun q hq => RT.reduce_ty levels hs₁.1 hs₁.1 (hT q hq)
          exact RT.tm_argSucc_iff.2 (.inr ⟨m₁, m₃, hs₁.trans hs₂,
            fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.trans (sub (depth_lt_arg _ _ _ _)) ha hsa selfNum (hd₁ rfl) (hd₂ rfl)⟩)
        | i + 1, hta => exact absurd hta tyTok_pred_succ
      · match i, hta with
        | 0, hta =>
          obtain ⟨hsig, rfl, hsa⟩ := tyTok_fst.1 hta
          have hdomTy : Ty (args .sigma 0 a) Elem.univ := Ideal.ty_args_dom (.inr rfl) ha
          have hd : d.depth < N := sub (depth_lt_arg .pair 0 [] d)
          rcases RT.tm_argPair_iff.1 h₁ with hvac | hcl₁
          · exact RT.of_vacuous hvac
          rcases RT.tm_argPair_iff.1 h₂ with hvac | hcl₂
          · exact RT.of_vacuous hvac
          refine RT.tm_argPair_iff.2 (.inr fun D E hTS => ?_)
          obtain ⟨e₁, -, h0₁, -⟩ := hcl₁ D E hTS
          obtain ⟨e₂, -, h0₂, -⟩ := hcl₂ D E hTS
          have selfD : ∀ q ∈ args .sigma 0 a, RT H Γ false q D D D :=
            RT.sigma_dom (RT.sigma_self hT hsig hTS) (fun q hq _ => hT q hq)
          exact ⟨.trans e₁ e₂, fun c hc => absurd hc List.not_mem_nil,
            fun _ => IH.trans hd hdomTy hsa selfD (h0₁ rfl) (h0₂ rfl),
            fun h1 => absurd h1 (by decide)⟩
        | 1, hta =>
          obtain ⟨hsig, hCty, hsa⟩ := tyTok_snd.1 hta
          have hdomTy : Ty (args .sigma 0 a) Elem.univ := Ideal.ty_args_dom (.inr rfl) ha
          have hfamTy : Ty (fnApp .sigma a C) Elem.univ := Ideal.ty_fnApp (.inr rfl) ha C
          have hd : d.depth < N := sub (depth_lt_arg .pair 1 C d)
          have hcd : ∀ c ∈ C, c.depth < N := fun c hc =>
            sub (Tok.depth_lt_of_mem_dep (t := .arg .pair 1 C d) hc)
          rcases RT.tm_argPair_iff.1 h₁ with hvac | hcl₁
          · exact RT.of_vacuous hvac
          rcases RT.tm_argPair_iff.1 h₂ with hvac | hcl₂
          · exact RT.of_vacuous hvac
          refine RT.tm_argPair_iff.2 (.inr fun D E hTS => ?_)
          obtain ⟨e₁, hC₁, -, h1₁⟩ := hcl₁ D E hTS
          obtain ⟨e₂, hC₂, -, h1₂⟩ := hcl₂ D E hTS
          have hp := RT.sigma_self hT hsig hTS
          have selfD : ∀ q ∈ args .sigma 0 a, RT H Γ false q D D D :=
            RT.sigma_dom hp (fun q hq _ => hT q hq)
          have hE : CIsType P (.snoc Γ D) E := ((CTypeEq.isType levels hTS.2 formed).2.sigma_parts).2
          obtain ⟨tM₁, tM₂⟩ := CEqual.typed levels e₁ formed
          refine ⟨.trans e₁ e₂, fun c hc => IH.trans (hcd c hc) hdomTy (hCty c hc) selfD
            (hC₁ c hc) (hC₂ c hc), fun h0 => absurd h0 (by decide), fun _ N₁ Q hQ hNQ => ?_⟩
          -- the new argument is related to the middle first projection, and to itself
          have selfN : ∀ c ∈ C, RT H Γ true c D N₁ N₁ := fun c hc =>
            RT.self_of_join levels formed (RT.left (hC₁ c hc)) hQ hNQ
          have midN : ∀ c ∈ C, RT H Γ true c D (.fst M₂) N₁ := fun c hc =>
            IH.trans (hcd c hc) hdomTy (hCty c hc) selfD
              (IH.symm (hcd c hc) hdomTy (hCty c hc) selfD (hC₁ c hc))
              (RT.retarget levels formed tM₁ (RT.left (hC₁ c hc)) hQ hNQ)
          have eMN : CEqual P Γ (.fst M₂) N₁ D := .trans (.symm e₁) (.trans hQ.2 (.symm hNQ.2))
          -- the second step, at the family at the middle first projection, moved to `N₁`
          have step₂ := (IH.conv hd hfamTy hsa (RT.sigma_fam_at hp hT eMN midN)
            (hE.instantiateEq tM₂ eMN)).1
            (h1₂ rfl (.fst M₂) (.fst M₂) (CRedTm.refl tM₂) (CRedTm.refl tM₂))
          exact IH.trans hd hfamTy hsa
            (RT.sigma_fam_at hp hT (CEqual.left hNQ.2) selfN)
            (h1₁ rfl N₁ Q hQ hNQ) step₂
        | i + 2, hta => exact absurd hta tyTok_pair_high
      · exact RT.tm_other htk (fun _ _ _ e => Tok.noConfusion e) hk.2.1
          (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2
  | fn k C X Y =>
      rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk
      · obtain ⟨hpi, -, -, hY⟩ := tyTok_lam.1 hta
        rcases RT.tm_lam_iff.1 h₁ with hvac | hcl₁
        · exact RT.of_vacuous hvac
        rcases RT.tm_lam_iff.1 h₂ with hvac | hcl₂
        · exact RT.of_vacuous hvac
        refine RT.tm_lam_iff.2 (.inr fun D E hB => ?_)
        obtain ⟨hi₁, hii₁⟩ := hcl₁ D E hB
        obtain ⟨hi₂, hii₂⟩ := hcl₂ D E hB
        exact ⟨fun N₁ N₁' hNN hx y hy =>
            ⟨(hi₁ N₁ N₁' hNN hx y hy).1, (hi₂ N₁ N₁' hNN hx y hy).2⟩,
          fun N₁ tN hx y hy => IH.trans (sub (depth_lt_fn_right hy))
            (Ideal.ty_fnApp (.inl rfl) ha X) (hY y hy)
            (RT.pi_fam_at (RT.pi_self hT hpi hB) hT (.refl tN) hx)
            (hii₁ N₁ tN hx y hy) (hii₂ N₁ tN hx y hy)⟩
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact absurd hta (tyTok_fn_other (by simp))
      · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
          (fun e => Tok.noConfusion e) hk.2.2.1 hk.2.2.2

end TermLaws

/-! ## The laws -/

section Final

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
  (formed : CCtxFormed P Γ)

include levels formed in
theorem LawsBelow.succ {N : Nat} (IH : LawsBelow H Γ N) : LawsBelow H Γ (N + 1) where
  conv ht _ ha hta _ _ _ _ hAB eAB := IH.conv_step levels formed ht ha hta hAB eAB
  symmTy ht hty _ _ h := IH.symmTy_step levels ht hty h
  transTy ht hty _ _ _ h₁ h₂ := IH.transTy_step levels ht hty h₁ h₂
  symm ht _ ha hta _ _ _ hT h := IH.symm_step levels formed ht ha hta hT h
  trans ht _ ha hta _ _ _ _ hT h₁ h₂ := IH.trans_step levels formed ht ha hta hT h₁ h₂

include levels formed in
/-- The laws hold at every depth. -/
theorem LawsBelow.all : ∀ N, LawsBelow H Γ N
  | 0 => LawsBelow.zero
  | N + 1 => (LawsBelow.all N).succ levels formed

include levels formed in
/-- **Conversion.** At a token typed at a type witness `a`, terms related at `A` are
related at `B` and back, when `A` and `B` are equal types related as far as `a`
observes. -/
theorem RT.conv_iff {t : Tok} {a : List Tok} (ha : Ty a Elem.univ) (hta : TyTok a t)
    {A B M M' : CTm Head n} (hAB : ∀ s ∈ a, RT H Γ false s A A B) (eAB : CTypeEq P Γ A B) :
    RT H Γ true t A M M' ↔ RT H Γ true t B M M' :=
  (LawsBelow.all levels formed (t.depth + 1)).conv (Nat.lt_succ_self _) ha hta hAB eAB

include levels formed in
/-- **Symmetry** of the type relation. -/
theorem RT.symm_ty {t : Tok} (hty : TyTok Elem.univ t) {A A' : CTm Head n}
    (h : RT H Γ false t A A A') : RT H Γ false t A' A' A :=
  (LawsBelow.all levels formed (t.depth + 1)).symmTy (Nat.lt_succ_self _) hty h

include levels formed in
/-- **Transitivity** of the type relation. -/
theorem RT.trans_ty {t : Tok} (hty : TyTok Elem.univ t) {A₁ A₂ A₃ : CTm Head n}
    (h₁ : RT H Γ false t A₁ A₁ A₂) (h₂ : RT H Γ false t A₂ A₂ A₃) : RT H Γ false t A₁ A₁ A₃ :=
  (LawsBelow.all levels formed (t.depth + 1)).transTy (Nat.lt_succ_self _) hty h₁ h₂

include levels formed in
/-- **Symmetry** of the term relation, at a type related to itself as far as the type
witness observes. -/
theorem RT.symm {t : Tok} {a : List Tok} (ha : Ty a Elem.univ) (hta : TyTok a t)
    {T M M' : CTm Head n} (hT : ∀ s ∈ a, RT H Γ false s T T T) (h : RT H Γ true t T M M') :
    RT H Γ true t T M' M :=
  (LawsBelow.all levels formed (t.depth + 1)).symm (Nat.lt_succ_self _) ha hta hT h

include levels formed in
/-- **Transitivity** of the term relation, at a type related to itself as far as the
type witness observes. -/
theorem RT.trans {t : Tok} {a : List Tok} (ha : Ty a Elem.univ) (hta : TyTok a t)
    {T M₁ M₂ M₃ : CTm Head n} (hT : ∀ s ∈ a, RT H Γ false s T T T)
    (h₁ : RT H Γ true t T M₁ M₂) (h₂ : RT H Γ true t T M₂ M₃) : RT H Γ true t T M₁ M₃ :=
  (LawsBelow.all levels formed (t.depth + 1)).trans (Nat.lt_succ_self _) ha hta hT h₁ h₂

end Final

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
