import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Compact

/-!
# Semantic typing of compact elements

The semantic typing of the domain model (Carneiro, Coquand, Frabetti Mathieu,
Lennon-Bertrand, Melliès and Weirich, *Definitional Inversion, Without
Normalisation*, §2.2) says when a compact element `u` is an element of a compact
type `a`. It is stated here for single tokens (`TyTok a t`), and an element is
typed when each of its tokens is (`Ty u a`). A token's dependency makes this
possible: the family entry of a dependent type records the domain its input is
typed at, the endpoints of an identity type record the carrier, and the second
projection of a pair records the first.

The clauses:

* the universe, the universe of codes, ground types, the numbers and the
  dependent and identity types are elements of the universe and of the universe
  of codes (`U : U`; the universe of codes has every type as element);
* the domain of a dependent type is a type; a family entry maps elements of the
  domain to types; the carrier of an identity type is a type and its endpoints
  are elements of the carrier;
* zero and successors are numbers;
* reflexivity at a point `w` is an element of an identity type when `w` is an
  element of the carrier below both endpoints;
* a function entry maps elements of the domain to elements of the family's value;
* the first projection of a pair is an element of the domain, and the second an
  element of the family's value at the first.

This is the intensional form of the typing of the paper (its Proposition 2.15):
a function is typed by a presentation whose inputs are all typed. Typing is
monotone in the type (`TyTok.mono`, the paper's Proposition 2.17), and the
typed elements of a type are closed under joins by definition. The least
element is an element of every type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

/-- The elements of `a` are types: `a` is the universe or the universe of codes. -/
def IsUniv (a : List Tok) : Prop := Tok.tag .univ ∈ a ∨ Tok.tag .codes ∈ a

/-- The type formers: the kinds whose elements are types. -/
def Kind.IsFormer : Kind → Prop
  | .univ | .ground | .codes | .nat | .pi | .sigma | .ident => True
  | _ => False

/-- The typing of a token at a type. -/
def TyTok (a : List Tok) : Tok → Prop
  | .tag k =>
      match k with
      | .univ | .ground | .codes | .nat | .pi | .sigma | .ident => IsUniv a
      | .zero | .succ => Tok.tag .nat ∈ a
      | .refl => Tok.tag .ident ∈ a
      | .lam | .pair => False
  | .arg k i C t =>
      match k, i with
      | .pi, 0 | .sigma, 0 | .ident, 0 => IsUniv a ∧ C = [] ∧ TyTok Elem.univ t
      | .ident, 1 | .ident, 2 =>
          IsUniv a ∧ (∀ c ∈ C.attach, TyTok Elem.univ c.1) ∧ TyTok C t
      | .succ, 0 => Tok.tag .nat ∈ a ∧ C = [] ∧ TyTok a t
      | .refl, 0 => Tok.tag .ident ∈ a ∧ C = [] ∧ TyTok (args .ident 0 a) t ∧
          ent (args .ident 1 a) t = true ∧ ent (args .ident 2 a) t = true
      | .pair, 0 => Tok.tag .sigma ∈ a ∧ C = [] ∧ TyTok (args .sigma 0 a) t
      | .pair, 1 => Tok.tag .sigma ∈ a ∧ (∀ c ∈ C.attach, TyTok (args .sigma 0 a) c.1) ∧
          TyTok (fnApp .sigma a C) t
      | _, _ => False
  | .fn k C X Y =>
      match k with
      | .pi | .sigma => IsUniv a ∧ (∀ c ∈ C.attach, TyTok Elem.univ c.1) ∧
          (∀ x ∈ X.attach, TyTok C x.1) ∧ ∀ y ∈ Y.attach, TyTok Elem.univ y.1
      | .lam => Tok.tag .pi ∈ a ∧ C = [] ∧ (∀ x ∈ X.attach, TyTok (args .pi 0 a) x.1) ∧
          ∀ y ∈ Y.attach, TyTok (fnApp .pi a X) y.1
      | _ => False
termination_by t => t.depth
decreasing_by
  all_goals first
    | exact depth_lt_arg _ _ _ _
    | exact Tok.depth_lt_of_mem_dep (t := .arg _ _ _ _) c.2
    | exact Tok.depth_lt_of_mem_dep (t := .fn _ _ _ _) c.2
    | exact depth_lt_fn_left x.2
    | exact depth_lt_fn_right y.2

/-- A compact element is an element of a type when each of its tokens is. -/
def Ty (u a : List Tok) : Prop := ∀ t ∈ u, TyTok a t

/-! ## The clauses -/

section Clauses

variable {a : List Tok}

private theorem forall_attach {P : Tok → Prop} {l : List Tok} :
    (∀ c ∈ l.attach, P c.1) ↔ ∀ c ∈ l, P c := by
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem tyTok_tag_former {k : Kind} (hk : k.IsFormer) : TyTok a (.tag k) ↔ IsUniv a := by
  cases k <;> first | exact absurd hk id | (rw [TyTok])

theorem tyTok_tag_zero : TyTok a (.tag .zero) ↔ Tok.tag .nat ∈ a := by rw [TyTok]
theorem tyTok_tag_succ : TyTok a (.tag .succ) ↔ Tok.tag .nat ∈ a := by rw [TyTok]
theorem tyTok_tag_refl : TyTok a (.tag .refl) ↔ Tok.tag .ident ∈ a := by rw [TyTok]
theorem tyTok_tag_lam : ¬ TyTok a (.tag .lam) := by rw [TyTok]; exact id
theorem tyTok_tag_pair : ¬ TyTok a (.tag .pair) := by rw [TyTok]; exact id

theorem tyTok_dom {k : Kind} (hk : k = .pi ∨ k = .sigma ∨ k = .ident) {C : List Tok} {t : Tok} :
    TyTok a (.arg k 0 C t) ↔ IsUniv a ∧ C = [] ∧ TyTok Elem.univ t := by
  rcases hk with rfl | rfl | rfl <;> rw [TyTok]

theorem tyTok_endpoint {i : Nat} (hi : i = 1 ∨ i = 2) {C : List Tok} {t : Tok} :
    TyTok a (.arg .ident i C t) ↔
      IsUniv a ∧ (∀ c ∈ C, TyTok Elem.univ c) ∧ TyTok C t := by
  rcases hi with rfl | rfl <;> (rw [TyTok]; rw [forall_attach])

theorem tyTok_pred {C : List Tok} {t : Tok} :
    TyTok a (.arg .succ 0 C t) ↔ Tok.tag .nat ∈ a ∧ C = [] ∧ TyTok a t := by
  rw [TyTok]

theorem tyTok_reflPoint {C : List Tok} {t : Tok} :
    TyTok a (.arg .refl 0 C t) ↔ Tok.tag .ident ∈ a ∧ C = [] ∧ TyTok (args .ident 0 a) t ∧
      ent (args .ident 1 a) t = true ∧ ent (args .ident 2 a) t = true := by
  rw [TyTok]

theorem tyTok_fst {C : List Tok} {t : Tok} :
    TyTok a (.arg .pair 0 C t) ↔ Tok.tag .sigma ∈ a ∧ C = [] ∧ TyTok (args .sigma 0 a) t := by
  rw [TyTok]

theorem tyTok_snd {C : List Tok} {t : Tok} :
    TyTok a (.arg .pair 1 C t) ↔ Tok.tag .sigma ∈ a ∧ (∀ c ∈ C, TyTok (args .sigma 0 a) c) ∧
      TyTok (fnApp .sigma a C) t := by
  rw [TyTok, forall_attach]

theorem tyTok_family {k : Kind} (hk : k = .pi ∨ k = .sigma) {C X Y : List Tok} :
    TyTok a (.fn k C X Y) ↔ IsUniv a ∧ (∀ c ∈ C, TyTok Elem.univ c) ∧
      (∀ x ∈ X, TyTok C x) ∧ ∀ y ∈ Y, TyTok Elem.univ y := by
  rcases hk with rfl | rfl <;> (rw [TyTok]; simp only [forall_attach])

theorem tyTok_lam {C X Y : List Tok} :
    TyTok a (.fn .lam C X Y) ↔ Tok.tag .pi ∈ a ∧ C = [] ∧ (∀ x ∈ X, TyTok (args .pi 0 a) x) ∧
      ∀ y ∈ Y, TyTok (fnApp .pi a X) y := by
  rw [TyTok]; simp only [forall_attach]

/-- The components that tokens may type: the domain of a dependent type, the
carrier and endpoints of an identity type, the predecessor of a successor, the
point of reflexivity, and the projections of a pair. -/
def argSlots : List (Kind × Nat) :=
  [(.pi, 0), (.sigma, 0), (.ident, 0), (.ident, 1), (.ident, 2), (.succ, 0), (.refl, 0),
    (.pair, 0), (.pair, 1)]

/-- The component tokens that are typed nowhere. -/
theorem tyTok_arg_other {k : Kind} {i : Nat} {C : List Tok} {t : Tok} (h : (k, i) ∉ argSlots) :
    ¬ TyTok a (.arg k i C t) := by
  rw [TyTok]
  · exact id
  all_goals rintro rfl rfl; exact h (by decide)

theorem tyTok_fn_other {k : Kind} {C X Y : List Tok}
    (h : k ≠ .pi ∧ k ≠ .sigma ∧ k ≠ .lam) : ¬ TyTok a (.fn k C X Y) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [TyTok]
  · exact id
  all_goals rintro rfl; simp_all

end Clauses

/-! ## Monotonicity in the type -/

theorem mem_of_le {k : Kind} {a a' : List Tok} (h : a ⊑ a') (hk : Tok.tag k ∈ a) :
    Tok.tag k ∈ a' := by
  have := h _ hk
  rwa [ent_tag, hasTag_iff] at this

theorem IsUniv.mono {a a' : List Tok} (h : a ⊑ a') (hu : IsUniv a) : IsUniv a' :=
  hu.imp (mem_of_le h) (mem_of_le h)

/-- The shapes of step-function tokens. -/
theorem fn_cases (k : Kind) :
    (k = .pi ∨ k = .sigma) ∨ k = .lam ∨ (k ≠ .pi ∧ k ≠ .sigma ∧ k ≠ .lam) := by
  cases k <;> simp

/-- The kinds of tags. -/
theorem tag_cases (k : Kind) :
    k.IsFormer ∨ k = .zero ∨ k = .succ ∨ k = .refl ∨ k = .lam ∨ k = .pair := by
  cases k <;> simp [Kind.IsFormer]

/-- **Typing is monotone in the type.** -/
theorem TyTok.mono : ∀ {t : Tok} {a a' : List Tok}, a ⊑ a' → TyTok a t → TyTok a' t
  | .tag k, _, _, h, ht => by
      rcases tag_cases k with hk | rfl | rfl | rfl | rfl | rfl
      · exact (tyTok_tag_former hk).2 (((tyTok_tag_former hk).1 ht).mono h)
      · exact tyTok_tag_zero.2 (mem_of_le h (tyTok_tag_zero.1 ht))
      · exact tyTok_tag_succ.2 (mem_of_le h (tyTok_tag_succ.1 ht))
      · exact tyTok_tag_refl.2 (mem_of_le h (tyTok_tag_refl.1 ht))
      · exact absurd ht tyTok_tag_lam
      · exact absurd ht tyTok_tag_pair
  | .arg k i C t, _, _, h, ht => by
      rcases Decidable.em ((k, i) ∈ argSlots) with hs | hother
      swap
      · exact absurd ht (tyTok_arg_other hother)
      simp only [argSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hu, hC, ht⟩ := (tyTok_dom (.inl rfl)).1 ht
        exact (tyTok_dom (.inl rfl)).2 ⟨hu.mono h, hC, ht⟩
      · obtain ⟨hu, hC, ht⟩ := (tyTok_dom (.inr (.inl rfl))).1 ht
        exact (tyTok_dom (.inr (.inl rfl))).2 ⟨hu.mono h, hC, ht⟩
      · obtain ⟨hu, hC, ht⟩ := (tyTok_dom (.inr (.inr rfl))).1 ht
        exact (tyTok_dom (.inr (.inr rfl))).2 ⟨hu.mono h, hC, ht⟩
      · obtain ⟨hu, hC, ht⟩ := (tyTok_endpoint (.inl rfl)).1 ht
        exact (tyTok_endpoint (.inl rfl)).2 ⟨hu.mono h, hC, ht⟩
      · obtain ⟨hu, hC, ht⟩ := (tyTok_endpoint (.inr rfl)).1 ht
        exact (tyTok_endpoint (.inr rfl)).2 ⟨hu.mono h, hC, ht⟩
      · obtain ⟨hn, hC, ht⟩ := tyTok_pred.1 ht
        exact tyTok_pred.2 ⟨mem_of_le h hn, hC, TyTok.mono h ht⟩
      · obtain ⟨hn, hC, ht, h1, h2⟩ := tyTok_reflPoint.1 ht
        exact tyTok_reflPoint.2 ⟨mem_of_le h hn, hC, TyTok.mono (h.args _ _) ht,
          ent_cut h1 (h.args _ _), ent_cut h2 (h.args _ _)⟩
      · obtain ⟨hn, hC, ht⟩ := tyTok_fst.1 ht
        exact tyTok_fst.2 ⟨mem_of_le h hn, hC, TyTok.mono (h.args _ _) ht⟩
      · obtain ⟨hn, hC, ht⟩ := tyTok_snd.1 ht
        exact tyTok_snd.2 ⟨mem_of_le h hn, fun c hc => TyTok.mono (h.args _ _) (hC c hc),
          TyTok.mono (fnApp_mono h (Le.refl C)) ht⟩
  | .fn k C X Y, _, _, h, ht => by
      rcases fn_cases k with hk | rfl | hother
      · obtain ⟨hu, hC, hX, hY⟩ := (tyTok_family hk).1 ht
        exact (tyTok_family hk).2 ⟨hu.mono h, hC, hX, hY⟩
      · obtain ⟨hp, hC, hX, hY⟩ := tyTok_lam.1 ht
        exact tyTok_lam.2 ⟨mem_of_le h hp, hC, fun x hx => TyTok.mono (h.args _ _) (hX x hx),
          fun y hy => TyTok.mono (fnApp_mono h (Le.refl X)) (hY y hy)⟩
      · exact absurd ht (tyTok_fn_other hother)
termination_by t => t.depth
decreasing_by
  all_goals first
    | exact depth_lt_arg _ _ _ _
    | exact Tok.depth_lt_of_mem_dep (t := .arg _ _ _ _) hc
    | exact depth_lt_fn_left hx
    | exact depth_lt_fn_right hy

theorem Ty.mono {u a a' : List Tok} (h : a ⊑ a') (hu : Ty u a) : Ty u a' :=
  fun t ht => (hu t ht).mono h

theorem Ty.nil (a : List Tok) : Ty [] a := fun _ ht => absurd ht List.not_mem_nil

theorem Ty.append {u v a : List Tok} (hu : Ty u a) (hv : Ty v a) : Ty (u ++ v) a := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact hu t ht
  · exact hv t ht

theorem Ty.of_subset {u v a : List Tok} (h : ∀ t ∈ u, t ∈ v) (hv : Ty v a) : Ty u a :=
  fun t ht => hv t (h t ht)

/-! ## The typing of the elements -/

namespace Elem

theorem ty_map_iff {α : Type} {l : List α} {f : α → Tok} {a : List Tok} :
    Ty (l.map f) a ↔ ∀ x ∈ l, TyTok a (f x) := by
  simp only [Ty, List.mem_map, forall_exists_index, and_imp]
  exact ⟨fun h x hx => h _ x hx rfl, fun h _ x hx e => e ▸ h x hx⟩

/-- A tag element is a type when its kind is a type former and the type is a
universe. -/
theorem ty_tag {k : Kind} (hk : k.IsFormer) {a : List Tok} (ha : IsUniv a) : Ty [.tag k] a := by
  intro t ht
  rw [List.mem_singleton.1 ht]
  exact (tyTok_tag_former hk).2 ha

theorem isUniv_univ : IsUniv univ := .inl List.mem_cons_self

theorem isUniv_codes : IsUniv codes := .inr List.mem_cons_self

/-- The universe is an element of itself. -/
theorem ty_univ_univ : Ty univ univ := ty_tag (k := .univ) trivial isUniv_univ

/-- A dependent type is a type when its domain is and its family maps elements
of the domain to types. -/
theorem ty_former {k : Kind} (hk : k = .pi ∨ k = .sigma) {a b : List Tok}
    {f : List (List Tok × List Tok)} (hb : IsUniv b) (ha : Ty a univ)
    (hf : ∀ p ∈ f, Ty p.1 a ∧ Ty p.2 univ) : Ty (former k a f) b := by
  intro t ht
  simp only [former, List.mem_cons, List.mem_append, List.mem_map] at ht
  rcases ht with rfl | ⟨s, hs, rfl⟩ | ⟨p, hp, rfl⟩
  · exact (tyTok_tag_former (by rcases hk with rfl | rfl <;> trivial)).2 hb
  · exact (tyTok_dom (by rcases hk with rfl | rfl <;> simp)).2 ⟨hb, rfl, ha s hs⟩
  · exact (tyTok_family hk).2 ⟨hb, ha, (hf p hp).1, (hf p hp).2⟩

/-- The typing of a function: its entries map elements of the domain to
elements of the family's values. -/
theorem ty_lam {f : List (List Tok × List Tok)} {a : List Tok} (hp : Tok.tag .pi ∈ a) :
    Ty (lam f) a ↔ ∀ p ∈ f, Ty p.1 (args .pi 0 a) ∧ Ty p.2 (fnApp .pi a p.1) := by
  rw [lam, ty_map_iff]
  simp only [tyTok_lam, hp, true_and]
  rfl

theorem ty_zero {a : List Tok} (h : Tok.tag .nat ∈ a) : Ty zero a := by
  intro t ht
  rw [List.mem_singleton.1 ht]
  exact tyTok_tag_zero.2 h

theorem ty_succ {u a : List Tok} (h : Tok.tag .nat ∈ a) : Ty (succ u) a ↔ Ty u a := by
  simp only [succ, Ty, List.mem_cons, forall_eq_or_imp, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, tyTok_tag_succ, h, true_and, tyTok_pred]

/-- The typing of a pair: its first component is an element of the domain, and
its second an element of the family's value at the first. -/
theorem ty_pair {u v a : List Tok} (h : Tok.tag .sigma ∈ a) (hu : Ty u (args .sigma 0 a))
    (hv : Ty v (fnApp .sigma a u)) : Ty (pair u v) a := by
  simp only [pair, Ty, List.mem_append, List.mem_map]
  rintro t (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
  · exact tyTok_fst.2 ⟨h, rfl, hu s hs⟩
  · exact tyTok_snd.2 ⟨h, hu, hv s hs⟩

theorem ty_pair_fst {u v a : List Tok} (hty : Ty (pair u v) a) : Ty u (args .sigma 0 a) := by
  intro s hs
  exact (tyTok_fst.1 (hty _ (List.mem_append_left _ (List.mem_map_of_mem hs)))).2.2

theorem ty_pair_snd {u v a : List Tok} (hty : Ty (pair u v) a) : Ty v (fnApp .sigma a u) := by
  intro s hs
  exact (tyTok_snd.1 (hty _ (List.mem_append_right _ (List.mem_map_of_mem hs)))).2.2

theorem ty_refl {w a : List Tok} (h : Tok.tag .ident ∈ a) :
    Ty (refl w) a ↔ Ty w (args .ident 0 a) ∧ w ⊑ args .ident 1 a ∧ w ⊑ args .ident 2 a := by
  simp only [refl, Ty, List.mem_cons, forall_eq_or_imp, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, tyTok_tag_refl, h, true_and, tyTok_reflPoint, Le]
  constructor
  · intro hw
    exact ⟨fun t ht => (hw t ht).1, fun t ht => (hw t ht).2.1, fun t ht => (hw t ht).2.2⟩
  · rintro ⟨h0, h1, h2⟩ t ht
    exact ⟨h0 t ht, h1 t ht, h2 t ht⟩

theorem ty_ident {c u v b : List Tok} (hb : IsUniv b) (hc : Ty c univ) (hu : Ty u c)
    (hv : Ty v c) : Ty (ident c u v) b := by
  intro t ht
  simp only [ident, List.mem_cons, List.mem_append, List.mem_map] at ht
  rcases ht with rfl | (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
  · exact (tyTok_tag_former (k := .ident) trivial).2 hb
  · exact (tyTok_dom (by simp)).2 ⟨hb, rfl, hc s hs⟩
  · exact (tyTok_endpoint (.inl rfl)).2 ⟨hb, hc, hu s hs⟩
  · exact (tyTok_endpoint (.inr rfl)).2 ⟨hb, hc, hv s hs⟩

end Elem

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
