import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CodomainNarrowingControls

/-!
# Meet narrowing: several domains and several codomains

In `X par ≐ t`, every solution gives an unknown `W` of the pattern `t` a body that is seen twice: by `W`'s own
declaration `Sort (dom W) ⟶ Sort (cod W)`, and, as part of `X`'s body, at `Sort (dom X) ⟶ Sort (cod X)`. The body
is then a code of the **meet** of the two views, `Sort (max (dom X) (dom W)) ⟶ Sort (min (cod X) (cod W))`, as soon
as the two declarations are **compatible**: the larger domain is at most the smaller codomain, or one of the two
admits no parameter (`Ty.meet`). Meet narrowing replaces `W` by `W' par`, with `W'` a new unknown declared at the meet
(`meetAssign`, `meet_exact`, `meet_forced_left`). It raises a domain and lowers a codomain at once; the narrowing of
`CodomainNarrowing` is its case with one domain.

The solver with meet narrowing, its termination, its decision on the fragment of compatible groups, and the
controls are in `MeetSolver`. Two declarations with one domain are always compatible (`Meet.one_domain_compatible`),
and so are the two of `CodomainNarrowingControls.domain_raising`. The cross store at `a < b` and the store of
`domain_needed` have incompatible declarations that both admit the parameter (`Meet.cross_incompatible`,
`Meet.domain_needed_incompatible`); on the second, meet narrowing loses a solution (`Meet.meet_needs_compatible`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

variable {v : Nat → Nat}

/-! ## The meet of two views -/

/-- **The meet of two views of one code**: a code of `Sort l` over a parameter of `Sort p` and of `Sort l'` over a
parameter of `Sort q` is a code of `Sort (min l l')` over a parameter of `Sort (max p q)`, when the larger domain is
at most the smaller codomain or one of the views admits no parameter. -/
theorem Ty.meet {Γ : Ctx} {p q : Nat} {b : Tm} {l : Nat} (one : Ty v Γ p b l) :
    ∀ {l' : Nat}, Ty v Γ q b l' → (max p q ≤ min l l' ∨ l < p ∨ l' < q) → Ty v Γ (max p q) b (min l l') := by
  induction one with
  | par h =>
      intro l' two cond
      have h' := Ty.par_inv two
      rcases cond with c | c | c
      · exact .par c
      · omega
      · omega
  | gnd => exact fun _ _ => .gnd
  | sort h =>
      intro l' two _
      cases two with
      | sort h' => exact .sort (le_min h h')
  | arr _ _ ihA ihB =>
      intro l' two cond
      obtain ⟨tA, tB⟩ := Ty.arr_inv two
      exact .arr (ihA tA cond) (ihB tB cond)
  | @app W t d l hW _ hc ih =>
      intro l' two _
      obtain ⟨d', hW', ht', hc'⟩ := Ty.app_inv two
      rw [hW] at hW'
      cases hW'
      have cond' : max p q ≤ min (Level.value v d.dom) (Level.value v d.dom) ∨ Level.value v d.dom < p ∨
          Level.value v d.dom < q := by
        by_cases h1 : p ≤ Level.value v d.dom
        · by_cases h2 : q ≤ Level.value v d.dom
          · exact Or.inl (by rw [min_self]; exact max_le h1 h2)
          · exact Or.inr (Or.inr (Nat.lt_of_not_le h2))
        · exact Or.inr (Or.inl (Nat.lt_of_not_le h1))
      have arg := ih ht' cond'
      rw [min_self] at arg
      exact .app hW arg (le_min hc hc')

/-- Two declarations are **compatible** when the larger domain is at most the smaller codomain, or one of them admits
no parameter. -/
def Compatible (v : Nat → Nat) (dX dW : Decl) : Prop :=
  max (Level.value v dX.dom) (Level.value v dW.dom) ≤ min (Level.value v dX.cod) (Level.value v dW.cod) ∨
    Level.value v dX.cod < Level.value v dX.dom ∨ Level.value v dW.cod < Level.value v dW.dom

theorem Compatible.symm {dX dW : Decl} (h : Compatible v dX dW) : Compatible v dW dX := by
  unfold Compatible at h ⊢
  rw [max_comm, min_comm]
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem Compatible.refl (d : Decl) : Compatible v d d := by
  unfold Compatible
  rw [max_self, min_self]
  by_cases h : Level.value v d.dom ≤ Level.value v d.cod
  · exact Or.inl h
  · exact Or.inr (Or.inl (Nat.lt_of_not_le h))

/-- **The meet declaration**: the larger domain and, at the valuation, the smaller codomain. -/
def meetDecl (v : Nat → Nat) (dX dW : Decl) : Decl :=
  ⟨.max dX.dom dW.dom, if Level.value v dX.cod ≤ Level.value v dW.cod then dX.cod else dW.cod⟩

theorem meetDecl_dom (dX dW : Decl) :
    Level.value v (meetDecl v dX dW).dom = max (Level.value v dX.dom) (Level.value v dW.dom) := rfl

theorem meetDecl_cod (dX dW : Decl) :
    Level.value v (meetDecl v dX dW).cod = min (Level.value v dX.cod) (Level.value v dW.cod) := by
  unfold meetDecl
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))).symm

/-- **The meet is compatible with every declaration compatible with both.** -/
theorem compatible_meet {dX dW dV : Decl} (xv : Compatible v dX dV) (wv : Compatible v dW dV) :
    Compatible v (meetDecl v dX dW) dV := by
  unfold Compatible at xv wv ⊢
  rw [meetDecl_dom, meetDecl_cod]
  omega

/-! ## Meet narrowing -/

theorem getElem?_append_old {Δ : Ctx} {d : Decl} {V : Nat} (h : V < Δ.length) : (Δ ++ [d])[V]? = Δ[V]? :=
  List.getElem?_append_left h

theorem getElem?_append_new {Δ : Ctx} {d : Decl} : (Δ ++ [d])[Δ.length]? = some d := by
  simp

theorem lt_of_append {Δ : Ctx} {d e : Decl} {V : Nat} (h : (Δ ++ [d])[V]? = some e) (ne : V ≠ Δ.length) :
    V < Δ.length := by
  have lt := (List.getElem?_eq_some_iff.mp h).1
  simp only [List.length_append, List.length_cons, List.length_nil] at lt
  omega

/-- **The meet narrowing morphism**: `W := W' par` with `W'` the new last unknown, the identity elsewhere. -/
def meetAssign (v : Nat → Nat) {Δ : Ctx} {W : Nat} {dW : Decl} (d' : Decl) (hW : Δ[W]? = some dW)
    (dom : Level.value v dW.dom ≤ Level.value v d'.dom) (cod : Level.value v d'.cod ≤ Level.value v dW.cod) :
    Assign v Δ (Δ ++ [d']) :=
  ⟨Function.update Tm.idA W (.app Δ.length .par), fun V d hV => by
    by_cases h : V = W
    · subst h
      rw [Function.update_self]
      rw [hW] at hV
      cases hV
      exact .app getElem?_append_new (.par dom) cod
    · rw [Function.update_of_ne h]
      exact .app (by rw [getElem?_append_old (lt_length_of_getElem? hV)]; exact hV) (.par le_rfl) le_rfl⟩

/-- **Meet narrowing is exact** as soon as every solution sends `W` to a code of the new declaration. -/
theorem meet_exact {Δ : Ctx} {S : EquationStore (Term Δ)} {W : Nat} {d' : Decl} {σ : Assign v Δ (Δ ++ [d'])}
    (hσ : σ.1 = Function.update Tm.idA W (.app Δ.length .par))
    (forced : ∀ (Γ : Ctx) (f : Assign v Δ Γ), (frames v).Models f S →
      Ty v Γ (Level.value v d'.dom) (f.1 W) (Level.value v d'.cod)) :
    Exact (frames v) S σ ((frames v).applyStore σ S) := by
  apply (exact_applyStore_iff S σ).mpr
  intro Γ f solved
  let body : Nat → Tm := fun V => if V = Δ.length then f.1 W else f.1 V
  have typed : TyA v (Δ ++ [d']) Γ body := by
    intro V d hV
    by_cases hV' : V = Δ.length
    · subst hV'
      rw [getElem?_append_new] at hV
      cases hV
      simp only [body, if_pos rfl]
      exact forced Γ f solved
    · rw [getElem?_append_old (lt_of_append hV hV')] at hV
      simp only [body, if_neg hV']
      exact f.2 V d hV
  refine ⟨⟨body, typed⟩, agree_of_unknowns fun V hV => ?_⟩
  show Tm.lower v (f.1 V) = Tm.lower v (Tm.act body (σ.1 V))
  rw [hσ]
  by_cases hVW : V = W
  · subst hVW
    rw [Function.update_self, act_app_par]
    simp only [body, if_pos rfl]
  · rw [Function.update_of_ne hVW]
    show Tm.lower v (f.1 V) = Tm.lower v (Tm.act body (.app V .par))
    rw [act_app_par]
    simp only [body, if_neg (Nat.ne_of_lt hV)]

/-- **What `X par ≐ t` forces, with compatible declarations**: every solution sends an unknown `W` of the pattern
`t` to a code of the meet of `X`'s and `W`'s declarations. -/
theorem meet_forced_left {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat}
    {dX dW : Decl} (hl : e.1.1 = .app X .par) (hp : Tm.Pattern e.2.1) (hWm : W ∈ Tm.unknowns e.2.1)
    (hX : Δ[X]? = some dX) (hW : Δ[W]? = some dW) (compat : Compatible v dX dW) (Γ : Ctx) (f : Assign v Δ Γ)
    (solved : (frames v).Models f (e :: S)) :
    Ty v Γ (Level.value v (meetDecl v dX dW).dom) (f.1 W) (Level.value v (meetDecl v dX dW).cod) := by
  have same := solves_head solved
  rw [hl, act_app_par] at same
  have viewX := Ty.of_pattern_mem hp hWm (Ty.of_lower_eq same (f.2 X dX hX))
  rw [meetDecl_dom, meetDecl_cod]
  exact Ty.meet viewX (f.2 W dW hW) compat

theorem meet_forced_right {Δ : Ctx} {e : Equation (Term Δ)} {S : EquationStore (Term Δ)} {X W : Nat}
    {dX dW : Decl} (hr : e.2.1 = .app X .par) (hp : Tm.Pattern e.1.1) (hWm : W ∈ Tm.unknowns e.1.1)
    (hX : Δ[X]? = some dX) (hW : Δ[W]? = some dW) (compat : Compatible v dX dW) (Γ : Ctx) (f : Assign v Δ Γ)
    (solved : (frames v).Models f (e :: S)) :
    Ty v Γ (Level.value v (meetDecl v dX dW).dom) (f.1 W) (Level.value v (meetDecl v dX dW).cod) := by
  have same := solves_head solved
  rw [hr, act_app_par] at same
  have viewX := Ty.of_pattern_mem hp hWm (Ty.of_lower_eq same.symm (f.2 X dX hX))
  rw [meetDecl_dom, meetDecl_cod]
  exact Ty.meet viewX (f.2 W dW hW) compat

/-- An unknown fits another's declaration: it takes the other's parameter and its codomain is at most the other's. -/
def Fits (v : Nat → Nat) (dX dW : Decl) : Prop :=
  Level.value v dX.dom ≤ Level.value v dW.dom ∧ Level.value v dW.cod ≤ Level.value v dX.cod

end CumulativeCodes

#print axioms CumulativeCodes.Ty.meet
#print axioms CumulativeCodes.compatible_meet
#print axioms CumulativeCodes.meet_exact
#print axioms CumulativeCodes.meet_forced_left

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
