import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Interp

/-!
# The components of dependent types, and the substitution laws of families

A dependent type of kind `k` (`k = pi` or `k = sigma`) has a domain, its
component `0`, and a family, its step function of kind `k`. For a type given as
an ideal `T`:

* `Ideal.dom k T` is the ideal of the domain tokens of `T`;
* `Ideal.fam k T y` is the value of the family at the ideal `y`: the outputs of
  the family entries of `T` whose inputs are in `y`. Application is the family
  of kind `lam` (`Ideal.app_eq_fam`).

The laws, all without typing:

* the domain and the family of a dependent type built by `Ideal.former` are its
  arguments (`dom_former`, `fam_former_const` for a constant family);
* **substitution for families**: the family of the interpretation of `Π A B` or
  `Σ A B` at `y` is the interpretation of `B` with `y` for the bound variable
  (`fam_interp_pi`, `fam_interp_sigma`), and applying the interpretation of an
  abstraction to `y` is the interpretation of its body at `y`
  (`app_interp_lam`). These are the semantic form of `B[a]` and of `β` at every
  argument, including arguments that are not interpretations of terms;
* the witnesses of a type are componentwise witnesses of its components
  (`below_dom_args`, `below_fam_fnApp`);
* a dependent type of kind `k` has the tag `k` and no other
  (`former_mem_tag_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace Ideal

/-! ## Components -/

/-- The domain of a dependent type of kind `k`: its component `0`. -/
def dom (k : Kind) (T : Ideal) : Ideal := closure fun s => T.Mem (.arg k 0 [] s)

/-- The value at `y` of the family of a dependent type of kind `k`: the outputs of
its entries whose inputs are in `y`. -/
def fam (k : Kind) (T y : Ideal) : Ideal :=
  closure fun t => ∃ C Z Y, T.Mem (.fn k C Z Y) ∧ Below Z y ∧ t ∈ Y

/-- Application is the family of kind `lam`. -/
theorem app_eq_fam (I J : Ideal) : app I J = fam .lam I J := rfl

theorem dom_mono {k : Kind} {T T' : Ideal} (h : T ≤ T') : dom k T ≤ dom k T' :=
  closure_mono fun _ hs => h _ hs

theorem fam_mono {k : Kind} {T T' y y' : Ideal} (hT : T ≤ T') (hy : y ≤ y') :
    fam k T y ≤ fam k T' y' :=
  closure_mono fun _ ⟨C, Z, Y, hm, hZ, ht⟩ => ⟨C, Z, Y, hT _ hm, hZ.mono hy, ht⟩

/-- The dependency of a component token is in the domain. -/
theorem mem_dom_of_arg_dep {k : Kind} {i : Nat} {C : List Tok} {s c : Tok} {T : Ideal}
    (h : T.Mem (.arg k i C s)) (hc : c ∈ C) : (dom k T).Mem c := by
  refine subset_closure (T.closed (v := [.arg k i C s]) (fun r hr => ?_) ?_)
  · rw [List.mem_singleton.1 hr]; exact h
  · rw [ent_arg, List.all_nil, Bool.true_and]
    apply ent_of_mem
    simp only [args_cons_arg, args_nil, List.append_nil, and_self, true_and, if_true,
      List.mem_append]
    exact .inr hc

/-- The dependency of a family entry is in the domain. -/
theorem mem_dom_of_fn_dep {k : Kind} {C Z Y : List Tok} {c : Tok} {T : Ideal}
    (h : T.Mem (.fn k C Z Y)) (hc : c ∈ C) : (dom k T).Mem c := by
  refine subset_closure (T.closed (v := [.fn k C Z Y]) (fun r hr => ?_) ?_)
  · rw [List.mem_singleton.1 hr]; exact h
  · rw [ent_arg, List.all_nil, Bool.true_and]
    apply ent_of_mem
    simp only [args_cons_fn, args_nil, List.append_nil, and_self, if_true]
    exact hc

/-- The domain token of a component `0` is in the domain. -/
theorem mem_dom_of_arg_zero {k : Kind} {C : List Tok} {s : Tok} {T : Ideal}
    (h : T.Mem (.arg k 0 C s)) : (dom k T).Mem s := by
  refine subset_closure (T.closed (v := [.arg k 0 C s]) (fun r hr => ?_) ?_)
  · rw [List.mem_singleton.1 hr]; exact h
  · rw [ent_arg, List.all_nil, Bool.true_and]
    apply ent_of_mem
    simp [args_cons_arg]

/-- The domain witnesses of a witness of a type are witnesses of its domain. -/
theorem below_dom_args {k : Kind} {u : List Tok} {T : Ideal} (h : Below u T) :
    Below (args k 0 u) (dom k T) := by
  intro s hs
  rcases mem_args_iff.1 hs with ⟨C, hC⟩ | ⟨-, t, ht, hk, hd⟩
  · exact mem_dom_of_arg_zero (h _ hC)
  · cases t with
    | tag => cases hd
    | arg k' i C s' =>
      change k' = k at hk
      subst hk
      exact mem_dom_of_arg_dep (h _ ht) hd
    | fn k' C Z Y =>
      change k' = k at hk
      subst hk
      exact mem_dom_of_fn_dep (h _ ht) hd

/-- The family values of a witness of a type are witnesses of its family. -/
theorem below_fam_fnApp {k : Kind} {u Z : List Tok} {T y : Ideal} (h : Below u T)
    (hZ : Below Z y) : Below (fnApp k u Z) (fam k T y) := by
  intro s hs
  obtain ⟨C, Z', Y, hm, hZ', hs⟩ := mem_fnApp'.1 hs
  exact subset_closure ⟨C, Z', Y, h _ hm, hZ.of_le hZ', hs⟩

/-! ## Dependent types built by `former` -/

/-- The closure of the tokens of an ideal is the ideal. -/
theorem closure_mem (I : Ideal) : closure I.Mem = I :=
  le_antisymm (closure_le fun _ h => h) fun _ h => subset_closure h

/-- The domain of a dependent type is its domain argument. -/
theorem dom_former (k : Kind) (A : Ideal) (F : List Tok → Ideal) : dom k (former k A F) = A := by
  have : (fun s => (former k A F).Mem (.arg k 0 [] s)) = A.Mem :=
    funext fun _ => propext mem_former_dom
  rw [dom, this, closure_mem]

/-- The family of a dependent type with a constant family is that family. -/
theorem fam_former_const (k : Kind) (A B y : Ideal) :
    fam k (former k A fun _ => B) y = B := by
  have hF : Monotone fun _ : List Tok => B := fun _ => le_refl B
  apply le_antisymm
  · refine closure_le fun t ⟨C, Z, Y, hm, _, ht⟩ => ?_
    exact ((mem_former_fn hF).1 hm).2 t ht
  · intro t ht
    refine subset_closure ⟨[], [], [t], (mem_former_fn hF).2 ⟨fun _ h => absurd h List.not_mem_nil,
      fun s hs => by rw [List.mem_singleton.1 hs]; exact ht⟩, fun _ h => absurd h List.not_mem_nil,
      List.mem_singleton_self t⟩

/-- A dependent type of kind `k` has the tag `k` and no other. -/
theorem former_mem_tag_iff {k k' : Kind} {A : Ideal} {F : List Tok → Ideal} :
    (former k A F).Mem (.tag k') ↔ k' = k := by
  constructor
  · rintro ⟨w, hw, ht⟩
    rw [ent_tag, hasTag_iff] at ht
    rcases hw _ ht with h | ⟨d, h, -⟩ | ⟨D, X, Y, h, -⟩
    · exact Tok.tag.inj h
    · cases h
    · cases h
  · intro h
    subst h
    exact mem_former_tag _ A F

/-! ## Substitution for families and application -/

variable {Head : Type} (Rd : Reading Head)

/-- The family of the interpretation of a dependent type of kind `k`, at `y`, is
the interpretation of its body with `y` for the bound variable. -/
theorem fam_interp_former {n : Nat} (k : Kind) (A : Tm Head n) (B : Tm Head (n + 1)) (ρ : Env n)
    (y : Ideal) :
    fam k (former k (interp Rd A ρ) fun X => interp Rd B (Env.cons (principal X) ρ)) y =
      interp Rd B (Env.cons y ρ) := by
  have hF : Monotone fun X => interp Rd B (Env.cons (principal X) ρ) :=
    interp_family_monotone Rd B ρ
  apply le_antisymm
  · refine closure_le fun t ⟨C, Z, Y, hm, hZ, ht⟩ => ?_
    refine interp_mono Rd B ?_ t (((mem_former_fn hF).1 hm).2 t ht)
    exact Env.Le.cons (principal_le_iff.2 hZ) (Env.Le.refl ρ)
  · intro t ht
    obtain ⟨X, hX, W, hW, ht'⟩ := Continuous.binder Rd (interp_cont Rd B _)
      (v := [t]) (fun s hs => by rw [List.mem_singleton.1 hs]; exact ht)
    refine subset_closure ⟨[], W, [t], (mem_former_fn hF).2 ⟨fun _ h => absurd h List.not_mem_nil,
      ?_⟩, hW, List.mem_singleton_self t⟩
    exact ht'.mono (interp_mono Rd B (Env.Le.cons (le_refl _) (approx_le hX)))

/-- **Substitution for the family of a dependent function type.** -/
theorem fam_interp_pi {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) (ρ : Env n) (y : Ideal) :
    fam .pi (interp Rd (.pi A B) ρ) y = interp Rd B (Env.cons y ρ) :=
  fam_interp_former Rd .pi A B ρ y

/-- **Substitution for the family of a dependent pair type.** -/
theorem fam_interp_sigma {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) (ρ : Env n)
    (y : Ideal) : fam .sigma (interp Rd (.sigma A B) ρ) y = interp Rd B (Env.cons y ρ) :=
  fam_interp_former Rd .sigma A B ρ y

theorem dom_interp_pi {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) (ρ : Env n) :
    dom .pi (interp Rd (.pi A B) ρ) = interp Rd A ρ :=
  dom_former _ _ _

theorem dom_interp_sigma {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) (ρ : Env n) :
    dom .sigma (interp Rd (.sigma A B) ρ) = interp Rd A ρ :=
  dom_former _ _ _

/-- **β at every argument**: applying the interpretation of an abstraction to an
ideal `y` is interpreting its body with `y` for the bound variable. -/
theorem app_interp_lam {n : Nat} (b : Tm Head (n + 1)) (ρ : Env n) (y : Ideal) :
    app (interp Rd (.lam b) ρ) y = interp Rd b (Env.cons y ρ) := by
  have hF : Monotone fun X => interp Rd b (Env.cons (principal X) ρ) :=
    interp_family_monotone Rd b ρ
  apply le_antisymm
  · intro t ht
    obtain ⟨X, Y, hX, hl, hY⟩ := mem_app.1 ht
    have hY' := (mem_lam_fn hF).1 hl
    refine Ideal.closed _ (hY'.mono (interp_mono Rd b ?_)) hY
    exact Env.Le.cons (principal_le_iff.2 hX) (Env.Le.refl ρ)
  · intro t ht
    obtain ⟨X, hX, W, hW, ht'⟩ := Continuous.binder Rd (interp_cont Rd b _)
      (v := [t]) (fun s hs => by rw [List.mem_singleton.1 hs]; exact ht)
    refine mem_app.2 ⟨W, [t], hW, (mem_lam_fn hF).2 ?_, ent_of_mem List.mem_cons_self⟩
    exact ht'.mono (interp_mono Rd b (Env.Le.cons (le_refl _) (approx_le hX)))

/-- An entry of a function interpreting an abstraction has its output in the
body's value at its input, whatever its dependency. -/
theorem below_of_mem_lam {F : List Tok → Ideal} (hF : Monotone F) {C X Y : List Tok}
    (h : (lam F).Mem (.fn .lam C X Y)) : Below Y (F X) := by
  obtain ⟨w, hw, h⟩ := h
  rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  intro y hy
  refine Ideal.closed (F X) (v := fnApp .lam w X) ?_ (h.2 y hy)
  intro s hs
  obtain ⟨C', X', Y', hp, hX, hs⟩ := mem_fnApp'.1 hs
  obtain ⟨X'', Y'', h', hY⟩ := hw _ hp
  cases h'
  exact hF hX s (hY s hs)

end Ideal
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
