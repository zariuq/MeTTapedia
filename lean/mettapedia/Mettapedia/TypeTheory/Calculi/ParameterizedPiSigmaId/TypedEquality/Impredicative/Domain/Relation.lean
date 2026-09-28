import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Families

/-!
# A logical relation on the domain, indexed by witnesses

Two elements `x`, `x'` of the domain are related at a type `T` (an ideal) *as far
as a witness `u` observes* (`Rel T u x x'`), and two types are related at a type
witness (`TyRel u X X'`). A witness is a compact element, a finite list of
tokens, and the relation is the conjunction of its values at the tokens of the
witness (`RT`). The clauses follow the structure of the type and of the token:

* at a dependent function type, a function entry `X ↦ Y` of the witness asks
  that arguments related as far as `X` observes are sent to results related as
  far as `Y` observes, at the family's value at the left argument: the relation
  at `Π` is **by application to related arguments**;
* at a dependent pair type, the components of a pair token ask that the first
  projections are related at the domain and the second projections at the
  family's value at the **first projection of the left element**: the relation
  at `Σ` is **by components**, and the dependency is explicit;
* at a universe or at the universe of codes, the elements are types and are
  related as types at the token;
* two types are related at a tag of a type former when both carry it, at a
  domain token when their domains are related at its content, and at a family
  entry `Z ↦ W` when their families send arguments related as far as `Z`
  observes to types related as far as `W` observes.

The relation is defined by well-founded recursion on the **depth of the witness
token**, not on types. A quantified argument is related as far as a token of the
entry's input observes, and the input is part of the entry, so it is smaller.
This is what makes the relation well defined at impredicative types: at the type
of codes of `∀ P : Prop. P → P`, the codes `P` range over all codes, but each is
only observed through a smaller witness (`RelationControls`). The type index of
the relation is an ideal and is never recursed on.

The relation is not reflexive on raw elements: at a function type, an element
is related to itself only when it sends related arguments to related results.

Laws:

* **closure under entailment** (`RT.closed`): a token entailed by a witness
  whose tokens all relate two elements relates them too;
* hence monotonicity in the witness (`Rel.mono`), joins (`Rel.append`), and the
  least witness (`Rel.nil`, `RT.of_ent_nil`);
* **application congruence** (`Rel.app`, and `Sem.app` for the relation over
  all witnesses of the left element);
* **pairs by components** (`Rel.fst`, `Rel.snd`, `Rel.pair_iff`) and
  **family coherence** (`TyRel.family`, `STy.family`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain

open Ideal

/-- The elements of `T` are types: `T` is the universe or the universe of codes. -/
def IsUnivI (T : Ideal) : Prop := T.Mem (.tag .univ) ∨ T.Mem (.tag .codes)

/-- The relation at one token. `RT true t T x x'`: `x` and `x'` are related at the
type `T` as far as the token `t` observes. `RT false t _ X X'`: the types `X` and
`X'` are related as far as the type token `t` observes; the type argument is not
used. -/
def RT : Bool → Tok → Ideal → Ideal → Ideal → Prop
  | true, t, T, x, x' =>
      (match t with
        | .fn .lam _ X Y => T.Mem (.tag .pi) → ∀ y y' : Ideal,
            (∀ s ∈ X.attach, RT true s.1 (dom .pi T) y y') →
            ∀ s ∈ Y.attach, RT true s.1 (fam .pi T y) (app x y) (app x' y')
        | .arg .pair i C s => T.Mem (.tag .sigma) →
            (∀ c ∈ C.attach, RT true c.1 (dom .sigma T) (fst x) (fst x')) ∧
            (i = 0 → RT true s (dom .sigma T) (fst x) (fst x')) ∧
            (i = 1 → RT true s (fam .sigma T (fst x)) (snd x) (snd x'))
        | .fn .pair C _ _ => T.Mem (.tag .sigma) →
            ∀ c ∈ C.attach, RT true c.1 (dom .sigma T) (fst x) (fst x')
        | _ => True) ∧
      (IsUnivI T → RT false t bot x x')
  | false, t, _, X, X' =>
      match t with
      | .tag k => k.IsFormer → X.Mem (.tag k) ∧ X'.Mem (.tag k)
      | .arg k i C s => (k = .pi ∨ k = .sigma) →
          (∀ c ∈ C.attach, RT false c.1 bot (dom k X) (dom k X')) ∧
          (i = 0 → RT false s bot (dom k X) (dom k X'))
      | .fn k C Z W => (k = .pi ∨ k = .sigma) →
          (∀ c ∈ C.attach, RT false c.1 bot (dom k X) (dom k X')) ∧
          ∀ y y' : Ideal, (∀ s ∈ Z.attach, RT true s.1 (dom k X) y y') →
            ∀ s ∈ W.attach, RT false s.1 bot (fam k X y) (fam k X' y')
termination_by b t => (t.depth, if b then 1 else 0)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by decide)
    | exact Prod.Lex.left _ _ (depth_lt_fn_left s.2)
    | exact Prod.Lex.left _ _ (depth_lt_fn_right s.2)
    | exact Prod.Lex.left _ _ (Tok.depth_lt_of_mem_dep (t := .arg _ _ _ _) c.2)
    | exact Prod.Lex.left _ _ (Tok.depth_lt_of_mem_dep (t := .fn _ _ _ _) c.2)
    | exact Prod.Lex.left _ _ (depth_lt_arg _ _ _ _)

/-! ## The clauses -/

section Clauses

variable {T x x' X X' : Ideal}

/-- The universe part of the relation at a token. -/
theorem RT.univ {t : Tok} (h : RT true t T x x') : IsUnivI T → RT false t bot x x' := by
  rw [RT.eq_def] at h
  exact h.2

theorem RT.lam_iff {C Z Y : List Tok} :
    RT true (.fn .lam C Z Y) T x x' ↔
      (T.Mem (.tag .pi) → ∀ y y' : Ideal, (∀ s ∈ Z, RT true s (dom .pi T) y y') →
        ∀ s ∈ Y, RT true s (fam .pi T y) (app x y) (app x' y')) ∧
      (IsUnivI T → RT false (.fn .lam C Z Y) bot x x') := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.pairArg_iff {i : Nat} {C : List Tok} {s : Tok} :
    RT true (.arg .pair i C s) T x x' ↔
      (T.Mem (.tag .sigma) →
        (∀ c ∈ C, RT true c (dom .sigma T) (fst x) (fst x')) ∧
        (i = 0 → RT true s (dom .sigma T) (fst x) (fst x')) ∧
        (i = 1 → RT true s (fam .sigma T (fst x)) (snd x) (snd x'))) ∧
      (IsUnivI T → RT false (.arg .pair i C s) bot x x') := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.pairFn_iff {C Z Y : List Tok} :
    RT true (.fn .pair C Z Y) T x x' ↔
      (T.Mem (.tag .sigma) → ∀ c ∈ C, RT true c (dom .sigma T) (fst x) (fst x')) ∧
      (IsUnivI T → RT false (.fn .pair C Z Y) bot x x') := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.tag_iff {k : Kind} :
    RT true (.tag k) T x x' ↔ (IsUnivI T → RT false (.tag k) bot x x') := by
  rw [RT.eq_def]
  exact and_iff_right trivial

theorem RT.arg_iff {k : Kind} (hk : k ≠ .pair) {i : Nat} {C : List Tok} {s : Tok} :
    RT true (.arg k i C s) T x x' ↔ (IsUnivI T → RT false (.arg k i C s) bot x x') := by
  cases k <;> first | exact absurd rfl hk | (rw [RT.eq_def]; exact and_iff_right trivial)

theorem RT.fn_iff {k : Kind} (hk : k ≠ .lam) (hk' : k ≠ .pair) {C Z Y : List Tok} :
    RT true (.fn k C Z Y) T x x' ↔ (IsUnivI T → RT false (.fn k C Z Y) bot x x') := by
  cases k <;> first | exact absurd rfl hk | exact absurd rfl hk' | (rw [RT.eq_def]; exact and_iff_right trivial)

theorem RT.ty_tag_iff {k : Kind} :
    RT false (.tag k) T X X' ↔ (k.IsFormer → X.Mem (.tag k) ∧ X'.Mem (.tag k)) := by
  rw [RT.eq_def]

theorem RT.ty_arg_iff {k : Kind} {i : Nat} {C : List Tok} {s : Tok} :
    RT false (.arg k i C s) T X X' ↔
      ((k = .pi ∨ k = .sigma) →
        (∀ c ∈ C, RT false c bot (dom k X) (dom k X')) ∧
        (i = 0 → RT false s bot (dom k X) (dom k X'))) := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_fn_iff {k : Kind} {C Z W : List Tok} :
    RT false (.fn k C Z W) T X X' ↔
      ((k = .pi ∨ k = .sigma) →
        (∀ c ∈ C, RT false c bot (dom k X) (dom k X')) ∧
        ∀ y y' : Ideal, (∀ s ∈ Z, RT true s (dom k X) y y') →
          ∀ s ∈ W, RT false s bot (fam k X y) (fam k X' y')) := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

/-- The type argument of the type relation is not used. -/
theorem RT.ty_irrel {t : Tok} {T T' : Ideal} : RT false t T X X' ↔ RT false t T' X X' := by
  rw [RT.eq_def, RT.eq_def]

end Clauses

/-! ## Closure under entailment -/

section Closure

/-- The domain witnesses of a list whose pair tokens relate two elements relate
their first projections. -/
theorem RT.args_pair_zero {v : List Tok} {T x x' : Ideal}
    (h : ∀ s ∈ v, RT true s T x x') (hT : T.Mem (.tag .sigma)) :
    ∀ r ∈ args .pair 0 v, RT true r (dom .sigma T) (fst x) (fst x') := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨-, t, ht, hk, hd⟩
  · exact ((RT.pairArg_iff.1 (h _ hC)).1 hT).2.1 rfl
  · cases t with
    | tag => cases hd
    | arg k i C s =>
      change k = .pair at hk
      subst hk
      exact ((RT.pairArg_iff.1 (h _ ht)).1 hT).1 r hd
    | fn k C Z Y =>
      change k = .pair at hk
      subst hk
      exact (RT.pairFn_iff.1 (h _ ht)).1 hT r hd

/-- The second-component witnesses of a list whose pair tokens relate two elements
relate their second projections, at the family's value at the left first
projection. -/
theorem RT.args_pair_one {v : List Tok} {T x x' : Ideal}
    (h : ∀ s ∈ v, RT true s T x x') (hT : T.Mem (.tag .sigma)) :
    ∀ r ∈ args .pair 1 v, RT true r (fam .sigma T (fst x)) (snd x) (snd x') := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨h1, -⟩
  · exact ((RT.pairArg_iff.1 (h _ hC)).1 hT).2.2 rfl
  · cases h1

/-- The domain witnesses of a list of type tokens relating two types relate their
domains. -/
theorem RT.args_ty {k : Kind} (hk : k = .pi ∨ k = .sigma) {v : List Tok} {T X X' : Ideal}
    (h : ∀ s ∈ v, RT false s T X X') :
    ∀ r ∈ args k 0 v, RT false r bot (dom k X) (dom k X') := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨-, t, ht, hk', hd⟩
  · exact ((RT.ty_arg_iff.1 (h _ hC)) hk).2 rfl
  · cases t with
    | tag => cases hd
    | arg k' i C s =>
      change k' = k at hk'
      subst hk'
      exact ((RT.ty_arg_iff.1 (h _ ht)) hk).1 r hd
    | fn k' C Z Y =>
      change k' = k at hk'
      subst hk'
      exact ((RT.ty_fn_iff.1 (h _ ht)) hk).1 r hd

/-- **Closure under entailment**: a token entailed by a list whose tokens all
relate two elements (or two types) relates them too. -/
theorem RT.closed : ∀ (b : Bool) (v : List Tok) (t : Tok) (T x x' : Ideal),
    ent v t = true → (∀ s ∈ v, RT b s T x x') → RT b t T x x'
  | true, v, t, T, x, x', e, h => by
    have hu : IsUnivI T → RT false t bot x x' := fun hT =>
      RT.closed false v t bot x x' e fun s hs => (RT.univ (h s hs) hT)
    cases t with
    | tag k => exact RT.tag_iff.2 hu
    | arg k i C s =>
      by_cases hk : k = .pair
      · subst hk
        rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at e
        refine RT.pairArg_iff.2 ⟨fun hT => ⟨fun c hc => ?_, fun hi => ?_, fun hi => ?_⟩, hu⟩
        · exact RT.closed true (args .pair 0 v) c (dom .sigma T) (fst x) (fst x') (e.1 c hc)
            (RT.args_pair_zero h hT)
        · subst hi
          exact RT.closed true (args .pair 0 v) s (dom .sigma T) (fst x) (fst x') e.2
            (RT.args_pair_zero h hT)
        · subst hi
          exact RT.closed true (args .pair 1 v) s (fam .sigma T (fst x)) (snd x) (snd x') e.2
            (RT.args_pair_one h hT)
      · exact (RT.arg_iff hk).2 hu
    | fn k C Z Y =>
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at e
      by_cases hk : k = .lam
      · subst hk
        refine RT.lam_iff.2 ⟨fun hT y y' hZ s hs => ?_, hu⟩
        refine RT.closed true (fnApp .lam v Z) s (fam .pi T y) (app x y) (app x' y') (e.2 s hs)
          fun r hr => ?_
        obtain ⟨C', Z', Y', hm, hZ', hr⟩ := mem_fnApp.1 hr
        exact (RT.lam_iff.1 (h _ hm)).1 hT y y'
          (fun s' hs' => RT.closed true Z s' (dom .pi T) y y' (hZ' s' hs') hZ) r hr
      · by_cases hk' : k = .pair
        · subst hk'
          exact RT.pairFn_iff.2 ⟨fun hT c hc => RT.closed true (args .pair 0 v) c
            (dom .sigma T) (fst x) (fst x') (e.1 c hc) (RT.args_pair_zero h hT), hu⟩
        · exact (RT.fn_iff hk hk').2 hu
  | false, v, t, T, X, X', e, h => by
    cases t with
    | tag k =>
      rw [ent_tag, hasTag_iff] at e
      exact RT.ty_tag_iff.2 (RT.ty_tag_iff.1 (h _ e))
    | arg k i C s =>
      rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at e
      refine RT.ty_arg_iff.2 fun hk => ⟨fun c hc => ?_, fun hi => ?_⟩
      · exact RT.closed false (args k 0 v) c bot (dom k X) (dom k X') (e.1 c hc)
          (RT.args_ty hk h)
      · subst hi
        exact RT.closed false (args k 0 v) s bot (dom k X) (dom k X') e.2 (RT.args_ty hk h)
    | fn k C Z W =>
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at e
      refine RT.ty_fn_iff.2 fun hk => ⟨fun c hc => ?_, fun y y' hZ s hs => ?_⟩
      · exact RT.closed false (args k 0 v) c bot (dom k X) (dom k X') (e.1 c hc)
          (RT.args_ty hk h)
      · refine RT.closed false (fnApp k v Z) s bot (fam k X y) (fam k X' y') (e.2 s hs)
          fun r hr => ?_
        obtain ⟨C', Z', W', hm, hZ', hr⟩ := mem_fnApp.1 hr
        exact ((RT.ty_fn_iff.1 (h _ hm)) hk).2 y y'
          (fun s' hs' => RT.closed true Z s' (dom k X) y y' (hZ' s' hs') hZ) r hr
termination_by b v t => (Tok.depthL v + t.depth, if b then 1 else 0)
decreasing_by
  all_goals subst_vars
  all_goals first
    | exact Prod.Lex.right _ (by decide)
    | exact Prod.Lex.left _ _ (Nat.add_lt_add_of_le_of_lt (depthL_args _ _ _)
        (Tok.depth_lt_of_mem_dep (t := .arg _ _ _ _) hc))
    | exact Prod.Lex.left _ _ (Nat.add_lt_add_of_le_of_lt (depthL_args _ _ _)
        (Tok.depth_lt_of_mem_dep (t := .fn _ _ _ _) hc))
    | exact Prod.Lex.left _ _ (Nat.add_lt_add_of_le_of_lt (depthL_args _ _ _)
        (depth_lt_arg _ _ _ _))
    | exact Prod.Lex.left _ _ (Nat.add_lt_add_of_le_of_lt (depthL_fnApp_le _ _ _)
        (depth_lt_fn_right hs))
    | exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (Nat.add_lt_add (depthL_lt_fn_left _ _ _ _)
        (Nat.lt_of_lt_of_le (depth_lt_fn_left hs') (Tok.depth_le_of_mem hm)))
        (Nat.le_of_eq (Nat.add_comm _ _)))

end Closure

/-- A token entailed by the least element relates every two elements, and every
two types. -/
theorem RT.of_ent_nil {b : Bool} {t : Tok} {T x x' : Ideal} (e : ent [] t = true) :
    RT b t T x x' :=
  RT.closed b [] t T x x' e fun _ h => absurd h List.not_mem_nil

/-- At a type with neither a dependent function nor a dependent pair facet, the
relation at a token is its universe part. -/
theorem RT.of_univ {t : Tok} {T x x' : Ideal} (hpi : ¬ T.Mem (.tag .pi))
    (hs : ¬ T.Mem (.tag .sigma)) (h : IsUnivI T → RT false t bot x x') : RT true t T x x' := by
  cases t with
  | tag k => exact RT.tag_iff.2 h
  | arg k i C s =>
    by_cases hk : k = .pair
    · subst hk
      exact RT.pairArg_iff.2 ⟨fun h' => absurd h' hs, h⟩
    · exact (RT.arg_iff hk).2 h
  | fn k C Z Y =>
    by_cases hk : k = .lam
    · subst hk
      exact RT.lam_iff.2 ⟨fun h' => absurd h' hpi, h⟩
    · by_cases hk' : k = .pair
      · subst hk'
        exact RT.pairFn_iff.2 ⟨fun h' => absurd h' hs, h⟩
      · exact (RT.fn_iff hk hk').2 h

/-- At a type whose only facet is a dependent function type, the relation at a
token other than a function entry holds. -/
theorem RT.of_not_lam {t : Tok} {T x x' : Ideal} (hs : ¬ T.Mem (.tag .sigma)) (hU : ¬ IsUnivI T)
    (ht : ∀ C Z Y, t ≠ .fn .lam C Z Y) : RT true t T x x' := by
  have h : IsUnivI T → RT false t bot x x' := fun h' => absurd h' hU
  cases t with
  | tag k => exact RT.tag_iff.2 h
  | arg k i C s =>
    by_cases hk : k = .pair
    · subst hk
      exact RT.pairArg_iff.2 ⟨fun h' => absurd h' hs, h⟩
    · exact (RT.arg_iff hk).2 h
  | fn k C Z Y =>
    by_cases hk : k = .lam
    · subst hk
      exact absurd rfl (ht C Z Y)
    · by_cases hk' : k = .pair
      · subst hk'
        exact RT.pairFn_iff.2 ⟨fun h' => absurd h' hs, h⟩
      · exact (RT.fn_iff hk hk').2 h

/-! ## The relation at a witness -/

/-- `x` and `x'` are related at the type `T` as far as the witness `u` observes. -/
def Rel (T : Ideal) (u : List Tok) (x x' : Ideal) : Prop := ∀ t ∈ u, RT true t T x x'

/-- The types `X` and `X'` are related as far as the type witness `u` observes. -/
def TyRel (u : List Tok) (X X' : Ideal) : Prop := ∀ t ∈ u, RT false t bot X X'

section Witness

variable {T x x' X X' : Ideal} {u v : List Tok}

/-- **Monotonicity in the witness.** -/
theorem Rel.mono (h : Rel T u x x') (hvu : v ⊑ u) : Rel T v x x' :=
  fun t ht => RT.closed true u t T x x' (hvu t ht) h

theorem TyRel.mono (h : TyRel u X X') (hvu : v ⊑ u) : TyRel v X X' :=
  fun t ht => RT.closed false u t bot X X' (hvu t ht) h

/-- The least witness observes nothing. -/
theorem Rel.nil : Rel T [] x x' := fun _ h => absurd h List.not_mem_nil

theorem TyRel.nil : TyRel [] X X' := fun _ h => absurd h List.not_mem_nil

/-- **Joins**: the relation at a join of witnesses is the relation at each. -/
theorem Rel.append (h₁ : Rel T u x x') (h₂ : Rel T v x x') : Rel T (u ++ v) x x' := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact h₁ t ht
  · exact h₂ t ht

theorem TyRel.append (h₁ : TyRel u X X') (h₂ : TyRel v X X') : TyRel (u ++ v) X X' := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact h₁ t ht
  · exact h₂ t ht

/-- At a universe, the relation is the type relation. -/
theorem Rel.tyRel (h : Rel T u x x') (hT : IsUnivI T) : TyRel u x x' :=
  fun t ht => RT.univ (h t ht) hT

/-- **Application congruence**: at a dependent function type, functions related as
far as a witness observes send arguments related as far as an input `Z` observes
to results related as far as the witness's value at `Z` observes, at the family's
value at the left argument. -/
theorem Rel.app (h : Rel T u x x') (hT : T.Mem (.tag .pi)) {Z : List Tok} {y y' : Ideal}
    (hy : Rel (dom .pi T) Z y y') : Rel (fam .pi T y) (fnApp .lam u Z) (app x y) (app x' y') := by
  intro r hr
  obtain ⟨C, Z', Y, hm, hZ', hr⟩ := mem_fnApp.1 hr
  exact (RT.lam_iff.1 (h _ hm)).1 hT y y' (hy.mono hZ') r hr

/-- **Pairs by components**: the first projections are related at the domain. -/
theorem Rel.fst (h : Rel T u x x') (hT : T.Mem (.tag .sigma)) :
    Rel (dom .sigma T) (args .pair 0 u) (Ideal.fst x) (Ideal.fst x') :=
  RT.args_pair_zero h hT

/-- **Pairs by components**: the second projections are related at the family's
value at the left first projection. -/
theorem Rel.snd (h : Rel T u x x') (hT : T.Mem (.tag .sigma)) :
    Rel (fam .sigma T (Ideal.fst x)) (args .pair 1 u) (Ideal.snd x) (Ideal.snd x') :=
  RT.args_pair_one h hT

/-- At a type whose only facet is a dependent pair type, two elements are related
as far as a witness observes when their components are. -/
theorem Rel.of_components (hpi : ¬ T.Mem (.tag .pi)) (hU : ¬ IsUnivI T)
    (h₀ : Rel (dom .sigma T) (args .pair 0 u) (Ideal.fst x) (Ideal.fst x'))
    (h₁ : Rel (fam .sigma T (Ideal.fst x)) (args .pair 1 u) (Ideal.snd x) (Ideal.snd x')) :
    Rel T u x x' := by
  intro t ht
  have hu : IsUnivI T → RT false t bot x x' := fun h => absurd h hU
  cases t with
  | tag k => exact RT.tag_iff.2 hu
  | arg k i C s =>
    by_cases hk : k = .pair
    · subst hk
      refine RT.pairArg_iff.2 ⟨fun _ => ⟨fun c hc => h₀ c (mem_args_of_dep ht rfl hc),
        fun hi => ?_, fun hi => ?_⟩, hu⟩
      · subst hi; exact h₀ s (mem_args_of_arg ht)
      · subst hi; exact h₁ s (mem_args_of_arg ht)
    · exact (RT.arg_iff hk).2 hu
  | fn k C Z Y =>
    by_cases hk : k = .lam
    · subst hk
      exact RT.lam_iff.2 ⟨fun h => absurd h hpi, hu⟩
    · by_cases hk' : k = .pair
      · subst hk'
        exact RT.pairFn_iff.2 ⟨fun _ c hc => h₀ c (mem_args_of_dep ht rfl hc), hu⟩
      · exact (RT.fn_iff hk hk').2 hu

/-- Pairs are related when their components are. -/
theorem Rel.pair (hpi : ¬ T.Mem (.tag .pi)) (hU : ¬ IsUnivI T) {a a' b b' : Ideal}
    (h₀ : Rel (dom .sigma T) (args .pair 0 u) a a')
    (h₁ : Rel (fam .sigma T a) (args .pair 1 u) b b') :
    Rel T u (Ideal.pair a b) (Ideal.pair a' b') := by
  refine Rel.of_components hpi hU ?_ ?_
  · rw [fst_pair, fst_pair]; exact h₀
  · rw [fst_pair, snd_pair, snd_pair]; exact h₁

/-- The domains of related types are related at the domain witnesses. -/
theorem TyRel.domain (h : TyRel u X X') {k : Kind} (hk : k = .pi ∨ k = .sigma) :
    TyRel (args k 0 u) (dom k X) (dom k X') :=
  RT.args_ty hk h

/-- **Family coherence**: related types send arguments related at the domain, as
far as an input `Z` observes, to types related as far as the witness's family
value at `Z` observes. -/
theorem TyRel.family (h : TyRel u X X') {k : Kind} (hk : k = .pi ∨ k = .sigma) {Z : List Tok}
    {y y' : Ideal} (hy : Rel (dom k X) Z y y') :
    TyRel (fnApp k u Z) (fam k X y) (fam k X' y') := by
  intro r hr
  obtain ⟨C, Z', W, hm, hZ', hr⟩ := mem_fnApp.1 hr
  exact ((RT.ty_fn_iff.1 (h _ hm)) hk).2 y y' (hy.mono hZ') r hr

end Witness

/-! ## The relation over all witnesses -/

/-- Two elements related at `T` as far as every witness of the left one observes. -/
def Sem (T x x' : Ideal) : Prop := ∀ u, Below u x → Rel T u x x'

/-- Two types related as far as every witness of the left one observes. -/
def STy (X X' : Ideal) : Prop := ∀ u, Below u X → TyRel u X X'

/-- A predicate closed under entailment holds of the ideal generated by tokens
satisfying it. -/
theorem RT.of_mem_closure {b : Bool} {P : Tok → Prop} {T x x' : Ideal}
    (hP : ∀ g, P g → RT b g T x x') {t : Tok} (ht : (closure P).Mem t) : RT b t T x x' := by
  obtain ⟨w, hw, e⟩ := ht
  exact RT.closed b w t T x x' e fun s hs => hP s (hw s hs)

/-- **Application congruence** over all witnesses. -/
theorem Sem.app {T f f' y y' : Ideal} (hf : Sem T f f') (hT : T.Mem (.tag .pi))
    (hy : Sem (dom .pi T) y y') : Sem (fam .pi T y) (app f y) (app f' y') := by
  intro v hv r hr
  obtain ⟨Z, Y, hZ, hm, hY⟩ := mem_app.1 (hv r hr)
  have hrel := Rel.app (hf [.fn .lam [] Z Y] fun s hs => by
    rw [List.mem_singleton.1 hs]; exact hm) hT (hy Z hZ)
  have hsub : Y ⊑ fnApp .lam [.fn .lam [] Z Y] Z := by
    intro s hs
    apply ent_of_mem
    exact mem_fnApp.2 ⟨[], Z, Y, List.mem_singleton_self _, fun s' hs' => ent_of_mem hs', hs⟩
  exact RT.closed true Y r _ _ _ hY (hrel.mono hsub)

/-- **Family coherence** over all witnesses: related types send related arguments
to related types. For a dependent pair type related to itself, this is the
coherence of the result family on related first components. -/
theorem STy.family {X X' y y' : Ideal} (h : STy X X') {k : Kind} (hk : k = .pi ∨ k = .sigma)
    (hy : Sem (dom k X) y y') : STy (fam k X y) (fam k X' y') := by
  intro v hv r hr
  obtain ⟨w, hw, e⟩ := hv r hr
  refine RT.closed false w r bot _ _ e fun g hg => ?_
  obtain ⟨C, Z, W, hm, hZ, hg⟩ := hw g hg
  have hrel := TyRel.family (h [.fn k C Z W] fun s hs => by
    rw [List.mem_singleton.1 hs]; exact hm) hk (hy Z hZ)
  refine hrel g ?_
  apply mem_fnApp.2
  exact ⟨C, Z, W, List.mem_singleton_self _, fun s hs => ent_of_mem hs, hg⟩

end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
