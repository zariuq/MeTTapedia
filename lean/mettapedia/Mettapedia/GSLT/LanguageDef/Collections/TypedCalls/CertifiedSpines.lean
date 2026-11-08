import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ClosedSortEvidence

/-!
# When a certified argument is a spine of the fold's own cells

A typed fold over a list could skip each cell's head and arity test when the
argument's certificate (PeTTa's type relation types it once at the closed
formal, `eval_petta_value_typed_once`) already says that every cell is a `Cons`
cell ending in `Nil`. `ClosedSortEvidence.list_certified_fold` proves the shape
for the declarations `{Nil, Cons}` and the walk. Here the question is the
signature.

**Function heads are not excluded.** A value PeTTa reaches without evaluating
it (an argument at an `Atom` parameter, a `match` result, a `quote`) may hold an
application of any declared head, and the relation types it by its head's
declaration, whether or not the head has equations. So the condition is on the
declarations, every symbol included.

**The condition** (`ListClosed`): `Nil` and `Cons` have their usual rows, and
every row of every other symbol offers (an arrow's range, or the row itself) a
type that is not a variable, not the bare symbol `List`, and not headed by `List`
or a variable (`AwayFromList`). The bare `List` and variables are excluded
because the relation gives an expression whose head has a non-arrow row its
tuple type, so `(: L List)` types `(L 5)` at `(List Number)`.

**Theorems** (PeTTa's relation, every row read, multiplicity aside):
* `not_meets_bareList`: under the condition no ground value has a derivation
  meeting the bare `List`, so no tuple type reaches a list type;
* `list_inversion`: a ground value typable at `(List τ)` is `Nil`, or a `Cons`
  of a value typable at `τ` and a value typable at `(List τ)`;
* `spine_of_typable`: a ground value typable at `(List τ)` is a spine of `Cons`
  cells ending in `Nil`, with every element typable at `τ`. Typed once is
  typable (`typable_iff_count`).

**Controls**, each a clause of the condition (stable-fixed PeTTa and CeTTa
certify these values):
* a second constructor, `(: pair (-> Number (List Number) (List Number)))`:
  `(Cons 1 (pair 2 Nil))` is typed once at `(List Number)` and is not a spine
  (`Controls.pair_certified`); the typed fold answers nothing on it, where a pass
  without the cell test would answer `3`;
* a tuple type: with `(: L List)`, `(L 5)` is typable at `(List Number)`
  (`Controls.tuple_certified`);
* a variable tail: `(Cons 1 $x)` is typed once and is not a spine
  (`Controls.var_tail_certified`), so groundness is needed (an O(1) flag in
  CeTTa);
* the Peano sort, with a second successor `(: P (-> Nat Nat))`: `(S (P Z))` is
  typed once at `Nat` (`Controls.peano_certified`), and `NatClosed` gives
  `nat_spine_of_typable`.

**Discharging a typed entry over an untyped producer** (PeTTa's analogue of
`InferredTypeSets`): the check asks for exactly one derivation meeting the closed
formal. Under functional declarations that is the value's one derivation meeting
it (`typed_once_iff`, `discharge_iff`), and an application of a constructor is
typed once where its range matches under an assignment typing every checked field
once (`ctor_typed_iff`), so inferred sets compose as HE's instance sets do, with
PeTTa's leaves (an untyped symbol meets no named formal). Two rows meeting the
formal type a value twice (`Controls.two_rows_twice`), and an untyped element is
rejected (`Controls.untyped_element_rejected`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CertifiedSpines

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open TypedCalls.Controls (listOf consRow cons_constructor)

/-! ## Rows away from lists -/

/-- A type no list type, and no bare `List` heading a tuple, comes from. -/
def AwayFromList : Ty String → Prop
  | .var _ => False
  | .sym s => s ≠ "List"
  | .app [] => True
  | .app (.sym s :: _) => s ≠ "List"
  | .app (.var _ :: _) => False
  | .app (.app _ :: _) => True

theorem away_ne {ρ : Ty String} (h : AwayFromList ρ) (f : String → Ty Empty) :
    ρ.bind f ≠ .sym "List" ∧ ∀ τ : Ty Empty, ρ.bind f ≠ listOf τ := by
  match ρ, h with
  | .sym s, h => exact ⟨fun same => h (by simpa using same), fun τ => by simp [listOf]⟩
  | .app [], _ => exact ⟨by simp, fun τ => by simp [listOf]⟩
  | .app (.sym s :: rest), h =>
      refine ⟨by simp, fun τ same => h ?_⟩
      simp only [Ty.bind_app, List.map_cons, Ty.bind_sym, listOf, Ty.app.injEq,
        List.cons.injEq, Ty.sym.injEq] at same
      exact same.1
  | .app (.app ts :: rest), _ => exact ⟨by simp, fun τ => by simp [listOf]⟩

theorem arrowSplit_head {V : Type} {ρ : Ty V} {As : List (Ty V)} {R : Ty V}
    (h : arrowSplit ρ = some (As, R)) : ∃ ts, ρ = .app (.sym "->" :: ts) := by
  match ρ with
  | .var _ => simp [arrowSplit] at h
  | .sym _ => simp [arrowSplit] at h
  | .app [] => simp [arrowSplit] at h
  | .app (.var _ :: _) => simp [arrowSplit] at h
  | .app (.app _ :: _) => simp [arrowSplit] at h
  | .app (.sym s :: ts) =>
      by_cases hs : s = "->"
      · exact ⟨ts, by rw [hs]⟩
      · simp [arrowSplit, hs] at h

theorem arrow_ne {ts : List (Ty String)} (f : String → Ty Empty) :
    (Ty.app (.sym "->" :: ts)).bind f ≠ .sym "List" ∧
      ∀ τ : Ty Empty, (Ty.app (.sym "->" :: ts)).bind f ≠ listOf τ :=
  ⟨by simp, fun τ => by simp [listOf]⟩

/-- What a row offers an application or a constant: an arrow's range, or the row
itself. -/
def offered (ρ : Ty String) : Ty String :=
  match arrowSplit ρ with
  | some (_, R) => R
  | none => ρ

/-- **The list sort is closed under the declarations**: `Nil` and `Cons` have
their usual rows, and every row of every other symbol offers a type away from
lists. -/
structure ListClosed (Γ : Decls) : Prop where
  nil : Γ "Nil" = [listOf (.var "a")]
  cons : Γ "Cons" = [consRow]
  other : ∀ s, s ≠ "Nil" → s ≠ "Cons" → ∀ ρ ∈ Γ s, AwayFromList (offered ρ)

/-- No row of a closed signature, read as the symbol's own type, is a list type
or the bare `List`. -/
theorem row_ne {Γ : Decls} (hΓ : ListClosed Γ) {s : String} {ρ : Ty String} (hρ : ρ ∈ Γ s)
    (notNil : s ≠ "Nil") (f : String → Ty Empty) :
    ρ.bind f ≠ .sym "List" ∧ ∀ τ : Ty Empty, ρ.bind f ≠ listOf τ := by
  by_cases isCons : s = "Cons"
  · subst isCons
    rw [hΓ.cons, List.mem_singleton] at hρ
    subst hρ
    exact arrow_ne f
  · have away := hΓ.other s notNil isCons ρ hρ
    cases hs : arrowSplit ρ with
    | none =>
        simp only [offered, hs] at away
        exact away_ne away f
    | some p =>
        obtain ⟨ts, rfl⟩ := arrowSplit_head hs
        exact arrow_ne f

/-- `Nil`'s row as the symbol's own type is no bare `List`. -/
theorem nil_row_ne (f : String → Ty Empty) : (listOf (.var "a") : Ty String).bind f ≠ .sym "List" := by
  simp [listOf]

/-! ## Ground values and derivations meeting a type -/

mutual
/-- A value without variables. -/
def Ground : Atom → Prop
  | .var _ => False
  | .symbol _ => True
  | .grounded _ => True
  | .expression xs => GroundAll xs
/-- Values without variables. -/
def GroundAll : List Atom → Prop
  | [] => True
  | x :: xs => Ground x ∧ GroundAll xs
end

/-- A derivation meets a ground type. -/
def Meets (d : Deriv) (T : Ty Empty) : Prop := Sat (d.eqs ++ [(d.ty, T.lift)])

/-- Some effective derivation of a value meets a ground type. -/
def Typable (Γ : Decls) (v : Atom) (T : Ty Empty) : Prop := ∃ d ∈ eff (info Γ v), Meets d T

theorem typable_iff_count (Γ : Decls) (v : Atom) (T : Ty Empty) :
    Typable Γ v T ↔ 0 < count (info Γ v) T := by
  classical
  unfold count Typable Meets
  rw [Multiset.card_pos_iff_exists_mem]
  simp only [Multiset.mem_filter]

theorem meets_iff {d : Deriv} {T : Ty Empty} :
    Meets d T ↔ ∃ σ : DVar → Ty Empty, Solves σ d.eqs ∧ d.ty.bind σ = T := by
  unfold Meets Sat
  constructor
  · rintro ⟨σ, hσ⟩
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hσ
    exact ⟨σ, hσ.1, hσ.2⟩
  · rintro ⟨σ, hs, ht⟩
    refine ⟨σ, (solves_append _ _ _).mpr ⟨hs, (solves_singleton _ _).mpr ?_⟩⟩
    rw [Ty.lift_bind_ground]
    exact ht

/-- A child's derivation seen from its parent meets what its parent's solution
gives it. -/
theorem meets_of_pushed {d : Deriv} {i : ℕ} {σ : DVar → Ty Empty} {T : Ty Empty}
    (heqs : Solves σ (d.push i).eqs) (hty : (d.push i).ty.bind σ = T) : Meets d T := by
  refine meets_iff.mpr ⟨σ ∘ DVar.push i, (solves_map σ (DVar.push i) d.eqs).mp heqs, ?_⟩
  rw [← hty]
  simp only [Deriv.push, Ty.bind_map]

theorem mem_eff {j : Info} {d : Deriv} (h : d ∈ eff j) : d ∈ j.cands ∨ d = undefinedDeriv := by
  unfold eff at h
  split_ifs at h
  · right
    simpa using h
  · left
    exact h

theorem mem_symbol_cands {Γ : Decls} {s : String} {d : Deriv} (h : d ∈ (info Γ (.symbol s)).cands) :
    ∃ ρ ∈ Γ s, d = ⟨ρ.map DVar.own, []⟩ := by
  rw [info_symbol] at h
  simp only [Multiset.mem_coe, List.mem_map] at h
  obtain ⟨ρ, hρ, rfl⟩ := h
  exact ⟨ρ, hρ, rfl⟩

theorem mem_expression_cands {Γ : Decls} {x : Atom} {xs : List Atom} {d : Deriv}
    (h : d ∈ (info Γ (.expression (x :: xs))).cands) :
    d ∈ funTrees (info Γ x) (xs.map (info Γ)) ∨ d ∈ tupleTrees (info Γ x :: xs.map (info Γ)) := by
  rw [info_expression, List.map_cons] at h
  simp only [nodeInfo] at h
  split_ifs at h
  · right
    exact h
  · left
    exact h

theorem mem_funTrees {head : Info} {args : List Info} {d : Deriv} (h : d ∈ funTrees head args) :
    ∃ ρ ∈ head.rows, ∃ As R, arrowSplit ρ = some (As, R) ∧ As.length = args.length ∧
      ∃ E ∈ argEqs 1 As args, d = ⟨R.map DVar.own, E⟩ := by
  classical
  unfold funTrees at h
  rw [Multiset.mem_bind] at h
  obtain ⟨ρ, hρ, hd⟩ := h
  refine ⟨ρ, by simpa using hρ, ?_⟩
  cases hs : arrowSplit ρ with
  | none =>
      rw [hs] at hd
      simp at hd
  | some p =>
      obtain ⟨As, R⟩ := p
      rw [hs] at hd
      simp only at hd
      split_ifs at hd with hlen
      · rw [Multiset.mem_filter, Multiset.mem_map] at hd
        obtain ⟨⟨E, hE, rfl⟩, -⟩ := hd
        exact ⟨As, R, rfl, hlen, E, hE, rfl⟩
      · simp at hd

theorem mem_tupleTrees_cons {j : Info} {js : List Info} {d : Deriv} (h : d ∈ tupleTrees (j :: js)) :
    ∃ dh ∈ eff j, ∃ p ∈ tupleParts 1 js,
      d = ⟨.app ((dh.push 0).ty :: p.1), (dh.push 0).eqs ++ p.2⟩ := by
  unfold tupleTrees at h
  rw [Multiset.mem_map] at h
  obtain ⟨q, hq, rfl⟩ := h
  simp only [tupleParts, Multiset.mem_bind, Multiset.mem_map] at hq
  obtain ⟨dh, hdh, p, hp, rfl⟩ := hq
  exact ⟨dh, hdh, p, hp, rfl⟩

/-- Only a symbol has rows. -/
theorem rows_info (Γ : Decls) : ∀ v : Atom, (info Γ v).rows = match v with
    | .symbol s => Γ s
    | _ => []
  | .symbol s => by rw [info_symbol]
  | .var _ => rfl
  | .grounded g => by cases g <;> rfl
  | .expression xs => by
      rw [info_expression]
      cases xs <;> rfl

/-- The derivations of a value that is not an expression and not a symbol. -/
theorem grounded_ty {Γ : Decls} {g : GroundedValue} {d : Deriv} (h : d ∈ eff (info Γ (.grounded g))) :
    d = undefinedDeriv ∨ ∃ c, (c = "Number" ∨ c = "String" ∨ c = "Bool") ∧ d = classDeriv c := by
  cases g with
  | int n =>
      rw [info_int] at h
      unfold eff at h
      simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.mem_singleton] at h
      exact .inr ⟨"Number", .inl rfl, h⟩
  | string s =>
      rw [info_string] at h
      unfold eff at h
      simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.mem_singleton] at h
      exact .inr ⟨"String", .inr (.inl rfl), h⟩
  | bool b =>
      rw [info_bool] at h
      unfold eff at h
      simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.mem_singleton] at h
      exact .inr ⟨"Bool", .inr (.inr rfl), h⟩
  | custom t v =>
      have : info Γ (.grounded (.custom t v)) = ⟨[], 0⟩ := rfl
      rw [this] at h
      unfold eff at h
      simp only [Multiset.card_zero, if_true, Multiset.mem_singleton] at h
      exact .inl h

theorem argEqs_cons_checked {i : ℕ} {A : Ty String} {As : List (Ty String)} {j : Info}
    {js : List Info} (h : ¬ Unchecked A) :
    argEqs i (A :: As) (j :: js) = (eff j).bind fun d =>
      (argEqs (i + 1) As js).map fun E => ((A.map DVar.own, (d.push i).ty) :: (d.push i).eqs) ++ E := by
  rw [argEqs, if_neg h]

/-! ## The inversion -/

section Inversion

variable {Γ : Decls}

/-- **No ground value meets the bare `List`** under a closed signature, so no
tuple type reaches a list type. -/
theorem not_meets_bareList (hΓ : ListClosed Γ) :
    ∀ v : Atom, Ground v → ∀ d ∈ eff (info Γ v), ¬ Meets d (.sym "List")
  | .var _, hg, _, _, _ => hg
  | .symbol s, _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · obtain ⟨ρ, hρ, rfl⟩ := mem_symbol_cands hc
        simp only [Ty.bind_map] at hty
        by_cases isNil : s = "Nil"
        · subst isNil
          rw [hΓ.nil, List.mem_singleton] at hρ
          subst hρ
          exact nil_row_ne _ hty
        · exact (row_ne hΓ hρ isNil _).1 hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .grounded g, _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases grounded_ty hd with rfl | ⟨c, hc, rfl⟩
      · simp [undefinedDeriv, undefinedTy] at hty
      · rcases hc with rfl | rfl | rfl <;> simp [classDeriv] at hty
  | .expression [], _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rw [info_expression] at hc
        simp only [List.map_nil, nodeInfo, tupleTrees, tupleParts, Multiset.map_singleton,
          Multiset.mem_singleton] at hc
        subst hc
        simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .expression (x :: xs), _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rcases mem_expression_cands hc with hf | ht
        · obtain ⟨ρ, hρ, As, R, hs, -, E, -, rfl⟩ := mem_funTrees hf
          simp only [Ty.bind_map] at hty
          rw [rows_info] at hρ
          match x, hρ with
          | .symbol s, hρ =>
              simp only at hρ
              by_cases isNil : s = "Nil"
              · subst isNil
                rw [hΓ.nil, List.mem_singleton] at hρ
                subst hρ
                simp [arrowSplit, listOf] at hs
              by_cases isCons : s = "Cons"
              · subst isCons
                rw [hΓ.cons, List.mem_singleton] at hρ
                subst hρ
                simp only [consRow, arrowSplit_arrow, Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨-, rfl⟩ := hs
                simp [listOf] at hty
              · have away := hΓ.other s isNil isCons ρ hρ
                simp only [offered, hs] at away
                exact (away_ne away _).1 hty
        · obtain ⟨dh, -, p, -, rfl⟩ := mem_tupleTrees_cons ht
          simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty

/-- **The list sort's inversion under a closed signature**: a ground value typable
at `(List τ)` is `Nil`, or a `Cons` of a value typable at `τ` and a value typable
at `(List τ)`. -/
theorem list_inversion (hΓ : ListClosed Γ) (τ : Ty Empty) :
    ∀ v : Atom, Ground v → Typable Γ v (listOf τ) →
      v = .symbol "Nil" ∨
        ∃ x r, v = .expression [.symbol "Cons", x, r] ∧ Typable Γ x τ ∧ Typable Γ r (listOf τ)
  | .var _, hg, _ => hg.elim
  | .symbol s, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · obtain ⟨ρ, hρ, rfl⟩ := mem_symbol_cands hc
        simp only [Ty.bind_map] at hty
        by_cases isNil : s = "Nil"
        · exact .inl (by rw [isNil])
        · exact absurd hty ((row_ne hΓ hρ isNil _).2 τ)
      · simp [undefinedDeriv, undefinedTy, listOf] at hty
  | .grounded g, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases grounded_ty hd with rfl | ⟨c, -, rfl⟩
      · simp [undefinedDeriv, undefinedTy, listOf] at hty
      · simp [classDeriv, listOf] at hty
  | .expression [], _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rw [info_expression] at hc
        simp only [List.map_nil, nodeInfo, tupleTrees, tupleParts, Multiset.map_singleton,
          Multiset.mem_singleton] at hc
        subst hc
        simp [listOf] at hty
      · simp [undefinedDeriv, undefinedTy, listOf] at hty
  | .expression (x :: xs), hg, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, hs, hty⟩ := meets_iff.mp hm
      have hgx : Ground x := hg.1
      rcases mem_eff hd with hc | rfl
      · rcases mem_expression_cands hc with hf | ht
        · obtain ⟨ρ, hρ, As, R, hsplit, hlen, E, hE, rfl⟩ := mem_funTrees hf
          simp only [Ty.bind_map] at hty
          rw [rows_info] at hρ
          match x, hρ, hgx with
          | .symbol s, hρ, _ =>
              simp only at hρ
              by_cases isNil : s = "Nil"
              · subst isNil
                rw [hΓ.nil, List.mem_singleton] at hρ
                subst hρ
                simp [arrowSplit, listOf] at hsplit
              by_cases isCons : s = "Cons"
              · subst isCons
                rw [hΓ.cons, List.mem_singleton] at hρ
                subst hρ
                simp only [consRow, arrowSplit_arrow, Option.some.injEq, Prod.mk.injEq] at hsplit
                obtain ⟨rfl, rfl⟩ := hsplit
                match xs, hlen with
                | [y, r], _ =>
                    right
                    refine ⟨y, r, rfl, ?_⟩
                    have hu1 : ¬ Unchecked (Ty.var "a" : Ty String) := by simp [Unchecked]
                    have hu2 : ¬ Unchecked (listOf (Ty.var "a") : Ty String) := by
                      simp [Unchecked, listOf]
                    rw [List.map_cons, List.map_cons, List.map_nil, argEqs_cons_checked hu1,
                      Multiset.mem_bind] at hE
                    obtain ⟨dy, hdy, hE⟩ := hE
                    rw [Multiset.mem_map] at hE
                    obtain ⟨E2, hE2, rfl⟩ := hE
                    rw [argEqs_cons_checked hu2, Multiset.mem_bind] at hE2
                    obtain ⟨dr, hdr, hE2⟩ := hE2
                    rw [argEqs, Multiset.map_singleton, Multiset.mem_singleton] at hE2
                    subst hE2
                    simp only [List.append_nil, List.cons_append, solves_cons, solves_append] at hs
                    obtain ⟨ha, hy, hl, hr⟩ := hs
                    have hτ : σ (DVar.own "a") = τ := by
                      simp only [listOf, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym,
                        Ty.app.injEq, List.cons.injEq, and_true, true_and] at hty
                      simpa [Function.comp] using hty
                    refine ⟨⟨dy, hdy, meets_of_pushed hy ?_⟩, ⟨dr, hdr, meets_of_pushed hr ?_⟩⟩
                    · rw [← ha]
                      simpa using hτ
                    · rw [← hl]
                      simp [listOf, hτ]
              · have away := hΓ.other s isNil isCons ρ hρ
                simp only [offered, hsplit] at away
                exact absurd hty ((away_ne away _).2 τ)
        · obtain ⟨dh, hdh, p, -, rfl⟩ := mem_tupleTrees_cons ht
          rw [solves_append] at hs
          simp only [Ty.bind_app, List.map_cons, listOf, Ty.app.injEq, List.cons.injEq] at hty
          exact absurd (meets_of_pushed hs.1 hty.1) (not_meets_bareList hΓ x hgx dh hdh)
      · simp [undefinedDeriv, undefinedTy, listOf] at hty

/-- A spine of `Cons` cells ending in `Nil`, each element satisfying `P`. -/
inductive ConsSpine (P : Atom → Prop) : Atom → Prop
  | nil : ConsSpine P (.symbol "Nil")
  | cons (x r : Atom) : P x → ConsSpine P r → ConsSpine P (.expression [.symbol "Cons", x, r])

theorem ground_cons_parts {x r : Atom} (h : Ground (.expression [.symbol "Cons", x, r])) :
    Ground x ∧ Ground r :=
  ⟨h.2.1, h.2.2.1⟩

/-- **A certified ground value is a spine of the fold's own cells**: under a
closed signature, a ground value typable at `(List τ)` is a spine of `Cons` cells
ending in `Nil`, each element typable at `τ`. -/
theorem spine_of_typable (hΓ : ListClosed Γ) (τ : Ty Empty) (v : Atom) (hg : Ground v)
    (ht : Typable Γ v (listOf τ)) : ConsSpine (fun x => Typable Γ x τ) v := by
  induction hn : sizeOf v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
      rcases list_inversion hΓ τ v hg ht with rfl | ⟨x, r, rfl, hx, hr⟩
      · exact .nil
      · refine .cons x r hx (ih (sizeOf r) ?_ r (ground_cons_parts hg).2 hr rfl)
        subst hn
        simp
        omega

/-- Typed once at `(List τ)` gives the spine. -/
theorem spine_of_count (hΓ : ListClosed Γ) (τ : Ty Empty) (v : Atom) (hg : Ground v)
    (one : count (info Γ v) (listOf τ) = 1) : ConsSpine (fun x => Typable Γ x τ) v :=
  spine_of_typable hΓ τ v hg ((typable_iff_count Γ v _).mpr (by omega))

end Inversion

/-! ## The Peano sort -/

/-- A type no `Nat`, from a row of a symbol other than `Z` and `S`. Tuple types
are applications, so they never meet `Nat`. -/
def AwayFromNat : Ty String → Prop
  | .var _ => False
  | .sym s => s ≠ "Nat"
  | .app _ => True

theorem awayNat_ne {ρ : Ty String} (h : AwayFromNat ρ) (f : String → Ty Empty) : ρ.bind f ≠ .sym "Nat" := by
  match ρ, h with
  | .sym s, h => exact fun same => h (by simpa using same)
  | .app ts, _ => simp

/-- **The Peano sort is closed**: `(: Z Nat)`, `(: S (-> Nat Nat))`, and every row
of every other symbol offers a type away from `Nat`. -/
structure NatClosed (Γ : Decls) : Prop where
  zero : Γ "Z" = [.sym "Nat"]
  succ : Γ "S" = [arrow [.sym "Nat"] (.sym "Nat")]
  other : ∀ s, s ≠ "Z" → s ≠ "S" → ∀ ρ ∈ Γ s, AwayFromNat (offered ρ)

/-- A spine of `S` cells ending in `Z`. -/
inductive NatSpine : Atom → Prop
  | zero : NatSpine (.symbol "Z")
  | succ (n : Atom) : NatSpine n → NatSpine (.expression [.symbol "S", n])

section Peano

variable {Γ : Decls}

/-- **The Peano sort's inversion under a closed signature**: a ground value
typable at `Nat` is `Z`, or `S` of a value typable at `Nat`. -/
theorem nat_inversion (hΓ : NatClosed Γ) :
    ∀ v : Atom, Ground v → Typable Γ v (.sym "Nat") →
      v = .symbol "Z" ∨ ∃ n, v = .expression [.symbol "S", n] ∧ Typable Γ n (.sym "Nat")
  | .var _, hg, _ => hg.elim
  | .symbol s, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · obtain ⟨ρ, hρ, rfl⟩ := mem_symbol_cands hc
        simp only [Ty.bind_map] at hty
        by_cases isZ : s = "Z"
        · exact .inl (by rw [isZ])
        by_cases isS : s = "S"
        · subst isS
          rw [hΓ.succ, List.mem_singleton] at hρ
          subst hρ
          simp [arrow] at hty
        · have away := hΓ.other s isZ isS ρ hρ
          cases hs : arrowSplit ρ with
          | none =>
              simp only [offered, hs] at away
              exact absurd hty (awayNat_ne away _)
          | some p =>
              obtain ⟨ts, rfl⟩ := arrowSplit_head hs
              simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .grounded g, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases grounded_ty hd with rfl | ⟨c, hc, rfl⟩
      · simp [undefinedDeriv, undefinedTy] at hty
      · rcases hc with rfl | rfl | rfl <;> simp [classDeriv] at hty
  | .expression [], _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rw [info_expression] at hc
        simp only [List.map_nil, nodeInfo, tupleTrees, tupleParts, Multiset.map_singleton,
          Multiset.mem_singleton] at hc
        subst hc
        simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .expression (x :: xs), _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, hs, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rcases mem_expression_cands hc with hf | ht
        · obtain ⟨ρ, hρ, As, R, hsplit, hlen, E, hE, rfl⟩ := mem_funTrees hf
          simp only [Ty.bind_map] at hty
          rw [rows_info] at hρ
          match x, hρ with
          | .symbol s, hρ =>
              simp only at hρ
              by_cases isZ : s = "Z"
              · subst isZ
                rw [hΓ.zero, List.mem_singleton] at hρ
                subst hρ
                simp [arrowSplit] at hsplit
              by_cases isS : s = "S"
              · subst isS
                rw [hΓ.succ, List.mem_singleton] at hρ
                subst hρ
                simp only [arrowSplit_arrow, Option.some.injEq, Prod.mk.injEq] at hsplit
                obtain ⟨rfl, rfl⟩ := hsplit
                match xs, hlen with
                | [n], _ =>
                    right
                    refine ⟨n, rfl, ?_⟩
                    have hu : ¬ Unchecked (Ty.sym "Nat" : Ty String) := by simp [Unchecked]
                    rw [List.map_cons, List.map_nil, argEqs_cons_checked hu, Multiset.mem_bind] at hE
                    obtain ⟨dn, hdn, hE⟩ := hE
                    rw [argEqs, Multiset.map_singleton, Multiset.mem_singleton] at hE
                    subst hE
                    simp only [List.append_nil, solves_cons] at hs
                    obtain ⟨hn, hns⟩ := hs
                    refine ⟨dn, hdn, meets_of_pushed hns ?_⟩
                    rw [← hn]
                    simp
              · have away := hΓ.other s isZ isS ρ hρ
                simp only [offered, hsplit] at away
                exact absurd hty (awayNat_ne away _)
        · obtain ⟨dh, -, p, -, rfl⟩ := mem_tupleTrees_cons ht
          simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty

/-- **A certified ground value is a Peano spine** under a closed signature. -/
theorem nat_spine_of_typable (hΓ : NatClosed Γ) (v : Atom) (hg : Ground v)
    (ht : Typable Γ v (.sym "Nat")) : NatSpine v := by
  induction hk : sizeOf v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
      rcases nat_inversion hΓ v hg ht with rfl | ⟨n, rfl, hn⟩
      · exact .zero
      · refine .succ n (ih (sizeOf n) ?_ n hg.2.1 hn rfl)
        subst hk
        simp
        omega

end Peano

theorem ConsSpine.head {P : Atom → Prop} {v : Atom} (h : ConsSpine P v) :
    v = .symbol "Nil" ∨ ∃ x r, v = .expression [.symbol "Cons", x, r] := by
  cases h with
  | nil => exact .inl rfl
  | cons x r _ _ => exact .inr ⟨x, r, rfl⟩

theorem NatSpine.head {v : Atom} (h : NatSpine v) :
    v = .symbol "Z" ∨ ∃ n, v = .expression [.symbol "S", n] := by
  cases h with
  | zero => exact .inl rfl
  | succ n _ => exact .inr ⟨n, rfl⟩

/-! ## Discharging a typed entry over an untyped producer

PeTTa's check at a closed formal asks for exactly one derivation meeting it
(`eval_petta_value_typed_once`), where HE's asks for some typing that unifies.
Under functional declarations every value has one effective derivation, so the
check is that derivation meeting the formal (`typed_once_iff`), and the set of
closed types at which an application of a constructor is typed once is read off
its fields' sets like HE's instance sets (`ctor_typed_iff`). An inferred set
built so (a literal its class, a variable every type, a symbol its one row,
an untyped symbol none) discharges the check exactly, multiplicity included, when
every member contains the formal. Without functional declarations a symbol with
two rows meeting the formal is typed twice and PeTTa's guard continues twice
(`Controls.two_rows_twice`); an untyped symbol is typed `%Undefined%`, which no
named formal meets (`Controls.untyped_element_rejected`), where HE's check
accepts it. -/

section Discharge

variable {Γ : Decls}

/-- **Typed once is the one derivation meeting the formal**, under functional
declarations. -/
theorem typed_once_iff (hΓ : Functional Γ) (v : Atom) (T : Ty Empty) :
    count (info Γ v) T = 1 ↔ Meets (theDeriv hΓ v) T := by
  rw [count_eq_ite hΓ]
  unfold Meets
  split_ifs with h <;> simp [h]

theorem freeField_of_unchecked {R A : Ty String} (h : Unchecked A) : FreeField R A := by
  cases A with
  | var x => exact h.elim
  | sym s => exact h
  | app ts => exact h.elim

/-- **The constructor step of an inferred set**: an application of a constructor
is typed once at a named closed type exactly when the range matches it under an
assignment at which every checked field is typed once. -/
theorem ctor_typed_iff (hΓ : Functional Γ) {C : String} {As : List (Ty String)} {R : Ty String}
    (row : Γ C = [arrow As R]) (hC : Constructor As R) (vs : List Atom) (len : vs.length = As.length)
    (T : Ty Empty) (hT : Named T) :
    count (info Γ (.expression (.symbol C :: vs))) T = 1 ↔
      ∃ σ : String → Ty Empty, R.bind σ = T ∧
        ∀ p ∈ List.zip As vs, ¬ Unchecked p.1 → count (info Γ p.2) (p.1.bind σ) = 1 := by
  constructor
  · exact ctor_inversion hΓ row vs len T hT
  · rintro ⟨σ, rfl, fields⟩
    exact ctor_construction hΓ row hC vs len σ fun p hp hfree =>
      fields p hp fun hu => hfree (freeField_of_unchecked hu)

/-- **Discharge is exact**: a producer's values are each typed once at the formal
exactly when each one's derivation meets it, so a call that skips the check
continues once per value, as the checked call does. -/
theorem discharge_iff (hΓ : Functional Γ) (vs : List Atom) (T : Ty Empty) :
    (∀ v ∈ vs, count (info Γ v) T = 1) ↔ ∀ v ∈ vs, Meets (theDeriv hΓ v) T :=
  forall₂_congr fun v _ => typed_once_iff hΓ v T

end Discharge

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (sym num app)
open ClosedSortEvidence (listDecls listDecls_nil listDecls_cons listDecls_other)

/-- Functional declarations whose only `Nil` row is `(List $a)` type `Nil` once at
every list type. -/
theorem count_nil_of {Γ : Decls} (hΓ : Functional Γ) (h : Γ "Nil" = [listOf (.var "a")])
    (τ : Ty Empty) : count (info Γ (sym "Nil")) (listOf τ) = 1 := by
  classical
  rw [count_eq_ite hΓ, if_pos]
  have : theDeriv hΓ (sym "Nil") = ⟨(listOf (.var "a")).map DVar.own, []⟩ := by
    have h' := eff_theDeriv hΓ (sym "Nil")
    rw [info_symbol] at h'
    unfold eff at h'
    simpa [h] using h'.symm
  rw [this]
  refine ⟨fun _ => τ, (solves_append _ _ _).mpr ⟨by simp, ?_⟩⟩
  rw [solves_singleton, Ty.lift_bind_ground]
  simp [listOf, Ty.map]

theorem count_int (Γ : Decls) (n : ℤ) : count (info Γ (num n)) (.sym "Number") = 1 := by
  rw [count_class Γ (g := .int n) rfl]
  simp

theorem closed_constructor (As : List (Ty String)) (R : Ty String) (named : Named R)
    (closedAs : ∀ A ∈ As, A.vars = []) : Constructor As R where
  named := named
  fields := fun A hA => .inr fun y hy => by simp [closedAs A hA] at hy
  distinct := List.pairwise_of_forall_mem_list fun A hA _ _ x _ hx => by
    have := closedAs A hA
    rw [hx] at this
    simp at this

/-! ### A second constructor of the list sort -/

/-- `(List Number)`. -/
abbrev listNum : Ty Empty := listOf (.sym "Number")

/-- `pair`'s row, `(-> Number (List Number) (List Number))`. -/
abbrev pairRow : Ty String := arrow [.sym "Number", listOf (.sym "Number")] (listOf (.sym "Number"))

/-- The list declarations with a second constructor `pair`. -/
def pairDecls : Decls := fun s =>
  if s = "Nil" then [listOf (.var "a")] else if s = "Cons" then [consRow]
  else if s = "pair" then [pairRow] else []

theorem pairDecls_functional : Functional pairDecls := by
  intro s
  unfold pairDecls
  split_ifs <;> simp

/-- `(Cons 1 (pair 2 Nil))`. -/
def pairValue : Atom := app "Cons" [num 1, app "pair" [num 2, sym "Nil"]]

/-- **A second constructor breaks the spine**: `(Cons 1 (pair 2 Nil))` is ground and
typed once at `(List Number)` (stable-fixed PeTTa and CeTTa certify it), is not a
spine of `Cons` cells, and the signature is not closed. -/
theorem pair_certified :
    count (info pairDecls pairValue) listNum = 1 ∧ Ground pairValue ∧
      ¬ ConsSpine (fun _ => True) pairValue ∧ ¬ ListClosed pairDecls := by
  have inner : count (info pairDecls (app "pair" [num 2, sym "Nil"])) listNum = 1 := by
    have hC : Constructor [.sym "Number", listOf (.sym "Number")] (listOf (.sym "Number")) :=
      closed_constructor _ _ (by simp [Named, listOf]) (by simp [listOf])
    have := ctor_construction pairDecls_functional (C := "pair") (by simp [pairDecls]) hC
      [num 2, sym "Nil"] rfl (fun _ => .sym "Number") (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl
        · exact count_int _ 2
        · simpa [listOf] using count_nil_of pairDecls_functional (by simp [pairDecls]) (.sym "Number"))
    simpa [listOf] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ctor_construction pairDecls_functional (C := "Cons") (by simp [pairDecls])
      cons_constructor [num 1, app "pair" [num 2, sym "Nil"]] rfl (fun _ => .sym "Number") (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl
        · exact count_int _ 1
        · simpa [listOf] using inner)
    simpa [pairValue, listOf] using this
  · simp [pairValue, Ground, GroundAll]
  · intro h
    cases h with
    | cons x r _ hr =>
        rcases hr.head with same | ⟨_, _, same⟩ <;> simp [app, sym] at same
  · intro h
    have := h.other "pair" (by decide) (by decide) pairRow (by simp [pairDecls])
    simp [offered, pairRow, AwayFromList, listOf] at this

/-! ### A variable tail -/

theorem listDecls_functional : Functional listDecls := by
  intro s
  by_cases h1 : s = "Nil"
  · subst h1
    simp [listDecls_nil]
  by_cases h2 : s = "Cons"
  · subst h2
    simp [listDecls_cons]
  · simp [listDecls_other h1 h2]

/-- The closed list signature `{Nil, Cons}` is closed. -/
theorem listDecls_closed : ListClosed listDecls where
  nil := listDecls_nil
  cons := listDecls_cons
  other := fun s h1 h2 ρ hρ => by simp [listDecls_other h1 h2] at hρ

/-- **A variable tail is certified**: under the closed signature `(Cons 1 $x)` is
typed once at `(List Number)` and is no spine: groundness is needed. -/
theorem var_tail_certified :
    count (info listDecls (app "Cons" [num 1, .var "x"])) listNum = 1 ∧
      ¬ Ground (app "Cons" [num 1, .var "x"]) ∧
      ¬ ConsSpine (fun _ => True) (app "Cons" [num 1, .var "x"]) := by
  refine ⟨?_, ?_, ?_⟩
  · have := ctor_construction listDecls_functional (C := "Cons") listDecls_cons
      cons_constructor [num 1, .var "x"] rfl (fun _ => .sym "Number") (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl
        · exact count_int _ 1
        · exact count_var _ _ _)
    simpa [listOf] using this
  · simp [Ground, GroundAll]
  · intro h
    cases h with
    | cons x r _ hr =>
        rcases hr.head with same | ⟨_, _, same⟩ <;> simp at same

/-! ### A second successor -/

/-- `(-> Nat Nat)`. -/
abbrev succRow : Ty String := arrow [.sym "Nat"] (.sym "Nat")

/-- `(: Z Nat)`, `(: S (-> Nat Nat))` and a second successor `(: P (-> Nat Nat))`. -/
def natPDecls : Decls := fun s =>
  if s = "Z" then [.sym "Nat"] else if s = "S" then [succRow] else if s = "P" then [succRow]
  else []

theorem natPDecls_functional : Functional natPDecls := by
  intro s
  unfold natPDecls
  split_ifs <;> simp

/-- `(S (P Z))`. -/
def sPZ : Atom := app "S" [app "P" [sym "Z"]]

/-- **A second successor breaks the Peano spine**: `(S (P Z))` is typed once at
`Nat` (stable-fixed PeTTa and CeTTa certify it; `toint` answers nothing on it),
is no Peano spine, and the signature is not closed. -/
theorem peano_certified :
    count (info natPDecls sPZ) (.sym "Nat") = 1 ∧ Ground sPZ ∧ ¬ NatSpine sPZ ∧
      ¬ NatClosed natPDecls := by
  have hC : Constructor [.sym "Nat"] (.sym "Nat") :=
    closed_constructor _ _ (by simp [Named]) (by simp)
  have z : count (info natPDecls (sym "Z")) (.sym "Nat") = 1 := by
    rw [count_symbol_closed natPDecls "Z" (.sym "Nat") (by simp [natPDecls, Ty.lift])]
    simp
  have pz : count (info natPDecls (app "P" [sym "Z"])) (.sym "Nat") = 1 := by
    have := ctor_construction natPDecls_functional (C := "P") (by simp [natPDecls]) hC
      [sym "Z"] rfl (fun _ => .sym "Nat") (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
        subst hp
        simpa using z)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ctor_construction natPDecls_functional (C := "S") (by simp [natPDecls]) hC
      [app "P" [sym "Z"]] rfl (fun _ => .sym "Nat") (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
        subst hp
        simpa using pz)
    simpa [sPZ] using this
  · simp [sPZ, Ground, GroundAll]
  · intro h
    cases h with
    | succ n hn =>
        rcases hn.head with same | ⟨_, same⟩ <;> simp [app, sym] at same
  · intro h
    have := h.other "P" (by decide) (by decide) succRow (by simp [natPDecls])
    simp [offered, succRow, AwayFromNat] at this

/-! ### Discharge: two rows, and an untyped element -/

/-- `(: d Number)` and `(: d $t)`. -/
def twoRowDecls : Decls := fun s => if s = "d" then [.sym "Number", .var "t"] else []

/-- **Two rows meeting the formal type a value twice**: PeTTa's guard continues
twice (`(f d)` answers `1 1` in stable-fixed PeTTa and CeTTa), so a discharge that
continues once changes the multiplicity. -/
theorem two_rows_twice : count (info twoRowDecls (sym "d")) (.sym "Number") = 2 := by
  classical
  unfold count
  rw [info_symbol]
  unfold eff
  have rows : twoRowDecls "d" = [.sym "Number", .var "t"] := by simp [twoRowDecls]
  simp only [rows, List.map_cons, List.map_nil]
  rw [if_neg (by simp)]
  rw [Multiset.filter_eq_self.mpr]
  · simp
  · intro d hd
    simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨fun _ => default, (solves_append _ _ _).mpr ⟨by simp,
        (solves_singleton _ _).mpr (by simp [Ty.lift_bind_ground])⟩⟩
    · exact ⟨fun _ => .sym "Number", (solves_append _ _ _).mpr ⟨by simp,
        (solves_singleton _ _).mpr (by simp [Ty.lift_bind_ground])⟩⟩

/-- **An untyped element is rejected**: `foo` has no row, so `(Cons foo Nil)` is
not typed at `(List Number)` (PeTTa types it `(List %Undefined%)`; stable-fixed
PeTTa and CeTTa answer nothing for `lsum` over it), where HE's check accepts an
untyped element. -/
theorem untyped_element_rejected :
    count (info listDecls (sym "foo")) (.sym "Number") = 0 ∧
      count (info listDecls (app "Cons" [sym "foo", sym "Nil"])) listNum = 0 := by
  classical
  have foo : count (info listDecls (sym "foo")) (.sym "Number") = 0 := by
    rw [count_eq_ite listDecls_functional, if_neg]
    have h := eff_theDeriv listDecls_functional (sym "foo")
    rw [info_symbol, listDecls_other (by decide) (by decide)] at h
    unfold eff at h
    simp only [List.map_nil, Multiset.coe_nil, Multiset.card_zero, if_true] at h
    rw [← Multiset.singleton_inj.mp h]
    rintro ⟨σ, hσ⟩
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hσ
    simp [undefinedDeriv, undefinedTy] at hσ
  refine ⟨foo, ?_⟩
  have le := count_le_one listDecls_functional (app "Cons" [sym "foo", sym "Nil"]) listNum
  by_contra ne
  have one : count (info listDecls (app "Cons" [sym "foo", sym "Nil"])) listNum = 1 := by omega
  obtain ⟨σ, hσ, fields⟩ := ctor_inversion listDecls_functional listDecls_cons _ rfl listNum
    (by simp [Named, listOf]) one
  have ha : σ "a" = .sym "Number" := by simpa [listOf] using hσ
  have field := fields (.var "a", sym "foo") (by simp) (by simp [Unchecked])
  rw [Ty.bind_var', ha, foo] at field
  cases field

/-! ### A tuple type at the sort -/

/-- The list declarations with `(: L List)`. -/
def lDecls : Decls := fun s => if s = "L" then [.sym "List"] else listDecls s

/-- **A tuple type reaches the sort**: `(L 5)` is typable at `(List Number)` through
its tuple type (stable-fixed PeTTa and CeTTa certify it), is no spine, and the bare
`List` row breaks the closure. -/
theorem tuple_certified :
    Typable lDecls (app "L" [num 5]) listNum ∧ Ground (app "L" [num 5]) ∧
      ¬ ConsSpine (fun _ => True) (app "L" [num 5]) ∧ ¬ ListClosed lDecls := by
  refine ⟨⟨⟨.app [.sym "List", .sym "Number"], []⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [info_expression]
    simp [nodeInfo, funTrees, info_symbol, lDecls, arrowSplit, tupleTrees, tupleParts, eff,
      info_int, Deriv.push, classDeriv]
  · exact meets_iff.mpr ⟨fun _ => default, by simp, by simp [listOf]⟩
  · simp [Ground, GroundAll]
  · intro h
    rcases h.head with same | ⟨_, _, same⟩ <;> simp at same
  · intro h
    have := h.other "L" (by decide) (by decide) (.sym "List") (by simp [lDecls])
    simp [offered, arrowSplit, AwayFromList] at this

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CertifiedSpines
