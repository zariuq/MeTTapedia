import Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping.Rules

/-!
# Exhaustive heads: pattern-matrix usefulness

`lib_det`'s `covers/2` (after Maranget) decides whether the rows of a pattern matrix leave no
vector of values of the given types unmatched. A column of variables only is dropped (the
default matrix); a column whose type has constructors is split by them (`specialize`); any other
column is covered by its variable rows only. Unions are split by alternative and a newtype by its
representation. Prolog's `covers/2` terminates because a column of variables only is dropped,
never split; here fuel makes the recursion structural, and running out of it answers `false`.

`coverN_sound`: every vector of values fitting the types matches some row. Patterns are linear:
their variables are anonymous, as `lib_det` keeps only heads without a repeated variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping

inductive Pat where
  | var
  | lit (l : Lit)
  | sym (s : String)
  /-- `(cons H T)`: a nonempty list. -/
  | cons (h t : Pat)
  /-- An expression pattern: `()`, a tuple, or a constructor application `(c P₁ .. Pₙ)`. -/
  | app (ps : List Pat)

namespace Pat

mutual
/-- Head unification with a linear pattern: an unbound value matches every pattern. -/
def unify : Pat → Term → Bool
  | _, .var _ => true
  | .var, _ => true
  | .lit l, .lit l' => decide (l = l')
  | .sym s, .sym s' => decide (s = s')
  | .cons h t, .app (x :: xs) => h.unify x && t.unify (.app xs)
  | .app ps, .app xs => unifyRow ps xs
  | _, _ => false
def unifyRow : List Pat → List Term → Bool
  | [], [] => true
  | p :: ps, x :: xs => p.unify x && unifyRow ps xs
  | _, _ => false
end

theorem unify_var (p : Pat) (x : Nat) : p.unify (.var x) = true := by
  cases p <;> simp [unify]

theorem var_unify (v : Term) : Pat.var.unify v = true := by
  cases v <;> simp [unify]

theorem unifyRow_append : ∀ {qs : List Pat} {fs : List Term} (ps : List Pat) (vs : List Term),
    qs.length = fs.length →
      unifyRow (qs ++ ps) (fs ++ vs) = (unifyRow qs fs && unifyRow ps vs)
  | [], [], _, _, _ => by simp [unifyRow]
  | q :: qs, f :: fs, ps, vs, h => by
      simp only [List.cons_append, unifyRow, Bool.and_assoc,
        unifyRow_append ps vs (by simpa using h)]

def isVar : Pat → Bool
  | .var => true
  | _ => false

end Pat

/-- The constructors a column is split by. -/
inductive Con where
  | nil | cons | lit (l : Lit) | sym (s : String) | ctor (c : String) | tuple

/-- `constructors/2`: lists, `Bool`, names by their declared constructors and symbols, a tag by
itself, and tuples, each with its field types. Other types have none. -/
def constructors (sig : Sig) : Ty → List (Con × List Ty)
  | .list E => [(.nil, []), (.cons, [E, .list E])]
  | .prim .bool => [(.lit (.bool true), []), (.lit (.bool false), [])]
  | .name N => sig.ctors.filterMap (fun d => if d.2.2 = N then some (.ctor d.1, d.2.1) else none) ++
      sig.symbols.filterMap (fun d => if d.2 = N then some (.sym d.1, []) else none) ++
      if sig.tag N then [(.sym N, [])] else []
  | .tuple Ts => [(.tuple, Ts)]
  | _ => []

/-- `pattern_fields/4`: the fields of a pattern under a constructor with `n` fields. -/
def Pat.fields : Pat → Con → Nat → Option (List Pat)
  | .var, _, n => some (List.replicate n .var)
  | .app [], .nil, 0 => some []
  | .cons h t, .cons, 2 => some [h, t]
  | .lit l, .lit l', 0 => if l = l' then some [] else none
  | .sym s, .sym s', 0 => if s = s' then some [] else none
  | .app (.sym c :: ps), .ctor c', n => if c = c' ∧ ps.length = n then some ps else none
  | .app ps, .tuple, n => if ps.length = n then some ps else none
  | _, _, _ => none

theorem Pat.fields_length {p : Pat} {k : Con} {n : Nat} {qs : List Pat}
    (h : p.fields k n = some qs) : qs.length = n := by
  unfold Pat.fields at h
  split at h <;> (try split at h) <;> cases h <;> simp_all

def specialize (rows : List (List Pat)) (k : Con) (n : Nat) : List (List Pat) :=
  rows.filterMap fun
    | p :: ps => (p.fields k n).map (· ++ ps)
    | [] => none

def defaultRows (rows : List (List Pat)) : List (List Pat) :=
  rows.filterMap fun
    | .var :: ps => some ps
    | _ => none

variable (sig : Sig)

/-- `covers/2` with fuel. -/
def coverN : Nat → List (List Pat) → List Ty → Bool
  | _, rows, [] => rows.any List.isEmpty
  | 0, _, _ :: _ => false
  | n + 1, rows, T :: Ts =>
      if rows.all (fun r => r.head?.all Pat.isVar) then coverN n (defaultRows rows) Ts
      else match T with
        | .union Us => !Us.isEmpty && Us.all fun U => coverN n rows (U :: Ts)
        | .newtype N => match sig.newtypes N with
          | some R => coverN n rows (R :: Ts)
          | none => coverN n (defaultRows rows) Ts
        | T => match constructors sig T with
          | [] => coverN n (defaultRows rows) Ts
          | Ks => Ks.all fun k => coverN n (specialize rows k.1 k.2.length) (k.2 ++ Ts)

/-- A sound coverage test: every vector of values fitting the types matches some row. -/
def CoverSound (cover : List (List Pat) → List Ty → Bool) : Prop :=
  ∀ rows Ts, cover rows Ts = true → ∀ vs, FitsAll sig vs Ts →
    ∃ row ∈ rows, Pat.unifyRow row vs = true

/-- How a value is built by a constructor from its fields. -/
inductive Decomp : Con → Term → List Term → Prop
  | nil : Decomp .nil (.app []) []
  | cons (x : Term) (xs : List Term) : Decomp .cons (.app (x :: xs)) [x, .app xs]
  | lit (l : Lit) : Decomp (.lit l) (.lit l) []
  | sym (s : String) : Decomp (.sym s) (.sym s) []
  | ctor (c : String) (fs : List Term) : Decomp (.ctor c) (.app (.sym c :: fs)) fs
  | tuple (xs : List Term) : Decomp .tuple (.app xs) xs

variable {sig}

/-- Every bound value of a type with constructors is built by one of them. -/
theorem constructors_complete {v : Term} {T : Ty} (h : Fits sig v T) (hv : ∀ x, v ≠ .var x)
    (hK : constructors sig T ≠ []) :
    ∃ k ∈ constructors sig T, ∃ fs, Decomp k.1 v fs ∧ FitsAll sig fs k.2 := by
  cases h with
  | var x => exact absurd rfl (hv x)
  | lit l =>
      cases l with
      | bool b =>
          exact ⟨(.lit (.bool b), []), by cases b <;> simp [constructors, Lit.prim], [], .lit _, .nil⟩
      | num | str => simp [constructors, Lit.prim] at hK
  | sym hs =>
      rename_i s N
      have h₁ : ((Con.sym s, []) : Con × List Ty) ∈ sig.symbols.filterMap
          (fun d => if d.2 = N then some (Con.sym d.1, []) else none) :=
        List.mem_filterMap.2 ⟨(s, N), hs, by simp⟩
      exact ⟨(.sym s, []), List.mem_append_left _ (List.mem_append_right _ h₁), [], .sym s, .nil⟩
  | tag ht =>
      rename_i N
      have h₁ : ((Con.sym N, []) : Con × List Ty) ∈
          (if sig.tag N then [(Con.sym N, [])] else [] : List (Con × List Ty)) := by simp [ht]
      exact ⟨(.sym N, []), List.mem_append_right _ h₁, [], .sym N, .nil⟩
  | ctor hc len h =>
      rename_i c N fs As
      have h₁ : ((Con.ctor c, As) : Con × List Ty) ∈ sig.ctors.filterMap
          (fun d => if d.2.2 = N then some (Con.ctor d.1, d.2.1) else none) :=
        List.mem_filterMap.2 ⟨(c, As, N), hc, by simp⟩
      exact ⟨(.ctor c, As), List.mem_append_left _ (List.mem_append_left _ h₁), fs, .ctor c fs, (fitsAll_iff sig _ _).2 ⟨len, h⟩⟩
  | list hxs =>
      rename_i xs E
      cases xs with
      | nil => exact ⟨(.nil, []), by simp [constructors], [], .nil, .nil⟩
      | cons x rest =>
          exact ⟨(.cons, [E, .list E]), by simp [constructors], _, .cons x rest,
            .cons (hxs x (by simp)) (.cons (.list fun y hy => hxs y (by simp [hy])) .nil)⟩
  | tuple len h =>
      exact ⟨(.tuple, _), by simp [constructors], _, .tuple _, (fitsAll_iff sig _ _).2 ⟨len, h⟩⟩
  | unknown | tvar | rigid | newtype | arrow | union => simp [constructors] at hK

/-- Matching the fields of a pattern matches the value they build. -/
theorem fields_match {k : Con} {v : Term} {fs : List Term} (hd : Decomp k v fs) {p : Pat}
    {qs : List Pat} (hf : p.fields k fs.length = some qs) (hm : Pat.unifyRow qs fs = true) :
    p.unify v = true := by
  cases p with
  | var => exact Pat.var_unify v
  | lit l => cases hd <;> simp_all [Pat.fields, Pat.unify]
  | sym s => cases hd <;> simp_all [Pat.fields, Pat.unify]
  | cons h t =>
      cases hd <;> simp [Pat.fields] at hf
      subst hf; simpa [Pat.unify, Pat.unifyRow] using hm
  | app ps =>
      cases hd with
      | nil => cases ps <;> simp_all [Pat.fields, Pat.unify, Pat.unifyRow]
      | ctor c fs =>
          cases ps with
          | nil => simp [Pat.fields] at hf
          | cons q ps' =>
              cases q <;> simp [Pat.fields] at hf
              obtain ⟨⟨rfl, -⟩, rfl⟩ := hf
              simp [Pat.unify, Pat.unifyRow, hm]
      | tuple xs =>
          cases ps <;> simp [Pat.fields] at hf <;> obtain ⟨-, rfl⟩ := hf <;>
            simpa [Pat.unify] using hm
      | cons | lit | sym => cases ps <;> simp_all [Pat.fields]

theorem mem_specialize {rows : List (List Pat)} {k : Con} {n : Nat} {r : List Pat}
    (h : r ∈ specialize rows k n) :
    ∃ p ps qs, p :: ps ∈ rows ∧ p.fields k n = some qs ∧ r = qs ++ ps := by
  obtain ⟨row, hrow, hr⟩ := List.mem_filterMap.1 h
  match row, hrow, hr with
  | p :: ps, hrow, hr =>
      obtain ⟨qs, hq, rfl⟩ := Option.map_eq_some_iff.1 hr
      exact ⟨p, ps, qs, hrow, hq, rfl⟩

theorem mem_defaultRows {rows : List (List Pat)} {r : List Pat} (h : r ∈ defaultRows rows) :
    .var :: r ∈ rows := by
  obtain ⟨row, hrow, hr⟩ := List.mem_filterMap.1 h
  match row, hrow, hr with
  | .var :: ps, hrow, hr => cases hr; exact hrow

/-- The default matrix is sound for a column of any type. -/
theorem default_sound {rows : List (List Pat)} {v : Term} {vs : List Term}
    (h : ∃ row ∈ defaultRows rows, Pat.unifyRow row vs = true) :
    ∃ row ∈ rows, Pat.unifyRow row (v :: vs) = true := by
  obtain ⟨row, hrow, hm⟩ := h
  exact ⟨_, mem_defaultRows hrow, by simp [Pat.unifyRow, Pat.var_unify, hm]⟩

theorem cover_nil {rows : List (List Pat)} (h : rows.any List.isEmpty = true) :
    ∃ row ∈ rows, Pat.unifyRow row [] = true := by
  obtain ⟨row, hrow, he⟩ := List.any_eq_true.1 h
  exact ⟨row, hrow, by simp at he; simp [he, Pat.unifyRow]⟩

/-- `covers_sound`: a covering matrix leaves no vector of fitting values unmatched. -/
theorem coverN_sound : ∀ n : Nat, CoverSound sig (coverN sig n) := by
  intro n
  induction n with
  | zero =>
      intro rows Ts h vs hvs
      cases Ts with
      | nil => cases hvs; exact cover_nil h
      | cons => simp [coverN] at h
  | succ n ih =>
      intro rows Ts h vs hvs
      cases Ts with
      | nil => cases hvs; exact cover_nil h
      | cons T Ts =>
          obtain ⟨v, vs', hv, hvs', rfl⟩ : ∃ v vs', Fits sig v T ∧ FitsAll sig vs' Ts ∧ vs = v :: vs' := by
            cases hvs with | cons hv hvs => exact ⟨_, _, hv, hvs, rfl⟩
          simp only [coverN] at h
          split at h
          · exact default_sound (ih _ _ h _ hvs')
          split at h
          · next Us =>
              simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
                List.all_eq_true] at h
              by_cases hx : ∃ x, v = .var x
              · obtain ⟨x, rfl⟩ := hx
                obtain ⟨U, hU⟩ := List.exists_mem_of_ne_nil _ h.1
                exact ih _ _ (h.2 U hU) _ (.cons (.var x U) hvs')
              · cases hv with
                | var x => exact absurd ⟨x, rfl⟩ hx
                | union hU hvU => exact ih _ _ (h.2 _ hU) _ (.cons hvU hvs')
          · next N =>
              split at h
              · next R hR => exact ih _ _ h _ (.cons ((fits_newtype sig hR v).1 hv) hvs')
              · exact default_sound (ih _ _ h _ hvs')
          · split at h
            · exact default_sound (ih _ _ h _ hvs')
            · next hK =>
                rw [List.all_eq_true] at h
                have hsplit : ∀ k ∈ constructors sig T, ∀ fs, FitsAll sig fs k.2 →
                    ∃ p ps qs, p :: ps ∈ rows ∧ p.fields k.1 k.2.length = some qs ∧
                      Pat.unifyRow qs fs = true ∧ Pat.unifyRow ps vs' = true := by
                  intro k hk fs hfs
                  obtain ⟨r, hr, hm⟩ := ih _ _ (h k hk) _ (List.rel_append hfs hvs')
                  obtain ⟨p, ps, qs, hp, hq, rfl⟩ := mem_specialize hr
                  rw [Pat.unifyRow_append _ _ ((Pat.fields_length hq).trans hfs.length_eq.symm),
                    Bool.and_eq_true] at hm
                  exact ⟨p, ps, qs, hp, hq, hm.1, hm.2⟩
                by_cases hx : ∃ x, v = .var x
                · obtain ⟨x, rfl⟩ := hx
                  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ hK
                  have hfs : FitsAll sig (k.2.map fun _ => Term.var x) k.2 := by
                    simp only [FitsAll, List.forall₂_map_left_iff]
                    exact List.forall₂_same.2 fun T _ => .var x T
                  obtain ⟨p, ps, _, hp, _, _, hm⟩ := hsplit k hk _ hfs
                  exact ⟨_, hp, by simp [Pat.unifyRow, Pat.unify_var, hm]⟩
                · obtain ⟨k, hk, fs, hd, hfs⟩ :=
                    constructors_complete hv (fun x h => hx ⟨x, h⟩) hK
                  obtain ⟨p, ps, qs, hp, hq, hmq, hm⟩ := hsplit k hk fs hfs
                  have hp' := fields_match hd (hfs.length_eq ▸ hq) hmq
                  exact ⟨_, hp, by simp [Pat.unifyRow, hp', hm]⟩

namespace Examples

def bools : List (List Pat) := [[.lit (.bool true)], [.lit (.bool false)]]

/-- `True` and `False` cover `Bool`; `True` alone does not. -/
theorem bool_heads :
    coverN Examples.nat 3 bools [.prim .bool] = true ∧
      coverN Examples.nat 3 [[.lit (.bool true)]] [.prim .bool] = false := by decide

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping
