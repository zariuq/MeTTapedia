import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol
import Mathlib.Logic.Equiv.Fintype
import Std.Data.String.ToNat

/-!
# Canonical declaration names and semantic renaming

The first-occurrence canonicalizer is connected to injective renaming of the
variables of a declaration. Its finite support map extends to a permutation
of all names. Consequently equal canonical forms justify the existing
derivation-by-derivation transport of type counts; this is not merely an
idempotence property of the declaration index.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

namespace RowAlpha

/-- The canonical name determined by a completed first-occurrence table. -/
def indexName (seen : List String) (x : String) : String := toString (seen.idxOf x)

theorem idxOf_of_some {seen : List String} {x : String} {i : Nat}
    (h : seen.idxOf? x = some i) : seen.idxOf x = i := by
  change seen.findIdx (fun y => y == x) = i
  rw [List.findIdx_eq_getD_findIdx?]
  change (seen.idxOf? x).getD seen.length = i
  rw [h]
  rfl

mutual
theorem canonAux_prefix (seen : List String) :
    ∀ t : Ty String, seen <+: (Ty.canonAux seen t).2
  | .var x => by
      cases h : seen.idxOf? x <;> simp only [Ty.canonAux, h]
      · exact ⟨[x], rfl⟩
      · exact ⟨[], by simp⟩
  | .sym _ => ⟨[], by simp [Ty.canonAux]⟩
  | .app ts => canonAuxList_prefix seen ts

theorem canonAuxList_prefix (seen : List String) :
    ∀ ts : List (Ty String), seen <+: (Ty.canonAuxList seen ts).2
  | [] => ⟨[], by simp [Ty.canonAuxList]⟩
  | t :: ts =>
      (canonAux_prefix seen t).trans (canonAuxList_prefix (Ty.canonAux seen t).2 ts)
end

mutual
theorem canonAux_contains (seen : List String) :
    ∀ (t : Ty String), ∀ x ∈ t.vars, x ∈ (Ty.canonAux seen t).2
  | .var x, y, hy => by
      simp only [Ty.vars_var, List.mem_singleton] at hy
      subst y
      cases h : seen.idxOf? x with
      | none => simp [Ty.canonAux, h]
      | some i =>
          simp only [Ty.canonAux, h]
          exact List.isSome_idxOf?.mp (by simp [h])
  | .sym _, _, h => by simp at h
  | .app ts, x, hx => by
      rw [Ty.vars_app] at hx
      exact canonAuxList_contains seen ts x hx

theorem canonAuxList_contains (seen : List String) :
    ∀ (ts : List (Ty String)), ∀ x ∈ ts.flatMap Ty.vars, x ∈ (Ty.canonAuxList seen ts).2
  | [], _, h => by simp at h
  | t :: ts, x, hx => by
      simp only [List.flatMap_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact (canonAuxList_prefix (Ty.canonAux seen t).2 ts).subset
          (canonAux_contains seen t x hx)
      · exact canonAuxList_contains (Ty.canonAux seen t).2 ts x hx
end

theorem map_congr {V W : Type} {f g : V → W} (t : Ty V)
    (h : ∀ x ∈ t.vars, f x = g x) : t.map f = t.map g :=
  Ty.bind_congr t fun x hx => congrArg Ty.var (h x hx)

mutual
theorem canonAux_eq_map (seen : List String) : ∀ t : Ty String,
    (Ty.canonAux seen t).1 = t.map (indexName (Ty.canonAux seen t).2)
  | .var x => by
      cases h : seen.idxOf? x with
      | none =>
          have hx : x ∉ seen := List.idxOf?_eq_none_iff.mp h
          simp [Ty.canonAux, h, indexName, List.idxOf_append_of_notMem hx]
      | some i => simp [Ty.canonAux, h, indexName, idxOf_of_some h]
  | .sym _ => rfl
  | .app ts => by
      simp only [Ty.canonAux, Ty.map_app]
      exact congrArg Ty.app (canonAuxList_eq_map seen ts)

theorem canonAuxList_eq_map (seen : List String) : ∀ ts : List (Ty String),
    (Ty.canonAuxList seen ts).1 = ts.map (fun t => t.map (indexName (Ty.canonAuxList seen ts).2))
  | [] => rfl
  | t :: ts => by
      simp only [Ty.canonAuxList, List.map_cons]
      rw [canonAux_eq_map, canonAuxList_eq_map]
      congr 1
      exact map_congr t fun x hx => congrArg toString
        ((canonAuxList_prefix (Ty.canonAux seen t).2 ts).idxOf_eq_of_mem
          (canonAux_contains seen t x hx))
end

theorem indexName_inj {seen : List String} {x y : String} (hx : x ∈ seen)
    (h : indexName seen x = indexName seen y) : x = y := by
  apply (List.idxOf_inj hx).mp
  exact Nat.repr_injective h

/-- Every canonicalization is an actual permutation of the row's names. -/
theorem canon_is_permutation (t : Ty String) :
    ∃ p : Equiv.Perm String, t.canon = t.map p := by
  classical
  let support := t.vars.toFinset
  let name : support → String := fun x => indexName (Ty.canonAux [] t).2 x.val
  have hn : Function.Injective name := by
    intro x y h
    apply Subtype.ext
    exact indexName_inj (canonAux_contains [] t x.val (List.mem_toFinset.mp x.property)) h
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun x : support => x.val) name Subtype.val_injective hn
  refine ⟨p, (canonAux_eq_map [] t).trans ?_⟩
  exact map_congr t fun x hx => (hp ⟨x, by simpa [support] using hx⟩).symm

/-- Equality of canonical names produces a globally injective row renaming. -/
theorem rowRen_of_alphaEq {t u : Ty String} (h : AlphaEq t u) : RowRen t u := by
  obtain ⟨p, hp⟩ := canon_is_permutation t
  obtain ⟨q, hq⟩ := canon_is_permutation u
  refine ⟨fun x => q.symm (p x), q.symm.injective.comp p.injective, ?_⟩
  have hh : t.map p = u.map q := hp.symm.trans ((show t.canon = u.canon from h).trans hq)
  have hr := congrArg (Ty.map q.symm) hh
  rw [Ty.map_map, Ty.map_map] at hr
  have hu : u.map (q.symm ∘ q) = u := by
    have hc : q.symm ∘ q = id := by funext x; exact q.symm_apply_apply x
    rw [hc, Ty.map_id']
  rw [hu] at hr
  exact hr.symm

/-- Choosing alpha-equivalent rows, in the same positions, preserves every
closed intrinsic type-count observation. -/
theorem count_alpha_rows {Γ Γ' : Decls}
    (h : ∀ s, List.Forall₂ AlphaEq (Γ s) (Γ' s))
    (v : Mettapedia.Languages.MeTTa.OSLFCore.Atom) (T : Ty Empty) :
    count (info Γ v) T = count (info Γ' v) T :=
  count_renamed_rows (fun s => (h s).imp fun _ _ hab => rowRen_of_alphaEq hab) v T

/-- The metatype fallback of a guard also survives the representative change. -/
theorem guardCount_alpha_rows {Γ Γ' : Decls}
    (h : ∀ s, List.Forall₂ AlphaEq (Γ s) (Γ' s))
    (v : Mettapedia.Languages.MeTTa.OSLFCore.Atom) (T : Ty Empty) (kind : String) :
    guardCount (info Γ v) T kind = guardCount (info Γ' v) T kind := by
  unfold guardCount
  rw [count_alpha_rows h]

/-- Closed argument protocols keep every guard multiplicity. -/
theorem argCount_alpha_rows {Γ Γ' : Decls}
    (h : ∀ s, List.Forall₂ AlphaEq (Γ s) (Γ' s))
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String) :
    ∀ (As : List (Ty Empty)) (vs : List Mettapedia.Languages.MeTTa.OSLFCore.Atom),
      argCount Γ kind As vs = argCount Γ' kind As vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | A :: As, v :: vs => by
      simp only [argCount, guardCount_alpha_rows h, argCount_alpha_rows h kind As vs]

/-- A closed row's entire body/result protocol is independent of the chosen
alpha-equivalent declaration representatives, including duplicate answers. -/
theorem chainCall_closed_alpha_rows {Γ Γ' : Decls}
    (h : ∀ s, List.Forall₂ AlphaEq (Γ s) (Γ' s))
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String)
    (body : List Mettapedia.Languages.MeTTa.OSLFCore.Atom →
      Multiset Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (As : List (Ty Empty)) (R : Ty Empty)
    (vs : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    chainCall Γ kind body (arrow (As.map Ty.lift) R.lift) vs =
      chainCall Γ' kind body (arrow (As.map Ty.lift) R.lift) vs := by
  rw [chainCall_closed, chainCall_closed, argCount_alpha_rows h]
  congr 1
  exact Multiset.bind_congr fun r _ => by rw [guardCount_alpha_rows h]

theorem eqn_map_map {U V W : Type} (f : U → V) (g : V → W) (S : List (Eqn U)) :
    (S.map (Eqn.map f)).map (Eqn.map g) = S.map (Eqn.map (g ∘ f)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, Eqn.map, Ty.map_map]

open Classical in
theorem filter_map_store {U V : Type} {g : U → V} (hg : Function.Injective g)
    (ss : Multiset (List (Eqn U))) :
    (ss.map (List.map (Eqn.map g))).filter Sat =
      (ss.filter Sat).map (List.map (Eqn.map g)) := by
  classical
  rw [Multiset.filter_map]
  congr 1
  exact Multiset.filter_congr fun S _ => sat_map_injective hg S

/-- The whole answer-store bag of a request is equivariant, not just its
cardinality. The embedding of each fresh derivation is renamed with it. -/
theorem getType_rename {U V : Type} {g : U → V} (hg : Function.Injective g)
    (e : DVar → U) (S : List (Eqn U)) (T : Ty U) (j : Info) :
    getType (g ∘ e) (S.map (Eqn.map g)) (T.map g) j =
      (getType e S T j).map (List.map (Eqn.map g)) := by
  classical
  unfold getType
  have packet : (fun d : Deriv =>
      S.map (Eqn.map g) ++ d.eqs.map (Eqn.map (g ∘ e)) ++
        [(d.ty.map (g ∘ e), T.map g)]) =
      (List.map (Eqn.map g)) ∘ (fun d : Deriv => S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)]) := by
    funext d
    simp only [Function.comp_apply, List.map_append, List.map_cons, List.map_nil,
      Eqn.map, Ty.map_map, eqn_map_map]
  rw [packet, ← Multiset.map_map, filter_map_store hg]

/-- Both branches of the soft-cut guard respect an injective renaming,
including metatype fallback when the intrinsic relation has no answers. -/
theorem guard_rename {U V : Type} {g : U → V} (hg : Function.Injective g)
    (e : DVar → U) (S : List (Eqn U)) (T : Ty U) (j : Info) (kind : String) :
    guard (g ∘ e) (S.map (Eqn.map g)) (T.map g) j kind =
      (guard e S T j kind).map (List.map (Eqn.map g)) := by
  classical
  unfold guard
  rw [getType_rename hg, Multiset.card_map]
  split_ifs
  · have packet : S.map (Eqn.map g) ++ [(Ty.sym kind, T.map g)] =
        (S ++ [(Ty.sym kind, T)]).map (Eqn.map g) := by simp [Eqn.map]
    rw [packet, ← Multiset.map_singleton, filter_map_store hg]
  · rfl

/-- A declaration renames only its own type variables. Derivation slots of
the value guards remain fixed, so their identities are never conflated. -/
def callRen (f : String → String) : CallVar → CallVar
  | .inl x => .inl (f x)
  | .inr d => .inr d

theorem callRen_injective {f : String → String} (hf : Function.Injective f) :
    Function.Injective (callRen f) := by
  intro x y h
  cases x <;> cases y <;> simp only [callRen, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl] at h ⊢
  · exact hf h
  · exact h

theorem callRen_atGuard (f : String → String) (k : Nat) :
    callRen f ∘ atGuard k = atGuard k := rfl

theorem row_to_call_map (f : String → String) (A : Ty String) :
    (A.map f).map (Sum.inl : String → CallVar) =
      (A.map Sum.inl).map (callRen f) := by
  rw [Ty.map_map, Ty.map_map]
  rfl

theorem demand_map (f : String → String) (A : Ty String) : demand (A.map f) = demand A := by
  cases A with
  | var _ => rfl
  | sym _ => rfl
  | app _ => simp [demand, Unchecked, Ty.map]

theorem resultGuarded_map (f : String → String) (R : Ty String) :
    ResultGuarded (R.map f) ↔ ResultGuarded R := by
  cases R <;> simp [ResultGuarded, Unchecked, Ty.map]

theorem guards_rename (Γ : Decls)
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String)
    {f : String → String} (hf : Function.Injective f) :
    ∀ (k : Nat) (As : List (Ty String))
      (vs : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) (S : List (Eqn CallVar)),
    guards Γ kind k (As.map (Ty.map f)) vs (S.map (Eqn.map (callRen f))) =
      (guards Γ kind k As vs S).map (List.map (Eqn.map (callRen f)))
  | _, [], [], _ => by simp [guards]
  | _, [], _ :: _, _ => by simp [guards]
  | _, _ :: _, [], _ => by simp [guards]
  | k, A :: As, v :: vs, S => by
      simp only [List.map_cons, guards, demand_map]
      split_ifs
      · have hg := guard_rename (callRen_injective hf) (atGuard k) S
          (A.map Sum.inl) (info Γ v) (kind v)
        rw [callRen_atGuard, ← row_to_call_map] at hg
        rw [hg, Multiset.bind_map, Multiset.map_bind]
        exact Multiset.bind_congr fun S' _ => guards_rename Γ kind hf (k + 1) As vs S'
      · exact guards_rename Γ kind hf (k + 1) As vs S

theorem resultGuard_rename (Γ : Decls)
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String)
    {f : String → String} (hf : Function.Injective f)
    (k : Nat) (R : Ty String) (S : List (Eqn CallVar))
    (r : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    resultGuard Γ kind k (R.map f) (S.map (Eqn.map (callRen f))) r =
      resultGuard Γ kind k R S r := by
  unfold resultGuard
  simp only [resultGuarded_map]
  split_ifs
  · have hg := guard_rename (callRen_injective hf) (atGuard k) S
      (R.map Sum.inl) (info Γ r) (kind r)
    rw [callRen_atGuard, ← row_to_call_map] at hg
    rw [hg, Multiset.map_map]
    rfl
  · rfl

/-- Renaming a whole declaration preserves its open-row call protocol.
In particular, a type variable shared by arguments and result stays shared. -/
theorem chainCall_rename (Γ : Decls)
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String)
    (body : List Mettapedia.Languages.MeTTa.OSLFCore.Atom →
      Multiset Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    {f : String → String} (hf : Function.Injective f) (row : Ty String)
    (vs : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    chainCall Γ kind body (row.map f) vs = chainCall Γ kind body row vs := by
  unfold chainCall
  rw [arrowSplit_map]
  cases h : arrowSplit row with
  | none => rfl
  | some pair =>
      rcases pair with ⟨As, R⟩
      simp only [Option.map_some]
      have hg := guards_rename Γ kind hf 0 As vs []
      simp only [List.map_nil] at hg
      rw [hg, Multiset.bind_map, List.length_map]
      exact Multiset.bind_congr fun S _ => Multiset.bind_congr fun r _ =>
        resultGuard_rename Γ kind hf As.length R S r

theorem chainCall_alphaEq (Γ : Decls)
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String)
    (body : List Mettapedia.Languages.MeTTa.OSLFCore.Atom →
      Multiset Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    {row row' : Ty String} (h : AlphaEq row row')
    (vs : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    chainCall Γ kind body row vs = chainCall Γ kind body row' vs := by
  obtain ⟨f, hf, rfl⟩ := rowRen_of_alphaEq h
  exact (chainCall_rename Γ kind body hf row vs).symm

theorem alphaEq_congr {a a' b b' : Ty String} (ha : AlphaEq a a') (hb : AlphaEq b b') :
    AlphaEq a b ↔ AlphaEq a' b' := by
  change a.canon = b.canon ↔ a'.canon = b'.canon
  rw [show a.canon = a'.canon from ha, show b.canon = b'.canon from hb]

theorem any_alphaEq {rows rows' : List (Ty String)}
    (h : List.Forall₂ AlphaEq rows rows') {r r' : Ty String} (hr : AlphaEq r r') :
    rows.any (fun t => decide (AlphaEq t r)) = rows'.any (fun t => decide (AlphaEq t r')) := by
  induction h with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
      simp only [List.any_cons, ih]
      simp only [alphaEq_congr hab hr]

theorem dedupAlpha_aux_rel {rows rows' : List (Ty String)}
    (h : List.Forall₂ AlphaEq rows rows') :
    ∀ {acc acc' : List (Ty String)}, List.Forall₂ AlphaEq acc acc' →
    List.Forall₂ AlphaEq
      (rows.foldl (fun acc r => if acc.any (fun t => decide (AlphaEq t r)) then acc else acc ++ [r]) acc)
      (rows'.foldl (fun acc r => if acc.any (fun t => decide (AlphaEq t r)) then acc else acc ++ [r]) acc') := by
  induction h with
  | nil => intro acc acc' ha; exact ha
  | @cons a b as bs hab _ ih =>
      intro acc acc' ha
      simp only [List.foldl_cons]
      rw [any_alphaEq ha hab]
      split_ifs
      · exact ih ha
      · exact ih (List.rel_append ha (.cons hab .nil))

/-- Alpha-deduplication chooses corresponding representatives when every
written declaration is replaced by an alpha-variant in the same position. -/
theorem dedupAlpha_rel {rows rows' : List (Ty String)}
    (h : List.Forall₂ AlphaEq rows rows') :
    List.Forall₂ AlphaEq (dedupAlpha rows) (dedupAlpha rows') :=
  dedupAlpha_aux_rel h .nil

theorem typedCall_alphaEq_rows (Γ : Decls)
    (kind : Mettapedia.Languages.MeTTa.OSLFCore.Atom → String)
    (body : List Mettapedia.Languages.MeTTa.OSLFCore.Atom →
      Multiset Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    {rows rows' : List (Ty String)} (h : List.Forall₂ AlphaEq rows rows')
    (vs : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    typedCall Γ kind body rows vs = typedCall Γ kind body rows' vs := by
  unfold typedCall
  have hd := dedupAlpha_rel h
  generalize dedupAlpha rows = rs at hd ⊢
  generalize dedupAlpha rows' = rs' at hd ⊢
  induction hd with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
      rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.cons_bind, Multiset.cons_bind,
        chainCall_alphaEq Γ kind body hab vs, ih]

/-- Declaration-index representative changes preserve closed type counts. -/
theorem count_idemAlpha_rows {Γ Γ' : Decls}
    (h : ∀ s, List.Forall₂ AlphaEq (Γ s) (Γ' s))
    (v : Mettapedia.Languages.MeTTa.OSLFCore.Atom) (T : Ty Empty) :
    count (info (Decls.idemAlpha Γ) v) T = count (info (Decls.idemAlpha Γ') v) T :=
  count_alpha_rows (fun s => dedupAlpha_rel (h s)) v T

namespace Controls

def sharedRow : Ty String := arrow [.var "a"] (.var "a")

def renamedRow : Ty String := arrow [.var "renamed"] (.var "renamed")

def independentRow : Ty String := arrow [.var "a"] (.var "b")

theorem shared_row_alpha : AlphaEq sharedRow renamedRow := by decide

theorem shared_row_renaming : RowRen sharedRow renamedRow :=
  rowRen_of_alphaEq shared_row_alpha

/-- Renaming may not merge two distinct type variables. -/
theorem independent_not_alpha : ¬ AlphaEq independentRow sharedRow := by decide

theorem independent_not_rowRen : ¬ RowRen independentRow sharedRow := by
  rintro ⟨f, hf, h⟩
  simp only [independentRow, sharedRow, arrow, List.cons_append, List.nil_append,
    Ty.map_app, List.map_cons, List.map_nil,
    Ty.map_sym, Ty.map_var, Ty.app.injEq, List.cons.injEq, Ty.var.injEq] at h
  have bad : ("a" : String) = "b" := hf (h.2.1.symm.trans h.2.2.1)
  exact (by decide : ("a" : String) ≠ "b") bad

open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls
  (decls probeKind num str numberRow identityRow)

/-- Two genuinely distinct declaration alternatives remain two answers after
changing the name of the polymorphic alternative's shared variable. -/
theorem renamed_distinct_rows_two_answers :
    typedCall decls probeKind (fun _ => {num 2}) [numberRow, renamedRow] [num 1] =
      {num 2, num 2} := by
  rw [typedCall_alphaEq_rows decls probeKind (fun _ => {num 2})
    (show List.Forall₂ AlphaEq [numberRow, renamedRow] [numberRow, identityRow] from
      .cons (AlphaEq.refl _) (.cons (by decide) .nil))]
  exact Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls.distinct_rows_two_answers

/-- Renaming the shared type variable does not turn a rejected range into a
successful call. -/
theorem renamed_shared_result_rejected :
    chainCall decls probeKind (fun _ => {str "a"}) renamedRow [num 1] = 0 := by
  rw [chainCall_alphaEq decls probeKind (fun _ => {str "a"})
    (show AlphaEq renamedRow identityRow from by decide)]
  exact Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls.shared_variable_checks_result

def independentStore : List (Eqn String) :=
  [(.var "x", .sym "Number"), (.var "y", .sym "String")]

theorem independent_store_satisfiable : Sat independentStore := by
  refine ⟨fun x => if x = "x" then .sym "Number" else .sym "String", ?_⟩
  intro e he
  simp only [independentStore, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> simp

/-- Non-injective renaming can turn compatible independent guards into a
contradiction, so injectivity in whole-store transport is essential. -/
theorem collapsing_store_is_unsatisfiable :
    ¬ Sat (independentStore.map (Eqn.map fun _ => "z")) := by
  rintro ⟨ρ, hρ⟩
  have hx := hρ (.var "z", .sym "Number") (by simp [independentStore, Eqn.map])
  have hy := hρ (.var "z", .sym "String") (by simp [independentStore, Eqn.map])
  simp only [Ty.bind_var', Ty.bind_sym] at hx hy
  have bad := hx.symm.trans hy
  exact (by decide : ("Number" : String) ≠ "String") (Ty.sym.inj bad)

end Controls

end RowAlpha

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
