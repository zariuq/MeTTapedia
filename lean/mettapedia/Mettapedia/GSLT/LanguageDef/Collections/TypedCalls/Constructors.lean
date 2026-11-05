import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRelation

/-!
# Constructor declarations: inversion, construction and tuple types

A constructor is a symbol with one arrow row `(-> B₁ … Bₖ R)` and no equations.
Under functional declarations the type relation of its applications is
decided field by field, which is what a trusted version reads.

* **The class** (`Constructor`): the result `R` is a *named* type, a symbol or
  a type constructor applied, such as `Nat` or `(List $a)` (`Named`); each
  field is *free*, a type variable that the result does not name and no other
  field names, or *fixed*, a type whose variables the result names. This is
  the condition of the C rule `contract_constructor_arrow`.
* **The count of an application** at a closed named type is one exactly when
  the declaration's equations with the request have a solution
  (`count_ctor`): the tuple type of an application of a constructor never
  meets a named type, since its head is the constructor's arrow
  (`tuple_ne_named`).
* **Inversion** (`ctor_inversion`): an application typed once at a closed
  named type `T` comes from the result matching `T`, and each checked field is
  typed once at its instance. A fixed field's instance is the same for every
  match (`fixed_instance_unique`): the requirement fixes it.
* **Construction** (`ctor_construction`): if every checked fixed field is typed
  once at its instance under some assignment `σ`, the application is typed once
  at `R σ`; free fields need nothing, since a type variable named once admits
  every value exactly once.
* **The guard is not the relation at the metatype.** The guard of a typed call
  succeeds at `Expression` for every expression, through `get-metatype`, while
  inversion and construction speak of the relation (`guard_inversion`, and the
  controls `Controls.metatype_guard_without_relation`).

Controls, with `List`, `Nil` and `Cons` declared as in the probes: a list of
numbers is typed at `(List Number)` (`Controls.numbers_typed`), a list holding
a string is not (`Controls.string_element_untyped`), and has a tuple type
instead; coupled fields `(-> $a $a Prop)` are outside the class, and `(Same 1
"x")` is not a `Prop` though each field has a type
(`Controls.coupled_fields_untyped`); a phantom result variable gives a value
every instance of its result (`Controls.phantom_every_instance`); repeated rows
of `Cons`, read without idempotence as SWI-PeTTa's `get-type` reads them,
count a one-cell list twice (`Controls.repeated_rows_twice`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Arrows and named types -/

/-- The arrow `(-> A₁ … Aₖ R)`. -/
def arrow {V : Type} (As : List (Ty V)) (R : Ty V) : Ty V := .app (.sym "->" :: (As ++ [R]))

@[simp] theorem arrowSplit_arrow {V : Type} (As : List (Ty V)) (R : Ty V) :
    arrowSplit (arrow As R) = some (As, R) := by
  simp [arrow, arrowSplit]

/-- A named type: a symbol, or a type constructor applied, whose head is a
symbol other than the arrow. -/
def Named {V : Type} : Ty V → Prop
  | .sym _ => True
  | .app (.sym s :: _ :: _) => s ≠ "->"
  | _ => False

theorem Named.bind {V W : Type} (f : V → Ty W) : ∀ {t : Ty V}, Named t → Named (t.bind f)
  | .sym _, _ => trivial
  | .app (.sym s :: _ :: _), h => by
      simp only [Ty.bind_app, List.map_cons, Ty.bind_sym]
      exact h
  | .var _, h => h.elim
  | .app [], h => h.elim
  | .app [.sym _], h => h.elim
  | .app (.var _ :: _), h => h.elim
  | .app (.app _ :: _), h => h.elim

/-- **A tuple type headed by an arrow never meets a named type.** -/
theorem tuple_ne_named {U : Type} (T : Ty Empty) (hT : Named T) (head : Ty U)
    (arrowHead : ∃ ts, head = .app (.sym "->" :: ts)) (rest : List (Ty U)) (ρ : U → Ty Empty) :
    (Ty.app (head :: rest)).bind ρ ≠ T := by
  obtain ⟨ts, rfl⟩ := arrowHead
  intro same
  rw [Ty.bind_app, List.map_cons, Ty.bind_app] at same
  match T, hT, same with
  | .app (.sym _ :: _ :: _), _, same =>
      simp only [Ty.app.injEq, List.cons.injEq] at same
      cases same.1

/-! ## The class of constructor declarations -/

/-- A free field: a type variable that the result does not name. -/
def FreeField (R : Ty String) : Ty String → Prop
  | .var x => x ∉ R.vars
  | _ => False

instance (R : Ty String) (A : Ty String) : Decidable (FreeField R A) := by
  cases A <;> unfold FreeField <;> infer_instance

/-- **The declarations the analysis inverts** (`contract_constructor_arrow`):
a named result; every field free or fixed by the result; free fields pairwise
distinct. -/
structure Constructor (As : List (Ty String)) (R : Ty String) : Prop where
  named : Named R
  fields : ∀ A ∈ As, FreeField R A ∨ ∀ y ∈ A.vars, y ∈ R.vars
  distinct : As.Pairwise fun A B => FreeField R A → FreeField R B → A ≠ B

/-- A fixed field's instance is the same under every match of the result:
the requirement fixes it. -/
theorem fixed_instance_unique {R A : Ty String} (fixed : ∀ y ∈ A.vars, y ∈ R.vars)
    {σ σ' : String → Ty Empty} (same : R.bind σ = R.bind σ') : A.bind σ = A.bind σ' := by
  have agree : ∀ y ∈ R.vars, σ y = σ' y := bind_agree R same
  exact Ty.bind_congr A fun y hy => agree y (fixed y hy)
where
  /-- Ground substitutions giving one image agree on the term's variables. -/
  bind_agree : ∀ (t : Ty String) {σ σ' : String → Ty Empty}, t.bind σ = t.bind σ' →
      ∀ y ∈ t.vars, σ y = σ' y
    | .var _, _, _, h, y, hy => by
        simp only [Ty.vars_var, List.mem_singleton] at hy
        subst hy
        exact h
    | .sym _, _, _, _, _, hy => absurd hy List.not_mem_nil
    | .app ts, σ, σ', h, y, hy => by
        rw [Ty.bind_app, Ty.bind_app, Ty.app.injEq, List.map_inj_left] at h
        rw [Ty.vars_app, List.mem_flatMap] at hy
        obtain ⟨t, ht, hy⟩ := hy
        exact bind_agree t (h t ht) y hy

/-! ## The equations of an application -/

/-- The equations of the checked fields of an application, from position `i`,
with one derivation per field. -/
def ctorEqs : ℕ → List (Ty String) → List Deriv → List (Eqn DVar)
  | i, A :: As, d :: ds =>
      if Unchecked A then ctorEqs (i + 1) As ds
      else ((A.map DVar.own, (d.push i).ty) :: (d.push i).eqs) ++ ctorEqs (i + 1) As ds
  | _, _, _ => []

theorem argEqs_singletons : ∀ (i : ℕ) (As : List (Ty String)) (js : List Info) (ds : List Deriv),
    As.length = js.length → List.Forall₂ (fun j d => eff j = {d}) js ds →
      argEqs i As js = {ctorEqs i As ds}
  | _, [], [], [], _, _ => rfl
  | i, A :: As, j :: js, d :: ds, len, .cons hj hjs => by
      have rest := argEqs_singletons (i + 1) As js ds (by simpa using len) hjs
      unfold argEqs ctorEqs
      split_ifs
      · exact rest
      · rw [hj, Multiset.singleton_bind, rest, Multiset.map_singleton]
  | _, [], _ :: _, _, len, _ => by simp at len
  | _, _ :: _, [], _, len, _ => by simp at len
  | _, [], [], _ :: _, _, h => by cases h
  | _, _ :: _, _ :: _, [], _, h => by cases h

/-- The variables of the equations: own variables of the fields, and variables of
the fields' derivations, whose paths start at a position from `i` on. -/
theorem ctorEqs_vars : ∀ (i : ℕ) (As : List (Ty String)) (ds : List Deriv),
    ∀ w ∈ eqnVars (ctorEqs i As ds),
      (∃ A ∈ As, ∃ y ∈ A.vars, w = DVar.own y) ∨ ∃ k, i ≤ k ∧ w.1.head? = some k
  | i, A :: As, d :: ds, w, hw => by
      have rest := ctorEqs_vars (i + 1) As ds
      unfold ctorEqs at hw
      split_ifs at hw
      · rcases rest w hw with ⟨B, hB, y, hy, rfl⟩ | ⟨k, hk, hw'⟩
        · exact .inl ⟨B, List.mem_cons_of_mem _ hB, y, hy, rfl⟩
        · exact .inr ⟨k, by omega, hw'⟩
      · rw [List.cons_append, eqnVars_cons, eqnVars_append, List.mem_append, List.mem_append,
          Eqn.vars, List.mem_append] at hw
        rcases hw with (hw | hw) | hw | hw
        · rw [Ty.vars_map, List.mem_map] at hw
          obtain ⟨y, hy, rfl⟩ := hw
          exact .inl ⟨A, by simp, y, hy, rfl⟩
        · change w ∈ (d.ty.map (DVar.push i)).vars at hw
          rw [Ty.vars_map, List.mem_map] at hw
          obtain ⟨u, -, rfl⟩ := hw
          exact .inr ⟨i, le_rfl, rfl⟩
        · exact .inr ⟨i, le_rfl, eqnVars_push i d.eqs w hw⟩
        · rcases rest w hw with ⟨B, hB, y, hy, rfl⟩ | ⟨k, hk, hw'⟩
          · exact .inl ⟨B, List.mem_cons_of_mem _ hB, y, hy, rfl⟩
          · exact .inr ⟨k, by omega, hw'⟩
  | _, [], _, w, hw => by simp [ctorEqs, eqnVars] at hw
  | _, _ :: _, [], w, hw => by simp [ctorEqs, eqnVars] at hw

/-- From a solution of the equations, each checked field's derivation meets the
field's instance. -/
theorem ctorEqs_solves_fields (ρ : DVar → Ty Empty) :
    ∀ (i : ℕ) (As : List (Ty String)) (ds : List Deriv), Solves ρ (ctorEqs i As ds) →
      ∀ p ∈ List.zip As ds, ¬ Unchecked p.1 →
        Sat (p.2.eqs ++ [(p.2.ty, (p.1.bind (ρ ∘ DVar.own)).lift)])
  | i, A :: As, d :: ds, h, p, hp => by
      unfold ctorEqs at h
      rw [List.zip_cons_cons, List.mem_cons] at hp
      split_ifs at h with hA
      · rcases hp with rfl | hp
        · exact fun hn => (hn hA).elim
        · exact ctorEqs_solves_fields ρ (i + 1) As ds h p hp
      · rw [List.cons_append, solves_cons, solves_append] at h
        obtain ⟨head, own, rest⟩ := h
        rcases hp with rfl | hp
        · intro _
          refine ⟨ρ ∘ DVar.push i, (solves_append _ _ _).mpr ⟨(solves_map ρ _ _).mp own, ?_⟩⟩
          rw [solves_singleton, Ty.lift_bind_ground]
          change (A.map DVar.own).bind ρ = (d.ty.map (DVar.push i)).bind ρ at head
          rw [Ty.bind_map, Ty.bind_map] at head
          exact head.symm
        · exact ctorEqs_solves_fields ρ (i + 1) As ds rest p hp
  | _, [], _, _, p, hp => by simp at hp
  | _, _ :: _, [], _, p, hp => by simp at hp

/-- **The equations of a constructor application have a solution** when every
checked field's derivation is satisfiable, and every checked fixed field's
derivation meets the field's instance under `σ`; the solution is `σ` on the
result's variables. Free fields are solved by their derivation's own type. -/
theorem ctorEqs_sat (R : Ty String) (σ : String → Ty Empty) :
    ∀ (i : ℕ) (As : List (Ty String)) (ds : List Deriv),
      (∀ A ∈ As, FreeField R A ∨ ∀ y ∈ A.vars, y ∈ R.vars) →
      As.Pairwise (fun A B => FreeField R A → FreeField R B → A ≠ B) →
      (∀ p ∈ List.zip As ds, ¬ Unchecked p.1 → Sat p.2.eqs) →
      (∀ p ∈ List.zip As ds, ¬ Unchecked p.1 → ¬ FreeField R p.1 →
        Sat (p.2.eqs ++ [(p.2.ty, (p.1.bind σ).lift)])) →
      ∃ ρ : DVar → Ty Empty, Solves ρ (ctorEqs i As ds) ∧ ∀ x ∈ R.vars, ρ (DVar.own x) = σ x
  | i, A :: As, d :: ds, fields, distinct, sat, fixed => by
      obtain ⟨ρ', hρ', agree'⟩ := ctorEqs_sat R σ (i + 1) As ds
        (fun B hB => fields B (List.mem_cons_of_mem _ hB)) (List.pairwise_cons.mp distinct).2
        (fun p hp => sat p (by simp [hp])) (fun p hp => fixed p (by simp [hp]))
      by_cases hA : Unchecked A
      · refine ⟨ρ', ?_, agree'⟩
        unfold ctorEqs
        rw [if_pos hA]
        exact hρ'
      have restVars := ctorEqs_vars (i + 1) As ds
      -- the variables of the remaining equations do not start at position `i`
      have notHere : ∀ w ∈ eqnVars (ctorEqs (i + 1) As ds), w.1.head? ≠ some i := by
        intro w hw
        rcases restVars w hw with ⟨B, -, y, -, rfl⟩ | ⟨k, hk, hw'⟩
        · simp [DVar.own]
        · rw [hw']
          intro h
          cases h
          omega
      have pushSame : ∀ (ρd : DVar → Ty Empty) (other : DVar → Ty Empty),
          (fun w : DVar => if w.1.head? = some i then ρd (w.1.tail, w.2) else other w) ∘
            DVar.push i = ρd := by
        intro ρd other
        funext w
        simp [DVar.push]
      unfold ctorEqs
      rw [if_neg hA]
      rcases fields A (by simp) with free | fixedA
      · -- a free field `$x`: its variable is solved by the derivation's type
        obtain ⟨x, rfl⟩ : ∃ x, A = .var x := by
          cases A with
          | var x => exact ⟨x, rfl⟩
          | sym _ => exact free.elim
          | app _ => exact free.elim
        obtain ⟨ρd, hρd⟩ := sat (.var x, d) (by simp) hA
        let ρ : DVar → Ty Empty := fun w =>
          if w.1.head? = some i then ρd (w.1.tail, w.2)
          else if w = DVar.own x then d.ty.bind ρd else ρ' w
        have xFresh : ∀ w ∈ eqnVars (ctorEqs (i + 1) As ds), w ≠ DVar.own x := by
          intro w hw same
          subst same
          rcases restVars _ hw with ⟨B, hB, y, hy, hxy⟩ | ⟨k, -, hk⟩
          · have hxy' : x = y := by simpa [DVar.own] using hxy
            subst hxy'
            rcases fields B (List.mem_cons_of_mem _ hB) with freeB | fixedB
            · obtain ⟨z, rfl⟩ : ∃ z, B = .var z := by
                cases B with
                | var z => exact ⟨z, rfl⟩
                | sym _ => exact freeB.elim
                | app _ => exact freeB.elim
              simp only [Ty.vars_var, List.mem_singleton] at hy
              subst hy
              exact (List.pairwise_cons.mp distinct).1 _ hB free freeB rfl
            · exact free (fixedB x hy)
          · simp [DVar.own] at hk
        refine ⟨ρ, ?_, ?_⟩
        · rw [List.cons_append, solves_cons, solves_append]
          refine ⟨?_, ?_, ?_⟩
          · change ((Ty.var x).map DVar.own).bind ρ = (d.ty.map (DVar.push i)).bind ρ
            rw [Ty.bind_map, Ty.bind_map]
            have : ρ ∘ DVar.push i = ρd := pushSame ρd _
            rw [this]
            simp [ρ, DVar.own]
          · change Solves ρ (d.eqs.map (Eqn.map (DVar.push i)))
            rw [solves_map]
            have : ρ ∘ DVar.push i = ρd := pushSame ρd _
            rw [this]
            exact hρd
          · refine (solves_congr fun w hw => ?_).mpr hρ'
            simp only [ρ, if_neg (notHere w hw), if_neg (xFresh w hw)]
        · intro y hy
          have hne : DVar.own y ≠ DVar.own x := by
            intro h
            have : y = x := DVar.own_injective h
            subst this
            exact free hy
          have head : (DVar.own y).1.head? ≠ some i := by simp [DVar.own]
          show (if (DVar.own y).1.head? = some i then ρd ((DVar.own y).1.tail, (DVar.own y).2)
            else if DVar.own y = DVar.own x then d.ty.bind ρd else ρ' (DVar.own y)) = σ y
          rw [if_neg head, if_neg hne]
          exact agree' y hy
      · -- a fixed field: its instance is the request of its derivation
        obtain ⟨ρd, hρd⟩ := fixed (A, d) (by simp) hA (fun free => by
          cases A with
          | var x =>
              exact free (fixedA x (by simp))
          | sym _ => exact free
          | app _ => exact free)
        let ρ : DVar → Ty Empty := fun w =>
          if w.1.head? = some i then ρd (w.1.tail, w.2) else ρ' w
        have own : ∀ y ∈ A.vars, ρ (DVar.own y) = σ y := by
          intro y hy
          simp only [ρ, DVar.own, List.head?_nil, reduceCtorEq, if_false]
          exact agree' y (fixedA y hy)
        rw [solves_append, solves_singleton] at hρd
        refine ⟨ρ, ?_, ?_⟩
        · rw [List.cons_append, solves_cons, solves_append]
          refine ⟨?_, ?_, ?_⟩
          · change (A.map DVar.own).bind ρ = (d.ty.map (DVar.push i)).bind ρ
            rw [Ty.bind_map, Ty.bind_map, pushSame ρd ρ', hρd.2, Ty.lift_bind_ground]
            exact Ty.bind_congr A fun y hy => own y hy
          · change Solves ρ (d.eqs.map (Eqn.map (DVar.push i)))
            rw [solves_map, pushSame ρd ρ']
            exact hρd.1
          · refine (solves_congr fun w hw => ?_).mpr hρ'
            simp only [ρ, if_neg (notHere w hw)]
        · intro y hy
          simp only [ρ, DVar.own, List.head?_nil, reduceCtorEq, if_false]
          exact agree' y hy
  | _, [], _, _, _, _, _ =>
      ⟨fun w => match w with
        | ([], some x) => σ x
        | _ => default, by simp [ctorEqs], fun _ _ => rfl⟩
  | _, _ :: _, [], _, _, _, _ =>
      ⟨fun w => match w with
        | ([], some x) => σ x
        | _ => default, by simp [ctorEqs], fun _ _ => rfl⟩

/-! ## Applications of a constructor -/

section Applications

variable {Γ : Decls}

/-- The one effective derivation of a value under functional declarations. -/
noncomputable def theDeriv (hΓ : Functional Γ) (v : Atom) : Deriv :=
  (Multiset.card_eq_one.mp (card_eff hΓ v)).choose

theorem eff_theDeriv (hΓ : Functional Γ) (v : Atom) : eff (info Γ v) = {theDeriv hΓ v} :=
  (Multiset.card_eq_one.mp (card_eff hΓ v)).choose_spec

theorem theDeriv_sat (hΓ : Functional Γ) (v : Atom) : Sat (theDeriv hΓ v).eqs :=
  eff_sat (cands_sat Γ v) _ (by rw [eff_theDeriv hΓ v]; exact Multiset.mem_singleton_self _)

open Classical in
theorem count_eq_ite (hΓ : Functional Γ) (v : Atom) (T : Ty Empty) :
    count (info Γ v) T =
      if Sat ((theDeriv hΓ v).eqs ++ [((theDeriv hΓ v).ty, T.lift)]) then 1 else 0 := by
  unfold count
  rw [eff_theDeriv hΓ v, Multiset.filter_singleton]
  split_ifs <;> rfl

theorem forall₂_theDeriv (hΓ : Functional Γ) :
    ∀ vs : List Atom, List.Forall₂ (fun j d => eff j = {d}) (vs.map (info Γ)) (vs.map (theDeriv hΓ))
  | [] => .nil
  | v :: vs => .cons (eff_theDeriv hΓ v) (forall₂_theDeriv hΓ vs)

open Classical in
/-- **The count of a constructor application at a closed named type**: one
exactly when the declaration's equations, with the request, have a solution. -/
theorem count_ctor (hΓ : Functional Γ) {C : String} {As : List (Ty String)} {R : Ty String}
    (row : Γ C = [arrow As R]) (vs : List Atom) (len : vs.length = As.length)
    (T : Ty Empty) (hT : Named T) :
    count (info Γ (.expression (.symbol C :: vs))) T =
      if Sat (ctorEqs 1 As (vs.map (theDeriv hΓ)) ++ [(R.map DVar.own, T.lift)]) then 1 else 0 := by
  set E := ctorEqs 1 As (vs.map (theDeriv hΓ)) with hEdef
  have args : argEqs 1 As (vs.map (info Γ)) = {E} :=
    argEqs_singletons 1 As _ _ (by simp [len]) (forall₂_theDeriv hΓ vs)
  have funT : funTrees (info Γ (.symbol C)) (vs.map (info Γ)) =
      (({(⟨R.map DVar.own, E⟩ : Deriv)} : Multiset Deriv)).filter fun d => Sat d.eqs := by
    unfold funTrees
    rw [info_symbol, row]
    simp only [Multiset.coe_singleton, Multiset.singleton_bind, arrowSplit_arrow, List.length_map,
      len, if_true, args, Multiset.map_singleton]
  rw [info_expression, List.map_cons]
  by_cases hE : Sat E
  · have one : funTrees (info Γ (.symbol C)) (vs.map (info Γ)) = {⟨R.map DVar.own, E⟩} := by
      rw [funT, Multiset.filter_singleton, if_pos hE]
    simp only [nodeInfo, one, Multiset.card_singleton, one_ne_zero, if_false]
    unfold count eff
    simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.filter_singleton]
    split_ifs <;> rfl
  · have zero : funTrees (info Γ (.symbol C)) (vs.map (info Γ)) = 0 := by
      rw [funT, Multiset.filter_singleton, if_neg hE]
      rfl
    simp only [nodeInfo, zero, Multiset.card_zero, if_true]
    rw [if_neg fun h => hE h.left]
    unfold count
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro d hd hsat
    have hcard : Multiset.card (tupleTrees (info Γ (.symbol C) :: vs.map (info Γ))) ≠ 0 := by
      rw [tupleTrees, Multiset.card_map, card_tupleParts 0 _ (fun j hj => by
        rw [List.mem_cons] at hj
        rcases hj with rfl | hj
        · exact card_eff hΓ _
        · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hj
          exact card_eff hΓ v)]
      exact one_ne_zero
    unfold eff at hd
    rw [if_neg hcard] at hd
    simp only [tupleTrees, Multiset.mem_map] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    simp only [tupleParts, Multiset.mem_bind, Multiset.mem_map] at hp
    obtain ⟨d0, hd0, p', -, rfl⟩ := hp
    have hd0' : d0 = ⟨(arrow As R).map DVar.own, []⟩ := by
      unfold eff at hd0
      rw [info_symbol, row] at hd0
      simpa using hd0
    subst hd0'
    obtain ⟨ρ, hρ⟩ := hsat
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hρ
    refine tuple_ne_named T hT _ ?_ _ ρ hρ.2
    simp only [Deriv.push, arrow, Ty.map_app, List.map_cons, Ty.map_sym]
    exact ⟨_, rfl⟩

/-- **Inversion**: an application of a constructor typed once at a closed named
type comes from a match of the declared result, and each checked field is
typed once at its instance under that match. -/
theorem ctor_inversion (hΓ : Functional Γ) {C : String} {As : List (Ty String)} {R : Ty String}
    (row : Γ C = [arrow As R]) (vs : List Atom) (len : vs.length = As.length)
    (T : Ty Empty) (hT : Named T)
    (typed : count (info Γ (.expression (.symbol C :: vs))) T = 1) :
    ∃ σ : String → Ty Empty, R.bind σ = T ∧
      ∀ p ∈ List.zip As vs, ¬ Unchecked p.1 → count (info Γ p.2) (p.1.bind σ) = 1 := by
  classical
  rw [count_ctor hΓ row vs len T hT] at typed
  split_ifs at typed with h
  obtain ⟨ρ, hρ⟩ := h
  rw [solves_append, solves_singleton] at hρ
  refine ⟨ρ ∘ DVar.own, ?_, ?_⟩
  · have := hρ.2
    rw [Ty.bind_map, Ty.lift_bind_ground] at this
    exact this
  · intro p hp hc
    have mem : (p.1, theDeriv hΓ p.2) ∈ List.zip As (vs.map (theDeriv hΓ)) := by
      rw [List.zip_map_right, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have := ctorEqs_solves_fields ρ 1 As _ hρ.1 _ mem hc
    rw [count_eq_ite hΓ, if_pos this]

/-- **Construction**: if every checked fixed field is typed once at its instance
under `σ`, the application is typed once at the result's instance. -/
theorem ctor_construction (hΓ : Functional Γ) {C : String} {As : List (Ty String)}
    {R : Ty String} (row : Γ C = [arrow As R]) (hC : Constructor As R) (vs : List Atom)
    (len : vs.length = As.length) (σ : String → Ty Empty)
    (fields : ∀ p ∈ List.zip As vs, ¬ Unchecked p.1 → ¬ FreeField R p.1 →
      count (info Γ p.2) (p.1.bind σ) = 1) :
    count (info Γ (.expression (.symbol C :: vs))) (R.bind σ) = 1 := by
  classical
  rw [count_ctor hΓ row vs len _ (hC.named.bind σ), if_pos]
  have zipMem : ∀ p ∈ List.zip As (vs.map (theDeriv hΓ)),
      ∃ v, p.2 = theDeriv hΓ v ∧ (p.1, v) ∈ List.zip As vs := by
    intro p hp
    rw [List.zip_map_right, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q.2, rfl, hq⟩
  obtain ⟨ρ, hρ, agree⟩ := ctorEqs_sat R σ 1 As (vs.map (theDeriv hΓ)) hC.fields hC.distinct
    (fun p hp _ => by
      obtain ⟨v, hv, -⟩ := zipMem p hp
      rw [hv]
      exact theDeriv_sat hΓ v)
    (fun p hp hc hf => by
      obtain ⟨v, hv, hmem⟩ := zipMem p hp
      have := fields (p.1, v) hmem hc hf
      rw [count_eq_ite hΓ] at this
      split_ifs at this with h
      rw [hv]
      exact h)
  refine ⟨ρ, (solves_append _ _ _).mpr ⟨hρ, (solves_singleton _ _).mpr ?_⟩⟩
  rw [Ty.bind_map, Ty.lift_bind_ground]
  exact Ty.bind_congr R fun y hy => agree y hy

end Applications

/-! ## The guard and the relation -/

/-- **Inversion through the guard**: at a closed named formal that is not the
value's metatype, a guard that succeeds once is the relation typing the value
once, so inversion applies. At the metatype it is not: see
`Controls.metatype_guard_without_relation`. -/
theorem guard_inversion {Γ : Decls} (hΓ : Functional Γ) {C : String} {As : List (Ty String)}
    {R : Ty String} (row : Γ C = [arrow As R]) (vs : List Atom) (len : vs.length = As.length)
    (T : Ty Empty) (hT : Named T) (notMeta : T ≠ .sym "Expression")
    (accepted : guardCount (info Γ (.expression (.symbol C :: vs))) T "Expression" = 1) :
    ∃ σ : String → Ty Empty, R.bind σ = T ∧
      ∀ p ∈ List.zip As vs, ¬ Unchecked p.1 → count (info Γ p.2) (p.1.bind σ) = 1 := by
  rw [guardCount_of_ne _ _ _ notMeta] at accepted
  exact ctor_inversion hΓ row vs len T hT accepted

/-! ## Rows of the head -/

open Classical in
/-- The derivations through a head's rows add over the rows. -/
theorem funTrees_rows_append (r₁ r₂ : List (Ty String)) (c c' : Multiset Deriv)
    (args : List Info) :
    funTrees ⟨r₁ ++ r₂, c⟩ args = funTrees ⟨r₁, c⟩ args + funTrees ⟨r₂, c'⟩ args := by
  unfold funTrees
  rw [← Multiset.coe_add, Multiset.add_bind]

open Classical in
/-- The derivations through one arrow row. -/
theorem funTrees_arrow (As : List (Ty String)) (R : Ty String) (c : Multiset Deriv)
    (args : List Info) (len : As.length = args.length) :
    funTrees ⟨[arrow As R], c⟩ args =
      ((argEqs 1 As args).map fun E => (⟨R.map DVar.own, E⟩ : Deriv)).filter fun d => Sat d.eqs := by
  unfold funTrees
  simp only [Multiset.coe_singleton, Multiset.singleton_bind, arrowSplit_arrow, len, if_true]

/-! ## Controls -/

namespace Controls

/-- `(List $a)`. -/
def listOf {V : Type} (a : Ty V) : Ty V := .app [.sym "List", a]

/-- The probe declarations: `(: Nil (List $a))`, `(: Cons (-> $a (List $a) (List $a)))`,
`(: Same (-> $a $a Prop))`, `(: MkPh (-> Number (Ph $a)))`, `(: C (-> Number Expression))`
and `(: Box (-> $a (Wrap $a)))`. -/
def decls : Decls := fun s =>
  if s = "Nil" then [listOf (.var "a")]
  else if s = "Cons" then [arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))]
  else if s = "Same" then [arrow [.var "a", .var "a"] (.sym "Prop")]
  else if s = "MkPh" then [arrow [.sym "Number"] (.app [.sym "Ph", .var "a"])]
  else if s = "C" then [arrow [.sym "Number"] (.sym "Expression")]
  else if s = "Box" then [arrow [.var "a"] (.app [.sym "Wrap", .var "a"])]
  else []

theorem decls_functional : Functional decls := by
  intro s
  unfold decls
  split_ifs <;> simp

abbrev sym (s : String) : Atom := .symbol s
abbrev num (n : ℤ) : Atom := .grounded (.int n)
abbrev str (s : String) : Atom := .grounded (.string s)
abbrev app (f : String) (args : List Atom) : Atom := .expression (sym f :: args)

/-- `(List Number)`, a closed request. -/
abbrev listNumber : Ty Empty := listOf (.sym "Number")

theorem cons_constructor : Constructor [.var "a", listOf (.var "a")] (listOf (.var "a")) where
  named := by simp [Named, listOf]
  fields := by
    intro A hA
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl <;> simp [listOf]
  distinct := by
    simp [FreeField, listOf]

theorem sat_class_iff (c : String) (T : Ty Empty) :
    Sat ((classDeriv c).eqs ++ [((classDeriv c).ty, T.lift)]) ↔ T = .sym c := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [solves_append, solves_singleton] at hσ
    have := hσ.2
    rw [Ty.lift_bind_ground] at this
    exact this.symm
  · rintro rfl
    exact ⟨fun _ => default, (solves_append _ _ _).mpr ⟨by simp [classDeriv],
      (solves_singleton _ _).mpr rfl⟩⟩

theorem theDeriv_int (n : ℤ) : theDeriv decls_functional (num n) = classDeriv "Number" := by
  have h := eff_theDeriv decls_functional (num n)
  rw [info_int] at h
  unfold eff at h
  simpa using h.symm

theorem count_num_number (n : ℤ) : count (info decls (num n)) (.sym "Number") = 1 := by
  classical
  rw [count_eq_ite decls_functional, theDeriv_int, if_pos ((sat_class_iff "Number" _).mpr rfl)]

theorem theDeriv_str (s : String) : theDeriv decls_functional (str s) = classDeriv "String" := by
  have h := eff_theDeriv decls_functional (str s)
  rw [info_string] at h
  unfold eff at h
  simpa using h.symm

theorem count_str (s : String) (T : Ty Empty) :
    count (info decls (str s)) T = if T = .sym "String" then 1 else 0 := by
  classical
  rw [count_eq_ite decls_functional, theDeriv_str]
  by_cases h : T = .sym "String"
  · rw [if_pos ((sat_class_iff "String" T).mpr h), if_pos h]
  · rw [if_neg (fun hs => h ((sat_class_iff "String" T).mp hs)), if_neg h]

theorem count_nil (τ : Ty Empty) : count (info decls (sym "Nil")) (listOf τ) = 1 := by
  classical
  rw [count_eq_ite decls_functional, if_pos]
  have : theDeriv decls_functional (sym "Nil") = ⟨(listOf (.var "a")).map DVar.own, []⟩ := by
    have h := eff_theDeriv decls_functional (sym "Nil")
    rw [info_symbol] at h
    unfold eff at h
    simpa [decls] using h.symm
  rw [this]
  refine ⟨fun _ => τ, (solves_append _ _ _).mpr ⟨by simp, ?_⟩⟩
  rw [solves_singleton, Ty.lift_bind_ground]
  simp [listOf, Ty.map]

/-- **A list of numbers is typed at `(List Number)`**, once. -/
theorem numbers_typed :
    count (info decls (app "Cons" [num 1, app "Cons" [num 2, sym "Nil"]])) listNumber = 1 := by
  have row : decls "Cons" = [arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))] := by
    simp [decls]
  have build : ∀ (rest : Atom) (n : ℤ), count (info decls rest) listNumber = 1 →
      count (info decls (app "Cons" [num n, rest])) listNumber = 1 := by
    intro rest n hrest
    have := ctor_construction decls_functional row cons_constructor [num n, rest] rfl
      (fun _ => .sym "Number") (by
        intro p hp _ _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl
        · exact count_num_number n
        · simpa [listOf] using hrest)
    simpa [listOf] using this
  exact build _ 1 (build _ 2 (count_nil (.sym "Number")))

/-- **A list holding a string is not typed at `(List Number)`**: inversion would
type the string at `Number`. -/
theorem string_element_untyped :
    count (info decls (app "Cons" [num 1, app "Cons" [str "two", sym "Nil"]])) listNumber = 0 := by
  have row : decls "Cons" = [arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))] := by
    simp [decls]
  have le := count_le_one decls_functional (app "Cons" [num 1, app "Cons" [str "two", sym "Nil"]])
    listNumber
  by_contra ne
  have one : count (info decls (app "Cons" [num 1, app "Cons" [str "two", sym "Nil"]]))
      listNumber = 1 := by omega
  obtain ⟨σ, hσ, fields⟩ := ctor_inversion decls_functional row _ rfl listNumber
    (by simp [Named, listOf]) one
  have hσa : σ "a" = .sym "Number" := by
    simpa [listOf, listNumber] using hσ
  have inner := fields (listOf (.var "a"), app "Cons" [str "two", sym "Nil"]) (by simp)
    (by simp [Unchecked, listOf])
  rw [show (listOf (.var "a") : Ty String).bind σ = listNumber by simp [listOf, hσa]] at inner
  obtain ⟨σ', hσ', fields'⟩ := ctor_inversion decls_functional row _ rfl listNumber
    (by simp [Named, listOf]) inner
  have hσa' : σ' "a" = .sym "Number" := by
    simpa [listOf, listNumber] using hσ'
  have elem := fields' (.var "a", str "two") (by simp) (by simp [Unchecked])
  rw [Ty.bind_var', hσa', count_str] at elem
  simp at elem

/-- The inner cell is a list of strings: it is typed at `(List String)`. -/
theorem string_cell_typed :
    count (info decls (app "Cons" [str "two", sym "Nil"])) (listOf (.sym "String")) = 1 := by
  have row : decls "Cons" = [arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))] := by
    simp [decls]
  have := ctor_construction decls_functional row cons_constructor [str "two", sym "Nil"] rfl
    (fun _ => .sym "String") (by
      intro p hp _ _
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · simp [count_str]
      · simpa [listOf] using count_nil (.sym "String"))
  simpa [listOf] using this

/-- **Coupled fields are outside the class.** `(-> $a $a Prop)` names `$a` in two
fields and not in its result. -/
theorem same_not_constructor : ¬ Constructor [.var "a", .var "a"] (.sym "Prop") := by
  intro h
  have := h.distinct
  simp [FreeField] at this

/-- **`(Same 1 "x")` is not a `Prop`, though each field has a type**: its fields
are typed `Number` and `String`, and the coupling makes them disagree. `(Same 1
2)` is a `Prop`. -/
theorem coupled_fields_untyped :
    count (info decls (app "Same" [num 1, str "x"])) (.sym "Prop") = 0 ∧
      count (info decls (num 1)) (.sym "Number") = 1 ∧
      count (info decls (str "x")) (.sym "String") = 1 ∧
      count (info decls (app "Same" [num 1, num 2])) (.sym "Prop") = 1 := by
  classical
  have row : decls "Same" = [arrow [.var "a", .var "a"] (.sym "Prop")] := by simp [decls]
  refine ⟨?_, count_num_number 1, by simp [count_str], ?_⟩
  · rw [count_ctor decls_functional row _ rfl _ (by simp [Named]), if_neg]
    rintro ⟨ρ, hρ⟩
    simp only [List.map_cons, List.map_nil, theDeriv_int, theDeriv_str, ctorEqs, Unchecked,
      classDeriv, Deriv.push] at hρ
    have h1 := hρ ((Ty.var "a").map DVar.own, (Ty.sym "Number" : Ty DVar).map (DVar.push 1))
      (by simp)
    have h2 := hρ ((Ty.var "a").map DVar.own, (Ty.sym "String" : Ty DVar).map (DVar.push 2))
      (by simp)
    simp only [Ty.map_var, Ty.map_sym, Ty.bind_var', Ty.bind_sym] at h1 h2
    rw [h1] at h2
    simp at h2
  · rw [count_ctor decls_functional row _ rfl _ (by simp [Named]), if_pos]
    refine ⟨fun _ => .sym "Number", ?_⟩
    simp only [List.map_cons, List.map_nil, theDeriv_int, ctorEqs, Unchecked, classDeriv,
      Deriv.push]
    intro e he
    simp at he
    rcases he with rfl | rfl | rfl <;> rfl

/-- **A phantom result variable gives a value every instance of its result**:
`(MkPh 1)` is typed once at `(Ph Number)` and once at `(Ph String)`, so it has no
single closed type to record. -/
theorem phantom_every_instance (τ : Ty Empty) :
    count (info decls (app "MkPh" [num 1])) (.app [.sym "Ph", τ]) = 1 := by
  have row : decls "MkPh" = [arrow [.sym "Number"] (.app [.sym "Ph", .var "a"])] := by
    simp [decls]
  have hC : Constructor [.sym "Number"] (.app [.sym "Ph", .var "a"]) :=
    ⟨by simp [Named], by simp, by simp⟩
  have := ctor_construction decls_functional row hC [num 1] rfl (fun _ => τ) (by
    intro p hp _ _
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact count_num_number 1)
  simpa using this

/-- **Finding: the guard at the metatype is not the relation.** With
`(: C (-> Number Expression))`, the guard of `(C "x")` at `Expression` succeeds
once, through `get-metatype`, while the relation has no answer and the field
`"x"` is not a `Number`: inverting the declaration from the guard would type
`"x"` at `Number`. -/
theorem metatype_guard_without_relation :
    guardCount (info decls (app "C" [str "x"])) (.sym "Expression") "Expression" = 1 ∧
      count (info decls (app "C" [str "x"])) (.sym "Expression") = 0 ∧
      count (info decls (str "x")) (.sym "Number") = 0 := by
  classical
  have row : decls "C" = [arrow [.sym "Number"] (.sym "Expression")] := by simp [decls]
  refine ⟨guardCount_metatype decls_functional _ _, ?_, by simp [count_str]⟩
  rw [count_ctor decls_functional row _ rfl _ (by simp [Named]), if_neg]
  rintro ⟨ρ, hρ⟩
  simp only [List.map_cons, List.map_nil, theDeriv_str, ctorEqs, Unchecked, classDeriv,
    Deriv.push] at hρ
  have h1 := hρ ((Ty.sym "Number" : Ty String).map DVar.own,
    (Ty.sym "String" : Ty DVar).map (DVar.push 1)) (by simp)
  simp at h1

/-- **Finding: a value accepted at the metatype is not typed there.** The
expression `(foo bar)`, of undeclared symbols, passes the guard at `Expression`
through `get-metatype`, but the relation does not type it at `Expression`, so
`(Box (foo bar))` is not typed at `(Wrap Expression)` although `Box`'s
declaration would construct that type from the guard's verdict. -/
theorem metatype_acceptance_not_typed :
    guardCount (info decls (app "foo" [sym "bar"])) (.sym "Expression") "Expression" = 1 ∧
      count (info decls (app "foo" [sym "bar"])) (.sym "Expression") = 0 ∧
      count (info decls (app "Box" [app "foo" [sym "bar"]])) (.app [.sym "Wrap", .sym "Expression"])
        = 0 := by
  classical
  have untyped : count (info decls (app "foo" [sym "bar"])) (.sym "Expression") = 0 := by
    unfold count
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro d hd hsat
    -- every derivation of `(foo bar)` is its tuple type, an application
    have tuple : ∃ ts, d.ty = .app ts := by
      rw [info_expression] at hd
      simp only [List.map_cons, List.map_nil, nodeInfo] at hd
      have noFun : funTrees (info decls (sym "foo")) [info decls (sym "bar")] = 0 := by
        unfold funTrees
        rw [info_symbol]
        simp [decls]
      rw [noFun] at hd
      simp only [Multiset.card_zero, if_true] at hd
      unfold eff at hd
      split_ifs at hd with h0
      · rw [tupleTrees, Multiset.card_map] at h0
        rw [card_tupleParts 0 _ (by
          intro j hj
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl <;> exact card_eff decls_functional _)] at h0
        cases h0
      · simp only [tupleTrees, Multiset.mem_map] at hd
        obtain ⟨p, -, rfl⟩ := hd
        exact ⟨_, rfl⟩
    obtain ⟨ts, hts⟩ := tuple
    obtain ⟨ρ, hρ⟩ := hsat
    rw [solves_append, solves_singleton, hts] at hρ
    have := hρ.2
    rw [Ty.bind_app, Ty.lift_bind_ground] at this
    cases this
  refine ⟨guardCount_metatype decls_functional _ _, untyped, ?_⟩
  have row : decls "Box" = [arrow [.var "a"] (.app [.sym "Wrap", .var "a"])] := by simp [decls]
  have le := count_le_one decls_functional (app "Box" [app "foo" [sym "bar"]])
    (.app [.sym "Wrap", .sym "Expression"])
  by_contra ne
  have one : count (info decls (app "Box" [app "foo" [sym "bar"]]))
      (.app [.sym "Wrap", .sym "Expression"]) = 1 := by omega
  obtain ⟨σ, hσ, fields⟩ := ctor_inversion decls_functional row _ rfl
    (.app [.sym "Wrap", .sym "Expression"]) (by simp [Named]) one
  have hσa : σ "a" = .sym "Expression" := by simpa using hσ
  have field := fields (.var "a", app "foo" [sym "bar"]) (by simp) (by simp [Unchecked])
  rw [Ty.bind_var', hσa, untyped] at field
  cases field

/-- `Cons`'s row. -/
abbrev consRow : Ty String := arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))

theorem cons_row : decls "Cons" = [consRow] := by simp [decls]

/-- `(Cons 5 Nil)` is typed once at `(List Number)` under the probe declarations. -/
theorem cons_five_typed : count (info decls (app "Cons" [num 5, sym "Nil"])) listNumber = 1 := by
  have := ctor_construction decls_functional cons_row cons_constructor [num 5, sym "Nil"] rfl
    (fun _ => .sym "Number") (by
      intro p hp _ _
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · exact count_num_number 5
      · simpa [listOf] using count_nil (.sym "Number"))
  simpa [listOf] using this

/-- **Repeated rows, read as SWI-PeTTa's `get-type` reads them, count twice**: with
`Cons` declared twice, `(Cons 5 Nil)` has two derivations at `(List Number)`.
Read with identical rows as one declaration, as CeTTa reads them, it has one. -/
theorem repeated_rows_twice :
    count (info (decls.addRow "Cons" consRow) (app "Cons" [num 5, sym "Nil"])) listNumber = 2 ∧
      count (info (Decls.idem (decls.addRow "Cons" consRow)) (app "Cons" [num 5, sym "Nil"]))
        listNumber = 1 := by
  classical
  constructor
  · have rows : decls.addRow "Cons" consRow "Cons" = [consRow] ++ [consRow] := by
      simp [Decls.addRow, decls]
    have nilInfo : info (decls.addRow "Cons" consRow) (sym "Nil") = info decls (sym "Nil") := by
      rw [info_symbol, info_symbol]
      simp [Decls.addRow]
    have numInfo : info (decls.addRow "Cons" consRow) (num 5) = info decls (num 5) := rfl
    set E := ctorEqs 1 [.var "a", listOf (.var "a")]
      [theDeriv decls_functional (num 5), theDeriv decls_functional (sym "Nil")] with hE
    have args : argEqs 1 [.var "a", listOf (.var "a")]
        [info decls (num 5), info decls (sym "Nil")] = {E} :=
      argEqs_singletons 1 _ _ _ rfl
        (.cons (eff_theDeriv decls_functional _) (.cons (eff_theDeriv decls_functional _) .nil))
    have typed := cons_five_typed
    rw [count_ctor decls_functional cons_row _ rfl _ (by simp [Named, listOf])] at typed
    split_ifs at typed with hsat
    have hE0 : Sat E := hsat.left
    have one : funTrees ⟨[consRow], 0⟩ [info decls (num 5), info decls (sym "Nil")] =
        {⟨(listOf (.var "a")).map DVar.own, E⟩} := by
      rw [funTrees_arrow _ _ _ _ rfl, args, Multiset.map_singleton, Multiset.filter_singleton,
        if_pos hE0]
    have funT : funTrees (info (decls.addRow "Cons" consRow) (sym "Cons"))
        [info decls (num 5), info decls (sym "Nil")] =
        {⟨(listOf (.var "a")).map DVar.own, E⟩} + {⟨(listOf (.var "a")).map DVar.own, E⟩} := by
      rw [info_symbol, rows, funTrees_rows_append _ _ _ 0, ← one]
      rfl
    rw [info_expression]
    simp only [List.map_cons, List.map_nil, numInfo, nilInfo, nodeInfo, funT]
    have hsat' : Sat (E ++ [((listOf (.var "a")).map DVar.own, listNumber.lift)]) := hsat
    unfold count eff
    rw [if_neg (by simp), if_neg (by simp), Multiset.filter_add, Multiset.filter_singleton]
    simp only [if_pos hsat']
    rfl
  · have same := info_idem_addRow (Γ := decls) "Cons" consRow (by simp [decls])
      (app "Cons" [num 5, sym "Nil"])
    have idemDecls : Decls.idem decls = decls := by
      funext s
      unfold Decls.idem decls
      split_ifs <;> simp
    rw [idemDecls] at same
    have h := cons_five_typed
    unfold count eff at h ⊢
    rw [same]
    exact h

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
