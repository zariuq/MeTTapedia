import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Constructors

/-!
# The typed call protocol

A call of a function with declared arrow rows runs, for each row, the row's
protocol: each argument is delivered by its parameter's demand and guarded,
the body runs, and its result is guarded (`chainCall`). The rows are read
with identical rows as one declaration (`typedCall`); distinct rows are
alternatives, and their answers add.

* **Demand.** A parameter typed `Atom` receives its argument as written and
  has no guard; `%Undefined%` and `_` receive it evaluated and unchecked;
  every other type is guarded (`Demand`, `demand`). A result typed `Atom`,
  `%Undefined%` or `_` is not guarded (`ResultGuarded`).
* **One continuation per answer.** Each guard is `TypeRelation.guard`: the
  type variables of a row are shared by its guards through a store of
  equations, so a row `(-> $t $t)` checks the result against the type its
  argument gave `$t` (`Controls.shared_variable_checks_result`).
* **Closed rows factor.** When a row has no type variables, its protocol is
  the body's bag, each answer counted by its result guard, the whole counted
  by the product of the argument guards (`chainCall_closed`).
* **Idempotent rows** (`typedCall_repeat`): adding a row alpha-equivalent to one
  the function has changes no answer; adding a row alpha-equivalent to none adds
  its alternatives (`typedCall_cons_fresh`). The declaration rows of the probe
  `distinct_declaration_rows`, `(-> Number Number)` and `(-> $t $t)`, give
  `(g2 1)` two answers (`Controls.distinct_rows_two_answers`).
* **HE** raises an error where PeTTa answers nothing (`HE.typedCall`): when no
  row admits the arguments, each row's failed check is an answer, `BadType` or
  `BadArgType` (`HE.typedCall_of_none`), and otherwise HE's answers are the
  admitted rows' (`HE.typedCall_of_some`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Demand -/

/-- How a parameter receives its argument. -/
inductive Demand where
  /-- `Atom`: as written, unguarded. -/
  | raw
  /-- `%Undefined%` or `_`: evaluated, unguarded. -/
  | unchecked
  /-- Any other type: evaluated and guarded. -/
  | guarded
  deriving DecidableEq, Repr

/-- The demand of a parameter type. -/
def demand (A : Ty String) : Demand :=
  if A = .sym "Atom" then .raw else if Unchecked A then .unchecked else .guarded

/-- Whether a result type is guarded: every type but `Atom`, `%Undefined%` and `_`. -/
def ResultGuarded (R : Ty String) : Prop := R ≠ .sym "Atom" ∧ ¬ Unchecked R

instance (R : Ty String) : Decidable (ResultGuarded R) := by
  unfold ResultGuarded
  infer_instance

/-! ## The protocol of one row -/

/-- The variables of a call's store: the row's type variables, and the
variables of the derivation read by the guard at each position. -/
abbrev CallVar := String ⊕ (ℕ × DVar)

/-- The derivation variables of the guard at position `k`. -/
def atGuard (k : ℕ) (d : DVar) : CallVar := .inr (k, d)

theorem atGuard_injective (k : ℕ) : Function.Injective (atGuard k) := by
  intro d d' h
  simpa [atGuard] using h

variable (Γ : Decls) (kind : Atom → String)

/-- The guards of the parameters, in order, threading the store; a parameter
that is not guarded passes the store on. Mismatched lengths have no
continuation. -/
noncomputable def guards : ℕ → List (Ty String) → List Atom → List (Eqn CallVar) →
    Multiset (List (Eqn CallVar))
  | _, [], [], S => {S}
  | k, A :: As, v :: vs, S =>
      if demand A = .guarded then
        (guard (atGuard k) S (A.map .inl) (info Γ v) (kind v)).bind (guards (k + 1) As vs)
      else guards (k + 1) As vs S
  | _, [], _ :: _, _ => 0
  | _, _ :: _, [], _ => 0

/-- The result guard of a row, after its arguments' guards left the store `S`. -/
noncomputable def resultGuard (k : ℕ) (R : Ty String) (S : List (Eqn CallVar)) (r : Atom) :
    Multiset Atom :=
  if ResultGuarded R then (guard (atGuard k) S (R.map .inl) (info Γ r) (kind r)).map fun _ => r
  else {r}

/-- **The protocol of one row**: the arguments' guards, the body, and the
result's guard. The arguments are the values each parameter's demand
delivered. -/
noncomputable def chainCall (body : List Atom → Multiset Atom) (τ : Ty String) (vs : List Atom) :
    Multiset Atom :=
  match arrowSplit τ with
  | some (As, R) =>
      (guards Γ kind 0 As vs []).bind fun S => (body vs).bind (resultGuard Γ kind As.length R S)
  | none => 0

/-- **A typed call**: the protocols of the function's rows, alpha-equivalent rows
read as one declaration (`dedupAlpha`). -/
noncomputable def typedCall (body : List Atom → Multiset Atom) (rows : List (Ty String))
    (vs : List Atom) : Multiset Atom :=
  ((dedupAlpha rows : List (Ty String)) : Multiset (Ty String)).bind fun τ => chainCall Γ kind body τ vs

/-! ## Identical and distinct rows -/

/-- **A row identical to one the function has changes no answer.** -/
theorem typedCall_repeat (body : List Atom → Multiset Atom) (rows : List (Ty String))
    (τ : Ty String) (repeated : ∃ σ ∈ rows, AlphaEq σ τ) (vs : List Atom) :
    typedCall Γ kind body (rows ++ [τ]) vs = typedCall Γ kind body rows vs := by
  unfold typedCall
  rw [dedupAlpha_append_alpha rows τ repeated]

/-- The index of a row followed by rows none of which is alpha-equivalent to it. -/
theorem dedupAlpha_cons_fresh (τ : Ty String) (rows : List (Ty String))
    (fresh : ∀ σ ∈ rows, ¬ AlphaEq τ σ) : dedupAlpha (τ :: rows) = τ :: dedupAlpha rows := by
  have step : ∀ (acc : List (Ty String)) (l : List (Ty String)), (∀ σ ∈ l, ¬ AlphaEq τ σ) →
      l.foldl (fun acc τ' => if acc.any fun σ => decide (AlphaEq σ τ') then acc else acc ++ [τ'])
          (τ :: acc) =
        τ :: l.foldl (fun acc τ' => if acc.any fun σ => decide (AlphaEq σ τ') then acc else acc ++ [τ'])
          acc := by
    intro acc l hl
    induction l generalizing acc with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldl_cons, List.any_cons]
        have hx : decide (AlphaEq τ x) = false := decide_eq_false (hl x (by simp))
        simp only [hx, Bool.false_or]
        split_ifs
        · exact ih acc fun σ hσ => hl σ (by simp [hσ])
        · rw [List.cons_append]
          exact ih (acc ++ [x]) fun σ hσ => hl σ (by simp [hσ])
  unfold dedupAlpha
  rw [List.foldl_cons]
  simp only [List.any_nil, Bool.false_eq_true, if_false, List.nil_append]
  exact step [] rows fresh

/-- **A row distinct from the function's rows adds its alternatives.** -/
theorem typedCall_cons_fresh (body : List Atom → Multiset Atom) (rows : List (Ty String))
    (τ : Ty String) (fresh : ∀ σ ∈ rows, ¬ AlphaEq τ σ) (vs : List Atom) :
    typedCall Γ kind body (τ :: rows) vs =
      chainCall Γ kind body τ vs + typedCall Γ kind body rows vs := by
  unfold typedCall
  rw [dedupAlpha_cons_fresh τ rows fresh, ← Multiset.cons_coe, Multiset.cons_bind]

/-- A function with one row runs that row's protocol. -/
theorem typedCall_single (body : List Atom → Multiset Atom) (τ : Ty String) (vs : List Atom) :
    typedCall Γ kind body [τ] vs = chainCall Γ kind body τ vs := by
  rw [show [τ] = τ :: ([] : List (Ty String)) from rfl,
    typedCall_cons_fresh Γ kind body [] τ (by simp) vs]
  simp [typedCall, dedupAlpha]

/-! ## Closed rows -/

/-- A store of the guards before position `k` of a closed row: satisfiable,
with only derivation variables of earlier guards. -/
def StoreOK (k : ℕ) (S : List (Eqn CallVar)) : Prop :=
  Sat S ∧ ∀ u ∈ eqnVars S, ∃ k' d, k' < k ∧ u = .inr (k', d)

theorem StoreOK.fresh {k : ℕ} {S : List (Eqn CallVar)} (h : StoreOK k S) :
    ∀ d, atGuard k d ∉ eqnVars S := by
  intro d hd
  obtain ⟨k', d', hk, he⟩ := h.2 _ hd
  simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at he
  omega

theorem StoreOK.nil : StoreOK 0 [] := ⟨sat_nil, by simp [eqnVars]⟩

theorem StoreOK.mono {k k' : ℕ} {S : List (Eqn CallVar)} (h : StoreOK k S) (le : k ≤ k') :
    StoreOK k' S :=
  ⟨h.1, fun u hu => by
    obtain ⟨j, d, hj, rfl⟩ := h.2 u hu
    exact ⟨j, d, by omega, rfl⟩⟩

theorem lift_map_inl (T : Ty Empty) : ((T.lift : Ty String).map Sum.inl : Ty CallVar) = T.lift := by
  rw [Ty.lift, Ty.map_map]
  congr 1
  funext v
  exact v.elim

open Classical in
/-- Every continuation of a guard at a closed formal is a good store one position
on. -/
theorem guard_closed_stores {k : ℕ} {S : List (Eqn CallVar)} (hS : StoreOK k S) (T : Ty Empty)
    (j : Info) (kindName : String) :
    ∀ S' ∈ guard (atGuard k) S T.lift j kindName, StoreOK (k + 1) S' := by
  intro S' hS'
  unfold guard at hS'
  have getTypeOK : ∀ S' ∈ getType (atGuard k) S T.lift j, StoreOK (k + 1) S' := by
    intro S' hS'
    unfold getType at hS'
    obtain ⟨hmem, hsat⟩ := Multiset.mem_filter.mp hS'
    obtain ⟨d, -, rfl⟩ := Multiset.mem_map.mp hmem
    refine ⟨hsat, fun u hu => ?_⟩
    rw [eqnVars_append, eqnVars_append, List.mem_append, List.mem_append, eqnVars_map] at hu
    rcases hu with (hu | hu) | hu
    · obtain ⟨j', d', hj, rfl⟩ := hS.2 u hu
      exact ⟨j', d', by omega, rfl⟩
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hu
      exact ⟨k, w, by omega, rfl⟩
    · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Ty.vars_lift, Ty.vars_map, List.mem_map] at hu
      obtain ⟨w, -, rfl⟩ := hu
      exact ⟨k, w, by omega, rfl⟩
  split_ifs at hS'
  · obtain ⟨hmem, hsat⟩ := Multiset.mem_filter.mp hS'
    rw [Multiset.mem_singleton] at hmem
    subst hmem
    refine ⟨hsat, fun u hu => ?_⟩
    rw [eqnVars_append, List.mem_append] at hu
    rcases hu with hu | hu
    · obtain ⟨j', d', hj, rfl⟩ := hS.2 u hu
      exact ⟨j', d', by omega, rfl⟩
    · simp [eqnVars, Eqn.vars] at hu
  · exact getTypeOK S' hS'

/-- `s.bind (fun _ => t)` repeats `t` once per element of `s`. -/
theorem bind_const' {α β : Type} (s : Multiset α) (t : Multiset β) :
    (s.bind fun _ => t) = Multiset.card s • t := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.cons_bind, ih, Multiset.card_cons, succ_nsmul, add_comm]

/-- The product of the guard counts of the guarded parameters of a closed row. -/
noncomputable def argCount : List (Ty Empty) → List Atom → ℕ
  | [], [] => 1
  | A :: As, v :: vs =>
      (if demand A.lift = .guarded then guardCount (info Γ v) A (kind v) else 1) * argCount As vs
  | [], _ :: _ => 0
  | _ :: _, [] => 0

/-- The guards of a closed row, followed by any continuation that ignores a
good store, count the continuation once per argument derivation. -/
theorem guards_closed_bind {β : Type} (n : ℕ) (f : List (Eqn CallVar) → Multiset β)
    (t : Multiset β) (hf : ∀ S, StoreOK n S → f S = t) :
    ∀ (k : ℕ) (As : List (Ty Empty)) (vs : List Atom) (S : List (Eqn CallVar)),
      k + As.length ≤ n → StoreOK k S →
      (guards Γ kind k (As.map Ty.lift) vs S).bind f = argCount Γ kind As vs • t
  | k, [], [], S, le, hS => by
      simp [guards, argCount, hf S (hS.mono (by simpa using le)), one_nsmul]
  | k, A :: As, v :: vs, S, le, hS => by
      simp only [List.length_cons] at le
      simp only [List.map_cons, guards, argCount]
      split_ifs with hd
      · rw [Multiset.bind_assoc]
        have each : ∀ S' ∈ guard (atGuard k) S ((A.lift : Ty String).map Sum.inl) (info Γ v) (kind v),
            (guards Γ kind (k + 1) (As.map Ty.lift) vs S').bind f = argCount Γ kind As vs • t := by
          intro S' hS'
          rw [lift_map_inl] at hS'
          exact guards_closed_bind n f t hf (k + 1) As vs S' (by omega)
            (guard_closed_stores hS A _ _ S' hS')
        rw [Multiset.bind_congr each, bind_const', lift_map_inl,
          card_guard_closed (atGuard k) (atGuard_injective k) S hS.fresh hS.1 A _ _, ← mul_nsmul,
          Nat.mul_comm]
      · rw [one_mul]
        exact guards_closed_bind n f t hf (k + 1) As vs S (by omega) (hS.mono (by omega))
  | _, [], _ :: _, _, _, _ => by simp [guards, argCount]
  | _, _ :: _, [], _, _, _ => by simp [guards, argCount]

theorem resultGuard_closed {k : ℕ} {S : List (Eqn CallVar)} (hS : StoreOK k S) (R : Ty Empty)
    (r : Atom) :
    resultGuard Γ kind k R.lift S r =
      if ResultGuarded R.lift then guardCount (info Γ r) R (kind r) • {r} else {r} := by
  unfold resultGuard
  split_ifs
  · rw [lift_map_inl, Multiset.map_const',
      card_guard_closed (atGuard k) (atGuard_injective k) S hS.fresh hS.1 R _ _,
      Multiset.nsmul_singleton]
  · rfl

/-- **The protocol of a closed row factors**: each answer of the body counted by
its result guard, the whole counted by the argument guards. -/
theorem chainCall_closed (body : List Atom → Multiset Atom) (As : List (Ty Empty)) (R : Ty Empty)
    (vs : List Atom) :
    chainCall Γ kind body (arrow (As.map Ty.lift) R.lift) vs =
      argCount Γ kind As vs • (body vs).bind fun r =>
        if ResultGuarded R.lift then guardCount (info Γ r) R (kind r) • {r} else {r} := by
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  rw [List.length_map]
  refine guards_closed_bind Γ kind As.length _ _ (fun S hS => ?_) 0 As vs [] (by omega)
    StoreOK.nil
  exact Multiset.bind_congr fun r _ => resultGuard_closed Γ kind hS R r

/-! ## One derivation at a request -/

open Classical in
theorem getType_of_eff {U : Type} (e : DVar → U) (S : List (Eqn U)) (T : Ty U) {j : Info} {d : Deriv}
    (h : eff j = {d}) :
    getType e S T j = if Sat (S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)])
      then {S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)]} else 0 := by
  unfold getType
  rw [h, Multiset.map_singleton, Multiset.filter_singleton]
  rfl

open Classical in
theorem guard_of_getType {U : Type} (e : DVar → U) (S : List (Eqn U)) (T : Ty U) (j : Info)
    (kindName : String) (h : getType e S T j ≠ 0) : guard e S T j kindName = getType e S T j := by
  unfold guard
  rw [if_neg (by rwa [Multiset.card_eq_zero])]

/-- Under functional declarations a guard at a closed type continues at most once. -/
theorem guardCount_le_one {Γ : Decls} (hΓ : Functional Γ) (v : Atom) (T : Ty Empty) (kindName : String) :
    guardCount (info Γ v) T kindName ≤ 1 := by
  unfold guardCount
  have := count_le_one hΓ v T
  split_ifs <;> omega

/-! ## Stores with the same solutions -/

/-- Two stores with the same solutions: no later guard tells them apart. -/
def SameSol {U : Type} (S S' : List (Eqn U)) : Prop := ∀ ρ : U → Ty Empty, Solves ρ S ↔ Solves ρ S'

/-- Related continuations: stores with the same solutions, the first satisfiable. -/
def Agree {U : Type} (S S' : List (Eqn U)) : Prop := SameSol S S' ∧ Sat S

theorem SameSol.append {U : Type} {S S' : List (Eqn U)} (h : SameSol S S') (X : List (Eqn U)) :
    SameSol (S ++ X) (S' ++ X) := fun ρ => by
  rw [solves_append, solves_append, h ρ]

theorem SameSol.sat_iff {U : Type} {S S' : List (Eqn U)} (h : SameSol S S') : Sat S ↔ Sat S' :=
  ⟨fun ⟨ρ, hρ⟩ => ⟨ρ, (h ρ).mp hρ⟩, fun ⟨ρ, hρ⟩ => ⟨ρ, (h ρ).mpr hρ⟩⟩

theorem SameSol.trans {U : Type} {S S' S'' : List (Eqn U)} (h : SameSol S S') (h' : SameSol S' S'') :
    SameSol S S'' := fun ρ => (h ρ).trans (h' ρ)

theorem SameSol.symm {U : Type} {S S' : List (Eqn U)} (h : SameSol S S') : SameSol S' S :=
  fun ρ => (h ρ).symm

/-- An equation between equal types binds nothing. -/
theorem sameSol_taut {U : Type} (S : List (Eqn U)) (t : Ty U) : SameSol (S ++ [(t, t)]) S :=
  fun ρ => by rw [solves_append, solves_singleton]; simp

open Classical in
theorem getType_agree {U : Type} (e : DVar → U) {S S' : List (Eqn U)} (h : SameSol S S')
    (T : Ty U) (j : Info) : Multiset.Rel Agree (getType e S T j) (getType e S' T j) := by
  unfold getType
  rw [Multiset.filter_map, Multiset.filter_map]
  have same : (eff j).filter (Sat ∘ fun d => S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)]) =
      (eff j).filter (Sat ∘ fun d => S' ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)]) :=
    Multiset.filter_congr fun d _ => by
      simp only [Function.comp, List.append_assoc]
      exact (h.append _).sat_iff
  rw [same, Multiset.rel_map]
  refine Multiset.rel_refl_of_refl_on fun d hd => ⟨?_, ?_⟩
  · simp only [List.append_assoc]
    exact h.append _
  · have hsat : Sat (S' ++ (d.eqs.map (Eqn.map e) ++ [(d.ty.map e, T)])) := by
      simpa only [Function.comp, List.append_assoc] using (Multiset.mem_filter.mp hd).2
    simpa only [List.append_assoc] using (h.append _).sat_iff.mpr hsat

open Classical in
/-- **A guard does not tell stores with the same solutions apart.** -/
theorem guard_agree {U : Type} (e : DVar → U) {S S' : List (Eqn U)} (h : SameSol S S') (T : Ty U)
    (j : Info) (kindName : String) :
    Multiset.Rel Agree (guard e S T j kindName) (guard e S' T j kindName) := by
  have rel := getType_agree e h T j
  unfold guard
  rw [Multiset.card_eq_card_of_rel rel]
  split_ifs
  · rw [Multiset.filter_singleton, Multiset.filter_singleton]
    by_cases hs : Sat (S ++ [(.sym kindName, T)])
    · rw [if_pos hs, if_pos ((h.append _).sat_iff.mp hs)]
      exact .cons ⟨h.append _, hs⟩ .zero
    · rw [if_neg hs, if_neg fun hs' => hs ((h.append _).sat_iff.mpr hs')]
      exact .zero
  · exact rel

/-- **The guards do not tell stores with the same solutions apart.** -/
theorem guards_agree : ∀ (k : ℕ) (As : List (Ty String)) (vs : List Atom) {S S' : List (Eqn CallVar)},
    Agree S S' → Multiset.Rel Agree (guards Γ kind k As vs S) (guards Γ kind k As vs S')
  | _, [], [], _, _, h => .cons h .zero
  | k, A :: As, v :: vs, S, S', h => by
      simp only [guards]
      split_ifs
      · exact Multiset.rel_bind (fun _ _ hab => guards_agree (k + 1) As vs hab)
          (guard_agree _ h.1 _ _ _)
      · exact guards_agree (k + 1) As vs h
  | _, [], _ :: _, _, _, _ => by simp only [guards]; exact .zero
  | _, _ :: _, [], _, _, _ => by simp only [guards]; exact .zero

/-- The result guard reads a store only through its solutions. -/
theorem resultGuard_congr (k : ℕ) (R : Ty String) {S S' : List (Eqn CallVar)} (h : SameSol S S')
    (r : Atom) : resultGuard Γ kind k R S r = resultGuard Γ kind k R S' r := by
  unfold resultGuard
  split_ifs
  · rw [Multiset.map_const', Multiset.map_const',
      Multiset.card_eq_card_of_rel (guard_agree _ h _ _ _)]
  · rfl

/-- Related continuations give the same answers to anything reading stores
through their solutions. -/
theorem bind_agree {β : Type} {s t : Multiset (List (Eqn CallVar))} (h : Multiset.Rel Agree s t)
    (f g : List (Eqn CallVar) → Multiset β) (hfg : ∀ {S S'}, Agree S S' → f S = g S') :
    s.bind f = t.bind g := by
  rw [← Multiset.rel_eq]
  exact Multiset.rel_bind (fun _ _ hab => by rw [hfg hab]; exact Multiset.rel_eq.mpr rfl) h

/-! ## A guard met on a literal of its class -/

/-- A grounded value of the value class `c`. -/
def Literal (c : String) : Atom → Prop
  | .grounded g => valueClass g = some c
  | _ => False

instance (c : String) (v : Atom) : Decidable (Literal c v) := by
  cases v <;> unfold Literal <;> infer_instance

open Classical in
/-- **A guard at a value class on a literal of that class** continues once, with
the store extended by an equation between equal types: it binds nothing. -/
theorem guard_literal {U : Type} (e : DVar → U) {S : List (Eqn U)} (hS : Sat S) {c : String}
    {v : Atom} (hv : Literal c v) (Γ : Decls) (kindName : String) :
    guard e S (.sym c) (info Γ v) kindName = {S ++ [(.sym c, .sym c)]} := by
  obtain ⟨g, rfl⟩ : ∃ g, v = .grounded g := by
    cases v with
    | grounded g => exact ⟨g, rfl⟩
    | symbol _ => exact (hv : False).elim
    | var _ => exact (hv : False).elim
    | expression _ => exact (hv : False).elim
  have hinfo := info_grounded_class Γ (show valueClass g = some c from hv)
  have heff : eff (info Γ (.grounded g)) = {classDeriv c} := by
    rw [hinfo]
    unfold eff
    simp
  have sat : Sat (S ++ (classDeriv c).eqs.map (Eqn.map e) ++
      [((classDeriv c).ty.map e, (.sym c : Ty U))]) := by
    obtain ⟨ρ, hρ⟩ := hS
    exact ⟨ρ, (solves_append _ _ _).mpr ⟨by simpa [classDeriv] using hρ,
      (solves_singleton _ _).mpr (by simp [classDeriv])⟩⟩
  have one : getType e S (.sym c) (info Γ (.grounded g)) =
      {S ++ [(.sym c, .sym c)]} := by
    rw [getType_of_eff e S _ heff, if_pos sat]
    simp [classDeriv]
  rw [guard_of_getType e S _ _ kindName (by rw [one]; exact Multiset.singleton_ne_zero _), one]

/-- A value class is guarded. -/
theorem demand_valueClass {c : String} (hc : IsValueClass c) : demand (.sym c) = .guarded := by
  rcases hc with rfl | rfl | rfl <;> decide

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional num str count_num_number theDeriv_int)

/-- The metatype classes of the probes: no symbol names a registered function. -/
def probeKind : Atom → String := metatype fun _ => false

/-- `(-> Number Number)`. -/
abbrev numberRow : Ty String := arrow [.sym "Number"] (.sym "Number")

/-- `(-> $t $t)`. -/
abbrev identityRow : Ty String := arrow [.var "t"] (.var "t")

theorem eff_num (n : ℤ) : eff (info decls (num n)) = {classDeriv "Number"} := by
  rw [info_int]
  unfold eff
  simp

theorem eff_str (s : String) : eff (info decls (str s)) = {classDeriv "String"} := by
  rw [info_string]
  unfold eff
  simp

/-- The closed row admits `1` and its body's `2` once. -/
theorem number_row_once :
    chainCall decls probeKind (fun _ => {num 2}) numberRow [num 1] = {num 2} := by
  have := chainCall_closed decls probeKind (fun _ => {num 2}) [.sym "Number"] (.sym "Number") [num 1]
  simp only [List.map_cons, List.map_nil] at this
  rw [show numberRow = arrow [(Ty.sym "Number" : Ty Empty).lift] (Ty.sym "Number" : Ty Empty).lift
    from rfl, this]
  have g1 : guardCount (info decls (num 1)) (.sym "Number") (probeKind (num 1)) = 1 := by
    rw [guardCount_of_ne _ _ _ (by simp [probeKind, metatype]), count_num_number]
  have g2 : guardCount (info decls (num 2)) (.sym "Number") (probeKind (num 2)) = 1 := by
    rw [guardCount_of_ne _ _ _ (by simp [probeKind, metatype]), count_num_number]
  simp [argCount, demand, Unchecked, Ty.lift, g1, g2, ResultGuarded, one_nsmul]

open Classical in
/-- **A row's type variable is shared by its guards**: `(-> $t $t)` fixes `$t` at
the argument's type and checks the result against it. -/
theorem identity_row (result : Atom) (resultType : String)
    (eff_result : eff (info decls result) = {classDeriv resultType})
    (kindResult : probeKind result = "Grounded") :
    chainCall decls probeKind (fun _ => {result}) identityRow [num 1] =
      if resultType = "Number" then {result} else 0 := by
  -- the argument's guard fixes `$t` at `Number`
  set S₁ : List (Eqn CallVar) := [] ++ (classDeriv "Number").eqs.map (Eqn.map (atGuard 0)) ++
    [((classDeriv "Number").ty.map (atGuard 0), (Ty.var "t").map Sum.inl)] with hS₁
  have sat₁ : Sat S₁ := ⟨fun _ => .sym "Number", by
    intro e he
    simp [hS₁, classDeriv] at he
    subst he
    rfl⟩
  have arg : guard (atGuard 0) [] ((Ty.var "t").map Sum.inl) (info decls (num 1)) (probeKind (num 1)) =
      {S₁} := by
    have gt := getType_of_eff (atGuard 0) [] ((Ty.var "t").map Sum.inl) (eff_num 1)
    rw [if_pos sat₁] at gt
    rw [guard_of_getType _ _ _ _ _ (by rw [gt]; exact Multiset.singleton_ne_zero _), gt]
  have dt : demand (Ty.var "t") = .guarded := by decide
  have gs : guards decls probeKind 0 [Ty.var "t"] [num 1] [] = {S₁} := by
    simp only [guards, if_pos dt, arg, Multiset.singleton_bind]
  have rg : ResultGuarded (Ty.var "t") := by decide
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  rw [gs, Multiset.singleton_bind, Multiset.singleton_bind]
  unfold resultGuard
  rw [if_pos rg, show [Ty.var "t"].length = 1 from rfl]
  have gt := getType_of_eff (atGuard 1) S₁ ((Ty.var "t").map Sum.inl) eff_result
  by_cases hr : resultType = "Number"
  · subst hr
    have sat₂ : Sat (S₁ ++ (classDeriv "Number").eqs.map (Eqn.map (atGuard 1)) ++
        [((classDeriv "Number").ty.map (atGuard 1), (Ty.var "t").map Sum.inl)]) := by
      refine ⟨fun _ => .sym "Number", ?_⟩
      intro e he
      simp [hS₁, classDeriv] at he
      subst he
      rfl
    rw [if_pos sat₂] at gt
    rw [guard_of_getType _ _ _ _ _ (by rw [gt]; exact Multiset.singleton_ne_zero _), gt, if_pos rfl]
    simp
  · have unsat : ¬ Sat (S₁ ++ (classDeriv resultType).eqs.map (Eqn.map (atGuard 1)) ++
        [((classDeriv resultType).ty.map (atGuard 1), (Ty.var "t").map Sum.inl)]) := by
      rintro ⟨σ, hσ⟩
      have h1 := hσ ((classDeriv "Number").ty.map (atGuard 0), (Ty.var "t").map Sum.inl) (by simp [hS₁])
      have h2 := hσ ((classDeriv resultType).ty.map (atGuard 1), (Ty.var "t").map Sum.inl) (by simp)
      simp only [classDeriv, Ty.map_sym, Ty.map_var, Ty.bind_sym, Ty.bind_var'] at h1 h2
      rw [← h1] at h2
      exact hr (Ty.sym.inj h2)
    rw [if_neg unsat] at gt
    rw [if_neg hr]
    unfold guard
    rw [gt, kindResult]
    -- the metatype `Grounded` does not meet `$t`, fixed at `Number`
    have noMeta : ¬ Sat (S₁ ++ [(Ty.sym "Grounded", (Ty.var "t").map Sum.inl)]) := by
      rintro ⟨σ, hσ⟩
      have h1 := hσ ((classDeriv "Number").ty.map (atGuard 0), (Ty.var "t").map Sum.inl) (by simp [hS₁])
      have h2 := hσ (Ty.sym "Grounded", (Ty.var "t").map Sum.inl) (by simp)
      simp only [classDeriv, Ty.map_sym, Ty.map_var, Ty.bind_sym, Ty.bind_var'] at h1 h2
      rw [← h1] at h2
      simp at h2
    rw [if_pos (by simp), Multiset.filter_singleton, if_neg noMeta]
    rfl

/-- **Distinct rows are alternatives**: with `(: g2 (-> Number Number))` and
`(: g2 (-> $t $t))`, `(g2 1)` answers `2` twice, once per row, as in the probe
`distinct_declaration_rows`. -/
theorem distinct_rows_two_answers :
    typedCall decls probeKind (fun _ => {num 2}) [numberRow, identityRow] [num 1] =
      {num 2, num 2} := by
  rw [typedCall_cons_fresh _ _ _ _ _ (by intro σ hσ; simp at hσ; subst hσ; decide), typedCall_single,
    number_row_once, identity_row (num 2) "Number" (eff_num 2) rfl, if_pos rfl]
  rfl

/-- **The shared variable checks the result**: a body answering a string through
`(-> $t $t)` at a number has no answer. -/
theorem shared_variable_checks_result :
    chainCall decls probeKind (fun _ => {str "a"}) identityRow [num 1] = 0 := by
  rw [identity_row (str "a") "String" (eff_str "a") rfl, if_neg (by decide)]

end Controls

/-! ## HE: errors where PeTTa answers nothing -/

namespace HE

/-- Why a row rejects a call. -/
inductive Cause where
  /-- An argument does not meet its parameter. -/
  | badArgType (position : ℕ)
  /-- The call does not meet the requested type. -/
  | badType
  deriving DecidableEq, Repr

/-- An answer of an HE call: a value, or the error of a row whose check failed. -/
inductive Answer where
  | value (r : Atom)
  | error (row : Ty String) (cause : Cause)

/-- **HE's typed call**: the answers of the rows that admit the arguments, each
admission once; when no row admits them, the error of every row. -/
def typedCall (admits : Ty String → List Atom → ℕ) (cause : Ty String → List Atom → Cause)
    (body : List Atom → Multiset Atom) (rows : List (Ty String)) (vs : List Atom) :
    Multiset Answer :=
  if ∀ τ ∈ rows, admits τ vs = 0 then ((rows.map fun τ => Answer.error τ (cause τ vs)) : List Answer)
  else ((rows : Multiset (Ty String)).bind fun τ => admits τ vs • (body vs).map Answer.value)

/-- **When no row admits the arguments, HE answers one error per row**, where
PeTTa's protocol answers nothing. -/
theorem typedCall_of_none (admits : Ty String → List Atom → ℕ) (cause : Ty String → List Atom → Cause)
    (body : List Atom → Multiset Atom) (rows : List (Ty String)) (vs : List Atom)
    (none_ : ∀ τ ∈ rows, admits τ vs = 0) :
    typedCall admits cause body rows vs = ((rows.map fun τ => Answer.error τ (cause τ vs)) : List Answer) ∧
      Multiset.card (typedCall admits cause body rows vs) = rows.length := by
  unfold typedCall
  rw [if_pos none_]
  exact ⟨rfl, by simp⟩

/-- **When some row admits them, HE's answers are values**: each admitted row's
body answers, once per admission. -/
theorem typedCall_of_some (admits : Ty String → List Atom → ℕ) (cause : Ty String → List Atom → Cause)
    (body : List Atom → Multiset Atom) (rows : List (Ty String)) (vs : List Atom)
    (some_ : ∃ τ ∈ rows, admits τ vs ≠ 0) :
    typedCall admits cause body rows vs =
      (rows : Multiset (Ty String)).bind fun τ => admits τ vs • (body vs).map Answer.value := by
  unfold typedCall
  rw [if_neg]
  rintro h
  obtain ⟨τ, hτ, hne⟩ := some_
  exact hne (h τ hτ)

/-- Where HE's check of each row counts what PeTTa's argument guards count, and
results are unguarded, HE's values are PeTTa's answers. -/
theorem values_of_admitted (admits : Ty String → List Atom → ℕ) (cause : Ty String → List Atom → Cause)
    (body : List Atom → Multiset Atom) (rows : List (Ty String)) (vs : List Atom)
    (some_ : ∃ τ ∈ rows, admits τ vs ≠ 0) :
    typedCall admits cause body rows vs =
      ((rows : Multiset (Ty String)).bind fun τ => admits τ vs • body vs).map Answer.value := by
  rw [typedCall_of_some admits cause body rows vs some_, Multiset.map_bind]
  congr 1
  funext τ
  rw [Multiset.map_nsmul]

end HE

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
