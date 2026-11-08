import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.DeclaredBuiltins

/-!
# Polymorphic signatures

A formal with type variables, such as the `(List $a)` of
`(: len (-> (List $a) Number))`, is guarded with a fresh copy of the row's
variables at every call. When the formal's variables are **private**, named by
no other formal and not by the result, the guard does not see the store
(`card_guard_private`), and it counts the value's derivations that meet some
instance of the formal (`polyCount`).

* **Exactly once.** Under functional declarations the guard of a private
  formal that is an application succeeds once exactly when the value is typed
  at some closed instance of the formal, and fails otherwise
  (`guardCountPoly_functional`, `PolyHolds`).
* **Inversion and construction at instances.** An application of a
  constructor accepted at a private formal is typed at a closed instance, so
  inversion gives its checked fields their instances (`poly_inversion`); a
  field whose declared type is an instance of the formal meets the formal
  again (`polyHolds_of_instance`), which is the fact a call to itself on the
  field needs; and a construction whose result is an instance of the formal
  meets it (`polyHolds_of_count`).
* **Private rows factor** (`chainCall_private`): with every formal's variables
  private and a closed result, the protocol is the body's bag counted by the
  guards, and the version theorem applies to it
  (`private_version_eq_protocol`, through `factored_version_eq`).
* **Shared variables: a store is a common instance.** The store of a call
  allows exactly the instances of the row's variables at which every value it
  has guarded is typed (`allows_extend`). So under functional declarations,
  with every formal and the result never a metatype name at any instance, an
  answer of the body counts once exactly when one instance of the row's
  variables types every argument and the answer, and otherwise not at all
  (`chainCall_shared`). In `(-> Number (List $a) (List $a))` the argument `Nil`
  leaves `$a` free and a list of numbers is admitted
  (`Controls.shared_nil`), while a list of strings fixes `$a` at `String` and
  the same answer is not (`Controls.shared_strings`).

* **Private formals in the analysis** (`contract_private_formal`,
  `AcceptedPriv`): facts read at every closed instance of the formals, calls to
  themselves meeting some instance (`contract_meets_formal`). Arguments meeting
  facts of some instance of each formal meet those of one instance of all
  (`entryPoly_instance`), and every guard passes once
  (`argCountPoly_of_entry`), so the version is the protocol
  (`private_accepted_version_eq_protocol`).
* **Facts read with the variables as constants** (`PatFactOpen`, `contract_invert`
  at a type with variables): matching a constructor's declared result one way
  onto an open type, `R.bind ρ = F`, and reading the fields under `ρ`, gives at
  every instance `F σ` the closed fact through `ρ` followed by `σ`
  (`PatFactOpen.instance`), so the open facts of an equation are the facts at
  every instance that `AcceptedPriv` reads (`eqFactsOpen_instance`,
  `Controls.len_open_fact`).
* **Uninterpreted arguments** (`PETTA_CONTRACT_ENTRY_UNINTERPRETED`,
  `oem_value_uninterpreted`, `contract_returns_argument`): an uninterpreted
  value's type is structural, and an instance of it (`substA`, the argument as
  unification leaves it) that puts no declared symbol at a head position (`Safe`)
  is typed at an instance of that type (`struct_of_safe`), so the pair guard of a
  parameter shared with the result passes the instance exactly once
  (`pair_once`); bindings by uninterpreted values meet the restriction
  (`safe_of_uninterp`, `pair_once_uninterp`). A declared symbol at a head
  position breaks it (`pair_zero`, `Controls.pair_rejects_declared_head`), and a
  declared head excludes the argument from the start (`Controls.same_not_safe`,
  with `TypedCalls.Controls.instance_loses_type`).
* **Versions at an uninterpreted parameter** (`PETTA_CONTRACT_ENTRY_UNINTERPRETED`,
  `contract_returns_argument`, `contract_bind_any`): at `(-> A₁ … $a … Aₖ $a)`, the
  `Aᵢ` closed, the protocol on an uninterpreted argument whose equations answer
  instances of it that keep its heads free counts each answer once
  (`pair_protocol`, through `guard_var_uninterp`, `pair_result_once`, and the closed
  guards on stores with and without `$a`'s equation, `guards_closed_pairStores`).
  When the equations call themselves only at such arguments and answer instances by
  uninterpreted bindings, the argument as two-way unification leaves it
  (`UnintHyps`), the version is the protocol at every fuel
  (`unint_version_eq_protocol`, `unint_checked_call_eq`). Controls: `(pin ($g 1) 2)`
  answers `($g 1)` once (`Controls.pin_version`), `(bnd ($g $m))` answers `($g 1)`
  once (`Controls.bnd_version`), and a binding to the declared `inc` makes an answer
  the version gives and the protocol rejects (`Controls.inc_binding_breaks`).
* **Arguments typed by their callee at a private formal**
  (`petta_machine_argument_typed_by_callee`): an answer typed at an instance of
  the callee's range `R'`, which the formal matches, `F σ = R'`, is typed at an
  instance of `F` (`polyHolds_of_range`), and every answer of a call with shared
  variables is typed at an instance of its range (`chainCall_shared_answers`); so
  a row with private parameters and a closed result has, on such answers, the
  answers of the row with that parameter unchecked (`argument_typed_by_callee_private`,
  `Controls.lenP_over_buildP`). A shared variable (`Controls.pairP_shared`) and a
  range matching no instance (`Controls.mktree_no_match`) are outside it.
* **Instance versions** (`contract_instance_version`): when the analysis
  accepts the equations at a closed instance `θ(S)` of a signature `S`, the run
  of `S`'s own protocol at every call has the version's answers at every fuel on
  arguments typed once at the instance's formals
  (`instance_version_eq_protocol`), and a checked call at `S`, its argument guards
  before the entry and its result guard after, enters the version
  (`instance_checked_call_eq`); its result check at the open range admits the
  version's answers once each, so it can be met (`instance_range_met`). A function
  argument whose one declaration is its
  formal's instance meets the instance (`constant_holds`), so a constant
  parameter whose declaration closes the signature is an instance version.
* **A range written as a parameter's type variable, as an owed class**
  (`PREPARED_PURE_VALUE_PARAMETER`, `return_class`): at `(-> A₁ … $t … Aₖ $t)`
  whose closed parameters pass, on a value of the class `c` at `$t`, the
  protocol checks once at `c` (`checksAt_value_parameter`), so an activation of
  such a head owes the class of its argument there, and its chain is the
  protocol (`Controls.lead_chain`, `Controls.flip_chain`, through
  `machine_call_eq_protocol`).

Controls with `(: len (-> (List $a) Number))`: `(Cons 1 (Cons "x" Nil))` fails the
guard, `(Cons "x" Nil)` and `Nil` pass it once (`Controls.len_guard`). With
`(: build (-> Number (List $a) (List $a)))`, whose body fixes `$a` at `Number`,
the instance version is the signature's protocol on lists of numbers
(`Controls.build_version`); `(build 0 (Cons "a" Nil))` misses the instance and
the signature's protocol answers it where the instance's answers nothing
(`Controls.build_off_instance`). `fold-with` called with `inc` is the instance
version that `inc`'s declaration fixes (`Controls.fold_version`). `len` is
accepted at its private formal (`Controls.len_accepted`, `Controls.len_version`)
and a list of strings meets its entry fact (`Controls.len_strings`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## The guard at a private formal -/

section Private

variable {U : Type}

open Classical in
/-- **A private formal does not see the store**: extending a satisfiable store by
a derivation and a formal whose variables are fresh is satisfiable exactly when
the derivation meets some closed instance of the formal. -/
theorem sat_extend_private_iff (e : DVar → U) (injective : Function.Injective e)
    (ι : String → U) (injι : Function.Injective ι) (S : List (Eqn U)) (hS : Sat S) (freshE : ∀ v, e v ∉ eqnVars S)
    (F : Ty String) (freshF : ∀ x ∈ F.vars, ι x ∉ eqnVars S) (apart : ∀ v x, e v ≠ ι x)
    (d : Deriv) :
    Sat (S ++ d.eqs.map (Eqn.map e) ++ [(d.ty.map e, F.map ι)]) ↔
      ∃ σ : String → Ty Empty, Sat (d.eqs ++ [(d.ty, (F.bind σ).lift)]) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    rw [solves_append, solves_append, solves_singleton] at hρ
    refine ⟨ρ ∘ ι, ρ ∘ e, (solves_append _ _ _).mpr ⟨(solves_map ρ e _).mp hρ.1.2, ?_⟩⟩
    rw [solves_singleton, Ty.lift_bind_ground]
    have := hρ.2
    rw [Ty.bind_map, Ty.bind_map] at this
    exact this
  · rintro ⟨σ, τ, hτ⟩
    obtain ⟨σS, hσS⟩ := hS
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hτ
    refine ⟨fun u => if h : ∃ v, e v = u then τ h.choose
      else if h' : ∃ x ∈ F.vars, ι x = u then σ h'.choose else σS u, ?_⟩
    rw [solves_append, solves_append, solves_singleton]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (solves_congr fun u hu => ?_).mpr hσS
      have h1 : ¬ ∃ v, e v = u := fun ⟨v, hv⟩ => freshE v (hv ▸ hu)
      have h2 : ¬ ∃ x ∈ F.vars, ι x = u := fun ⟨x, hx, hxu⟩ => freshF x hx (hxu ▸ hu)
      simp [h1, h2]
    · rw [solves_map]
      refine (solves_congr fun v _ => ?_).mpr hτ.1
      have h : ∃ w, e w = e v := ⟨v, rfl⟩
      simp only [Function.comp, dif_pos h]
      rw [injective h.choose_spec]
    · rw [Ty.bind_map, Ty.bind_map]
      have left : d.ty.bind ((fun u => if h : ∃ v, e v = u then τ h.choose
          else if h' : ∃ x ∈ F.vars, ι x = u then σ h'.choose else σS u) ∘ e) = d.ty.bind τ := by
        refine Ty.bind_congr _ fun v _ => ?_
        have h : ∃ w, e w = e v := ⟨v, rfl⟩
        simp only [Function.comp, dif_pos h]
        rw [injective h.choose_spec]
      have right : F.bind ((fun u => if h : ∃ v, e v = u then τ h.choose
          else if h' : ∃ x ∈ F.vars, ι x = u then σ h'.choose else σS u) ∘ ι) = F.bind σ := by
        refine Ty.bind_congr _ fun x hx => ?_
        have h1 : ¬ ∃ v, e v = ι x := fun ⟨v, hv⟩ => apart v x hv
        have h2 : ∃ y ∈ F.vars, ι y = ι x := ⟨x, hx, rfl⟩
        simp only [Function.comp, dif_neg h1, dif_pos h2]
        rw [injι h2.choose_spec.2]
      rw [left, right]
      exact hτ.2

open Classical in
/-- The derivations of a value that meet some closed instance of a formal. -/
noncomputable def polyCount (j : Info) (F : Ty String) : ℕ :=
  Multiset.card ((eff j).filter fun d =>
    ∃ σ : String → Ty Empty, Sat (d.eqs ++ [(d.ty, (F.bind σ).lift)]))

open Classical in
theorem card_getType_private (e : DVar → U) (injective : Function.Injective e) (ι : String → U)
    (injι : Function.Injective ι) (S : List (Eqn U)) (hS : Sat S) (freshE : ∀ v, e v ∉ eqnVars S)
    (F : Ty String) (freshF : ∀ x ∈ F.vars, ι x ∉ eqnVars S) (apart : ∀ v x, e v ≠ ι x)
    (j : Info) : Multiset.card (getType e S (F.map ι) j) = polyCount j F := by
  unfold getType polyCount
  rw [Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d _
  exact sat_extend_private_iff e injective ι injι S hS freshE F freshF apart d

open Classical in
/-- The guard's continuations at a private formal: the derivations meeting some
instance of it, or, when there are none, one if the metatype is an instance. -/
noncomputable def guardCountPoly (j : Info) (F : Ty String) (kind : String) : ℕ :=
  if polyCount j F = 0 then (if ∃ σ : String → Ty Empty, F.bind σ = .sym kind then 1 else 0)
  else polyCount j F

open Classical in
/-- **The guard at a private formal**, counted without the store. -/
theorem card_guard_private (e : DVar → U) (injective : Function.Injective e) (ι : String → U)
    (injι : Function.Injective ι) (S : List (Eqn U)) (hS : Sat S) (freshE : ∀ v, e v ∉ eqnVars S)
    (F : Ty String) (freshF : ∀ x ∈ F.vars, ι x ∉ eqnVars S) (apart : ∀ v x, e v ≠ ι x)
    (j : Info) (kind : String) :
    Multiset.card (guard e S (F.map ι) j kind) = guardCountPoly j F kind := by
  have metaIff : Sat (S ++ [(.sym kind, F.map ι)]) ↔ ∃ σ : String → Ty Empty, F.bind σ = .sym kind := by
    have := sat_extend_private_iff e injective ι injι S hS freshE F freshF apart ⟨.sym kind, []⟩
    simp only [List.map_nil, List.append_nil, Ty.map_sym, List.nil_append] at this
    rw [this]
    constructor
    · rintro ⟨σ, ρ, hρ⟩
      rw [solves_singleton, Ty.bind_sym, Ty.lift_bind_ground] at hρ
      exact ⟨σ, hρ.symm⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨σ, fun _ => default, (solves_singleton _ _).mpr (by
        rw [Ty.bind_sym, Ty.lift_bind_ground, hσ])⟩
  have hc := card_getType_private e injective ι injι S hS freshE F freshF apart j
  unfold guard guardCountPoly
  by_cases h0 : polyCount j F = 0
  · rw [if_pos (by rw [hc, h0]), if_pos h0]
    by_cases hk : ∃ σ : String → Ty Empty, F.bind σ = .sym kind
    · rw [if_pos hk, Multiset.card_eq_one]
      exact ⟨_, Multiset.filter_eq_self.mpr fun x hx => by
        rw [Multiset.mem_singleton] at hx
        subst hx
        exact metaIff.mpr hk⟩
    · rw [if_neg hk, Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro x hx
      rw [Multiset.mem_singleton] at hx
      subst hx
      exact fun h => hk (metaIff.mp h)
  · rw [if_neg (by rw [hc]; exact h0), if_neg h0]
    exact hc

end Private

/-! ## Functional declarations -/

section Functional

variable {Γ : Decls}

/-- A value typed once at some closed instance of a formal. -/
def PolyHolds (Γ : Decls) (v : Atom) (F : Ty String) : Prop :=
  ∃ σ : String → Ty Empty, count (info Γ v) (F.bind σ) = 1

open Classical in
theorem polyCount_functional (hΓ : Functional Γ) (v : Atom) (F : Ty String) :
    polyCount (info Γ v) F = if PolyHolds Γ v F then 1 else 0 := by
  unfold polyCount PolyHolds
  rw [eff_theDeriv hΓ v, Multiset.filter_singleton]
  have iff : (∃ σ : String → Ty Empty, Sat ((theDeriv hΓ v).eqs ++
      [((theDeriv hΓ v).ty, (F.bind σ).lift)])) ↔ ∃ σ : String → Ty Empty,
      count (info Γ v) (F.bind σ) = 1 := by
    refine exists_congr fun σ => ?_
    rw [count_eq_ite hΓ]
    split_ifs with h <;> simp [h]
  by_cases h : ∃ σ : String → Ty Empty, count (info Γ v) (F.bind σ) = 1
  · rw [if_pos (iff.mpr h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (iff.mp h')), if_neg h]
    rfl

open Classical in
/-- **The guard of a private formal that is an application succeeds once exactly
when the value is typed at some closed instance**, under functional
declarations; the metatype never meets an application. -/
theorem guardCountPoly_functional (hΓ : Functional Γ) (v : Atom) (ts : List (Ty String))
    (kind : String) :
    guardCountPoly (info Γ v) (.app ts) kind = if PolyHolds Γ v (.app ts) then 1 else 0 := by
  have noMeta : ¬ ∃ σ : String → Ty Empty, (Ty.app ts).bind σ = .sym kind := by
    rintro ⟨σ, hσ⟩
    rw [Ty.bind_app] at hσ
    cases hσ
  unfold guardCountPoly
  rw [polyCount_functional hΓ]
  by_cases h : PolyHolds Γ v (.app ts)
  · rw [if_pos h, if_neg one_ne_zero]
  · rw [if_neg h, if_pos rfl, if_neg noMeta]

/-- **Inversion at a private formal**: an application of a constructor typed at
some instance of a named formal gives its checked fields their instances. -/
theorem poly_inversion (hΓ : Functional Γ) {C : String} {As : List (Ty String)} {R : Ty String}
    (row : Γ C = [arrow As R]) (vs : List Atom) (len : vs.length = As.length) (F : Ty String)
    (named : Named F) (h : PolyHolds Γ (.expression (.symbol C :: vs)) F) :
    ∃ σ σ' : String → Ty Empty, R.bind σ' = F.bind σ ∧
      ∀ p ∈ List.zip As vs, ¬ Unchecked p.1 → count (info Γ p.2) (p.1.bind σ') = 1 := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨σ', hσ', fields⟩ := ctor_inversion hΓ row vs len (F.bind σ) (named.bind σ) hσ
  exact ⟨σ, σ', hσ', fields⟩

/-- **A field whose declared type is an instance of the formal meets the formal**:
`(Cons $x $xs)` accepted at `(List $a)` gives `$xs`, declared `(List $a)` in
`Cons`, the fact a call `(len $xs)` needs. -/
theorem polyHolds_of_instance {v : Atom} {B F : Ty String} {σ' : String → Ty Empty}
    (typed : count (info Γ v) (B.bind σ') = 1) (inst : ∃ θ : String → Ty String, B = F.bind θ) :
    PolyHolds Γ v F := by
  obtain ⟨θ, rfl⟩ := inst
  refine ⟨fun x => (θ x).bind σ', ?_⟩
  rw [← Ty.bind_bind]
  exact typed

/-- A value typed at an instance of a formal meets it. -/
theorem polyHolds_of_count {v : Atom} {F : Ty String} {σ : String → Ty Empty}
    (typed : count (info Γ v) (F.bind σ) = 1) : PolyHolds Γ v F := ⟨σ, typed⟩

end Functional

/-! ## Rows with private parameters -/

section Rows

variable (Γ : Decls) (kind : Atom → String)

/-- No two parameters of a row share a type variable. -/
def PrivateParams (As : List (Ty String)) : Prop :=
  As.Pairwise fun A B => ∀ x ∈ A.vars, x ∉ B.vars

/-- The product of the guard counts of a row with private parameters. -/
noncomputable def argCountPoly : List (Ty String) → List Atom → ℕ
  | [], [] => 1
  | A :: As, v :: vs =>
      (if demand A = .guarded then guardCountPoly (info Γ v) A (kind v) else 1) * argCountPoly As vs
  | [], _ :: _ => 0
  | _ :: _, [] => 0

/-- A store of the guards before position `k`: satisfiable, with the derivation
variables of earlier guards and the type variables of earlier parameters. -/
def PrivStore (k : ℕ) (prev : List String) (S : List (Eqn CallVar)) : Prop :=
  Sat S ∧ ∀ u ∈ eqnVars S, (∃ k' d, k' < k ∧ u = .inr (k', d)) ∨ ∃ x ∈ prev, u = .inl x

variable {Γ kind}

theorem PrivStore.freshE {k : ℕ} {prev : List String} {S : List (Eqn CallVar)}
    (h : PrivStore k prev S) : ∀ d, atGuard k d ∉ eqnVars S := by
  intro d hd
  rcases h.2 _ hd with ⟨k', d', hk, he⟩ | ⟨x, -, he⟩
  · simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at he
    omega
  · cases he

theorem PrivStore.freshF {k : ℕ} {prev : List String} {S : List (Eqn CallVar)}
    (h : PrivStore k prev S) {A : Ty String} (disj : ∀ x ∈ A.vars, x ∉ prev) :
    ∀ x ∈ A.vars, (Sum.inl x : CallVar) ∉ eqnVars S := by
  intro x hx hS
  rcases h.2 _ hS with ⟨k', d', -, he⟩ | ⟨y, hy, he⟩
  · cases he
  · simp only [Sum.inl.injEq] at he
    subst he
    exact disj x hx hy

theorem PrivStore.mono {k k' : ℕ} {prev prev' : List String} {S : List (Eqn CallVar)}
    (h : PrivStore k prev S) (hk : k ≤ k') (hp : prev ⊆ prev') : PrivStore k' prev' S :=
  ⟨h.1, fun u hu => by
    rcases h.2 u hu with ⟨j, d, hj, rfl⟩ | ⟨x, hx, rfl⟩
    · exact .inl ⟨j, d, by omega, rfl⟩
    · exact .inr ⟨x, hp hx, rfl⟩⟩

open Classical in
/-- Every continuation of a guard at a private formal is a good store one
position on, with the formal's variables added. -/
theorem guard_private_stores {k : ℕ} {prev : List String} {S : List (Eqn CallVar)}
    (hS : PrivStore k prev S) (A : Ty String) (j : Info) (kindName : String) :
    ∀ S' ∈ guard (atGuard k) S (A.map Sum.inl) j kindName, PrivStore (k + 1) (prev ++ A.vars) S' := by
  intro S' hS'
  have formalVars : ∀ u ∈ (A.map Sum.inl : Ty CallVar).vars, ∃ x ∈ prev ++ A.vars, u = .inl x := by
    intro u hu
    rw [Ty.vars_map, List.mem_map] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, List.mem_append_right _ hx, rfl⟩
  have old : ∀ u ∈ eqnVars S, (∃ k' d, k' < k + 1 ∧ u = .inr (k', d)) ∨ ∃ x ∈ prev ++ A.vars, u = .inl x := by
    intro u hu
    rcases hS.2 u hu with ⟨j', d', hj, rfl⟩ | ⟨x, hx, rfl⟩
    · exact .inl ⟨j', d', by omega, rfl⟩
    · exact .inr ⟨x, List.mem_append_left _ hx, rfl⟩
  unfold guard at hS'
  split_ifs at hS'
  · obtain ⟨hmem, hsat⟩ := Multiset.mem_filter.mp hS'
    rw [Multiset.mem_singleton] at hmem
    subst hmem
    refine ⟨hsat, fun u hu => ?_⟩
    rw [eqnVars_append, List.mem_append] at hu
    rcases hu with hu | hu
    · exact old u hu
    · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Ty.vars_sym, List.nil_append] at hu
      exact .inr (formalVars u hu)
  · unfold getType at hS'
    obtain ⟨hmem, hsat⟩ := Multiset.mem_filter.mp hS'
    obtain ⟨d, -, rfl⟩ := Multiset.mem_map.mp hmem
    refine ⟨hsat, fun u hu => ?_⟩
    rw [eqnVars_append, eqnVars_append, List.mem_append, List.mem_append, eqnVars_map] at hu
    rcases hu with (hu | hu) | hu
    · exact old u hu
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hu
      exact .inl ⟨k, w, by omega, rfl⟩
    · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, Ty.vars_map, List.mem_map] at hu
      rcases hu with ⟨w, -, rfl⟩ | hu
      · exact .inl ⟨k, w, by omega, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := hu
        exact .inr ⟨x, List.mem_append_right _ hx, rfl⟩

/-- The guards of a row with private parameters, followed by any continuation
that ignores a good store, count the continuation once per argument
derivation. -/
theorem guards_private_bind {β : Type} (n : ℕ) (f : List (Eqn CallVar) → Multiset β)
    (t : Multiset β) (hf : ∀ prev S, PrivStore n prev S → f S = t) :
    ∀ (k : ℕ) (As : List (Ty String)) (vs : List Atom) (prev : List String)
      (S : List (Eqn CallVar)), k + As.length ≤ n → PrivateParams As →
      (∀ A ∈ As, ∀ x ∈ A.vars, x ∉ prev) → PrivStore k prev S →
      (guards Γ kind k As vs S).bind f = argCountPoly Γ kind As vs • t
  | k, [], [], prev, S, le, _, _, hS => by
      simp [guards, argCountPoly, hf prev S (hS.mono (by simpa using le) (fun _ h => h)), one_nsmul]
  | k, A :: As, v :: vs, prev, S, le, priv, disj, hS => by
      simp only [List.length_cons] at le
      have privRest : PrivateParams As := (List.pairwise_cons.mp priv).2
      have disjRest : ∀ B ∈ As, ∀ x ∈ B.vars, x ∉ prev ++ A.vars := by
        intro B hB x hx hmem
        rcases List.mem_append.mp hmem with h | h
        · exact disj B (by simp [hB]) x hx h
        · exact (List.pairwise_cons.mp priv).1 B hB x h hx
      simp only [guards, argCountPoly]
      split_ifs with hd
      · rw [Multiset.bind_assoc]
        have each : ∀ S' ∈ guard (atGuard k) S (A.map Sum.inl) (info Γ v) (kind v),
            (guards Γ kind (k + 1) As vs S').bind f = argCountPoly Γ kind As vs • t := fun S' hS' =>
          guards_private_bind n f t hf (k + 1) As vs (prev ++ A.vars) S' (by omega) privRest
            disjRest (guard_private_stores hS A _ _ S' hS')
        rw [Multiset.bind_congr each, bind_const',
          card_guard_private (atGuard k) (atGuard_injective k) Sum.inl Sum.inl_injective S hS.1
            hS.freshE A (hS.freshF fun x hx => disj A (by simp) x hx) (fun _ _ h => by cases h)
            _ _, ← mul_nsmul, Nat.mul_comm]
      · rw [one_mul]
        exact guards_private_bind n f t hf (k + 1) As vs (prev ++ A.vars) S (by omega) privRest
          disjRest (hS.mono (by omega) (List.subset_append_left _ _))
  | _, [], _ :: _, _, _, _, _, _, _ => by simp [guards, argCountPoly]
  | _, _ :: _, [], _, _, _, _, _, _ => by simp [guards, argCountPoly]

theorem resultGuard_private {k : ℕ} {prev : List String} {S : List (Eqn CallVar)}
    (hS : PrivStore k prev S) (R : Ty Empty) (r : Atom) :
    resultGuard Γ kind k R.lift S r =
      (if ResultGuarded R.lift then guardCount (info Γ r) R (kind r) else 1) • {r} := by
  unfold resultGuard
  split_ifs
  · rw [lift_map_inl, Multiset.map_const',
      card_guard_closed (atGuard k) (atGuard_injective k) S hS.freshE hS.1 R _ _,
      Multiset.nsmul_singleton]
  · rw [one_nsmul]

/-- **A row with private parameters and a closed result factors**: the body's bag,
each answer counted by its result guard, the whole counted by the argument
guards. -/
theorem chainCall_private (body : List Atom → Multiset Atom) (As : List (Ty String))
    (R : Ty Empty) (priv : PrivateParams As) (vs : List Atom) :
    chainCall Γ kind body (arrow As R.lift) vs =
      argCountPoly Γ kind As vs • (body vs).bind fun r =>
        (if ResultGuarded R.lift then guardCount (info Γ r) R (kind r) else 1) • {r} := by
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  refine guards_private_bind As.length _ _ (fun prev S hS => ?_) 0 As vs [] [] (by omega) priv
    (by simp) ⟨sat_nil, by simp [eqnVars]⟩
  exact Multiset.bind_congr fun r _ => resultGuard_private hS R r

/-- The protocol of a row with private parameters factors. -/
noncomputable def privateFactored (As : List (Ty String)) (R : Ty Empty) (priv : PrivateParams As) :
    Factored fun B vs => chainCall Γ kind B (arrow As R.lift) vs where
  args := argCountPoly Γ kind As
  result r := if ResultGuarded R.lift then guardCount (info Γ r) R (kind r) else 1
  eq B vs := chainCall_private (Γ := Γ) (kind := kind) B As R priv vs

/-- **The version theorem for rows with private parameters**: on arguments
meeting entry facts that make every guard succeed once, with the result's
facts making its guard succeed once, the version's run is the protocol's. -/
theorem private_version_eq_protocol (As : List (Ty String)) (R : Ty Empty) (priv : PrivateParams As)
    {body : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {Entry : List Atom → Prop} {Res : Atom → Prop}
    (entry : ∀ vs, Entry vs → argCountPoly Γ kind As vs = 1)
    (res : ∀ r, Res r → (if ResultGuarded R.lift then guardCount (info Γ r) R (kind r) else 1) = 1)
    (calls : ∀ o o' : List Atom → Multiset Atom, (∀ ws, Entry ws → o ws = o' ws) →
      (∀ ws, Entry ws → ∀ r ∈ o ws, Res r) → ∀ vs, Entry vs → body o vs = body o' vs)
    (results : ∀ o : List Atom → Multiset Atom, (∀ ws, Entry ws → ∀ r ∈ o ws, Res r) →
      ∀ vs, Entry vs → ∀ r ∈ body o vs, Res r) (n : ℕ) (vs : List Atom) (hvs : Entry vs) :
    factoredRun (fun B vs => chainCall Γ kind B (arrow As R.lift) vs) body n vs =
      versionRun body n vs :=
  (factored_version_eq (privateFactored As R priv) entry res calls results n vs hvs).1

/-! ### Arguments typed by their callee at a private formal -/

/-- The formal of a parameter that is not checked. -/
def uncheckedFormal : Ty String := .sym "%Undefined%"

theorem argCountPoly_drop (pre : List (Ty String)) (F : Ty String) (post : List (Ty String))
    (us : List Atom) (w : Atom) (vs : List Atom) (len : pre.length = us.length) :
    argCountPoly Γ kind (pre ++ F :: post) (us ++ w :: vs) =
      (if demand F = .guarded then guardCountPoly (info Γ w) F (kind w) else 1) *
        argCountPoly Γ kind (pre ++ uncheckedFormal :: post) (us ++ w :: vs) := by
  induction pre generalizing us with
  | nil =>
      cases us with
      | nil =>
          have unchecked : demand uncheckedFormal ≠ .guarded := by decide
          simp only [List.nil_append, argCountPoly, if_neg unchecked, one_mul]
      | cons _ _ => simp at len
  | cons B pre ih =>
      cases us with
      | nil => simp at len
      | cons u us =>
          simp only [List.cons_append, argCountPoly]
          rw [ih us (by simpa using len)]
          ring

theorem privateParams_drop {pre post : List (Ty String)} {F : Ty String}
    (priv : PrivateParams (pre ++ F :: post)) : PrivateParams (pre ++ uncheckedFormal :: post) := by
  unfold PrivateParams at priv ⊢
  rw [List.pairwise_append, List.pairwise_cons] at priv ⊢
  obtain ⟨hpre, ⟨-, hpost⟩, cross⟩ := priv
  refine ⟨hpre, ⟨fun B _ x hx => by simp [uncheckedFormal] at hx, hpost⟩, fun A hA B hB => ?_⟩
  rcases List.mem_cons.mp hB with rfl | hB
  · intro x _ hx
    simp [uncheckedFormal] at hx
  · exact cross A hA B (List.mem_cons_of_mem _ hB)

/-- Under functional declarations a value typed once at some closed instance of a
formal passes the formal's guard once. -/
theorem guardCountPoly_of_polyHolds (hΓ : Functional Γ) {v : Atom} {F : Ty String}
    (h : PolyHolds Γ v F) (kindName : String) : guardCountPoly (info Γ v) F kindName = 1 := by
  unfold guardCountPoly
  rw [polyCount_functional hΓ, if_pos h]
  rfl

/-- **A value typed at an instance of a callee's range is typed at an instance of
the formal it matches**: `F σ = R'`, the variables of `R'` held rigid. -/
theorem polyHolds_of_range {w : Atom} {F R' : Ty String} {σ : String → Ty String}
    (hmatch : F.bind σ = R') (typed : ∃ τ : String → Ty Empty, count (info Γ w) (R'.bind τ) = 1) :
    PolyHolds Γ w F := by
  obtain ⟨τ, hτ⟩ := typed
  refine ⟨fun x => (σ x).bind τ, ?_⟩
  rw [← Ty.bind_bind, hmatch]
  exact hτ

/-- **An argument typed by its callee needs no check at a private formal**
(`petta_machine_argument_typed_by_callee`, private case): on the answers of an
argument each typed once at some closed instance of the formal `F`, a row whose
parameters are private and whose result is closed has the answers, with their
multiplicities, of the same row with that parameter not checked. -/
theorem argument_typed_by_callee_private (hΓ : Functional Γ) (body : List Atom → Multiset Atom)
    (pre post : List (Ty String)) (F : Ty String) (R : Ty Empty)
    (priv : PrivateParams (pre ++ F :: post)) (us vs : List Atom) (len : pre.length = us.length)
    {ws : Multiset Atom} (typed : ∀ w ∈ ws, PolyHolds Γ w F) :
    (ws.bind fun w => chainCall Γ kind body (arrow (pre ++ F :: post) R.lift) (us ++ w :: vs)) =
      ws.bind fun w => chainCall Γ kind body (arrow (pre ++ uncheckedFormal :: post) R.lift)
        (us ++ w :: vs) := by
  refine Multiset.bind_congr fun w hw => ?_
  rw [chainCall_private (Γ := Γ) (kind := kind) body _ R priv,
    chainCall_private (Γ := Γ) (kind := kind) body _ R (privateParams_drop priv),
    argCountPoly_drop pre F post us w vs len, guardCountPoly_of_polyHolds hΓ (typed w hw)]
  split_ifs <;> simp

end Rows

/-! ## Shared variables: a store is a common instance -/

section Shared

/-- The instances of a row's variables that a store allows. -/
def Allows (S : List (Eqn CallVar)) (σ : String → Ty Empty) : Prop :=
  ∃ ρ : CallVar → Ty Empty, Solves ρ S ∧ ∀ x, ρ (.inl x) = σ x

theorem sat_iff_allows (S : List (Eqn CallVar)) : Sat S ↔ ∃ σ, Allows S σ :=
  ⟨fun ⟨ρ, h⟩ => ⟨fun x => ρ (.inl x), ρ, h, fun _ => rfl⟩, fun ⟨_, ρ, h, _⟩ => ⟨ρ, h⟩⟩

open Classical in
/-- **A guard's extension of a store allows the instances the store allowed at
which the derivation meets the formal.** -/
theorem allows_extend (k : ℕ) (S : List (Eqn CallVar)) (fresh : ∀ d, atGuard k d ∉ eqnVars S)
    (d : Deriv) (F : Ty String) (σ : String → Ty Empty) :
    Allows (S ++ d.eqs.map (Eqn.map (atGuard k)) ++ [(d.ty.map (atGuard k), F.map Sum.inl)]) σ ↔
      Allows S σ ∧ Sat (d.eqs ++ [(d.ty, (F.bind σ).lift)]) := by
  constructor
  · rintro ⟨ρ, hρ, hσ⟩
    rw [solves_append, solves_append, solves_singleton] at hρ
    have inl : (fun x => ρ (Sum.inl x)) = σ := funext hσ
    refine ⟨⟨ρ, hρ.1.1, hσ⟩, ρ ∘ atGuard k, (solves_append _ _ _).mpr
      ⟨(solves_map ρ _ _).mp hρ.1.2, ?_⟩⟩
    rw [solves_singleton, Ty.lift_bind_ground]
    have := hρ.2
    rw [Ty.bind_map, Ty.bind_map] at this
    rw [this]
    exact congrArg (fun f => F.bind f) inl
  · rintro ⟨⟨ρS, hρS, hσ⟩, τ, hτ⟩
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hτ
    refine ⟨fun u => if h : ∃ v, atGuard k v = u then τ h.choose else ρS u, ?_, fun x => ?_⟩
    · rw [solves_append, solves_append, solves_singleton]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · refine (solves_congr fun u hu => ?_).mpr hρS
        have h : ¬ ∃ v, atGuard k v = u := fun ⟨v, hv⟩ => fresh v (hv ▸ hu)
        simp [h]
      · rw [solves_map]
        refine (solves_congr fun v _ => ?_).mpr hτ.1
        have h : ∃ w, atGuard k w = atGuard k v := ⟨v, rfl⟩
        simp only [Function.comp, dif_pos h]
        rw [atGuard_injective k h.choose_spec]
      · rw [Ty.bind_map, Ty.bind_map]
        have left : d.ty.bind ((fun u => if h : ∃ v, atGuard k v = u then τ h.choose else ρS u) ∘
            atGuard k) = d.ty.bind τ := by
          refine Ty.bind_congr _ fun v _ => ?_
          have h : ∃ w, atGuard k w = atGuard k v := ⟨v, rfl⟩
          simp only [Function.comp, dif_pos h]
          rw [atGuard_injective k h.choose_spec]
        have right : F.bind ((fun u => if h : ∃ v, atGuard k v = u then τ h.choose else ρS u) ∘
            Sum.inl) = F.bind σ := by
          refine Ty.bind_congr _ fun x _ => ?_
          have h : ¬ ∃ v, atGuard k v = Sum.inl x := fun ⟨v, hv⟩ => by cases hv
          simp only [Function.comp, dif_neg h]
          exact hσ x
        rw [left, right]
        exact hτ.2
    · have h : ¬ ∃ v, atGuard k v = Sum.inl x := fun ⟨v, hv⟩ => by cases hv
      simp only [dif_neg h]
      exact hσ x

/-- A formal that no instance makes a metatype name: an application, or a closed
type that is not one. -/
def NoMeta (F : Ty String) : Prop := ∀ σ : String → Ty Empty, ¬ MetaName (F.bind σ)

theorem noMeta_app (ts : List (Ty String)) : NoMeta (.app ts) := by
  intro σ h
  rw [Ty.bind_app] at h
  rcases h with h | h | h | h <;> cases h

/-- A formal that no instance makes a metatype name is not a bare variable. -/
theorem NoMeta.not_var {F : Ty String} (h : NoMeta F) : ∀ y, F ≠ .var y := by
  rintro y rfl
  exact h (fun _ => .sym "Expression") (.inl rfl)

/-- **The instance of a formal that is not a bare variable has the formal's
demand**: a symbol is its own instance, and an application stays guarded. -/
theorem demand_bind_lift {F : Ty String} (hF : ∀ y, F ≠ .var y) (σ : String → Ty Empty) :
    demand ((F.bind σ).lift : Ty String) = demand F := by
  cases F with
  | var y => exact absurd rfl (hF y)
  | sym s => rfl
  | app ts =>
      obtain ⟨ts', h⟩ : ∃ ts', (((Ty.app ts).bind σ).lift : Ty String) = .app ts' := ⟨_, rfl⟩
      rw [h]
      simp [demand, Unchecked]

/-- A formal the protocol does not guard is a symbol, its own instance. -/
theorem demand_bind_lift_of_not_guarded {F : Ty String} (hF : demand F ≠ .guarded)
    (σ : String → Ty Empty) : demand ((F.bind σ).lift : Ty String) = demand F :=
  demand_bind_lift (fun y h => hF (by subst h; simp [demand, Unchecked])) σ

/-- The metatype branch of a guard never allows an instance of a formal that no
instance makes a metatype name. -/
theorem not_sat_meta {S : List (Eqn CallVar)} {F : Ty String} (hF : NoMeta F)
    (grounded : String → Bool) (v : Atom) :
    ¬ Sat (S ++ [(.sym (metatype grounded v), F.map Sum.inl)]) := by
  rintro ⟨ρ, hρ⟩
  rw [solves_append, solves_singleton, Ty.bind_sym, Ty.bind_map] at hρ
  exact hF (ρ ∘ Sum.inl) (hρ.2 ▸ metaName_metatype grounded v)

/-- Every argument typed once at its formal's instance under `σ`. -/
def AllTyped (Γ : Decls) (As : List (Ty String)) (vs : List Atom) (σ : String → Ty Empty) : Prop :=
  ∀ p ∈ List.zip As vs, count (info Γ p.2) (p.1.bind σ) = 1

/-- No derivation variable of a guard from position `k` on occurs in the store. -/
def FreshFrom (k : ℕ) (S : List (Eqn CallVar)) : Prop :=
  ∀ k' d, k ≤ k' → atGuard k' d ∉ eqnVars S

theorem allows_nil (σ : String → Ty Empty) : Allows [] σ :=
  ⟨fun u => match u with
    | .inl x => σ x
    | .inr _ => default, by simp, fun _ => rfl⟩

open Classical in
/-- A guard at a formal no instance makes a metatype name, under functional
declarations: one continuation, the extended store, exactly when the store
allows an instance at which the value is typed. -/
theorem guard_shared {Γ : Decls} (hΓ : Functional Γ) (grounded : String → Bool) (k : ℕ)
    (S : List (Eqn CallVar)) (fresh : ∀ d, atGuard k d ∉ eqnVars S) (A : Ty String) (hA : NoMeta A)
    (v : Atom) :
    guard (atGuard k) S (A.map Sum.inl) (info Γ v) (metatype grounded v) =
      if ∃ σ, Allows S σ ∧ count (info Γ v) (A.bind σ) = 1 then
        {S ++ (theDeriv hΓ v).eqs.map (Eqn.map (atGuard k)) ++
          [((theDeriv hΓ v).ty.map (atGuard k), A.map Sum.inl)]}
      else 0 := by
  have iff : Sat (S ++ (theDeriv hΓ v).eqs.map (Eqn.map (atGuard k)) ++
      [((theDeriv hΓ v).ty.map (atGuard k), A.map Sum.inl)]) ↔
      ∃ σ, Allows S σ ∧ count (info Γ v) (A.bind σ) = 1 := by
    rw [sat_iff_allows]
    refine exists_congr fun σ => ?_
    rw [allows_extend k S fresh _ A σ, count_eq_ite hΓ]
    split_ifs with h <;> simp [h]
  have gt := getType_of_eff (atGuard k) S (A.map Sum.inl) (eff_theDeriv hΓ v)
  by_cases h : ∃ σ, Allows S σ ∧ count (info Γ v) (A.bind σ) = 1
  · rw [if_pos (iff.mpr h)] at gt
    rw [if_pos h, guard_of_getType _ _ _ _ _ (by rw [gt]; exact Multiset.singleton_ne_zero _), gt]
  · rw [if_neg (fun hs => h (iff.mp hs))] at gt
    rw [if_neg h]
    unfold guard
    rw [gt, Multiset.card_zero, if_pos rfl, Multiset.filter_singleton,
      if_neg (not_sat_meta hA grounded v)]
    rfl

theorem freshFrom_extend {k : ℕ} {S : List (Eqn CallVar)} (h : FreshFrom k S) (d : Deriv)
    (F : Ty String) :
    FreshFrom (k + 1) (S ++ d.eqs.map (Eqn.map (atGuard k)) ++ [(d.ty.map (atGuard k), F.map Sum.inl)]) := by
  intro k' d' hk hmem
  rw [eqnVars_append, eqnVars_append, List.mem_append, List.mem_append, eqnVars_map] at hmem
  rcases hmem with (hmem | hmem) | hmem
  · exact h k' d' (by omega) hmem
  · obtain ⟨w, -, hw⟩ := List.mem_map.mp hmem
    simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at hw
    omega
  · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, Ty.vars_map, List.mem_map] at hmem
    rcases hmem with ⟨w, -, hw⟩ | ⟨x, -, hx⟩
    · simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at hw
      omega
    · cases hx

open Classical in
/-- **The guards of a row are one store, allowing the common instances** at which
every argument is typed, or no store when there is none, under functional
declarations and formals no instance makes a metatype name. -/
theorem guards_shared {Γ : Decls} (hΓ : Functional Γ) (grounded : String → Bool) :
    ∀ (k : ℕ) (As : List (Ty String)) (vs : List Atom) (S : List (Eqn CallVar)),
      As.length = vs.length → (∀ A ∈ As, demand A = .guarded ∧ NoMeta A) → Sat S → FreshFrom k S →
      ∃ S', guards Γ (metatype grounded) k As vs S =
          (if ∃ σ, Allows S σ ∧ AllTyped Γ As vs σ then ({S'} : Multiset (List (Eqn CallVar)))
            else 0) ∧
        (∀ σ, Allows S' σ ↔ Allows S σ ∧ AllTyped Γ As vs σ) ∧ FreshFrom (k + As.length) S'
  | k, [], [], S, _, _, hS, fresh => by
      refine ⟨S, ?_, fun σ => ⟨fun h => ⟨h, by simp [AllTyped]⟩, fun h => h.1⟩, by simpa using fresh⟩
      have : ∃ σ, Allows S σ ∧ AllTyped Γ [] [] σ := by
        obtain ⟨σ, hσ⟩ := (sat_iff_allows S).mp hS
        exact ⟨σ, hσ, by simp [AllTyped]⟩
      rw [if_pos this]
      rfl
  | k, A :: As, v :: vs, S, len, hAs, hS, fresh => by
      obtain ⟨guarded, noMeta⟩ := hAs A (by simp)
      set S₁ := S ++ (theDeriv hΓ v).eqs.map (Eqn.map (atGuard k)) ++
        [((theDeriv hΓ v).ty.map (atGuard k), A.map Sum.inl)] with hS₁
      have allows₁ : ∀ σ, Allows S₁ σ ↔ Allows S σ ∧ count (info Γ v) (A.bind σ) = 1 := by
        intro σ
        rw [hS₁, allows_extend k S (fun d => fresh k d le_rfl) _ A σ, count_eq_ite hΓ]
        split_ifs with h <;> simp [h]
      have zip : ∀ σ, AllTyped Γ (A :: As) (v :: vs) σ ↔
          count (info Γ v) (A.bind σ) = 1 ∧ AllTyped Γ As vs σ := by
        intro σ
        simp only [AllTyped, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
      simp only [guards, guarded, if_true]
      rw [guard_shared hΓ grounded k S (fun d => fresh k d le_rfl) A noMeta v]
      by_cases h : ∃ σ, Allows S σ ∧ count (info Γ v) (A.bind σ) = 1
      · rw [if_pos h, Multiset.singleton_bind]
        have hS₁sat : Sat S₁ := (sat_iff_allows S₁).mpr (by
          obtain ⟨σ, hσ⟩ := h
          exact ⟨σ, (allows₁ σ).mpr hσ⟩)
        obtain ⟨S', hguards, hallows, hfresh⟩ := guards_shared hΓ grounded (k + 1) As vs S₁
          (by simpa using len) (fun B hB => hAs B (by simp [hB])) hS₁sat
          (freshFrom_extend fresh _ A)
        refine ⟨S', ?_, fun σ => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hfresh⟩
        · rw [hguards]
          congr 1
          apply propext
          constructor
          · rintro ⟨σ, hσ, hall⟩
            exact ⟨σ, ((allows₁ σ).mp hσ).1, (zip σ).mpr ⟨((allows₁ σ).mp hσ).2, hall⟩⟩
          · rintro ⟨σ, hσ, hall⟩
            exact ⟨σ, (allows₁ σ).mpr ⟨hσ, ((zip σ).mp hall).1⟩, ((zip σ).mp hall).2⟩
        · rw [hallows, allows₁, zip]
          tauto
      · rw [if_neg h, Multiset.zero_bind]
        refine ⟨[(.sym "a", .sym "b")], ?_, fun σ => ?_, fun k' d _ => by simp [eqnVars, Eqn.vars]⟩
        · rw [if_neg]
          rintro ⟨σ, hσ, hall⟩
          exact h ⟨σ, hσ, ((zip σ).mp hall).1⟩
        · constructor
          · rintro ⟨ρ, hρ, -⟩
            have := (solves_singleton ρ _).mp hρ
            simp at this
          · intro hσ
            exact absurd ⟨σ, hσ.1, ((zip σ).mp hσ.2).1⟩ h
  | _, [], _ :: _, _, len, _, _, _ => by simp at len
  | _, _ :: _, [], _, len, _, _, _ => by simp at len

open Classical in
/-- **A row whose type variables are shared is counted by a common instance**:
under functional declarations, with every parameter guarded and no instance of
a formal or of the result a metatype name, an answer of the body counts once
exactly when one instance of the row's variables types every argument and the
answer, and otherwise not at all. -/
theorem chainCall_shared {Γ : Decls} (hΓ : Functional Γ) (grounded : String → Bool)
    (body : List Atom → Multiset Atom) (As : List (Ty String)) (R : Ty String) (vs : List Atom)
    (len : As.length = vs.length) (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A)
    (hR : ResultGuarded R) (noMetaR : NoMeta R) :
    chainCall Γ (metatype grounded) body (arrow As R) vs =
      (body vs).bind fun r =>
        if ∃ σ, AllTyped Γ As vs σ ∧ count (info Γ r) (R.bind σ) = 1 then {r} else 0 := by
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  obtain ⟨S', hguards, hallows, hfresh⟩ := guards_shared hΓ grounded 0 As vs [] len hAs sat_nil
    (fun _ _ _ h => by simp [eqnVars] at h)
  rw [hguards]
  by_cases cond : ∃ σ, Allows [] σ ∧ AllTyped Γ As vs σ
  · rw [if_pos cond, Multiset.singleton_bind]
    refine Multiset.bind_congr fun r _ => ?_
    unfold resultGuard
    rw [if_pos hR, guard_shared hΓ grounded As.length S' (fun d => hfresh As.length d (by omega)) R
      noMetaR r]
    have iff : (∃ σ, Allows S' σ ∧ count (info Γ r) (R.bind σ) = 1) ↔
        ∃ σ, AllTyped Γ As vs σ ∧ count (info Γ r) (R.bind σ) = 1 := by
      refine exists_congr fun σ => ?_
      rw [hallows]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨allows_nil σ, h.1⟩, h.2⟩⟩
    by_cases h : ∃ σ, AllTyped Γ As vs σ ∧ count (info Γ r) (R.bind σ) = 1
    · rw [if_pos (iff.mpr h), if_pos h, Multiset.map_singleton]
    · rw [if_neg (fun h' => h (iff.mp h')), if_neg h, Multiset.map_zero]
  · rw [if_neg cond, Multiset.zero_bind]
    symm
    rw [Multiset.bind_congr (g := fun _ => 0) fun r _ => if_neg fun ⟨σ, hall, _⟩ =>
      cond ⟨σ, allows_nil σ, hall⟩, Multiset.bind_zero]

/-! ## Facts read at a type with variables -/

/-- **The facts read from a pattern at a type with variables, the variables held
as constants** (`contract_invert` at a private formal): a variable has the type;
an application of a constructor in the class whose declared result matches the
type one way, `R.bind ρ = F`, gives each field that is not free its declared
type under `ρ`. -/
inductive PatFactOpen (Γ : Decls) : Pat → Ty String → String → Ty String → Prop
  | var (x : String) (F : Ty String) : PatFactOpen Γ (.var x) F x F
  | ctor {c : String} {Bs : List (Ty String)} {R : Ty String} {ps : List Pat} {F : Ty String}
      {ρ : String → Ty String} {x : String} {U : Ty String} {B : Ty String} {p : Pat}
      (row : Γ c = [arrow Bs R]) (cls : Constructor Bs R) (len : ps.length = Bs.length)
      (noMeta : NoMeta F) (named : Named F) (hmatch : R.bind ρ = F)
      (field : (B, p) ∈ List.zip Bs ps) (fixed : ¬ FreeField R B)
      (inner : PatFactOpen Γ p (B.bind ρ) x U) : PatFactOpen Γ (.ctor c ps) F x U

/-- **A fact read with the variables as constants holds at every instance**: at
the instance `F σ`, the match `ρ` followed by `σ` matches the declared result, so
the derivation instantiates to the closed one. Refusing a declared result that
names a variable twice is not needed for this. -/
theorem PatFactOpen.instance {Γ : Decls} {p : Pat} {F : Ty String} {x : String} {U : Ty String}
    (h : PatFactOpen Γ p F x U) (σ : String → Ty Empty) : PatFact Γ p (F.bind σ) x (U.bind σ) := by
  induction h with
  | var x F => exact .var x (F.bind σ)
  | @ctor c Bs R ps F ρ x U B p row cls len noMeta named hmatch field fixed inner ih =>
      have assoc : ∀ t : Ty String, (t.bind ρ).bind σ = t.bind fun y => (ρ y).bind σ :=
        fun t => Ty.bind_bind ρ σ t
      refine PatFact.ctor (σ := fun y => (ρ y).bind σ) row cls len (noMeta σ) (named.bind σ) ?_
        field fixed ?_
      · rw [← assoc, hmatch]
      · rw [← assoc]
        exact ih

/-- The facts of an equation's head patterns at formals with variables. -/
def eqFactsOpen (Γ : Decls) (Fs : List (Ty String)) (eq : Equation) (x : String) (U : Ty String) :
    Prop :=
  ∃ F p, (F, p) ∈ List.zip Fs eq.pats ∧ demand F = .guarded ∧ (∀ y, F ≠ .var y) ∧ PatFactOpen Γ p F x U

/-- **Open facts give the facts at every instance** that `AcceptedPriv` reads. -/
theorem eqFactsOpen_instance {Γ : Decls} {Fs : List (Ty String)} {eq : Equation} {x : String}
    {U : Ty String} (h : eqFactsOpen Γ Fs eq x U) (σ : String → Ty Empty) :
    eqFacts Γ (Fs.map fun F => F.bind σ) eq x (U.bind σ) := by
  obtain ⟨F, p, hmem, hg, hnv, hp⟩ := h
  refine ⟨F.bind σ, p, ?_, by rw [demand_bind_lift hnv σ]; exact hg, hp.instance σ⟩
  rw [List.zip_map_left]
  exact List.mem_map.mpr ⟨(F, p), hmem, rfl⟩

/-! ## Instance versions -/

theorem allTyped_of_entryFacts {Γ : Decls} {grounded : String → Bool} {As : List (Ty String)}
    {vs : List Atom} (θ : String → Ty Empty) (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A)
    (hvs : EntryFacts Γ grounded (As.map fun A => A.bind θ) vs) : AllTyped Γ As vs θ := by
  intro p hp
  have each : List.Forall₂
      (fun A v => demand ((A.bind θ).lift : Ty String) = .guarded → Holds Γ grounded v (A.bind θ)) As vs :=
    List.forall₂_map_left_iff.mp hvs
  have hA := hAs p.1 (List.of_mem_zip hp).1
  exact (forall₂_zip each p.1 p.2 hp (by rw [demand_bind_lift hA.2.not_var θ]; exact hA.1)).count (hA.2 θ)

/-- **A version of a closed instance is the signature's protocol at the
instance** (`contract_instance_version`). When the analysis accepts the
equations at the closed instance `θ(S)` of the signature `S`, so that the version
theorem's hypotheses hold there, the run of `S`'s own protocol at every call,
its calls to itself included, has the version's answers at every fuel on
arguments typed once at the instance's formals. Each of `S`'s guards takes fresh
variables at every call; under functional declarations an answer counts once
when one instance types every argument and the answer (`chainCall_shared`), and
the instance `θ` does. -/
theorem instance_version_eq_protocol {Γ : Decls} (hΓ : Functional Γ) {grounded : String → Bool}
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty String)} {R : Ty String} (θ : String → Ty Empty)
    (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A) (hR : ResultGuarded R) (noMetaR : NoMeta R)
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV (As.map fun A => A.bind θ)
      (R.bind θ)) :
    ∀ n vs, EntryFacts Γ grounded (As.map fun A => A.bind θ) vs →
      protocolRun Γ grounded bodyP (arrow As R) n vs = versionRun bodyV n vs
  | 0, _, _ => rfl
  | n + 1, vs, hvs => by
      have len : As.length = vs.length := by simpa using hvs.length_eq
      have typed := allTyped_of_entryFacts θ hAs hvs
      simp only [protocolRun, versionRun]
      rw [chainCall_shared hΓ grounded _ As R vs len hAs hR noMetaR,
        h.calls _ _ (instance_version_eq_protocol hΓ θ hAs hR noMetaR h n) (fun ws hws r hr => by
          rw [instance_version_eq_protocol hΓ θ hAs hR noMetaR h n ws hws] at hr
          exact version_results h n ws hws r hr) vs hvs]
      refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
      · rw [if_pos ⟨θ, typed,
          (h.results _ (version_results h n) vs hvs r hr).count (noMetaR θ)⟩]
      · rw [Multiset.bind_singleton, Multiset.map_id']

/-- **A checked call at the signature enters the instance's version**: `S`'s
argument guards before the entry and `S`'s result guard after the version's
answers give the answers of `S`'s protocol, on arguments typed once at the
instance's formals. -/
theorem instance_checked_call_eq {Γ : Decls} (hΓ : Functional Γ) {grounded : String → Bool}
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty String)} {R : Ty String} (θ : String → Ty Empty)
    (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A) (hR : ResultGuarded R) (noMetaR : NoMeta R)
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV (As.map fun A => A.bind θ)
      (R.bind θ)) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts Γ grounded (As.map fun A => A.bind θ) vs) :
    chainCall Γ (metatype grounded) (bodyP (protocolRun Γ grounded bodyP (arrow As R) n))
        (arrow As R) vs =
      chainCall Γ (metatype grounded) (bodyV (versionRun bodyV n)) (arrow As R) vs := by
  have len : As.length = vs.length := by simpa using hvs.length_eq
  rw [chainCall_shared hΓ grounded _ As R vs len hAs hR noMetaR,
    chainCall_shared hΓ grounded _ As R vs len hAs hR noMetaR,
    h.calls _ _ (instance_version_eq_protocol hΓ θ hAs hR noMetaR h n) (fun ws hws r hr => by
      rw [instance_version_eq_protocol hΓ θ hAs hR noMetaR h n ws hws] at hr
      exact version_results h n ws hws r hr) vs hvs]

/-- **An instance version's answers meet the signature's open result check**
(`petta_open_answer_meet_range` at an instance version): on arguments typed
once at the instance's formals, the checked call at `S`, its result check at the
open range included, answers exactly the version's answers, so that check can be
met without running it. -/
theorem instance_range_met {Γ : Decls} (hΓ : Functional Γ) {grounded : String → Bool}
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty String)} {R : Ty String} (θ : String → Ty Empty)
    (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A) (hR : ResultGuarded R) (noMetaR : NoMeta R)
    (h : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV (As.map fun A => A.bind θ)
      (R.bind θ)) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts Γ grounded (As.map fun A => A.bind θ) vs) :
    chainCall Γ (metatype grounded) (bodyV (versionRun bodyV n)) (arrow As R) vs =
      bodyV (versionRun bodyV n) vs := by
  rw [← instance_checked_call_eq hΓ θ hAs hR noMetaR h n vs hvs]
  exact instance_version_eq_protocol hΓ θ hAs hR noMetaR h (n + 1) vs hvs

/-- **A constant function argument meets its instance** (`contract_fixes_closed`):
a function name whose one declaration is the closed instance `D` of its formal
is typed once at `D`, so a constant parameter's fact is the entry fact of the
instance that `D` fixes. -/
theorem constant_holds {Γ : Decls} {grounded : String → Bool} {f : String} {D : Ty Empty}
    (row : Γ f = [D.lift]) : Holds Γ grounded (.symbol f) D :=
  Holds.of_count (by rw [count_symbol_closed Γ f D row, if_pos rfl])

/-! ### Private formals in the analysis -/

/-- Under functional declarations a value meeting the fact of some instance of a
formal that no instance makes a metatype name passes the formal's guard once. -/
theorem guardCountPoly_of_entry {Γ : Decls} (hΓ : Functional Γ) {grounded : String → Bool} {v : Atom}
    {F : Ty String} (hF : NoMeta F) (h : ∃ τ : String → Ty Empty, Holds Γ grounded v (F.bind τ))
    (kindName : String) : guardCountPoly (info Γ v) F kindName = 1 := by
  obtain ⟨τ, hτ⟩ := h
  have hp : PolyHolds Γ v F := ⟨τ, hτ.count (hF τ)⟩
  unfold guardCountPoly
  rw [polyCount_functional hΓ, if_pos hp]
  simp

theorem argCountPoly_of_entry {Γ : Decls} (hΓ : Functional Γ) {grounded : String → Bool} :
    ∀ {Fs : List (Ty String)} {vs : List Atom}, (∀ F ∈ Fs, NoMeta F) →
      EntryPoly Γ grounded Fs vs → argCountPoly Γ (metatype grounded) Fs vs = 1
  | [], [], _, _ => rfl
  | F :: Fs, v :: vs, noMeta, .cons hv hvs => by
      simp only [argCountPoly]
      rw [argCountPoly_of_entry hΓ (fun F' hF' => noMeta F' (by simp [hF'])) hvs, mul_one]
      split_ifs with hg
      · exact guardCountPoly_of_entry hΓ (noMeta F (by simp)) (hv hg) _
      · rfl

/-- **One instance for all private formals**: arguments meeting facts of some
instance of each formal meet the facts of one instance of all, since no two
formals share a variable. -/
theorem entryPoly_instance {Γ : Decls} {grounded : String → Bool} :
    ∀ {Fs : List (Ty String)} {vs : List Atom}, PrivateParams Fs → EntryPoly Γ grounded Fs vs →
      ∃ σ : String → Ty Empty, EntryFacts Γ grounded (Fs.map fun F => F.bind σ) vs
  | [], [], _, _ => ⟨fun _ => default, .nil⟩
  | F :: Fs, v :: vs, priv, .cons hv hvs => by
      classical
      rw [PrivateParams, List.pairwise_cons] at priv
      obtain ⟨σ', hσ'⟩ := entryPoly_instance priv.2 hvs
      by_cases hg : demand F = .guarded
      swap
      · refine ⟨σ', .cons (fun hg' => absurd (by rwa [demand_bind_lift_of_not_guarded hg σ'] at hg') hg) hσ'⟩
      obtain ⟨τ, hτ⟩ := hv hg
      refine ⟨fun y => if y ∈ F.vars then τ y else σ' y, .cons (fun _ => ?_) ?_⟩
      · show Holds Γ grounded v (F.bind fun y => if y ∈ F.vars then τ y else σ' y)
        rw [show F.bind (fun y => if y ∈ F.vars then τ y else σ' y) = F.bind τ from
          Ty.bind_congr F fun y hy => if_pos hy]
        exact hτ
      · have same : (Fs.map fun F' => F'.bind fun y => if y ∈ F.vars then τ y else σ' y) =
            Fs.map fun F' => F'.bind σ' :=
          List.map_congr_left fun F' hF' => Ty.bind_congr F' fun y hy =>
            if_neg fun hyF => priv.1 F' hF' y hyF hy
        rw [same]
        exact hσ'

/-- **The version of a relation accepted at private formals is its protocol**
(`contract_private_formal`), at every fuel, on arguments typed once at some
instance of each formal: the facts the analysis reads at every instance hold at
the arguments' instance, and every call to itself meets some instance of the
formals, which its guards then pass once. -/
theorem private_accepted_version_eq_protocol {Γ : Decls} (hΓ : Functional Γ) {grounded : String → Bool}
    {res : String → Ty Empty} {ent : String → List (Ty Empty)} {E : Env} {eqs : List Equation}
    {Fs : List (Ty String)} {R : Ty Empty} (priv : PrivateParams Fs) (noMeta : ∀ F ∈ Fs, NoMeta F)
    (rg : ResultGuarded R.lift) (acc : ∀ eq ∈ eqs, AcceptedPriv Γ res ent Fs R eq)
    (hE : EnvOK Γ grounded res E) (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, EntryFacts Γ grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, EntryFacts Γ grounded (ent f) ws → ∀ r ∈ enV f ws, Holds Γ grounded r (res f))
    (n : ℕ) (vs : List Atom) (hvs : EntryPoly Γ grounded Fs vs) :
    factoredRun (fun B vs => chainCall Γ (metatype grounded) B (arrow Fs R.lift) vs)
        (fun o => equationsBody E eqs ⟨o, enP⟩) n vs =
      versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs := by
  refine (factored_version_eq (privateFactored (Γ := Γ) (kind := metatype grounded) Fs R priv)
    (Entry := EntryPoly Γ grounded Fs) (Res := fun r => Holds Γ grounded r R)
    (fun ws hws => argCountPoly_of_entry hΓ noMeta hws)
    (fun r hr => by
      show (if ResultGuarded R.lift then guardCount (info Γ r) R (metatype grounded r) else 1) = 1
      rw [if_pos rg]
      exact hr.guardCount)
    (fun o o' agree oracle ws hws => ?_) (fun o oracle ws hws r hr => ?_) n vs hvs).1
  · obtain ⟨σ, hσ⟩ := entryPoly_instance priv hws
    unfold equationsBody
    refine Multiset.bind_congr fun eq heq => ?_
    split
    · next ρ hm =>
        exact eval_congr hΓ hE ⟨oracle, fun f ws hws r hr => enRes f ws hws r (enAgree f ws hws ▸ hr)⟩
          ⟨agree, enAgree⟩ eq.rhs ρ (eqFacts_sound hΓ (acc eq heq).linear hm hσ) ((acc eq heq).calls σ)
    · rfl
  · obtain ⟨σ, hσ⟩ := entryPoly_instance priv hws
    unfold equationsBody at hr
    obtain ⟨eq, heq, hr⟩ := Multiset.mem_bind.mp hr
    split at hr
    · next ρ hm =>
        exact eval_sound hΓ hE ⟨oracle, enRes⟩ eq.rhs ρ (eqFacts_sound hΓ (acc eq heq).linear hm hσ) R
          ((acc eq heq).result σ) ((acc eq heq).calls σ) r hr
    · exact absurd hr (Multiset.notMem_zero r)

/-- **Every answer of a call with shared variables is typed at an instance of its
range**: its result check admitted it there. -/
theorem chainCall_shared_answers {Γ : Decls} (hΓ : Functional Γ) (grounded : String → Bool)
    (body : List Atom → Multiset Atom) (As : List (Ty String)) (R : Ty String) (vs : List Atom)
    (len : As.length = vs.length) (hAs : ∀ A ∈ As, demand A = .guarded ∧ NoMeta A)
    (hR : ResultGuarded R) (noMetaR : NoMeta R) :
    ∀ w ∈ chainCall Γ (metatype grounded) body (arrow As R) vs,
      ∃ τ : String → Ty Empty, count (info Γ w) (R.bind τ) = 1 := by
  intro w hw
  rw [chainCall_shared hΓ grounded body As R vs len hAs hR noMetaR] at hw
  obtain ⟨r, -, hr⟩ := Multiset.mem_bind.mp hw
  split_ifs at hr with h
  · rw [Multiset.mem_singleton] at hr
    subst hr
    obtain ⟨σ, -, hσ⟩ := h
    exact ⟨σ, hσ⟩
  · exact absurd hr (Multiset.notMem_zero _)

end Shared

/-! ## Uninterpreted arguments -/

section Uninterpreted

variable {Γ : Decls}

mutual
/-- The instance of a value under a substitution of its variables: an argument
as unification leaves it. -/
def substA (θ : String → Atom) : Atom → Atom
  | .var x => θ x
  | .symbol s => .symbol s
  | .grounded g => .grounded g
  | .expression es => .expression (substL θ es)

/-- The instance of a list of values. -/
def substL (θ : String → Atom) : List Atom → List Atom
  | [] => []
  | e :: es => substA θ e :: substL θ es
end

/-- No declared symbol heads the value: its record has no rows. -/
def HeadFree (Γ : Decls) : Atom → Prop
  | .symbol s => Γ s = []
  | _ => True

mutual
/-- **An uninterpreted argument and an instance that keeps its heads free**
(`oem_value_uninterpreted`): no symbol of the value is declared, and the
instance puts no declared symbol at a head position, where a variable heads an
application. -/
def Safe (Γ : Decls) (θ : String → Atom) : Atom → Prop
  | .symbol s => Γ s = []
  | .var _ => True
  | .grounded _ => True
  | .expression [] => True
  | .expression (h :: es) => HeadFree Γ (substA θ h) ∧ Safe Γ θ h ∧ SafeAll Γ θ es

/-- Every element safe. -/
def SafeAll (Γ : Decls) (θ : String → Atom) : List Atom → Prop
  | [] => True
  | e :: es => Safe Γ θ e ∧ SafeAll Γ θ es
end

theorem rows_headFree {a : Atom} (h : HeadFree Γ a) : (info Γ a).rows = [] := by
  cases a with
  | symbol s => exact h
  | var _ => rfl
  | grounded g => cases g <;> rfl
  | expression es =>
      rw [info_expression]
      cases es <;> rfl

theorem headFree_of_safe {θ : String → Atom} {a : Atom} (h : Safe Γ θ a) (ha : ¬ ∃ x, a = .var x) :
    HeadFree Γ a := by
  cases a with
  | symbol s => exact h
  | var x => exact (ha ⟨x, rfl⟩).elim
  | grounded _ => trivial
  | expression _ => trivial

/-- The parts of the one tuple derivation of values with one derivation each. -/
def partsOf : ℕ → List Deriv → List (Ty DVar) × List (Eqn DVar)
  | _, [] => ([], [])
  | i, d :: ds => ((d.push i).ty :: (partsOf (i + 1) ds).1, (d.push i).eqs ++ (partsOf (i + 1) ds).2)

theorem tupleParts_single : ∀ (i : ℕ) (js : List Info) (ds : List Deriv),
    List.Forall₂ (fun j d => eff j = {d}) js ds → tupleParts i js = {partsOf i ds}
  | _, [], [], .nil => rfl
  | i, _ :: js, d :: ds, .cons hj hjs => by
      simp only [tupleParts, hj, Multiset.singleton_bind, tupleParts_single (i + 1) js ds hjs,
        Multiset.map_singleton, partsOf]

theorem partsOf_vars : ∀ (k : ℕ) (ds : List Deriv), ∀ t ∈ (partsOf k ds).1, ∀ u ∈ t.vars,
    ∃ k', k ≤ k' ∧ u.1.head? = some k'
  | _, [], t, ht, _, _ => by simp [partsOf] at ht
  | k, d :: ds, t, ht, u, hu => by
      simp only [partsOf, List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp only [Deriv.push, Ty.vars_map, List.mem_map] at hu
        obtain ⟨u', -, rfl⟩ := hu
        exact ⟨k, le_rfl, rfl⟩
      · obtain ⟨k', hk, h⟩ := partsOf_vars (k + 1) ds t ht u hu
        exact ⟨k', by omega, h⟩

theorem eff_single_cands {j : Info} {d : Deriv} (h : j.cands = {d}) : eff j = {d} := by
  unfold eff
  rw [h, if_neg (by simp)]

/-- An application whose head has no rows has its one tuple derivation. -/
theorem eff_tuple {h : Atom} {es : List Atom} (hh : HeadFree Γ h) {ds : List Deriv}
    (each : List.Forall₂ (fun e d => eff (info Γ e) = {d}) (h :: es) ds) :
    eff (info Γ (.expression (h :: es))) = {⟨.app (partsOf 0 ds).1, (partsOf 0 ds).2⟩} := by
  classical
  have noFun : funTrees (info Γ h) (es.map (info Γ)) = 0 := by
    unfold funTrees
    rw [rows_headFree hh]
    rfl
  apply eff_single_cands
  rw [info_expression, List.map_cons]
  simp only [nodeInfo, noFun, Multiset.card_zero, if_true, tupleTrees]
  rw [tupleParts_single 0 _ ds (by rw [← List.map_cons]; exact List.forall₂_map_left_iff.mpr each)]
  rfl

/-- One derivation for a value, without equations, and one for its instance,
which at every solution of its equations is a closed instance of the value's. -/
def Struct (Γ : Decls) (v r : Atom) : Prop :=
  ∃ dv dr : Deriv, eff (info Γ v) = {dv} ∧ eff (info Γ r) = {dr} ∧ dv.eqs = [] ∧
    ∀ ρ₁ : DVar → Ty Empty, Solves ρ₁ dr.eqs → ∃ ρ₀ : DVar → Ty Empty, dv.ty.bind ρ₀ = dr.ty.bind ρ₁

/-- The list version, for the parts from position `i`. -/
def StructAll (Γ : Decls) (i : ℕ) (vs rs : List Atom) : Prop :=
  ∃ dvs drs : List Deriv, List.Forall₂ (fun e d => eff (info Γ e) = {d}) vs dvs ∧
    List.Forall₂ (fun e d => eff (info Γ e) = {d}) rs drs ∧ (partsOf i dvs).2 = [] ∧
    ∀ ρ₁ : DVar → Ty Empty, Solves ρ₁ (partsOf i drs).2 → ∃ ρ₀ : DVar → Ty Empty,
      (partsOf i dvs).1.map (fun t => t.bind ρ₀) = (partsOf i drs).1.map fun t => t.bind ρ₁

theorem struct_closed {v : Atom} {d : Deriv} (h : eff (info Γ v) = {d}) (eqs : d.eqs = [])
    (closed : ∃ c, d.ty = .sym c) : Struct Γ v v :=
  ⟨d, d, h, h, eqs, fun ρ₁ _ => ⟨ρ₁, by obtain ⟨c, hc⟩ := closed; rw [hc]⟩⟩

mutual
/-- **The structural type of an uninterpreted value instantiates with the value**:
an instance that keeps the heads free has, at every solution of its equations,
a closed instance of the value's type. -/
theorem struct_of_safe (hΓ : Functional Γ) (θ : String → Atom) :
    ∀ v : Atom, Safe Γ θ v → Struct Γ v (substA θ v)
  | .symbol s, h => by
      have : eff (info Γ (.symbol s)) = {undefinedDeriv} := by
        unfold eff
        rw [info_symbol, show Γ s = [] from h]
        simp
      exact struct_closed this rfl ⟨_, rfl⟩
  | .var x, _ => by
      obtain ⟨d', hd'⟩ := Multiset.card_eq_one.mp (card_eff hΓ (θ x))
      refine ⟨⟨.var ([], none), []⟩, d', ?_, hd', rfl, fun ρ₁ _ => ⟨fun _ => d'.ty.bind ρ₁, rfl⟩⟩
      unfold eff
      rw [info_var]
      simp
  | .grounded g, _ => by
      cases g with
      | int n =>
          exact struct_closed (d := classDeriv "Number") (by unfold eff; rw [info_int]; simp) rfl
            ⟨_, rfl⟩
      | string t =>
          exact struct_closed (d := classDeriv "String") (by unfold eff; rw [info_string]; simp) rfl
            ⟨_, rfl⟩
      | bool b =>
          exact struct_closed (d := classDeriv "Bool") (by unfold eff; rw [info_bool]; simp) rfl
            ⟨_, rfl⟩
      | custom a b =>
          have hinfo : info Γ (.grounded (.custom a b)) = ⟨[], 0⟩ := rfl
          exact struct_closed (d := undefinedDeriv) (by unfold eff; rw [hinfo]; simp) rfl ⟨_, rfl⟩
  | .expression [], _ => by
      have : eff (info Γ (.expression [])) = {⟨.app [], []⟩} := by
        apply eff_single_cands
        rw [info_expression]
        rfl
      exact ⟨_, _, this, this, rfl, fun ρ₁ _ => ⟨ρ₁, rfl⟩⟩
  | .expression (h :: es), ⟨hh, hsafe, hall⟩ => by
      obtain ⟨dvs, drs, hvs, hrs, eqs, cond⟩ := structAll_of_safe hΓ θ 0 (h :: es) ⟨hsafe, hall⟩
      have hhv : HeadFree Γ h := by
        cases h with
        | var _ => trivial
        | symbol s => exact hsafe
        | grounded _ => trivial
        | expression _ => trivial
      have hrs' : List.Forall₂ (fun e d => eff (info Γ e) = {d}) (substA θ h :: substL θ es) drs := hrs
      refine ⟨⟨.app (partsOf 0 dvs).1, (partsOf 0 dvs).2⟩, ⟨.app (partsOf 0 drs).1, (partsOf 0 drs).2⟩,
        eff_tuple hhv hvs, eff_tuple hh hrs', eqs, fun ρ₁ hρ₁ => ?_⟩
      obtain ⟨ρ₀, hρ₀⟩ := cond ρ₁ hρ₁
      exact ⟨ρ₀, by simp only [Ty.bind_app]; rw [hρ₀]⟩

/-- The list version. -/
theorem structAll_of_safe (hΓ : Functional Γ) (θ : String → Atom) :
    ∀ (i : ℕ) (vs : List Atom), SafeAll Γ θ vs → StructAll Γ i vs (substL θ vs)
  | _, [], _ => ⟨[], [], .nil, .nil, rfl, fun ρ₁ _ => ⟨fun _ => default, rfl⟩⟩
  | i, v :: vs, ⟨hv, hvs⟩ => by
      classical
      obtain ⟨dv, dr, hve, hre, hdv, condv⟩ := struct_of_safe hΓ θ v hv
      obtain ⟨dvs, drs, hves, hres, eqs, cond⟩ := structAll_of_safe hΓ θ (i + 1) vs hvs
      refine ⟨dv :: dvs, dr :: drs, .cons hve hves, .cons hre hres, ?_, fun ρ₁ hρ₁ => ?_⟩
      · simp [partsOf, Deriv.push, hdv, eqs]
      · simp only [partsOf] at hρ₁
        rw [solves_append] at hρ₁
        obtain ⟨ρ₀', hρ₀'⟩ := condv (ρ₁ ∘ DVar.push i) ((solves_map ρ₁ (DVar.push i) dr.eqs).mp hρ₁.1)
        obtain ⟨ρ₀'', hρ₀''⟩ := cond ρ₁ hρ₁.2
        refine ⟨fun u => if u.1.head? = some i then ρ₀' (u.1.tail, u.2) else ρ₀'' u, ?_⟩
        simp only [partsOf, List.map_cons, List.cons.injEq]
        constructor
        · simp only [Deriv.push, Ty.bind_map]
          rw [show ((fun u : DVar => if u.1.head? = some i then ρ₀' (u.1.tail, u.2) else ρ₀'' u) ∘
              DVar.push i) = ρ₀' from funext fun u => by simp [DVar.push], hρ₀']
        · rw [← hρ₀'']
          refine List.map_congr_left fun t ht => Ty.bind_congr t fun u hu => ?_
          obtain ⟨k', hk, hhead⟩ := partsOf_vars (i + 1) dvs t ht u hu
          rw [if_neg (by rw [hhead]; intro h; cases h; omega)]
end

/-- `(-> $a $a)`: a parameter whose type variable the result shares. -/
abbrev pairRow : Ty String := arrow [.var "a"] (.var "a")

open Classical in
/-- **The pair guard accepts any instance of an uninterpreted argument exactly
once** (`PETTA_CONTRACT_ENTRY_UNINTERPRETED`, `oem_value_uninterpreted`,
`contract_returns_argument`). The argument `v` passes the guard at `$a` with a
fresh copy, which then stands for `v`'s structural type; the answer, `v` as
unification leaves it, `substA θ v`, is typed at an instance of that type, so the
result guard passes once and the call answers it once. The restriction `Safe`
is the one the theorem needs: no declared symbol in `v`, and none placed at a
head position by the instance. -/
theorem pair_once (hΓ : Functional Γ) (kind : Atom → String) {θ : String → Atom} {v : Atom}
    (hv : Safe Γ θ v) :
    chainCall Γ kind (fun _ => {substA θ v}) pairRow [v] = {substA θ v} := by
  obtain ⟨dv, dr, hve, hre, hdv, cond⟩ := struct_of_safe hΓ θ v hv
  have satDr : Sat dr.eqs :=
    eff_sat (cands_sat Γ (substA θ v)) dr (by rw [hre]; exact Multiset.mem_singleton_self _)
  obtain ⟨ρ₁, hρ₁⟩ := satDr
  obtain ⟨ρ₀, hρ₀⟩ := cond ρ₁ hρ₁
  -- the store the argument's guard leaves
  let S₀ : List (Eqn CallVar) := [(dv.ty.map (atGuard 0), .var (.inl "a"))]
  have sat0 : Sat ([] ++ dv.eqs.map (Eqn.map (atGuard 0)) ++
      [(dv.ty.map (atGuard 0), (Ty.var (Sum.inl "a") : Ty CallVar))]) := by
    refine ⟨fun u => match u with
      | .inl _ => dv.ty.bind ρ₀
      | .inr (_, d) => ρ₀ d, ?_⟩
    rw [hdv]
    simp only [List.map_nil, List.nil_append, solves_singleton, Ty.bind_var', Ty.bind_map]
    rfl
  have g0 : guard (atGuard 0) [] ((Ty.var "a" : Ty String).map Sum.inl) (info Γ v) (kind v) = {S₀} := by
    rw [guard_of_getType _ _ _ _ _ (by
        rw [Ty.map_var, getType_of_eff _ _ _ hve, if_pos sat0]
        exact Multiset.singleton_ne_zero _),
      Ty.map_var, getType_of_eff _ _ _ hve, if_pos sat0, hdv]
    rfl
  -- the result guard at the store
  have sat1 : Sat (S₀ ++ dr.eqs.map (Eqn.map (atGuard 1)) ++
      [(dr.ty.map (atGuard 1), (Ty.var (Sum.inl "a") : Ty CallVar))]) := by
    refine ⟨fun u => match u with
      | .inl _ => dr.ty.bind ρ₁
      | .inr (k, d) => if k = 0 then ρ₀ d else ρ₁ d, ?_⟩
    rw [solves_append, solves_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [S₀, solves_singleton, Ty.bind_var', Ty.bind_map]
      rw [← hρ₀]
      rfl
    · rw [solves_map]
      exact hρ₁
    · simp only [solves_singleton, Ty.bind_var', Ty.bind_map]
      rfl
  have g1 : guard (atGuard 1) S₀ ((Ty.var "a" : Ty String).map Sum.inl) (info Γ (substA θ v))
      (kind (substA θ v)) = {S₀ ++ dr.eqs.map (Eqn.map (atGuard 1)) ++
        [(dr.ty.map (atGuard 1), (Ty.var (Sum.inl "a") : Ty CallVar))]} := by
    rw [guard_of_getType _ _ _ _ _ (by
        rw [Ty.map_var, getType_of_eff _ _ _ hre, if_pos sat1]
        exact Multiset.singleton_ne_zero _),
      Ty.map_var, getType_of_eff _ _ _ hre, if_pos sat1]
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  have guarded : demand (Ty.var "a" : Ty String) = .guarded := by decide
  simp only [guards, guarded, if_true, g0, Multiset.singleton_bind, List.length_singleton]
  unfold resultGuard
  rw [if_pos (by decide), g1, Multiset.map_singleton]

/-- **An uninterpreted value** (`oem_value_uninterpreted`): no symbol of it is
declared. -/
abbrev Uninterp (Γ : Decls) (a : Atom) : Prop := Safe Γ Atom.var a

theorem headFree_of_uninterp {a : Atom} (h : Uninterp Γ a) : HeadFree Γ a := by
  cases a with
  | symbol s => exact h
  | var _ => trivial
  | grounded _ => trivial
  | expression _ => trivial

theorem headFree_subst {θ : String → Atom} (hθ : ∀ x, Uninterp Γ (θ x)) :
    ∀ h : Atom, Uninterp Γ h → HeadFree Γ (substA θ h)
  | .var x, _ => headFree_of_uninterp (hθ x)
  | .symbol _, h => h
  | .grounded _, _ => trivial
  | .expression _, _ => trivial

mutual
/-- **Uninterpreted bindings keep the heads free**: an uninterpreted value under a
substitution by uninterpreted values meets the restriction. -/
theorem safe_of_uninterp {θ : String → Atom} (hθ : ∀ x, Uninterp Γ (θ x)) :
    ∀ v : Atom, Uninterp Γ v → Safe Γ θ v
  | .symbol _, h => h
  | .var _, _ => trivial
  | .grounded _, _ => trivial
  | .expression [], _ => trivial
  | .expression (h :: es), ⟨_, hh, hes⟩ =>
      ⟨headFree_subst hθ h hh, safe_of_uninterp hθ h hh, safeAll_of_uninterp hθ es hes⟩

/-- The list version. -/
theorem safeAll_of_uninterp {θ : String → Atom} (hθ : ∀ x, Uninterp Γ (θ x)) :
    ∀ es : List Atom, SafeAll Γ Atom.var es → SafeAll Γ θ es
  | [], _ => trivial
  | e :: es, ⟨he, hes⟩ => ⟨safe_of_uninterp hθ e he, safeAll_of_uninterp hθ es hes⟩
end

/-- **The pair passes every instance of an uninterpreted argument by
uninterpreted bindings exactly once**: the entry fact's run-time check
(`oem_value_uninterpreted`) on the argument, and bindings from uninterpreted
sources, which the analysis must keep, give the restriction. -/
theorem pair_once_uninterp (hΓ : Functional Γ) (kind : Atom → String) {θ : String → Atom}
    {v : Atom} (hv : Uninterp Γ v) (hθ : ∀ x, Uninterp Γ (θ x)) :
    chainCall Γ kind (fun _ => {substA θ v}) pairRow [v] = {substA θ v} :=
  pair_once hΓ kind (safe_of_uninterp hθ v hv)

open Classical in
/-- **The pair guard rejects an instance whose type meets no instance of the
argument's**: when the argument has one derivation, an application without
equations, and no derivation of the answer meets it under any solutions, the
call has no answer. -/
theorem pair_zero (kind : Atom → String) {v r : Atom} {dv : Deriv} (hve : eff (info Γ v) = {dv})
    (hdv : dv.eqs = []) (happ : ∃ ts, dv.ty = .app ts)
    (apart : ∀ d ∈ eff (info Γ r), ∀ ρ₀ ρ₁ : DVar → Ty Empty, dv.ty.bind ρ₀ ≠ d.ty.bind ρ₁) :
    chainCall Γ kind (fun _ => {r}) pairRow [v] = 0 := by
  let S₀ : List (Eqn CallVar) := [(dv.ty.map (atGuard 0), .var (.inl "a"))]
  have sat0 : Sat ([] ++ dv.eqs.map (Eqn.map (atGuard 0)) ++
      [(dv.ty.map (atGuard 0), (Ty.var (Sum.inl "a") : Ty CallVar))]) := by
    refine ⟨fun u => match u with
      | .inl _ => dv.ty.bind fun _ => default
      | .inr (_, _) => default, ?_⟩
    rw [hdv]
    simp only [List.map_nil, List.nil_append, solves_singleton, Ty.bind_var', Ty.bind_map]
    rfl
  have g0 : guard (atGuard 0) [] ((Ty.var "a" : Ty String).map Sum.inl) (info Γ v) (kind v) = {S₀} := by
    rw [guard_of_getType _ _ _ _ _ (by
        rw [Ty.map_var, getType_of_eff _ _ _ hve, if_pos sat0]
        exact Multiset.singleton_ne_zero _),
      Ty.map_var, getType_of_eff _ _ _ hve, if_pos sat0, hdv]
    rfl
  have g1 : guard (atGuard 1) S₀ ((Ty.var "a" : Ty String).map Sum.inl) (info Γ r) (kind r) = 0 := by
    have none : getType (atGuard 1) S₀ (.var (.inl "a")) (info Γ r) = 0 := by
      unfold getType
      rw [Multiset.filter_eq_nil]
      intro E hE ⟨ρ, hρ⟩
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hE
      rw [solves_append, solves_append] at hρ
      have h0 := hρ.1.1
      have h1 := hρ.2
      simp only [S₀, solves_singleton, Ty.bind_var', Ty.bind_map] at h0 h1
      exact apart d hd (ρ ∘ atGuard 0) (ρ ∘ atGuard 1) (h0.trans h1.symm)
    unfold guard
    rw [Ty.map_var, if_pos (by rw [none]; rfl), Multiset.filter_singleton, if_neg]
    · rfl
    · rintro ⟨ρ, hρ⟩
      rw [solves_append] at hρ
      have h0 := hρ.1
      have h2 := hρ.2
      simp only [S₀, solves_singleton, Ty.bind_var', Ty.bind_sym, Ty.bind_map] at h0 h2
      obtain ⟨ts, hts⟩ := happ
      rw [← h0, hts, Ty.bind_app] at h2
      cases h2
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  have guarded : demand (Ty.var "a" : Ty String) = .guarded := by decide
  simp only [guards, guarded, if_true, g0, Multiset.singleton_bind, List.length_singleton]
  unfold resultGuard
  rw [if_pos (by decide), g1, Multiset.map_zero]

mutual
/-- The identity substitution leaves a value as it is. -/
theorem substA_var_self : ∀ v : Atom, substA Atom.var v = v
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es => by rw [substA, substL_var_self es]

theorem substL_var_self : ∀ es : List Atom, substL Atom.var es = es
  | [] => rfl
  | e :: es => by rw [substL, substA_var_self e, substL_var_self es]
end

/-! ### Versions at an uninterpreted parameter -/

/-- Variables a store keeps clear of: the shared type variable `$a` and the
derivation variables of the argument's guard position `k` and the result's `m`. -/
def PairClear (a : String) (k m : ℕ) (X : List (Eqn CallVar)) : Prop :=
  ∀ w ∈ eqnVars X, w ≠ .inl a ∧ (∀ d, w ≠ atGuard k d) ∧ ∀ d, w ≠ atGuard m d

theorem PairClear.append {a : String} {k m : ℕ} {X Y : List (Eqn CallVar)} (hX : PairClear a k m X)
    (hY : PairClear a k m Y) : PairClear a k m (X ++ Y) := fun w hw => by
  rw [eqnVars_append, List.mem_append] at hw
  exact hw.elim (hX w) (hY w)

/-- Stores with and without the equation the guard at `$a` adds, which binds `$a`
to the argument's type `T`. -/
def PairStores (T : Ty DVar) (a : String) (k m : ℕ) (So Sc : List (Eqn CallVar)) : Prop :=
  ∃ S X, So = S ++ [(T.map (atGuard k), .var (.inl a))] ++ X ∧ Sc = S ++ X ∧
    PairClear a k m S ∧ PairClear a k m X

theorem PairStores.append {T : Ty DVar} {a : String} {k m : ℕ} {So Sc : List (Eqn CallVar)}
    (h : PairStores T a k m So Sc) (Y : List (Eqn CallVar)) (hY : PairClear a k m Y) :
    PairStores T a k m (So ++ Y) (Sc ++ Y) := by
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  exact ⟨S, X ++ Y, by simp, by simp, hS, hX.append hY⟩

/-- The equation binding a fresh `$a` changes no satisfiability. -/
theorem PairStores.sat_iff {T : Ty DVar} {a : String} {k m : ℕ} {So Sc : List (Eqn CallVar)}
    (h : PairStores T a k m So Sc) : Sat So ↔ Sat Sc := by
  classical
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  constructor
  · rintro ⟨ρ, hρ⟩
    simp only [solves_append] at hρ
    exact ⟨ρ, (solves_append _ _ _).mpr ⟨hρ.1.1, hρ.2⟩⟩
  · rintro ⟨ρ, hρ⟩
    rw [solves_append] at hρ
    let ρ' : CallVar → Ty Empty := fun w => if w = .inl a then (T.map (atGuard k)).bind ρ else ρ w
    have agree : ∀ w, w ≠ .inl a → ρ' w = ρ w := fun w hw => if_neg hw
    have hT : (T.map (atGuard k)).bind ρ' = (T.map (atGuard k)).bind ρ := by
      refine Ty.bind_congr _ fun w hw => agree w ?_
      rw [Ty.vars_map, List.mem_map] at hw
      obtain ⟨d, -, rfl⟩ := hw
      simp [atGuard]
    refine ⟨ρ', (solves_append _ _ _).mpr ⟨(solves_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩⟩
    · exact (solves_congr fun w hw => agree w (hS w hw).1).mpr hρ.1
    · rw [solves_singleton, hT]
      simp [ρ']
    · exact (solves_congr fun w hw => agree w (hX w hw).1).mpr hρ.2

theorem pairClear_guard_ext {a : String} {k m j : ℕ} (hjk : j ≠ k) (hjm : j ≠ m) (d : Deriv) (A : Ty Empty) :
    PairClear a k m (d.eqs.map (Eqn.map (atGuard j)) ++ [(d.ty.map (atGuard j), A.lift)]) := by
  intro w hw
  rw [eqnVars_append, List.mem_append, eqnVars_map] at hw
  have hat : ∃ d', w = atGuard j d' := by
    rcases hw with hw | hw
    · obtain ⟨d', -, rfl⟩ := List.mem_map.mp hw
      exact ⟨d', rfl⟩
    · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil, Ty.vars_lift,
        Ty.vars_map, List.mem_map] at hw
      obtain ⟨d', -, rfl⟩ := hw
      exact ⟨d', rfl⟩
  obtain ⟨d', rfl⟩ := hat
  refine ⟨by simp [atGuard], fun d'' h => ?_, fun d'' h => ?_⟩
  · simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at h
    exact hjk h.1
  · simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at h
    exact hjm h.1

open Classical in
/-- A closed parameter's guard, at another position, on paired stores answers
paired stores, one for one. -/
theorem guard_closed_pairStores {T : Ty DVar} {a : String} {k m j : ℕ} (hjk : j ≠ k) (hjm : j ≠ m)
    {So Sc : List (Eqn CallVar)} (h : PairStores T a k m So Sc) (A : Ty Empty) (inf : Info) (kn : String) :
    Multiset.Rel (PairStores T a k m) (guard (atGuard j) So A.lift inf kn) (guard (atGuard j) Sc A.lift inf kn) := by
  have rel : Multiset.Rel (PairStores T a k m) (getType (atGuard j) So A.lift inf)
      (getType (atGuard j) Sc A.lift inf) := by
    unfold getType
    rw [Multiset.filter_map, Multiset.filter_map]
    have same : (eff inf).filter (Sat ∘ fun d => So ++ d.eqs.map (Eqn.map (atGuard j)) ++
        [(d.ty.map (atGuard j), A.lift)]) =
        (eff inf).filter (Sat ∘ fun d => Sc ++ d.eqs.map (Eqn.map (atGuard j)) ++
          [(d.ty.map (atGuard j), A.lift)]) :=
      Multiset.filter_congr fun d _ => by
        simp only [Function.comp, List.append_assoc]
        exact (h.append _ (pairClear_guard_ext hjk hjm d A)).sat_iff
    rw [same, Multiset.rel_map]
    refine Multiset.rel_refl_of_refl_on fun d _ => ?_
    simp only [List.append_assoc]
    exact h.append _ (pairClear_guard_ext hjk hjm d A)
  unfold guard
  rw [Multiset.card_eq_card_of_rel rel]
  split_ifs
  · have hY : PairClear a k m [((Ty.sym kn : Ty CallVar), (A.lift : Ty CallVar))] := by
      intro w hw
      simp [eqnVars, Eqn.vars] at hw
    rw [Multiset.filter_singleton, Multiset.filter_singleton]
    by_cases hs : Sat (So ++ [(.sym kn, A.lift)])
    · rw [if_pos hs, if_pos ((h.append _ hY).sat_iff.mp hs)]
      exact .cons (h.append _ hY) .zero
    · rw [if_neg hs, if_neg fun hs' => hs ((h.append _ hY).sat_iff.mpr hs')]
      exact .zero
  · exact rel

/-- So do the guards of closed parameters between the two positions. -/
theorem guards_closed_pairStores {T : Ty DVar} {a : String} {k m : ℕ} (kind : Atom → String) :
    ∀ (j : ℕ) (As : List (Ty Empty)) (vs : List Atom), k < j → j + As.length ≤ m →
      ∀ {So Sc : List (Eqn CallVar)}, PairStores T a k m So Sc →
      Multiset.Rel (PairStores T a k m) (guards Γ kind j (As.map Ty.lift) vs So)
        (guards Γ kind j (As.map Ty.lift) vs Sc)
  | _, [], [], _, _, _, _, h => .cons h .zero
  | j, A :: As, v :: vs, hk, hm, So, Sc, h => by
      simp only [List.map_cons, guards]
      split_ifs
      · exact Multiset.rel_bind (fun _ _ hab => guards_closed_pairStores kind (j + 1) As vs (by omega)
            (by simp at hm; omega) hab)
          (by rw [lift_map_inl]; exact guard_closed_pairStores (by omega) (by simp at hm; omega) h A _ _)
      · exact guards_closed_pairStores kind (j + 1) As vs (by omega) (by simp at hm; omega) h
  | _, [], _ :: _, _, _, _, _, _ => by simp only [List.map_nil, guards]; exact .zero
  | _, _ :: _, [], _, _, _, _, _ => by simp only [List.map_cons, guards]; exact .zero

open Classical in
/-- **The guard at `$a` on an uninterpreted argument** binds `$a` to the argument's
type, once. -/
theorem guard_var_uninterp {a : String} {k : ℕ} {S : List (Eqn CallVar)} (hS : StoreOK k S) {v : Atom}
    {dv : Deriv} (hdv : eff (info Γ v) = {dv}) (hdve : dv.eqs = []) (kn : String) :
    guard (atGuard k) S ((Ty.var a : Ty String).map Sum.inl) (info Γ v) kn =
      {S ++ [(dv.ty.map (atGuard k), .var (.inl a))]} := by
  obtain ⟨ρ, hρ⟩ := hS.1
  have sat : Sat (S ++ dv.eqs.map (Eqn.map (atGuard k)) ++
      [(dv.ty.map (atGuard k), (Ty.var (Sum.inl a) : Ty CallVar))]) := by
    refine ⟨fun w => if w = .inl a then (dv.ty.map (atGuard k)).bind ρ else ρ w, ?_⟩
    rw [hdve, List.map_nil, List.append_nil, solves_append]
    refine ⟨(solves_congr fun w hw => ?_).mpr hρ, ?_⟩
    · obtain ⟨_, _, _, rfl⟩ := hS.2 w hw
      simp
    · rw [solves_singleton]
      simp only [Ty.bind_var', if_true]
      refine Ty.bind_congr _ fun w hw => ?_
      rw [Ty.vars_map, List.mem_map] at hw
      obtain ⟨d, -, rfl⟩ := hw
      simp [atGuard]
  rw [Ty.map_var, guard_of_getType _ _ _ _ _ (by
      rw [getType_of_eff _ _ _ hdv, if_pos sat]
      exact Multiset.singleton_ne_zero _),
    getType_of_eff _ _ _ hdv, if_pos sat, hdve, List.map_nil, List.append_nil]

open Classical in
/-- **The result guard at `$a` passes an instance of the argument once**, on a store
that binds `$a` to the argument's type among the other parameters' equations. -/
theorem pair_result_once (hΓ : Functional Γ) (kind : Atom → String) {a : String} {k m : ℕ} (hkm : k ≠ m)
    {θ : String → Atom} {v : Atom} (hv : Safe Γ θ v) {dv : Deriv} (hdv : eff (info Γ v) = {dv})
    {So Sc : List (Eqn CallVar)} (h : PairStores dv.ty a k m So Sc) (hSc : Sat Sc) :
    resultGuard Γ kind m (.var a) So (substA θ v) = {substA θ v} := by
  obtain ⟨dv', dr, hve, hre, -, cond⟩ := struct_of_safe hΓ θ v hv
  have same : dv' = dv := by
    rw [hdv] at hve
    exact (Multiset.singleton_inj.mp hve).symm
  subst same
  obtain ⟨ρ₁, hρ₁⟩ : Sat dr.eqs :=
    eff_sat (cands_sat Γ (substA θ v)) dr (by rw [hre]; exact Multiset.mem_singleton_self _)
  obtain ⟨ρ₀, hρ₀⟩ := cond ρ₁ hρ₁
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  obtain ⟨ρc, hρc⟩ := hSc
  rw [solves_append] at hρc
  let ρ : CallVar → Ty Empty := fun w => match w with
    | .inl _ => if w = .inl a then dr.ty.bind ρ₁ else ρc w
    | .inr (j, d) => if j = k then ρ₀ d else if j = m then ρ₁ d else ρc w
  have agree : ∀ w, w ≠ .inl a → (∀ d, w ≠ atGuard k d) → (∀ d, w ≠ atGuard m d) → ρ w = ρc w := by
    intro w h1 h2 h3
    rcases w with x | ⟨j, d⟩
    · simp only [ρ, if_neg h1]
    · have hjk : j ≠ k := fun e => h2 d (by rw [e]; rfl)
      have hjm : j ≠ m := fun e => h3 d (by rw [e]; rfl)
      simp only [ρ, if_neg hjk, if_neg hjm]
  have atK : ρ ∘ atGuard k = ρ₀ := funext fun d => by simp [ρ, atGuard]
  have atM : ρ ∘ atGuard m = ρ₁ := funext fun d => by simp [ρ, atGuard, Ne.symm hkm]
  have atA : ρ (.inl a) = dr.ty.bind ρ₁ := by simp [ρ]
  have sat : Sat (S ++ [(dv'.ty.map (atGuard k), .var (.inl a))] ++ X ++ dr.eqs.map (Eqn.map (atGuard m)) ++
      [(dr.ty.map (atGuard m), (Ty.var (Sum.inl a) : Ty CallVar))]) := by
    refine ⟨ρ, ?_⟩
    simp only [solves_append, solves_singleton]
    refine ⟨⟨⟨⟨(solves_congr fun w hw => agree w (hS w hw).1 (hS w hw).2.1 (hS w hw).2.2).mpr hρc.1, ?_⟩,
      (solves_congr fun w hw => agree w (hX w hw).1 (hX w hw).2.1 (hX w hw).2.2).mpr hρc.2⟩, ?_⟩, ?_⟩
    · rw [Ty.bind_map, atK, hρ₀, Ty.bind_var', atA]
    · rw [solves_map, atM]
      exact hρ₁
    · rw [Ty.bind_map, atM, Ty.bind_var', atA]
  unfold resultGuard
  rw [if_pos (by refine ⟨?_, ?_⟩ <;> simp [Unchecked]), Ty.map_var,
    guard_of_getType _ _ _ _ _ (by rw [getType_of_eff _ _ _ hre, if_pos sat]; exact Multiset.singleton_ne_zero _),
    getType_of_eff _ _ _ hre, if_pos sat, Multiset.map_singleton]

/-- The stores the guards of closed parameters leave are as many as their count. -/
theorem card_guards_closed (kind : Atom → String) {k : ℕ} {S : List (Eqn CallVar)} (hS : StoreOK k S)
    (As : List (Ty Empty)) (vs : List Atom) :
    Multiset.card (guards Γ kind k (As.map Ty.lift) vs S) = argCount Γ kind As vs := by
  have h := guards_closed_bind Γ kind (k + As.length) (fun _ => ({()} : Multiset Unit)) {()}
    (fun _ _ => rfl) k As vs S le_rfl hS
  rw [bind_const'] at h
  have h2 := congrArg Multiset.card h
  simpa using h2

open Classical in
/-- **The protocol of a row with an uninterpreted parameter**
(`PETTA_CONTRACT_ENTRY_UNINTERPRETED`): at `(-> A₁ … $a … Aₖ $a)`, every `Aᵢ` closed and
`$a` named nowhere else, on an uninterpreted argument at `$a` and equations whose
answers are instances of it that keep its heads free (`contract_returns_argument`,
the argument as two-way unification leaves it), the protocol is the closed
parameters' count times the equations' answers: the result guard at `$a` passes
each answer once. -/
theorem pair_protocol (hΓ : Functional Γ) (kind : Atom → String) (pre post : List (Ty Empty)) (a : String)
    (body : List Atom → Multiset Atom) (us ws : List Atom) (v : Atom) (len : pre.length = us.length)
    (hv : Uninterp Γ v)
    (inst : ∀ r ∈ body (us ++ v :: ws), ∃ θ : String → Atom, r = substA θ v ∧ Safe Γ θ v) :
    chainCall Γ kind body (arrow (pre.map Ty.lift ++ .var a :: post.map Ty.lift) (.var a)) (us ++ v :: ws) =
      (argCount Γ kind pre us * argCount Γ kind post ws) • body (us ++ v :: ws) := by
  obtain ⟨dv, -, hdv, -, hdve, -⟩ := struct_of_safe hΓ Atom.var v hv
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  rw [guards_append _ 0 _ _ _ _ _ (by simpa using len), Multiset.bind_assoc]
  have hlen : (List.map Ty.lift pre ++ Ty.var a :: List.map Ty.lift post).length =
      pre.length + 1 + post.length := by simp; omega
  rw [hlen]
  have inner : ∀ S, StoreOK pre.length S →
      ((guards Γ kind (0 + (pre.map (Ty.lift : Ty Empty → Ty String)).length) (Ty.var a :: post.map Ty.lift)
        (v :: ws) S).bind
        fun S' => (body (us ++ v :: ws)).bind (resultGuard Γ kind (pre.length + 1 + post.length) (.var a) S')) =
        argCount Γ kind post ws • body (us ++ v :: ws) := by
    intro S hS
    rw [show 0 + (pre.map (Ty.lift : Ty Empty → Ty String)).length = pre.length by simp]
    have guarded : demand (Ty.var a : Ty String) = .guarded := by
      unfold demand
      rw [if_neg (fun h => by cases h), if_neg (show ¬ Unchecked (Ty.var a : Ty String) from fun h => h)]
    simp only [guards, guarded, if_true]
    rw [guard_var_uninterp hS hdv hdve, Multiset.singleton_bind]
    have clearS : PairClear a pre.length (pre.length + 1 + post.length) S := by
      intro w hw
      obtain ⟨j, d, hj, rfl⟩ := hS.2 w hw
      refine ⟨by simp, fun d' h => ?_, fun d' h => ?_⟩ <;>
        · simp only [atGuard, Sum.inr.injEq, Prod.mk.injEq] at h
          omega
    have rel := guards_closed_pairStores (Γ := Γ) (a := a) (k := pre.length)
      (m := pre.length + 1 + post.length) (T := dv.ty) kind (pre.length + 1) post ws (by omega) (by omega)
      (So := S ++ [(dv.ty.map (atGuard pre.length), .var (.inl a))]) (Sc := S)
      ⟨S, [], by simp, by simp, clearS, by simp [PairClear, eqnVars]⟩
    have each : ∀ So ∈ guards Γ kind (pre.length + 1) (post.map Ty.lift) ws
        (S ++ [(dv.ty.map (atGuard pre.length), .var (.inl a))]),
        (body (us ++ v :: ws)).bind (resultGuard Γ kind (pre.length + 1 + post.length) (.var a) So) =
          body (us ++ v :: ws) := by
      intro So hSo
      obtain ⟨Sc, hSc, hp⟩ := Multiset.exists_mem_of_rel_of_mem rel hSo
      have hScOK := guards_closed_stores (Γ := Γ) kind (pre.length + 1) post ws S
        (hS.mono (by omega)) Sc hSc
      calc (body (us ++ v :: ws)).bind (resultGuard Γ kind (pre.length + 1 + post.length) (.var a) So)
          = (body (us ++ v :: ws)).bind fun r => ({r} : Multiset Atom) := Multiset.bind_congr fun r hr => by
            obtain ⟨θ, rfl, hθ⟩ := inst r hr
            exact pair_result_once hΓ kind (by omega) hθ hdv hp hScOK.1
        _ = body (us ++ v :: ws) := by rw [Multiset.bind_singleton, Multiset.map_id']
    rw [Multiset.bind_congr each, bind_const', Multiset.card_eq_card_of_rel rel,
      card_guards_closed kind (hS.mono (by omega)) post ws]
  rw [guards_closed_bind Γ kind pre.length _ _ inner 0 pre us [] (by omega) StoreOK.nil, mul_comm, mul_nsmul]

/-- A protocol reads its equations only at its arguments. -/
theorem chainCall_congr (kind : Atom → String) {body body' : List Atom → Multiset Atom} (τ : Ty String)
    {vs : List Atom} (h : body vs = body' vs) : chainCall Γ kind body τ vs = chainCall Γ kind body' τ vs := by
  unfold chainCall
  rw [h]

mutual
/-- An instance of an uninterpreted value by uninterpreted bindings is uninterpreted. -/
theorem uninterp_substA {θ : String → Atom} (hθ : ∀ x, Uninterp Γ (θ x)) :
    ∀ v : Atom, Uninterp Γ v → Uninterp Γ (substA θ v)
  | .symbol _, h => h
  | .var x, _ => hθ x
  | .grounded _, _ => trivial
  | .expression [], _ => trivial
  | .expression (h :: es), ⟨_, hh, hes⟩ => by
      refine ⟨?_, uninterp_substA hθ h hh, uninterpAll_substL hθ es hes⟩
      exact headFree_subst (θ := Atom.var) (fun x => trivial) _ (uninterp_substA hθ h hh)

/-- The list version. -/
theorem uninterpAll_substL {θ : String → Atom} (hθ : ∀ x, Uninterp Γ (θ x)) :
    ∀ es : List Atom, SafeAll Γ Atom.var es → SafeAll Γ Atom.var (substL θ es)
  | [], _ => trivial
  | e :: es, ⟨he, hes⟩ => ⟨uninterp_substA hθ e he, uninterpAll_substL hθ es hes⟩
end

variable (Γ) (grounded : String → Bool) in
/-- **The entry facts of a row with an uninterpreted parameter**: the closed
parameters' entry facts, and an uninterpreted value between them. -/
def UnintEntry (pre post : List (Ty Empty)) (args : List Atom) : Prop :=
  ∃ us v ws, args = us ++ v :: ws ∧ pre.length = us.length ∧ EntryFacts Γ grounded pre us ∧
    Uninterp Γ v ∧ EntryFacts Γ grounded post ws

variable (Γ) (grounded : String → Bool) in
/-- **The hypotheses of the version at an uninterpreted parameter**
(`contract_returns_argument`, `contract_bind_any`): the equations call themselves
only at such arguments, and, where the calls to themselves answer uninterpreted
values, every answer is an instance of the argument by uninterpreted bindings, the
argument as two-way unification leaves it. -/
structure UnintHyps (bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (pre post : List (Ty Empty)) : Prop where
  calls : ∀ o o' : List Atom → Multiset Atom,
    (∀ ws, UnintEntry Γ grounded pre post ws → o ws = o' ws) →
    (∀ ws, UnintEntry Γ grounded pre post ws → ∀ r ∈ o ws, Uninterp Γ r) →
    ∀ args, UnintEntry Γ grounded pre post args → bodyP o args = bodyV o' args
  results : ∀ o : List Atom → Multiset Atom,
    (∀ ws, UnintEntry Γ grounded pre post ws → ∀ r ∈ o ws, Uninterp Γ r) →
    ∀ us v ws, pre.length = us.length → UnintEntry Γ grounded pre post (us ++ v :: ws) →
      ∀ r ∈ bodyV o (us ++ v :: ws), ∃ θ : String → Atom, r = substA θ v ∧ ∀ x, Uninterp Γ (θ x)

/-- The version's answers at such arguments are uninterpreted. -/
theorem unint_results {grounded : String → Bool} {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {pre post : List (Ty Empty)} (h : UnintHyps Γ grounded bodyP bodyV pre post) :
    ∀ n args, UnintEntry Γ grounded pre post args → ∀ r ∈ versionRun bodyV n args, Uninterp Γ r
  | 0, _, _, r, hr => absurd hr (Multiset.notMem_zero r)
  | n + 1, args, hargs, r, hr => by
      obtain ⟨us, v, ws, rfl, len, hpre, hv, hpost⟩ := hargs
      obtain ⟨θ, rfl, hθ⟩ := h.results _ (unint_results h n) us v ws len
        ⟨us, v, ws, rfl, len, hpre, hv, hpost⟩ r hr
      exact uninterp_substA hθ v hv

/-- **The version at an uninterpreted parameter is the protocol**
(`PETTA_CONTRACT_ENTRY_UNINTERPRETED`): on arguments meeting the entry facts, the run
whose calls to themselves skip the protocol, the guard at `$a` and the result's
included, has at every fuel exactly the answers of the run whose every call runs
it. -/
theorem unint_version_eq_protocol (hΓ : Functional Γ) {grounded : String → Bool}
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {pre post : List (Ty Empty)} (a : String) (h : UnintHyps Γ grounded bodyP bodyV pre post) :
    ∀ n args, UnintEntry Γ grounded pre post args →
      protocolRun Γ grounded bodyP (arrow (pre.map Ty.lift ++ .var a :: post.map Ty.lift) (.var a)) n args =
        versionRun bodyV n args
  | 0, _, _ => rfl
  | n + 1, args, hargs => by
      have ih := unint_version_eq_protocol hΓ a h n
      have agree := h.calls _ _ ih (fun ws hws r hr => by
        rw [ih ws hws] at hr
        exact unint_results h n ws hws r hr) args hargs
      obtain ⟨us, v, ws, rfl, len, hpre, hv, hpost⟩ := hargs
      simp only [protocolRun, versionRun]
      rw [chainCall_congr _ _ agree, pair_protocol hΓ _ pre post a _ us ws v len hv (fun r hr => ?_),
        argCount_of_entryFacts hpre, argCount_of_entryFacts hpost, mul_one, one_nsmul]
      obtain ⟨θ, rfl, hθ⟩ := h.results _ (unint_results h n) us v ws len
        ⟨us, v, ws, rfl, len, hpre, hv, hpost⟩ r hr
      exact ⟨θ, rfl, safe_of_uninterp hθ v hv⟩

/-- **A checked call at the row enters the version**: its guards before the entry
and its result guard after leave the version's answers as they are. -/
theorem unint_checked_call_eq (hΓ : Functional Γ) {grounded : String → Bool}
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {pre post : List (Ty Empty)} (a : String) (h : UnintHyps Γ grounded bodyP bodyV pre post) (n : ℕ)
    (args : List Atom) (hargs : UnintEntry Γ grounded pre post args) :
    chainCall Γ (metatype grounded) (bodyV (versionRun bodyV n))
        (arrow (pre.map Ty.lift ++ .var a :: post.map Ty.lift) (.var a)) args =
      versionRun bodyV (n + 1) args := by
  obtain ⟨us, v, ws, rfl, len, hpre, hv, hpost⟩ := hargs
  rw [pair_protocol hΓ _ pre post a _ us ws v len hv (fun r hr => ?_), argCount_of_entryFacts hpre,
    argCount_of_entryFacts hpost, mul_one, one_nsmul]
  · rfl
  · obtain ⟨θ, rfl, hθ⟩ := h.results _ (unint_results h n) us v ws len
      ⟨us, v, ws, rfl, len, hpre, hv, hpost⟩ r hr
    exact ⟨θ, rfl, safe_of_uninterp hθ v hv⟩

end Uninterpreted

/-! ## A range written as a parameter's type variable, as an owed class -/

section ValueParameterClass

variable {Γ : Decls} {grounded : String → Bool}

/-- **A range written as a parameter's type variable checks once at the
argument's class** (`PREPARED_PURE_VALUE_PARAMETER` as a return class): at
`(-> A₁ … $t … Aₖ $t)` whose closed parameters pass once, on an argument there
that is a value of the class `c`, the protocol is the equations' answers checked
at `c`. -/
theorem checksAt_value_parameter {pre post : List (Ty Empty)} {t c : String} (hc : IsValueClass c)
    {us : List Atom} {v : Atom} {vs : List Atom} (hv : Literal c v) (len : pre.length = us.length)
    (hpre : argCount Γ (metatype grounded) pre us = 1) (hpost : argCount Γ (metatype grounded) post vs = 1) :
    ChecksAt Γ grounded (arrow (pre.map Ty.lift ++ .var t :: post.map Ty.lift) (.var t)) (us ++ v :: vs)
      (.sym c) := by
  intro body
  have rg : ResultGuarded ((Ty.sym c : Ty Empty).lift : Ty String) := by
    rcases hc with rfl | rfl | rfl <;> decide
  rw [value_parameter_protocol_at grounded body pre post t c hc us v vs hv len]
  refine checksAt_closed rg ?_ body
  rw [argCount_append _ _ _ _ _ len]
  simp only [argCount, guardCount_literal grounded hc hv, hpre, hpost, one_mul, ite_self]

end ValueParameterClass

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional sym num str app listOf listNumber consRow
  cons_row cons_constructor count_num_number count_str count_nil string_cell_typed)

/-- `(List $a)`, a formal whose variable is private. -/
abbrev listA : Ty String := listOf (.var "a")

/-- **The guard of `(: len (-> (List $a) Number))`**: `(Cons 1 (Cons "x" Nil))` has
no instance of `(List $a)`, `(Cons "x" Nil)` and `Nil` have one, so the guard
fails once and passes once. -/
theorem len_guard (grounded : String → Bool) :
    guardCountPoly (info decls (app "Cons" [num 1, app "Cons" [str "x", sym "Nil"]])) listA
        (metatype grounded (app "Cons" [num 1, app "Cons" [str "x", sym "Nil"]])) = 0 ∧
      guardCountPoly (info decls (app "Cons" [str "x", sym "Nil"])) listA
        (metatype grounded (app "Cons" [str "x", sym "Nil"])) = 1 ∧
      guardCountPoly (info decls (sym "Nil")) listA (metatype grounded (sym "Nil")) = 1 := by
  have formal : listA = Ty.app [.sym "List", .var "a"] := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [formal, guardCountPoly_functional decls_functional, if_neg]
    rintro ⟨σ, hσ⟩
    obtain ⟨σ₁, hσ₁, fields⟩ := ctor_inversion decls_functional cons_row _ rfl _
      (by simp [Named]) hσ
    have a₁ : σ₁ "a" = σ "a" := by simpa [listOf] using hσ₁
    have head := fields (.var "a", num 1) (by simp) (by simp [Unchecked])
    rw [Ty.bind_var', a₁] at head
    have rest := fields (listOf (.var "a"), app "Cons" [str "x", sym "Nil"]) (by simp)
      (by simp [Unchecked, listOf])
    obtain ⟨σ₂, hσ₂, fields₂⟩ := ctor_inversion decls_functional cons_row _ rfl _
      (by simp [Named, listOf]) rest
    have a₂ : σ₂ "a" = σ₁ "a" := by simpa [listOf] using hσ₂
    have elem := fields₂ (.var "a", str "x") (by simp) (by simp [Unchecked])
    rw [Ty.bind_var', a₂, a₁, count_str] at elem
    have isString : σ "a" = .sym "String" := by
      by_contra h
      rw [if_neg h] at elem
      cases elem
    rw [isString] at head
    have := count_num_number 1
    -- `1` is typed `Number`, not `String`
    have numCount : count (info decls (num 1)) (.sym "String") = 0 := by
      have h := count_class decls (g := .int 1) (c := "Number") rfl (.sym "String")
      simpa using h
    rw [numCount] at head
    cases head
  · rw [formal, guardCountPoly_functional decls_functional, if_pos]
    exact ⟨fun _ => .sym "String", by simpa [listOf] using string_cell_typed "x"⟩
  · rw [formal, guardCountPoly_functional decls_functional, if_pos]
    exact ⟨fun _ => .sym "Number", by simpa [listOf] using count_nil (.sym "Number")⟩

/-- `(-> Number (List $a) (List $a))`: the result shares `$a` with a parameter. -/
abbrev sharedRow : Ty String := arrow [.sym "Number", listA] listA

/-- `(Cons 5 Nil)`. -/
abbrev cons5 : Atom := app "Cons" [num 5, sym "Nil"]

theorem sharedRow_hyps : ∀ A ∈ [Ty.sym "Number", listA], demand A = .guarded ∧ NoMeta A := by
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl
  · exact ⟨by decide, fun σ => by simp [MetaName]⟩
  · exact ⟨by decide, noMeta_app _⟩

/-- **`Nil` leaves the shared variable free**: with the arguments `1` and `Nil`, a
body answering `(Cons 5 Nil)` answers it once, `$a` met at `Number`. -/
theorem shared_nil (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {cons5}) sharedRow [num 1, sym "Nil"] = {cons5} := by
  classical
  rw [show sharedRow = arrow [.sym "Number", listA] (.app [.sym "List", .var "a"]) from rfl,
    chainCall_shared decls_functional grounded _ _ _ _ rfl sharedRow_hyps (by decide)
    (noMeta_app _), Multiset.singleton_bind, if_pos]
  refine ⟨fun _ => .sym "Number", fun p hp => ?_, ?_⟩
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · exact count_num_number 1
    · simpa [listA, listOf] using count_nil (.sym "Number")
  · simpa [listA, listOf] using TypedCalls.Controls.cons_five_typed

/-- **A list of strings fixes the shared variable at `String`**, and the same
answer `(Cons 5 Nil)` then has no count. -/
theorem shared_strings (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {cons5}) sharedRow
      [num 1, app "Cons" [str "x", sym "Nil"]] = 0 := by
  classical
  rw [show sharedRow = arrow [.sym "Number", listA] (.app [.sym "List", .var "a"]) from rfl,
    chainCall_shared decls_functional grounded _ _ _ _ rfl sharedRow_hyps (by decide)
    (noMeta_app _), Multiset.singleton_bind, if_neg]
  rintro ⟨σ, hall, hres⟩
  have arg := hall (listA, app "Cons" [str "x", sym "Nil"]) (by simp)
  obtain ⟨σ₁, hσ₁, fields⟩ := ctor_inversion decls_functional cons_row _ rfl _
    (by simp [Named, listA, listOf]) arg
  have a₁ : σ₁ "a" = σ "a" := by simpa [listA, listOf] using hσ₁
  have elem := fields (.var "a", str "x") (by simp) (by simp [Unchecked])
  rw [Ty.bind_var', a₁, count_str] at elem
  have isString : σ "a" = .sym "String" := by
    by_contra h
    rw [if_neg h] at elem
    cases elem
  obtain ⟨σ₂, hσ₂, fields₂⟩ := ctor_inversion decls_functional cons_row _ rfl _
    (by simp [Named]) hres
  have a₂ : σ₂ "a" = σ "a" := by simpa [listA, listOf] using hσ₂
  have five := fields₂ (.var "a", num 5) (by simp) (by simp [Unchecked])
  rw [Ty.bind_var', a₂, isString] at five
  have numCount : count (info decls (num 5)) (.sym "String") = 0 := by
    have h := count_class decls (g := .int 5) (c := "Number") rfl (.sym "String")
    simpa using h
  rw [numCount] at five
  cases five

/-! ### An instance version -/

/-- `(= (build $n $acc) (if (> $n 0) (build (- $n 1) (Cons $n $acc)) $acc))` for
`(: build (-> Number (List $a) (List $a)))`: the body fixes `$a` at `Number`. -/
def buildCell : Equation :=
  ⟨[.var "n", .var "acc"],
    .ifE (.prim ">" [.var "n", .const (num 0)])
      (.self [.prim "-" [.var "n", .const (num 1)], .ctor "Cons" [.var "n", .var "acc"]])
      (.var "acc")⟩

/-- `build`'s equations. -/
def buildEqs : List Equation := [buildCell]

/-- `build`'s equations, with no callee. -/
abbrev buildBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env buildEqs ⟨o, noCallee⟩

/-- The instance `$a := Number`. -/
def atNumber : String → Ty Empty := fun _ => .sym "Number"

/-- **`build` is accepted at the instance `(-> Number (List Number) (List Number))`**:
`(Cons $n $acc)` is a list of numbers and the call to itself meets the instance. -/
theorem build_accepted :
    ∀ eq ∈ buildEqs, Accepted decls noRes noEnt
      ([Ty.sym "Number", listA].map fun A => A.bind atNumber) (listA.bind atNumber) eq := by
  intro eq heq
  simp only [buildEqs, List.mem_singleton] at heq
  subst heq
  have factN : eqFacts decls ([Ty.sym "Number", listA].map fun A => A.bind atNumber)
      buildCell "n" (.sym "Number") :=
    ⟨.sym "Number", .var "n", by simp [buildCell], by decide, .var _ _⟩
  have factAcc : eqFacts decls ([Ty.sym "Number", listA].map fun A => A.bind atNumber)
      buildCell "acc" listNumber :=
    ⟨listNumber, .var "acc", by simp [buildCell, atNumber, listA, listOf, listNumber], by decide, .var _ _⟩
  have cell : HasType decls noRes (eqFacts decls ([Ty.sym "Number", listA].map fun A => A.bind atNumber)
      buildCell) (listA.bind atNumber)
      (.ctor "Cons" [.var "n", .var "acc"]) listNumber := by
    have := HasType.ctor (Γ := decls) (res := noRes) (R := listA.bind atNumber)
      (Φ := eqFacts decls ([Ty.sym "Number", listA].map fun A => A.bind atNumber)
        buildCell)
      (σ := atNumber) (args := [.var "n", .var "acc"]) cons_row cons_constructor rfl
      (fun q hq _ => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hq
        rcases hq with rfl | rfl <;> simp [MetaName, atNumber, listOf])
      (fun q hq _ => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hq
        rcases hq with rfl | rfl
        · exact .var factN
        · exact .var (by simpa [atNumber, listOf, listNumber] using factAcc))
    simpa [atNumber, listOf, listNumber] using this
  refine ⟨by simp [buildCell, Pat.varsAll, Pat.vars], rfl, ?_, ?_⟩
  · refine .ifE (.prim fun e he => ?_) (CallsOK.selfClosed (fun e he => ?_) ?_) .var
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact .var
      · exact .const
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · refine .prim fun e he => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact .var
        · exact .const
      · refine .ctor fun e he => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> exact .var
    · exact .cons (.prim rfl) (.cons (by simpa [atNumber, listA, listOf, listNumber] using cell) .nil)
  · exact .ifE .self (.var (by simpa [atNumber, listA, listOf, listNumber] using factAcc))

/-- **`build`'s instance version is its signature's protocol**, at every fuel, on a
number and a list of numbers. -/
theorem build_version (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : EntryFacts decls grounded ([Ty.sym "Number", listA].map fun A => A.bind atNumber) vs) :
    protocolRun decls grounded buildBody (arrow [.sym "Number", listA] listA) n vs =
      versionRun buildBody n vs :=
  instance_version_eq_protocol decls_functional atNumber sharedRow_hyps (by decide) (noMeta_app _)
    (accepted_versionHyps decls_functional (by decide)
      build_accepted (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
      (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))) n vs hvs

/-- `build` counts down: `(build 2 Nil)` is `(Cons 1 (Cons 2 Nil))`. -/
theorem build_answers :
    versionRun buildBody 3 [num 2, sym "Nil"] = {app "Cons" [num 1, app "Cons" [num 2, sym "Nil"]]} := by
  decide

/-- `(Cons "a" Nil)`. -/
abbrev cellA : Atom := app "Cons" [str "a", sym "Nil"]

/-- **Off the instance the version may not be entered**: `(Cons "a" Nil)` is not a
list of numbers, so `(build 0 (Cons "a" Nil))` misses the instance's entry fact;
the signature's protocol answers it, at `$a := String`, while the instance's
protocol answers nothing. -/
theorem build_off_instance (grounded : String → Bool) :
    count (info decls cellA) listNumber = 0 ∧
      protocolRun decls grounded buildBody (arrow [.sym "Number", listA] listA) 1 [num 0, cellA] =
        {cellA} ∧
      protocolRun decls grounded buildBody
        (arrow ([Ty.sym "Number", listNumber].map Ty.lift) listNumber.lift) 1 [num 0, cellA] = 0 := by
  classical
  have untyped : count (info decls cellA) listNumber = 0 := by
    have le := count_le_one decls_functional cellA listNumber
    by_contra ne
    have one : count (info decls cellA) listNumber = 1 := by omega
    obtain ⟨σ, hσ, fields⟩ := ctor_inversion decls_functional cons_row _ rfl _
      (by simp [Named, listNumber, listOf]) one
    have a : σ "a" = .sym "Number" := by simpa [listOf, listNumber] using hσ
    have elem := fields (.var "a", str "a") (by simp) (by simp [Unchecked])
    rw [Ty.bind_var', a, count_str] at elem
    simp at elem
  have body : ∀ o, buildBody o [num 0, cellA] = {cellA} := fun o => rfl
  refine ⟨untyped, ?_, ?_⟩
  · simp only [protocolRun]
    rw [show (arrow [.sym "Number", listA] listA : Ty String) =
        arrow [.sym "Number", listA] (.app [.sym "List", .var "a"]) from rfl,
      chainCall_shared decls_functional grounded _ _ _ _ rfl sharedRow_hyps (by decide)
      (noMeta_app _), body, Multiset.singleton_bind, if_pos]
    refine ⟨fun _ => .sym "String", fun p hp => ?_, by simpa [listOf] using string_cell_typed "a"⟩
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · exact count_num_number 0
    · simpa [listOf] using string_cell_typed "a"
  · simp only [protocolRun]
    rw [chainCall_closed]
    have notMeta : ¬ MetaName listNumber := by simp [MetaName, listNumber, listOf]
    have guardedList : demand ((listNumber : Ty Empty).lift) = .guarded := by
      simp [demand, listNumber, listOf, Ty.lift, Unchecked]
    simp only [argCount, guardedList, if_true, guardCount_of_not_meta notMeta, untyped,
      zero_mul, mul_zero, zero_nsmul]

/-! ### A constant function parameter -/

/-- `(-> $a $a)`, the formal of a function parameter. -/
abbrev arrowA : Ty String := arrow [.var "a"] (.var "a")

/-- `(= (fold-with $f Nil) 0)` and `(= (fold-with $f (Cons $x $xs)) (+ 1 (fold-with $f
$xs)))` for `(: fold-with (-> (-> $a $a) (List $a) Number))`, called with `inc`
at every call: `inc`'s declaration fixes `$a` at `Number`. -/
def foldEqs : List Equation :=
  [⟨[.var "f", .const (sym "Nil")], .const (num 0)⟩,
   ⟨[.var "f", .ctor "Cons" [.var "x", .var "xs"]],
     .prim "+" [.const (num 1), .self [.var "f", .var "xs"]]⟩]

theorem fold_accepted :
    ∀ eq ∈ foldEqs, Accepted decls noRes noEnt
      ([arrowA, listA].map fun A => A.bind atNumber) (Ty.sym "Number") eq := by
  intro eq heq
  simp only [foldEqs, List.mem_cons, List.not_mem_nil, or_false] at heq
  rcases heq with rfl | rfl
  · exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, .const, .const (count_int decls 0)⟩
  · refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, .prim fun e he => ?_, .prim rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .const
    · refine CallsOK.selfClosed (fun e he => ?_) (.cons (.var ⟨_, .var "f", by simp, by decide, .var _ _⟩)
        (.cons (.var ⟨listNumber, .ctor "Cons" [.var "x", .var "xs"],
          by simp [atNumber, listA, listOf, listNumber], by decide, xs_fact⟩) .nil))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .var

/-- `fold-with`'s equations, with no callee. -/
abbrev foldBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env foldEqs ⟨o, noCallee⟩

/-- **A constant parameter's version is the signature's protocol**
(`contract_fixes_closed`): `inc` meets the instance `(-> Number Number)` that its
declaration fixes (`constant_holds`), so on `inc` and a list of numbers the
version of `(-> (-> Number Number) (List Number) Number)` has the answers of
`fold-with`'s own protocol at every fuel. -/
theorem fold_version (grounded : String → Bool) (n : ℕ) (xs : Atom)
    (hxs : Holds decls grounded xs listNumber) :
    protocolRun decls grounded foldBody (arrow [arrowA, listA] (.sym "Number")) n [sym "inc", xs] =
      versionRun foldBody n [sym "inc", xs] :=
  instance_version_eq_protocol decls_functional atNumber
    (fun A hA => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact ⟨by decide, noMeta_app _⟩
      · exact ⟨by decide, noMeta_app _⟩)
    (by decide) (fun σ => by simp [MetaName])
    (accepted_versionHyps decls_functional (by decide) fold_accepted (env_ok grounded noRes)
      noCallee noCallee (fun _ _ _ => rfl) (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r)))
    n [sym "inc", xs]
    (.cons (fun _ => constant_holds (by simp [decls]; rfl)) (.cons (fun _ => hxs) .nil))

/-! ### A private formal -/

/-- The fact a fold reads for `$xs` from `(Cons $x $xs)` at the list type of any
element type. -/
theorem xs_fact_at (τ : Ty Empty) :
    PatFact decls (.ctor "Cons" [.var "x", .var "xs"]) (listOf τ) "xs" (listOf τ) := by
  have inst : ((listOf (Ty.var "a") : Ty String).bind fun _ => τ) = listOf τ := by simp [listOf]
  refine PatFact.ctor (σ := fun _ => τ) (B := listOf (.var "a")) (p := .var "xs")
    cons_row cons_constructor rfl (by simp [MetaName, listOf]) (by simp [Named, listOf]) inst
    (by simp) (by simp [FreeField, listOf]) ?_
  rw [inst]
  exact PatFact.var _ _

/-- `(= (len Nil) 0)` and `(= (len (Cons $x $xs)) (+ 1 (len $xs)))` for
`(: len (-> (List $a) Number))`. -/
def lenEqs : List Equation :=
  [⟨[.const (sym "Nil")], .const (num 0)⟩,
   ⟨[.ctor "Cons" [.var "x", .var "xs"]], .prim "+" [.const (num 1), .self [.var "xs"]]⟩]

/-- **`len` is accepted at its private formal**: at every instance `(List τ)` of
the formal, `$xs` is a `(List τ)` and the call to itself meets the formal there. -/
theorem len_accepted : ∀ eq ∈ lenEqs, AcceptedPriv decls noRes noEnt [listA] (.sym "Number") eq := by
  intro eq heq
  simp only [lenEqs, List.mem_cons, List.not_mem_nil, or_false] at heq
  rcases heq with rfl | rfl
  · exact ⟨by simp [Pat.varsAll, Pat.vars], rfl, fun _ => .const,
      fun _ => .const (count_int decls 0)⟩
  · refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, fun σ => .prim fun e he => ?_, fun _ => .prim rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .const
    · refine .self (fun e he => ?_) (.cons (fun _ => ⟨σ, .var ⟨listA.bind σ, .ctor "Cons" [.var "x", .var "xs"],
        by simp, by rw [demand_bind_lift (F := listA) (noMeta_app _).not_var σ]; decide,
        xs_fact_at (σ "a")⟩⟩) .nil)
      rw [List.mem_singleton] at he
      subst he
      exact .var

/-- **`len`'s fact read with `$a` held as a constant**: `(Cons $x $xs)` at
`(List $a)` gives `$xs` the open type `(List $a)`, which at every instance is
the fact `len_accepted` reads. -/
theorem len_open_fact :
    eqFactsOpen decls [listA] (lenEqs.getLast (by simp [lenEqs])) "xs" listA ∧
      ∀ σ : String → Ty Empty, eqFacts decls ([listA].map fun F => F.bind σ)
        (lenEqs.getLast (by simp [lenEqs])) "xs" (listA.bind σ) := by
  have h : eqFactsOpen decls [listA] (lenEqs.getLast (by simp [lenEqs])) "xs" listA :=
    ⟨listA, .ctor "Cons" [.var "x", .var "xs"], by simp [lenEqs], by decide, (noMeta_app _).not_var,
      .ctor (ρ := fun _ => .var "a") (B := listOf (.var "a")) (p := .var "xs") cons_row cons_constructor
        rfl (noMeta_app _) (by simp [Named, listA, listOf]) (by simp [listA, listOf]) (by simp)
        (by simp [FreeField, listOf]) (by simpa [listA, listOf] using PatFactOpen.var "xs" listA)⟩
  exact ⟨h, eqFactsOpen_instance h⟩

/-- `len`'s equations, with no callee. -/
abbrev lenBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody env lenEqs ⟨o, noCallee⟩

/-- **`len`'s version is its protocol** at every fuel, on any list typed at some
instance of `(List $a)`. -/
theorem len_version (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : EntryPoly decls grounded [listA] vs) :
    factoredRun (fun B vs => chainCall decls (metatype grounded) B
        (arrow [listA] (Ty.sym "Number" : Ty Empty).lift) vs) lenBody n vs =
      versionRun lenBody n vs :=
  private_accepted_version_eq_protocol decls_functional (by simp [PrivateParams])
    (fun F hF => by
      rw [List.mem_singleton] at hF
      subst hF
      exact noMeta_app _)
    number_guarded len_accepted (env_ok grounded noRes) noCallee noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r)) n vs hvs

/-- **Any instance**: a list of strings meets `len`'s entry fact, at `$a := String`,
and the version counts it. -/
theorem len_strings (grounded : String → Bool) :
    EntryPoly decls grounded [listA] [app "Cons" [str "x", sym "Nil"]] ∧
      versionRun lenBody 2 [app "Cons" [str "x", sym "Nil"]] = {num 1} :=
  ⟨.cons (fun _ => ⟨fun _ => .sym "String", Holds.of_count (by simpa [listA, listOf] using string_cell_typed "x")⟩)
    .nil, by decide⟩

/-! ### Uninterpreted arguments -/

/-- `($g 1)`: an uninterpreted argument whose head is a variable. -/
abbrev gOne : Atom := .expression [.var "g", num 1]

theorem eff_gOne : eff (info decls gOne) = {⟨.app [.var ([0], none), .sym "Number"], []⟩} := by
  rw [eff_tuple (Γ := decls) (h := .var "g") (es := [num 1]) trivial
    (ds := [⟨.var ([], none), []⟩, classDeriv "Number"])
    (.cons (by unfold eff; rw [info_var]; simp) (.cons (by unfold eff; rw [info_int]; simp) .nil))]
  rfl

theorem eff_incOne : ∃ E, eff (info decls (.expression [sym "inc", num 1])) = {⟨.sym "Number", E⟩} := by
  classical
  have row : decls "inc" = [arrow [.sym "Number"] (.sym "Number")] := by simp [decls]
  have args : argEqs 1 [.sym "Number"] [info decls (num 1)] =
      {ctorEqs 1 [.sym "Number"] [classDeriv "Number"]} :=
    argEqs_singletons 1 _ _ _ rfl (.cons (by unfold eff; rw [info_int]; simp) .nil)
  have sat : Sat (ctorEqs 1 [.sym "Number"] [classDeriv "Number"]) :=
    ⟨fun _ => default, fun e he => by
      simp [ctorEqs, Unchecked, classDeriv, Deriv.push] at he
      subst he
      rfl⟩
  have funT : funTrees (info decls (sym "inc")) [info decls (num 1)] =
      {⟨(Ty.sym "Number").map DVar.own, ctorEqs 1 [.sym "Number"] [classDeriv "Number"]⟩} := by
    rw [info_symbol, row, funTrees_arrow _ _ _ _ rfl, args, Multiset.map_singleton,
      Multiset.filter_singleton, if_pos sat]
  refine ⟨ctorEqs 1 [.sym "Number"] [classDeriv "Number"], eff_single_cands ?_⟩
  rw [info_expression]
  simp only [List.map_cons, List.map_nil, nodeInfo, funT, Multiset.card_singleton, one_ne_zero,
    if_false]
  rfl

/-- **The pair accepts instances that keep the heads free**: `($g 1)` with `$g`
bound to the undeclared `foo` is answered once; so is a bare variable bound to
the list `(Cons 5 Nil)`, whose declared symbols fill a variable's place, not a
head. -/
theorem pair_accepts_instance (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {.expression [sym "foo", num 1]}) pairRow [gOne] =
        {.expression [sym "foo", num 1]} ∧
      chainCall decls (metatype grounded) (fun _ => {app "Cons" [num 5, sym "Nil"]}) pairRow
        [.var "y"] = {app "Cons" [num 5, sym "Nil"]} :=
  ⟨pair_once decls_functional _ (θ := fun _ => sym "foo") (v := gOne)
      ⟨by simp [HeadFree, decls, substA], trivial, trivial, trivial⟩,
    pair_once decls_functional _ (θ := fun _ => app "Cons" [num 5, sym "Nil"]) (v := .var "y") trivial⟩

/-- **A declared symbol at a head position breaks the pair**: binding `$g` in
`($g 1)` to the declared `inc` makes `(inc 1)`, a `Number`, which meets no
instance of `($g 1)`'s tuple type; the restriction excludes it, and the call has
no answer. This is the instance the C's `let` produced in the probe with
`Cons`. -/
theorem pair_rejects_declared_head (grounded : String → Bool) :
    ¬ Safe decls (fun _ => sym "inc") gOne ∧
      chainCall decls (metatype grounded) (fun _ => {.expression [sym "inc", num 1]}) pairRow [gOne] =
        0 := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [Safe, substA, HeadFree] at h
    simp [decls] at h
  · obtain ⟨E, hE⟩ := eff_incOne
    refine pair_zero _ eff_gOne rfl ⟨_, rfl⟩ fun d hd ρ₀ ρ₁ => ?_
    rw [hE, Multiset.mem_singleton] at hd
    subst hd
    simp

/-- **A declared head is outside the restriction from the start**: `(Same $x $y)`
is not an uninterpreted argument, and its instance `(Same 1 "x")` loses its type
(`TypedCalls.Controls.instance_loses_type`). -/
theorem same_not_safe (θ : String → Atom) : ¬ Safe decls θ (app "Same" [.var "x", .var "y"]) := by
  intro h
  simp only [Safe, substA, HeadFree] at h
  simp [decls] at h

theorem gOne_uninterp : Uninterp decls gOne := ⟨trivial, trivial, trivial, trivial⟩

/-- `(= (pin $x 0) $x)` and `(= (pin $x $n) (let $s (pin $x (- $n 1)) $x))` at
`(: pin (-> $a Number $a))`: each answer is the argument, and the call to itself, at
the same argument, is used. -/
def pinBody (o : List Atom → Multiset Atom) (args : List Atom) : Multiset Atom :=
  match args with
  | [x, .grounded (.int n)] => if n = 0 then {x} else (o [x, num (n - 1)]).bind fun _ => {x}
  | _ => 0

/-- `(-> $a Number $a)`. -/
abbrev pinRow : Ty String :=
  arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" :: ([Ty.sym "Number"] : List (Ty Empty)).map Ty.lift)
    (.var "a")

theorem pin_answers (o : List Atom → Multiset Atom) (args : List Atom) :
    ∀ r ∈ pinBody o args, ∃ x n, args = [x, num n] ∧ r = x := by
  intro r hr
  unfold pinBody at hr
  split at hr
  · next x n =>
      split_ifs at hr
      · exact ⟨x, n, rfl, (Multiset.mem_singleton.mp hr)⟩
      · obtain ⟨_, -, hr⟩ := Multiset.mem_bind.mp hr
        exact ⟨x, n, rfl, (Multiset.mem_singleton.mp hr)⟩
  · exact absurd hr (Multiset.notMem_zero r)

theorem pin_hyps (grounded : String → Bool) :
    UnintHyps decls grounded pinBody pinBody [] [.sym "Number"] where
  calls o o' agree _ args hargs := by
    obtain ⟨us, v, ws, rfl, len, -, hv, -⟩ := hargs
    cases us with
    | cons _ _ => simp at len
    | nil =>
        simp only [List.nil_append]
        unfold pinBody
        split
        · next x n heq =>
            split_ifs
            · rfl
            · simp only [List.cons.injEq] at heq
              rw [agree [x, num (n - 1)] ⟨[], x, [num (n - 1)], rfl, rfl, .nil, heq.1 ▸ hv,
                .cons (fun _ => Holds.of_count (count_int decls _)) .nil⟩]
        · rfl
  results o _ us v ws len _ r hr := by
    obtain ⟨x, n, heq, hrx⟩ := pin_answers o _ r hr
    cases us with
    | cons _ _ => simp at len
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        exact ⟨Atom.var, by rw [hrx, ← heq.1, substA_var_self], fun _ => trivial⟩

/-- **A version at an uninterpreted parameter is the protocol**
(`PETTA_CONTRACT_ENTRY_UNINTERPRETED`): `(pin ($g 1) 2)` answers `($g 1)` once through the
protocol of `(-> $a Number $a)`, every call guarded at `$a` and checked at `$a`, as its
version answers it, at every fuel from three on. -/
theorem pin_version (grounded : String → Bool) (k : ℕ) :
    protocolRun decls grounded pinBody pinRow (k + 3) [gOne, num 2] = {gOne} := by
  rw [unint_version_eq_protocol decls_functional "a" (pin_hyps grounded) (k + 3) [gOne, num 2]
    ⟨[], gOne, [num 2], rfl, rfl, .nil, gOne_uninterp,
      .cons (fun _ => Holds.of_count (count_int decls 2)) .nil⟩]
  show pinBody (versionRun pinBody (k + 2)) [gOne, num 2] = _
  simp only [pinBody]
  show (pinBody (versionRun pinBody (k + 1)) [gOne, num 1]).bind _ = _
  simp only [pinBody]
  show ((pinBody (versionRun pinBody k) [gOne, num 0]).bind _).bind _ = _
  simp [pinBody]

/-- `$m` bound to `1`, as unifying `($p 1)` with `($g $m)` leaves it. -/
def mOne (x : String) : Atom := if x = "m" then num 1 else .var x

/-- `(= (bnd $x) (let ($p 1) $x $x))` at `(: bnd (-> $a $a))`, as two-way unification
answers it: the argument with its variable bound. -/
def bndBody (_ : List Atom → Multiset Atom) (args : List Atom) : Multiset Atom :=
  match args with
  | [v] => {substA mOne v}
  | _ => 0

theorem bnd_hyps (grounded : String → Bool) : UnintHyps decls grounded bndBody bndBody [] [] where
  calls _ _ _ _ _ _ := rfl
  results _ _ us v ws len _ r hr := by
    cases us with
    | cons _ _ => simp at len
    | nil =>
        cases ws with
        | nil =>
            simp only [List.nil_append, bndBody, Multiset.mem_singleton] at hr
            exact ⟨mOne, hr, fun x => by unfold mOne; split_ifs <;> trivial⟩
        | cons _ _ => simp [bndBody] at hr

/-- `($g $m)`, uninterpreted. -/
abbrev gM : Atom := .expression [.var "g", .var "m"]

/-- **An instance by two-way unification is answered once**: `(bnd ($g $m))` answers
`($g 1)`, the argument as unification leaves it, once through the protocol of
`(-> $a $a)`. -/
theorem bnd_version (grounded : String → Bool) (k : ℕ) :
    protocolRun decls grounded bndBody
        (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" :: ([] : List (Ty Empty)).map Ty.lift) (.var "a"))
        (k + 1) [gM] = {.expression [.var "g", num 1]} := by
  rw [unint_version_eq_protocol decls_functional "a" (bnd_hyps grounded) (k + 1) [gM]
    ⟨[], gM, [], rfl, rfl, .nil, ⟨trivial, trivial, trivial, trivial⟩, .nil⟩]
  show bndBody _ [gM] = _
  simp [bndBody, substA, substL, mOne]

/-- `(= (inc1 $x) …)` answering its argument with every variable bound to the declared
`inc`. -/
def incBody (_ : List Atom → Multiset Atom) (args : List Atom) : Multiset Atom :=
  match args with
  | [v] => {substA (fun _ => sym "inc") v}
  | _ => 0

/-- **An interpreted binding breaks the version** (`contract_bind_any`): bound to the
declared `inc`, `($g 1)` becomes `(inc 1)`, which the version answers and the
protocol's result guard at `$a` rejects; the binding is not uninterpreted, so the
hypotheses of `unint_version_eq_protocol` exclude it. -/
theorem inc_binding_breaks (grounded : String → Bool) :
    versionRun incBody 1 [gOne] = {.expression [sym "inc", num 1]} ∧
      protocolRun decls grounded incBody pairRow 1 [gOne] = 0 ∧ ¬ Uninterp decls (sym "inc") := by
  have body : incBody (protocolRun decls grounded incBody pairRow 0) [gOne] = {.expression [sym "inc", num 1]} := by
    simp [incBody, substA, substL]
  refine ⟨by simp [versionRun, incBody, substA, substL], ?_, by simp [Uninterp, Safe, decls]⟩
  show chainCall decls (metatype grounded) (incBody (protocolRun decls grounded incBody pairRow 0)) pairRow [gOne] = 0
  rw [chainCall_congr (body' := fun _ => {.expression [sym "inc", num 1]}) _ _ body]
  exact (pair_rejects_declared_head grounded).2

/-! ### Arguments typed by their callee at a private formal -/

/-- `(: lenP (-> (List $a) Number))`. -/
abbrev lenRow : Ty String := arrow [listA] (Ty.sym "Number" : Ty Empty).lift

/-- **`(lenP (buildP n Nil))` needs no check of its argument**: for every body of
`(: buildP (-> Number (List $a) (List $a)))`, each answer is typed at an instance
of `(List $a)`, which `lenP`'s private formal meets, so `lenP`'s protocol with the
argument checked has the answers of the protocol without the check. -/
theorem lenP_over_buildP (grounded : String → Bool) (gBody lBody : List Atom → Multiset Atom) (n : ℤ) :
    ((chainCall decls (metatype grounded) gBody sharedRow [num n, sym "Nil"]).bind fun w =>
        chainCall decls (metatype grounded) lBody lenRow [w]) =
      (chainCall decls (metatype grounded) gBody sharedRow [num n, sym "Nil"]).bind fun w =>
        chainCall decls (metatype grounded) lBody
          (arrow [uncheckedFormal] (Ty.sym "Number" : Ty Empty).lift) [w] := by
  refine argument_typed_by_callee_private (Γ := decls) (kind := metatype grounded) decls_functional
    lBody [] [] listA (.sym "Number") (by simp [PrivateParams]) [] [] rfl fun w hw => ?_
  have typed := chainCall_shared_answers decls_functional grounded gBody [.sym "Number", listA]
    (.app [.sym "List", .var "a"]) [num n, sym "Nil"] rfl sharedRow_hyps (by decide) (noMeta_app _) w hw
  exact polyHolds_of_range (σ := fun x => .var x) rfl typed

/-- `(Cons "s" Nil)`. -/
abbrev consS : Atom := app "Cons" [str "s", sym "Nil"]

/-- **A shared variable is outside the rule**: in `(: pairP (-> (List $a) (List $a)
Number))` the variable `$a` is shared, and `(pairP (Cons 5 Nil) (Cons "s" Nil))`
answers nothing through the protocol, where the row without the first check
answers. -/
theorem pairP_shared (grounded : String → Bool) :
    ¬ PrivateParams [listA, listA] ∧
      chainCall decls (metatype grounded) (fun _ => {num 2})
        (arrow [listA, listA] (Ty.sym "Number" : Ty Empty).lift) [cons5, consS] = 0 ∧
      chainCall decls (metatype grounded) (fun _ => {num 2})
        (arrow [uncheckedFormal, listA] (Ty.sym "Number" : Ty Empty).lift) [cons5, consS] = {num 2} := by
  classical
  refine ⟨fun h => ?_, ?_, ?_⟩
  · unfold PrivateParams at h
    simp [listA, listOf] at h
  · have hAs : ∀ A ∈ [listA, listA], demand A = .guarded ∧ NoMeta A := by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hA
      subst hA
      exact ⟨by decide, noMeta_app _⟩
    rw [chainCall_shared decls_functional grounded _ _ _ _ rfl hAs (by decide)
      (fun σ => by rw [Ty.lift_bind_ground]; simp [MetaName]), Multiset.singleton_bind, if_neg]
    rintro ⟨σ, hall, -⟩
    have five := hall (listA, cons5) (by simp)
    have strs := hall (listA, consS) (by simp)
    obtain ⟨σ₁, hσ₁, fields⟩ := ctor_inversion decls_functional cons_row _ rfl _
      (by simp [Named, listA, listOf]) five
    obtain ⟨σ₂, hσ₂, fields₂⟩ := ctor_inversion decls_functional cons_row _ rfl _
      (by simp [Named, listA, listOf]) strs
    have a₁ : σ₁ "a" = σ "a" := by simpa [listA, listOf] using hσ₁
    have a₂ : σ₂ "a" = σ "a" := by simpa [listA, listOf] using hσ₂
    have hn := fields (.var "a", num 5) (by simp) (by simp [Unchecked])
    have hs := fields₂ (.var "a", str "s") (by simp) (by simp [Unchecked])
    rw [Ty.bind_var', a₁, count_class decls (g := .int 5) rfl] at hn
    rw [Ty.bind_var', a₂, count_str] at hs
    have e₁ : σ "a" = .sym "Number" := by
      by_contra h
      rw [if_neg h] at hn
      cases hn
    have e₂ : σ "a" = .sym "String" := by
      by_contra h
      rw [if_neg h] at hs
      cases hs
    rw [e₁] at e₂
    simp at e₂
  · have priv : PrivateParams [uncheckedFormal, listA] := by
      simp [PrivateParams, uncheckedFormal]
    rw [chainCall_private (Γ := decls) (kind := metatype grounded) _ _ _ priv]
    have strTyped : PolyHolds decls consS listA :=
      ⟨fun _ => .sym "String", by simpa [listA, listOf] using string_cell_typed "s"⟩
    have unchecked : demand uncheckedFormal ≠ .guarded := by decide
    simp only [argCountPoly, if_neg unchecked, if_pos (show demand listA = .guarded by decide),
      guardCountPoly_of_polyHolds decls_functional strTyped, mul_one, one_nsmul,
      Multiset.singleton_bind]
    have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
    rw [if_pos (by decide), guardCount_of_not_meta notMeta, count_int, one_nsmul]

/-- **A range that matches no instance of the formal is outside the rule**:
`(: mktree (-> Number (Tree2 Number)))`'s range is no instance of `lenP`'s
`(List $a)`. -/
theorem mktree_no_match : ¬ ∃ σ : String → Ty String, listA.bind σ = .app [.sym "Tree2", .sym "Number"] := by
  rintro ⟨σ, h⟩
  simp [listA, listOf] at h

/-! ### A range written as a parameter's type variable, as an owed class -/

/-- The heads of `(= (lead $x $n) (if (== $n 0) $x (lead $x (- $n 1))))` and
`(= (flip $n $x) (if (== $n 0) 7 (flip (- $n 1) $x)))`. -/
inductive LeadHead
  | lead
  | flip

/-- `(: lead (-> $t Number $t))` and `(: flip (-> Number $t $t))`. -/
def leadSig : LeadHead → Option (Ty String)
  | .lead => some (arrow [.var "t", (Ty.sym "Number" : Ty Empty).lift] (.var "t"))
  | .flip => some (arrow [(Ty.sym "Number" : Ty Empty).lift, .var "t"] (.var "t"))

/-- The class of a value of a class (`prepared_pure_value_class`). -/
def classOf : Atom → Option (Ty Empty)
  | .grounded g => (valueClass g).map Ty.sym
  | _ => none

theorem classOf_literal {c : String} {x : Atom} (hx : Literal c x) : classOf x = some (.sym c) := by
  cases x with
  | grounded g => simp [classOf, show valueClass g = some c from hx]
  | _ => exact (hx : False).elim

/-- Each owes the class of its argument at `$t`. -/
def leadOwe : LeadHead → List Atom → Option (Ty Empty)
  | .lead, [x, _] => classOf x
  | .flip, [_, x] => classOf x
  | _, _ => none

def leadSteps : LeadHead → (LeadHead → List Atom → Multiset Atom) → List Atom →
    Multiset (Atom ⊕ (LeadHead × List Atom))
  | .lead, _, [x, .grounded (.int n)] => if n = 0 then {.inl x} else {.inr (.lead, [x, num (n - 1)])}
  | .flip, _, [.grounded (.int n), x] => if n = 0 then {.inl (num 7)} else {.inr (.flip, [num (n - 1), x])}
  | _, _, _ => 0

/-- An activation at a value of a class at `$t` and a number owes that class. -/
def leadAct : Option (Ty Empty) → LeadHead → List Atom → Prop
  | o, .lead, vs => ∃ (c : String) (x : Atom) (n : ℤ), IsValueClass c ∧ Literal c x ∧ vs = [x, num n] ∧
      o = some (.sym c)
  | o, .flip, vs => ∃ (c : String) (x : Atom) (n : ℤ), IsValueClass c ∧ Literal c x ∧ vs = [num n, x] ∧
      o = some (.sym c)

theorem lead_hyps (grounded : String → Bool) :
    ChainHyps decls grounded leadSig leadOwe leadSteps (fun _ _ _ _ => False) leadAct where
  owes := by
    rintro o (_ | _) vs R ⟨c, x, n, hc, hx, rfl, rfl⟩ hR
    · simp only [leadOwe, classOf_literal hx, Option.some.injEq] at hR
      subst hR
      exact ⟨rfl, _, rfl, checksAt_value_parameter (pre := []) (post := [.sym "Number"]) (us := [])
        (vs := [num n]) hc hx rfl rfl (argCount_number grounded n)⟩
    · simp only [leadOwe, classOf_literal hx, Option.some.injEq] at hR
      subst hR
      exact ⟨rfl, _, rfl, checksAt_value_parameter (pre := [.sym "Number"]) (post := []) (us := [num n])
        (vs := []) hc hx rfl (argCount_number grounded n) rfl⟩
  proven := by
    rintro o (_ | _) vs T ⟨c, x, n, hc, hx, rfl, rfl⟩ hR <;>
      simp [leadOwe, classOf_literal hx] at hR
  congr := by
    rintro o (_ | _) vs ⟨c, x, n, hc, hx, rfl, rfl⟩ O O' - - <;> rfl
  nonTail := fun _ _ _ _ _ _ h => h.elim
  tail := by
    rintro o (_ | _) vs O ⟨c, x, n, hc, hx, rfl, rfl⟩ hO g ws hg
    · simp only [leadSteps] at hg
      split_ifs at hg
      · simp at hg
      · rw [Multiset.mem_singleton] at hg
        cases hg
        exact ⟨c, x, n - 1, hc, hx, rfl, rfl⟩
    · simp only [leadSteps] at hg
      split_ifs at hg
      · simp at hg
      · rw [Multiset.mem_singleton] at hg
        cases hg
        exact ⟨c, x, n - 1, hc, hx, rfl, rfl⟩

theorem lead_zero (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) (x : Atom) :
    machineRunS decls grounded leadOwe leadSteps (k + 1) o .lead [x, num 0] = owedCheck decls grounded o {x} := by
  show (leadSteps .lead _ [x, num 0]).bind _ = _
  simp [leadSteps]

theorem lead_succ (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) (x : Atom) {n : ℤ} (hn : n ≠ 0) :
    machineRunS decls grounded leadOwe leadSteps (k + 1) o .lead [x, num n] =
      machineRunS decls grounded leadOwe leadSteps k (o.or (classOf x)) .lead [x, num (n - 1)] := by
  show (leadSteps .lead _ [x, num n]).bind _ = _
  simp only [leadSteps, if_neg hn, Multiset.singleton_bind, leadOwe]

theorem flip_zero (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) (x : Atom) :
    machineRunS decls grounded leadOwe leadSteps (k + 1) o .flip [num 0, x] =
      owedCheck decls grounded o {num 7} := by
  show (leadSteps .flip _ [num 0, x]).bind _ = _
  simp [leadSteps]

theorem flip_succ (grounded : String → Bool) (k : ℕ) (o : Option (Ty Empty)) (x : Atom) {n : ℤ} (hn : n ≠ 0) :
    machineRunS decls grounded leadOwe leadSteps (k + 1) o .flip [num n, x] =
      machineRunS decls grounded leadOwe leadSteps k (o.or (classOf x)) .flip [num (n - 1), x] := by
  show (leadSteps .flip _ [num n, x]).bind _ = _
  simp only [leadSteps, if_neg hn, Multiset.singleton_bind, leadOwe]

/-- **`$t` first, as an owed class** (`lead` of `prepared_parameter_range`): `(lead
"s" 3)` runs as an activation owing `String`, the class of its argument at `$t`,
and answers `"s"` once; `(lead 4 2)` owes `Number` and answers `4` once; the
protocol of `(-> $t Number $t)` agrees, at every fuel from four on. -/
theorem lead_chain (grounded : String → Bool) (k : ℕ) :
    protocolRunS decls grounded leadSig leadSteps (k + 4) .lead [str "s", num 3] = {str "s"} ∧
      protocolRunS decls grounded leadSig leadSteps (k + 4) .lead [num 4, num 2] = {num 4} := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have notMetaS : ¬ MetaName (Ty.sym "String") := by simp [MetaName]
  constructor
  · rw [← machine_call_eq_protocol decls_functional (lead_hyps grounded) (h := .lead)
      ⟨"String", str "s", 3, .inr (.inl rfl), rfl, rfl, rfl⟩]
    simp only [leadOwe, classOf_literal (c := "String") (x := str "s") rfl]
    rw [lead_succ grounded _ _ _ (by decide), lead_succ grounded _ _ _ (by decide),
      lead_succ grounded _ _ _ (by decide)]
    norm_num
    rw [lead_zero]
    simp only [owedCheck]
    rw [rangeCheck_value grounded (g := .string "s") (c := "String") rfl notMetaS, if_pos rfl]
  · rw [← machine_call_eq_protocol decls_functional (lead_hyps grounded) (h := .lead)
      ⟨"Number", num 4, 2, .inl rfl, rfl, rfl, rfl⟩]
    simp only [leadOwe, classOf_literal (c := "Number") (x := num 4) rfl]
    rw [lead_succ grounded _ _ _ (by decide), lead_succ grounded _ _ _ (by decide)]
    norm_num
    rw [lead_zero]
    simp only [owedCheck]
    rw [rangeCheck_value grounded (g := .int 4) (c := "Number") rfl notMeta, if_pos rfl]

/-- **An answer of another class than the argument's** (`flip` of
`prepared_parameter_range`): `(flip 2 "s")` owes `String`, and its answer `7` is
removed, as the protocol of `(-> Number $t $t)` removes it; `(flip 2 5)` owes
`Number` and answers `7` once. -/
theorem flip_chain (grounded : String → Bool) (k : ℕ) :
    protocolRunS decls grounded leadSig leadSteps (k + 3) .flip [num 2, str "s"] = 0 ∧
      protocolRunS decls grounded leadSig leadSteps (k + 3) .flip [num 2, num 5] = {num 7} := by
  have notMeta : ¬ MetaName (Ty.sym "Number") := by simp [MetaName]
  have notMetaS : ¬ MetaName (Ty.sym "String") := by simp [MetaName]
  constructor
  · rw [← machine_call_eq_protocol decls_functional (lead_hyps grounded) (h := .flip)
      ⟨"String", str "s", 2, .inr (.inl rfl), rfl, rfl, rfl⟩]
    simp only [leadOwe, classOf_literal (c := "String") (x := str "s") rfl]
    rw [flip_succ grounded _ _ _ (by decide), flip_succ grounded _ _ _ (by decide)]
    norm_num
    rw [flip_zero]
    simp only [owedCheck]
    rw [rangeCheck_value grounded (g := .int 7) (c := "Number") rfl notMetaS, if_neg (by decide)]
  · rw [← machine_call_eq_protocol decls_functional (lead_hyps grounded) (h := .flip)
      ⟨"Number", num 5, 2, .inl rfl, rfl, rfl, rfl⟩]
    simp only [leadOwe, classOf_literal (c := "Number") (x := num 5) rfl]
    rw [flip_succ grounded _ _ _ (by decide), flip_succ grounded _ _ _ (by decide)]
    norm_num
    rw [flip_zero]
    simp only [owedCheck]
    rw [rangeCheck_value grounded (g := .int 7) (c := "Number") rfl notMeta, if_pos rfl]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
