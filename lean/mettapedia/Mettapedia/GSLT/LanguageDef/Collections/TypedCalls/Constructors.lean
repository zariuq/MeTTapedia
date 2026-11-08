import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRelation

/-!
# Constructor declarations: inversion, construction and tuple types

A constructor is a symbol with one arrow row `(-> B₁ … Bₖ R)` and no equations.
Under functional declarations the type relation of its applications is
decided field by field, which is what a trusted version reads.

* **The class** (`Constructor`): the result `R` is a *named* type, a symbol or
  a type constructor applied, such as `Nat` or `(List $a)` (`Named`); each
  field is *free*, a type `get-type` never checks a field at (`%Undefined%`,
  `_`) or a type variable that the declaration names nowhere else, or *fixed*,
  a type whose variables the result names. This is exactly the test of the C
  rule `contract_constructor_arrow`, field by field `contract_field_free`
  (`constructor_iff`, `Constructor.freeField_iff`).
* **The count of an application** at a closed named type is one exactly when
  the declaration's equations with the request have a solution
  (`count_ctor`): the tuple type of an application of a constructor never
  meets a named type, since its head is the constructor's arrow
  (`tuple_ne_named`).
* **Inversion** (`ctor_inversion`): an application typed once at a closed
  named type `T` comes from the result matching `T`, and each checked field is
  typed once at its instance. A fixed field's instance is the same for every
  match (`fixed_instance_unique`): the requirement fixes it.
* **Construction** (`ctor_construction`): if every field that is not free is
  typed once at its instance under some assignment `σ`, the application is
  typed once at `R σ`; free fields need nothing, since `get-type` does not
  check an unchecked field and a type variable named once admits every value
  exactly once.
* **The guard is not the relation at the metatype.** The guard of a typed call
  succeeds at `Expression` for every expression, through `get-metatype`, while
  inversion and construction speak of the relation (`guard_inversion`, and the
  controls `Controls.metatype_guard_without_relation`).
* **The walk of a ground tree** (`petta_type_walk_once`, `Walk`): a subject read at
  a closed type node by node: a literal at its class; a constant whose one
  declaration, not an arrow, matches the type one way; an application of a head
  whose one declaration `(-> P₁ … Pₖ R)` has its range matching the type one way,
  each argument walked at its parameter's formal, which is the binding of a
  variable the range names, a closed parameter itself, or the node's type where
  the parameter is the range (`FormalOf`). A successful walk is the service's
  answer exactly once (`walk_count`, `walk_getType`, `walk_guardCount`): every
  node has one derivation, and it meets its type (`walk_deriv`). Only the
  declarations the walk reads need one row. An application's tuple type is a
  candidate only where no row derives it, so it never meets a walked node. A
  parameter its range does not fix counts its argument's derivations
  (`free_parameter_count`), which no formal reads. Declarations here have symbol
  subjects, as when no value subject is annotated, the condition under which the
  C walks.

Controls, with `List`, `Nil` and `Cons` declared as in the probes: a list of
numbers is typed at `(List Number)` (`Controls.numbers_typed`), a list holding
a string is not (`Controls.string_element_untyped`), and has a tuple type
instead; coupled fields `(-> $a $a Prop)` are outside the class, and `(Same 1
"x")` is not a `Prop` though each field has a type
(`Controls.coupled_fields_untyped`); a phantom result variable gives a value
every instance of its result (`Controls.phantom_every_instance`); a field
declared `%Undefined%` or `_` holds any value, which has no type at that field
(`Controls.unchecked_field_any`); repeated rows
of `Cons`, read without idempotence as SWI-PeTTa's `get-type` reads them,
count a one-cell list twice (`Controls.repeated_rows_twice`). In the walk's probe, where
`Pair` has two declarations, lists of numbers of every length, nested lists and
`(S (S (S Z)))` walk (`Controls.lsum_walk`, `Controls.lens_walk`,
`Controls.toint_walk`); an element of another class leaves the walk and is never
typed there (`Controls.two_not_walk`); `Pair` leaves it (`Controls.pair_not_walk`),
and two rows that both meet `(Two Number)` count twice though each alone walks
(`Controls.pair_twice`); `Wrap`'s free parameter leaves it
(`Controls.wrap_not_walk`), and `Wrap`'s count is its argument's derivations
(`Controls.wrap_answers`).
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

theorem arrow_inj {V : Type} {As Bs : List (Ty V)} {R R' : Ty V} (h : arrow As R = arrow Bs R') :
    As = Bs ∧ R = R' := by
  simp only [arrow, Ty.app.injEq, List.cons.injEq, true_and] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
  exact ⟨h₁, List.singleton_inj.mp h₂⟩

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

/-- A free field: a type `get-type` never checks a field at (`%Undefined%`,
`_`), or a type variable that the result does not name. In the class below no
other field names a free variable, so a free field takes any value: its pattern
gets no fact and a construction asks nothing of its part. -/
def FreeField (R : Ty String) : Ty String → Prop
  | .var x => x ∉ R.vars
  | .sym s => s = "%Undefined%" ∨ s = "_"
  | .app _ => False

instance (R : Ty String) (A : Ty String) : Decidable (FreeField R A) := by
  cases A <;> unfold FreeField <;> infer_instance

theorem FreeField.of_unchecked {R A : Ty String} (h : Unchecked A) : FreeField R A := by
  cases A with
  | var _ => exact (h : False).elim
  | sym _ => exact h
  | app _ => exact (h : False).elim

/-- A field that is not free is checked by `get-type`. -/
theorem checked_of_not_free {R A : Ty String} (h : ¬ FreeField R A) : ¬ Unchecked A :=
  fun hu => h (FreeField.of_unchecked hu)

/-- A checked free field is a type variable the result does not name. -/
theorem FreeField.var_of_checked {R A : Ty String} (h : FreeField R A) (hc : ¬ Unchecked A) :
    ∃ x, A = .var x ∧ x ∉ R.vars := by
  cases A with
  | var x => exact ⟨x, rfl, h⟩
  | sym _ => exact (hc h).elim
  | app _ => exact (h : False).elim

/-- **The declarations the analysis inverts** (`contract_constructor_arrow`):
a named result; every field free or fixed by the result; no two fields the same
free variable. -/
structure Constructor (As : List (Ty String)) (R : Ty String) : Prop where
  named : Named R
  fields : ∀ A ∈ As, FreeField R A ∨ ∀ y ∈ A.vars, y ∈ R.vars
  distinct : As.Pairwise fun A B => ∀ x, x ∉ R.vars → A = .var x → B ≠ .var x

/-! ### The class is the C's test -/

/-- The C's test of a field of the declaration `(-> As R)`
(`contract_field_free`): a type `get-type` never checks a field at, or a type
variable that the whole declaration names once. -/
def FreeIn (As : List (Ty String)) (R : Ty String) (A : Ty String) : Prop :=
  Unchecked A ∨ ∃ x, A = .var x ∧ (arrow As R).vars.count x = 1

theorem arrow_vars_count (As : List (Ty String)) (R : Ty String) (x : String) :
    (arrow As R).vars.count x = (As.flatMap Ty.vars).count x + R.vars.count x := by
  simp [arrow, List.flatMap_append]

/-- A field other than the free variable `$x` does not name `x`. -/
theorem not_mem_vars_of_ne {R A : Ty String} {x : String} (hx : x ∉ R.vars)
    (hA : FreeField R A ∨ ∀ y ∈ A.vars, y ∈ R.vars) (ne : A ≠ .var x) : x ∉ A.vars := by
  intro mem
  rcases hA with free | fixed
  · cases A with
    | var z =>
        simp only [Ty.vars_var, List.mem_singleton] at mem
        exact ne (by rw [mem])
    | sym _ => simp at mem
    | app _ => exact free
  · exact hx (fixed x mem)

/-- In the class, a free variable field is named once by the fields. -/
theorem count_free_var {R : Ty String} {x : String} (hx : x ∉ R.vars) :
    ∀ As : List (Ty String), (∀ A ∈ As, FreeField R A ∨ ∀ y ∈ A.vars, y ∈ R.vars) →
      As.Pairwise (fun A B => ∀ z, z ∉ R.vars → A = .var z → B ≠ .var z) →
      Ty.var x ∈ As → (As.flatMap Ty.vars).count x = 1
  | [], _, _, mem => absurd mem List.not_mem_nil
  | B :: Bs, fields, distinct, mem => by
      rw [List.flatMap_cons, List.count_append]
      rw [List.pairwise_cons] at distinct
      by_cases hB : B = .var x
      · subst hB
        have none : (Bs.flatMap Ty.vars).count x = 0 := by
          rw [List.count_eq_zero, List.mem_flatMap]
          rintro ⟨C, hC, hxC⟩
          exact not_mem_vars_of_ne hx (fields C (List.mem_cons_of_mem _ hC))
            (distinct.1 C hC x hx rfl) hxC
        simp [none]
      · have here : B.vars.count x = 0 :=
          List.count_eq_zero.mpr (not_mem_vars_of_ne hx (fields B (by simp)) hB)
        have mem' : Ty.var x ∈ Bs := by
          rcases List.mem_cons.mp mem with h | h
          · exact (hB h.symm).elim
          · exact h
        rw [here, count_free_var hx Bs (fun A hA => fields A (List.mem_cons_of_mem _ hA))
          distinct.2 mem']

/-- **The class is the C's test** (`contract_constructor_arrow`): a named
result, and every field free in the declaration (`contract_field_free`) or with
every variable named by the result. -/
theorem constructor_iff {As : List (Ty String)} {R : Ty String} :
    Constructor As R ↔ Named R ∧ ∀ A ∈ As, FreeIn As R A ∨ ∀ y ∈ A.vars, y ∈ R.vars := by
  constructor
  · intro hC
    refine ⟨hC.named, fun A hA => ?_⟩
    rcases hC.fields A hA with free | fixed
    · by_cases hu : Unchecked A
      · exact .inl (.inl hu)
      · obtain ⟨x, rfl, hx⟩ := free.var_of_checked hu
        refine .inl (.inr ⟨x, rfl, ?_⟩)
        rw [arrow_vars_count, count_free_var hx As hC.fields hC.distinct hA,
          List.count_eq_zero.mpr hx]
    · exact .inr fixed
  · rintro ⟨named, test⟩
    -- a variable named once by the declaration is not named by the result
    have once : ∀ x, Ty.var x ∈ As → (arrow As R).vars.count x = 1 → x ∉ R.vars := by
      intro x hx count hxR
      have field : 1 ≤ (As.flatMap Ty.vars).count x :=
        List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨_, hx, by simp⟩)
      have result : 1 ≤ R.vars.count x := List.count_pos_iff.mpr hxR
      rw [arrow_vars_count] at count
      omega
    refine ⟨named, fun A hA => ?_, List.pairwise_iff_forall_sublist.mpr ?_⟩
    · rcases test A hA with (hu | ⟨x, rfl, count⟩) | fixed
      · exact .inl (FreeField.of_unchecked hu)
      · exact .inl (once x hA count)
      · exact .inr fixed
    · rintro A B sub x hx rfl rfl
      have twice : 2 ≤ (As.flatMap Ty.vars).count x := by
        have := (sub.flatMap Ty.vars).count_le x
        simpa using this
      have hA : Ty.var x ∈ As := sub.subset (by simp)
      rcases test _ hA with (hu | ⟨y, hy, count⟩) | fixed
      · exact hu
      · cases hy
        rw [arrow_vars_count] at count
        omega
      · exact hx (fixed x (by simp))

/-- **In the class a field is free exactly when the C's test says so.** -/
theorem Constructor.freeField_iff {As : List (Ty String)} {R A : Ty String}
    (hC : Constructor As R) (hA : A ∈ As) : FreeField R A ↔ FreeIn As R A := by
  constructor
  · intro free
    by_cases hu : Unchecked A
    · exact .inl hu
    · obtain ⟨x, rfl, hx⟩ := free.var_of_checked hu
      refine .inr ⟨x, rfl, ?_⟩
      rw [arrow_vars_count, count_free_var hx As hC.fields hC.distinct hA,
        List.count_eq_zero.mpr hx]
  · rintro (hu | ⟨x, rfl, count⟩)
    · exact FreeField.of_unchecked hu
    · intro hxR
      have field : 1 ≤ (As.flatMap Ty.vars).count x :=
        List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨_, hA, by simp⟩)
      have result : 1 ≤ R.vars.count x := List.count_pos_iff.mpr hxR
      rw [arrow_vars_count] at count
      omega

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
checked field's derivation is satisfiable, and the derivation of every field
that is not free meets the field's instance under `σ`; the solution is `σ` on
the result's variables. Checked free fields are solved by their derivation's
own type. -/
theorem ctorEqs_sat (R : Ty String) (σ : String → Ty Empty) :
    ∀ (i : ℕ) (As : List (Ty String)) (ds : List Deriv),
      (∀ A ∈ As, FreeField R A ∨ ∀ y ∈ A.vars, y ∈ R.vars) →
      As.Pairwise (fun A B => ∀ x, x ∉ R.vars → A = .var x → B ≠ .var x) →
      (∀ p ∈ List.zip As ds, ¬ Unchecked p.1 → Sat p.2.eqs) →
      (∀ p ∈ List.zip As ds, ¬ FreeField R p.1 →
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
      · -- a checked free field `$x`: its variable is solved by the derivation's type
        obtain ⟨x, rfl, free⟩ := free.var_of_checked hA
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
            exact not_mem_vars_of_ne free (fields B (List.mem_cons_of_mem _ hB))
              ((List.pairwise_cons.mp distinct).1 _ hB x free rfl) hy
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
        obtain ⟨ρd, hρd⟩ := fixed (A, d) (by simp) (fun free => by
          cases A with
          | var x => exact free (fixedA x (by simp))
          | sym _ => exact hA free
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
typed once at its instance under that match. Each field that is not free is
checked (`checked_of_not_free`), and its instance is the same for every match
(`fixed_instance_unique`): that instance is the fact the analysis records. -/
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

/-- **Construction**: if every field that is not free is typed once at its
instance under `σ`, the application is typed once at the result's instance. A
free field asks nothing of its part. -/
theorem ctor_construction (hΓ : Functional Γ) {C : String} {As : List (Ty String)}
    {R : Ty String} (row : Γ C = [arrow As R]) (hC : Constructor As R) (vs : List Atom)
    (len : vs.length = As.length) (σ : String → Ty Empty)
    (fields : ∀ p ∈ List.zip As vs, ¬ FreeField R p.1 → count (info Γ p.2) (p.1.bind σ) = 1) :
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
    (fun p hp hf => by
      obtain ⟨v, hv, hmem⟩ := zipMem p hp
      have := fields (p.1, v) hmem hf
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

/-! ## The walk of a ground tree -/

/-- A type headed by the arrow. -/
def IsArrowTy {V : Type} : Ty V → Prop
  | .app (.sym s :: _) => s = "->"
  | _ => False

/-- **A parameter's formal from the range's match** (`petta_type_walk_once`): a
variable the range names takes its binding, a closed type is itself, and the
range itself is the node's type; any other parameter leaves the walk. In every
case the formal is the parameter's instance under the match. -/
def FormalOf (R P : Ty String) : Prop :=
  (∃ x, P = .var x ∧ x ∈ R.vars) ∨ P.vars = [] ∨ P = R

/-- The range names every variable of a parameter that has a formal. -/
theorem FormalOf.vars_sub {R P : Ty String} (h : FormalOf R P) : ∀ y ∈ P.vars, y ∈ R.vars := by
  rcases h with ⟨x, rfl, hx⟩ | h | rfl
  · intro y hy
    simp only [Ty.vars_var, List.mem_singleton] at hy
    subst hy
    exact hx
  · intro y hy
    rw [h] at hy
    exact absurd hy List.not_mem_nil
  · exact fun _ hy => hy

mutual
/-- **The walk** (`petta_type_walk_once`) of a subject at a closed type: a literal
at its class; a constant whose one declaration, not an arrow, matches the type
one way; an application of a symbol, with arguments, whose one declaration is
an arrow `(-> P₁ … Pₖ R)` of its arity, the range matching the type one way and
each argument walked at its parameter's formal. A variable, a value of no class
and any other expression leave the walk. -/
def Walk (Γ : Decls) : Atom → Ty Empty → Prop
  | .grounded g, T => ∃ c, valueClass g = some c ∧ T = .sym c
  | .symbol s, T => ∃ D, Γ s = [D] ∧ ¬ IsArrowTy D ∧ ∃ σ : String → Ty Empty, D.bind σ = T
  | .expression (.symbol H :: c :: cs), T => ∃ Ps R, Γ H = [arrow Ps R] ∧
      ∃ σ : String → Ty Empty, R.bind σ = T ∧ WalkArgs Γ R σ Ps (c :: cs)
  | _, _ => False

/-- The walk of the arguments at their parameters' formals under the range's
match `σ`. -/
def WalkArgs (Γ : Decls) (R : Ty String) (σ : String → Ty Empty) :
    List (Ty String) → List Atom → Prop
  | [], [] => True
  | P :: Ps, c :: cs => FormalOf R P ∧ Walk Γ c (P.bind σ) ∧ WalkArgs Γ R σ Ps cs
  | _, _ => False
end

section Walks

variable {Γ : Decls}

mutual
/-- **A node that walks has one derivation, and it meets the type.** No
declaration outside the subject is read, so no other symbol need have one
declaration. -/
theorem walk_deriv : ∀ (v : Atom) (T : Ty Empty), Walk Γ v T →
    ∃ d, eff (info Γ v) = {d} ∧ Sat (d.eqs ++ [(d.ty, T.lift)])
  | .grounded g, T, h => by
      obtain ⟨c, hc, rfl⟩ := h
      refine ⟨classDeriv c, ?_, (sat_classDeriv_iff c _).mpr rfl⟩
      rw [info_grounded_class Γ hc]
      unfold eff
      simp
  | .symbol s, T, h => by
      obtain ⟨D, hD, -, σ, hσ⟩ := h
      refine ⟨⟨D.map DVar.own, []⟩, ?_, ?_⟩
      · rw [info_symbol, hD]
        unfold eff
        simp
      · refine ⟨fun w => match w with
          | ([], some x) => σ x
          | _ => default, ?_⟩
        rw [List.nil_append, solves_singleton, Ty.lift_bind_ground, Ty.bind_map, ← hσ]
        rfl
  | .expression (.symbol H :: c :: cs), T, h => by
      classical
      obtain ⟨Ps, R, hrow, σ, hσ, hargs⟩ := h
      obtain ⟨ds, single, sat, len, formal⟩ := walkArgs_derivs Ps (c :: cs) hargs
      have fixedVars : ∀ A ∈ Ps, ∀ y ∈ A.vars, y ∈ R.vars := fun A hA => (formal A hA).vars_sub
      have args : argEqs 1 Ps ((c :: cs).map (info Γ)) = {ctorEqs 1 Ps ds} :=
        argEqs_singletons 1 Ps _ ds (by simp [len]) single
      obtain ⟨ρ, hρ, agree⟩ := ctorEqs_sat R σ 1 Ps ds (fun A hA => .inr (fixedVars A hA))
        (List.pairwise_iff_forall_sublist.mpr fun {A B} sub x hx hA _ =>
          hx (fixedVars A (sub.subset (by simp)) x (by rw [hA]; simp)))
        (fun p hp _ => (sat p hp).left) (fun p hp _ => sat p hp)
      have hE : Sat (ctorEqs 1 Ps ds) := ⟨ρ, hρ⟩
      have hreq : Sat (ctorEqs 1 Ps ds ++ [(R.map DVar.own, T.lift)]) := by
        refine ⟨ρ, (solves_append _ _ _).mpr ⟨hρ, (solves_singleton _ _).mpr ?_⟩⟩
        rw [Ty.bind_map, Ty.lift_bind_ground, ← hσ]
        exact Ty.bind_congr R fun y hy => agree y hy
      have funT : funTrees (info Γ (.symbol H)) ((c :: cs).map (info Γ)) =
          {⟨R.map DVar.own, ctorEqs 1 Ps ds⟩} := by
        rw [info_symbol, hrow, funTrees_arrow _ _ _ _ (by simp [len]), args, Multiset.map_singleton,
          Multiset.filter_singleton, if_pos hE]
      refine ⟨⟨R.map DVar.own, ctorEqs 1 Ps ds⟩, ?_, hreq⟩
      rw [info_expression, List.map_cons]
      simp only [nodeInfo, funT, Multiset.card_singleton, one_ne_zero, if_false]
      unfold eff
      simp
  | .var _, _, h => False.elim h
  | .expression [], _, h => False.elim h
  | .expression [.symbol _], _, h => False.elim h
  | .expression [.var _], _, h => False.elim h
  | .expression [.grounded _], _, h => False.elim h
  | .expression [.expression _], _, h => False.elim h
  | .expression (.var _ :: _ :: _), _, h => False.elim h
  | .expression (.grounded _ :: _ :: _), _, h => False.elim h
  | .expression (.expression _ :: _ :: _), _, h => False.elim h

/-- Arguments that walk have one derivation each, meeting their formals, and
every parameter has a formal. -/
theorem walkArgs_derivs {R : Ty String} {σ : String → Ty Empty} :
    ∀ (Ps : List (Ty String)) (cs : List Atom), WalkArgs Γ R σ Ps cs →
      ∃ ds : List Deriv, List.Forall₂ (fun j d => eff j = {d}) (cs.map (info Γ)) ds ∧
        (∀ p ∈ List.zip Ps ds, Sat (p.2.eqs ++ [(p.2.ty, (p.1.bind σ).lift)])) ∧
        Ps.length = cs.length ∧ ∀ P ∈ Ps, FormalOf R P
  | [], [], _ => ⟨[], .nil, by simp, rfl, by simp⟩
  | P :: Ps, c :: cs, h => by
      obtain ⟨hP, hc, hrest⟩ := h
      obtain ⟨d, hd, hsat⟩ := walk_deriv c (P.bind σ) hc
      obtain ⟨ds, hds, hsats, len, hformal⟩ := walkArgs_derivs Ps cs hrest
      refine ⟨d :: ds, .cons hd hds, ?_, by simp [len], ?_⟩
      · intro p hp
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hsat
        · exact hsats p hp
      · intro Q hQ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · exact hP
        · exact hformal Q hQ
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
end

/-- **A successful walk is the service's own answer** (`petta_type_walk_once`):
the type relation types the subject at the closed type exactly once. -/
theorem walk_count {v : Atom} {T : Ty Empty} (h : Walk Γ v T) : count (info Γ v) T = 1 := by
  classical
  obtain ⟨d, hd, hsat⟩ := walk_deriv v T h
  unfold count
  rw [hd, Multiset.filter_singleton, if_pos hsat]
  rfl

/-- **The bound query answers the target once** (`petta_type_answers_bound`):
under any satisfiable store, `get-type` at the closed target has one answer. -/
theorem walk_getType {U : Type} (e : DVar → U) (injective : Function.Injective e) (S : List (Eqn U))
    (fresh : ∀ w, e w ∉ eqnVars S) (hS : Sat S) {v : Atom} {T : Ty Empty} (h : Walk Γ v T) :
    Multiset.card (getType e S T.lift (info Γ v)) = 1 := by
  rw [card_getType_closed e injective S fresh hS T, walk_count h]

/-- The guard of a typed call at the target succeeds once. -/
theorem walk_guardCount {v : Atom} {T : Ty Empty} (h : Walk Γ v T) (kind : String) :
    guardCount (info Γ v) T kind = 1 := by
  unfold guardCount
  rw [walk_count h]
  simp

/-- A value contributes at least one derivation. -/
theorem card_eff_ne_zero (j : Info) : Multiset.card (eff j) ≠ 0 := by
  unfold eff
  split_ifs with h
  · simp
  · exact h

open Classical in
/-- **A parameter its range does not fix counts its argument's derivations**: for a
head whose one row is `(-> $x R)`, `R` closed, the application is typed at `R`
once for every derivation of its argument. A walk reads one formal per
argument and none fits here, so it leaves such a head to the general path. -/
theorem free_parameter_count {H x : String} {R : Ty Empty} (row : Γ H = [arrow [.var x] R.lift])
    (v : Atom) : count (info Γ (.expression [.symbol H, v])) R = Multiset.card (eff (info Γ v)) := by
  set M : Multiset Deriv := (eff (info Γ v)).map fun d =>
    (⟨R.lift.map DVar.own, ((Ty.var x).map DVar.own, (d.push 1).ty) :: (d.push 1).eqs⟩ : Deriv) with hM
  have args : argEqs 1 [.var x] [info Γ v] =
      (eff (info Γ v)).map fun d => ((Ty.var x).map DVar.own, (d.push 1).ty) :: (d.push 1).eqs := by
    simp only [argEqs, Unchecked]
    simp [Multiset.bind_singleton]
  have allSat : ∀ d ∈ M, Sat (d.eqs ++ [(d.ty, R.lift)]) := by
    intro d hd
    rw [hM, Multiset.mem_map] at hd
    obtain ⟨d0, hd0, rfl⟩ := hd
    obtain ⟨ρd, hρd⟩ := eff_sat (cands_sat Γ v) d0 hd0
    let ρ : DVar → Ty Empty := fun w => match w with
      | ([], some y) => if y = x then d0.ty.bind ρd else default
      | (1 :: p, y) => ρd (p, y)
      | _ => default
    have push : ρ ∘ DVar.push 1 = ρd := by
      funext w
      rfl
    refine ⟨ρ, ?_⟩
    simp only [List.cons_append, solves_cons, solves_append]
    refine ⟨?_, ?_, ?_⟩
    · change ((Ty.var x).map DVar.own).bind ρ = (d0.ty.map (DVar.push 1)).bind ρ
      rw [Ty.bind_map, Ty.bind_map, push]
      simp [ρ, DVar.own]
    · change Solves ρ (d0.eqs.map (Eqn.map (DVar.push 1)))
      rw [solves_map, push]
      exact hρd
    · simp [Solves, Ty.bind_map, Ty.lift_bind_ground]
  have funT : funTrees (info Γ (.symbol H)) [info Γ v] = M := by
    rw [info_symbol, row, funTrees_arrow _ _ _ _ rfl, args, Multiset.map_map]
    exact Multiset.filter_eq_self.mpr fun d hd => (allSat d hd).left
  have cardM : Multiset.card M = Multiset.card (eff (info Γ v)) := by
    rw [hM, Multiset.card_map]
  rw [info_expression]
  simp only [List.map_cons, List.map_nil, nodeInfo, funT]
  rw [if_neg (by rw [cardM]; exact card_eff_ne_zero _)]
  unfold count
  have effM : eff ⟨[], M⟩ = M := by
    unfold eff
    rw [if_neg (by rw [cardM]; exact card_eff_ne_zero _)]
  rw [effM, Multiset.filter_eq_self.mpr allSat, cardM]

end Walks

/-! ## Controls -/

namespace Controls

/-- `(List $a)`. -/
def listOf {V : Type} (a : Ty V) : Ty V := .app [.sym "List", a]

/-- The probe declarations: `(: Nil (List $a))`, `(: Cons (-> $a (List $a) (List $a)))`,
`(: Same (-> $a $a Prop))`, `(: MkPh (-> Number (Ph $a)))`, `(: C (-> Number Expression))`,
`(: Box (-> $a (Wrap $a)))`, `(: UBox (-> %Undefined% Boxed))`, `(: WBox (-> _ Boxed))` and
`(: inc (-> Number Number))` and `(: dblS (-> String String))`. -/
def decls : Decls := fun s =>
  if s = "Nil" then [listOf (.var "a")]
  else if s = "Cons" then [arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))]
  else if s = "Same" then [arrow [.var "a", .var "a"] (.sym "Prop")]
  else if s = "MkPh" then [arrow [.sym "Number"] (.app [.sym "Ph", .var "a"])]
  else if s = "C" then [arrow [.sym "Number"] (.sym "Expression")]
  else if s = "Box" then [arrow [.var "a"] (.app [.sym "Wrap", .var "a"])]
  else if s = "UBox" then [arrow [.sym "%Undefined%"] (.sym "Boxed")]
  else if s = "WBox" then [arrow [.sym "_"] (.sym "Boxed")]
  else if s = "inc" then [arrow [.sym "Number"] (.sym "Number")]
  else if s = "dblS" then [arrow [.sym "String"] (.sym "String")]
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
    simp [listOf]

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
        intro p hp _
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

/-- **A list holding a string has its tuple type**: no derivation goes through
`Cons`'s row, so its one derivation is the list of its elements' types, headed
by `Cons`'s arrow, as SWI-PeTTa's `((-> $V (List $V) (List $V)) Number (List String))`. -/
theorem string_element_tuple :
    ∃ d, (info decls (app "Cons" [num 1, app "Cons" [str "two", sym "Nil"]])).cands = {d} ∧
      ∃ ts, d.ty = .app ((((arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))).map DVar.own).map
        (DVar.push 0)) :: ts) := by
  classical
  have row : decls "Cons" = [arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))] := by
    simp [decls]
  set vs : List Atom := [num 1, app "Cons" [str "two", sym "Nil"]]
  set E := ctorEqs 1 [.var "a", listOf (.var "a")] (vs.map (theDeriv decls_functional)) with hEdef
  have args : argEqs 1 [.var "a", listOf (.var "a")] (vs.map (info decls)) = {E} :=
    argEqs_singletons 1 _ _ _ rfl (forall₂_theDeriv decls_functional vs)
  -- the row's equations have no solution: a solution would type the list at a list type
  have unsat : ¬ Sat E := by
    rintro ⟨ρ, hρ⟩
    have typed : count (info decls (app "Cons" vs)) (listOf (ρ (DVar.own "a"))) = 1 := by
      rw [count_ctor decls_functional row vs rfl _ (by simp [Named, listOf]), if_pos]
      refine ⟨ρ, (solves_append _ _ _).mpr ⟨hρ, (solves_singleton _ _).mpr ?_⟩⟩
      rw [Ty.lift_bind_ground]
      simp [listOf, Ty.map]
    obtain ⟨σ, hσ, fields⟩ := ctor_inversion decls_functional row vs rfl _
      (by simp [Named, listOf]) typed
    have a₁ : σ "a" = ρ (DVar.own "a") := by simpa [listOf] using hσ
    have head := fields (.var "a", num 1) (by simp [vs]) (by simp [Unchecked])
    rw [Ty.bind_var', a₁] at head
    have rest := fields (listOf (.var "a"), app "Cons" [str "two", sym "Nil"]) (by simp [vs])
      (by simp [Unchecked, listOf])
    obtain ⟨σ₂, hσ₂, fields₂⟩ := ctor_inversion decls_functional row _ rfl _
      (by simp [Named, listOf]) rest
    have a₂ : σ₂ "a" = ρ (DVar.own "a") := by simpa [listOf, a₁] using hσ₂
    have elem := fields₂ (.var "a", str "two") (by simp) (by simp [Unchecked])
    rw [Ty.bind_var', a₂, count_str] at elem
    have isString : ρ (DVar.own "a") = .sym "String" := by
      by_contra h
      rw [if_neg h] at elem
      cases elem
    rw [isString] at head
    have := count_class decls (g := .int 1) (c := "Number") rfl (.sym "String")
    simp only [Ty.sym.injEq] at this
    rw [show (num 1 : Atom) = .grounded (.int 1) from rfl] at head
    rw [this] at head
    cases head
  have zero : funTrees (info decls (sym "Cons")) (vs.map (info decls)) = 0 := by
    rw [info_symbol, row, funTrees_arrow _ _ _ _ rfl, args, Multiset.map_singleton,
      Multiset.filter_singleton, if_neg unsat]
    rfl
  rw [info_expression, List.map_cons]
  simp only [nodeInfo, zero, Multiset.card_zero, if_true]
  have one : Multiset.card (tupleTrees (info decls (sym "Cons") :: vs.map (info decls))) = 1 := by
    rw [tupleTrees, Multiset.card_map, card_tupleParts 0 _ (fun j hj => by
      rw [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact card_eff decls_functional _
      · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hj
        exact card_eff decls_functional v)]
  obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp one
  refine ⟨d, hd, ?_⟩
  have mem : d ∈ tupleTrees (info decls (sym "Cons") :: vs.map (info decls)) := by
    rw [hd]
    exact Multiset.mem_singleton_self d
  simp only [tupleTrees, Multiset.mem_map] at mem
  obtain ⟨p, hp, rfl⟩ := mem
  simp only [tupleParts, Multiset.mem_bind, Multiset.mem_map] at hp
  obtain ⟨d0, hd0, p', -, rfl⟩ := hp
  have hd0' : d0 = ⟨(arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))).map DVar.own, []⟩ := by
    unfold eff at hd0
    rw [info_symbol, row] at hd0
    simpa using hd0
  subst hd0'
  exact ⟨p'.1, rfl⟩

/-- The inner cell is a list of strings: it is typed at `(List String)`. -/
theorem string_cell_typed (s : String) :
    count (info decls (app "Cons" [str s, sym "Nil"])) (listOf (.sym "String")) = 1 := by
  have row : decls "Cons" = [arrow [.var "a", listOf (.var "a")] (listOf (.var "a"))] := by
    simp [decls]
  have := ctor_construction decls_functional row cons_constructor [str s, sym "Nil"] rfl
    (fun _ => .sym "String") (by
      intro p hp _
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
  simp at this

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

theorem theDeriv_var (x : String) :
    theDeriv decls_functional (.var x) = ⟨.var ([], none), []⟩ := by
  have h := eff_theDeriv decls_functional (.var x)
  rw [info_var] at h
  unfold eff at h
  simpa using h.symm

/-- **An instance of an interpreted value can lose its type**: `(Same $x $y)` is a
`Prop`, and its instance `(Same 1 "x")` is not. A fact that a value keeps its
type under the bindings a call makes needs the value's type to be structural,
as an uninterpreted value's is. -/
theorem instance_loses_type :
    count (info decls (app "Same" [.var "x", .var "y"])) (.sym "Prop") = 1 ∧
      count (info decls (app "Same" [num 1, str "x"])) (.sym "Prop") = 0 := by
  classical
  have row : decls "Same" = [arrow [.var "a", .var "a"] (.sym "Prop")] := by simp [decls]
  refine ⟨?_, coupled_fields_untyped.1⟩
  rw [count_ctor decls_functional row _ rfl _ (by simp [Named]), if_pos]
  refine ⟨fun _ => .sym "Number", ?_⟩
  simp only [List.map_cons, List.map_nil, theDeriv_var, ctorEqs, Unchecked, Deriv.push]
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
    intro p hp _
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact count_num_number 1)
  simpa using this

theorem ubox_row : decls "UBox" = [arrow [.sym "%Undefined%"] (.sym "Boxed")] := by
  simp [decls]

theorem wbox_row : decls "WBox" = [arrow [.sym "_"] (.sym "Boxed")] := by simp [decls]

theorem ubox_constructor : Constructor [.sym "%Undefined%"] (.sym "Boxed") :=
  ⟨by simp [Named], by simp [FreeField], by simp⟩

theorem wbox_constructor : Constructor [.sym "_"] (.sym "Boxed") :=
  ⟨by simp [Named], by simp [FreeField], by simp⟩

/-- **A field declared `%Undefined%` or `_` holds any value**: `(UBox v)` and
`(WBox v)` are typed once at `Boxed` for every value `v`, the construction
asking nothing of `v`; and the field is no type of its part, as `5` is not typed
at `%Undefined%`, so a fact read at that field would be false. -/
theorem unchecked_field_any (v : Atom) :
    count (info decls (app "UBox" [v])) (.sym "Boxed") = 1 ∧
      count (info decls (app "WBox" [v])) (.sym "Boxed") = 1 ∧
      count (info decls (num 5)) (.sym "%Undefined%") = 0 := by
  classical
  have any : ∀ (c u : String), decls c = [arrow [.sym u] (.sym "Boxed")] →
      Constructor [.sym u] (.sym "Boxed") → (u = "%Undefined%" ∨ u = "_") →
      count (info decls (app c [v])) (.sym "Boxed") = 1 := by
    intro c u row hC hu
    have := ctor_construction decls_functional row hC [v] rfl (fun _ => .sym "Boxed") (by
      intro p hp notFree
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
      subst hp
      exact (notFree hu).elim)
    simpa using this
  refine ⟨any "UBox" _ ubox_row ubox_constructor (.inl rfl),
    any "WBox" _ wbox_row wbox_constructor (.inr rfl), ?_⟩
  rw [count_eq_ite decls_functional, theDeriv_int, if_neg]
  intro h
  have := (sat_class_iff "Number" _).mp h
  simp at this

/-- **The class is the C's test, on the probes**: `$a` in `Cons`'s first field
is fixed, the result naming it; `%Undefined%` in `UBox`'s field is free in the
declaration; `$a` in `Same`'s fields is named twice, neither free nor fixed. -/
theorem class_as_tested :
    (∀ y ∈ (Ty.var "a" : Ty String).vars, y ∈ (listOf (.var "a") : Ty String).vars) ∧
      FreeIn [.sym "%Undefined%"] (.sym "Boxed") (.sym "%Undefined%") ∧
      ¬ FreeIn [.var "a", .var "a"] (.sym "Prop") (.var "a") ∧
      ¬ (∀ y ∈ (Ty.var "a" : Ty String).vars, y ∈ (Ty.sym "Prop" : Ty String).vars) := by
  refine ⟨by simp [listOf], .inl (.inl rfl), ?_, by simp⟩
  rintro (h | ⟨x, hx, count⟩)
  · exact h
  · cases hx
    simp [arrow] at count

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
      intro p hp _
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

/-! ### Renamed rows -/

/-- The swap of `a` and `b`. -/
def swapAB (x : String) : String := if x = "a" then "b" else if x = "b" then "a" else x

theorem swapAB_injective : Function.Injective swapAB := by
  intro x y h
  unfold swapAB at h
  split_ifs at h <;> subst_vars <;> first | rfl | (exfalso; simp_all)

/-- `Cons` declared as `(-> $b (List $b) (List $b))`. -/
def declsSwapped : Decls := fun s => if s = "Cons" then [consRow.map swapAB] else decls s

theorem rowRen_refl (τ : Ty String) : RowRen τ τ := ⟨id, Function.injective_id, (Ty.map_id' τ).symm⟩

/-- **A renamed row changes no count**: with `Cons`'s variable renamed, `(Cons 5 Nil)` is
still typed once at `(List Number)`. -/
theorem renamed_cons_typed :
    count (info declsSwapped (app "Cons" [num 5, sym "Nil"])) listNumber = 1 := by
  rw [← count_renamed_rows (Γ := decls) (Γ' := declsSwapped) (fun s => ?_)]
  · exact cons_five_typed
  · unfold declsSwapped
    split_ifs with h
    · subst h
      rw [cons_row]
      exact .cons ⟨swapAB, swapAB_injective, rfl⟩ .nil
    · exact List.forall₂_same.mpr fun τ _ => rowRen_refl τ

/-- `Same` declared as `(-> $a $b Prop)`, whose fields are not coupled. -/
def declsUncoupled : Decls := fun s =>
  if s = "Same" then [arrow [.var "a", .var "b"] (.sym "Prop")] else decls s

theorem declsUncoupled_functional : Functional declsUncoupled := by
  intro s
  unfold declsUncoupled
  split_ifs
  · simp
  · exact decls_functional s

/-- **The renaming must be injective**: `(-> $a $a Prop)` is `(-> $a $b Prop)` with `$b`
renamed to `$a`, and `(Same 1 "x")` is a `Prop` under the second and not under the
first. -/
theorem uncoupled_differs :
    count (info declsUncoupled (app "Same" [num 1, str "x"])) (.sym "Prop") = 1 ∧
      count (info decls (app "Same" [num 1, str "x"])) (.sym "Prop") = 0 ∧
      (arrow [.var "a", .var "a"] (.sym "Prop") : Ty String) =
        (arrow [.var "a", .var "b"] (.sym "Prop")).map fun _ => "a" := by
  refine ⟨?_, coupled_fields_untyped.1, rfl⟩
  have row : declsUncoupled "Same" = [arrow [.var "a", .var "b"] (.sym "Prop")] := by
    simp [declsUncoupled]
  have hC : Constructor [.var "a", .var "b"] (.sym "Prop") :=
    ⟨by simp [Named], by simp [FreeField], by simp⟩
  have := ctor_construction declsUncoupled_functional row hC [num 1, str "x"] rfl (fun _ => .sym "Prop")
    (by
      intro p hp notFree
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl <;> exact (notFree (by simp [FreeField])).elim)
  simpa using this

/-! ### The walk of a ground tree -/

/-- `(Two $a)`. -/
def twoOf {V : Type} (a : Ty V) : Ty V := .app [.sym "Two", a]

/-- `(Box $a)`. -/
def boxOf {V : Type} (a : Ty V) : Ty V := .app [.sym "Box", a]

/-- A row `(-> Number Number R)` of `Pair`. -/
abbrev twoRow (R : Ty String) : Ty String := arrow [.sym "Number", .sym "Number"] R

/-- The declarations of the walk's probe (`type_walk_constructors`), `Pair`'s rows
given: `(: List (-> Type Type))`, `(: Nil (List $a))`, `(: Cons (-> $a (List $a) (List $a)))`,
`(: lsum (-> (List Number) Number))`, `(: lens (-> (List (List Number)) Number))`,
`(: Nat Type)`, `(: Z Nat)`, `(: S (-> Nat Nat))`, `(: toint (-> Nat Number))`,
`(: first2 (-> (Two Number) Number))`, `(: Wrap (-> $b (Box Number)))` and
`(: unbox (-> (Box Number) Number))`. -/
def walkProgram (pairRows : List (Ty String)) : Decls := fun s =>
  if s = "List" then [arrow [.sym "Type"] (.sym "Type")]
  else if s = "Nil" then [listOf (.var "a")]
  else if s = "Cons" then [consRow]
  else if s = "lsum" then [arrow [listOf (.sym "Number")] (.sym "Number")]
  else if s = "lens" then [arrow [listOf (listOf (.sym "Number"))] (.sym "Number")]
  else if s = "Nat" then [.sym "Type"]
  else if s = "Z" then [.sym "Nat"]
  else if s = "S" then [arrow [.sym "Nat"] (.sym "Nat")]
  else if s = "toint" then [arrow [.sym "Nat"] (.sym "Number")]
  else if s = "Pair" then pairRows
  else if s = "first2" then [arrow [twoOf (.sym "Number")] (.sym "Number")]
  else if s = "Wrap" then [arrow [.var "b"] (boxOf (.sym "Number"))]
  else if s = "unbox" then [arrow [boxOf (.sym "Number")] (.sym "Number")]
  else []

/-- The probe's own program: `Pair` declared at `(Two Number)` and at `(Two Atom)`,
so the declarations are not functional. -/
abbrev walkDecls : Decls :=
  walkProgram [twoRow (twoOf (.sym "Number")), twoRow (twoOf (.sym "Atom"))]

/-- `(Cons x₁ (Cons x₂ … Nil))`. -/
def consList : List Atom → Atom
  | [] => sym "Nil"
  | x :: xs => app "Cons" [x, consList xs]

theorem walk_num (rows : List (Ty String)) (n : ℤ) : Walk (walkProgram rows) (num n) (.sym "Number") :=
  ⟨"Number", rfl, rfl⟩

theorem walk_nil (rows : List (Ty String)) (τ : Ty Empty) : Walk (walkProgram rows) (sym "Nil") (listOf τ) :=
  ⟨listOf (.var "a"), by simp [walkProgram], by simp [IsArrowTy, listOf], fun _ => τ, by simp [listOf]⟩

/-- A cell walks at `(List τ)` exactly when its element walks at `τ` and its rest
at `(List τ)`. -/
theorem walk_cons_iff (rows : List (Ty String)) (x rest : Atom) (τ : Ty Empty) :
    Walk (walkProgram rows) (app "Cons" [x, rest]) (listOf τ) ↔
      Walk (walkProgram rows) x τ ∧ Walk (walkProgram rows) rest (listOf τ) := by
  constructor
  · rintro ⟨Ps, R, hrow, σ, hσ, hargs⟩
    have hrow' : consRow = arrow Ps R := by simpa [walkProgram] using hrow
    obtain ⟨rfl, rfl⟩ := arrow_inj hrow'
    have ha : σ "a" = τ := by simpa [listOf] using hσ
    obtain ⟨-, hx, -, hrest, -⟩ := hargs
    refine ⟨by simpa [ha] using hx, ?_⟩
    simpa [listOf, ha] using hrest
  · rintro ⟨hx, hrest⟩
    refine ⟨[.var "a", listOf (.var "a")], listOf (.var "a"), by simp [walkProgram, consRow], fun _ => τ,
      by simp [listOf], .inl ⟨"a", rfl, by simp [listOf]⟩, by simpa using hx, .inr (.inr rfl), ?_, trivial⟩
    simpa [listOf] using hrest

theorem walk_consList (rows : List (Ty String)) (τ : Ty Empty) :
    ∀ xs : List Atom, (∀ x ∈ xs, Walk (walkProgram rows) x τ) →
      Walk (walkProgram rows) (consList xs) (listOf τ)
  | [], _ => walk_nil rows τ
  | x :: xs, h => (walk_cons_iff rows x _ τ).mpr
      ⟨h x (by simp), walk_consList rows τ xs fun y hy => h y (by simp [hy])⟩

/-- **A list of numbers walks** (`(lsum (build 30 Nil))`): at `(List Number)`, for
every length, so the service types it there once, though `Pair` has two
declarations in the same program. -/
theorem lsum_walk (ns : List ℤ) :
    Walk walkDecls (consList (ns.map num)) listNumber ∧
      count (info walkDecls (consList (ns.map num))) listNumber = 1 := by
  have h : Walk walkDecls (consList (ns.map num)) listNumber :=
    walk_consList _ _ _ fun x hx => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
      exact walk_num _ n
  exact ⟨h, walk_count h⟩

/-- **Nested lists walk**: `(Cons (Cons 1 (Cons 2 Nil)) (Cons (Cons 3 Nil) Nil))` at
`(List (List Number))`; with `"x"` for `3` the inner element leaves the walk. -/
theorem lens_walk :
    count (info walkDecls (consList [consList [num 1, num 2], consList [num 3]])) (listOf listNumber) = 1 ∧
      ¬ Walk walkDecls (consList [consList [num 1], consList [str "x"]]) (listOf listNumber) := by
  refine ⟨walk_count (walk_consList _ _ _ fun x hx => ?_), fun h => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact walk_consList _ _ _ fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> exact walk_num _ _
  · obtain ⟨-, h⟩ := (walk_cons_iff _ _ _ _).mp h
    obtain ⟨h, -⟩ := (walk_cons_iff _ _ _ _).mp h
    obtain ⟨⟨c, hc, he⟩, -⟩ := (walk_cons_iff _ _ _ _).mp h
    cases hc
    exact absurd (Ty.sym.inj he) (by decide)

/-- The numeral `(S (S … Z))`. -/
def peano : ℕ → Atom
  | 0 => sym "Z"
  | k + 1 => app "S" [peano k]

theorem walk_peano (rows : List (Ty String)) : ∀ k, Walk (walkProgram rows) (peano k) (.sym "Nat")
  | 0 => ⟨.sym "Nat", by simp [walkProgram], by simp [IsArrowTy], fun _ => default, rfl⟩
  | k + 1 => ⟨[.sym "Nat"], .sym "Nat", by simp [walkProgram], fun _ => default, rfl,
      .inr (.inl rfl), walk_peano rows k, trivial⟩

/-- **Peano numbers walk**: `(S (S (S Z)))` at `Nat`, typed there once. -/
theorem toint_walk : count (info walkDecls (peano 3)) (.sym "Nat") = 1 :=
  walk_count (walk_peano _ 3)

/-- **An element of another class leaves the walk**: `(Cons 1 (Cons "two" Nil))` does
not walk at `(List Number)`, and the service types it there never. -/
theorem two_not_walk :
    ¬ Walk walkDecls (consList [num 1, str "two"]) listNumber ∧
      count (info walkDecls (consList [num 1, str "two"])) listNumber = 0 := by
  constructor
  · intro h
    obtain ⟨-, h⟩ := (walk_cons_iff _ _ _ _).mp h
    obtain ⟨⟨c, hc, he⟩, -⟩ := (walk_cons_iff _ _ _ _).mp h
    cases hc
    exact absurd (Ty.sym.inj he) (by decide)
  · have same : info walkDecls (consList [num 1, str "two"]) = info decls (consList [num 1, str "two"]) := by
      unfold info
      refine TypedCertificates.Judgment.full_congr typeRelation _ fun ℓ hℓ => ?_
      simp only [consList, TypedCertificates.Judgment.leaves, TypedCertificates.Judgment.leavesAll,
        List.append_nil, List.mem_append, List.mem_singleton] at hℓ
      rcases hℓ with rfl | rfl | rfl | rfl | rfl <;> simp [typeRelation, leafInfo, walkProgram, decls]
    rw [same]
    exact string_element_untyped

/-- **A constructor with two declarations leaves the walk**, at every type. -/
theorem pair_not_walk (T : Ty Empty) : ¬ Walk walkDecls (app "Pair" [num 4, num 5]) T := by
  rintro ⟨Ps, R, hrow, -⟩
  simp [walkProgram] at hrow

/-- The equations of `(Pair 4 5)` through a row `(-> Number Number R)`. -/
abbrev pairEqs : List (Eqn DVar) :=
  ctorEqs 1 [.sym "Number", .sym "Number"] [classDeriv "Number", classDeriv "Number"]

theorem solves_pairEqs : Solves (fun _ => (Ty.sym "Number" : Ty Empty)) pairEqs := by
  simp [ctorEqs, Unchecked, classDeriv, Deriv.push, Solves, Ty.map]

/-- `(Pair 4 5)` has one derivation through each of two rows. -/
theorem pair_info (R₁ R₂ : Ty String) :
    info (walkProgram [twoRow R₁, twoRow R₂]) (app "Pair" [num 4, num 5]) =
      ⟨[], {⟨R₁.map DVar.own, pairEqs⟩} + {⟨R₂.map DVar.own, pairEqs⟩}⟩ := by
  classical
  set Γ := walkProgram [twoRow R₁, twoRow R₂] with hΓ
  have effNum : ∀ n : ℤ, eff (info Γ (num n)) = {classDeriv "Number"} := by
    intro n
    rw [info_int]
    unfold eff
    simp
  have args : argEqs 1 [.sym "Number", .sym "Number"] [info Γ (num 4), info Γ (num 5)] = {pairEqs} :=
    argEqs_singletons 1 _ _ _ rfl (.cons (effNum 4) (.cons (effNum 5) .nil))
  have part : ∀ (R : Ty String) (c : Multiset Deriv),
      funTrees ⟨[twoRow R], c⟩ [info Γ (num 4), info Γ (num 5)] = {⟨R.map DVar.own, pairEqs⟩} := by
    intro R c
    rw [funTrees_arrow _ _ _ _ rfl, args, Multiset.map_singleton, Multiset.filter_singleton,
      if_pos ⟨_, solves_pairEqs⟩]
  have rows : Γ "Pair" = [twoRow R₁] ++ [twoRow R₂] := by simp [hΓ, walkProgram]
  have funT : funTrees (info Γ (sym "Pair")) [info Γ (num 4), info Γ (num 5)] =
      {⟨R₁.map DVar.own, pairEqs⟩} + {⟨R₂.map DVar.own, pairEqs⟩} := by
    rw [info_symbol, rows, funTrees_rows_append _ _ _ 0, part, part]
  rw [info_expression]
  simp only [List.map_cons, List.map_nil, nodeInfo, funT]
  rw [if_neg (by simp)]

/-- **The general path answers `(Pair 4 5)` at `(Two Number)` once** (`(first2 (Pair 4
5))` answers `4`): through the first row; the second gives `(Two Atom)`. -/
theorem pair_answers : count (info walkDecls (app "Pair" [num 4, num 5])) (twoOf (.sym "Number")) = 1 := by
  classical
  rw [pair_info]
  unfold count eff
  rw [if_neg (by simp), Multiset.filter_add, Multiset.filter_singleton, Multiset.filter_singleton, if_pos,
    if_neg]
  · rfl
  · rintro ⟨ρ, hρ⟩
    rw [solves_append, solves_singleton] at hρ
    simp [twoOf, Ty.map, Ty.lift_bind_ground] at hρ
  · exact ⟨fun _ => .sym "Number", (solves_append _ _ _).mpr ⟨solves_pairEqs,
      by simp [Solves, twoOf, Ty.map, Ty.lift_bind_ground]⟩⟩

/-- **The one declaration is needed**: with rows `(-> Number Number (Two Number))` and
`(-> Number Number (Two $t))`, each alone walks `(Pair 4 5)` at `(Two Number)`,
while the two together type it there twice. -/
theorem pair_twice :
    (∀ R ∈ [twoOf (.sym "Number"), twoOf (.var "t")],
      Walk (walkProgram [twoRow R]) (app "Pair" [num 4, num 5]) (twoOf (.sym "Number"))) ∧
      count (info (walkProgram [twoRow (twoOf (.sym "Number")), twoRow (twoOf (.var "t"))])
        (app "Pair" [num 4, num 5])) (twoOf (.sym "Number")) = 2 := by
  classical
  constructor
  · intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    refine ⟨[.sym "Number", .sym "Number"], R, by simp [walkProgram], fun _ => .sym "Number", ?_,
      .inr (.inl rfl), walk_num _ 4, .inr (.inl rfl), walk_num _ 5, trivial⟩
    rcases hR with rfl | rfl <;> rfl
  · rw [pair_info]
    unfold count eff
    rw [if_neg (by simp), Multiset.filter_add, Multiset.filter_singleton, Multiset.filter_singleton, if_pos,
      if_pos]
    · rfl
    · exact ⟨fun _ => .sym "Number", (solves_append _ _ _).mpr ⟨solves_pairEqs,
        by simp [Solves, twoOf, Ty.map, Ty.lift_bind_ground]⟩⟩
    · exact ⟨fun _ => .sym "Number", (solves_append _ _ _).mpr ⟨solves_pairEqs,
        by simp [Solves, twoOf, Ty.map, Ty.lift_bind_ground]⟩⟩

/-- **A parameter the range does not fix leaves the walk**: `(: Wrap (-> $b (Box
Number)))` has no formal for `$b`. -/
theorem wrap_not_walk (rows : List (Ty String)) (v : Atom) (T : Ty Empty) :
    ¬ Walk (walkProgram rows) (app "Wrap" [v]) T := by
  rintro ⟨Ps, R, hrow, σ, -, hargs⟩
  have hrow' : arrow [.var "b"] (boxOf (.sym "Number")) = arrow Ps R := by
    simpa [walkProgram] using hrow
  obtain ⟨rfl, rfl⟩ := arrow_inj hrow'
  obtain ⟨hP, -⟩ := hargs
  simp [FormalOf, boxOf] at hP

/-- **What the general path answers for `Wrap`**: `(Wrap "anything")` at `(Box Number)`
once (`(unbox (Wrap "anything"))` answers `7`), and `(Wrap (Pair 4 5))` twice where
`Pair` has two rows that both give `(Pair 4 5)` a derivation: the count is the
argument's derivations, which no formal reads. -/
theorem wrap_answers :
    count (info walkDecls (app "Wrap" [str "anything"])) (boxOf (.sym "Number")) = 1 ∧
      count (info (walkProgram [twoRow (twoOf (.sym "Number")), twoRow (twoOf (.var "t"))])
        (app "Wrap" [app "Pair" [num 4, num 5]])) (boxOf (.sym "Number")) = 2 := by
  have row : ∀ rows : List (Ty String), walkProgram rows "Wrap" =
      [arrow [.var "b"] ((boxOf (.sym "Number") : Ty Empty)).lift] := by
    intro rows
    simp [walkProgram, boxOf, Ty.lift, Ty.map]
  constructor
  · rw [free_parameter_count (row _), info_string]
    unfold eff
    simp
  · rw [free_parameter_count (row _), pair_info]
    unfold eff
    simp

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
