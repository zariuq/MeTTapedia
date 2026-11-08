import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol

/-!
# Declared builtins: the protocol as class tests

Declaring a grounded operation, `(: + (-> Number Number Number))`, makes its
calls typed calls: `(+ "a" 1)` then answers nothing instead of raising. The
compiled tier meets some guards without the type relation.

* **Values and variables.** For a number, a string or a truth value, the type
  relation answers its class and nothing else, whatever the declarations
  (`count_class`); a variable value has every type once (`count_var`). So the
  guard at a value class is a class test (`guardCount_classTest`): a value of
  that class passes once, a value of another class fails, and a variable
  passes (`ClassTest`); the inline protocol of class tests is the row's
  protocol on such arguments (`inline_eq_protocol`).
* **Met on a literal, binding nothing.** A guard at a value class on a literal
  of that class continues once, extending the store by an equation between
  equal types (`guard_literal`); stores with the same solutions are not told
  apart by any later guard (`guards_agree`, `resultGuard_congr`). So any rule
  that meets inline only literals of a value class at that class, passing the
  store on, gives every row's protocol, closed or not, with its multiplicities
  (`chainInline_eq`).
* **The class guard** (`ClassMet`, `oem_class_guard_met`): a guard at `Number`
  or `String` on a grounded value of that class is met inline; every other
  value, variables, symbols and expressions included, takes the full guard,
  failures included (`classGuard_protocol`).
* **Elided literal arguments** (`Elided`, `oem_build_declared_builtin`): when
  every argument as written is a variable or a literal, a literal's guard at
  the symbol of its class is not compiled; with the class guards and the
  result's, the compiled protocol is the row's (`declaredBuiltin_protocol`).
* **One program.** The relation here is that of a program with no `get-type`
  or `get-metatype` rule: the condition `oem_literal_types_intrinsic` checks
  when compiling, and the compiled tier relies on by running only on the
  program it compiled, with arguments that change no program before a guard.
  A rule adds answers (`Rules`, `guardCountWith`): with
  `(= (get-type 3) Number)`, `(f 3)` answers four times where the compiled
  protocol of the program without the rule answers once
  (`Controls.rule_breaks_class_verdict`).
* **Arguments typed by their callee** (`petta_machine_argument_typed_by_callee`):
  every answer of a call whose range is a closed guarded type passed its result
  guard there (`chainCall_answers_passed`), and under functional declarations a
  guard passes such a value once more (`bind_guard_passed`), so a closed row's
  protocol with that argument checked has the answers, multiplicities included,
  of the row with it unchecked (`argument_typed_by_callee`,
  `Controls.drop_after_callee`). The callee's own check removes an ill-typed
  answer and checks each answer of a nondeterministic body once
  (`Controls.callee_cases`); with `(= (get-type 3) Number)` the counts differ
  (`Controls.rule_breaks_callee_discharge`).
* **Steps of a native fold** (`native_fold_step_declarations_numeric`): a step
  declared by one arrow whose positions every integer meets (`MeetsInts`:
  `Number`, `%Undefined%`, `_`, or a type variable) has, on integer arguments and
  integer answers, exactly its body's answers through its protocol
  (`fold_step_protocol`); a `String` result, `Atom`, a string item and two
  distinct arrows do not (`Controls.fold_steps_declined`).
* **A range written as one parameter's type variable**
  (`PREPARED_PURE_VALUE_PARAMETER`, `prepared_pure_parameter_range_variable`):
  at `(-> A₁ … $t … Aₖ $t)`, every `Aᵢ` closed and `$t` named nowhere else, on a
  value of the class `c` at `$t`, the guard there binds `$t` to `c` once
  (`guard_var_literal`), the closed guards after it see the store as the
  instance's (`guards_closed_pair`), and the result guard at `$t` is the guard at
  `c` (`resultGuard_pair`): the protocol is the protocol of the row with `c`
  written for `$t` (`value_parameter_protocol_at`), and at the last position the
  closed checks, the body and one check at `c` (`value_parameter_protocol`).
  Controls: `(: cnt (-> Number $t $t))` keeps `1000`, `flip` removes `7` at a
  string (`Controls.cnt_value_parameter`, `Controls.flip_value_parameter`), and
  `(-> $t Number $t)` keeps `5` at a number and removes `7` at a string
  (`Controls.value_parameter_first`).
* **Not for symbols or expressions.** A symbol's guard is its declarations:
  with `(: a Number)` the guard of `a` at `Number` passes, and without it fails
  (`Controls.symbol_guard_reads_declarations`).
* **Distinct rows** are alternatives, and the inline protocol of one row is
  not the call (`Controls.distinct_rows_add`).

Controls replay the probes: typed `(+ 1 2)` answers `3`, typed `(+ "a" 1)`
answers nothing where the untyped builtin raises, and typed `(+ $v 1)` runs the
builtin, which raises (`Controls.typed_plus`); the class guard meets a number
at `Number` and a string at `String` only (`Controls.classMet_cases`); elision
needs every argument written as a variable or a literal
(`Controls.elided_cases`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Value classes -/

/-- The arguments whose guard is a class test: variables and values of a class. -/
def Simple : Atom → Prop
  | .var _ => True
  | .grounded g => (valueClass g).isSome
  | _ => False

/-- The class test at the value class `c`: a variable passes, a grounded value
passes when it is of class `c`. -/
def ClassTest (c : String) : Atom → Prop
  | .var _ => True
  | .grounded g => valueClass g = some c
  | _ => False

instance (c : String) (v : Atom) : Decidable (ClassTest c v) := by
  cases v <;> unfold ClassTest <;> infer_instance

instance (v : Atom) : Decidable (Simple v) := by
  cases v <;> unfold Simple <;> infer_instance

/-- **The guard at a value class is the class test** on variables and values of
a class, whatever the declarations. -/
theorem guardCount_classTest (Γ : Decls) (grounded : String → Bool) {c : String} (hc : IsValueClass c)
    {v : Atom} (hv : Simple v) :
    guardCount (info Γ v) (.sym c) (metatype grounded v) = if ClassTest c v then 1 else 0 := by
  have notMeta : (Ty.sym c : Ty Empty) ≠ .sym (metatype grounded v) := by
    intro h
    have := Ty.sym.inj h
    cases v with
    | var _ =>
        simp only [metatype] at this
        exact absurd this (by rcases hc with rfl | rfl | rfl <;> decide)
    | grounded _ =>
        simp only [metatype] at this
        exact absurd this (by rcases hc with rfl | rfl | rfl <;> decide)
    | symbol _ => exact hv.elim
    | expression _ => exact hv.elim
  rw [guardCount_of_ne _ _ _ notMeta]
  cases v with
  | var x => rw [count_var]; simp [ClassTest]
  | grounded g =>
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hv
      rw [count_class Γ hc']
      simp only [ClassTest, hc', Option.some.injEq, Ty.sym.injEq]
      by_cases h : c = c'
      · subst h
        simp
      · simp [h, Ne.symm h]
  | symbol _ => exact hv.elim
  | expression _ => exact hv.elim

/-! ## The inline protocol -/

/-- **The inline protocol of a declared builtin** with value-class parameters: a
class test per argument, then the operation, each answer tested by the
result's class. -/
def inlineCall (op : List Atom → Multiset Atom) (classes : List String) (resultClass : String)
    (vs : List Atom) : Multiset Atom :=
  if List.Forall₂ ClassTest classes vs then (op vs).filter (ClassTest resultClass) else 0

theorem argCount_classes (Γ : Decls) (grounded : String → Bool) :
    ∀ (classes : List String) (vs : List Atom), (∀ c ∈ classes, IsValueClass c) →
      (∀ v ∈ vs, Simple v) →
      argCount Γ (metatype grounded) (classes.map fun c => (.sym c : Ty Empty)) vs =
        if List.Forall₂ ClassTest classes vs then 1 else 0
  | [], [], _, _ => by simp [argCount]
  | c :: cs, v :: vs, hcs, hvs => by
      have hc := hcs c (by simp)
      have guarded : demand ((Ty.sym c : Ty Empty).lift) = .guarded := by
        rcases hc with rfl | rfl | rfl <;> decide
      simp only [List.map_cons, argCount, guarded, if_true,
        guardCount_classTest Γ grounded hc (hvs v (by simp)),
        argCount_classes Γ grounded cs vs (fun c' hc' => hcs c' (by simp [hc']))
          (fun v' hv' => hvs v' (by simp [hv'])), List.forall₂_cons]
      by_cases h₁ : ClassTest c v <;> by_cases h₂ : List.Forall₂ ClassTest cs vs <;> simp [h₁, h₂]
  | [], _ :: _, _, _ => by simp [argCount]
  | _ :: _, [], _, _ => by simp [argCount]

/-- **The inline protocol is the row's protocol** when the arguments and the
operation's answers are values or variables. -/
theorem inline_eq_protocol (Γ : Decls) (grounded : String → Bool) (op : List Atom → Multiset Atom)
    (classes : List String) (resultClass : String) (vs : List Atom)
    (hclasses : ∀ c ∈ classes, IsValueClass c) (hresult : IsValueClass resultClass)
    (hvs : ∀ v ∈ vs, Simple v) (hanswers : ∀ r ∈ op vs, Simple r) :
    chainCall Γ (metatype grounded) op
        (arrow ((classes.map fun c => (.sym c : Ty Empty)).map Ty.lift) (Ty.sym resultClass : Ty Empty).lift)
        vs =
      inlineCall op classes resultClass vs := by
  rw [chainCall_closed, argCount_classes Γ grounded classes vs hclasses hvs]
  have guarded : ResultGuarded ((Ty.sym resultClass : Ty Empty).lift) := by
    rcases hresult with rfl | rfl | rfl <;> decide
  simp only [if_pos guarded]
  unfold inlineCall
  split_ifs
  · rw [one_nsmul, Multiset.filter_eq_bind]
    refine Multiset.bind_congr fun r hr => ?_
    rw [guardCount_classTest Γ grounded hresult (hanswers r hr)]
    split_ifs
    · exact one_nsmul _
    · exact zero_nsmul _
  · rw [zero_nsmul]

/-- **The builtin runs exactly when every class test passes**: the protocol's
continuations before the body are one when every argument passes its class
test and none otherwise, so a failed test answers nothing and never runs the
builtin, and a passed test runs it, raising where the builtin raises. -/
theorem argCount_classes_eq_one_iff (Γ : Decls) (grounded : String → Bool) (classes : List String)
    (vs : List Atom) (hclasses : ∀ c ∈ classes, IsValueClass c) (hvs : ∀ v ∈ vs, Simple v) :
    argCount Γ (metatype grounded) (classes.map fun c => (.sym c : Ty Empty)) vs = 1 ↔
      List.Forall₂ ClassTest classes vs := by
  rw [argCount_classes Γ grounded classes vs hclasses hvs]
  split_ifs with h <;> simp [h]

/-- A failed class test answers nothing, whatever the body would do. -/
theorem chainCall_of_test_fails (Γ : Decls) (grounded : String → Bool)
    (body : List Atom → Multiset Atom) (classes : List String) (resultClass : String)
    (vs : List Atom) (hclasses : ∀ c ∈ classes, IsValueClass c) (hvs : ∀ v ∈ vs, Simple v)
    (fails : ¬ List.Forall₂ ClassTest classes vs) :
    chainCall Γ (metatype grounded) body
        (arrow ((classes.map fun c => (.sym c : Ty Empty)).map Ty.lift) (Ty.sym resultClass : Ty Empty).lift)
        vs = 0 := by
  rw [chainCall_closed, argCount_classes Γ grounded classes vs hclasses hvs, if_neg fails, zero_nsmul]

/-! ## The compiled tier: guards met inline -/

section Compiled

variable (Γ : Decls) (kind : Atom → String)

open Classical in
/-- **The compiled guards**: a guard the compiled tier meets inline (`met`, given
the position, the formal and the value) passes the store on, one continuation
that binds nothing; every other guarded parameter takes its guard. -/
noncomputable def guardsInline (met : ℕ → Ty String → Atom → Prop) :
    ℕ → List (Ty String) → List Atom → List (Eqn CallVar) → Multiset (List (Eqn CallVar))
  | _, [], [], S => {S}
  | k, A :: As, v :: vs, S =>
      if demand A = .guarded ∧ ¬ met k A v then
        (guard (atGuard k) S (A.map .inl) (info Γ v) (kind v)).bind (guardsInline met (k + 1) As vs)
      else guardsInline met (k + 1) As vs S
  | _, [], _ :: _, _ => 0
  | _, _ :: _, [], _ => 0

open Classical in
/-- **The compiled protocol of one row**: the compiled guards, the body, and the
result guard, met inline (`metResult`) or run. -/
noncomputable def chainInline (met : ℕ → Ty String → Atom → Prop)
    (metResult : Ty String → Atom → Prop) (body : List Atom → Multiset Atom) (τ : Ty String)
    (vs : List Atom) : Multiset Atom :=
  match arrowSplit τ with
  | some (As, R) => (guardsInline Γ kind met 0 As vs []).bind fun S =>
      (body vs).bind fun r => if metResult R r then {r} else resultGuard Γ kind As.length R S r
  | none => 0

/-- A rule that meets inline only a literal of a value class, at the symbol of
that class. -/
def MeetsLiterals (met : ℕ → Ty String → Atom → Prop) : Prop :=
  ∀ k A v, met k A v → ∃ c, A = .sym c ∧ IsValueClass c ∧ Literal c v

variable {Γ kind}

theorem MeetsLiterals.or {met met' : ℕ → Ty String → Atom → Prop} (h : MeetsLiterals met)
    (h' : MeetsLiterals met') : MeetsLiterals fun k A v => met k A v ∨ met' k A v :=
  fun k A v hm => hm.elim (h k A v) (h' k A v)

theorem guardsInline_agree {met : ℕ → Ty String → Atom → Prop} (hmet : MeetsLiterals met) :
    ∀ (k : ℕ) (As : List (Ty String)) (vs : List Atom) {S S' : List (Eqn CallVar)}, Agree S S' →
      Multiset.Rel Agree (guardsInline Γ kind met k As vs S) (guards Γ kind k As vs S')
  | _, [], [], _, _, h => .cons h .zero
  | k, A :: As, v :: vs, S, S', h => by
      simp only [guardsInline, guards]
      by_cases hm : met k A v
      · obtain ⟨c, rfl, hc, hv⟩ := hmet k A v hm
        rw [if_neg fun h => h.2 hm, if_pos (demand_valueClass hc), Ty.map_sym,
          guard_literal _ (h.1.sat_iff.mp h.2) hv Γ _, Multiset.singleton_bind]
        exact guardsInline_agree hmet (k + 1) As vs ⟨h.1.trans (sameSol_taut S' _).symm, h.2⟩
      · by_cases hg : demand A = .guarded
        · rw [if_pos ⟨hg, hm⟩, if_pos hg]
          exact Multiset.rel_bind (fun _ _ hab => guardsInline_agree hmet (k + 1) As vs hab)
            (guard_agree _ h.1 _ _ _)
        · rw [if_neg fun h => hg h.1, if_neg hg]
          exact guardsInline_agree hmet (k + 1) As vs h
  | _, [], _ :: _, _, _, _ => by simp only [guardsInline, guards]; exact .zero
  | _, _ :: _, [], _, _, _ => by simp only [guardsInline, guards]; exact .zero

theorem resultGuarded_valueClass {c : String} (hc : IsValueClass c) : ResultGuarded (.sym c) := by
  rcases hc with rfl | rfl | rfl <;> decide

/-- **Guards met inline on literals of their class are exact**: for any rule
that meets inline only a literal of a value class at that class, at the
parameters and at the result, the compiled protocol of a row has the row's
answers, with their multiplicities, for every row, closed or not. -/
theorem chainInline_eq {met : ℕ → Ty String → Atom → Prop} {metResult : Ty String → Atom → Prop}
    (hmet : MeetsLiterals met) (hres : MeetsLiterals fun _ => metResult)
    (body : List Atom → Multiset Atom) (τ : Ty String) (vs : List Atom) :
    chainInline Γ kind met metResult body τ vs = chainCall Γ kind body τ vs := by
  unfold chainInline chainCall
  cases arrowSplit τ with
  | none => rfl
  | some p =>
    obtain ⟨As, R⟩ := p
    dsimp only
    refine bind_agree (guardsInline_agree hmet 0 As vs ⟨fun _ => Iff.rfl, sat_nil⟩) _ _
      fun {S S'} h => Multiset.bind_congr fun r _ => ?_
    split_ifs with hr
    · obtain ⟨c, rfl, hc, hlit⟩ := hres 0 R r hr
      unfold resultGuard
      rw [if_pos (resultGuarded_valueClass hc), Ty.map_sym,
        guard_literal _ (h.1.sat_iff.mp h.2) hlit Γ _, Multiset.map_singleton]
    · exact resultGuard_congr Γ kind _ R h.1 r

/-! ### The class guard -/

/-- **The guards met by the value's class** (`oem_guard_class`,
`oem_class_guard_met`): a guard at `Number` on a grounded number, or at `String`
on a grounded string. A variable, a symbol, an expression or a value of another
class is not met here: it takes the full guard, failures included. -/
def ClassMet (_k : ℕ) (A : Ty String) (v : Atom) : Prop :=
  (A = .sym "Number" ∧ Literal "Number" v) ∨ (A = .sym "String" ∧ Literal "String" v)

theorem classMet_literals : MeetsLiterals ClassMet := by
  rintro k A v (⟨rfl, hv⟩ | ⟨rfl, hv⟩)
  · exact ⟨"Number", rfl, .inl rfl, hv⟩
  · exact ⟨"String", rfl, .inr (.inl rfl), hv⟩

/-- **The class guard is exact**: meeting the guards of a row at `Number` and
`String` by the class of grounded values, and every other guard by the full
guard, gives the row's protocol. -/
theorem classGuard_protocol (body : List Atom → Multiset Atom) (τ : Ty String) (vs : List Atom) :
    chainInline Γ kind ClassMet (ClassMet 0) body τ vs = chainCall Γ kind body τ vs :=
  chainInline_eq classMet_literals (fun _ => classMet_literals 0) body τ vs

/-! ### Elided literal arguments -/

/-- An argument written as a variable or a literal: its value changes no
program. -/
def ValueArg : Atom → Prop
  | .var _ => True
  | .grounded _ => True
  | _ => False

/-- **The guards `oem_build_declared_builtin` elides**: when every argument as
written (`srcs`) is a variable or a literal, the guard of a literal argument at
the symbol of its class (`petta_type_literal_proves`); the literal's value is
the literal. -/
def Elided (srcs : List Atom) (k : ℕ) (A : Ty String) (v : Atom) : Prop :=
  (∀ s ∈ srcs, ValueArg s) ∧ srcs[k]? = some v ∧ ∃ c, A = .sym c ∧ IsValueClass c ∧ Literal c v

theorem elided_literals (srcs : List Atom) : MeetsLiterals (Elided srcs) :=
  fun _ _ _ h => h.2.2

/-- **A declared builtin's compiled protocol is the row's**: elided literal
arguments, class guards on numbers and strings, and the result's class guard,
as `oem_build_declared_builtin` compiles them. -/
theorem declaredBuiltin_protocol (srcs : List Atom) (body : List Atom → Multiset Atom)
    (τ : Ty String) (vs : List Atom) :
    chainInline Γ kind (fun k A v => Elided srcs k A v ∨ ClassMet k A v) (ClassMet 0) body τ vs =
      chainCall Γ kind body τ vs :=
  chainInline_eq ((elided_literals srcs).or classMet_literals) (fun _ => classMet_literals 0)
    body τ vs

end Compiled

/-! ## Steps of a native fold -/

section NativeFold

variable {Γ : Decls} (kind : Atom → String)

/-- **A declared position that every integer meets once**
(`native_fold_position_meets_integers`): `Number`, a type `get-type` never checks
(`%Undefined%`, `_`), or a type variable. `Atom` is not one. -/
def MeetsInts : Ty String → Prop
  | .sym s => s = "Number" ∨ s = "%Undefined%" ∨ s = "_"
  | .var _ => True
  | .app _ => False

/-- An integer value. -/
def IsInt : Atom → Prop
  | .grounded (.int _) => True
  | _ => False

/-- The stores the guards of such a row leave on integers: each equation is
`Number` against `Number` or against a type variable of the row. -/
def IntStore (S : List (Eqn CallVar)) : Prop :=
  ∀ e ∈ S, e.1 = .sym "Number" ∧ (e.2 = .sym "Number" ∨ ∃ x, e.2 = .var (.inl x))

theorem IntStore.sat {S : List (Eqn CallVar)} (h : IntStore S) : Sat S :=
  ⟨fun _ => .sym "Number", fun e he => by
    obtain ⟨h₁, h₂ | ⟨x, h₂⟩⟩ := h e he <;> rw [h₁] <;> simp [h₂]⟩

theorem formal_inl {A : Ty String} (hA : MeetsInts A) (guarded : demand A = .guarded) :
    (A.map Sum.inl : Ty CallVar) = .sym "Number" ∨ ∃ x, (A.map Sum.inl : Ty CallVar) = .var (.inl x) := by
  cases A with
  | var x => exact .inr ⟨x, rfl⟩
  | sym s =>
      rcases hA with rfl | rfl | rfl
      · exact .inl rfl
      · exact absurd guarded (by decide)
      · exact absurd guarded (by decide)
  | app _ => exact hA.elim

open Classical in
/-- **A guard of such a position on an integer continues once**, binding a type
variable to `Number`. -/
theorem guard_int {k : ℕ} {S : List (Eqn CallVar)} (hS : IntStore S) {A : Ty String}
    (hA : MeetsInts A) (guarded : demand A = .guarded) {v : Atom} (hv : IsInt v) (kindName : String) :
    guard (atGuard k) S (A.map Sum.inl) (info Γ v) kindName = {S ++ [(.sym "Number", A.map Sum.inl)]} ∧
      IntStore (S ++ [(.sym "Number", A.map Sum.inl)]) := by
  obtain ⟨n, rfl⟩ : ∃ n, v = .grounded (.int n) := by
    cases v with
    | grounded g => cases g with
      | int n => exact ⟨n, rfl⟩
      | _ => exact hv.elim
    | _ => exact hv.elim
  have store : IntStore (S ++ [(.sym "Number", A.map Sum.inl)]) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hS e he
    · rw [List.mem_singleton] at he
      subst he
      exact ⟨rfl, formal_inl hA guarded⟩
  have heff : eff (info Γ (.grounded (.int n))) = {classDeriv "Number"} := by
    rw [info_int]
    unfold eff
    simp
  have sat : Sat (S ++ (classDeriv "Number").eqs.map (Eqn.map (atGuard k)) ++
      [((classDeriv "Number").ty.map (atGuard k), A.map Sum.inl)]) := by
    simpa [classDeriv] using store.sat
  have one : getType (atGuard k) S (A.map Sum.inl) (info Γ (.grounded (.int n))) =
      {S ++ [(.sym "Number", A.map Sum.inl)]} := by
    rw [getType_of_eff _ _ _ heff, if_pos sat]
    simp [classDeriv]
  refine ⟨?_, store⟩
  rw [guard_of_getType _ _ _ _ _ (by rw [one]; exact Multiset.singleton_ne_zero _), one]

theorem guards_int : ∀ (k : ℕ) (As : List (Ty String)) (vs : List Atom) (S : List (Eqn CallVar)),
    IntStore S → (∀ A ∈ As, MeetsInts A) → (∀ v ∈ vs, IsInt v) → As.length = vs.length →
      ∃ S', IntStore S' ∧ guards Γ kind k As vs S = {S'}
  | _, [], [], S, hS, _, _, _ => ⟨S, hS, rfl⟩
  | k, A :: As, v :: vs, S, hS, hAs, hvs, len => by
      simp only [guards]
      split_ifs with hg
      · obtain ⟨hguard, hS'⟩ := guard_int hS (hAs A (by simp)) hg (hvs v (by simp)) (kind v) (Γ := Γ)
          (k := k)
        rw [hguard, Multiset.singleton_bind]
        exact guards_int (k + 1) As vs _ hS' (fun B hB => hAs B (by simp [hB]))
          (fun w hw => hvs w (by simp [hw])) (by simpa using len)
      · exact guards_int (k + 1) As vs S hS (fun B hB => hAs B (by simp [hB]))
          (fun w hw => hvs w (by simp [hw])) (by simpa using len)
  | _, [], _ :: _, _, _, _, _, len => by simp at len
  | _, _ :: _, [], _, _, _, _, len => by simp at len

/-- **A step declared by one arrow of positions every integer meets has the
body's answers on integers** (`native_fold_step_declarations_numeric`): on integer
arguments and integer answers, each guard of the arrow passes exactly once and
binds type variables only to `Number`, so the protocol of the step's application
is its body, multiplicities included, which a native fold computes. -/
theorem fold_step_protocol (body : List Atom → Multiset Atom) (As : List (Ty String)) (C : Ty String)
    (hAs : ∀ A ∈ As, MeetsInts A) (hC : MeetsInts C) (vs : List Atom) (hvs : ∀ v ∈ vs, IsInt v)
    (len : As.length = vs.length) (answers : ∀ r ∈ body vs, IsInt r) :
    chainCall Γ kind body (arrow As C) vs = body vs := by
  unfold chainCall
  rw [arrowSplit_arrow]
  dsimp only
  obtain ⟨S', hS', hguards⟩ := guards_int (Γ := Γ) kind 0 As vs [] (fun e he => by simp at he) hAs hvs len
  rw [hguards, Multiset.singleton_bind]
  refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
  · unfold resultGuard
    split_ifs with hR
    · have guarded : demand C = .guarded := by
        unfold demand
        rw [if_neg hR.1, if_neg hR.2]
      rw [(guard_int hS' hC guarded (answers r hr) (kind r) (k := As.length)).1, Multiset.map_singleton]
    · rfl
  · rw [Multiset.bind_singleton, Multiset.map_id']

end NativeFold

/-! ## A range written as one parameter's type variable -/

section ValueParameter

variable {Γ : Decls} (kind : Atom → String)

/-- The guards of a row's parameters split at any position. -/
theorem guards_append : ∀ (k : ℕ) (P Q : List (Ty String)) (us ws : List Atom) (S : List (Eqn CallVar)),
    P.length = us.length →
      guards Γ kind k (P ++ Q) (us ++ ws) S = (guards Γ kind k P us S).bind (guards Γ kind (k + P.length) Q ws)
  | k, [], Q, [], ws, S, _ => by simp [guards]
  | k, B :: P, Q, u :: us, ws, S, len => by
      have ih := fun S' => guards_append (k + 1) P Q us ws S' (by simpa using len)
      have idx : k + 1 + P.length = k + (B :: P).length := by simp; omega
      show guards Γ kind k (B :: (P ++ Q)) (u :: (us ++ ws)) S =
        (guards Γ kind k (B :: P) (u :: us) S).bind (guards Γ kind (k + (B :: P).length) Q ws)
      rw [guards, guards]
      split_ifs
      · rw [Multiset.bind_assoc]
        refine Multiset.bind_congr fun S' _ => ?_
        rw [ih S', idx]
      · rw [ih S, idx]
  | _, [], _, _ :: _, _, _, len => by simp at len
  | _, _ :: _, _, [], _, _, len => by simp at len

/-- The parameter count of a closed row splits at any position. -/
theorem argCount_append : ∀ (P Q : List (Ty Empty)) (us ws : List Atom), P.length = us.length →
    argCount Γ kind (P ++ Q) (us ++ ws) = argCount Γ kind P us * argCount Γ kind Q ws
  | [], _, [], _, _ => by simp [argCount]
  | _ :: P, Q, _ :: us, ws, len => by
      simp only [List.cons_append, argCount]
      rw [argCount_append P Q us ws (by simpa using len), mul_assoc]
  | [], _, _ :: _, _, len => by simp at len
  | _ :: _, _, [], _, len => by simp at len

/-- The guards of closed parameters keep a good store good. -/
theorem guards_closed_stores : ∀ (k : ℕ) (As : List (Ty Empty)) (vs : List Atom) (S : List (Eqn CallVar)),
    StoreOK k S → ∀ S' ∈ guards Γ kind k (As.map Ty.lift) vs S, StoreOK (k + As.length) S'
  | k, [], [], S, hS, S', hS' => by
      simp only [List.map_nil, guards, Multiset.mem_singleton] at hS'
      subst hS'
      simpa using hS
  | k, A :: As, v :: vs, S, hS, S', hS' => by
      simp only [List.map_cons, guards] at hS'
      split_ifs at hS'
      · obtain ⟨S₁, h₁, h₂⟩ := Multiset.mem_bind.mp hS'
        rw [lift_map_inl] at h₁
        have := guards_closed_stores (k + 1) As vs S₁ (guard_closed_stores hS A _ _ S₁ h₁) S' h₂
        simpa [Nat.add_assoc, Nat.add_comm 1] using this
      · have := guards_closed_stores (k + 1) As vs S (hS.mono (by omega)) S' hS'
        simpa [Nat.add_assoc, Nat.add_comm 1] using this
  | _, [], _ :: _, _, _, _, h => by simp [guards] at h
  | _, _ :: _, [], _, _, _, h => by simp [guards] at h

/-- Setting the variable to the class: a store that names it as the class, and
equations that do not name it otherwise, are satisfiable as with the class
written in its place. -/
theorem sat_elim_class {S X : List (Eqn CallVar)} {t c : String} {dty : Ty CallVar}
    (hS : ∀ u ∈ eqnVars S, u ≠ .inl t) (hX : ∀ u ∈ eqnVars X, u ≠ .inl t)
    (hd : ∀ u ∈ dty.vars, u ≠ .inl t) :
    Sat (S ++ [(.sym c, .var (.inl t))] ++ X ++ [(dty, .var (.inl t))]) ↔
      Sat (S ++ [(.sym c, .sym c)] ++ X ++ [(dty, .sym c)]) := by
  classical
  constructor
  · rintro ⟨ρ, hρ⟩
    simp only [solves_append, solves_singleton, Ty.bind_sym, Ty.bind_var'] at hρ
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hρ
    refine ⟨ρ, (solves_append _ _ _).mpr ⟨(solves_append _ _ _).mpr ⟨(solves_append _ _ _).mpr
      ⟨h1, (solves_singleton _ _).mpr rfl⟩, h3⟩, (solves_singleton _ _).mpr ?_⟩⟩
    rw [Ty.bind_sym]
    exact h4.trans h2.symm
  · rintro ⟨ρ, hρ⟩
    simp only [solves_append, solves_singleton, Ty.bind_sym] at hρ
    obtain ⟨⟨⟨h1, -⟩, h3⟩, h4⟩ := hρ
    let ρ' : CallVar → Ty Empty := fun u => if u = .inl t then .sym c else ρ u
    have agree : ∀ u, u ≠ .inl t → ρ' u = ρ u := fun u hu => if_neg hu
    refine ⟨ρ', ?_⟩
    simp only [solves_append, solves_singleton, Ty.bind_sym, Ty.bind_var']
    refine ⟨⟨⟨(solves_congr fun u hu => agree u (hS u hu)).mpr h1, by simp [ρ']⟩,
      (solves_congr fun u hu => agree u (hX u hu)).mpr h3⟩, ?_⟩
    rw [Ty.bind_congr dty fun u hu => agree u (hd u hu), h4]
    simp [ρ']

theorem metatype_ne_class (grounded : String → Bool) {c : String} (hc : IsValueClass c) (v : Atom) :
    metatype grounded v ≠ c := by
  rcases hc with rfl | rfl | rfl <;> cases v <;> simp only [metatype] <;> (try split_ifs) <;> decide

open Classical in
/-- **The guard at the variable on a value of the class** binds the variable to
the class, once. -/
theorem guard_var_literal {k : ℕ} {S : List (Eqn CallVar)} (hS : StoreOK k S) {c : String}
    {v : Atom} (hv : Literal c v) (t kindName : String) :
    guard (atGuard k) S ((Ty.var t : Ty String).map Sum.inl) (info Γ v) kindName =
      {S ++ [(.sym c, .var (.inl t))]} := by
  obtain ⟨g, rfl⟩ : ∃ g, v = .grounded g := by
    cases v with
    | grounded g => exact ⟨g, rfl⟩
    | _ => exact (hv : False).elim
  have heff : eff (info Γ (.grounded g)) = {classDeriv c} := by
    rw [info_grounded_class Γ (show valueClass g = some c from hv)]
    unfold eff
    simp
  have sat : Sat (S ++ (classDeriv c).eqs.map (Eqn.map (atGuard k)) ++
      [((classDeriv c).ty.map (atGuard k), (Ty.var (Sum.inl t) : Ty CallVar))]) := by
    obtain ⟨ρ, hρ⟩ := hS.1
    refine ⟨fun u => if u = .inl t then .sym c else ρ u, ?_⟩
    simp only [classDeriv, List.map_nil, List.append_nil, solves_append, solves_singleton, Ty.map_sym,
      Ty.bind_sym, Ty.bind_var']
    refine ⟨(solves_congr fun u hu => ?_).mpr hρ, by simp⟩
    obtain ⟨_, _, _, rfl⟩ := hS.2 u hu
    simp
  have one : getType (atGuard k) S (.var (.inl t)) (info Γ (.grounded g)) =
      {S ++ [(.sym c, .var (.inl t))]} := by
    rw [getType_of_eff _ _ _ heff, if_pos sat]
    simp [classDeriv]
  rw [Ty.map_var, guard_of_getType _ _ _ _ _ (by rw [one]; exact Multiset.singleton_ne_zero _), one]

/-- A value of a class passes the guard at its class once. -/
theorem guardCount_literal (grounded : String → Bool) {c : String} (hc : IsValueClass c) {v : Atom}
    (hv : Literal c v) : guardCount (info Γ v) (.sym c) (metatype grounded v) = 1 := by
  obtain ⟨g, rfl⟩ : ∃ g, v = .grounded g := by
    cases v with
    | grounded g => exact ⟨g, rfl⟩
    | _ => exact (hv : False).elim
  rw [guardCount_classTest Γ grounded hc (show Simple (.grounded g) from by
    simp [Simple, show valueClass g = some c from hv]), if_pos (show ClassTest c (.grounded g) from hv)]

/-! ### At any position, with closed parameters after it -/

/-- Stores of the open row and of its instance at the class: the open one names
the variable as the class, the instance writes the class in its place. -/
def ClassPair (t c : String) (So Sc : List (Eqn CallVar)) : Prop :=
  ∃ S X : List (Eqn CallVar), So = S ++ [(.sym c, .var (.inl t))] ++ X ∧ Sc = S ++ [(.sym c, .sym c)] ++ X ∧
    (∀ u ∈ eqnVars S, u ≠ .inl t) ∧ ∀ u ∈ eqnVars X, u ≠ .inl t

/-- Setting the variable to the class in a store whose other equations do not
name it. -/
theorem sat_elim_class_store {S X : List (Eqn CallVar)} {t c : String}
    (hS : ∀ u ∈ eqnVars S, u ≠ .inl t) (hX : ∀ u ∈ eqnVars X, u ≠ .inl t) :
    Sat (S ++ [(.sym c, .var (.inl t))] ++ X) ↔ Sat (S ++ [(.sym c, .sym c)] ++ X) := by
  classical
  constructor
  · rintro ⟨ρ, hρ⟩
    simp only [solves_append, solves_singleton] at hρ
    exact ⟨ρ, (solves_append _ _ _).mpr ⟨(solves_append _ _ _).mpr ⟨hρ.1.1,
      (solves_singleton _ _).mpr rfl⟩, hρ.2⟩⟩
  · rintro ⟨ρ, hρ⟩
    simp only [solves_append, solves_singleton] at hρ
    let ρ' : CallVar → Ty Empty := fun u => if u = .inl t then .sym c else ρ u
    have agree : ∀ u, u ≠ .inl t → ρ' u = ρ u := fun u hu => if_neg hu
    refine ⟨ρ', (solves_append _ _ _).mpr ⟨(solves_append _ _ _).mpr
      ⟨(solves_congr fun u hu => agree u (hS u hu)).mpr hρ.1.1, (solves_singleton _ _).mpr ?_⟩,
      (solves_congr fun u hu => agree u (hX u hu)).mpr hρ.2⟩⟩
    simp [ρ']

theorem ClassPair.append {t c : String} {So Sc : List (Eqn CallVar)} (h : ClassPair t c So Sc)
    (Y : List (Eqn CallVar)) (hY : ∀ u ∈ eqnVars Y, u ≠ .inl t) : ClassPair t c (So ++ Y) (Sc ++ Y) := by
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  refine ⟨S, X ++ Y, by simp, by simp, hS, fun u hu => ?_⟩
  rw [eqnVars_append, List.mem_append] at hu
  exact hu.elim (hX u) (hY u)

theorem ClassPair.sat_iff {t c : String} {So Sc : List (Eqn CallVar)} (h : ClassPair t c So Sc) :
    Sat So ↔ Sat Sc := by
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  exact sat_elim_class_store hS hX

open Classical in
/-- A closed parameter's guard on paired stores answers paired stores, one for
one. -/
theorem guard_closed_pair {k : ℕ} {t c : String} {So Sc : List (Eqn CallVar)} (h : ClassPair t c So Sc)
    (A : Ty Empty) (j : Info) (kindName : String) :
    Multiset.Rel (ClassPair t c) (guard (atGuard k) So A.lift j kindName) (guard (atGuard k) Sc A.lift j kindName) := by
  have ext : ∀ d : Deriv, ∀ u ∈ eqnVars (d.eqs.map (Eqn.map (atGuard k)) ++ [(d.ty.map (atGuard k), A.lift)]),
      u ≠ .inl t := by
    intro d u hu
    rw [eqnVars_append, List.mem_append, eqnVars_map] at hu
    rcases hu with hu | hu
    · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hu
      simp [atGuard]
    · simp only [eqnVars, Eqn.vars, List.flatMap_cons, List.flatMap_nil, List.append_nil, Ty.vars_lift,
        Ty.vars_map, List.mem_map] at hu
      obtain ⟨w, -, rfl⟩ := hu
      simp [atGuard]
  have rel : Multiset.Rel (ClassPair t c) (getType (atGuard k) So A.lift j) (getType (atGuard k) Sc A.lift j) := by
    unfold getType
    rw [Multiset.filter_map, Multiset.filter_map]
    have same : (eff j).filter (Sat ∘ fun d => So ++ d.eqs.map (Eqn.map (atGuard k)) ++
        [(d.ty.map (atGuard k), A.lift)]) =
        (eff j).filter (Sat ∘ fun d => Sc ++ d.eqs.map (Eqn.map (atGuard k)) ++
          [(d.ty.map (atGuard k), A.lift)]) :=
      Multiset.filter_congr fun d _ => by
        simp only [Function.comp, List.append_assoc]
        exact (h.append _ (ext d)).sat_iff
    rw [same, Multiset.rel_map]
    refine Multiset.rel_refl_of_refl_on fun d _ => ?_
    simp only [List.append_assoc]
    exact h.append _ (ext d)
  unfold guard
  rw [Multiset.card_eq_card_of_rel rel]
  split_ifs
  · have hY : ∀ u ∈ eqnVars [((Ty.sym kindName : Ty CallVar), (A.lift : Ty CallVar))], u ≠ .inl t := by
      simp [eqnVars, Eqn.vars]
    rw [Multiset.filter_singleton, Multiset.filter_singleton]
    by_cases hs : Sat (So ++ [(.sym kindName, A.lift)])
    · rw [if_pos hs, if_pos ((h.append _ hY).sat_iff.mp hs)]
      exact .cons (h.append _ hY) .zero
    · rw [if_neg hs, if_neg fun hs' => hs ((h.append _ hY).sat_iff.mpr hs')]
      exact .zero
  · exact rel

/-- So do the guards of closed parameters. -/
theorem guards_closed_pair {t c : String} : ∀ (k : ℕ) (As : List (Ty Empty)) (vs : List Atom)
    {So Sc : List (Eqn CallVar)}, ClassPair t c So Sc →
      Multiset.Rel (ClassPair t c) (guards Γ kind k (As.map Ty.lift) vs So) (guards Γ kind k (As.map Ty.lift) vs Sc)
  | _, [], [], _, _, h => .cons h .zero
  | k, A :: As, v :: vs, So, Sc, h => by
      simp only [List.map_cons, guards]
      split_ifs
      · exact Multiset.rel_bind (fun _ _ hab => guards_closed_pair (k + 1) As vs hab)
          (by rw [lift_map_inl]; exact guard_closed_pair h A _ _)
      · exact guards_closed_pair (k + 1) As vs h
  | _, [], _ :: _, _, _, _ => by simp only [List.map_nil, guards]; exact .zero
  | _, _ :: _, [], _, _, _ => by simp only [List.map_cons, guards]; exact .zero

open Classical in
/-- **The result guard at the variable** on the open row's store is the result
guard at the class on the instance's. -/
theorem resultGuard_pair (grounded : String → Bool) {k : ℕ} {t c : String} (hc : IsValueClass c)
    {So Sc : List (Eqn CallVar)} (h : ClassPair t c So Sc) (r : Atom) :
    resultGuard Γ (metatype grounded) k (.var t) So r =
      resultGuard Γ (metatype grounded) k ((Ty.sym c : Ty Empty).lift) Sc r := by
  obtain ⟨S, X, rfl, rfl, hS, hX⟩ := h
  have rgVar : ResultGuarded (Ty.var t : Ty String) := by
    refine ⟨?_, ?_⟩ <;> simp [Unchecked]
  have rgCls : ResultGuarded ((Ty.sym c : Ty Empty).lift : Ty String) := by
    rcases hc with rfl | rfl | rfl <;> decide
  unfold resultGuard
  rw [if_pos rgVar, if_pos rgCls, Multiset.map_const', Multiset.map_const']
  congr 1
  have extVars : ∀ d : Deriv, ∀ u ∈ eqnVars (X ++ d.eqs.map (Eqn.map (atGuard k))), u ≠ .inl t := by
    intro d u hu
    rw [eqnVars_append, List.mem_append] at hu
    rcases hu with hu | hu
    · exact hX u hu
    · rw [eqnVars_map, List.mem_map] at hu
      obtain ⟨w, -, rfl⟩ := hu
      simp [atGuard]
  have cardEq : Multiset.card (getType (atGuard k) (S ++ [(.sym c, .var (.inl t))] ++ X)
      (.var (.inl t)) (info Γ r)) =
      Multiset.card (getType (atGuard k) (S ++ [(.sym c, .sym c)] ++ X) (.sym c) (info Γ r)) := by
    unfold getType
    rw [Multiset.filter_map, Multiset.filter_map, Multiset.card_map, Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun d _ => ?_
    simp only [Function.comp]
    have := sat_elim_class (S := S) (X := X ++ d.eqs.map (Eqn.map (atGuard k))) (t := t) (c := c)
      (dty := d.ty.map (atGuard k)) hS (extVars d) (fun u hu => by
        rw [Ty.vars_map, List.mem_map] at hu
        obtain ⟨w, -, rfl⟩ := hu
        simp [atGuard])
    simpa only [List.append_assoc] using this
  have neq := metatype_ne_class grounded hc r
  rw [Ty.map_var, show ((Ty.sym c : Ty Empty).lift : Ty String).map Sum.inl = (.sym c : Ty CallVar) from rfl]
  unfold guard
  rw [cardEq]
  split_ifs with h0
  · rw [Multiset.filter_singleton, Multiset.filter_singleton, if_neg, if_neg]
    · rintro ⟨ρ, hρ⟩
      simp only [solves_append, solves_singleton, Ty.bind_sym] at hρ
      exact neq (Ty.sym.inj hρ.2)
    · rintro ⟨ρ, hρ⟩
      simp only [solves_append, solves_singleton, Ty.bind_sym, Ty.bind_var'] at hρ
      exact neq (Ty.sym.inj (hρ.2.trans hρ.1.1.2.symm))
  · exact cardEq

/-- Related bags bind to one bag under functions that agree on related elements. -/
theorem bind_rel {α β : Type} {r : α → α → Prop} {s t : Multiset α} (h : Multiset.Rel r s t)
    (f g : α → Multiset β) (hfg : ∀ a b, r a b → f a = g b) : s.bind f = t.bind g := by
  rw [← Multiset.rel_eq]
  exact Multiset.rel_bind (fun a b hab => by rw [hfg a b hab]; exact Multiset.rel_eq.mpr rfl) h

/-- **A range written as one parameter's type variable, at any position**
(`prepared_pure_parameter_range_variable`): at `(-> A₁ … $t … Aₖ $t)`, every `Aᵢ`
closed and `$t` named nowhere else, on an argument there that is a value of the
class `c`, the protocol is the protocol of the row with `c` written for `$t`: the
closed parameters' checks, the body, each answer checked at `c`. -/
theorem value_parameter_protocol_at (grounded : String → Bool) (body : List Atom → Multiset Atom)
    (pre post : List (Ty Empty)) (t c : String) (hc : IsValueClass c) (us : List Atom) (v : Atom)
    (vs : List Atom) (hv : Literal c v) (len : pre.length = us.length) :
    chainCall Γ (metatype grounded) body (arrow (pre.map Ty.lift ++ .var t :: post.map Ty.lift) (.var t))
        (us ++ v :: vs) =
      chainCall Γ (metatype grounded) body
        (arrow ((pre ++ .sym c :: post).map Ty.lift) (Ty.sym c : Ty Empty).lift) (us ++ v :: vs) := by
  unfold chainCall
  rw [arrowSplit_arrow, arrowSplit_arrow]
  dsimp only
  rw [List.map_append, List.map_cons,
    guards_append _ 0 _ _ _ _ _ (by simpa using len), guards_append _ 0 _ _ _ _ _ (by simpa using len),
    Multiset.bind_assoc, Multiset.bind_assoc]
  refine Multiset.bind_congr fun S hS => ?_
  have hS' := guards_closed_stores (Γ := Γ) (metatype grounded) 0 pre us [] StoreOK.nil S hS
  rw [Nat.zero_add] at hS'
  have svars : ∀ u ∈ eqnVars S, u ≠ .inl t := fun u hu => by
    obtain ⟨_, _, _, rfl⟩ := hS'.2 u hu
    simp
  have guardedVar : demand (Ty.var t : Ty String) = .guarded := by
    unfold demand
    rw [if_neg (fun h => by cases h), if_neg (show ¬ Unchecked (Ty.var t : Ty String) from fun h => h)]
  have guardedCls : demand ((Ty.sym c : Ty Empty).lift : Ty String) = .guarded := by
    rcases hc with rfl | rfl | rfl <;> decide
  simp only [guards, guardedVar, guardedCls, if_true, Nat.zero_add, List.length_map,
    List.length_cons, List.length_append]
  rw [guard_var_literal hS' hv t (metatype grounded v), Multiset.singleton_bind,
    show ((Ty.sym c : Ty Empty).lift : Ty String).map Sum.inl = (.sym c : Ty CallVar) from rfl,
    guard_literal _ hS'.1 hv Γ (metatype grounded v), Multiset.singleton_bind]
  have pair : ClassPair t c (S ++ [(.sym c, .var (.inl t))]) (S ++ [(.sym c, .sym c)]) :=
    ⟨S, [], by simp, by simp, svars, by simp [eqnVars]⟩
  refine bind_rel (guards_closed_pair (metatype grounded) (pre.length + 1) post vs pair) _ _ fun So Sc hp => ?_
  exact Multiset.bind_congr fun r _ => resultGuard_pair grounded hc hp r

/-- **A range written as the last parameter's type variable**
(`PREPARED_PURE_VALUE_PARAMETER`): at `(-> A₁ … Aₖ $t $t)`, on a last argument
that is a value of the class `c`, the protocol is the closed parameters' checks,
the body, and each answer checked at `c`, as the machine runs it. -/
theorem value_parameter_protocol (grounded : String → Bool) (body : List Atom → Multiset Atom)
    (pre : List (Ty Empty)) (t c : String) (hc : IsValueClass c) (us : List Atom) (v : Atom)
    (hv : Literal c v) (len : pre.length = us.length) :
    chainCall Γ (metatype grounded) body (arrow (pre.map Ty.lift ++ [.var t]) (.var t)) (us ++ [v]) =
      argCount Γ (metatype grounded) pre us • (body (us ++ [v])).bind fun r =>
        guardCount (info Γ r) (.sym c) (metatype grounded r) • {r} := by
  have h := value_parameter_protocol_at (Γ := Γ) grounded body pre [] t c hc us v [] hv len
  rw [List.map_nil] at h
  rw [h, chainCall_closed, argCount_append _ _ _ _ _ len]
  have rg : ResultGuarded ((Ty.sym c : Ty Empty).lift : Ty String) := by
    rcases hc with rfl | rfl | rfl <;> decide
  simp only [argCount, guardCount_literal grounded hc hv, mul_one, if_pos rg, ite_self]

end ValueParameter

/-! ## Programs with `get-type` rules -/

/-- The answers authored `get-type` rules add to a value's own:
`(= (get-type 3) Number)` adds `Number` to the answers for `3`, so CeTTa's
`get-type` of `3` answers `(Number Number)`. -/
abbrev Rules := Atom → Multiset (Ty Empty)

/-- The guard at a closed request in a program with rules: one continuation per
answer of the relation or of the rules at the request, the metatype only when
there is none. -/
noncomputable def guardCountWith (rules : Rules) (Γ : Decls) (v : Atom) (T : Ty Empty)
    (kindName : String) : ℕ :=
  if count (info Γ v) T + (rules v).count T = 0 then (if T = .sym kindName then 1 else 0)
  else count (info Γ v) T + (rules v).count T

/-- The argument guards of a closed row in a program with rules. -/
noncomputable def argCountWith (rules : Rules) (Γ : Decls) (kind : Atom → String) :
    List (Ty Empty) → List Atom → ℕ
  | [], [] => 1
  | A :: As, v :: vs =>
      (if demand A.lift = .guarded then guardCountWith rules Γ v A (kind v) else 1) *
        argCountWith rules Γ kind As vs
  | [], _ :: _ => 0
  | _ :: _, [] => 0

/-- The protocol of a closed row with a guarded result in a program with rules. -/
noncomputable def chainCallWith (rules : Rules) (Γ : Decls) (kind : Atom → String)
    (body : List Atom → Multiset Atom) (As : List (Ty Empty)) (R : Ty Empty) (vs : List Atom) :
    Multiset Atom :=
  argCountWith rules Γ kind As vs • (body vs).bind fun r => guardCountWith rules Γ r R (kind r) • {r}

theorem guardCountWith_none (Γ : Decls) (v : Atom) (T : Ty Empty) (kindName : String) :
    guardCountWith (fun _ => 0) Γ v T kindName = guardCount (info Γ v) T kindName := by
  simp [guardCountWith, guardCount]

theorem argCountWith_none (Γ : Decls) (kind : Atom → String) :
    ∀ (As : List (Ty Empty)) (vs : List Atom), argCountWith (fun _ => 0) Γ kind As vs = argCount Γ kind As vs
  | [], [] => rfl
  | A :: As, v :: vs => by
      simp only [argCountWith, argCount, guardCountWith_none, argCountWith_none Γ kind As vs]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

/-- **Without rules the protocol is the model's.** -/
theorem chainCallWith_none (Γ : Decls) (kind : Atom → String) (body : List Atom → Multiset Atom)
    (As : List (Ty Empty)) (R : Ty Empty) (hR : ResultGuarded R.lift) (vs : List Atom) :
    chainCallWith (fun _ => 0) Γ kind body As R vs = chainCall Γ kind body (arrow (As.map Ty.lift) R.lift) vs := by
  rw [chainCall_closed, chainCallWith, argCountWith_none]
  simp only [if_pos hR, guardCountWith_none]

/-! ## Arguments typed by their callee -/

section Callee

variable {Γ : Decls} (kind : Atom → String)

/-- **A guard on values that passed it is no guard**: when every answer of an
argument passed a guard at the closed type `A`, weighting any continuation by
that guard again changes no answer and no multiplicity. -/
theorem bind_guard_passed (hΓ : Functional Γ) {A : Ty Empty} {ws : Multiset Atom}
    (passed : ∀ w ∈ ws, guardCount (info Γ w) A (kind w) ≠ 0) {β : Type} (K : Atom → Multiset β) :
    (ws.bind fun w => guardCount (info Γ w) A (kind w) • K w) = ws.bind K := by
  refine Multiset.bind_congr fun w hw => ?_
  have le := guardCount_le_one hΓ w A (kind w)
  have one : guardCount (info Γ w) A (kind w) = 1 := by have := passed w hw; omega
  rw [one, one_nsmul]

open Classical in
/-- A guard at a closed type that continues at all, under any store, has a
positive count without the store. -/
theorem guard_closed_passed {U : Type} (e : DVar → U) (S : List (Eqn U)) (R : Ty Empty) (j : Info)
    (kindName : String) {S' : List (Eqn U)} (h : S' ∈ guard e S (R.lift) j kindName) :
    guardCount j R kindName ≠ 0 := by
  unfold guard at h
  split_ifs at h with h0
  · obtain ⟨hmem, ρ, hρ⟩ := Multiset.mem_filter.mp h
    rw [Multiset.mem_singleton] at hmem
    subst hmem
    rw [solves_append, solves_singleton, Ty.bind_sym, Ty.lift_bind_ground] at hρ
    unfold guardCount
    split_ifs with hc hR
    · exact one_ne_zero
    · exact absurd hρ.2.symm hR
    · exact hc
  · unfold getType at h
    obtain ⟨hmem, ρ, hρ⟩ := Multiset.mem_filter.mp h
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hmem
    rw [solves_append, solves_append, solves_singleton] at hρ
    have pos : count j R ≠ 0 := by
      unfold count
      refine Nat.pos_iff_ne_zero.mp (Multiset.card_pos_iff_exists_mem.mpr
        ⟨d, Multiset.mem_filter.mpr ⟨hd, ρ ∘ e, (solves_append _ _ _).mpr
          ⟨(solves_map ρ e _).mp hρ.1.2, (solves_singleton _ _).mpr ?_⟩⟩⟩)
      have := hρ.2
      rw [Ty.bind_map, Ty.lift_bind_ground] at this
      rw [Ty.lift_bind_ground]
      exact this
    unfold guardCount
    rw [if_neg pos]
    exact pos

/-- **Every answer of a call whose range is a closed guarded type passed its
result guard** there, whatever its formals. -/
theorem chainCall_answers_passed (body : List Atom → Multiset Atom) (Bs : List (Ty String))
    (R : Ty Empty) (hR : ResultGuarded R.lift) (us : List Atom) :
    ∀ w ∈ chainCall Γ kind body (arrow Bs R.lift) us, guardCount (info Γ w) R (kind w) ≠ 0 := by
  intro w hw
  unfold chainCall at hw
  rw [arrowSplit_arrow] at hw
  obtain ⟨S, -, hw⟩ := Multiset.mem_bind.mp hw
  obtain ⟨r, -, hw⟩ := Multiset.mem_bind.mp hw
  unfold resultGuard at hw
  rw [if_pos hR, lift_map_inl] at hw
  obtain ⟨S', hS', rfl⟩ := Multiset.mem_map.mp hw
  exact guard_closed_passed _ _ R _ _ hS'

/-- The type of a parameter that is not checked. -/
def uncheckedTy : Ty Empty := .sym "%Undefined%"

theorem argCount_drop (pre : List (Ty Empty)) (A : Ty Empty) (post : List (Ty Empty))
    (us : List Atom) (w : Atom) (vs : List Atom) (len : pre.length = us.length) :
    argCount Γ kind (pre ++ A :: post) (us ++ w :: vs) =
      (if demand A.lift = .guarded then guardCount (info Γ w) A (kind w) else 1) *
        argCount Γ kind (pre ++ uncheckedTy :: post) (us ++ w :: vs) := by
  induction pre generalizing us with
  | nil =>
      cases us with
      | nil =>
          have unchecked : demand (uncheckedTy.lift : Ty String) ≠ .guarded := by decide
          simp only [List.nil_append, argCount, if_neg unchecked, one_mul]
      | cons _ _ => simp at len
  | cons B pre ih =>
      cases us with
      | nil => simp at len
      | cons u us =>
          simp only [List.cons_append, argCount]
          rw [ih us (by simpa using len)]
          ring

/-- **An argument typed by its callee needs no check**
(`petta_machine_argument_typed_by_callee`): on the answers of an argument that
each passed a guard at the closed formal `A`, as the answers of a call whose
range is `A` did, the protocol of a closed row has the answers, with their
multiplicities, of the same row with that parameter not checked. -/
theorem argument_typed_by_callee (hΓ : Functional Γ) (body : List Atom → Multiset Atom)
    (pre post : List (Ty Empty)) (A R : Ty Empty) (us vs : List Atom) (len : pre.length = us.length)
    {ws : Multiset Atom} (passed : ∀ w ∈ ws, guardCount (info Γ w) A (kind w) ≠ 0) :
    (ws.bind fun w => chainCall Γ kind body (arrow ((pre ++ A :: post).map Ty.lift) R.lift)
        (us ++ w :: vs)) =
      ws.bind fun w => chainCall Γ kind body (arrow ((pre ++ uncheckedTy :: post).map Ty.lift) R.lift)
        (us ++ w :: vs) := by
  refine Multiset.bind_congr fun w hw => ?_
  rw [chainCall_closed, chainCall_closed, argCount_drop kind pre A post us w vs len]
  have le := guardCount_le_one hΓ w A (kind w)
  have one : guardCount (info Γ w) A (kind w) = 1 := by have := passed w hw; omega
  split_ifs <;> simp [one]

end Callee

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional num str sym)

/-- The answers of PeTTa's `+` where it does not raise: the sum of two numbers.
On a string or a variable it raises. -/
def plusOp : List Atom → Multiset Atom
  | [.grounded (.int m), .grounded (.int n)] => {.grounded (.int (m + n))}
  | _ => 0

/-- The declared row `(-> Number Number Number)`. -/
abbrev plusRow : Ty String :=
  arrow ((["Number", "Number"].map fun c => (.sym c : Ty Empty)).map Ty.lift)
    (Ty.sym "Number" : Ty Empty).lift

/-- **Typed `+`**: `(+ 1 2)` answers `3`; `(+ "a" 1)` fails its class test, so it
answers nothing and the builtin, which would raise, never runs; `(+ $v 1)`
passes, so the builtin runs on a variable and raises, as in the probes. -/
theorem typed_plus (grounded : String → Bool) :
    chainCall decls (metatype grounded) plusOp plusRow [num 1, num 2] = {num 3} ∧
      (∀ body : List Atom → Multiset Atom,
        chainCall decls (metatype grounded) body plusRow [str "a", num 1] = 0) ∧
      argCount decls (metatype grounded) ((["Number", "Number"].map fun c => (.sym c : Ty Empty)))
        [.var "v", num 1] = 1 := by
  refine ⟨?_, fun body => ?_, ?_⟩
  · rw [inline_eq_protocol decls grounded plusOp _ _ _ (by decide) (by decide) (by decide)
      (by intro r hr; simp [plusOp] at hr; subst hr; decide)]
    decide
  · exact chainCall_of_test_fails decls grounded body _ _ _ (by decide) (by decide) (by decide)
  · exact (argCount_classes_eq_one_iff decls grounded _ _ (by decide) (by decide)).mpr (by decide)

theorem count_symbol_undeclared (Γ : Decls) (s : String) (h : Γ s = []) (T : Ty Empty)
    (hT : T ≠ .sym "%Undefined%") : count (info Γ (.symbol s)) T = 0 := by
  classical
  unfold count
  rw [info_symbol, h]
  unfold eff
  simp only [List.map_nil, Multiset.coe_nil, Multiset.card_zero, if_true, Multiset.filter_singleton]
  rw [if_neg]
  · rfl
  · rintro ⟨σ, hσ⟩
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hσ
    exact hT hσ.2.symm

/-- **A symbol's guard reads the declarations**: with `(: a Number)` the guard of
`a` at `Number` passes, without it the guard fails, so no test of the value's
kind decides it. -/
theorem symbol_guard_reads_declarations (grounded : String → Bool) :
    guardCount (info (fun s => if s = "a" then [(Ty.sym "Number" : Ty Empty).lift] else []) (sym "a"))
        (.sym "Number") (metatype grounded (sym "a")) = 1 ∧
      guardCount (info decls (sym "a")) (.sym "Number") (metatype grounded (sym "a")) = 0 := by
  have notMeta : (Ty.sym "Number" : Ty Empty) ≠ .sym (metatype grounded (sym "a")) := by
    simp only [metatype]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [guardCount_of_ne _ _ _ notMeta, count_symbol_closed _ "a" (.sym "Number") (by simp),
      if_pos rfl]
  · rw [guardCount_of_ne _ _ _ notMeta, count_symbol_undeclared decls "a"
      (by simp [TypedCalls.Controls.decls]) _ (by simp)]

/-- **Distinct rows are alternatives**: with `(: + (-> Number Number Number))` and
`(: + (-> String String String))`, a call runs both rows' protocols, so the
inline protocol of one row is not the call. -/
theorem distinct_rows_add (grounded : String → Bool) (body : List Atom → Multiset Atom)
    (vs : List Atom) :
    typedCall decls (metatype grounded) body
        [plusRow, arrow ((["String", "String"].map fun c => (.sym c : Ty Empty)).map Ty.lift)
          (Ty.sym "String" : Ty Empty).lift] vs =
      chainCall decls (metatype grounded) body plusRow vs +
        chainCall decls (metatype grounded) body
          (arrow ((["String", "String"].map fun c => (.sym c : Ty Empty)).map Ty.lift)
            (Ty.sym "String" : Ty Empty).lift) vs := by
  rw [typedCall_cons_fresh _ _ _ _ _ (by intro σ hσ; simp at hσ; subst hσ; decide), typedCall_single]

/-! ### The compiled tier -/

/-- The rule `(= (get-type 3) Number)`. -/
def ruleThree : Rules := fun v => if v = num 3 then {.sym "Number"} else 0

/-- The body of `(= (f $x) $x)`. -/
def idBody : List Atom → Multiset Atom
  | [v] => {v}
  | _ => 0

theorem count_three : count (info decls (num 3)) (.sym "Number") = 1 := by
  rw [count_class decls (g := .int 3) rfl, if_pos rfl]

/-- **The class guard meets literals of its class only**: a number at `Number` and
a string at `String`; a variable, a symbol, an expression and a number at
`String` take the full guard. -/
theorem classMet_cases :
    ClassMet 0 (.sym "Number") (num 3) ∧ ClassMet 0 (.sym "String") (str "s") ∧
      ¬ ClassMet 0 (.sym "Number") (.var "x") ∧ ¬ ClassMet 0 (.sym "Number") (sym "a") ∧
      ¬ ClassMet 0 (.sym "Number") (.expression [sym "a"]) ∧
      ¬ ClassMet 0 (.sym "String") (num 3) := by
  refine ⟨.inl ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [ClassMet, Literal, valueClass]

/-- **Elision needs every argument written as a variable or a literal**: in
`(+ 1 2)` both guards are elided; in `(+ (f) 2)` neither is. -/
theorem elided_cases :
    Elided [num 1, num 2] 0 (.sym "Number") (num 1) ∧ Elided [num 1, num 2] 1 (.sym "Number") (num 2) ∧
      ¬ Elided [app "f" [], num 2] 1 (.sym "Number") (num 2) := by
  refine ⟨⟨by simp [ValueArg], rfl, "Number", rfl, .inl rfl, rfl⟩,
    ⟨by simp [ValueArg], rfl, "Number", rfl, .inl rfl, rfl⟩, ?_⟩
  rintro ⟨values, -⟩
  exact values (app "f" []) (by simp)

/-- **A `get-type` rule breaks the class verdict.** With `(= (get-type 3) Number)`
the guard of `3` at `Number` continues twice, so `(f 3)`, for `(: f (-> Number
Number))` and `(= (f $x) $x)`, answers `3` four times, as CeTTa does; the
compiled protocol of the program without the rule answers it once. A verdict
that literals have only their class holds of one program: the program the
guard reads. -/
theorem rule_breaks_class_verdict (grounded : String → Bool) :
    guardCountWith ruleThree decls (num 3) (.sym "Number") (metatype grounded (num 3)) = 2 ∧
      chainCallWith ruleThree decls (metatype grounded) idBody [.sym "Number"] (.sym "Number")
        [num 3] = {num 3, num 3, num 3, num 3} ∧
      chainInline decls (metatype grounded) ClassMet (ClassMet 0) idBody
        (arrow [.sym "Number"] (.sym "Number")) [num 3] = {num 3} := by
  have two : guardCountWith ruleThree decls (num 3) (.sym "Number") (metatype grounded (num 3)) = 2 := by
    simp only [guardCountWith, count_three, ruleThree]
    rfl
  refine ⟨two, ?_, ?_⟩
  · have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
    simp only [chainCallWith, argCountWith, guarded, if_true, two, mul_one, idBody,
      Multiset.singleton_bind]
    decide
  · rw [classGuard_protocol, show (arrow [.sym "Number"] (.sym "Number") : Ty String) =
      arrow (([.sym "Number"] : List (Ty Empty)).map Ty.lift) (Ty.sym "Number" : Ty Empty).lift
      from rfl, chainCall_closed]
    have notMeta : (Ty.sym "Number" : Ty Empty) ≠ .sym (metatype grounded (num 3)) := by
      simp [metatype]
    have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
    simp only [argCount, guarded, if_true, guardCount_of_ne _ _ _ notMeta, count_three, mul_one,
      one_nsmul, idBody, Multiset.singleton_bind]
    rw [if_pos (by decide)]

/-! ### Arguments typed by their callee -/

/-- `(: g (-> Number))`. -/
abbrev gRow : Ty String := arrow (([] : List (Ty Empty)).map Ty.lift) (Ty.sym "Number" : Ty Empty).lift

theorem number_guarded : ResultGuarded ((Ty.sym "Number" : Ty Empty).lift) := by decide

theorem not_meta_number (grounded : String → Bool) (v : Atom) :
    (Ty.sym "Number" : Ty Empty) ≠ .sym (metatype grounded v) := by
  cases v <;> simp only [metatype] <;> try split_ifs
  all_goals simp

/-- **The callee's own check**: a body answering `"a"` at the range `Number` has
no answer through `g`'s protocol; a nondeterministic body's answers `1`, `2`,
`2` pass once each; an unbound variable passes once. -/
theorem callee_cases (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {str "a"}) gRow [] = 0 ∧
      chainCall decls (metatype grounded) (fun _ => {num 1, num 2, num 2}) gRow [] =
        {num 1, num 2, num 2} ∧
      chainCall decls (metatype grounded) (fun _ => {.var "x"}) gRow [] = {.var "x"} := by
  have once : ∀ v, count (info decls v) (.sym "Number") = 1 →
      guardCount (info decls v) (.sym "Number") (metatype grounded v) = 1 := fun v hv => by
    rw [guardCount_of_ne _ _ _ (not_meta_number grounded v), hv]
  have numOnce : ∀ n : ℤ, guardCount (info decls (num n)) (.sym "Number") (metatype grounded (num n)) = 1 :=
    fun n => once _ (by rw [count_class decls (g := .int n) rfl, if_pos rfl])
  have strNone : guardCount (info decls (str "a")) (.sym "Number") (metatype grounded (str "a")) = 0 := by
    rw [guardCount_of_ne _ _ _ (not_meta_number grounded _), count_class decls (g := .string "a") rfl]
    decide
  refine ⟨?_, ?_, ?_⟩
  · rw [chainCall_closed]
    simp only [argCount, one_nsmul, if_pos number_guarded, Multiset.singleton_bind, strNone, zero_nsmul]
  · rw [chainCall_closed]
    simp only [argCount, one_nsmul, if_pos number_guarded, Multiset.insert_eq_cons,
      Multiset.cons_bind, Multiset.singleton_bind, numOnce]
    rfl
  · rw [chainCall_closed]
    simp only [argCount, one_nsmul, if_pos number_guarded, Multiset.singleton_bind]
    rw [once _ (count_var decls "x" _), one_nsmul]

/-- **`(f (g))` needs no check of `(g)`**: for every body of `g`, the call
`(f (g))` with `f`'s argument guard has the answers, multiplicities included, of
the call without it. -/
theorem drop_after_callee (grounded : String → Bool) (body : List Atom → Multiset Atom) :
    ((chainCall decls (metatype grounded) body gRow []).bind fun w =>
        chainCall decls (metatype grounded) idBody
          (arrow ([Ty.sym "Number"].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) [w]) =
      (chainCall decls (metatype grounded) body gRow []).bind fun w =>
        chainCall decls (metatype grounded) idBody
          (arrow ([uncheckedTy].map Ty.lift) (Ty.sym "Number" : Ty Empty).lift) [w] :=
  argument_typed_by_callee (metatype grounded) decls_functional idBody [] [] _ _ [] [] rfl
    (chainCall_answers_passed (metatype grounded) body [] _ number_guarded [])

/-- **Without the program condition the counts differ**: with
`(= (get-type 3) Number)`, `g` answering `3` passes its own result guard twice,
and the argument's guard of `(f (g))`, for `(: f (-> Number Number))` and
`(= (f $x) $x)`, counts each of those answers twice again, eight answers in all,
where the call without the argument's guard has four. -/
theorem rule_breaks_callee_discharge (grounded : String → Bool) :
    Multiset.card ((chainCallWith ruleThree decls (metatype grounded) (fun _ => {num 3}) [] (.sym "Number")
        []).bind fun w => chainCallWith ruleThree decls (metatype grounded) idBody [.sym "Number"]
          (.sym "Number") [w]) = 8 ∧
      Multiset.card ((chainCallWith ruleThree decls (metatype grounded) (fun _ => {num 3}) []
        (.sym "Number") []).bind fun w => chainCallWith ruleThree decls (metatype grounded) idBody
          [uncheckedTy] (.sym "Number") [w]) = 4 := by
  have two := (rule_breaks_class_verdict grounded).1
  have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
  have unchecked : demand (uncheckedTy.lift : Ty String) ≠ .guarded := by decide
  have g : chainCallWith ruleThree decls (metatype grounded) (fun _ => {num 3}) [] (.sym "Number") [] =
      2 • {num 3} := by
    simp only [chainCallWith, argCountWith, one_nsmul, Multiset.singleton_bind, two]
  rw [g]
  simp only [chainCallWith, argCountWith, idBody, if_pos guarded, if_neg unchecked,
    Multiset.singleton_bind, mul_one]
  simp only [Multiset.card_bind, Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
    Multiset.sum_singleton, Function.comp_apply]
  simp only [Multiset.card_nsmul, Multiset.card_singleton, two]
  decide

/-! ### A range written as a parameter's variable, first -/

/-- **`$t` first**: at `(-> $t Number $t)` a number at `$t` gives the protocol of
`(-> Number Number Number)`, so the answer `5` is kept; a string there gives the
protocol of `(-> String Number String)`, and the answer `7` is removed. -/
theorem value_parameter_first (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {num 5})
        (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "t" :: ([Ty.sym "Number"] : List (Ty Empty)).map Ty.lift)
          (.var "t")) ([] ++ num 5 :: [num 1]) = {num 5} ∧
      chainCall decls (metatype grounded) (fun _ => {num 7})
        (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "t" :: ([Ty.sym "Number"] : List (Ty Empty)).map Ty.lift)
          (.var "t")) ([] ++ str "s" :: [num 1]) = 0 := by
  have guarded : ∀ c : String, IsValueClass c → demand ((Ty.sym c : Ty Empty).lift) = .guarded := by
    intro c hc
    rcases hc with rfl | rfl | rfl <;> decide
  have once : ∀ (c : String) (g : GroundedValue), valueClass g = some c → IsValueClass c →
      guardCount (info decls (.grounded g)) (.sym c) (metatype grounded (.grounded g)) = 1 := by
    intro c g hg hc
    rw [guardCount_of_ne _ _ _ (fun h => metatype_ne_class grounded hc _ (Ty.sym.inj h).symm),
      count_class decls hg, if_pos rfl]
  constructor
  · rw [value_parameter_protocol_at grounded _ [] [.sym "Number"] "t" "Number" (.inl rfl) [] (num 5) [num 1]
      rfl rfl, chainCall_closed]
    simp only [List.nil_append, argCount, guarded "Number" (.inl rfl), if_true,
      once "Number" (.int 5) rfl (.inl rfl), once "Number" (.int 1) rfl (.inl rfl), mul_one, one_nsmul,
      if_pos (show ResultGuarded ((Ty.sym "Number" : Ty Empty).lift) by decide), Multiset.singleton_bind]
  · rw [value_parameter_protocol_at grounded _ [] [.sym "Number"] "t" "String" (.inr (.inl rfl)) [] (str "s")
      [num 1] rfl rfl, chainCall_closed]
    simp only [List.nil_append, argCount, guarded "String" (.inr (.inl rfl)),
      guarded "Number" (.inl rfl), if_true, once "String" (.string "s") rfl (.inr (.inl rfl)),
      once "Number" (.int 1) rfl (.inl rfl), mul_one, one_nsmul,
      if_pos (show ResultGuarded ((Ty.sym "String" : Ty Empty).lift) by decide), Multiset.singleton_bind]
    have notMetaS : (Ty.sym "String" : Ty Empty) ≠ .sym (metatype grounded (num 7)) := by simp [metatype]
    rw [guardCount_of_ne _ _ _ notMetaS, count_class decls (g := .int 7) rfl]
    simp

/-! ### Steps of a native fold -/

/-- The body of a step answering `6`. -/
def sixBody : List Atom → Multiset Atom := fun _ => {num 6}

/-- **Typed steps whose positions every integer meets**: `(-> $a Number $a)` and
`(-> %Undefined% $b Number)` answer `6` once on `1` and `5`, the step's own answer. -/
theorem fold_steps_numeric (grounded : String → Bool) :
    chainCall decls (metatype grounded) sixBody (arrow [.var "a", .sym "Number"] (.var "a"))
        [num 1, num 5] = {num 6} ∧
      chainCall decls (metatype grounded) sixBody (arrow [.sym "%Undefined%", .var "b"] (.sym "Number"))
        [num 1, num 5] = {num 6} := by
  have ints : ∀ v ∈ [num 1, num 5], IsInt v := by simp [IsInt]
  have six : ∀ r ∈ sixBody [num 1, num 5], IsInt r := by simp [sixBody, IsInt]
  exact ⟨fold_step_protocol _ sixBody [.var "a", .sym "Number"] (.var "a") (by simp [MeetsInts])
      (by simp [MeetsInts]) _ ints rfl six,
    fold_step_protocol _ sixBody [.sym "%Undefined%", .var "b"] (.sym "Number") (by simp [MeetsInts])
      (by simp [MeetsInts]) _ ints rfl six⟩

/-- **The negative controls**: a `String` result is no position integers meet,
and its protocol answers nothing where the step's arithmetic gives `6`; `Atom`
is not one either; a string item fails the guard at `Number`; two distinct
arrows are two alternatives, so the protocol answers `6` twice. -/
theorem fold_steps_declined (grounded : String → Bool) :
    ¬ MeetsInts (.sym "String") ∧ ¬ MeetsInts (.sym "Atom") ∧
      chainCall decls (metatype grounded) sixBody
        (arrow (([Ty.sym "Number", Ty.sym "Number"] : List (Ty Empty)).map Ty.lift)
          (Ty.sym "String" : Ty Empty).lift) [num 1, num 5] = 0 ∧
      chainCall decls (metatype grounded) sixBody
        (arrow (([Ty.sym "Number", Ty.sym "Number"] : List (Ty Empty)).map Ty.lift)
          (Ty.sym "Number" : Ty Empty).lift) [str "a", num 5] = 0 ∧
      typedCall decls (metatype grounded) sixBody
        [arrow [.sym "Number", .sym "Number"] (.sym "Number"), arrow [.var "a", .var "a"] (.var "a")]
        [num 1, num 5] = {num 6, num 6} := by
  have notMetaS : (Ty.sym "String" : Ty Empty) ≠ .sym (metatype grounded (num 6)) := by
    simp [metatype]
  have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
  have numOnce : ∀ v : Atom, IsInt v → guardCount (info decls v) (.sym "Number") (metatype grounded v) = 1 := by
    intro v hv
    obtain ⟨n, rfl⟩ : ∃ n, v = .grounded (.int n) := by
      cases v with
      | grounded g => cases g with
        | int n => exact ⟨n, rfl⟩
        | _ => exact hv.elim
      | _ => exact hv.elim
    rw [guardCount_of_ne _ _ _ (not_meta_number grounded _), count_class decls (g := .int n) rfl,
      if_pos rfl]
  refine ⟨by simp [MeetsInts], by simp [MeetsInts], ?_, ?_, ?_⟩
  · rw [chainCall_closed]
    have h1 := numOnce (num 1) trivial
    have h5 := numOnce (num 5) trivial
    simp only [argCount, guarded, if_true, h1, h5, mul_one, one_nsmul,
      if_pos (show ResultGuarded ((Ty.sym "String" : Ty Empty).lift) by decide), sixBody,
      Multiset.singleton_bind]
    rw [guardCount_of_ne _ _ _ notMetaS, count_class decls (g := .int 6) rfl]
    simp
  · rw [chainCall_closed]
    have strNone : guardCount (info decls (str "a")) (.sym "Number") (metatype grounded (str "a")) = 0 := by
      rw [guardCount_of_ne _ _ _ (not_meta_number grounded _), count_class decls (g := .string "a") rfl]
      decide
    simp only [argCount, guarded, if_true, strNone, zero_mul, zero_nsmul]
  · rw [typedCall_cons_fresh _ _ _ _ _ (by intro σ hσ; simp at hσ; subst hσ; decide), typedCall_single]
    have ints : ∀ v ∈ [num 1, num 5], IsInt v := by simp [IsInt]
    have six : ∀ r ∈ sixBody [num 1, num 5], IsInt r := by simp [sixBody, IsInt]
    rw [fold_step_protocol _ sixBody [.sym "Number", .sym "Number"] (.sym "Number")
        (by simp [MeetsInts]) (by simp [MeetsInts]) _ ints rfl six,
      fold_step_protocol _ sixBody [.var "a", .var "a"] (.var "a") (by simp [MeetsInts])
        (by simp [MeetsInts]) _ ints rfl six]
    rfl

/-! ### A range written as one parameter's type variable -/

/-- **`(cnt 1000 0)` is `1000`** at `(-> Number $t $t)`: the value parameter is a
number, so the answer is checked at `Number` and kept. -/
theorem cnt_value_parameter (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {num 1000})
        (arrow (([Ty.sym "Number"] : List (Ty Empty)).map Ty.lift ++ [.var "t"]) (.var "t"))
        [num 1000, num 0] = {num 1000} := by
  rw [show ([num 1000, num 0] : List Atom) = [num 1000] ++ [num 0] from rfl,
    value_parameter_protocol grounded _ [.sym "Number"] "t" "Number" (.inl rfl) [num 1000] (num 0) rfl rfl]
  have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
  have numOnce : ∀ n : ℤ, guardCount (info decls (num n)) (.sym "Number") (metatype grounded (num n)) = 1 :=
    fun n => by
      rw [guardCount_of_ne _ _ _ (not_meta_number grounded _), count_class decls (g := .int n) rfl, if_pos rfl]
  simp only [argCount, guarded, if_true, numOnce, mul_one, one_nsmul, Multiset.singleton_bind]

/-- **`(flip 2 "s")`, whose body answers `7`, answers nothing** at `(-> Number $t $t)`:
the value parameter is a string, so the answer is checked at `String`. -/
theorem flip_value_parameter (grounded : String → Bool) :
    chainCall decls (metatype grounded) (fun _ => {num 7})
        (arrow (([Ty.sym "Number"] : List (Ty Empty)).map Ty.lift ++ [.var "t"]) (.var "t"))
        [num 2, str "s"] = 0 := by
  rw [show ([num 2, str "s"] : List Atom) = [num 2] ++ [str "s"] from rfl,
    value_parameter_protocol grounded _ [.sym "Number"] "t" "String" (.inr (.inl rfl)) [num 2] (str "s") rfl rfl]
  have guarded : demand ((Ty.sym "Number" : Ty Empty).lift) = .guarded := by decide
  have notMetaS : (Ty.sym "String" : Ty Empty) ≠ .sym (metatype grounded (num 7)) := by simp [metatype]
  simp only [argCount, guarded, if_true, mul_one, Multiset.singleton_bind]
  rw [guardCount_of_ne _ _ _ notMetaS, count_class decls (g := .int 7) rfl]
  simp

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
