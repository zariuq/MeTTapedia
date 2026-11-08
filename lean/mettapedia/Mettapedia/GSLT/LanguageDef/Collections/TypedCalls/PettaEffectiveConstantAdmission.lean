import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaConstantRowResidual
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypeQueryReplies

/-!
# Effective query evidence for constant-parameter admission

The constant rule consumes a completed singleton effective type query, not a
raw annotation. Intrinsic truth values retain Bool even if a declaration for
their spelling claims an arrow. This bridge computes the existing ordered
source query and recovers the exact guard derivation for named source leaves.
The source/native value codec and intrinsic registry remain separate ports;
in particular an internal C truth symbol denotes a grounded source value.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaEffectiveConstantAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.LP (Subst unifyTotal)
open PettaTypeQueryReplies (solve solveAll inferred)
open PettaConstantRowResidual (AcceptedConstant assignment)

/-- The source values represented by the native named-constant entrance.
Truth spellings use their intrinsic source value, not an ordinary symbol. -/
inductive NamedValue : Atom → Prop where
  | symbol (name : String) : NamedValue (.symbol name)
  | bool (value : Bool) : NamedValue (.grounded (.bool value))

/-- Exactly the provider-side tests in contract_effective_type. A declined
provider, incomplete result, empty or multiple result, and Undefined all
refuse admission; they do not become a declaration lookup. -/
def select {V : Type} [DecidableEq V] (answered complete : Bool)
    (replies : List (Ty V)) : Option (Ty V) :=
  if answered && complete then
    match replies with
    | [type] => if type = .sym "%Undefined%" then none else some type
    | _ => none
  else none

theorem select_accepted_iff {V : Type} [DecidableEq V]
    (answered complete : Bool) (replies : List (Ty V)) (type : Ty V) :
    select answered complete replies = some type ↔
      answered = true ∧ complete = true ∧ replies = [type] ∧ type ≠ .sym "%Undefined%" := by
  cases answered <;> cases complete <;> cases replies with
  | nil => simp [select]
  | cons first rest =>
      cases rest with
      | nil => by_cases undefined : first = .sym "%Undefined%" <;> simp_all [select] <;> aesop
      | cons second tail => simp [select]

theorem solve_unconstrained (type : Ty DVar) : solve ⟨type, []⟩ = some type := by
  simp [solve, TypeEquationSolver.equations, unifyTotal,
    Subst.applyTerm_id, TypeEquationSolver.decode_encode]

theorem solveAll_unconstrained (types : List (Ty DVar)) :
    solveAll (types.map fun type => ⟨type, []⟩) = some types := by
  induction types with
  | nil => rfl
  | cons first rest ih => simp [solveAll, solve_unconstrained, ih]

theorem inferred_symbol (declarations : Decls) (name : String) :
    inferred declarations (.symbol name) =
      some (if (declarations name).isEmpty then [.sym "%Undefined%"]
        else (declarations name).map (Ty.map DVar.own)) := by
  change solveAll (OrderedTypeRelation.effective (OrderedTypeRelation.leaf declarations (.symbol name))) = _
  by_cases empty : declarations name = []
  · simp [OrderedTypeRelation.effective, OrderedTypeRelation.leaf, empty,
      solveAll, undefinedDeriv, undefinedTy, solve_unconstrained]
  · have nonempty : (declarations name).isEmpty = false := by simpa using empty
    simp only [OrderedTypeRelation.effective, OrderedTypeRelation.leaf, List.isEmpty_map,
      nonempty, Bool.false_eq_true, ↓reduceIte]
    simpa only [List.map_map, Function.comp_def] using
      solveAll_unconstrained ((declarations name).map (Ty.map DVar.own))

theorem inferred_bool (declarations : Decls) (value : Bool) :
    inferred declarations (.grounded (.bool value)) = some [.sym "Bool"] := by
  change solveAll [classDeriv "Bool"] = _
  simp [solveAll, classDeriv, solve_unconstrained]

/-- Query replies and exact guard derivations agree at this source entrance.
This is obtained from the computed query, not assumed as a guard premise. -/
theorem named_query_recovers_derivations (declarations : Decls) (value : Atom)
    (named : NamedValue value) (replies : List (Ty DVar))
    (computed : inferred declarations value = some replies) :
    eff (info declarations value) =
      ((replies.map fun type => (⟨type, []⟩ : Deriv)) : Multiset Deriv) := by
  cases named with
  | symbol name =>
      rw [inferred_symbol] at computed
      cases Option.some.inj computed
      rw [info_symbol]
      by_cases empty : declarations name = []
      · simp [empty, eff, undefinedDeriv, undefinedTy]
      · simp [eff, empty, List.isEmpty_iff, List.map_map, Function.comp_def]
  | bool value =>
      rw [inferred_bool] at computed
      cases Option.some.inj computed
      simp [info_bool, eff, classDeriv]

theorem effective_query_earns_single_derivation (declarations : Decls) (value : Atom)
    (named : NamedValue value) (replies : List (Ty DVar))
    (computed : inferred declarations value = some replies)
    (type : Ty DVar) (admitted : select true true replies = some type) :
    eff (info declarations value) = {⟨type, []⟩} := by
  obtain ⟨_, _, rfl, _⟩ := (select_accepted_iff true true replies type).mp admitted
  simpa using named_query_recovers_derivations declarations value named [type] computed

open Classical in
/-- Actual effective-query admission followed by the compiler's MGU entails
one ordered guard continuation at every allowed residual instance. -/
theorem effective_constant_guard_once (entry : AcceptedConstant) (declarations : Decls)
    (value : Atom) (named : NamedValue value) (replies : List (Ty DVar))
    (computed : inferred declarations value = some replies)
    (admitted : select true true replies = some (entry.declaration.map DVar.own))
    (grounded : String → Bool) (index : Nat) (store : List (Eqn CallVar))
    (fresh : ∀ v, atGuard index v ∉ eqnVars store)
    (residual : ConstantInstances.Side → Ty Empty)
    (allowed : Allows store (assignment entry residual)) :
    guard (atGuard index) store (entry.formal.map Sum.inl)
      (info declarations value) (metatype grounded value) =
      {store ++ [(((entry.declaration.map DVar.own).map (atGuard index) : Ty CallVar),
        entry.formal.map Sum.inl)]} := by
  have exactDerivation := effective_query_earns_single_derivation declarations value named
    replies computed (entry.declaration.map DVar.own) admitted
  have satisfiable : Sat (store ++
      [(((entry.declaration.map DVar.own).map (atGuard index) : Ty CallVar), entry.formal.map Sum.inl)]) := by
    rw [sat_iff_allows]
    exact ⟨assignment entry residual,
      (PettaConstantRowResidual.constant_constraint_allows_exactly entry index store fresh residual).mpr allowed⟩
  have actual := getType_of_eff (atGuard index) store (entry.formal.map Sum.inl) exactDerivation
  simp only [List.map_nil, List.append_nil, if_pos satisfiable] at actual
  rw [guard_of_getType _ _ _ _ _ (by rw [actual]; exact Multiset.singleton_ne_zero _), actual]

theorem effective_constant_ordered_guard_once (entry : AcceptedConstant) (declarations : Decls)
    (value : Atom) (named : NamedValue value) (replies : List (Ty DVar))
    (computed : inferred declarations value = some replies)
    (admitted : select true true replies = some (entry.declaration.map DVar.own))
    (grounded : String → Bool) (index : Nat) (store : List (Eqn CallVar))
    (fresh : ∀ v, atGuard index v ∉ eqnVars store)
    (residual : ConstantInstances.Side → Ty Empty)
    (allowed : Allows store (assignment entry residual)) :
    OrderedTypeRelation.guardOrdered (atGuard index) store (entry.formal.map Sum.inl)
      (OrderedTypeRelation.infer declarations value) (metatype grounded value) =
      [store ++ [(((entry.declaration.map DVar.own).map (atGuard index) : Ty CallVar),
        entry.formal.map Sum.inl)]] := by
  apply Multiset.coe_eq_singleton.mp
  rw [OrderedTypeRelation.guardOrdered_erases, OrderedTypeRelation.infer_erases]
  exact effective_constant_guard_once entry declarations value named replies computed admitted
    grounded index store fresh residual allowed

/-- No instance of an intrinsic atomic type is an arrow. The rejection is
derived from soundness of the actual compiler MGU. -/
theorem derive_application_not_symbol (children : List (Ty String)) (symbol : String) :
    ConstantInstances.derive (.app children) (.sym symbol) = none := by
  cases result : ConstantInstances.derive (.app children) (.sym symbol) with
  | none => rfl
  | some solver =>
      have impossible := ConstantInstances.derive_unifies result
      simp only [Ty.map_app, Ty.map_sym, Ty.bind_app, Ty.bind_sym] at impossible
      cases impossible

theorem symbol_application_store_unsatisfiable {V : Type} (store : List (Eqn V))
    (symbol : String) (children : List (Ty V)) :
    ¬ Sat (store ++ [(.sym symbol, .app children)]) := by
  rintro ⟨valuation, solved⟩
  have impossible := solved (.sym symbol, .app children) (by simp)
  simp only [Ty.bind_sym, Ty.bind_app] at impossible
  cases impossible

/-- Both actual branches fail: Bool does not match an arrow, and neither
does the Grounded metatype. Authored rows for its spelling are irrelevant. -/
theorem bool_arrow_guard_empty (declarations : Decls) (value : Bool)
    (grounded : String → Bool) (index : Nat) (store : List (Eqn CallVar))
    (children : List (Ty String)) :
    guard (atGuard index) store ((Ty.app children).map Sum.inl)
      (info declarations (.grounded (.bool value)))
      (metatype grounded (.grounded (.bool value))) = 0 := by
  simp [guard, getType, info_bool, eff, classDeriv, metatype,
    symbol_application_store_unsatisfiable]

namespace Controls

def numberArrow : Ty String := arrow [.sym "Number"] (.sym "Number")
def polymorphicArrow : Ty String := arrow [.var "z"] (.sym "Number")

def declarations : Decls := fun name =>
  if name = "inc" then [numberArrow]
  else if name = "true" then [polymorphicArrow]
  else []

theorem declared_function_query_is_accepted :
    inferred declarations (.symbol "inc") = some [numberArrow.map DVar.own] ∧
      select true true [numberArrow.map DVar.own] = some (numberArrow.map DVar.own) := by
  constructor
  · rw [inferred_symbol]; rfl
  · rfl

theorem truth_annotation_does_not_override_effective_type :
    Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readToken "true" =
      .ok (.grounded (.bool true)) ∧
    inferred declarations (.symbol "true") = some [polymorphicArrow.map DVar.own] ∧
    inferred declarations (.grounded (.bool true)) = some [.sym "Bool"] := by
  refine ⟨by decide +kernel, ?_, inferred_bool _ _⟩
  rw [inferred_symbol]
  rfl

theorem effective_truth_cannot_be_a_constant_function (formalArgs : List (Ty String))
    (formalRange : Ty String) :
    select true true ([.sym "Bool"] : List (Ty DVar)) = some (.sym "Bool") ∧
    ConstantInstances.derive (arrow formalArgs formalRange) (.sym "Bool") = none := by
  exact ⟨rfl, derive_application_not_symbol _ _⟩

theorem incomplete_query_is_not_a_constant :
    select true false [numberArrow] = none := rfl

theorem declined_provider_is_not_a_constant :
    select false true [numberArrow] = none := rfl

theorem overloads_are_not_silently_first_selected :
    select true true [numberArrow, polymorphicArrow] = none := rfl

theorem undefined_is_not_a_constant :
    select true true ([.sym "%Undefined%"] : List (Ty String)) = none := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaEffectiveConstantAdmission
