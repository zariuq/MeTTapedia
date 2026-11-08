import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ContractBindingFacts

/-!
# A constructor-head alias invalidates a discharged polymorphic range

The declaration family is functional: Known has one Number-to-Tag arrow.
An active argument whose head is an open variable has a tuple-shaped type.
Binding its aliased ANY argument to Known turns that head into a declared
constructor. The original shared result guard rejects its Tag result.

The body below uses the existing two-way source evaluator. The enclosing
consumer uses the existing Expr evaluator and consumes the callee's whole
answer bag. Omitting the callee's result protocol makes a later literal
observable, even though retaining that protocol produces no answer.

This is the theory control for the native discharged-range reproducer.
It does not assert textual parsing or C compiler correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ContractAliasRangeCounterexample

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions

def declarations : Decls := fun name =>
  if name = "Known" then [arrow [.sym "Number"] (.sym "Tag")] else []

def one : Atom := .grounded (.int 1)
def known : Atom := .symbol "Known"
def input : Atom := .expression [.var "shared", one]
def result : Atom := .expression [known, one]
def row : Ty String := arrow [.var "a", .sym "%Undefined%"] (.var "a")
def args : List Atom := [input, .var "shared"]

theorem functional : Functional declarations := by
  intro name
  by_cases same : name = "Known" <;> simp [declarations, same]

def bodyExpr : Expr := .letE (.var "b") (.const known) (.var "a")
def initial (first second : Atom) : Substitution := fun name =>
  if name = "a" then first else if name = "b" then second else .var name

def body : List Atom → Multiset Atom
  | [first, second] =>
      (evalUnifying (fun _ _ => 0) (fun _ => 0) bodyExpr (initial first second)).map observe
  | _ => 0

theorem actual_body_result : body args = {result} := by cbv

theorem input_uninterpreted : Uninterp declarations input := by
  simp [input, one, Uninterp, Safe, SafeAll, substA, HeadFree]

theorem eff_input : eff (info declarations input) =
    {⟨.app [.var ([0], none), .sym "Number"], []⟩} := by
  rw [eff_tuple (Γ := declarations) (h := .var "shared") (es := [one]) trivial
    (ds := [⟨.var ([], none), []⟩, classDeriv "Number"])
    (.cons (by unfold eff; rw [info_var]; simp)
      (.cons (by unfold eff; rw [show one = .grounded (.int 1) from rfl, info_int]; simp) .nil))]
  rfl

theorem eff_result : ∃ equations, eff (info declarations result) = {⟨.sym "Tag", equations⟩} := by
  classical
  have declared : declarations "Known" = [arrow [.sym "Number"] (.sym "Tag")] := by simp [declarations]
  have argument : argEqs 1 [.sym "Number"] [info declarations one] =
      {ctorEqs 1 [.sym "Number"] [classDeriv "Number"]} :=
    argEqs_singletons 1 _ _ _ rfl
      (.cons (by unfold eff; rw [show one = .grounded (.int 1) from rfl, info_int]; simp) .nil)
  have satisfiable : Sat (ctorEqs 1 [.sym "Number"] [classDeriv "Number"]) :=
    ⟨fun _ => default, fun equation member => by
      simp [ctorEqs, Unchecked, classDeriv, Deriv.push] at member
      subst equation
      rfl⟩
  have tree : funTrees (info declarations known) [info declarations one] =
      {⟨(Ty.sym "Tag").map DVar.own, ctorEqs 1 [.sym "Number"] [classDeriv "Number"]⟩} := by
    rw [show known = .symbol "Known" from rfl, info_symbol, declared,
      funTrees_arrow _ _ _ _ rfl, argument, Multiset.map_singleton,
      Multiset.filter_singleton, if_pos satisfiable]
  refine ⟨ctorEqs 1 [.sym "Number"] [classDeriv "Number"], eff_single_cands ?_⟩
  rw [show result = .expression [known, one] from rfl, info_expression]
  simp only [List.map_cons, List.map_nil, nodeInfo, tree, Multiset.card_singleton, one_ne_zero, if_false]
  rfl

open Classical in
/-- The unchecked second argument adds no guard store. The shared first/
result type variable still carries the first argument's tuple obligation. -/
theorem retained_result_guard_rejects (kind : Atom → String) :
    chainCall declarations kind body row args = 0 := by
  let derivation : Deriv := ⟨.app [.var ([0], none), .sym "Number"], []⟩
  let store : List (Eqn CallVar) := [(derivation.ty.map (atGuard 0), .var (.inl "a"))]
  have initialSat : Sat ([] ++ derivation.eqs.map (Eqn.map (atGuard 0)) ++
      [(derivation.ty.map (atGuard 0), (Ty.var (Sum.inl "a") : Ty CallVar))]) := by
    refine ⟨fun variableName => match variableName with
      | .inl _ => derivation.ty.bind fun _ => default
      | .inr _ => default, ?_⟩
    simp only [derivation, List.map_nil, List.nil_append, solves_singleton,
      Ty.bind_var', Ty.bind_map]
    rfl
  have firstGuard : guard (atGuard 0) [] ((Ty.var "a" : Ty String).map Sum.inl)
      (info declarations input) (kind input) = {store} := by
    rw [guard_of_getType _ _ _ _ _ (by
        rw [Ty.map_var, getType_of_eff _ _ _ eff_input, if_pos initialSat]
        exact Multiset.singleton_ne_zero _),
      Ty.map_var, getType_of_eff _ _ _ eff_input, if_pos initialSat]
    rfl
  obtain ⟨equations, resultInfo⟩ := eff_result
  have lastGuard : guard (atGuard 2) store ((Ty.var "a" : Ty String).map Sum.inl)
      (info declarations result) (kind result) = 0 := by
    have noType : getType (atGuard 2) store (.var (.inl "a")) (info declarations result) = 0 := by
      unfold getType
      rw [resultInfo, Multiset.map_singleton, Multiset.filter_singleton, if_neg]
      · rfl
      · rintro ⟨solution, solves⟩
        rw [solves_append, solves_append] at solves
        have first := solves.1.1
        have last := solves.2
        simp only [store, derivation, solves_singleton, Ty.bind_var', Ty.bind_map,
          Ty.map_sym, Ty.bind_sym] at first last
        have impossible := first.trans last.symm
        cases impossible
    unfold guard
    rw [Ty.map_var, if_pos (by rw [noType]; rfl), Multiset.filter_singleton, if_neg]
    · rfl
    · rintro ⟨solution, solves⟩
      rw [solves_append] at solves
      have first := solves.1
      have last := solves.2
      simp only [store, derivation, solves_singleton, Ty.bind_var', Ty.bind_map, Ty.bind_sym] at first last
      have impossible := first.trans last.symm
      cases impossible
  unfold chainCall
  rw [show row = arrow [.var "a", .sym "%Undefined%"] (.var "a") from rfl, arrowSplit_arrow]
  dsimp only
  have active : demand (Ty.var "a" : Ty String) = .guarded := by decide
  have ignored : demand (Ty.sym "%Undefined%" : Ty String) ≠ .guarded := by decide
  simp only [args, guards, active, if_true, firstGuard, Multiset.singleton_bind,
    ignored, if_false, List.length_cons, List.length_nil, Nat.reduceAdd, actual_body_result]
  change ((body args).bind (resultGuard declarations kind 2 (.var "a") store)) = 0
  rw [actual_body_result, Multiset.singleton_bind]
  unfold resultGuard
  rw [if_pos (by decide), lastGuard, Multiset.map_zero]

def consumer : Expr := .letE (.var "result")
  (.call "alias-bind-u" [.const input, .const (.var "shared")]) (.const one)

def environment (callee : List Atom → Multiset Atom) : Env where
  prim := fun _ _ => 0
  kept := fun _ => callee
  rows := fun _ => 0

def noCalls : Oracle := ⟨fun _ => 0, fun _ _ => 0⟩

theorem consumed_after_discharge : Expr.eval (environment body) noCalls [] consumer = {one} := by
  simp only [consumer, Expr.eval, Expr.evalAll, Multiset.singleton_bind, Multiset.map_singleton,
    environment, List.cons_append, List.nil_append]
  change (body args).bind (fun value => match Pat.matchUnder [] (.var "result") value with
    | some bindings => {one}
    | none => 0) = _
  rw [actual_body_result, Multiset.singleton_bind]
  rfl

theorem consumed_with_protocol (kind : Atom → String) :
    Expr.eval (environment (chainCall declarations kind body row)) noCalls [] consumer = 0 := by
  simp only [consumer, Expr.eval, Expr.evalAll, Multiset.singleton_bind, Multiset.map_singleton,
    environment, List.cons_append, List.nil_append]
  change (chainCall declarations kind body row args).bind (fun value =>
    match Pat.matchUnder [] (.var "result") value with
    | some bindings => {one}
    | none => 0) = _
  rw [retained_result_guard_rejects, Multiset.zero_bind]

theorem nested_discharge_changes_observation (kind : Atom → String) :
    Expr.eval (environment body) noCalls [] consumer ≠
      Expr.eval (environment (chainCall declarations kind body row)) noCalls [] consumer := by
  rw [consumed_after_discharge, consumed_with_protocol]
  exact Multiset.singleton_ne_zero _

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ContractAliasRangeCounterexample
