import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationSolver

/-!
# Ordered executable realization of the PeTTa type relation

The list realization follows written declaration order and depth-first product
order, with the last argument varying fastest. Its erasure is the existing
`TypeRelation`, and every consistency test uses the existing total unifier.
Only type derivations are enumerated here; values are never evaluated.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedTypeRelation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

structure OrderedInfo where
  rows : List (Ty String)
  candidates : List Deriv

def OrderedInfo.erase (info : OrderedInfo) : Info := ⟨info.rows, info.candidates⟩

def effective (info : OrderedInfo) : List Deriv :=
  if info.candidates.isEmpty then [undefinedDeriv] else info.candidates

def argumentEquations : Nat → List (Ty String) → List OrderedInfo → List (List (Eqn DVar))
  | _, [], [] => [[]]
  | index, formal :: formals, info :: infos =>
    if Unchecked formal then argumentEquations (index + 1) formals infos
    else (effective info).flatMap fun derivation =>
      (argumentEquations (index + 1) formals infos).map fun equations =>
        ((formal.map DVar.own, (derivation.push index).ty) :: (derivation.push index).eqs) ++ equations
  | _, [], _ :: _ => []
  | _, _ :: _, [] => []

def functionDerivations (head : OrderedInfo) (arguments : List OrderedInfo) : List Deriv :=
  head.rows.flatMap fun row =>
    match arrowSplit row with
    | none => []
    | some (formals, range) =>
      if formals.length = arguments.length then
        ((argumentEquations 1 formals arguments).map fun equations =>
          (⟨range.map DVar.own, equations⟩ : Deriv)).filter fun derivation =>
            TypeEquationSolver.check derivation.eqs
      else []

def tuplePartsOrdered : Nat → List OrderedInfo → List (List (Ty DVar) × List (Eqn DVar))
  | _, [] => [([], [])]
  | index, info :: infos => (effective info).flatMap fun derivation =>
      (tuplePartsOrdered (index + 1) infos).map fun tail =>
        ((derivation.push index).ty :: tail.1, (derivation.push index).eqs ++ tail.2)

def tupleDerivations (infos : List OrderedInfo) : List Deriv :=
  (tuplePartsOrdered 0 infos).map fun fields => ⟨.app fields.1, fields.2⟩

def leaf (declarations : Decls) : Atom → OrderedInfo
  | .symbol name => ⟨declarations name, (declarations name).map fun type => ⟨type.map DVar.own, []⟩⟩
  | .var _ => ⟨[], [⟨.var ([], none), []⟩]⟩
  | .grounded (.int _) => ⟨[], [classDeriv "Number"]⟩
  | .grounded (.string _) => ⟨[], [classDeriv "String"]⟩
  | .grounded (.bool _) => ⟨[], [classDeriv "Bool"]⟩
  | .grounded (.custom _ _) => ⟨[], []⟩
  | .expression _ => ⟨[], []⟩

def node : List OrderedInfo → OrderedInfo
  | [] => ⟨[], tupleDerivations []⟩
  | first :: rest =>
      let functions := functionDerivations first rest
      ⟨[], if functions.isEmpty then tupleDerivations (first :: rest) else functions⟩

def relation : TypedCertificates.Judgment Decls OrderedInfo where
  leaf := leaf
  node := node

def infer (declarations : Decls) (value : Atom) : OrderedInfo :=
  TypedCertificates.Judgment.full relation declarations value

def exactTypes {V : Type} [DecidableEq V] (rename : DVar → V)
    (store : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) : List (List (Eqn V)) :=
  ((effective info).map fun derivation =>
    store ++ derivation.eqs.map (Eqn.map rename) ++ [(derivation.ty.map rename, expected)]).filter
      TypeEquationSolver.check

def guardOrdered {V : Type} [DecidableEq V] (rename : DVar → V)
    (store : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) (kind : String) : List (List (Eqn V)) :=
  let exact := exactTypes rename store expected info
  if exact.isEmpty then
    [store ++ [(.sym kind, expected)]].filter TypeEquationSolver.check
  else exact

theorem effective_erases (info : OrderedInfo) :
    (effective info : Multiset Deriv) = eff info.erase := by
  by_cases empty : info.candidates = [] <;>
    simp [effective, eff, OrderedInfo.erase, List.isEmpty_iff, empty]

open Classical in
theorem checked_filter {V : Type} [DecidableEq V] (stores : List (List (Eqn V))) :
    ((stores.filter TypeEquationSolver.check : List (List (Eqn V))) : Multiset (List (Eqn V))) =
      (stores : Multiset (List (Eqn V))).filter Sat := by
  classical
  have checks : (TypeEquationSolver.check : List (Eqn V) → Bool) = fun store => decide (Sat store) :=
    funext TypeEquationSolver.check_eq_decide
  rw [checks, Multiset.filter_coe]

theorem argumentEquations_erases : ∀ (index : Nat) (formals : List (Ty String)) (infos : List OrderedInfo),
    (argumentEquations index formals infos : Multiset (List (Eqn DVar))) =
      argEqs index formals (infos.map OrderedInfo.erase)
  | _, [], [] => rfl
  | index, formal :: formals, info :: infos => by
    simp only [argumentEquations, List.map_cons, argEqs]
    split
    · exact argumentEquations_erases _ _ _
    · rw [← Multiset.coe_bind, effective_erases]
      congr 1
      funext derivation
      rw [← Multiset.map_coe, argumentEquations_erases]
  | _, [], _ :: _ => rfl
  | _, _ :: _, [] => rfl

theorem functionDerivations_erases (head : OrderedInfo) (arguments : List OrderedInfo) :
    (functionDerivations head arguments : Multiset Deriv) =
      funTrees head.erase (arguments.map OrderedInfo.erase) := by
  classical
  unfold functionDerivations funTrees
  rw [← Multiset.coe_bind]
  congr 1
  funext row
  cases split : arrowSplit row with
  | none => rfl
  | some pair =>
    rcases pair with ⟨formals, range⟩
    simp only [List.length_map]
    split
    · have filter : ∀ candidates : List Deriv,
          ((candidates.filter fun derivation => TypeEquationSolver.check derivation.eqs) : Multiset Deriv) =
            (candidates : Multiset Deriv).filter (fun derivation => Sat derivation.eqs) := by
        intro candidates
        simp only [TypeEquationSolver.check_eq_decide, Multiset.filter_coe]
      rw [filter, ← Multiset.map_coe, argumentEquations_erases]
    · rfl

theorem tuplePartsOrdered_erases : ∀ (index : Nat) (infos : List OrderedInfo),
    (tuplePartsOrdered index infos : Multiset (List (Ty DVar) × List (Eqn DVar))) =
      tupleParts index (infos.map OrderedInfo.erase)
  | _, [] => rfl
  | index, info :: infos => by
    simp only [tuplePartsOrdered, tupleParts, List.map_cons]
    rw [← Multiset.coe_bind, effective_erases]
    congr 1
    funext derivation
    rw [← Multiset.map_coe, tuplePartsOrdered_erases]

theorem tupleDerivations_erases (infos : List OrderedInfo) :
    (tupleDerivations infos : Multiset Deriv) = tupleTrees (infos.map OrderedInfo.erase) := by
  rw [tupleDerivations, tupleTrees, ← Multiset.map_coe, tuplePartsOrdered_erases]

theorem leaf_erases (declarations : Decls) (value : Atom) :
    (leaf declarations value).erase = leafInfo declarations value := by
  cases value with
  | grounded value => cases value <;> rfl
  | symbol _ | var _ | expression _ => rfl

theorem node_erases (infos : List OrderedInfo) :
    (node infos).erase = nodeInfo (infos.map OrderedInfo.erase) := by
  cases infos with
  | nil =>
    simp only [node, nodeInfo, List.map_nil, OrderedInfo.erase]
    rw [tupleDerivations_erases]
    rfl
  | cons head rest =>
    have functions := functionDerivations_erases head rest
    have tuples := tupleDerivations_erases (head :: rest)
    dsimp only [OrderedInfo.erase] at functions tuples
    simp only [node, nodeInfo, List.map_cons, OrderedInfo.erase]
    rw [← functions]
    simp only [Multiset.coe_card, List.length_eq_zero_iff, List.isEmpty_iff]
    split <;> simp_all
    rfl

theorem infer_erases (declarations : Decls) (value : Atom) :
    (infer declarations value).erase = info declarations value := by
  induction value using Atom.rec (motive_2 := fun values =>
    ∀ value ∈ values, (infer declarations value).erase = info declarations value) with
  | symbol name | var name | grounded name =>
    simpa only [infer, info, relation, typeRelation, TypedCertificates.Judgment.full] using
      leaf_erases declarations _
  | expression values each =>
    unfold infer
    rw [TypedCertificates.Judgment.full_expression]
    change (node (values.map (infer declarations))).erase = _
    rw [node_erases, info_expression, List.map_map]
    congr 1
    exact List.map_congr_left each
  | nil value member => cases member
  | cons head rest headIH restIH value member =>
    rcases List.mem_cons.mp member with rfl | member
    · exact headIH
    · exact restIH value member

theorem exactTypes_erases {V : Type} [DecidableEq V] (rename : DVar → V)
    (store : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) :
    (exactTypes rename store expected info : Multiset (List (Eqn V))) =
      getType rename store expected info.erase := by
  rw [exactTypes, checked_filter, ← Multiset.map_coe, effective_erases]
  rfl

theorem guardOrdered_erases {V : Type} [DecidableEq V] (rename : DVar → V)
    (store : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) (kind : String) :
    (guardOrdered rename store expected info kind : Multiset (List (Eqn V))) =
      guard rename store expected info.erase kind := by
  unfold guardOrdered guard
  rw [← exactTypes_erases]
  simp only [Multiset.coe_card, List.length_eq_zero_iff, List.isEmpty_iff]
  split
  · exact checked_filter (V := V) [store ++ [(.sym kind, expected)]]
  · rfl

/-- Guards retain the order of the effective derivations: filtering removes
failed trials, but neither reorders nor coalesces successful occurrences. -/
theorem exactTypes_order {V : Type} [DecidableEq V] (rename : DVar → V)
    (store : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) :
    List.Sublist (exactTypes rename store expected info)
      ((effective info).map fun derivation => store ++ derivation.eqs.map (Eqn.map rename) ++
        [(derivation.ty.map rename, expected)]) := List.filter_sublist

theorem exactTypes_accepts_iff {V : Type} [DecidableEq V] (rename : DVar → V)
    (store answer : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) :
    answer ∈ exactTypes rename store expected info ↔
      ∃ derivation ∈ effective info,
        answer = store ++ derivation.eqs.map (Eqn.map rename) ++ [(derivation.ty.map rename, expected)] ∧
        Sat answer := by
  simp only [exactTypes, List.mem_filter, List.mem_map, TypeEquationSolver.check_iff_sat]
  constructor
  · rintro ⟨⟨derivation, member, same⟩, sat⟩
    exact ⟨derivation, member, same.symm, sat⟩
  · rintro ⟨derivation, member, same, sat⟩
    exact ⟨⟨derivation, member, same.symm⟩, sat⟩

theorem function_declaration_order (first rest : List (Ty String)) (candidates : List Deriv)
    (arguments : List OrderedInfo) :
    functionDerivations ⟨first ++ rest, candidates⟩ arguments =
      functionDerivations ⟨first, candidates⟩ arguments ++
        functionDerivations ⟨rest, candidates⟩ arguments := by
  simp [functionDerivations, List.flatMap_append]

/-- Exact-type success suppresses the metatype branch, including when the
successful derivations happen to produce identical stores. -/
theorem guard_exact_before_metatype {V : Type} [DecidableEq V] (rename : DVar → V)
    (store : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) (kind : String)
    (present : exactTypes rename store expected info ≠ []) :
    guardOrdered rename store expected info kind = exactTypes rename store expected info := by
  simp [guardOrdered, List.isEmpty_iff, present]

theorem guard_metatype_only_after_empty {V : Type} [DecidableEq V] (rename : DVar → V)
    (store : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) (kind : String)
    (empty : exactTypes rename store expected info = []) :
    guardOrdered rename store expected info kind =
      [store ++ [(.sym kind, expected)]].filter TypeEquationSolver.check := by
  simp [guardOrdered, empty]

/-- A successful guard extends, rather than replaces, the row's shared type
store. Its full extended system is satisfiable. -/
theorem guardOrdered_extends {V : Type} [DecidableEq V] (rename : DVar → V)
    (store answer : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) (kind : String)
    (member : answer ∈ guardOrdered rename store expected info kind) :
    ∃ suffix, answer = store ++ suffix ∧ Sat answer := by
  dsimp only [guardOrdered] at member
  split at member
  · obtain ⟨present, accepted⟩ := List.mem_filter.mp member
    have same := List.mem_singleton.mp present
    exact ⟨[(.sym kind, expected)], same, (TypeEquationSolver.check_iff_sat answer).mp accepted⟩
  · obtain ⟨derivation, _present, same, sat⟩ :=
      (exactTypes_accepts_iff rename store answer expected info).mp member
    exact ⟨derivation.eqs.map (Eqn.map rename) ++ [(derivation.ty.map rename, expected)],
      same.trans (List.append_assoc _ _ _), sat⟩

theorem guardOrdered_keeps_row_solution {V : Type} [DecidableEq V] (rename : DVar → V)
    (store answer : List (Eqn V)) (expected : Ty V) (info : OrderedInfo) (kind : String)
    (member : answer ∈ guardOrdered rename store expected info kind)
    (solution : V → Ty Empty) (solves : Solves solution answer) :
    Solves solution store := by
  obtain ⟨suffix, rfl, _sat⟩ := guardOrdered_extends rename store answer expected info kind member
  exact ((solves_append solution store suffix).mp solves).1

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OrderedTypeRelation
