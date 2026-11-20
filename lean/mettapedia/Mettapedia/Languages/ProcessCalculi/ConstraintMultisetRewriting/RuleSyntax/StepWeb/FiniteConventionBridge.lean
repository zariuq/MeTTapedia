import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteBridge

/-!
# The source up to alpha-equivalence inside the tree's corrected semantics modulo the bag laws

`FiniteBridge` places the bag presentation's COMM (`BagComm`) inside the tree's own relational semantics of the
manuscript modulo the bag laws, `Corrected.BagCommStep Corrected.conventional`, for processes whose parallel
skeleton is binary. Here the source up to alpha-equivalence (`CommUpToAlpha`) is placed inside the same semantics
with the closing admission, `Corrected.BagCommStep Corrected.closing`: a COMM step of a tame alpha-variant of a
process's parts is a step of the corrected semantics from the process itself, to a process whose parts are
alpha-equivalent to the step's target (`commUpToAlpha_corrected`). With `communication_complete_up_to_alpha`,
every communication matched there is such a step. The closing admission matters: with the admission
`conventional` the corrected semantics also reaches reducts with codes (`corrected_step_reaches_a_code` in
`FiniteConventionControls`).

* `parts_closeIn`: closing commutes with taking binary parallel parts.
* `parts_parList_flatMap`, `components_parList_flatMap`: the parts and the components of a right-nested parallel
  composition.

What is not shown: the converse, that every step of the corrected semantics from such a process is a step of the
source up to alpha-equivalence. Its COMM asks a principal unifier, not a ground one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero applyDot)
open MeTTaCalculus.Corrected (components components_par components_pZero components_pFor components_closeIn
  components_of_mem_components bagEq_iff BagEq BagCommStep closing close closeIn closeIn_par closeIn_pZero
  closeIn_apply closeList_eq_map lookupBound boundCode)
open FiniteProgram (parts parts_par parts_pZero IsPar parts_of_not_par parts_of_mem_parts parList BagComm)

/-! ## Closing and the binary parallel structure -/

/-- Closing keeps the shape of a binary parallel composition. -/
theorem isPar_of_closeIn {env : List (List String)} {p : Pattern} (isPar : IsPar (closeIn env p)) : IsPar p := by
  obtain ⟨a, b, same⟩ := isPar
  cases p with
  | collection ct elems rest =>
      simp only [closeIn, closeList_eq_map, par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
      obtain ⟨rfl, lengths, rfl⟩ := same
      have two : elems.length = 2 := by simpa using congrArg List.length lengths
      match elems, two with
      | [a', b'], _ => exact ⟨a', b', rfl⟩
  | fvar x =>
      cases found : lookupBound env x <;> simp [closeIn, found, boundCode, par, MeTTaCalculus.pPar] at same
  | bvar n => simp [closeIn, par, MeTTaCalculus.pPar] at same
  | apply c args =>
      rw [closeIn_apply] at same
      simp [par, MeTTaCalculus.pPar] at same
  | lambda nm b => simp [closeIn, par, MeTTaCalculus.pPar] at same
  | multiLambda k nms b => simp [closeIn, par, MeTTaCalculus.pPar] at same
  | subst b r => simp [closeIn, par, MeTTaCalculus.pPar] at same

/-- A process closes to `0` only when it is `0`. -/
theorem eq_pZero_of_closeIn {env : List (List String)} {p : Pattern} (zero : closeIn env p = pZero) :
    p = pZero := by
  cases p with
  | apply c args =>
      rw [closeIn_apply] at zero
      simp only [pZero, Pattern.apply.injEq] at zero
      obtain ⟨rfl, empty⟩ := zero
      have notFor : ¬ ("MZero" : String) = "MFor" := by decide
      simp only [notFor, if_false, List.map_eq_nil_iff] at empty
      subst empty
      rfl
  | fvar x => cases found : lookupBound env x <;> simp [closeIn, found, boundCode, pZero] at zero
  | bvar n => simp [closeIn, pZero] at zero
  | lambda nm b => simp [closeIn, pZero] at zero
  | multiLambda k nms b => simp [closeIn, pZero] at zero
  | subst b r => simp [closeIn, pZero] at zero
  | collection ct elems rest => simp [closeIn, pZero] at zero

theorem parts_closeIn_of_not_par (env : List (List String)) {p : Pattern} (notPar : ¬ IsPar p) :
    parts (closeIn env p) = (parts p).map (closeIn env) := by
  rw [parts_of_not_par notPar, parts_of_not_par fun isPar => notPar (isPar_of_closeIn isPar)]
  by_cases zero : p = pZero
  · subst zero
    simp [closeIn_pZero]
  · rw [if_neg zero, if_neg fun same => zero (eq_pZero_of_closeIn same)]
    simp

/-- **Closing commutes with taking binary parallel parts.** -/
theorem parts_closeIn (env : List (List String)) (p : Pattern) :
    parts (closeIn env p) = (parts p).map (closeIn env) := by
  induction p using Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, parts (closeIn env q) = (parts q).map (closeIn env)) with
  | collection ct elems rest ih =>
      by_cases isPar : IsPar (.collection ct elems rest)
      · obtain ⟨a, b, same⟩ := isPar
        simp only [par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl, closeIn_par, parts_par, parts_par,
          ih a (by simp), ih b (by simp), List.map_append]
      · exact parts_closeIn_of_not_par env isPar
  | bvar n => exact parts_closeIn_of_not_par env (by rintro ⟨a, b, same⟩; cases same)
  | fvar x => exact parts_closeIn_of_not_par env (by rintro ⟨a, b, same⟩; cases same)
  | apply f args ih => exact parts_closeIn_of_not_par env (by rintro ⟨a, b, same⟩; cases same)
  | lambda nm body ih => exact parts_closeIn_of_not_par env (by rintro ⟨a, b, same⟩; cases same)
  | multiLambda n nms body ih => exact parts_closeIn_of_not_par env (by rintro ⟨a, b, same⟩; cases same)
  | subst body repl ihb ihr => exact parts_closeIn_of_not_par env (by rintro ⟨a, b, same⟩; cases same)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact tail q later

theorem parts_parList_flatMap : ∀ L : List Pattern, parts (parList L) = L.flatMap parts
  | [] => by simp [parList, parts_pZero]
  | p :: ps => by
      rw [parList, parts_par, parts_parList_flatMap ps]
      simp

theorem components_parList_flatMap : ∀ L : List Pattern, components (parList L) = L.flatMap components
  | [] => by simp [parList, components_pZero]
  | p :: ps => by
      rw [parList, components_par, components_parList_flatMap ps]
      simp

theorem flatMap_singleton_map (f : Pattern → Pattern) : ∀ L : List Pattern, (L.flatMap fun d => [f d]) = L.map f
  | [] => rfl
  | d :: L => by simp [flatMap_singleton_map f L]

/-! ## The source up to alpha-equivalence is a step of the corrected semantics -/

/-- **A step of the source up to alpha-equivalence is a step of the tree's corrected semantics modulo the bag
laws, with the closing admission.** From a process whose parallel skeleton is binary, a COMM step of a tame
alpha-variant of its parts is a step of `Corrected.BagCommStep Corrected.closing` from the process itself, to a
process whose parts are alpha-equivalent to the step's target. The closing admission asks guard-free calculus
patterns, calculus continuations and a unifier that grounds the patterns' variables; the tame source gives them. -/
theorem commUpToAlpha_corrected {P : Pattern} {M' : Multiset Pattern} (binary : components P = parts P)
    (step : CommUpToAlpha (parts P : Multiset Pattern) M') :
    ∃ Q', BagCommStep closing P Q' ∧ (parts Q' : Multiset Pattern).map close = M'.map close := by
  obtain ⟨N, N', tameN, sameN, comm, sameN'⟩ := step
  obtain ⟨t, u, x, A, B, bs, rest, gp, convention, -⟩ := comm
  obtain ⟨calcT, freeT, -, tameA⟩ := MeTTaCalculus.Corrected.tame_pFor.mp (tameN _ (Multiset.mem_cons_self _ _))
  obtain ⟨calcU, freeU, -, tameB⟩ := MeTTaCalculus.Corrected.tame_pFor.mp
    (tameN _ (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)))
  have admitted : closing t A u B bs :=
    ⟨convention, freeT, freeU, calcT, calcU, MeTTaCalculus.Corrected.tame_calcTerm A tameA,
      MeTTaCalculus.Corrected.tame_calcTerm B tameB, fun v inPatterns _ => gp.covers v inPatterns⟩
  have matched : ∀ d ∈ rest.toList, ∃ c ∈ parts P, close c = close d := by
    intro d member
    have inN : close d ∈ (pFor t x A ::ₘ pFor u x B ::ₘ rest).map close :=
      Multiset.mem_map_of_mem _
        (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem (Multiset.mem_toList.mp member)))
    rw [← sameN] at inN
    obtain ⟨c, inP, same⟩ := Multiset.mem_map.mp inN
    exact ⟨c, Multiset.mem_coe.mp inP, same⟩
  have closedComponents : ∀ d ∈ rest.toList, (components d).map close = [close d] := by
    intro d member
    obtain ⟨c, inP, same⟩ := matched d member
    have leaf : components c = [c] := components_of_mem_components P c (binary ▸ inP)
    calc (components d).map close = components (close d) := (components_closeIn d []).symm
      _ = components (close c) := by rw [same]
      _ = (components c).map close := components_closeIn c []
      _ = [close d] := by rw [leaf, List.map_singleton, same]
  have closedParts : ∀ d ∈ rest.toList, (parts d).map close = [close d] := by
    intro d member
    obtain ⟨c, inP, same⟩ := matched d member
    have leaf : parts c = [c] := parts_of_mem_parts P c inP
    calc (parts d).map close = parts (close d) := (parts_closeIn [] d).symm
      _ = parts (close c) := by rw [same]
      _ = (parts c).map close := parts_closeIn [] c
      _ = [close d] := by rw [leaf, List.map_singleton, same]
  have restMap : rest.map close = ((rest.toList.map close : List Pattern) : Multiset Pattern) := by
    conv_lhs => rw [← Multiset.coe_toList rest]
    rw [Multiset.map_coe]
  have similar : BagEq P (par (par (pFor t x A) (pFor u x B)) (parList rest.toList)) := by
    rw [bagEq_iff, binary, components_par, components_par, components_pFor, components_pFor,
      components_parList_flatMap, List.map_append, List.map_append, List.map_flatMap,
      List.flatMap_congr closedComponents, flatMap_singleton_map]
    apply Multiset.coe_eq_coe.mp
    rw [← Multiset.map_coe, sameN, Multiset.map_cons, Multiset.map_cons, restMap]
    rfl
  have fires : BagCommStep closing (par (par (pFor t x A) (pFor u x B)) (parList rest.toList))
      (par (par (applyDot bs A) (applyDot bs B)) (parList rest.toList)) :=
    .parallel _ (.comm t u x A B bs (Comm.principal_of_groundPrincipal gp) admitted)
  refine ⟨_, .congruence similar fires (BagEq.refl _), ?_⟩
  have partsAfter : (parts (par (par (applyDot bs A) (applyDot bs B)) (parList rest.toList))).map close =
      (parts (applyDot bs A)).map close ++ (parts (applyDot bs B)).map close ++ rest.toList.map close := by
    rw [parts_par, parts_par, parts_parList_flatMap, List.map_append, List.map_append, List.map_flatMap,
      List.flatMap_congr closedParts, flatMap_singleton_map]
  rw [← sameN', Multiset.map_coe, partsAfter, Multiset.map_add, Multiset.map_add, Multiset.map_coe,
    Multiset.map_coe, restMap, Multiset.coe_add, Multiset.coe_add]

/-- **The communications matched up to alpha are steps of the corrected semantics.** At a state that represents
the parts of a process with a binary parallel skeleton, every step of the source up to alpha-equivalence is a step
of `Corrected.BagCommStep Corrected.closing` from the process, and housekeeping firings and one communication
reach a state that represents an alpha-variant of the step's target. -/
theorem commUpToAlpha_matched_and_corrected {s : State Comm.Tm ℕ} {P : Pattern} {M' : Multiset Pattern}
    (represented : FiniteProgram.Represents s (parts P : Multiset Pattern)) (binary : components P = parts P)
    (tameParts : ∀ c ∈ (parts P : Multiset Pattern), MeTTaCalculus.Corrected.tame c = true)
    (step : CommUpToAlpha (parts P : Multiset Pattern) M') :
    (∃ Q', BagCommStep closing P Q' ∧ (parts Q' : Multiset Pattern).map close = M'.map close) ∧
      ∃ (s₁ s₂ : State Comm.Tm ℕ) (M'' : Multiset Pattern),
        Relation.ReflTransGen FiniteProgram.Administers s s₁ ∧ FiniteProgram.Communicates s₁ s₂ ∧
          FiniteProgram.Represents s₂ M'' ∧ M''.map close = M'.map close :=
  ⟨commUpToAlpha_corrected binary step, communication_complete_up_to_alpha represented tameParts step⟩

#print axioms isPar_of_closeIn
#print axioms eq_pZero_of_closeIn
#print axioms parts_closeIn
#print axioms parts_parList_flatMap
#print axioms components_parList_flatMap
#print axioms commUpToAlpha_corrected
#print axioms commUpToAlpha_matched_and_corrected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention
