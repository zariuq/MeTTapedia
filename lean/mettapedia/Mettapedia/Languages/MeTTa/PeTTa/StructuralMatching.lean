import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# PeTTa's structural pattern fragment

A pattern in this fragment uses literal expression shape at each node.
The dialect's list-view pattern has a separate source interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StructuralMatching

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open SpaceSemantics (matchValue matchValue_expression_of_not_cons)

inductive Structural : Atom → Prop where
  | var (name : String) : Structural (.var name)
  | symbol (name : String) : Structural (.symbol name)
  | grounded (value : GroundedValue) : Structural (.grounded value)
  | expression (items : List Atom)
      (notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest])
      (members : ∀ item ∈ items, Structural item) : Structural (.expression items)

private theorem matchLists (patterns values : List Atom) (initial : Subst)
    (ordinary : ∀ pattern ∈ patterns, ∀ current value,
      matchValue current pattern value = matchAtom current pattern value) :
    matchValue.matchValues initial patterns values = matchAtom.matchAtomList initial patterns values := by
  induction patterns generalizing initial values with
  | nil => cases values <;> simp [matchValue.matchValues, matchAtom.matchAtomList]
  | cons pattern patterns ih =>
    cases values with
    | nil => simp [matchValue.matchValues, matchAtom.matchAtomList]
    | cons value values =>
      simp only [matchValue.matchValues, matchAtom.matchAtomList, ordinary pattern (List.mem_cons_self ..)]
      cases matchAtom initial pattern value with
      | none => rfl
      | some bound =>
        exact ih values bound (fun item member => ordinary item (List.mem_cons_of_mem _ member))

theorem match_value {pattern : Atom} (structural : Structural pattern)
    (initial : Subst) (value : Atom) :
    matchValue initial pattern value = matchAtom initial pattern value := by
  induction structural generalizing initial value with
  | var name => cases value <;> simp [matchValue]
  | symbol name => cases value <;> simp [matchValue]
  | grounded payload => cases value <;> simp [matchValue]
  | expression items notCons nested ih =>
    cases value with
    | expression values =>
      rw [matchValue_expression_of_not_cons initial items values notCons]
      exact matchLists items values initial ih
    | var _ | symbol _ | grounded _ =>
      unfold matchValue
      split <;> simp_all [matchAtom]

theorem match_arguments (patterns values : List Atom) (initial : Subst)
    (structural : ∀ pattern ∈ patterns, Structural pattern) :
    matchValue.matchValues initial patterns values = matchAtom.matchAtomList initial patterns values :=
  matchLists patterns values initial (fun pattern member => match_value (structural pattern member))

theorem excludes_list_view (first rest : Atom) :
    ¬ Structural (.expression [.symbol "cons", first, rest]) := by
  intro accepted
  cases accepted with
  | expression _ ordinary _ => exact ordinary first rest rfl

end Mettapedia.Languages.MeTTa.PeTTa.StructuralMatching
