import Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiteralQuerySource

/-!
# Query patterns fixed by the current substitution

Every variable is read from the actual incoming substitution. Structural
patterns exclude the special list view; their matcher cannot extend or
replace the incoming bindings. Checked capture also requires a literal
result and ordinary query heads. Open captures and active query forms refuse.
This is not the scoped unifier's principal-environment capture operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.BoundQueryPattern

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics

inductive Frozen (bindings : Subst) : Atom → Prop where
  | var (name : String) (value : Atom) (bound : Subst.lookup bindings name = some value) : Frozen bindings (.var name)
  | symbol (name : String) : Frozen bindings (.symbol name)
  | grounded (value : GroundedValue) : Frozen bindings (.grounded value)
  | expression (items : List Atom)
      (notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest])
      (members : ∀ item ∈ items, Frozen bindings item) : Frozen bindings (.expression items)

theorem Frozen.match_exact {bindings : Subst} {pattern : Atom} (frozen : Frozen bindings pattern) (value : Atom) :
    matchValue bindings pattern value = if applySubst bindings pattern = value then some bindings else none := by
  induction frozen generalizing value with
  | var name read bound =>
      by_cases same : value = read
      · subst value
        simp [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, applySubst, bound]
      · simp [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, applySubst, bound, same, Ne.symm same]
  | symbol name => cases value <;> simp [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, applySubst]
  | grounded ground => cases value <;> simp [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, applySubst]
  | expression patterns notCons members ih =>
      have lists (values : List Atom) : matchValue.matchValues bindings patterns values =
          if applySubst.applySubstList bindings patterns = values then some bindings else none := by
        clear notCons members
        induction patterns generalizing values with
        | nil => cases values <;> simp [matchValue.matchValues, applySubst.applySubstList]
        | cons first rest tail =>
            cases values with
            | nil => simp [matchValue.matchValues, applySubst.applySubstList]
            | cons value values =>
                simp only [matchValue.matchValues, ih first List.mem_cons_self value,
                  applySubst.applySubstList]
                by_cases same : applySubst bindings first = value
                · simp only [same, ↓reduceIte, List.cons.injEq, true_and]
                  exact tail (fun item member => ih item (List.mem_cons_of_mem _ member)) values
                · simp [same]
      cases value with
      | expression values =>
          rw [matchValue_expression_of_not_cons bindings patterns values notCons, lists]
          simp [applySubst]
      | var name | symbol name | grounded ground =>
          unfold matchValue
          split <;> simp_all [applySubst]

def check (bindings : Subst) : Atom → Bool
  | .var name => (Subst.lookup bindings name).isSome
  | .symbol _ | .grounded _ => true
  | .expression items => !LiteralQuerySource.consView items && items.attach.all (fun item => check bindings item.val)
termination_by atom => sizeOf atom
decreasing_by
  have smaller := List.sizeOf_lt_of_mem item.property
  simp_wf
  omega

theorem check_iff (bindings : Subst) (pattern : Atom) : check bindings pattern = true ↔ Frozen bindings pattern := by
  cases pattern with
  | var name =>
      constructor
      · intro ready
        rw [check] at ready
        obtain ⟨value, bound⟩ := Option.isSome_iff_exists.mp ready
        exact Frozen.var name value bound
      · intro frozen
        cases frozen with
        | var _ value bound => simp [check, bound]
  | symbol name => simp [check, Frozen.symbol]
  | grounded value => simp [check, Frozen.grounded]
  | expression items =>
      rw [check, Bool.and_eq_true, Bool.not_eq_true', LiteralQuerySource.consView_false]
      constructor
      · rintro ⟨ordinary, all⟩
        apply Frozen.expression items ordinary
        intro item member
        exact (check_iff bindings item).mp (List.all_eq_true.mp all ⟨item, member⟩ (by simp))
      · intro frozen
        cases frozen with
        | expression _ ordinary members =>
            refine ⟨ordinary, List.all_eq_true.mpr ?_⟩
            intro item _
            exact (check_iff bindings item.val).mpr (members item.val item.property)
termination_by sizeOf pattern
decreasing_by
  · have smaller := List.sizeOf_lt_of_mem member
    simp_wf
    omega
  · have smaller := List.sizeOf_lt_of_mem item.property
    simp_wf
    omega

structure Captured (bindings : Subst) (pattern : Atom) : Type where
  frozen : Frozen bindings pattern
  literal : Literal (applySubst bindings pattern)
  ordinarySource : LiteralQuerySource.ordinaryQuery pattern = true
  ordinaryValue : LiteralQuerySource.ordinaryQuery (applySubst bindings pattern) = true

def capture (bindings : Subst) (pattern : Atom) : Option (Captured bindings pattern) :=
  if ready : check bindings pattern = true then
    if closed : LiteralQuerySource.checkLiteral (applySubst bindings pattern) = true then
      if ordinary : LiteralQuerySource.ordinaryQuery pattern = true then
        if resultOrdinary : LiteralQuerySource.ordinaryQuery (applySubst bindings pattern) = true then
          some ⟨(check_iff bindings pattern).mp ready,
            (LiteralQuerySource.checkLiteral_iff _).mp closed, ordinary, resultOrdinary⟩
        else none
      else none
    else none
  else none

theorem capture_complete {bindings : Subst} {pattern : Atom} (certificate : Captured bindings pattern) :
    capture bindings pattern = some certificate := by
  simp [capture, (check_iff bindings pattern).mpr certificate.frozen,
    (LiteralQuerySource.checkLiteral_iff _).mpr certificate.literal,
    certificate.ordinarySource, certificate.ordinaryValue]

theorem Captured.match_exact {bindings : Subst} {pattern : Atom} (certificate : Captured bindings pattern)
    (value : Atom) :
    matchValue bindings pattern value = if applySubst bindings pattern = value then some bindings else none :=
  certificate.frozen.match_exact value

theorem Captured.matches_bound_literal {bindings : Subst} {pattern : Atom} (certificate : Captured bindings pattern)
    (value : Atom) : matchValue bindings pattern value = matchValue bindings (applySubst bindings pattern) value := by
  rw [certificate.match_exact, matchValue_literal certificate.literal]

theorem Frozen.extends {bindings later : Subst} {pattern : Atom} (frozen : Frozen bindings pattern)
    (extended : later.lookupExtends bindings) : Frozen later pattern := by
  induction frozen with
  | var name value bound => exact .var name value (extended name value bound)
  | symbol name => exact .symbol name
  | grounded value => exact .grounded value
  | expression items ordinary _ ih => exact .expression items ordinary ih

theorem Frozen.subst_ext {bindings later : Subst} {pattern : Atom} (frozen : Frozen bindings pattern)
    (extended : later.lookupExtends bindings) : applySubst later pattern = applySubst bindings pattern := by
  induction frozen with
  | var name value bound => simp [applySubst, bound, extended name value bound]
  | symbol | grounded => rfl
  | expression items ordinary members ih =>
      clear ordinary members
      simp only [applySubst]
      congr 1
      induction items with
      | nil => rfl
      | cons first rest tail =>
          simp only [applySubst.applySubstList, List.cons.injEq]
          exact ⟨ih first List.mem_cons_self, tail (fun item member => ih item (List.mem_cons_of_mem _ member))⟩

def Captured.extend {bindings later : Subst} {pattern : Atom} (certificate : Captured bindings pattern)
    (extended : later.lookupExtends bindings) : Captured later pattern where
  frozen := certificate.frozen.extends extended
  literal := by simpa only [certificate.frozen.subst_ext extended] using certificate.literal
  ordinarySource := certificate.ordinarySource
  ordinaryValue := by simpa only [certificate.frozen.subst_ext extended] using certificate.ordinaryValue

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.BoundQueryPattern
