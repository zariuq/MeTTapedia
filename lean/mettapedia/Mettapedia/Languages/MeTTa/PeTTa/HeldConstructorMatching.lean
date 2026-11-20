import Mettapedia.Languages.MeTTa.PeTTa.UnifyingGround
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement
import Mettapedia.Languages.MeTTa.PeTTa.HeldArgumentSpecialization

/-!
# Constructor matching at a captured continuation boundary

The operands here have completed evaluation. The first-order equality
contract uses the existing two-sided unifier; the specialized boundary uses
the existing one-sided matcher. On a ground value and a ground incoming
binding range they choose exactly the same continuation and substitution.
Exhaustion is retained as an unavailable decision, never a false answer.
The ground range concerns ordinary value slots. Captured source is separate
syntax and may still mention unknowns subsequently refined by the match.

Captured source may mention unknowns which matching subsequently binds.
Those refinements remain visible when the compiler hides a callee's fresh
lexical locals. The projection theorem states the required freshness law.
This is a primitive/continuation correspondence, not a verification of the
C implementation or of the complete text of a library.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.HeldConstructorMatching

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
  (Subst applySubst atomFreeVars isGroundAtom matchAtom)
open Unifying (Unified Control Configuration resolve GroundRange)

/-- Swapping a ground operand preserves the actual solved bindings, not
merely solvability. General two-variable unification has no such equality. -/
theorem unifyTerms_ground_swap (fuel : Nat) :
    ∀ (bindings : Subst) (pattern value : Atom), GroundRange bindings →
      isGroundAtom value = true → Unifying.atomSize value < fuel →
      Unifying.unifyTerms fuel bindings value pattern =
        Unifying.unifyTerms fuel bindings pattern value := by
  induction fuel with
  | zero => intro _ _ _ _ _ small; omega
  | succ fuel ih =>
      intro bindings pattern value range ground small
      have lists : ∀ (values patterns : List Atom) (current : Subst),
          GroundRange current → (∀ item ∈ values, isGroundAtom item = true) →
          (∀ item ∈ values, Unifying.atomSize item < fuel) →
          Unifying.unifyLists (Unifying.unifyTerms fuel) current values patterns =
            Unifying.unifyLists (Unifying.unifyTerms fuel) current patterns values := by
        intro values
        induction values with
        | nil => intro patterns current _ _ _; cases patterns <;> rfl
        | cons first rest tail =>
            intro patterns current currentRange groundValues sizes
            cases patterns with
            | nil => rfl
            | cons other others =>
                simp only [Unifying.unifyLists]
                rw [ih current other first currentRange
                  (groundValues first (by simp)) (sizes first (by simp))]
                cases decided : Unifying.unifyTerms fuel current other first with
                | clash => rfl
                | exhausted => rfl
                | ok middle =>
                    have bridge := Unifying.unifyTerms_ground fuel current other first currentRange
                      (groundValues first (by simp)) (sizes first (by simp))
                    rw [decided] at bridge
                    have matched : matchAtom current other first = some middle := by
                      cases found : matchAtom current other first with
                      | none => simp [found, Unifying.ofMatch] at bridge
                      | some next =>
                          have same : middle = next := by
                            simpa [found, Unifying.ofMatch] using bridge
                          simp [same]
                    exact tail others middle (Unifying.matchAtom_groundRange currentRange
                      (groundValues first (by simp)) matched)
                      (fun item member => groundValues item (List.mem_cons_of_mem first member))
                      (fun item member => sizes item (List.mem_cons_of_mem first member))
      have resolved : resolve bindings value = value :=
        Unifying.applySubst_ground bindings value ground
      conv_lhs => rw [Unifying.unifyTerms]
      conv_rhs => rw [Unifying.unifyTerms]
      simp only [resolved]
      cases shape : resolve bindings pattern with
      | var name =>
          have absent := Unifying.occurs_ground (name := name) ground
          cases value <;> simp [isGroundAtom] at ground <;> simp [absent]
      | symbol name => cases value <;> simp [isGroundAtom] at ground <;> simp [eq_comm]
      | grounded literal => cases value <;> simp [isGroundAtom] at ground <;> simp [eq_comm]
      | expression patterns =>
          cases value with
          | var name => simp [isGroundAtom] at ground
          | symbol name => rfl
          | grounded literal => rfl
          | expression values =>
              exact lists values patterns bindings range
                (fun item member => Unifying.isGround_of_mem member ground)
                (fun item member => Nat.lt_of_lt_of_le
                  (Unifying.atomSize_lt_of_mem member) (Nat.le_of_lt_succ small))

theorem unify_ground_value_first (bindings : Subst) (pattern value : Atom)
    (range : GroundRange bindings) (ground : isGroundAtom value = true) :
    Unifying.unify bindings value pattern = Unifying.ofMatch (matchAtom bindings pattern value) := by
  have fuelSwap : Unifying.fuelFor bindings value pattern =
      Unifying.fuelFor bindings pattern value := by
    simp only [Unifying.fuelFor]
    omega
  unfold Unifying.unify
  rw [fuelSwap, unifyTerms_ground_swap _ bindings pattern value range ground
    (by unfold Unifying.fuelFor; omega)]
  exact Unifying.unifyTerms_ground _ bindings pattern value range ground
    (by unfold Unifying.fuelFor; omega)

/-- The completed equality primitive followed by its authored branches. -/
def unificationContinuation (bindings : Subst) (pattern value yes no : Atom) : Option Control :=
  match Unifying.unify bindings pattern value with
  | .ok refined => some (.evaluate refined yes)
  | .clash => some (.evaluate bindings no)
  | .exhausted => none

/-- A constructor matcher followed by either the bound or original branch. -/
def matchingContinuation (bindings : Subst) (pattern value yes no : Atom) : Control :=
  match matchAtom bindings pattern value with
  | some refined => .evaluate refined yes
  | none => .evaluate bindings no

theorem continuation_correspondence (bindings : Subst) (pattern value yes no : Atom)
    (range : GroundRange bindings) (ground : isGroundAtom value = true) :
    unificationContinuation bindings pattern value yes no =
      some (matchingContinuation bindings pattern value yes no) := by
  unfold unificationContinuation matchingContinuation
  rw [Unifying.unify_ground range ground]
  cases matchAtom bindings pattern value <;> rfl

theorem continuation_correspondence_value_first (bindings : Subst) (pattern value yes no : Atom)
    (range : GroundRange bindings) (ground : isGroundAtom value = true) :
    unificationContinuation bindings value pattern yes no =
      some (matchingContinuation bindings pattern value yes no) := by
  unfold unificationContinuation matchingContinuation
  rw [unify_ground_value_first bindings pattern value range ground]
  cases matchAtom bindings pattern value <;> rfl

/-- No state, I/O, scope supply or surrounding frame changes at the matching
boundary. Equal controls therefore give equal subsequent machine behavior. -/
theorem configuration_correspondence (before : Configuration)
    (bindings : Subst) (pattern value yes no : Atom)
    (range : GroundRange bindings) (ground : isGroundAtom value = true) :
    (unificationContinuation bindings pattern value yes no).map
        (fun control => {before with control}) =
      some {before with control := matchingContinuation bindings pattern value yes no} := by
  rw [continuation_correspondence bindings pattern value yes no range ground]
  rfl

/-- The equality primitive's complete answer carries the branch substitution. -/
def equalityCompletion (bindings : Subst) (pattern value : Atom) : Option Unifying.Answer :=
  match Unifying.unify bindings pattern value with
  | .ok refined => some ⟨Effects.boolean true, refined⟩
  | .clash => some ⟨Effects.boolean false, bindings⟩
  | .exhausted => none

/-- The actual source machine's branch frame consumes the completed equality
answer exactly as the specialized match boundary does. -/
theorem equality_branch_step (registry : SpaceSemantics.Program) (before : Configuration)
    (bindings : Subst) (pattern value yes no : Atom)
    (range : GroundRange bindings) (ground : isGroundAtom value = true) :
    (equalityCompletion bindings pattern value).bind (fun answer =>
      Unifying.step registry { before with
        control := .returned [answer]
        frames := .branch yes no :: before.frames }) =
      some { before with
        control := .sequence [matchingContinuation bindings pattern value yes no] [] } := by
  unfold equalityCompletion
  rw [Unifying.unify_ground range ground]
  cases matched : matchAtom bindings pattern value <;>
    simp [Unifying.ofMatch, Unifying.step, matchingContinuation, matched, Effects.boolean]

theorem equality_branch_step_value_first (registry : SpaceSemantics.Program) (before : Configuration)
    (bindings : Subst) (pattern value yes no : Atom)
    (range : GroundRange bindings) (ground : isGroundAtom value = true) :
    (equalityCompletion bindings value pattern).bind (fun answer =>
      Unifying.step registry { before with
        control := .returned [answer]
        frames := .branch yes no :: before.frames }) =
      some { before with
        control := .sequence [matchingContinuation bindings pattern value yes no] [] } := by
  unfold equalityCompletion
  rw [unify_ground_value_first bindings pattern value range ground]
  cases matched : matchAtom bindings pattern value <;>
    simp [Unifying.ofMatch, Unifying.step, matchingContinuation, matched, Effects.boolean]

theorem successful_match_enters_refined_branch {bindings refined : Subst}
    {pattern value yes no : Atom}
    (matched : matchAtom bindings pattern value = some refined) :
    matchingContinuation bindings pattern value yes no = .evaluate refined yes := by
  simp [matchingContinuation, matched]

theorem failed_match_enters_original_branch {bindings : Subst}
    {pattern value yes no : Atom}
    (failed : matchAtom bindings pattern value = none) :
    matchingContinuation bindings pattern value yes no = .evaluate bindings no := by
  simp [matchingContinuation, failed]

theorem ground_range_idempotent {bindings : Subst} (range : GroundRange bindings) :
    Unifying.Idempotent bindings := by
  intro name value found other present
  have empty := Unifying.freeVars_ground value (Unifying.lookup_ground range found)
  rw [empty] at present
  cases present

/-- A successful match refines the source's captured unknowns as well as its
immediate pattern. This is derived from the actual unifier's soundness. -/
theorem successful_match_refines_capture {bindings refined : Subst}
    {pattern value : Atom} (range : GroundRange bindings)
    (ground : isGroundAtom value = true)
    (matched : matchAtom bindings pattern value = some refined) (captured : Atom) :
    resolve refined (resolve bindings captured) = resolve refined captured ∧
      resolve refined pattern = value := by
  have unified : Unifying.unify bindings pattern value = .ok refined := by
    rw [Unifying.unify_ground range ground, matched]
    rfl
  have sound := Unifying.unifyTerms_sound _ bindings refined pattern value
    (ground_range_idempotent range) unified
  exact ⟨sound.2.1 captured,
    sound.2.2.trans (Unifying.applySubst_ground refined value ground)⟩

theorem successful_match_keeps_old_values {bindings refined : Subst}
    {pattern value : Atom} (matched : matchAtom bindings pattern value = some refined) :
    Unifying.Keeps bindings refined := Unifying.matchAtom_keeps matched

/-- A literal constructor subtree contributes no bindings. Comparing it as
a whole avoids unfolding every path through a shared ground DAG. -/
theorem literal_subtree_match (bindings : Subst) (pattern value : Atom)
    (literal : SpaceSemantics.Literal pattern) :
    matchAtom bindings pattern value =
      if pattern = value then some bindings else none :=
  SpaceSemantics.matchAtom_literal literal bindings value

/-- A fresh field receives the input value itself. This is a value-origin
law; physical slot storage and allocator calls are outside its statement. -/
theorem fresh_field_reuses_value (bindings : Subst) (name : String) (value : Atom)
    (fresh : bindings.lookup name = none) (range : GroundRange bindings)
    (ground : isGroundAtom value = true) :
    Unifying.unify bindings (.var name) value = .ok ((name, value) :: bindings) := by
  rw [Unifying.unify_ground range ground]
  simp [matchAtom, fresh, Unifying.ofMatch]

theorem fresh_field_reuses_value_first (bindings : Subst) (name : String) (value : Atom)
    (fresh : bindings.lookup name = none) (range : GroundRange bindings)
    (ground : isGroundAtom value = true) :
    Unifying.unify bindings value (.var name) = .ok ((name, value) :: bindings) := by
  rw [unify_ground_value_first bindings (.var name) value range ground]
  simp [matchAtom, fresh, Unifying.ofMatch]

theorem matched_field_is_still_ground {bindings refined : Subst}
    {pattern value : Atom} (range : GroundRange bindings)
    (ground : isGroundAtom value = true)
    (matched : matchAtom bindings pattern value = some refined) :
    GroundRange refined := Unifying.matchAtom_groundRange range ground matched

/-- Compiler-only lexical locals and logical refinements have distinct
visibility when source is read through a saved caller caller. -/
structure ScopedBinding where
  name : String
  value : Atom
  refinement : Bool

def allBindings (suffix : List ScopedBinding) : Subst :=
  suffix.map fun binding => (binding.name, binding.value)

def refinedBindings (suffix : List ScopedBinding) : Subst :=
  suffix.filterMap fun binding =>
    if binding.refinement then some (binding.name, binding.value) else none

theorem projected_lookup (caller : Subst) (suffix : List ScopedBinding) (name : String)
    (fresh : ∀ binding ∈ suffix, binding.refinement = false → binding.name ≠ name) :
    (allBindings suffix ++ caller).lookup name =
      (refinedBindings suffix ++ caller).lookup name := by
  induction suffix with
  | nil => rfl
  | cons binding rest ih =>
      have tail := ih (fun other member => fresh other (List.mem_cons_of_mem _ member))
      cases marked : binding.refinement with
      | true =>
          simp only [allBindings, List.map_cons, List.cons_append,
            refinedBindings, List.filterMap_cons, marked, ↓reduceIte,
            Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
            List.find?_cons] at tail ⊢
          split <;> simp_all
      | false =>
          have different := fresh binding (by simp) marked
          simp only [allBindings, List.map_cons, List.cons_append,
            refinedBindings, List.filterMap_cons, marked, ↓reduceIte,
            Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
            List.find?_cons, show (binding.name == name) = false by simpa using different,
            Bool.false_eq_true, ↓reduceIte]
          exact tail

theorem projected_capture_readout (caller : Subst) (suffix : List ScopedBinding)
    (captured : Atom)
    (fresh : ∀ binding ∈ suffix, binding.refinement = false →
      binding.name ∉ atomFreeVars captured) :
    resolve (allBindings suffix ++ caller) captured =
      resolve (refinedBindings suffix ++ caller) captured := by
  match captured with
  | .var name =>
      have lookup := projected_lookup caller suffix name
        (fun binding member localKey same => fresh binding member localKey (by simp [atomFreeVars, same]))
      simpa only [resolve, applySubst] using congrArg (fun found => found.getD (.var name)) lookup
  | .symbol _ | .grounded _ => rfl
  | .expression items =>
      simp only [resolve, applySubst, Atom.expression.injEq]
      exact list caller suffix items
        (fun item _ freshItem => projected_capture_readout caller suffix item freshItem) fresh
termination_by sizeOf captured
where
  list (caller : Subst) (suffix : List ScopedBinding) (items : List Atom)
      (ih : ∀ item ∈ items,
        (∀ binding ∈ suffix, binding.refinement = false → binding.name ∉ atomFreeVars item) →
        applySubst (allBindings suffix ++ caller) item =
          applySubst (refinedBindings suffix ++ caller) item)
      (fresh : ∀ binding ∈ suffix, binding.refinement = false →
        binding.name ∉ Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars.atomFreeVarsList items) :
      applySubst.applySubstList (allBindings suffix ++ caller) items =
        applySubst.applySubstList (refinedBindings suffix ++ caller) items := by
    induction items with
    | nil => rfl
    | cons first rest tail =>
        simp only [applySubst.applySubstList]
        rw [ih first (by simp)
          (fun binding member localKey present => fresh binding member localKey (by
            simp [atomFreeVars.atomFreeVarsList, present])),
          tail (fun item member => ih item (List.mem_cons_of_mem first member))
            (fun binding member localKey present => fresh binding member localKey (by
              simp [atomFreeVars.atomFreeVarsList, present]))]

namespace Controls

def pair (left right : Atom) : Atom := .expression [.symbol "Pair", left, right]

theorem a_whole_value_is_a_single_fresh_field :
    matchingContinuation [] (.var "whole") (pair (.grounded (.int 3)) (.grounded (.int 5)))
      (.var "whole") (.symbol "no") =
      .evaluate [("whole", pair (.grounded (.int 3)) (.grounded (.int 5)))] (.var "whole") := by rfl

theorem the_empty_constructor_has_no_fields_to_bind :
    matchingContinuation [] (.expression []) (.expression []) (.symbol "yes") (.symbol "no") =
      .evaluate [] (.symbol "yes") := by rfl

theorem fresh_constructor_binds_both_fields :
    matchingContinuation [] (pair (.var "x") (.var "y"))
      (pair (.grounded (.int 3)) (.grounded (.int 5))) (.var "x") (.symbol "no") =
      .evaluate [("y", .grounded (.int 5)), ("x", .grounded (.int 3))] (.var "x") := by rfl

theorem mismatch_discards_tentative_bindings :
    matchingContinuation [] (pair (.var "x") (.var "x"))
      (pair (.grounded (.int 3)) (.grounded (.int 5))) (.var "x") (.symbol "no") =
      .evaluate [] (.symbol "no") := by rfl

theorem aliases_agree_when_fields_agree :
    (matchAtom [] (pair (.var "x") (.var "x"))
      (pair (.grounded (.int 3)) (.grounded (.int 3)))).isSome = true := by decide

theorem lexical_local_does_not_hide_refinement :
    resolve (refinedBindings [⟨"x", .grounded (.int 3), true⟩,
      ⟨"callee", .grounded (.int 9), false⟩]) (pair (.var "x") (.var "callee")) =
      pair (.grounded (.int 3)) (.var "callee") := by decide

theorem dropping_all_suffix_bindings_loses_the_answer :
    resolve [] (.var "x") ≠
      resolve (refinedBindings [⟨"x", .grounded (.int 3), true⟩]) (.var "x") := by decide

theorem lexical_freshness_is_needed_for_projection :
    resolve (allBindings [⟨"x", .grounded (.int 9), false⟩]) (.var "x") ≠
      resolve (refinedBindings [⟨"x", .grounded (.int 9), false⟩]) (.var "x") := by decide

theorem open_old_bindings_need_refinement_in_their_values :
    Unifying.unify [("alias", .var "x")] (.var "x") (.grounded (.int 3)) ≠
      Unifying.ofMatch (matchAtom [("alias", .var "x")] (.var "x") (.grounded (.int 3))) := by decide

theorem open_values_need_two_sided_unification :
    Unifying.unify [] (.symbol "a") (.var "open") ≠
      Unifying.ofMatch (matchAtom [] (.symbol "a") (.var "open")) := by decide

theorem arbitrary_unification_is_not_binding_symmetric :
    Unifying.unify [] (.var "x") (.var "y") ≠
      Unifying.unify [] (.var "y") (.var "x") := by decide

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.HeldConstructorMatching
