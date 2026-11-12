import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfInBodies

/-!
# Why a declared branch of `if` is not yet covered: the frontier's frame is fixed only up to meaning

On the scoped lookup, `(if True 1 2)` selects a fresh copy `$t` of `if`'s arrow, the operator meets
it by recording `t = t1` (`ScopedIf.operator_accepts`), and the query of `if`'s rows reads the taken
branch `1`, whose stored type is `Number`, and casts it against `$t`. That cast succeeds or fails
depending on the frame the query reached.

HE's frontier gives the frame of a matching row only through `LogicalMergeRel`: any bindings with the
same solutions and the same names as the row's match merged into the call's frame. HE's spec admits
representative cycles there (`Steps.representative_cycle_does_not_make_constraints_inconsistent`).

* `cycle_admitted`: for the row's match `{then1 := 1, else1 := 2}` and the call's frame `{t = t1}`, the
  bindings `{t := $t1, t1 := $t, then1 := 1, else1 := 2}` are a logical merge.
* `cycle_rejects_number`: at those bindings no type match of `$t` with `Number` exists, under either
  matching policy: HE's merge of `t := Number` must match `$t1` with `Number`, which must match `$t`
  with `Number` again, and a derivation is finite.
* `cycle_cast_error`: there HE's cast of the declared branch `1` against `$t` derives the failure
  rule and publishes `(Error 1 (BadType $t Number))`, under either matching policy.
* `syntactic_accepts_number`, `syntactic_cast_succeeds` (positive controls): at the syntactic merge
  `{then1 := 1, else1 := 2, t = t1}` the match exists and the cast keeps `1`.

So on HE's model a run of `(pair (if True 1 2) (if True True False))` may publish a cast error for a
reason HE's interpreter does not have (it merges syntactically; its answer is `[(pair 1 True)]`). The
every-run statement for declared branches therefore needs a model refinement: the frontier's frame as
a syntactic merge, or a type match invariant under logical equivalence of frames. Undeclared branches
meet `$t` by `undefinedRight` at every frame and are not affected (`IfInBodies`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DeclaredBranchGap

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied
  applyTypeValuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (specBindingVars LogicalMergeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open AnswerBags.Controls (sym)

/-- The match of `(if True 1 2)` against the fresh row pattern `(if True $then1 $else1)`. -/
def rowMatch : Bindings := ⟨[("then1", .grounded (.int 1)), ("else1", .grounded (.int 2))], []⟩

/-- The call's frame after the operator met its arrow: `{t = t1}`. -/
def callFrame : Bindings := Bindings.empty.addEquality "t" "t1"

/-- A representative cycle for `t = t1`, with the row's match. -/
def cycleFrame : Bindings :=
  ⟨[("t", .var "t1"), ("t1", .var "t"), ("then1", .grounded (.int 1)),
    ("else1", .grounded (.int 2))], []⟩

/-- The syntactic merge of the row's match into the call's frame. -/
def syntacticFrame : Bindings :=
  ⟨rowMatch.assignments ++ callFrame.assignments, rowMatch.equalities ++ callFrame.equalities⟩

/-! ## The cycle is a logical merge -/

theorem cycle_solutions (v : String → Atom) :
    TypeBindingSatisfied v cycleFrame ↔ TypeBindingSatisfied v syntacticFrame := by
  simp only [TypeBindingSatisfied, cycleFrame, syntacticFrame, rowMatch, callFrame, Bindings.empty,
    Bindings.addEquality, List.mem_cons, List.not_mem_nil, Prod.mk.injEq,
    or_false, List.nil_append, List.append_nil]
  constructor
  · rintro ⟨assignments, _⟩
    refine ⟨fun name value member => ?_, fun left right member => ?_⟩
    · rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact assignments _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact assignments _ _ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · obtain ⟨rfl, rfl⟩ := member
      have first := assignments "t" (.var "t1") (Or.inl ⟨rfl, rfl⟩)
      simpa [applyTypeValuation] using first
  · rintro ⟨assignments, equalities⟩
    have same := equalities "t" "t1" ⟨rfl, rfl⟩
    refine ⟨fun name value member => ?_, fun left right member => by simp at member⟩
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [applyTypeValuation] using same
    · simpa [applyTypeValuation] using same.symm
    · exact assignments _ _ (Or.inl ⟨rfl, rfl⟩)
    · exact assignments _ _ (Or.inr ⟨rfl, rfl⟩)

theorem cycle_support (name : String) :
    name ∈ specBindingVars cycleFrame ↔ name ∈ specBindingVars syntacticFrame := by
  simp only [specBindingVars, cycleFrame, syntacticFrame, rowMatch, callFrame, Bindings.empty,
    Bindings.addEquality, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **The frontier may present `t = t1` as a cycle**: `{t := $t1, t1 := $t, then1 := 1,
else1 := 2}` is a logical merge of the row's match into the call's frame. -/
theorem cycle_admitted : LogicalMergeRel rowMatch callFrame cycleFrame := by
  refine ⟨⟨cycle_solutions, cycle_support⟩, ?_⟩
  refine ⟨fun name => if name = "then1" then .grounded (.int 1)
    else if name = "else1" then .grounded (.int 2) else .symbol "A", ?_⟩
  refine ⟨fun name value member => ?_, fun left right member => by simp [cycleFrame] at member⟩
  simp only [cycleFrame, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [applyTypeValuation]

/-! ## No match of `$t` with `Number` at the cycle -/

theorem cycle_t : cycleFrame.classValues "t" = [.var "t1"] := by decide
theorem cycle_t1 : cycleFrame.classValues "t1" = [.var "t"] := by decide

/-- The other name of the cycle. -/
def other : String → String
  | "t" => "t1"
  | _ => "t"

theorem cycle_values {x : String} (inCycle : x = "t" ∨ x = "t1") :
    cycleFrame.classValues x = [.var (other x)] := by
  rcases inCycle with rfl | rfl
  · exact cycle_t
  · exact cycle_t1

theorem other_in {x : String} (inCycle : x = "t" ∨ x = "t1") :
    other x = "t" ∨ other x = "t1" := by
  rcases inCycle with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem match_var_symbol {p : Parameters} {x : String} {s : String} {m : Bindings}
    (matched : MatchRel p (.var x) (.symbol s) m) : m = Bindings.empty.assign x (.symbol s) := by
  cases matched with
  | varNonVar _ _ => rfl

theorem constraints_assign (x : String) (v : Atom) :
    constraints (Bindings.empty.assign x v) = [.value x v] := by
  simp [constraints, Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup,
    List.eraseDups_cons]

theorem single_value {x : String} {first : Atom} {rest : List Atom}
    (inCycle : x = "t" ∨ x = "t1") (hvalues : (first :: rest).Perm (cycleFrame.classValues x)) :
    first = .var (other x) ∧ rest = [] := by
  rw [cycle_values inCycle] at hvalues
  have := List.perm_singleton.mp hvalues
  simp only [List.cons.injEq] at this
  exact this

mutual
/-- No merge of `x := Number` into the cycle, for `x` either name of it: every derivation would
contain a smaller one of the same kind. -/
theorem no_add {p : Parameters} : ∀ {b : Bindings} {x : String} {v : Atom} {out : Bindings},
    AddVarBindingRel p b x v out → b = cycleFrame → v = .symbol "Number" →
      (x = "t" ∨ x = "t1") → False
  | _, _, _, _, .fresh hvalues => fun hb _ inCycle => by
      rw [hb, cycle_values inCycle] at hvalues
      cases hvalues
  | _, _, _, _, .same hvalues _ same => fun hb hv inCycle => by
      rw [hb] at hvalues
      obtain ⟨hfirst, _⟩ := single_value inCycle hvalues
      rw [hv, hfirst] at same
      cases same
  | _, x, _, _, .conflict hvalues _ _ matched merged => fun hb hv inCycle => by
      rw [hb] at hvalues
      obtain ⟨hfirst, _⟩ := single_value inCycle hvalues
      rw [hfirst, hv] at matched
      exact no_merge merged hb (other x) (other_in inCycle) (match_var_symbol matched)
  | _, _, _, _, .reconcile hvalues notAgree _ _ => fun hb _ inCycle => by
      rw [hb] at hvalues
      obtain ⟨hfirst, hrest⟩ := single_value inCycle hvalues
      rw [hfirst, hrest] at notAgree
      exact notAgree (by simp [ValuesAgree])

theorem no_merge {p : Parameters} : ∀ {b m out : Bindings},
    MergeRel p b m out → b = cycleFrame → ∀ y : String, (y = "t" ∨ y = "t1") →
      m = Bindings.empty.assign y (.symbol "Number") → False
  | _, _, _, .mk perm folded => fun hb y inCycle hm => by
      rw [hm, constraints_assign] at perm
      have same := List.perm_singleton.mp perm
      exact no_constraints folded hb y inCycle same

theorem no_constraints {p : Parameters} :
    ∀ {b : Bindings} {order : List Constraint} {out : Bindings},
    MergeConstraintsRel p b order out → b = cycleFrame → ∀ y : String, (y = "t" ∨ y = "t1") →
      order = [.value y (.symbol "Number")] → False
  | _, _, _, .nil => fun _ _ _ same => by cases same
  | _, _, _, .value add _ => fun hb y inCycle same => by
      simp only [List.cons.injEq, Constraint.value.injEq] at same
      obtain ⟨⟨hx, hv⟩, _⟩ := same
      rw [← hx] at inCycle
      exact no_add add hb hv inCycle
  | _, _, _, .equality _ _ => fun _ _ _ same => by cases same
end

/-- **At the cycle, `$t` matches no `Number`**: the cast of the declared branch `1` against `if`'s
fresh return type fails there. -/
theorem cycle_rejects_number : ¬ ∃ out, TypeMatchRel (.var "t") (sym "Number") cycleFrame out := by
  rintro ⟨out, matched⟩
  generalize sameE : Atom.var "t" = E at matched
  generalize sameA : sym "Number" = A at matched
  cases matched with
  | undefinedLeft => cases sameE
  | atomLeft => cases sameE
  | undefinedRight => simp [Atom.undefinedType] at sameA
  | atomRight => simp [Atom.atomType] at sameA
  | structural _ _ _ _ inner merged =>
      subst sameE sameA
      exact no_merge merged rfl "t" (Or.inl rfl) (match_var_symbol inner)

/-- Under either matching policy. -/
theorem cycle_rejects_number_policy (policy : Policy) :
    ¬ ∃ out, policy.matching.Rel (.var "t") (sym "Number") cycleFrame out := by
  rintro ⟨out, matched⟩
  exact cycle_rejects_number
    ⟨out, Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.TypeMatchingPolicy.Rel.source matched⟩

/-- **Positive control**: at the syntactic merge the match exists, binding `t := Number`. -/
theorem syntactic_accepts_number :
    ∃ out, TypeMatchRel (.var "t") (sym "Number") syntacticFrame out :=
  ⟨_, TypeMatchRel.expected_variable_symbol "t" "Number" syntacticFrame (by decide) (by decide)
    (by decide)⟩

/-- The stored type of `1` in HE's `if` program. -/
theorem one_types : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel
    (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram) (.grounded (.int 1))
    [sym "Number"] :=
  .groundedKnown (.int 1) (by simp [Atom.undefinedType])

/-- **At the cycle, HE's cast of the declared branch `1` against `$t` publishes a `BadType` error**,
under either matching policy: the cast's failure rule applies, since no type of `1` matches `$t`
there. HE's interpreter casts `1` successfully and answers `[(pair 1 True)]`. -/
theorem cycle_cast_error (policy : Policy) :
    Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel
      (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram) (.grounded (.int 1))
      (.var "t") cycleFrame
      [(Mettapedia.Languages.MeTTa.HE.mkError (.grounded (.int 1)) (.badType (.var "t") (sym "Number")),
        cycleFrame)]
      (lookup := Mettapedia.Languages.MeTTa.HE.Spec.Type.rawTypeLookupRel
        (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram))
      (matching := policy.matching.Rel) :=
  .failure one_types fun candidateType member candidate matched => by
    rw [List.mem_singleton] at member
    subst member
    exact cycle_rejects_number_policy policy ⟨candidate, matched⟩

/-- **Positive control**: at the syntactic merge the cast of `1` against `$t` succeeds and keeps
`1`. -/
theorem syntactic_cast_succeeds : ∃ out,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel
      (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram) (.grounded (.int 1))
      (.var "t") syntacticFrame [(.grounded (.int 1), out)]
      (lookup := Mettapedia.Languages.MeTTa.HE.Spec.Type.rawTypeLookupRel
        (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram)) := by
  obtain ⟨out, matched⟩ := syntactic_accepts_number
  exact ⟨out, .success one_types (earlierTypes := []) (laterTypes := []) rfl
    (fun _ member => by cases member) matched⟩

#print axioms cycle_solutions
#print axioms cycle_admitted
#print axioms cycle_rejects_number
#print axioms cycle_rejects_number_policy
#print axioms syntactic_accepts_number
#print axioms cycle_cast_error
#print axioms syntactic_cast_succeeds

end DeclaredBranchGap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
