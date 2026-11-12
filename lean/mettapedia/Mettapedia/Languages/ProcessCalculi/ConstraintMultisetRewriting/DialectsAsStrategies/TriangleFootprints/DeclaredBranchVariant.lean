import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.VariantRuns

/-!
# Declared branches of `if` on the variant machine, and `(pair (if True 1 2) (if True True False))`

On HE's model a row hit carries any record with the meaning of the row's match merged into the
call's record, and `DeclaredBranchGap` shows a circular record among them at which the cast of a
declared branch of `if` against `if`'s fresh return type fails. HE's interpreter answers
`(pair (if True 1 2) (if True True False))` with `[(pair 1 True)]`.

On the variant machine of `SyntacticMerge` the hit carries the syntactic merge. This module proves
that there every run of `(if b y n)` with a Boolean literal and a data taken branch finishes with
the taken branch, at every frame, and that every run of that term finishes with `[(pair 1 True)]`.

## The record of the hit

* `arrows_match_out`: every type match of two fresh copies of `if`'s arrow records exactly their
  equality `u = w` (the operator's cast leaves the frame `before + {u = w}`).
* `if_record`: every match of `(if b y n)` with a fresh copy of the row `(if b $then $else)` is
  `{then' := y, else' := n}`, with both names outside the names visible to the query.
* `frontier_hits`: every work of a variant frontier is a hit of its row with the syntactic merge.
* `declared_cast`: at the record `{then' := y, else' := n} ++ before + {u = w}` the class of `u` has
  no value, so `$u` meets a symbolic type `s`, and the result has a model.

## The run

* `DeclaredBranches`: the conditions on the program and the call: both branches are data atoms with
  one closed stored type each, the taken branch's type is a symbol other than `%Undefined%` and
  `Atom`, and the call's region is HE's row for the condition. `UndeclaredBranches`: the same with
  an undeclared taken branch. `IfWalk`: what the run needs of either: the taken branch's cast against
  the fresh return name at a frame recording one more equality.
* `goodv_function_declared`, `goodv_query_walk`, `goodv_if_walk`: **every run of `(if b y n)` under
  `%Undefined%`, at every frame and under every continuation, goes on with the taken branch**;
  `goodv_if_declared`, `goodv_if_undeclared` for the two kinds of taken branch. For an undeclared
  taken branch the variant machine has the model's answers.
* `declared_if_every_run`: from the entry, every run of the variant machine finishes with the taken
  branch.
* `Controls.pair_if_every_run`: **every run of `(pair (if True 1 2) (if True True False))` on the
  variant machine finishes and publishes `[(pair 1 True)]`, and a complete run exists**, under
  either matching policy and either reentry policy.

## The proposed change to the model, with its effect

In the row step of the equation frontier (`EquationRowResultsRel.hit`), the work's record is any
`output` with `LogicalMergeRel matched incoming output`. The proposal: the work's record is

  `⟨matched.assignments ++ incoming.assignments, matched.equalities ++ incoming.equalities⟩`

under the premise that this record has a model. The `miss` rule keeps its meaning: a logical merge
exists exactly when that record has a model (`SyntacticMerge.logical_iff`). Its effect:

* no frontier is new, and every frontier of the model remains up to how each record is written
  (`SyntacticMerge.SynFrontierRel.sound`, `SyntacticMerge.frontier_represented`);
* every every-run result of the model holds as it stands (`SyntacticMerge.every_run_of_model`);
* declared branches of `if` have HE's answers on every run (`declared_if_every_run`,
  `Controls.pair_if_every_run`), which the model does not give (`DeclaredBranchGap.cycle_cast_error`).

The record is the one against which the model already defines its logical merge, and on the two
records of `DeclaredBranchGap` it is exactly the one output of the model's executable merge, in
either argument order, while the circular record is not an output
(`SyntacticMerge.Controls.native_merge_is_variant`, `native_merge_not_cycle`). Taking the outputs of
the executable merge as the hit's records is the alternative form of the change; the two forms are
compared here on that example only. Where the match binds a name that the incoming record also
binds, the concatenation holds both assignments, and HE's merge reconciles them. No call in this
development reaches that case (a query is read at its frame first); the comparison there is open.

The rule for primitive `unify` takes a logical merge in the same way, with the same circular record
among its candidates (`UnifyCandidateGap`); the same change belongs in that rule. The run proved
here passes through no `unify`.

## Controls

* `Controls.one_every_run`, `Controls.false_every_run`, `Controls.bool_every_run` (positive):
  `(if True 1 2)`, `(if False 1 2)` and `(if True True False)` on every run.
* `Controls.pair_if_every_run` (positive): `(pair (if True 1 2) (if True True False))`; HE's
  `metta-repl` answers `[(pair 1 True)]`.
* `Controls.pair_if_not_other` (negative): that term does not go on to `[(pair 2 False)]`.
* `Controls.yes_every_run` (positive, an undeclared taken branch): `(if b yes no)` on every run.
* `Controls.undeclared_outside` (negative): an undeclared branch (`yes`) is outside
  `DeclaredBranches`; it meets `UndeclaredBranches` (`Controls.yes_branches`).
* `Controls.second_name_needed` (negative): the record's freshness matters: at a record that binds
  the return name `u` to `Bool`, the class of `u` has a value, and `declared_cast`'s premise fails.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DeclaredBranchVariant

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel AlphaVariantRel
  QueryVisibleName)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied renameTypeVars
  applyTypeValuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (specBindingVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs MatchRel MatchListAccRel MergeRel
  MergeConstraintsRel AddVarBindingRel AddVarEqualityRel Parameters equalityGroundedSemantic
  isVariableB)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes IfFinishes
  ScopedTransfer ScopedIf SyntacticMerge VariantRuns
open AnswerBags.Controls (sym app rule)

variable {dispatch : GroundedDispatch} {policy : Policy} {target : List Atom}

/-! ## Matches and merges with one result -/

theorem data_nonVar {d : Atom} (data : DataAtom d) : isVariableB d = false := by
  cases data <;> rfl

/-- Two grounded values match with no binding. -/
theorem match_grounded_out {g g' : GroundedValue} {m : Bindings}
    (matched : MatchRel equalityGroundedSemantic (.grounded g) (.grounded g') m) :
    m = Bindings.empty := by
  cases matched with
  | groundedLeftCustom _ _ custom _ =>
      exact (show Atom.grounded g' = .grounded g ∧ m = Bindings.empty from custom).2
  | groundedRightCustom _ noCustom _ _ _ =>
      exact (noCustom (by simp [Parameters.atomHasCustomMatcher, equalityGroundedSemantic])).elim
  | groundedFallback _ _ _ => rfl

/-- A non-variable atom matches a variable by assigning it. -/
theorem match_nonvar_var {d : Atom} {x : String} {m : Bindings} (nonVar : isVariableB d = false)
    (matched : MatchRel equalityGroundedSemantic d (.var x) m) :
    m = Bindings.empty.assign x d := by
  cases matched <;> first | rfl | simp_all [isVariableB]

/-- Two variables match by their equality. -/
theorem match_var_var {x y : String} {m : Bindings}
    (matched : MatchRel equalityGroundedSemantic (.var x) (.var y) m) :
    m = Bindings.empty.addEquality x y := by
  cases matched <;> first | rfl | simp_all [isVariableB]

/-- Adding a value to a class without values records it. -/
theorem add_fresh_out {b : Bindings} {x : String} {v : Atom} {out : Bindings}
    (unbound : b.classValues x = [])
    (add : AddVarBindingRel equalityGroundedSemantic b x v out) : out = b.assign x v := by
  cases add with
  | fresh _ => rfl
  | same hvalues _ _ =>
      rw [unbound] at hvalues
      exact absurd (List.Perm.length_eq hvalues) (by simp)
  | conflict hvalues _ _ _ _ =>
      rw [unbound] at hvalues
      exact absurd (List.Perm.length_eq hvalues) (by simp)
  | reconcile hvalues _ _ _ =>
      rw [unbound] at hvalues
      exact absurd (List.Perm.length_eq hvalues) (by simp)

/-- Merging one assignment into bindings where its class has no value records it. -/
theorem merge_value_out {b : Bindings} {x : String} {v : Atom} {out : Bindings}
    (unbound : b.classValues x = [])
    (merged : MergeRel equalityGroundedSemantic b (Bindings.empty.assign x v) out) :
    out = b.assign x v := by
  cases merged with
  | mk perm folded =>
      rw [DeclaredBranchGap.constraints_assign] at perm
      obtain rfl := List.perm_singleton.mp perm
      cases folded with
      | value add rest =>
          cases rest
          exact add_fresh_out unbound add

/-- Merging one equality whose class has no value records it. -/
theorem merge_pair_out {b : Bindings} {u w : String} {out : Bindings}
    (empty : (b.addEquality u w).classValues u = [])
    (merged : MergeRel equalityGroundedSemantic b (pairEq u w) out) : out = b.addEquality u w := by
  cases merged with
  | mk perm folded =>
      rw [pairEq_constraints] at perm
      obtain rfl := List.perm_singleton.mp perm
      cases folded with
      | equality add rest =>
          cases rest
          cases add with
          | consistent _ _ => rfl
          | reconcile hvalues _ _ _ =>
              rw [empty] at hvalues
              exact absurd (List.Perm.length_eq hvalues) (by simp)

/-- Every structural match of two copies of `if`'s arrow is `{u = w}`. -/
theorem arrows_inner_out {u w : String} {m : Bindings} (different : u ≠ w)
    (matched : MatchRel equalityGroundedSemantic (ifArrowV u) (ifArrowV w) m) : m = pairEq u w := by
  cases matched with
  | expression items _ =>
      cases items with
      | cons m1 g1 rest1 =>
          obtain rfl := LetSource.match_symbol_symbol m1
          obtain rfl := merge_empty_out g1
          cases rest1 with
          | cons m2 g2 rest2 =>
              obtain rfl := LetSource.match_symbol_symbol m2
              obtain rfl := merge_empty_out g2
              cases rest2 with
              | cons m3 g3 rest3 =>
                  obtain rfl := LetSource.match_symbol_symbol m3
                  obtain rfl := merge_empty_out g3
                  cases rest3 with
                  | cons m4 g4 rest4 =>
                      obtain rfl := LetSource.match_symbol_symbol m4
                      obtain rfl := merge_empty_out g4
                      cases rest4 with
                      | cons m5 g5 rest5 =>
                          obtain rfl := match_var_var m5
                          obtain rfl := merge_pair_out (pairEq_empty_classValues different) g5
                          cases rest5
                          rfl

/-- **Every type match of two fresh copies of `if`'s arrow records exactly `u = w`.** -/
theorem arrows_match_out {b out : Bindings} {u w : String} (freshU : u ∉ specBindingVars b)
    (freshW : w ∉ specBindingVars b) (different : u ≠ w)
    (matched : TypeMatchRel (ifArrowV u) (ifArrowV w) b out) : out = b.addEquality u w := by
  obtain ⟨m, inner, merged⟩ := TypeMatchRel.structural_of_nonWildcard
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) matched
  obtain rfl := arrows_inner_out different inner
  exact merge_pair_out (classValues_fresh_pair freshU freshW different) merged

theorem lookup_single {t e : String} {v : Atom} (different : e ≠ t) :
    (Bindings.empty.assign t v).lookup e = none := by
  have beqFalse : (e == t) = false := beq_eq_false_iff_ne.mpr different
  simp [Bindings.assign, Bindings.isBound, Bindings.lookup, Bindings.empty, List.lookup, beqFalse]

theorem assign_two {t e : String} {y n : Atom} (different : e ≠ t) :
    (Bindings.empty.assign t y).assign e n = ⟨[(t, y), (e, n)], []⟩ := by
  have beqFalse : (e == t) = false := beq_eq_false_iff_ne.mpr different
  simp [Bindings.assign, Bindings.isBound, Bindings.lookup, Bindings.empty, List.lookup, beqFalse]

/-- **Every match of `(if b y n)` with a row pattern `(if b' $t $e)` is `{t := y, e := n}`**, for
data branches and distinct names. -/
theorem row_match_out {b b' : Bool} {y n : Atom} {t e : String} {matched : Bindings}
    (dataY : DataAtom y) (dataN : DataAtom n) (distinct : t ≠ e)
    (matching : MatchRel equalityGroundedSemantic
      (.expression [.symbol "if", .grounded (.bool b), y, n])
      (.expression [.symbol "if", .grounded (.bool b'), .var t, .var e]) matched) :
    matched = ⟨[(t, y), (e, n)], []⟩ := by
  cases matching with
  | expression items _ =>
      cases items with
      | cons m1 g1 rest1 =>
          obtain rfl := LetSource.match_symbol_symbol m1
          obtain rfl := merge_empty_out g1
          cases rest1 with
          | cons m2 g2 rest2 =>
              obtain rfl := match_grounded_out m2
              obtain rfl := merge_empty_out g2
              cases rest2 with
              | cons m3 g3 rest3 =>
                  obtain rfl := match_nonvar_var (data_nonVar dataY) m3
                  obtain rfl := merge_value_out
                    (ScopedIf.Controls.classValues_no_equalities rfl rfl) g3
                  cases rest3 with
                  | cons m4 g4 rest4 =>
                      obtain rfl := match_nonvar_var (data_nonVar dataN) m4
                      obtain rfl := merge_value_out (ScopedIf.Controls.classValues_no_equalities rfl
                        (lookup_single distinct.symm)) g4
                      cases rest4
                      exact assign_two distinct.symm

/-! ## The works of a variant frontier -/

theorem row_hit {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {position : Nat} {row : Atom} {block : List EquationWork},
      SynRowResultsRel live query incoming position row block → ∀ w ∈ block, ∃ matched,
        AlphaVariantRel live query incoming w.left w.right w.pattern w.body ∧
          MatchRel equalityGroundedSemantic query w.pattern matched ∧
          w.bindings = merge matched incoming
  | _, _, _, .irrelevant _ _ _ => fun w member => by cases member
  | _, _, _, .miss _ _ _ _ _ _ _ => fun w member => by cases member
  | _, _, _, .hit _ _ _ _ _ matched alpha matching _ => fun w member => by
      rw [List.mem_singleton] at member
      subst member
      exact ⟨matched, alpha, matching, rfl⟩

theorem rows_hits {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {rows : List (Atom × Nat)} {blocks : List (List EquationWork)},
      List.Forall₂ (fun row block => SynRowResultsRel live query incoming row.2 row.1 block)
        rows blocks →
      ∀ w ∈ blocks.flatten, ∃ matched,
        AlphaVariantRel live query incoming w.left w.right w.pattern w.body ∧
          MatchRel equalityGroundedSemantic query w.pattern matched ∧
          w.bindings = merge matched incoming
  | [], [], .nil => fun w member => by cases member
  | _ :: _, _ :: _, .cons here rest => fun w member => by
      simp only [List.flatten_cons, List.mem_append] at member
      rcases member with inHere | inRest
      · exact row_hit here w inHere
      · exact rows_hits rest w inRest

/-- **Every work of a variant frontier is a hit of its row**: a fresh copy of the row, a match of the
query with its pattern, and the syntactic merge of that match as its record. -/
theorem frontier_hits {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (syn : SynFrontierRel space live query incoming works) :
    ∀ w ∈ works, ∃ matched,
      AlphaVariantRel live query incoming w.left w.right w.pattern w.body ∧
        MatchRel equalityGroundedSemantic query w.pattern matched ∧
        w.bindings = merge matched incoming := by
  cases syn with
  | completed covered => exact rows_hits covered

/-- **The record of `if`'s row on `(if b y n)`**: `{then' := y, else' := n}` for two distinct names
that the query's configuration does not show. -/
theorem if_record {b : Bool} {y n : Atom} (dataY : DataAtom y) (dataN : DataAtom n)
    {live : List Atom} {incoming : Bindings} {right pattern body : Atom} {matched : Bindings}
    (alpha : AlphaVariantRel live (callOf b y n) incoming
      (app "if" [.grounded (.bool b), .var "then", .var "else"]) right pattern body)
    (matching : MatchRel equalityGroundedSemantic (callOf b y n) pattern matched) :
    ∃ t e : String, t ≠ e ∧ ¬ QueryVisibleName live (callOf b y n) incoming t ∧
      ¬ QueryVisibleName live (callOf b y n) incoming e ∧ matched = ⟨[(t, y), (e, n)], []⟩ := by
  obtain ⟨rename, injective, renamedLeft, _, hidden⟩ := alpha
  have shape : pattern = .expression [.symbol "if", .grounded (.bool b), .var (rename "then"),
      .var (rename "else")] := by
    rw [Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft]
    simp [renameTypeVars]
  subst shape
  have distinct : rename "then" ≠ rename "else" := fun same => absurd (injective same) (by decide)
  refine ⟨rename "then", rename "else", distinct, ?_, ?_, row_match_out dataY dataN distinct matching⟩
  · exact hidden "then" (Or.inl (.expression (atom := .var "then") (by simp) (.var "then")))
  · exact hidden "else" (Or.inl (.expression (atom := .var "else") (by simp) (.var "else")))

/-- A name the query's configuration does not show is neither the live return name nor the name
equated with it. -/
theorem hidden_names {live : List Atom} {query : Atom} {incoming rest : Bindings} {u w x : String}
    (recorded : incoming = rest.addEquality u w)
    (hidden : ¬ QueryVisibleName (.var u :: live) query incoming x) : u ≠ x ∧ w ≠ x := by
  constructor
  · intro same
    subst same
    exact hidden (Or.inr (Or.inl ⟨.var u, List.mem_cons_self, .var u⟩))
  · intro same
    subst same
    refine hidden (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, w, ?_, Or.inr rfl⟩))))
    rw [recorded]
    simp [Bindings.addEquality]

/-! ## The declared branch meets the fresh return type at the syntactic record -/

/-- Names outside the support of the syntactic record. -/
theorem merged_support {before : Bindings} {t e x : String} {y n : Atom}
    (groundY : TypeSubst.typeVars y = []) (groundN : TypeSubst.typeVars n = [])
    (notT : x ≠ t) (notE : x ≠ e) (outside : x ∉ specBindingVars before) :
    x ∉ specBindingVars ⟨[(t, y), (e, n)] ++ before.assignments, before.equalities⟩ := by
  intro member
  simp only [specBindingVars, List.cons_append, List.nil_append, List.flatMap_cons, groundY, groundN,
    List.mem_append, List.mem_cons] at member outside
  tauto

theorem assign_unbound {b : Bindings} {x : String} {val : Atom} (unbound : b.lookup x = none) :
    b.assign x val = ⟨b.assignments ++ [(x, val)], b.equalities⟩ := by
  simp [Bindings.assign, Bindings.isBound, unbound]

/-- A model of `rest + {u = w}`, sent to `s` at both fresh names, models the assignment of `s`. -/
theorem assigned_model {v0 : String → Atom} {rest : Bindings} {u w s : String}
    (freshU : u ∉ specBindingVars rest) (freshW : w ∉ specBindingVars rest)
    (sat : TypeBindingSatisfied v0 (rest.addEquality u w)) :
    TypeBindingSatisfied (fun x => if x = u ∨ x = w then Atom.symbol s else v0 x)
      ((rest.addEquality u w).assign u (.symbol s)) := by
  have unbound : (rest.addEquality u w).lookup u = none := by
    change rest.lookup u = none
    exact lookup_none_of_outside freshU
  rw [assign_unbound unbound]
  have agree : Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ValuationsAgreeOn
      (specBindingVars rest) v0 (fun x => if x = u ∨ x = w then Atom.symbol s else v0 x) := by
    intro name member
    have notU : name ≠ u := fun same => freshU (same ▸ member)
    have notW : name ≠ w := fun same => freshW (same ▸ member)
    simp [notU, notW]
  have satRest : TypeBindingSatisfied v0 rest :=
    ⟨fun name value member => sat.1 name value member,
      fun left right member => sat.2 left right (List.mem_append_left _ member)⟩
  have satNew :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.specTypeBindingSatisfied_congr_of_bindingVars
      agree).mp satRest
  refine ⟨fun name value member => ?_, fun left right member => ?_⟩
  · simp only [Bindings.addEquality, List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
    rcases member with inRest | ⟨rfl, rfl⟩
    · exact satNew.1 name value inRest
    · simp [applyTypeValuation]
  · simp only [Bindings.addEquality, List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
    rcases member with inRest | ⟨rfl, rfl⟩
    · exact satNew.2 left right inRest
    · simp

/-- **A fresh return name meets a symbolic type** at a frame `rest + {u = w}` with both names
outside `rest`: the match exists under either policy, and its result has a model. -/
theorem declared_accepts (policy : Policy) {G : Frame} {rest : Bindings} {u w s : String}
    (record : G.bindings = rest.addEquality u w) (freshU : u ∉ specBindingVars rest)
    (freshW : w ∉ specBindingVars rest) (different : u ≠ w) (notUndefined : s ≠ "%Undefined%")
    (notAtom : s ≠ "Atom") :
    ∃ output, policy.matching.Rel (.var u) (.symbol s) G.bindings output ∧
      ∃ v : String → Atom, TypeBindingSatisfied v output := by
  obtain ⟨v0, sat0⟩ := G.certified.satisfiable
  rw [record] at sat0
  have empty : G.bindings.classValues u = [] := by
    rw [record]
    exact classValues_fresh_pair freshU freshW different
  have matched := TypeMatchRel.expected_variable_symbol u s G.bindings notUndefined notAtom empty
  have model : ∃ v : String → Atom, TypeBindingSatisfied v (G.bindings.assign u (.symbol s)) := by
    rw [record]
    exact ⟨_, assigned_model freshU freshW sat0⟩
  refine ⟨_, ?_, model⟩
  cases policy.matching with
  | raw => exact matched
  | finite => exact ⟨matched, model⟩

/-- **At the syntactic record of `if`'s hit, the fresh return name meets a symbolic type.** -/
theorem declared_cast (policy : Policy) {s : String} (notUndefined : s ≠ "%Undefined%")
    (notAtom : s ≠ "Atom") {G : Frame} {before : Bindings} {t e u w : String} {y n : Atom}
    (record : G.bindings = merge ⟨[(t, y), (e, n)], []⟩ (before.addEquality u w))
    (groundY : TypeSubst.typeVars y = []) (groundN : TypeSubst.typeVars n = [])
    (uT : u ≠ t) (uE : u ≠ e) (wT : w ≠ t) (wE : w ≠ e)
    (freshU : u ∉ specBindingVars before) (freshW : w ∉ specBindingVars before)
    (different : u ≠ w) :
    ∃ output, policy.matching.Rel (.var u) (.symbol s) G.bindings output ∧
      ∃ v : String → Atom, TypeBindingSatisfied v output :=
  declared_accepts policy (rest := ⟨[(t, y), (e, n)] ++ before.assignments, before.equalities⟩)
    record (merged_support groundY groundN uT uE freshU) (merged_support groundY groundN wT wE freshW)
    different notUndefined notAtom

/-- The first step of the declared branch's cast. -/
theorem declared_first (policy : Policy) {space : Space} {P : List String} {d : Atom} {s u : String}
    (stored : StorageTypesRel space d [.symbol s]) {G : Frame}
    (accepted : ∃ output, policy.matching.Rel (.var u) (.symbol s) G.bindings output ∧
      ∃ v : String → Atom, TypeBindingSatisfied v output) :
    ∃ (T : Atom) (after : Frame), Completed.scopedLookup P space G.bindings d (.var u) [T] ∧
      Completed.Frame.TypeRenewRel policy (.var u) T G after := by
  obtain ⟨output, matched, model⟩ := accepted
  obtain ⟨after, _, renewal⟩ := Completed.Frame.TypeRenewRel.of_modelled_match G matched model
  exact ⟨.symbol s, after, scoped_closed_answers stored rfl, renewal⟩

/-! ## `(if b y n)` with a declared taken branch -/

/-- **The branches of `(if b y n)` with a declared taken branch**: both branches are data atoms with
one closed stored type each; the taken branch's stored type is a symbol other than the two wildcard
types; and the call's region is HE's row for `b`. -/
structure DeclaredBranches (atoms : List Atom) (b : Bool) (y n : Atom) (s : String) : Prop where
  dataYes : DataAtom y
  dataNo : DataAtom n
  takenNotRefused : pick b y n ≠ Atom.notReducible
  takenType : StorageTypesRel (Space.ofList atoms) (pick b y n) [.symbol s]
  notUndefined : s ≠ "%Undefined%"
  notAtom : s ≠ "Atom"
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T] ∧ TypeSubst.typeVars T = []
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T] ∧ TypeSubst.typeVars T = []
  region : regionInstances atoms "if" [.grounded (.bool b), y, n] = [pick b y n]
  sides : regionSides atoms "if" [.grounded (.bool b), y, n] =
    [(app "if" [.grounded (.bool b), .var "then", .var "else"], pick b (.var "then") (.var "else"))]

theorem DeclaredBranches.takenData {atoms : List Atom} {b : Bool} {y n : Atom} {s : String}
    (branches : DeclaredBranches atoms b y n s) : DataAtom (pick b y n) := by
  cases b
  · exact branches.dataNo
  · exact branches.dataYes

/-- **The branches of `(if b y n)` with an undeclared taken branch**: as `DeclaredBranches`, with
the taken branch's stored type `%Undefined%`. -/
structure UndeclaredBranches (atoms : List Atom) (b : Bool) (y n : Atom) : Prop where
  dataYes : DataAtom y
  dataNo : DataAtom n
  takenNotRefused : pick b y n ≠ Atom.notReducible
  takenUndeclared : StorageTypesRel (Space.ofList atoms) (pick b y n) [Atom.undefinedType]
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T] ∧ TypeSubst.typeVars T = []
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T] ∧ TypeSubst.typeVars T = []
  region : regionInstances atoms "if" [.grounded (.bool b), y, n] = [pick b y n]
  sides : regionSides atoms "if" [.grounded (.bool b), y, n] =
    [(app "if" [.grounded (.bool b), .var "then", .var "else"], pick b (.var "then") (.var "else"))]

/-- **What the run of `(if b y n)` needs of its program and call**, for either kind of taken
branch: both branches are data atoms with one closed stored type each; the call's region is HE's
row for `b`; and, at every frame that records one more equality `u = w` of two names outside the
rest of its record, the taken branch's cast against `$u` has a first step and every answer of its
lookup holds a type that `$u` accepts. -/
structure IfWalk (policy : Policy) (atoms : List Atom) (b : Bool) (y n : Atom) : Prop where
  dataYes : DataAtom y
  dataNo : DataAtom n
  takenNotRefused : pick b y n ≠ Atom.notReducible
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T] ∧ TypeSubst.typeVars T = []
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T] ∧ TypeSubst.typeVars T = []
  region : regionInstances atoms "if" [.grounded (.bool b), y, n] = [pick b y n]
  sides : regionSides atoms "if" [.grounded (.bool b), y, n] =
    [(app "if" [.grounded (.bool b), .var "then", .var "else"], pick b (.var "then") (.var "else"))]
  cast : ∀ (P : List String) (G : Frame) (rest : Bindings) (u w : String),
    G.bindings = rest.addEquality u w → u ∉ specBindingVars rest → w ∉ specBindingVars rest →
    u ≠ w →
    (∃ (T : Atom) (after : Frame),
        Completed.scopedLookup P (Space.ofList atoms) G.bindings (pick b y n) (.var u) [T] ∧
          Completed.Frame.TypeRenewRel policy (.var u) T G after) ∧
      ∀ types, Completed.scopedLookup P (Space.ofList atoms) G.bindings (pick b y n) (.var u)
          types →
        ∃ actual ∈ types, ∃ output, policy.matching.Rel (.var u) actual G.bindings output

theorem IfWalk.takenData {atoms : List Atom} {b : Bool} {y n : Atom}
    (walk : IfWalk policy atoms b y n) : DataAtom (pick b y n) := by
  cases b
  · exact walk.dataNo
  · exact walk.dataYes

/-- A declared taken branch meets the fresh return name at the syntactic record. -/
theorem DeclaredBranches.walk {atoms : List Atom} {b : Bool} {y n : Atom} {s : String}
    (branches : DeclaredBranches atoms b y n s) (policy : Policy) : IfWalk policy atoms b y n where
  dataYes := branches.dataYes
  dataNo := branches.dataNo
  takenNotRefused := branches.takenNotRefused
  typedYes := branches.typedYes
  typedNo := branches.typedNo
  region := branches.region
  sides := branches.sides
  cast := fun P G rest u w record freshU freshW different => by
    obtain ⟨output, matched, model⟩ := declared_accepts policy record freshU freshW different
      branches.notUndefined branches.notAtom
    exact ⟨declared_first policy branches.takenType ⟨output, matched, model⟩,
      closed_accepts branches.takenType rfl ⟨output, matched⟩⟩

/-- An undeclared taken branch meets every return name at every frame. -/
theorem UndeclaredBranches.walk {atoms : List Atom} {b : Bool} {y n : Atom}
    (branches : UndeclaredBranches atoms b y n) (policy : Policy) : IfWalk policy atoms b y n where
  dataYes := branches.dataYes
  dataNo := branches.dataNo
  takenNotRefused := branches.takenNotRefused
  typedYes := branches.typedYes
  typedNo := branches.typedNo
  region := branches.region
  sides := branches.sides
  cast := fun _ G _ u _ _ _ _ _ =>
    ⟨keeping_cast_step branches.takenUndeclared rfl (.undefinedRight _ _),
      closed_accepts branches.takenUndeclared rfl (variable_meets_undefined u G)⟩

/-- **Every run of the function application of `(if b y n)` against a fresh copy `$u` goes on with
the call value, at a frame that records exactly one more equality `u = w`**, for a second fresh
name `w`: the operator meets its own fresh copy, the condition's cast to `Bool` and the two
deliveries keep the frame. -/
theorem goodv_function_declared {atoms : List Atom} (program : IfProgram atoms) {b : Bool}
    {y n : Atom} (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    {live : List Atom} {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    {u : String} (functionType : signature.functionType = ifArrowV u) {activation : Frame}
    (freshU : u ∉ specBindingVars activation.bindings)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ (R : List Result) (w : String), R.map (fun r => r.1.erase) = [callOf b y n] →
      (∀ r ∈ R, r.2.bindings = activation.bindings.addEquality u w) →
      w ∉ specBindingVars activation.bindings → u ≠ w →
      GoodV dispatch Completed.scopedLookup policy target
        ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
      .work (.function live scope expected signature (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom y, Entry.Value.ofAtom n]
        activation), stack, emitted⟩ := by
  have projections := if_projections_v functionType
  refine goodv_functionStart (by simp [projections.1]) ?_
  rw [projections.1, functionType]
  simp only [List.zip_cons_cons, List.zip_nil_right]
  refine goodv_cast if_data (symbol_cast_entry (by decide) (by decide) (arrowV_not_raw u))
    (operator_step program freshU) (operator_cast_accepts program freshU) ?_
  intro frF info
  obtain ⟨types, actual, queried, member, matched⟩ := info
  obtain ⟨w, rfl, freshW⟩ := scoped_if_answers program queried
  rw [List.mem_singleton] at member
  subst member
  have inner := outside_scope freshW
  have different : u ≠ w := by
    intro same
    apply inner.2.1
    rw [← same]
    simp [TypeSubst.typeVarsList, TypeSubst.typeVars, Atom.atomType]
  have recorded : frF.bindings = activation.bindings.addEquality u w :=
    arrows_match_out freshU inner.2.2 different matched.source
  apply goodv_functionHeads_frame
  refine goodv_functionBranches_continue ?_ ?_
  · simpa using if_data.not_stopped
  apply goodv_argumentsCons
  refine goodv_cast (DataAtom.grounded (.bool b)) (bool_cast_entry b)
    (keeping_cast_step (bool_types_in _ b) rfl (bool_matches _))
    (closed_accepts (bool_types_in _ b) rfl (bool_accepts _)) ?_
  intro fr1 info1
  obtain ⟨types1, actual1, queried1, member1, matched1⟩ := info1
  obtain rfl := scoped_closed_answer (bool_types_in _ b) rfl queried1
  rw [List.mem_singleton] at member1
  subst member1
  have kept : fr1.bindings = frF.bindings := bool_match_output matched1.source
  apply goodv_arguments_frame
  refine goodv_argumentBranches_continue ?_ ?_
  · rintro ⟨stopped, _⟩
    exact (DataAtom.grounded (.bool b)).not_stopped (by simpa using stopped)
  apply goodv_argumentsCons
  refine goodv_deliver_closed closedY ?_
  apply goodv_arguments_frame
  refine goodv_argumentBranches_continue ?_ ?_
  · rintro ⟨_, changed⟩
    exact changed rfl
  apply goodv_argumentsCons
  refine goodv_deliver_closed closedN ?_
  apply goodv_arguments_frame
  refine goodv_argumentBranches_continue ?_ ?_
  · rintro ⟨_, changed⟩
    exact changed rfl
  apply goodv_argumentsNil
  apply goodv_argumentTail
  apply goodv_append
  apply goodv_argumentBranches_nil
  apply goodv_prepend
  apply goodv_argumentTail
  apply goodv_append
  apply goodv_argumentBranches_nil
  apply goodv_prepend
  apply goodv_argumentTail
  apply goodv_append
  apply goodv_argumentBranches_nil
  apply goodv_prepend
  apply goodv_functionAssemble
  apply goodv_append
  apply goodv_functionBranches_nil
  apply goodv_prepend
  refine cont _ w ?_ ?_ inner.2.2 different
  · simp [Completed.functionAssemble, Completed.argumentPrepend, Entry.Value.erase,
      Entry.Value.erase_ofAtom, callOf, app]
  · intro r member
    simp [Completed.functionAssemble, Completed.argumentPrepend] at member
    subst member
    exact kept.trans recorded

/-- **Every run of the typed query of `(if b y n)` under its fresh return demand `$u`, at a frame
`before + {u = w}`, goes on with the taken branch, on the variant machine**: the frontier's one work
carries the syntactic record, the body is read as the taken branch, and the taken branch meets `$u`
there. -/
theorem goodv_query_walk (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : IfWalk policy atoms b y n) {live : List Atom} {scope : List String}
    {u w : String} {value : Entry.Value} (erased : value.erase = callOf b y n) {activation : Frame}
    {before : Bindings} (recorded : activation.bindings = before.addEquality u w)
    (freshU : u ∉ specBindingVars before) (freshW : w ∉ specBindingVars before) (different : u ≠ w)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      GoodV dispatch Completed.scopedLookup policy target
        ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
      .work (.call live scope value (.var u) activation), stack, emitted⟩ := by
  have takenData := branches.takenData
  have closedY := data_closed branches.dataYes
  have closedN := data_closed branches.dataNo
  have groundY := HERuns.ground_typeVars (answerable_of_data branches.dataYes)
  have groundN := HERuns.ground_typeVars (answerable_of_data branches.dataNo)
  have ground := call_ground (b := b) closedY closedN
  have notError : ¬ IsErrorRel value.erase := by
    rw [erased]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch value.erase := by
    rw [erased]
    refine And.intro ?_ (by simp [Minimal.embeddedInstruction])
    rintro ⟨operator, arguments, same, executable⟩
    simp only [callOf, app, Atom.expression.injEq, List.cons.injEq] at same
    rw [← same.1] at executable
    exact notHost executable
  have notPending : ¬ Completed.FunctionPending policy (Entry.Value.ofAtom (pick b y n)) := by
    rintro ⟨⟨inner, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    have data := takenData
    rw [same] at data
    cases data
  have fromFrontier : ∀ works : List EquationWork,
      SynFrontierRel (Space.ofList atoms) (.var u :: live) (callOf b y n) activation.bindings
        works →
      GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
        .work (.equations live scope value (.var u) activation works), stack, emitted⟩ := by
    intro works syn
    have frontier := syn.sound
    have instances := works_instances_ground policy ground program.rows
      activation.certified.satisfiable frontier
    rw [branches.region] at instances
    obtain ⟨wk, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
    obtain rfl := List.forall₂_nil_right_iff.mp rest
    have sidesEq := frontier_sides ground activation.certified.satisfiable
      (scoped_consFree program.rows) frontier
    rw [branches.sides] at sidesEq
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at sidesEq
    obtain ⟨matched, alpha, matching, record⟩ := frontier_hits syn wk List.mem_cons_self
    rw [sidesEq.1, sidesEq.2] at alpha
    obtain ⟨t, e, _, hiddenT, hiddenE, rfl⟩ :=
      if_record branches.dataYes branches.dataNo alpha matching
    obtain ⟨uT, wT⟩ := hidden_names recorded hiddenT
    obtain ⟨uE, wE⟩ := hidden_names recorded hiddenE
    have frontier' : EquationFrontierRel (Space.ofList atoms) (.var u :: live) value.erase
        activation.bindings [wk] := by
      rw [erased]
      exact frontier
    obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
      (policy := policy.rebuilding) activation.certified frontier'
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired wk List.mem_cons_self
    refine .step ⟨_, .internal (.equationsCons (output := ⟨wk.bindings, after, certificate⟩) rfl
      unified), True.intro⟩ ?_
    intro z step
    obtain ⟨model, -⟩ := step
    cases model with
    | internal l =>
        cases l with
        | equationsCons sameBindings _ =>
            have readValue := value_of_data takenData (reads _ sameBindings)
            have recordG := sameBindings.trans record
            rw [recorded] at recordG
            have kit := fun P : List String => branches.cast P _
              ⟨[(t, y), (e, n)] ++ before.assignments, before.equalities⟩ u w recordG
              (merged_support groundY groundN uT uE freshU)
              (merged_support groundY groundN wT wE freshW) different
            rw [readValue]
            refine goodv_boundary_producer notPending ?_
            apply goodv_boundaryBatch_frame
            apply goodv_boundaryBatch_cons
            apply goodv_boundary_returned
            refine goodv_returned_evaluate ?_ ?_ ?_
            · simpa [Entry.Value.erase_ofAtom] using branches.takenNotRefused
            · simpa [Entry.Value.erase_ofAtom] using takenData.not_stopped
            refine goodv_data_cast takenData (data_var_entry takenData u) (kit _).1 (kit _).2 ?_
            intro final
            apply goodv_append
            apply goodv_boundaryBatch_nil
            apply goodv_prepend
            apply goodv_append
            apply goodv_equations_nil
            apply goodv_prepend
            apply cont
            simp
  obtain ⟨works0, frontier0⟩ := frontier_total (Space.ofList atoms) (.var u :: live)
    (callOf b y n) activation.bindings
  have instances0 := works_instances_ground policy ground program.rows
    activation.certified.satisfiable frontier0
  have nonempty0 : works0 ≠ [] := by
    intro isEmpty
    subst isEmpty
    rw [branches.region] at instances0
    cases instances0
  obtain ⟨works1, syn1, same1⟩ := frontier_represented frontier0
  have syn1' : SynFrontierRel (Space.ofList atoms) (.var u :: live) value.erase
      activation.bindings works1 := by
    rw [erased]
    exact syn1
  refine .step ⟨_, vstep_call_iff.mpr ⟨notError, nonGrounded, syn1',
    same_length same1 nonempty0⟩⟩ ?_
  intro z step
  obtain ⟨model, syntactic⟩ := step
  cases model with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed notError
      | callEmbedded _ _ instruction =>
          rw [erased] at instruction
          simp [Minimal.embeddedInstruction] at instruction
      | callAbsent _ _ frontierEmpty =>
          rw [erased] at frontierEmpty
          have noWork := works_instances_ground policy ground program.rows
            activation.certified.satisfiable frontierEmpty
          rw [branches.region] at noWork
          cases noWork
      | callEquations _ _ frontierW _ =>
          have syn : SynFrontierRel (Space.ofList atoms) (.var u :: live) value.erase
              activation.bindings _ := syn_iff.mpr ⟨frontierW, syntactic⟩
          rw [erased] at syn
          exact fromFrontier _ syn

/-- **Every run of `(if b y n)`, under `%Undefined%`, at every frame and under every continuation,
goes on with the taken branch, on the variant machine and the scoped lookup**, for either kind of
taken branch. -/
theorem goodv_if_walk (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : IfWalk policy atoms b y n) :
    GoodRuns dispatch Completed.scopedLookup policy target atoms
      (Entry.Value.ofAtom (callOf b y n)) [pick b y n] := by
  intro live scope frame stack emitted cont
  obtain ⟨Ty, typesY, closedTy⟩ := branches.typedYes
  obtain ⟨Tn, typesN, closedTn⟩ := branches.typedNo
  have takenData := branches.takenData
  have closedY := data_closed branches.dataYes
  have closedN := data_closed branches.dataNo
  have readC : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      Entry.Value.ofAtom (callOf b y n) :=
    HERuns.read_closed policy frame (IfAtFrames.call_closed closedY closedN)
  have entry : Entry.Rel policy.reentry
      (frame.read policy (Entry.Value.ofAtom (callOf b y n))).status
      (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase Atom.undefinedType
      .interpret := by
    have atEmpty := call_entry policy if_data [.grounded (.bool b), y, n]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shape : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.bool b), y, n].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [callOf, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  obtain ⟨variant, rename, injective, renamed, fresh⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.TypeCandidateAlphaVariantRel.exists
      (invocationTypeScope (invocationTypeScope scope live (callOf b y n) Atom.undefinedType
        frame.bindings) [] (.symbol "if") Atom.undefinedType frame.bindings) ifArrow
  have freshU := fresh "t" (by rw [ifArrow_vars]; exact List.mem_singleton_self _)
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.scopedLookup policy live scope
      (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame
      (.selected (ifPolicyV (rename "t")) [frame]) := by
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact if_selection_succeeds_scoped policy program b typesY closedTy typesN closedTn live scope
      frame freshU
  have clean : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      ∀ r ∈ R, Answerable r.1.erase := by
    intro R eraseR r member
    have inR : r.1.erase ∈ [pick b y n] := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inR
    rw [inR]
    exact answerable_of_data takenData
  refine .step ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry shape
    selection), True.intro⟩ ?_
  intro z moved
  obtain ⟨model, -⟩ := moved
  cases model with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped occurs =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Entry.Value.erase_ofAtom] at occurs
          have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
            program.types.occurrences
          simp [Atom.undefinedType] at same
      | atomFallback _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, _, _, impossible⟩ :=
            if_selection_scoped program b typesY closedTy typesN closedTn chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, _, _, impossible⟩ :=
            if_selection_scoped program b typesY closedTy typesN closedTn chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨u, signature, after, freshFrame, functionType, afterBindings, selected⟩ :=
            if_selection_scoped program b typesY closedTy typesN closedTn chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have freshAfter : u ∉ specBindingVars after.bindings := by
            rw [afterBindings]
            exact freshFrame
          apply goodv_invocations_cons
          rw [returnType_v functionType]
          simp only [List.map_cons, List.map_nil]
          refine goodv_function_declared program closedY closedN functionType freshAfter _ _ ?_
          intro R w eraseR framesR freshW different
          obtain ⟨r, rfl, rErase⟩ : ∃ r, R = [r] ∧ r.1.erase = callOf b y n := by
            obtain ⟨r, sameR, rErase⟩ := List.map_eq_singleton_iff.mp eraseR
            exact ⟨r, sameR, rErase⟩
          have rBindings := framesR r List.mem_cons_self
          apply goodv_calls_frame
          apply goodv_calls_cons
          refine goodv_query_walk notHost program branches rErase rBindings freshAfter freshW
            different _ _ ?_
          intro Q eraseQ
          apply goodv_append
          apply goodv_calls_nil
          apply goodv_prepend
          apply goodv_append
          apply goodv_invocations_nil
          apply goodv_prepend
          refine goodv_publish (clean _ (by simpa using eraseQ)) ?_
          apply cont
          rw [publish_erase]
          simpa using eraseQ

/-- **Every run of `(if b y n)` with a declared taken branch, under `%Undefined%`, at every frame
and under every continuation, goes on with the taken branch, on the variant machine and the scoped
lookup.** -/
theorem goodv_if_declared (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {b : Bool} {y n : Atom} {s : String}
    (branches : DeclaredBranches atoms b y n s) :
    GoodRuns dispatch Completed.scopedLookup policy target atoms
      (Entry.Value.ofAtom (callOf b y n)) [pick b y n] :=
  goodv_if_walk notHost program (branches.walk policy)

/-- **The same for an undeclared taken branch**: the variant machine has the model's answers there
(`ScopedIf.fine_if_scoped`, `IfInBodies`). -/
theorem goodv_if_undeclared (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : UndeclaredBranches atoms b y n) :
    GoodRuns dispatch Completed.scopedLookup policy target atoms
      (Entry.Value.ofAtom (callOf b y n)) [pick b y n] :=
  goodv_if_walk notHost program (branches.walk policy)

/-- **From the entry, every run of the variant machine on `(if b y n)` with a declared taken branch
finishes and publishes the taken branch, and a complete run exists.** -/
theorem declared_if_every_run (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom} {s : String}
    (branches : DeclaredBranches atoms b y n s) :
    EveryRunV dispatch Completed.scopedLookup policy (Space.ofList atoms) (callOf b y n)
      [pick b y n] :=
  (goodv_entry (goodv_if_declared notHost program branches)).every_run

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)

/-- `1`, `2`, `True`, `False`. -/
abbrev one : Atom := .grounded (.int 1)
abbrev two : Atom := .grounded (.int 2)
abbrev tru : Atom := .grounded (.bool true)
abbrev fls : Atom := .grounded (.bool false)

/-- HE's `if` program carries HE's `if`. -/
theorem if_program_full : IfProgram ifProgram := ⟨if_types, if_program⟩

theorem number_types (k : Int) :
    StorageTypesRel (Space.ofList ifProgram) (.grounded (.int k)) [sym "Number"] :=
  .groundedKnown (.int k) (by simp [Atom.undefinedType])

/-- The branches of `(if b 1 2)`: both are `Number`. -/
theorem number_branches (b : Bool) : DeclaredBranches ifProgram b one two "Number" where
  dataYes := .grounded _
  dataNo := .grounded _
  takenNotRefused := by cases b <;> simp [pick, Atom.notReducible]
  takenType := by cases b <;> exact number_types _
  notUndefined := by decide
  notAtom := by decide
  typedYes := ⟨_, number_types 1, rfl⟩
  typedNo := ⟨_, number_types 2, rfl⟩
  region := by cases b <;> decide +kernel
  sides := by cases b <;> decide +kernel

/-- The branches of `(if True True False)`: both are `Bool`. -/
theorem bool_branches : DeclaredBranches ifProgram true tru fls "Bool" where
  dataYes := .grounded _
  dataNo := .grounded _
  takenNotRefused := by simp [pick, Atom.notReducible]
  takenType := bool_types_in _ true
  notUndefined := by decide
  notAtom := by decide
  typedYes := ⟨_, bool_types_in _ true, rfl⟩
  typedNo := ⟨_, bool_types_in _ false, rfl⟩
  region := by decide +kernel
  sides := by decide +kernel

/-- **Positive control**: every run of `(if True 1 2)` on the variant machine finishes with `[1]`.
On the model a run may publish a cast error (`DeclaredBranchGap.cycle_cast_error`). -/
theorem one_every_run (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList ifProgram) (callOf true one two)
      [one] :=
  declared_if_every_run (fun impossible => impossible) policy if_program_full (number_branches true)

/-- **Positive control**: the other row: every run of `(if False 1 2)` finishes with `[2]`. -/
theorem false_every_run (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList ifProgram) (callOf false one two)
      [two] :=
  declared_if_every_run (fun impossible => impossible) policy if_program_full
    (number_branches false)

/-- **Positive control**: every run of `(if True True False)` finishes with `[True]`. -/
theorem bool_every_run (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList ifProgram) (callOf true tru fls)
      [tru] :=
  declared_if_every_run (fun impossible => impossible) policy if_program_full bool_branches

/-- The branches of `(if b yes no)`: the taken branch has no declared type. -/
theorem yes_branches (b : Bool) : UndeclaredBranches ifProgram b (sym "yes") (sym "no") where
  dataYes := .symbol (by decide) (by decide)
  dataNo := .symbol (by decide) (by decide)
  takenNotRefused := by cases b <;> simp [pick, Atom.notReducible]
  takenUndeclared := by cases b <;> exact IfInBodies.Controls.undeclared_of (by decide)
  typedYes := ⟨_, IfInBodies.Controls.undeclared_of (by decide), rfl⟩
  typedNo := ⟨_, IfInBodies.Controls.undeclared_of (by decide), rfl⟩
  region := by cases b <;> decide +kernel
  sides := by cases b <;> decide +kernel

/-- **Positive control, an undeclared taken branch**: every run of `(if b yes no)` on the variant
machine finishes with the taken branch, as on the model. -/
theorem yes_every_run (policy : Policy) (b : Bool) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList ifProgram)
      (callOf b (sym "yes") (sym "no")) [pick b (sym "yes") (sym "no")] :=
  (goodv_entry (goodv_if_undeclared (fun impossible => impossible) if_program_full
    (yes_branches b))).every_run

/-- `(pair (if True 1 2) (if True True False))`. -/
abbrev pairIfCall : Atom := app "pair" [callOf true one two, callOf true tru fls]

/-- `(pair 1 True)`. -/
abbrev pairIfAnswer : Atom := app "pair" [one, tru]

theorem pair_if_value : Entry.Value.ofAtom pairIfCall =
    .expression .active (.symbol "pair" :: [Entry.Value.ofAtom (callOf true one two),
      Entry.Value.ofAtom (callOf true tru fls)]) := by
  simp [Entry.Value.ofAtom]

theorem pair_if_closed : ∀ name,
    ¬ AtomOccurs (.expression (.symbol "pair" :: [callOf true one two, callOf true tru fls])) name := by
  intro name occurs
  cases occurs with
  | expression member inner =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · cases inner
      · exact IfAtFrames.call_closed (data_closed (.grounded _)) (data_closed (.grounded _)) name
          inner
      · exact IfAtFrames.call_closed (data_closed (.grounded _)) (data_closed (.grounded _)) name
          inner

/-- Every run of `(pair (if True 1 2) (if True True False))` on the variant machine goes on to
`[(pair 1 True)]`. -/
theorem pair_if_good (policy : Policy) (goal : List Atom) :
    GoodRuns noHost Completed.scopedLookup policy goal ifProgram (Entry.Value.ofAtom pairIfCall)
      [pairIfAnswer] := by
  rw [pair_if_value]
  have built := goodv_constructor (dispatch := noHost) (policy := policy) (target := goal)
    scoped_answers scoped_contract (scoped_consFree if_program) VariantRuns.Controls.pair_head
    (by decide +kernel) (ts := [callOf true one two, callOf true tru fls]) (Ls := [[one], [tru]])
    pair_if_closed
    (vs := [Entry.Value.ofAtom (callOf true one two), Entry.Value.ofAtom (callOf true tru fls)])
    (by simp [Entry.Value.erase_ofAtom])
    (.cons ⟨goodv_if_declared (fun impossible => impossible) if_program_full (number_branches true),
        fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data (.grounded _)⟩
      (.cons ⟨goodv_if_declared (fun impossible => impossible) if_program_full bool_branches,
        fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data (.grounded _)⟩ .nil))
  simpa [combos] using built

/-- **`(pair (if True 1 2) (if True True False))` on the variant machine**: a complete run exists,
every complete run publishes `[(pair 1 True)]`, no run is infinite, and every configuration reached
from the entry can step or is final with `[(pair 1 True)]`, under either matching policy and either
reentry policy. HE's interpreter answers `[(pair 1 True)]`. -/
theorem pair_if_every_run (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList ifProgram) pairIfCall [pairIfAnswer] :=
  (goodv_entry (pair_if_good policy [pairIfAnswer])).every_run

/-- **Negative control**: that term does not go on to `[(pair 2 False)]`. -/
theorem pair_if_not_other (policy : Policy) :
    ¬ GoodV noHost Completed.scopedLookup policy [app "pair" [two, fls]]
      (load (Space.ofList ifProgram) pairIfCall Atom.undefinedType) := by
  intro wrong
  obtain ⟨⟨answers, run⟩, _⟩ := pair_if_every_run policy
  have published := wrong.every_run.2.1 answers run
  have actual := (pair_if_every_run policy).2.1 answers run
  rw [actual] at published
  simp at published

/-- **Negative control**: an undeclared branch is outside `DeclaredBranches`: the stored type of
`yes` is `%Undefined%`. It meets `UndeclaredBranches` (`yes_branches`). -/
theorem undeclared_outside (s : String) :
    ¬ DeclaredBranches ifProgram true (sym "yes") (sym "no") s := by
  intro branches
  have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.unique branches.takenType
    yes_types'
  simp only [List.cons.injEq, and_true] at same
  apply branches.notUndefined
  simpa [Atom.undefinedType] using same

/-- **Negative control**: the freshness of the return name matters: at a record that already gives
the return name `u` the value `Bool`, the class of `u` has a value. -/
theorem second_name_needed :
    (Bindings.empty.assign "u" (sym "Bool")).classValues "u" ≠ [] := by
  decide

end Controls

#print axioms arrows_match_out
#print axioms row_match_out
#print axioms frontier_hits
#print axioms if_record
#print axioms declared_accepts
#print axioms declared_cast
#print axioms goodv_function_declared
#print axioms goodv_query_walk
#print axioms goodv_if_walk
#print axioms goodv_if_declared
#print axioms goodv_if_undeclared
#print axioms declared_if_every_run
#print axioms Controls.number_branches
#print axioms Controls.bool_branches
#print axioms Controls.yes_branches
#print axioms Controls.yes_every_run
#print axioms Controls.one_every_run
#print axioms Controls.false_every_run
#print axioms Controls.bool_every_run
#print axioms Controls.pair_if_good
#print axioms Controls.pair_if_every_run
#print axioms Controls.pair_if_not_other
#print axioms Controls.undeclared_outside
#print axioms Controls.second_name_needed

end DeclaredBranchVariant

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
