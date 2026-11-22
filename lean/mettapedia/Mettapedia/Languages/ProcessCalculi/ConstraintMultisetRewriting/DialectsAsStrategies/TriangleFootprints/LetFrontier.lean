import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.UncoveredFinishes
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness

/-!
# HE's frontier for queries with variable arguments, reads between variables, and `unify`

HE's `let` is the equation `(= (let $pattern $atom $template) (unify $atom $pattern $template Empty))`
with `(: let (-> Atom %Undefined% Atom %Undefined%))`, and `unify` is a minimal instruction. A `let`
with a variable pattern, `(let $x 5 (pair $x $x))`, queries `let` with a variable argument, reads its
body through the binding `pattern = x` between two variables, and runs `unify`. This module proves
the three pieces on HE's source relations, for any atoms as arguments:

* `candidate_iff`: **`unify` has a candidate exactly when some model of the incoming bindings solves
  the equation** (the match is HE's semantic matcher, the merge any logical merge);
* `linear_row_hit`, `linear_frontier`: **the frontier of a query `(h args)` with any arguments, on a
  program whose one equation for `h` at that arity has distinct variables as parameters**: exactly one
  work, from that row, whose bindings have the incoming solutions conjoined with the equation between
  the query and the row's fresh left side; rows with another head or arity contribute nothing
  (`foreign_row_empty`);
* `let_frontier`: on HE's `let` program, for every query `(let p a b)` (variables allowed), one work
  whose fresh names `pattern'`, `atom'`, `template'` equal `p`, `a`, `b` in every model;
* `read_sound`, `read_forced`: every model of a frame sees a read through it as the value itself, and
  a read returns every atom all models force, so reads between variables need no chosen
  representative;
* `unify_published`, `unify_steps`, `minimal_unify_source`: the value `unify` publishes at a candidate
  frame is the then-branch forced by the solved equation, and every step of HE's machine, and every
  derivation of its completed relation, on a `unify` instruction is the success rule, with a
  candidate frame, or the failure rule, without one;
* `let_body_sees`, `let_published`, `let_no_candidate`, `let_semantics`: **HE's `let`, from the query
  to the value**: at every frame of the work's bindings, every `unify` candidate publishes the template
  forced by `p = a` over the incoming bindings, and there is no candidate when no model solves `p = a`.

What stays open for `let` is the evaluation around these pieces on HE's machine: the admission of
`let`'s and `unify`'s closed arrows on open arguments, the delivery of `Atom` arguments, the embedded
invocation of `unify`, and the evaluation of the published value. PeTTa's side is `LetPeTTa`.

## Controls

* `Controls.pattern_var_frontier` (positive): `(let $x 5 (pair $x $x))` has one work, whose fresh
  names equal `$x`, `5` and `(pair $x $x)` in every model.
* `Controls.five_semantics`, `Controls.five_forced` (positive): every `unify` candidate of that work
  publishes `(pair 5 5)`; HE answers `[(pair 5 5)]`.
* `Controls.swap_forced` (positive, a structured pattern): `(let (pair $a $b) (pair 1 2) (pair $b $a))`
  forces `(pair 2 1)`; HE answers `[(pair 2 1)]`.
* `Controls.read_forced_five`, `Controls.petta_read` (positive, both dialects): `(let $x 5 $x)` forces
  `5`, and PeTTa yields `5` from fuel `6` on.
* `Controls.nonlinear_unsolvable` (negative): `(let (pair $a $a) (pair 1 2) yes)` has no solving model,
  so its `unify` has no candidate (`let_no_candidate`); HE answers `[]`.
* `Controls.unify_no_candidate` (negative): `(unify (pair 1 2) (pair $a $a) yes no)` has no candidate,
  so only the failure rule applies; HE answers `[no]`.
* `Controls.nonlinear_row_misses` (negative, linearity matters): the row `(= (same $v $v) yes)` gives
  `(same 1 2)` no work; HE answers `(same 1 2)` itself.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetFrontier

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel
  EquationRowResultsRel UnifyCandidateRel UnifyNoMatchRel AlphaVariantRel QueryVisibleName)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied
  applyTypeValuation renameTypeVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (specBindingVars LogicalMergeRel
  ValuationsAgreeOn)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)

/-! ## `unify` candidates are the satisfiable equations -/

/-- **A candidate exists when a model of the incoming bindings solves the equation**: HE's semantic
matcher matches the two atoms, and the record of the match followed by the incoming record is a
logical merge. -/
theorem candidate_of_model {target pattern : Atom} {incoming : Bindings} {v : String → Atom}
    (model : TypeBindingSatisfied v incoming)
    (solves : applyTypeValuation v target = applyTypeValuation v pattern) :
    ∃ output, UnifyCandidateRel target pattern incoming output := by
  have equation : Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
      (fun name => Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.encodeModelAtom (v name))
      target pattern := by
    unfold Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
    rw [← Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,
      ← Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,
      solves]
  obtain ⟨matched, matching, satisfied⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness.exists_specMatch_of_solution equation
  refine ⟨⟨matched.assignments ++ incoming.assignments, matched.equalities ++ incoming.equalities⟩,
    matched, matching, Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _, v, ?_⟩
  exact (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.bindingSatisfied_append_iff v
    matched incoming).mpr
    ⟨(Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated
      v matched).mpr satisfied, model⟩

/-- **`unify` has a candidate exactly when some model of the incoming bindings solves the
equation.** -/
theorem candidate_iff {target pattern : Atom} {incoming : Bindings} :
    (∃ output, UnifyCandidateRel target pattern incoming output) ↔
      ∃ v, TypeBindingSatisfied v incoming ∧
        applyTypeValuation v target = applyTypeValuation v pattern := by
  constructor
  · rintro ⟨output, matched, matching, merged⟩
    obtain ⟨v, model⟩ := merged.2
    have solved := (UnifyCandidateRel.solutions ⟨matched, matching, merged⟩ v).mp model
    exact ⟨v, solved.2, solved.1⟩
  · rintro ⟨v, model, solves⟩
    exact candidate_of_model model solves

/-! ## Rows whose parameters are distinct variables -/

/-- A left side `(h $v₁ … $vₙ)` with distinct variables. -/
structure LinearLeft (left : Atom) (h : String) (vs : List String) : Prop where
  shape : left = .expression (.symbol h :: vs.map Atom.var)
  distinct : vs.Nodup

/-- The model that sends each name `rs[i]` to the base model's value of `args[i]`. -/
def extend (m : String → Atom) : List String → List Atom → String → Atom
  | r :: rs, q :: qs, name => if name = r then applyTypeValuation m q else extend m rs qs name
  | _, _, name => m name

theorem extend_outside (m : String → Atom) :
    ∀ (rs : List String) (args : List Atom) (name : String), name ∉ rs →
      extend m rs args name = m name
  | [], _, _, _ => by simp [extend]
  | _ :: _, [], _, _ => by simp [extend]
  | r :: rs, _ :: qs, name, outside => by
      simp only [List.mem_cons, not_or] at outside
      simp only [extend, if_neg outside.1]
      exact extend_outside m rs qs name outside.2

theorem extend_vars (m : String → Atom) :
    ∀ (rs : List String) (args : List Atom), rs.Nodup → rs.length = args.length →
      rs.map (extend m rs args) = args.map (applyTypeValuation m)
  | [], [], _, _ => rfl
  | [], _ :: _, _, same => by simp at same
  | _ :: _, [], _, same => by simp at same
  | r :: rs, q :: qs, distinct, same => by
      rw [List.nodup_cons] at distinct
      have tail : rs.map (extend m (r :: rs) (q :: qs)) = rs.map (extend m rs qs) := by
        apply List.map_congr_left
        intro name member
        have different : name ≠ r := fun equal => distinct.1 (equal ▸ member)
        simp only [extend, if_neg different]
      rw [List.map_cons, tail, extend_vars m rs qs distinct.2 (by simpa using same), List.map_cons]
      congr 1
      simp [extend]

theorem typeVars_vars (vs : List String) (h : String) :
    TypeSubst.typeVars (.expression (.symbol h :: vs.map Atom.var)) = vs := by
  induction vs with
  | nil => simp [TypeSubst.typeVars, TypeSubst.typeVarsList]
  | cons v vs ih =>
      simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.map_cons, List.nil_append] at ih ⊢
      simp [ih]

theorem rename_linear (rename : String → String) (h : String) (vs : List String) :
    renameTypeVars rename (.expression (.symbol h :: vs.map Atom.var)) =
      .expression (.symbol h :: (vs.map rename).map Atom.var) := by
  simp [renameTypeVars]

theorem apply_vars (v : String → Atom) (h : String) (rs : List String) :
    applyTypeValuation v (.expression (.symbol h :: rs.map Atom.var)) =
      .expression (.symbol h :: rs.map v) := by
  simp [applyTypeValuation]

theorem visible_of_support {live : List Atom} {query : Atom} {incoming : Bindings} {name : String}
    (member : name ∈ specBindingVars incoming) : QueryVisibleName live query incoming name := by
  unfold specBindingVars at member
  rw [List.mem_append, List.mem_flatMap, List.mem_flatMap] at member
  rcases member with ⟨⟨key, value⟩, assigned, inEntry⟩ | ⟨⟨left, right⟩, equal, inEntry⟩
  · simp only [List.mem_cons] at inEntry
    rcases inEntry with rfl | inValue
    · exact Or.inr (Or.inr (Or.inl ⟨value, assigned⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨key, value, assigned,
        (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars value name).mpr
          inValue⟩)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at inEntry
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, equal, inEntry⟩)))

/-- **Every alpha-variant of a linear row is viable for every query of its head and arity**, over
satisfiable incoming bindings: the fresh names are outside the query and the incoming support, so a
model of the incoming bindings extends to one solving the query's equation. -/
theorem linear_viable {live : List Atom} {h : String} {args : List Atom} {incoming : Bindings}
    {left right pattern body : Atom} {vs : List String}
    (linear : LinearLeft left h vs) (arity : vs.length = args.length)
    (satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m incoming)
    (alpha : AlphaVariantRel live (.expression (.symbol h :: args)) incoming left right pattern body) :
    ∃ output, UnifyCandidateRel (.expression (.symbol h :: args)) pattern incoming output := by
  obtain ⟨m, model⟩ := satisfiable
  obtain ⟨rename, injective, renamedLeft, _, fresh⟩ := alpha
  have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  rw [linear.shape, rename_linear] at patternEq
  have hidden : ∀ name ∈ vs.map rename,
      ¬ QueryVisibleName live (.expression (.symbol h :: args)) incoming name := by
    intro name member
    obtain ⟨v, inVs, rfl⟩ := List.mem_map.mp member
    apply fresh v
    left
    rw [Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars, linear.shape,
      typeVars_vars]
    exact inVs
  refine candidate_of_model (v := extend m (vs.map rename) args) ?_ ?_
  · refine (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.specTypeBindingSatisfied_congr_of_bindingVars
      (left := extend m (vs.map rename) args) (right := m) ?_).mpr model
    intro name member
    exact extend_outside m _ args name fun inside => hidden name inside (visible_of_support member)
  · have queryEq : applyTypeValuation (extend m (vs.map rename) args) (.expression (.symbol h :: args)) =
        applyTypeValuation m (.expression (.symbol h :: args)) :=
      Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
        _ fun name member => extend_outside m _ args name fun inside =>
          hidden name inside (Or.inl
            ((Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ name).mpr member))
    rw [queryEq, patternEq, apply_vars,
      extend_vars m _ args (linear.distinct.map injective) (by simpa using arity)]
    simp [applyTypeValuation]

/-- **A linear row contributes exactly one work** to the frontier of a query of its head and arity,
whatever the query's arguments. -/
theorem linear_row_hit {live : List Atom} {h : String} {args : List Atom} {incoming : Bindings}
    {position : Nat} {left right : Atom} {vs : List String} {block : List EquationWork}
    (linear : LinearLeft left h vs) (arity : vs.length = args.length)
    (satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m incoming)
    (row : EquationRowResultsRel live (.expression (.symbol h :: args)) incoming position
      (.expression [.symbol "=", left, right]) block) :
    ∃ w : EquationWork, block = [w] ∧ w.left = left ∧ w.right = right := by
  cases row with
  | irrelevant _ notEquation => exact absurd rfl (notEquation left right)
  | miss _ _ pattern body alpha absent =>
      obtain ⟨output, matched, matching, merged⟩ := linear_viable linear arity satisfiable alpha
      exact absurd ⟨matching, merged⟩ (absent pattern body alpha matched output)
  | hit _ _ pattern body matched output => exact ⟨_, rfl, rfl, rfl⟩

/-- A row foreign to the queries `(h a₁ … aₙ)`: not an equation, or an equation whose left side has
another head symbol or another arity. -/
def Foreign (h : String) (n : Nat) (row : Atom) : Prop :=
  (∀ l r, row ≠ .expression [.symbol "=", l, r]) ∨
    ∃ l r g tail, row = .expression [.symbol "=", l, r] ∧ l = .expression (.symbol g :: tail) ∧
      (g ≠ h ∨ tail.length ≠ n)

/-- **A foreign row contributes no work.** -/
theorem foreign_row_empty {live : List Atom} {h : String} {args : List Atom} {incoming : Bindings}
    {position : Nat} {row : Atom} {block : List EquationWork}
    (foreign : Foreign h args.length row)
    (rel : EquationRowResultsRel live (.expression (.symbol h :: args)) incoming position row block) :
    block = [] := by
  cases rel with
  | irrelevant => rfl
  | miss => rfl
  | hit l r pattern body matched output alpha matching merged =>
      exfalso
      obtain ⟨v, model⟩ := merged.2
      have solved := ((UnifyCandidateRel.solutions ⟨matched, matching, merged⟩ v).mp model).1
      obtain ⟨rename, _, renamedLeft, _, _⟩ := alpha
      have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
      rcases foreign with notEquation | ⟨l', r', g, tail, same, shape, differs⟩
      · exact notEquation l r rfl
      · simp only [Atom.expression.injEq, List.cons.injEq, and_true, true_and] at same
        obtain ⟨rfl, rfl⟩ := same
        rw [patternEq, shape] at solved
        simp only [applyTypeValuation, renameTypeVars, List.map_cons, List.map_map,
          Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at solved
        obtain ⟨sameHead, sameArgs⟩ := solved
        rcases differs with otherHead | otherArity
        · exact otherHead sameHead.symm
        · have lengths := congrArg List.length sameArgs
          simp only [List.length_map] at lengths
          exact otherArity lengths.symm

theorem foreign_ne {h : String} {n : Nat} {left right row : Atom} {vs : List String}
    (linear : LinearLeft left h vs) (arity : vs.length = n) (foreign : Foreign h n row) :
    row ≠ .expression [.symbol "=", left, right] := by
  intro same
  rcases foreign with notEquation | ⟨l', r', g, tail, rowShape, shape, differs⟩
  · exact notEquation left right same
  · rw [same] at rowShape
    simp only [Atom.expression.injEq, List.cons.injEq, and_true, true_and] at rowShape
    rw [← rowShape.1, linear.shape] at shape
    simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at shape
    rcases differs with otherHead | otherArity
    · exact otherHead shape.1.symm
    · apply otherArity
      rw [← shape.2, List.length_map, arity]

/-- The sides of the works of a frontier, row by row: the linear row gives its sides, every foreign
row nothing. -/
theorem sides_of_rows {live : List Atom} {h : String} {args : List Atom} {incoming : Bindings}
    {left right : Atom} {vs : List String}
    (linear : LinearLeft left h vs) (arity : vs.length = args.length)
    (satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m incoming) :
    ∀ (rows : List Atom) (k : Nat) (blocks : List (List EquationWork)),
      (∀ row ∈ rows, row = .expression [.symbol "=", left, right] ∨ Foreign h args.length row) →
      List.Forall₂ (fun row block => EquationRowResultsRel live (.expression (.symbol h :: args))
        incoming row.2 row.1 block) (rows.zipIdx k) blocks →
      blocks.flatten.map (fun w => (w.left, w.right)) =
        rows.filterMap (fun row =>
          if row = .expression [.symbol "=", left, right] then some (left, right) else none) := by
  intro rows
  induction rows with
  | nil =>
      intro k blocks _ covered
      cases covered
      rfl
  | cons row rows ih =>
      intro k blocks kinds covered
      rw [List.zipIdx_cons] at covered
      cases covered with
      | cons here rest =>
          have tail := ih (k + 1) _ (fun r member => kinds r (List.mem_cons_of_mem _ member)) rest
          rcases kinds row List.mem_cons_self with isRow | foreign
          · subst isRow
            obtain ⟨w, rfl, wLeft, wRight⟩ := linear_row_hit linear arity satisfiable here
            simp only [List.flatten_cons, List.singleton_append, List.map_cons, wLeft, wRight, tail,
              List.filterMap_cons, ↓reduceIte]
          · have empty := foreign_row_empty foreign here
            subst empty
            simp only [List.flatten_cons, List.nil_append, tail, List.filterMap_cons,
              if_neg (foreign_ne linear arity foreign)]

/-- **HE's frontier of a query `(h args)` with any arguments, on a program whose one equation for `h`
at that arity is linear: exactly one work, from that row.** -/
theorem linear_frontier {pre post live : List Atom} {h : String} {args : List Atom}
    {incoming : Bindings} {left right : Atom} {vs : List String} {works : List EquationWork}
    (linear : LinearLeft left h vs) (arity : vs.length = args.length)
    (foreign : ∀ row ∈ pre ++ post, Foreign h args.length row)
    (satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m incoming)
    (frontier : EquationFrontierRel (Space.ofList (pre ++ .expression [.symbol "=", left, right] :: post))
      live (.expression (.symbol h :: args)) incoming works) :
    ∃ w : EquationWork, works = [w] ∧ w.left = left ∧ w.right = right := by
  cases frontier with
  | completed covered =>
      have kinds : ∀ row ∈ pre ++ .expression [.symbol "=", left, right] :: post,
          row = .expression [.symbol "=", left, right] ∨ Foreign h args.length row := by
        intro row member
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inPre | rfl | inPost
        · exact Or.inr (foreign row (List.mem_append_left _ inPre))
        · exact Or.inl rfl
        · exact Or.inr (foreign row (List.mem_append_right _ inPost))
      have sides := sides_of_rows linear arity satisfiable _ 0 _ kinds covered
      have none : ∀ rows : List Atom, (∀ row ∈ rows, Foreign h args.length row) →
          rows.filterMap (fun row =>
            if row = .expression [.symbol "=", left, right] then some (left, right) else none) = [] := by
        intro rows all
        rw [List.filterMap_eq_nil_iff]
        intro row member
        simp only [if_neg (foreign_ne linear arity (all row member))]
      rw [List.filterMap_append, List.filterMap_cons, if_pos rfl,
        none pre (fun row member => foreign row (List.mem_append_left _ member)),
        none post (fun row member => foreign row (List.mem_append_right _ member))] at sides
      obtain ⟨w, same, sidesW⟩ := List.map_eq_singleton_iff.mp sides
      simp only [Prod.mk.injEq] at sidesW
      exact ⟨w, same, sidesW.1, sidesW.2⟩

/-! ## HE's `let` row -/

/-- `(: let (-> Atom %Undefined% Atom %Undefined%))`. -/
def letDecl : Atom := .expression [.symbol ":", .symbol "let",
  .expression [.symbol "->", .symbol "Atom", Atom.undefinedType, .symbol "Atom", Atom.undefinedType]]

/-- `(: unify (-> Atom Atom Atom Atom %Undefined%))`. -/
def unifyDecl : Atom := .expression [.symbol ":", .symbol "unify",
  .expression [.symbol "->", .symbol "Atom", .symbol "Atom", .symbol "Atom", .symbol "Atom",
    Atom.undefinedType]]

/-- `(let $pattern $atom $template)`. -/
def letLeft : Atom := .expression [.symbol "let", .var "pattern", .var "atom", .var "template"]

/-- `(unify $atom $pattern $template Empty)`. -/
def letRight : Atom :=
  .expression [.symbol "unify", .var "atom", .var "pattern", .var "template", Atom.empty]

/-- HE's `let` program, as in HE's standard library. -/
abbrev letRows : List Atom := [letDecl, unifyDecl, .expression [.symbol "=", letLeft, letRight]]

theorem let_linear : LinearLeft letLeft "let" ["pattern", "atom", "template"] := ⟨rfl, by decide⟩

theorem decls_foreign : ∀ row ∈ [letDecl, unifyDecl], Foreign "let" 3 row := by
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    exact Or.inl fun l r same => by simp [letDecl, unifyDecl] at same

/-- **HE's frontier of `(let p a b)`, for any atoms `p`, `a`, `b`** (a variable pattern included), on
HE's `let` program with rows foreign to `let`: one work, from the `let` row, freshened by an injective
renaming; its bindings hold exactly when the fresh `pattern'`, `atom'`, `template'` equal `p`, `a`,
`b` and the incoming bindings hold. -/
theorem let_frontier {rest live : List Atom} {p a b : Atom} {incoming : Bindings}
    {works : List EquationWork} (foreign : ∀ row ∈ rest, Foreign "let" 3 row)
    (satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m incoming)
    (frontier : EquationFrontierRel (Space.ofList (letRows ++ rest)) live
      (.expression [.symbol "let", p, a, b]) incoming works) :
    ∃ (w : EquationWork) (rename : String → String), works = [w] ∧ Function.Injective rename ∧
      w.pattern = .expression [.symbol "let", .var (rename "pattern"), .var (rename "atom"),
        .var (rename "template")] ∧
      w.body = .expression [.symbol "unify", .var (rename "atom"), .var (rename "pattern"),
        .var (rename "template"), Atom.empty] ∧
      ∀ v : String → Atom, TypeBindingSatisfied v w.bindings ↔
        (applyTypeValuation v p = v (rename "pattern") ∧ applyTypeValuation v a = v (rename "atom") ∧
          applyTypeValuation v b = v (rename "template")) ∧ TypeBindingSatisfied v incoming := by
  have shaped : letRows ++ rest =
      [letDecl, unifyDecl] ++ .expression [.symbol "=", letLeft, letRight] :: rest := rfl
  rw [shaped] at frontier
  obtain ⟨w, rfl, wLeft, wRight⟩ := linear_frontier (pre := [letDecl, unifyDecl]) (post := rest)
    (args := [p, a, b]) let_linear rfl
    (fun row member => by
      rcases List.mem_append.mp member with inDecls | inRest
      · exact decls_foreign row inDecls
      · exact foreign row inRest)
    satisfiable frontier
  obtain ⟨matched, occurrence⟩ := frontier.occurrence (List.mem_singleton_self w)
  obtain ⟨rename, injective, renamedLeft, renamedRight, _⟩ := occurrence.selected.1
  have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  have bodyEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedRight
  rw [wLeft] at patternEq
  rw [wRight] at bodyEq
  refine ⟨w, rename, rfl, injective, ?_, ?_, fun v => ?_⟩
  · rw [patternEq]
    simp [letLeft, renameTypeVars]
  · rw [bodyEq]
    simp [letRight, renameTypeVars, Atom.empty]
  · rw [occurrence.solutions v, patternEq]
    simp [letLeft, renameTypeVars, applyTypeValuation]

/-! ## Reads between variables -/

/-- **Every model of a frame sees a read through it as the value itself**: whichever representative
the frame's readout picks for a class of variables, the models of its bindings agree. -/
theorem read_sound (policy : Policy) (frame : Frame) (x : Entry.Value) {v : String → Atom}
    (model : TypeBindingSatisfied v frame.bindings) :
    applyTypeValuation v (frame.read policy x).erase = applyTypeValuation v x.erase := by
  unfold Completed.Frame.read
  rw [Entry.Value.erase_substitute_environment]
  exact ((frame.certified.theory v).mpr model).absorbs x.erase

/-- **A read through a frame returns every atom that all models of the frame force.** -/
theorem read_forced (policy : Policy) (frame : Frame) (x : Entry.Value) (G : Atom)
    (forced : ∀ v, TypeBindingSatisfied v frame.bindings → applyTypeValuation v x.erase = G) :
    (frame.read policy x).erase = G := by
  unfold Completed.Frame.read
  rw [Entry.Value.erase_substitute_environment]
  exact frame.certified.forced_read x.erase G forced

/-! ## HE's minimal `unify` -/

/-- **The value `unify` publishes at a candidate frame is the then-branch forced by the solved
equation.** -/
theorem unify_published (policy : Policy) {target pattern : Atom} {activation : Bindings}
    {output : Frame} (candidate : UnifyCandidateRel target pattern activation output.bindings)
    (yes : Entry.Value) (G : Atom)
    (forced : ∀ v, TypeBindingSatisfied v activation →
      applyTypeValuation v target = applyTypeValuation v pattern → applyTypeValuation v yes.erase = G) :
    (output.read policy yes).erase = G :=
  read_forced policy output yes G fun v model => by
    obtain ⟨solves, before⟩ := (UnifyCandidateRel.solutions candidate v).mp model
    exact forced v before solves

/-- **Every step of HE's machine on a `unify` instruction** is the success rule, with a candidate
frame, publishing the read of the then-branch there, or the failure rule, without any candidate,
publishing the else-branch. -/
theorem unify_steps {dispatch : GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    {S : Space} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Entry.Status} {target pattern yes no : Entry.Value} {activation : Frame}
    {stack : List Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Continuation}
    {emitted : List Completed.Result} {z : HEOnTheStep.HEConfig}
    (moved : Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.Step dispatch lookup policy
      ⟨S, .work (.minimal live scope caller
        (.expression readiness [.symbol "unify", target, pattern, yes, no]) activation), stack, emitted⟩ z) :
    (∃ output : Frame, UnifyCandidateRel target.erase pattern.erase activation.bindings output.bindings ∧
        z = ⟨S, .returning [(output.read policy yes, output)], stack, emitted⟩) ∨
      (UnifyNoMatchRel target.erase pattern.erase activation.bindings ∧
        z = ⟨S, .returning [(no, activation)], stack, emitted⟩) := by
  generalize same : Entry.Value.expression readiness [.symbol "unify", target, pattern, yes, no] =
    instruction at moved
  cases moved with
  | internal l =>
      cases l with
      | minimalData notInstruction =>
          subst same
          simp [Minimal.embeddedInstruction, Entry.Value.erase] at notInstruction
      | minimalUnifyYes candidate _ =>
          simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
          exact Or.inl ⟨_, candidate, rfl⟩
      | minimalUnifyNo noMatch =>
          simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
          exact Or.inr ⟨noMatch, rfl⟩
      | minimalUnifyBadArity badLength =>
          simp only [Entry.Value.expression.injEq, List.cons.injEq, true_and] at same
          obtain ⟨-, rfl⟩ := same
          exact absurd rfl badLength
      | _ => simp at same

/-- **Every derivation of HE's completed relation for a `unify` instruction** is the success rule,
with a candidate frame, publishing the read of the then-branch there, or the failure rule, without
any candidate, publishing the else-branch. -/
theorem minimal_unify_source {dispatch : GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Policy} {S : Space} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Entry.Status} {target pattern yes no : Entry.Value} {frame : Frame}
    {results : List Completed.Result}
    (derived : Completed.MinimalRel S dispatch lookup live scope caller
      (.expression readiness [.symbol "unify", target, pattern, yes, no]) frame results
      (policy := policy)) :
    (∃ output : Frame, UnifyCandidateRel target.erase pattern.erase frame.bindings output.bindings ∧
        results = [(output.read policy yes, output)]) ∨
      (UnifyNoMatchRel target.erase pattern.erase frame.bindings ∧ results = [(no, frame)]) := by
  generalize same : Entry.Value.expression readiness [.symbol "unify", target, pattern, yes, no] =
    instruction at derived
  cases derived with
  | data notInstruction =>
      subst same
      simp [Minimal.embeddedInstruction, Entry.Value.erase] at notInstruction
  | unifyYes candidate _ =>
      simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
      exact Or.inl ⟨_, candidate, rfl⟩
  | unifyNo noMatch =>
      simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
      exact Or.inr ⟨noMatch, rfl⟩
  | unifyBadArity badLength =>
      simp only [Entry.Value.expression.injEq, List.cons.injEq, true_and] at same
      obtain ⟨-, rfl⟩ := same
      exact absurd rfl badLength
  | _ => simp at same

/-! ## The value of `let` -/

/-- **What the models of the `let` work see.** At every frame carrying the bindings of the `let`
row's work, every model of the frame satisfies the incoming bindings, and sees the reads of the fresh
`atom'`, `pattern'`, `template'` as `a`, `p`, `b`. -/
theorem let_body_sees (policy : Policy) {p a b : Atom} {incoming : Bindings} {w : EquationWork}
    {rename : String → String}
    (solutions : ∀ v : String → Atom, TypeBindingSatisfied v w.bindings ↔
      (applyTypeValuation v p = v (rename "pattern") ∧ applyTypeValuation v a = v (rename "atom") ∧
        applyTypeValuation v b = v (rename "template")) ∧ TypeBindingSatisfied v incoming)
    (frame : Frame) (sameBindings : frame.bindings = w.bindings) (v : String → Atom)
    (model : TypeBindingSatisfied v frame.bindings) :
    TypeBindingSatisfied v incoming ∧
      applyTypeValuation v (frame.read policy (.var (rename "atom"))).erase = applyTypeValuation v a ∧
      applyTypeValuation v (frame.read policy (.var (rename "pattern"))).erase =
        applyTypeValuation v p ∧
      applyTypeValuation v (frame.read policy (.var (rename "template"))).erase =
        applyTypeValuation v b := by
  have work := (solutions v).mp (sameBindings ▸ model)
  obtain ⟨⟨isP, isA, isB⟩, before⟩ := work
  refine ⟨before, ?_, ?_, ?_⟩ <;>
    rw [read_sound policy frame _ model] <;>
    simp [Entry.Value.erase, applyTypeValuation, isP, isA, isB]

/-- **The value of `let` with any pattern.** When the models of a frame see the `unify`
instruction's target, pattern and then-branch as `a`, `p` and `b` over the incoming bindings
(`let_body_sees`), every candidate frame of `unify` publishes `G`, provided every model of the
incoming bindings solving `p = a` sends `b` to `G`. -/
theorem let_published (policy : Policy) {incoming : Bindings} {p a b G : Atom} {activation : Frame}
    {target pattern : Atom} {yes : Entry.Value} {output : Frame}
    (sees : ∀ v, TypeBindingSatisfied v activation.bindings →
      TypeBindingSatisfied v incoming ∧ applyTypeValuation v target = applyTypeValuation v a ∧
        applyTypeValuation v pattern = applyTypeValuation v p ∧
        applyTypeValuation v yes.erase = applyTypeValuation v b)
    (forced : ∀ v, TypeBindingSatisfied v incoming →
      applyTypeValuation v p = applyTypeValuation v a → applyTypeValuation v b = G)
    (candidate : UnifyCandidateRel target pattern activation.bindings output.bindings) :
    (output.read policy yes).erase = G :=
  unify_published policy candidate yes G fun v model solves => by
    obtain ⟨before, isA, isP, isB⟩ := sees v model
    rw [isB]
    exact forced v before (by rw [← isP, ← isA, solves])

/-- **A `let` whose pattern no model of the incoming bindings unifies with its atom has no `unify`
candidate**, so only the failure rule applies and `unify` publishes its else-branch. -/
theorem let_no_candidate {incoming : Bindings} {p a b : Atom} {activation : Frame}
    {target pattern : Atom} {yes : Entry.Value}
    (sees : ∀ v, TypeBindingSatisfied v activation.bindings →
      TypeBindingSatisfied v incoming ∧ applyTypeValuation v target = applyTypeValuation v a ∧
        applyTypeValuation v pattern = applyTypeValuation v p ∧
        applyTypeValuation v yes.erase = applyTypeValuation v b)
    (unsolvable : ∀ v, TypeBindingSatisfied v incoming →
      applyTypeValuation v p ≠ applyTypeValuation v a) :
    UnifyNoMatchRel target pattern activation.bindings := by
  intro output candidate
  obtain ⟨v, model, solves⟩ := candidate_iff.mp ⟨output, candidate⟩
  obtain ⟨before, isA, isP, _⟩ := sees v model
  exact unsolvable v before (by rw [← isP, ← isA, solves])

/-- **HE's `let`, from the query to the value `unify` publishes.** On HE's `let` program, for every
query `(let p a b)` (any atoms, a variable pattern included) over satisfiable incoming bindings, every
frontier has one work, whose body is `(unify $atom' $pattern' $template' Empty)`; at every frame
carrying its bindings, every candidate frame of `unify` on the reads of `$atom'` and `$pattern'`
publishes the read of `$template'` as `G`, whenever every model of the incoming bindings solving
`p = a` sends `b` to `G`; and `unify` has no candidate when no such model solves `p = a`. -/
theorem let_semantics (policy : Policy) {rest live : List Atom} {p a b : Atom} {incoming : Bindings}
    {works : List EquationWork} (foreign : ∀ row ∈ rest, Foreign "let" 3 row)
    (satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m incoming)
    (frontier : EquationFrontierRel (Space.ofList (letRows ++ rest)) live
      (.expression [.symbol "let", p, a, b]) incoming works) :
    ∃ (w : EquationWork) (rename : String → String), works = [w] ∧
      w.body = .expression [.symbol "unify", .var (rename "atom"), .var (rename "pattern"),
        .var (rename "template"), Atom.empty] ∧
      ∀ frame : Frame, frame.bindings = w.bindings →
        (∀ G : Atom, (∀ v, TypeBindingSatisfied v incoming →
            applyTypeValuation v p = applyTypeValuation v a → applyTypeValuation v b = G) →
          ∀ output : Frame, UnifyCandidateRel (frame.read policy (.var (rename "atom"))).erase
              (frame.read policy (.var (rename "pattern"))).erase frame.bindings output.bindings →
            (output.read policy (frame.read policy (.var (rename "template")))).erase = G) ∧
        ((∀ v, TypeBindingSatisfied v incoming → applyTypeValuation v p ≠ applyTypeValuation v a) →
          UnifyNoMatchRel (frame.read policy (.var (rename "atom"))).erase
            (frame.read policy (.var (rename "pattern"))).erase frame.bindings) := by
  obtain ⟨w, rename, same, _, _, body, solutions⟩ := let_frontier foreign satisfiable frontier
  refine ⟨w, rename, same, body, fun frame sameBindings => ⟨?_, ?_⟩⟩
  · intro G forced output candidate
    exact let_published policy (fun v model => let_body_sees policy solutions frame sameBindings v model)
      forced candidate
  · intro unsolvable
    exact let_no_candidate (fun v model => let_body_sees policy solutions frame sameBindings v model)
      unsolvable

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app)

theorem empty_satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m Bindings.empty :=
  ⟨fun _ => Atom.undefinedType, by
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
      Bindings.empty]⟩

/-- `(let $x 5 (pair $x $x))`. -/
def fiveCall : Atom :=
  .expression [.symbol "let", .var "x", .grounded (.int 5), app "pair" [.var "x", .var "x"]]

/-- **Positive control, a variable pattern**: the frontier of `(let $x 5 (pair $x $x))` exists, and
every frontier has one work whose models send the fresh `pattern'`, `atom'`, `template'` to `$x`, `5`
and `(pair $x $x)`. -/
theorem pattern_var_frontier (live : List Atom) :
    (∃ works, EquationFrontierRel (Space.ofList letRows) live fiveCall Bindings.empty works) ∧
    ∀ works, EquationFrontierRel (Space.ofList letRows) live fiveCall Bindings.empty works →
      ∃ (w : EquationWork) (rename : String → String), works = [w] ∧
        ∀ v : String → Atom, TypeBindingSatisfied v w.bindings ↔
          (v "x" = v (rename "pattern") ∧ Atom.grounded (.int 5) = v (rename "atom") ∧
            app "pair" [v "x", v "x"] = v (rename "template")) ∧
          TypeBindingSatisfied v Bindings.empty := by
  refine ⟨EntryToQuery.frontier_total _ live fiveCall Bindings.empty, fun works frontier => ?_⟩
  have rows : letRows = letRows ++ [] := rfl
  rw [rows] at frontier
  obtain ⟨w, rename, same, _, _, _, solutions⟩ :=
    let_frontier (by simp) empty_satisfiable frontier
  refine ⟨w, rename, same, fun v => ?_⟩
  rw [solutions v]
  simp [applyTypeValuation, app]

/-- **Positive control, the value**: every model of the empty bindings solving `$x = 5` sends
`(pair $x $x)` to `(pair 5 5)`, so every candidate frame of the `unify` of `(let $x 5 (pair $x $x))`
publishes `(pair 5 5)` (`let_published`); HE answers `[(pair 5 5)]`. -/
theorem five_forced : ∀ v : String → Atom, TypeBindingSatisfied v Bindings.empty →
    applyTypeValuation v (.var "x") = applyTypeValuation v (.grounded (.int 5)) →
    applyTypeValuation v (app "pair" [.var "x", .var "x"]) =
      app "pair" [.grounded (.int 5), .grounded (.int 5)] := by
  intro v _ solves
  simp only [applyTypeValuation] at solves
  simp [applyTypeValuation, app, solves]

/-- **Positive control, end to end**: for `(let $x 5 (pair $x $x))` on HE's `let` program, every
frontier has one work, and at every frame of its bindings every candidate frame of its `unify`
publishes `(pair 5 5)`; HE answers `[(pair 5 5)]`. -/
theorem five_semantics (policy : Policy) (live : List Atom) (works : List EquationWork)
    (frontier : EquationFrontierRel (Space.ofList letRows) live fiveCall Bindings.empty works) :
    ∃ (w : EquationWork) (rename : String → String), works = [w] ∧
      ∀ frame : Frame, frame.bindings = w.bindings →
        ∀ output : Frame, UnifyCandidateRel (frame.read policy (.var (rename "atom"))).erase
            (frame.read policy (.var (rename "pattern"))).erase frame.bindings output.bindings →
          (output.read policy (frame.read policy (.var (rename "template")))).erase =
            app "pair" [.grounded (.int 5), .grounded (.int 5)] := by
  have rows : letRows = letRows ++ [] := rfl
  rw [rows] at frontier
  obtain ⟨w, rename, same, _, semantics⟩ := let_semantics policy (by simp) empty_satisfiable frontier
  exact ⟨w, rename, same, fun frame sameBindings =>
    (semantics frame sameBindings).1 _ five_forced⟩

/-- **Positive control, a structured pattern**: `(let (pair $a $b) (pair 1 2) (pair $b $a))` forces
`(pair 2 1)`; HE answers `[(pair 2 1)]`. -/
theorem swap_forced : ∀ v : String → Atom, TypeBindingSatisfied v Bindings.empty →
    applyTypeValuation v (app "pair" [.var "a", .var "b"]) =
      applyTypeValuation v (app "pair" [.grounded (.int 1), .grounded (.int 2)]) →
    applyTypeValuation v (app "pair" [.var "b", .var "a"]) =
      app "pair" [.grounded (.int 2), .grounded (.int 1)] := by
  intro v _ solves
  simp only [applyTypeValuation, app, List.map_cons, List.map_nil, Atom.expression.injEq,
    List.cons.injEq, and_true, true_and] at solves
  simp [applyTypeValuation, app, solves.1, solves.2]

/-- **Negative control, a non-linear pattern**: `(let (pair $a $a) (pair 1 2) yes)` has no model
solving its equation, so its `unify` has no candidate and publishes the else-branch `Empty`
(`let_no_candidate`); HE answers `[]`. -/
theorem nonlinear_unsolvable : ∀ v : String → Atom, TypeBindingSatisfied v Bindings.empty →
    applyTypeValuation v (app "pair" [.var "a", .var "a"]) ≠
      applyTypeValuation v (app "pair" [.grounded (.int 1), .grounded (.int 2)]) := by
  intro v _ solves
  simp only [applyTypeValuation, app, List.map_cons, List.map_nil, Atom.expression.injEq,
    List.cons.injEq, and_true, true_and] at solves
  have oneTwo := solves.1.symm.trans solves.2
  simp at oneTwo

/-- **Negative control, `unify` without candidate**: `(unify (pair 1 2) (pair $a $a) yes no)` has no
candidate at any bindings, so every step takes the failure rule (`unify_steps`); HE answers `[no]`. -/
theorem unify_no_candidate (incoming : Bindings) :
    UnifyNoMatchRel (app "pair" [.grounded (.int 1), .grounded (.int 2)])
      (app "pair" [.var "a", .var "a"]) incoming := by
  intro output candidate
  obtain ⟨v, _, solves⟩ := candidate_iff.mp ⟨output, candidate⟩
  simp only [applyTypeValuation, app, List.map_cons, List.map_nil, Atom.expression.injEq,
    List.cons.injEq, and_true, true_and] at solves
  rw [← solves.1] at solves
  simp at solves

/-- `(= (same $v $v) yes)`. -/
def sameRow : Atom :=
  .expression [.symbol "=", app "same" [.var "v", .var "v"], sym "yes"]

/-- **Negative control, linearity matters**: the non-linear row `(= (same $v $v) yes)` contributes no
work to the frontier of `(same 1 2)`; HE answers `(same 1 2)` itself. -/
theorem nonlinear_row_misses {live : List Atom} {incoming : Bindings} {position : Nat}
    {block : List EquationWork}
    (row : EquationRowResultsRel live (app "same" [.grounded (.int 1), .grounded (.int 2)]) incoming
      position sameRow block) : block = [] := by
  cases row with
  | irrelevant => rfl
  | miss => rfl
  | hit l r pattern body matched output alpha matching merged =>
      exfalso
      obtain ⟨v, model⟩ := merged.2
      have solved := ((UnifyCandidateRel.solutions ⟨matched, matching, merged⟩ v).mp model).1
      obtain ⟨rename, _, renamedLeft, _, _⟩ := alpha
      have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
      rw [patternEq] at solved
      simp only [applyTypeValuation, renameTypeVars, app, List.map_cons, List.map_nil,
        Atom.expression.injEq, List.cons.injEq, and_true, true_and] at solved
      rw [← solved.1] at solved
      simp at solved

/-! ### PeTTa on the same programs -/

open Mettapedia.Languages.MeTTa.PeTTa
open AnswerBags (translate store advance_stable)

/-- `(let $x 5 $x)`. -/
def readCall : Atom := .expression [.symbol "let", .var "x", .grounded (.int 5), .var "x"]

/-- **Positive control, the binding read back**: every model of the empty bindings solving
`$x = 5` sends `$x` to `5`, so every candidate frame of the `unify` of `(let $x 5 $x)` publishes `5`
(`let_published`). -/
theorem read_forced_five : ∀ v : String → Atom, TypeBindingSatisfied v Bindings.empty →
    applyTypeValuation v (.var "x") = applyTypeValuation v (.grounded (.int 5)) →
    applyTypeValuation v (.var "x") = .grounded (.int 5) := by
  intro v _ solves
  simpa [applyTypeValuation] using solves

/-- **PeTTa's `let` with a variable pattern** yields `5` for `(let $x 5 $x)` from fuel `6` on, the
value HE's `unify` publishes at every candidate frame (`read_forced_five`). -/
theorem petta_read : ∀ k, 6 ≤ k → Streaming.values (Streaming.advance (translate letRows) k
    (Streaming.enter { state := store letRows } readCall)) = [.grounded (.int 5)] := by
  have done : (Streaming.advance (translate letRows) 6
      (Streaming.enter { state := store letRows } readCall)).agenda.length = 0 := by
    decide +kernel
  have value : Streaming.values (Streaming.advance (translate letRows) 6
      (Streaming.enter { state := store letRows } readCall)) = [.grounded (.int 5)] := by
    decide +kernel
  intro k bigger
  rw [advance_stable (List.eq_nil_of_length_eq_zero done) k bigger]
  exact value

end Controls

#print axioms Controls.read_forced_five
#print axioms Controls.petta_read
#print axioms candidate_iff
#print axioms linear_row_hit
#print axioms foreign_row_empty
#print axioms linear_frontier
#print axioms let_frontier
#print axioms read_sound
#print axioms read_forced
#print axioms unify_published
#print axioms unify_steps
#print axioms minimal_unify_source
#print axioms let_body_sees
#print axioms let_published
#print axioms let_no_candidate
#print axioms let_semantics
#print axioms Controls.five_semantics
#print axioms Controls.pattern_var_frontier
#print axioms Controls.five_forced
#print axioms Controls.swap_forced
#print axioms Controls.nonlinear_unsolvable
#print axioms Controls.unify_no_candidate
#print axioms Controls.nonlinear_row_misses

end LetFrontier

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
