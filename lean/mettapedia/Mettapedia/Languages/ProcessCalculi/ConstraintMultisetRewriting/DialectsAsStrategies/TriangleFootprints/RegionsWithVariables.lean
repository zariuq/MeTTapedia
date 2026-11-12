import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.WholeRunWords
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness

/-!
# Regions with pattern variables: HE's and PeTTa's regions agree outside H2's two separators

`GroundFragment` proved that HE's region of an equation query and PeTTa's region of a call agree
when every equation's left side is a literal. Here the left sides may carry variables: a row
`(= (f p₁ … pₙ) rhs)` whose head is a symbol and whose argument patterns have no `cons` list view
(`ConsFree`, `ConsFreeHeads`); variables may repeat. The call is `(f v₁ … vₙ)` with variable-free
values. These are exactly the rows outside H2's two separating programs (a head that is not a
symbol, a `cons` list view).

## Results

* `he_hit_instance`: when HE's region holds such a row, a valuation instantiates its left side to
  the call. HE's surviving candidate makes the query and the fresh pattern equal in every model of
  its bindings (`UnifyCandidateRel.solutions`), the fresh pattern is a renaming of the left side
  (`EquationFreshening.alphaRename_eq`), and the call has no variables.
* `completesConsistent`: PeTTa's argument matching (`SpaceSemantics.matchValue`) succeeds on every
  instance of a `cons`-free pattern, from bindings consistent with the instance. Hence
  `he_region_sub_petta_consFree`: **HE's region lies inside PeTTa's**, for any incoming bindings.
* `sound`, `sound_list`: PeTTa's matching on a `cons`-free pattern is sound: every extension of its
  result instantiates the pattern to the value.
* `he_inside_of_instance_satisfiable`: a left side with an instance equal to the call is in HE's
  region under any satisfiable incoming bindings. HE's semantic matcher completeness
  (`Spec.Match.Completeness.exists_specMatch_of_solution`) gives the match against the fresh
  variant, `ScopeObservation.ModelTransport` carries its model back, and the fresh names are hidden
  from the incoming record, so one valuation serves both. Hence **PeTTa's region lies inside HE's**.
* `regions_agree_consFree`, `footprints_coincide_consFree`: **the two regions agree, and the two
  footprints coincide, at every activation frame of HE's machine, on programs of symbol-headed,
  `cons`-free equations.** This extends `GroundFragment.footprints_coincide` from literal left sides
  to patterns with variables.
* `whole_run_rows_consFree`: the whole-run rows of `WholeRunWords` agree on that fragment;
  `Controls.h1_whole_run` is H1's own program `{(p a), (= (double $x) (+ $x $x))}`.
* The linear versions (`completes`, `he_region_sub_petta`, `regions_agree_linear`, …) were the first
  steps and remain as corollaries; `he_rows_sub_petta` states the inclusion as a sublist of rows.

## Controls

* `Controls.h1_row_inside_both`: H1's row `(= (double $x) (+ $x $x))` is in both regions of
  `(double 4)`.
* `Controls.repeated_variable` (positive and negative): on `(= (same $x $x) yes)` the call
  `(same 1 1)` is in HE's region, `(same 1 2)` is not, at every activation.
* `Controls.cons_row_outside_fragment`: H2's `cons` list-view row lies outside the fragment, and
  there the regions part: PeTTa's region holds it, HE's does not.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace RegionsWithVariables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst.typeVars TypeSubst.typeVarsList)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (applyTypeValuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (AlphaVariantRel EquationRowResultsRel
  UnifyCandidateRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (LogicalMergeRel)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (matchValue matchValue_expression_of_not_cons)
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings (rowSupply Row)

/-! ## Patterns -/

/-- **A pattern without PeTTa's `cons` list view** at any position; variables are allowed. -/
inductive ConsFree : Atom → Prop
  | var (name : String) : ConsFree (.var name)
  | symbol (name : String) : ConsFree (.symbol name)
  | grounded (value : GroundedValue) : ConsFree (.grounded value)
  | expression (items : List Atom) (notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest])
      (members : ∀ item ∈ items, ConsFree item) : ConsFree (.expression items)

/-! ## PeTTa's matching succeeds on instances -/

/-- PeTTa's matching of a pattern against one of its instances, from bindings that leave the
pattern's variables free, succeeds and binds only the pattern's variables. -/
def Completes (valuation : String → Atom) (pattern : Atom) : Prop :=
  ∀ σ : Mettapedia.Languages.ProcessCalculi.MORK.Subst, (TypeSubst.typeVars pattern).Nodup →
    (∀ x ∈ TypeSubst.typeVars pattern, σ.lookup x = none) →
      ∃ σ', matchValue σ pattern (applyTypeValuation valuation pattern) = some σ' ∧
        ∀ x, x ∉ TypeSubst.typeVars pattern → σ'.lookup x = σ.lookup x

theorem completes_list (valuation : String → Atom) :
    ∀ (items : List Atom), (∀ item ∈ items, Completes valuation item) →
      ∀ σ : Mettapedia.Languages.ProcessCalculi.MORK.Subst, (TypeSubst.typeVarsList items).Nodup →
        (∀ x ∈ TypeSubst.typeVarsList items, σ.lookup x = none) →
          ∃ σ', matchValue.matchValues σ items (items.map (applyTypeValuation valuation)) =
              some σ' ∧
            ∀ x, x ∉ TypeSubst.typeVarsList items → σ'.lookup x = σ.lookup x
  | [], _, σ, _, _ => ⟨σ, by simp [matchValue.matchValues], fun _ _ => rfl⟩
  | item :: rest, each, σ, distinct, unbound => by
      have distinct' : (TypeSubst.typeVars item ++ TypeSubst.typeVarsList rest).Nodup := distinct
      obtain ⟨σ₁, first, frame₁⟩ := each item List.mem_cons_self σ distinct'.of_append_left
        (fun x member => unbound x (List.mem_append_left _ member))
      have apart := List.disjoint_of_nodup_append distinct'
      obtain ⟨σ₂, later, frame₂⟩ := completes_list valuation rest
        (fun other member => each other (List.mem_cons_of_mem _ member)) σ₁
        distinct'.of_append_right (fun x member => by
          rw [frame₁ x (fun inItem => apart inItem member)]
          exact unbound x (List.mem_append_right _ member))
      refine ⟨σ₂, ?_, fun x outside => ?_⟩
      · simp [matchValue.matchValues, first, later]
      · have outside' : x ∉ TypeSubst.typeVars item ∧ x ∉ TypeSubst.typeVarsList rest := by
          constructor
          · exact fun member => outside (List.mem_append_left _ member)
          · exact fun member => outside (List.mem_append_right _ member)
        rw [frame₂ x outside'.2, frame₁ x outside'.1]

/-- **PeTTa's matching succeeds on every instance of a linear, `cons`-free pattern.** -/
theorem completes (valuation : String → Atom) {pattern : Atom} (consFree : ConsFree pattern) :
    Completes valuation pattern := by
  induction consFree with
  | var name =>
      intro σ _ unbound
      have free : σ.lookup name = none := unbound name (List.mem_singleton_self _)
      refine ⟨(name, valuation name) :: σ, ?_, fun x outside => ?_⟩
      · have applied : applyTypeValuation valuation (.var name) = valuation name := by
          simp [applyTypeValuation]
        rw [applied]
        generalize valuation name = value
        cases value <;> simp [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, free]
      · have different : name ≠ x := fun same => outside (by simp [TypeSubst.typeVars, same])
        simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, beq_eq_false_iff_ne.mpr different]
  | symbol name =>
      intro σ _ _
      exact ⟨σ, by simp [matchValue, applyTypeValuation,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom], fun _ _ => rfl⟩
  | grounded value =>
      intro σ _ _
      exact ⟨σ, by simp [matchValue, applyTypeValuation,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom], fun _ _ => rfl⟩
  | expression items notCons _ ih =>
      intro σ distinct unbound
      obtain ⟨σ', matched, frame⟩ := completes_list valuation items ih σ distinct unbound
      refine ⟨σ', ?_, frame⟩
      have applied : applyTypeValuation valuation (.expression items) =
          .expression (items.map (applyTypeValuation valuation)) := by
        simp [applyTypeValuation]
      rw [applied, matchValue_expression_of_not_cons σ items _ notCons]
      exact matched

/-! ## Without linearity: matching from bindings consistent with the instance -/

/-- Bindings consistent with a valuation: every bound name holds the valuation's atom. -/
def Consistent (valuation : String → Atom) (σ : Mettapedia.Languages.ProcessCalculi.MORK.Subst) :
    Prop :=
  ∀ x a, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup σ x = some a → a = valuation x

/-- PeTTa's matching of a pattern against one of its instances, from bindings consistent with the
instance, succeeds with bindings consistent with it. Repeated variables are allowed. -/
def CompletesConsistent (valuation : String → Atom) (pattern : Atom) : Prop :=
  ∀ σ, Consistent valuation σ →
    ∃ σ', matchValue σ pattern (applyTypeValuation valuation pattern) = some σ' ∧
      Consistent valuation σ'

theorem completesConsistent_list (valuation : String → Atom) :
    ∀ (items : List Atom), (∀ item ∈ items, CompletesConsistent valuation item) →
      ∀ σ, Consistent valuation σ →
        ∃ σ', matchValue.matchValues σ items (items.map (applyTypeValuation valuation)) =
            some σ' ∧ Consistent valuation σ'
  | [], _, σ, consistent => ⟨σ, by simp [matchValue.matchValues], consistent⟩
  | item :: rest, each, σ, consistent => by
      obtain ⟨σ₁, first, consistent₁⟩ := each item List.mem_cons_self σ consistent
      obtain ⟨σ₂, later, consistent₂⟩ := completesConsistent_list valuation rest
        (fun other member => each other (List.mem_cons_of_mem _ member)) σ₁ consistent₁
      exact ⟨σ₂, by simp [matchValue.matchValues, first, later], consistent₂⟩

/-- **PeTTa's matching succeeds on every instance of a `cons`-free pattern**, repeated variables
included, from bindings consistent with the instance. -/
theorem completesConsistent (valuation : String → Atom) {pattern : Atom}
    (consFree : ConsFree pattern) : CompletesConsistent valuation pattern := by
  induction consFree with
  | var name =>
      intro σ consistent
      have applied : applyTypeValuation valuation (.var name) = valuation name := by
        simp [applyTypeValuation]
      rw [applied]
      cases bound : Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup σ name with
      | some held =>
          have same : held = valuation name := consistent name held bound
          refine ⟨σ, ?_, consistent⟩
          rw [← same]
          cases held <;>
            simp [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, bound]
      | none =>
          refine ⟨(name, valuation name) :: σ, ?_, fun x a found => ?_⟩
          · generalize valuation name = value
            cases value <;>
              simp [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, bound]
          · by_cases same : x = name
            · subst same
              simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] at found
              exact found.symm
            · exact consistent x a (by
                simpa [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
                  beq_eq_false_iff_ne.mpr (Ne.symm same)] using found)
  | symbol name =>
      intro σ consistent
      exact ⟨σ, by simp [matchValue, applyTypeValuation,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom], consistent⟩
  | grounded value =>
      intro σ consistent
      exact ⟨σ, by simp [matchValue, applyTypeValuation,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom], consistent⟩
  | expression items notCons _ ih =>
      intro σ consistent
      obtain ⟨σ', matched, consistent'⟩ := completesConsistent_list valuation items ih σ consistent
      refine ⟨σ', ?_, consistent'⟩
      have applied : applyTypeValuation valuation (.expression items) =
          .expression (items.map (applyTypeValuation valuation)) := by
        simp [applyTypeValuation]
      rw [applied, matchValue_expression_of_not_cons σ items _ notCons]
      exact matched

/-! ## HE's hits are instances -/

/-- **A row in HE's region of a ground query has a left side that instantiates to the query.** -/
theorem he_hit_instance {live : List Atom} {query lhs rhs : Atom} {incoming : Bindings}
    (ground : TypeSubst.typeVars query = [])
    (inside : eqRegion live query incoming (.expression [.symbol "=", lhs, rhs]) = true) :
    ∃ valuation : String → Atom, applyTypeValuation valuation lhs = query := by
  have notInert : ¬ Inert live query incoming (.expression [.symbol "=", lhs, rhs]) := by
    simpa [eqRegion] using inside
  have candidate : ∃ pattern body, AlphaVariantRel live query incoming lhs rhs pattern body ∧
      ∃ matched output, MatchRel equalityGroundedSemantic query pattern matched ∧
        LogicalMergeRel matched incoming output := by
    by_contra none
    apply notInert
    intro position block
    constructor
    · intro derived
      cases derived with
      | irrelevant =>
          rename_i notEquation
          exact absurd rfl (notEquation _ _)
      | miss => rfl
      | hit =>
          exact absurd ⟨_, _, ‹AlphaVariantRel _ _ _ _ _ _ _›, _, _, ‹MatchRel _ _ _ _›,
            ‹LogicalMergeRel _ _ _›⟩ none
    · rintro rfl
      exact .miss position lhs rhs _ _
        (Mettapedia.Languages.MeTTa.HE.EquationFreshening.freshRule_alphaVariant live query lhs rhs
          incoming position)
        (fun pattern body alpha matched output viable =>
          none ⟨pattern, body, alpha, matched, output, viable.1, viable.2⟩)
  obtain ⟨pattern, body, alpha, matched, output, matching, merged⟩ := candidate
  obtain ⟨valuation, model⟩ := merged.2
  have equal := ((UnifyCandidateRel.solutions ⟨matched, matching, merged⟩ valuation).mp model).1
  obtain ⟨rename, _, renamedLeft, _, _⟩ := alpha
  rw [Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
    Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground valuation ground] at equal
  exact ⟨valuation ∘ rename, equal.symm⟩

/-! ## The inclusion -/

/-- **HE's region lies inside PeTTa's on symbol-headed equations with linear, `cons`-free argument
patterns**, for a call with variable-free values. -/
theorem he_region_sub_petta (live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = []) {incoming : Bindings}
    {name : String} {args : List Atom} {rhs : Atom}
    (consFree : ∀ arg ∈ args, ConsFree arg) (linear : (TypeSubst.typeVarsList args).Nodup)
    (inside : eqRegion live (.expression (.symbol head :: values)) incoming
      (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) = true) :
    pettaCallRegion head values
      (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) = true := by
  have closedQuery : TypeSubst.typeVars (.expression (.symbol head :: values)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff values).mpr ground
  obtain ⟨valuation, instantiated⟩ := he_hit_instance closedQuery inside
  simp only [applyTypeValuation, List.map_cons, Atom.expression.injEq, List.cons.injEq,
    Atom.symbol.injEq] at instantiated
  obtain ⟨sameHead, sameValues⟩ := instantiated
  subst sameHead sameValues
  obtain ⟨σ', matched, _⟩ := completes_list valuation args
    (fun arg member => completes valuation (consFree arg member)) [] linear
    (by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup])
  simp [pettaCallRegion, LiveEquations.equationOfRow, matched]

/-- The fragment of rows: non-equations, and equations whose left side is a symbol applied to
linear, `cons`-free argument patterns. -/
def LinearHeads (row : Atom) : Prop :=
  ∀ lhs rhs, row = .expression [.symbol "=", lhs, rhs] →
    ∃ name args, lhs = .expression (.symbol name :: args) ∧ (∀ arg ∈ args, ConsFree arg) ∧
      (TypeSubst.typeVarsList args).Nodup

/-- **On a program of such rows, HE's equation query reads a sublist of the rows PeTTa's complete
call request reads**, with their positions. -/
theorem he_rows_sub_petta (atoms live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = []) {incoming : Bindings}
    (program : ∀ row ∈ atoms, LinearHeads row) :
    (regionRows (eqRegion live (.expression (.symbol head :: values)) incoming)
        (Space.ofList atoms).atoms).Sublist
      ((completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
        fun row => (row.atom, row.serial)) := by
  rw [completeCall_load]
  have sub : ∀ row ∈ atoms, eqRegion live (.expression (.symbol head :: values)) incoming row = true →
      pettaCallRegion head values row = true := by
    intro row member inside
    by_cases isEquation : ∃ lhs rhs, row = .expression [.symbol "=", lhs, rhs]
    · obtain ⟨lhs, rhs, rfl⟩ := isEquation
      obtain ⟨name, args, rfl, consFree, linear⟩ := program _ member lhs rhs rfl
      exact he_region_sub_petta live ground consFree linear inside
    · rw [eqRegion_not_equation fun lhs rhs same => isEquation ⟨lhs, rhs, same⟩] at inside
      cases inside
  have shrink : regionRows (eqRegion live (.expression (.symbol head :: values)) incoming) atoms =
      (regionRows (pettaCallRegion head values) atoms).filter
        fun row => eqRegion live (.expression (.symbol head :: values)) incoming row.1 := by
    unfold regionRows
    rw [List.filter_filter]
    apply List.filter_congr
    intro row member
    by_cases inside : eqRegion live (.expression (.symbol head :: values)) incoming row.1 = true
    · simp [inside, sub row.1 (List.fst_mem_of_mem_zipIdx member) inside]
    · simp [inside]
  show (regionRows (eqRegion live (.expression (.symbol head :: values)) incoming) atoms).Sublist _
  rw [shrink]
  exact List.filter_sublist

/-! ## The converse at HE's entry: PeTTa's region lies inside HE's -/

/-- One substitution extends another: every binding is kept. -/
def Extends (σ τ : Mettapedia.Languages.ProcessCalculi.MORK.Subst) : Prop :=
  ∀ x a, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup σ x = some a →
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup τ x = some a

theorem Extends.refl (σ : Mettapedia.Languages.ProcessCalculi.MORK.Subst) : Extends σ σ :=
  fun _ _ found => found

theorem Extends.trans {σ τ υ : Mettapedia.Languages.ProcessCalculi.MORK.Subst}
    (first : Extends σ τ) (second : Extends τ υ) : Extends σ υ :=
  fun x a found => second x a (first x a found)

/-- The valuation a substitution presents: bound names to their atoms, free names to themselves. -/
def asValuation (τ : Mettapedia.Languages.ProcessCalculi.MORK.Subst) : String → Atom :=
  fun x => (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup τ x).getD (.var x)

/-- PeTTa's matching is sound: it extends its bindings, binds every variable of the pattern, and every
extension of its result instantiates the pattern to the value. -/
def Sound (pattern : Atom) : Prop :=
  ∀ σ σ' value, matchValue σ pattern value = some σ' →
    Extends σ σ' ∧
      (∀ x ∈ TypeSubst.typeVars pattern,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup σ' x ≠ none) ∧
      ∀ τ, Extends σ' τ → applyTypeValuation (asValuation τ) pattern = value

theorem sound_list : ∀ (items : List Atom), (∀ item ∈ items, Sound item) →
    ∀ σ σ' values, matchValue.matchValues σ items values = some σ' →
      Extends σ σ' ∧
        (∀ x ∈ TypeSubst.typeVarsList items,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup σ' x ≠ none) ∧
        ∀ τ, Extends σ' τ → items.map (applyTypeValuation (asValuation τ)) = values
  | [], _, σ, σ', values, matched => by
      cases values with
      | nil =>
          simp only [matchValue.matchValues, Option.some.injEq] at matched
          subst matched
          exact ⟨Extends.refl _, fun _ member => by simp [TypeSubst.typeVarsList] at member,
            fun _ _ => rfl⟩
      | cons _ _ => simp [matchValue.matchValues] at matched
  | item :: rest, each, σ, σ', values, matched => by
      cases values with
      | nil => simp [matchValue.matchValues] at matched
      | cons value later =>
          simp only [matchValue.matchValues, Option.bind_eq_bind] at matched
          cases first : matchValue σ item value with
          | none => simp [first] at matched
          | some σ₁ =>
              rw [first, Option.bind_some] at matched
              obtain ⟨extends₁, bound₁, instance₁⟩ := each item List.mem_cons_self σ σ₁ value first
              obtain ⟨extends₂, bound₂, instance₂⟩ := sound_list rest
                (fun other member => each other (List.mem_cons_of_mem _ member)) σ₁ σ' later matched
              refine ⟨extends₁.trans extends₂, fun x member => ?_, fun τ extended => ?_⟩
              · rcases List.mem_append.mp member with inItem | inRest
                · intro unbound
                  obtain ⟨a, found⟩ := Option.ne_none_iff_exists'.mp (bound₁ x inItem)
                  rw [extends₂ x a found] at unbound
                  cases unbound
                · exact bound₂ x inRest
              · rw [List.map_cons, instance₁ τ (extends₂.trans extended), instance₂ τ extended]

/-- **PeTTa's matching is sound on `cons`-free patterns.** -/
theorem sound {pattern : Atom} (consFree : ConsFree pattern) : Sound pattern := by
  induction consFree with
  | var name =>
      intro σ σ' value matched
      cases bound : Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup σ name with
      | some held =>
          have same : value = held ∧ σ' = σ := by
            cases value <;> simp_all [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
          obtain ⟨rfl, rfl⟩ := same
          refine ⟨Extends.refl _, fun x member => ?_, fun τ extended => ?_⟩
          · simp only [TypeSubst.typeVars, List.mem_singleton] at member
            subst member
            simp [bound]
          · simp [applyTypeValuation, asValuation, extended name value bound]
      | none =>
          have same : σ' = (name, value) :: σ := by
            cases value <;> simp_all [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
          subst same
          have here : Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup ((name, value) :: σ) name =
              some value := by
            simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
          refine ⟨fun x a found => ?_, fun x member => ?_, fun τ extended => ?_⟩
          · by_cases same : x = name
            · subst same
              rw [bound] at found
              cases found
            · simpa [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
                beq_eq_false_iff_ne.mpr (Ne.symm same)] using found
          · simp only [TypeSubst.typeVars, List.mem_singleton] at member
            subst member
            simp [here]
          · simp [applyTypeValuation, asValuation, extended name value here]
  | symbol name =>
      intro σ σ' value matched
      have same : value = .symbol name ∧ σ' = σ := by
        cases value <;> simp_all [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨Extends.refl _, fun x member => by simp [TypeSubst.typeVars] at member,
        fun _ _ => by simp [applyTypeValuation]⟩
  | grounded ground =>
      intro σ σ' value matched
      have same : value = .grounded ground ∧ σ' = σ := by
        cases value <;> simp_all [matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨Extends.refl _, fun x member => by simp [TypeSubst.typeVars] at member,
        fun _ _ => by simp [applyTypeValuation]⟩
  | expression items notCons _ ih =>
      intro σ σ' value matched
      cases value with
      | expression values =>
          rw [matchValue_expression_of_not_cons σ items values notCons] at matched
          obtain ⟨extended, bound, instantiated⟩ := sound_list items ih σ σ' values matched
          refine ⟨extended, bound, fun τ further => ?_⟩
          simp only [applyTypeValuation, instantiated τ further]
      | symbol _ => simp [matchValue] at matched
      | var _ => simp [matchValue] at matched
      | grounded _ => simp [matchValue] at matched

/-- **A left side with an instance equal to the call is in HE's region of the call**, at the empty
incoming bindings of HE's entry. HE's semantic matcher completeness
(`Spec.Match.Completeness.exists_specMatch_of_solution`) supplies the match against the fresh
variant, and the valuation transport of `ScopeObservation.ModelTransport` its model. -/
theorem he_inside_of_instance (live : List Atom) {query lhs rhs : Atom}
    (ground : TypeSubst.typeVars query = []) (valuation : String → Atom)
    (instantiated : applyTypeValuation valuation lhs = query) :
    eqRegion live query Bindings.empty (.expression [.symbol "=", lhs, rhs]) = true := by
  apply eqRegion_of_not_inert
  intro inert
  obtain ⟨pattern, body, alpha⟩ : ∃ pattern body,
      AlphaVariantRel live query Bindings.empty lhs rhs pattern body :=
    ⟨_, _, Mettapedia.Languages.MeTTa.HE.EquationFreshening.freshRule_alphaVariant live query lhs rhs
      Bindings.empty 0⟩
  obtain ⟨rename, injective, renamedLeft, renamedRight, fresh⟩ := alpha
  let w : String → Atom := fun x => valuation (Function.invFun rename x)
  have conjugate : w ∘ rename = valuation := by
    funext x
    simp [w, Function.leftInverse_invFun injective x]
  have patternInstance : applyTypeValuation w pattern = query := by
    rw [Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      conjugate, instantiated]
  have equation : Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
      (fun name => Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.encodeModelAtom (w name))
      query pattern := by
    unfold Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
    rw [← Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,
      ← Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,
      patternInstance, Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground w ground]
  obtain ⟨out, matching, satisfied⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness.exists_specMatch_of_solution equation
  have model : Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied w out :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated
      w out).mpr satisfied
  have merged : LogicalMergeRel out Bindings.empty
      ⟨out.assignments ++ Bindings.empty.assignments, out.equalities ++ Bindings.empty.equalities⟩ := by
    refine ⟨Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _, w, ?_, ?_⟩
    · intro name value member
      exact model.1 name value (by simpa [Bindings.empty] using member)
    · intro left right member
      exact model.2 left right (by simpa [Bindings.empty] using member)
  have hit := EquationRowResultsRel.hit 0 lhs rhs pattern body out _
    ⟨rename, injective, renamedLeft, renamedRight, fresh⟩ matching merged
  cases (inert 0 _).mp hit

/-- **The same under any satisfiable incoming bindings.** The fresh variant's names are hidden from
the incoming record (`AlphaVariantRel`'s freshness), so one valuation can agree with the instance on
the pattern and with a model of the incoming record elsewhere. -/
theorem he_inside_of_instance_satisfiable (live : List Atom) {query lhs rhs : Atom}
    {incoming : Bindings} (ground : TypeSubst.typeVars query = []) (valuation : String → Atom)
    (instantiated : applyTypeValuation valuation lhs = query)
    (satisfiable : ∃ model : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming) :
    eqRegion live query incoming (.expression [.symbol "=", lhs, rhs]) = true := by
  apply eqRegion_of_not_inert
  intro inert
  obtain ⟨pattern, body, alpha⟩ : ∃ pattern body,
      AlphaVariantRel live query incoming lhs rhs pattern body :=
    ⟨_, _, Mettapedia.Languages.MeTTa.HE.EquationFreshening.freshRule_alphaVariant live query lhs rhs
      incoming 0⟩
  obtain ⟨rename, injective, renamedLeft, renamedRight, fresh⟩ := alpha
  obtain ⟨model, satisfied⟩ := satisfiable
  have patternShape :=
    Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  have hidden : ∀ n, n ∈ TypeSubst.typeVars pattern →
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.QueryVisibleName live query incoming n := by
    intro n member
    rw [patternShape,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
      at member
    obtain ⟨x, inLhs, rfl⟩ := List.mem_map.mp member
    exact fresh x (Or.inl
      ((Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars lhs x).mpr inLhs))
  let w : String → Atom := fun x => valuation (Function.invFun rename x)
  let c : String → Atom := fun x => if x ∈ TypeSubst.typeVars pattern then w x else model x
  have conjugate : w ∘ rename = valuation := by
    funext x
    simp [w, Function.leftInverse_invFun injective x]
  have patternInstance : applyTypeValuation c pattern = query := by
    rw [Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
      (left := c) (right := w) pattern (fun n member => by simp only [c, if_pos member]),
      patternShape,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      conjugate, instantiated]
  have equation : Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
      (fun name => Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.encodeModelAtom (c name))
      query pattern := by
    unfold Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
    rw [← Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,
      ← Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,
      patternInstance, Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground c ground]
  obtain ⟨out, matching, solved⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness.exists_specMatch_of_solution equation
  have outModel : Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied c out :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated
      c out).mpr solved
  have incomingModel :
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied c incoming := by
    constructor
    · intro name value member
      have nameOut : name ∉ TypeSubst.typeVars pattern := fun inPattern =>
        hidden name inPattern (Or.inr (Or.inr (Or.inl ⟨value, member⟩)))
      have valueAgrees : applyTypeValuation c value = applyTypeValuation model value :=
        Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
          value (fun n inValue => by
            have notPattern : n ∉ TypeSubst.typeVars pattern := fun inPattern =>
              hidden n inPattern (Or.inr (Or.inr (Or.inr (Or.inl ⟨name, value, member,
                (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars value n).mpr
                  inValue⟩))))
            simp only [c, if_neg notPattern])
      rw [valueAgrees]
      simp only [c, if_neg nameOut]
      exact satisfied.1 name value member
    · intro left right member
      have leftOut : left ∉ TypeSubst.typeVars pattern := fun inPattern =>
        hidden left inPattern (Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, Or.inl rfl⟩))))
      have rightOut : right ∉ TypeSubst.typeVars pattern := fun inPattern =>
        hidden right inPattern (Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, Or.inr rfl⟩))))
      simp only [c, if_neg leftOut, if_neg rightOut]
      exact satisfied.2 left right member
  have merged : LogicalMergeRel out incoming
      ⟨out.assignments ++ incoming.assignments, out.equalities ++ incoming.equalities⟩ := by
    refine ⟨Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _, c, ?_, ?_⟩
    · intro name value member
      rcases List.mem_append.mp member with inOut | inIncoming
      · exact outModel.1 name value inOut
      · exact incomingModel.1 name value inIncoming
    · intro left right member
      rcases List.mem_append.mp member with inOut | inIncoming
      · exact outModel.2 left right inOut
      · exact incomingModel.2 left right inIncoming
  have hit := EquationRowResultsRel.hit 0 lhs rhs pattern body out _
    ⟨rename, injective, renamedLeft, renamedRight, fresh⟩ matching merged
  cases (inert 0 _).mp hit

/-- **The regions agree at every activation**: for symbol-headed equations with linear, `cons`-free
argument patterns, a call with variable-free values and satisfiable incoming bindings. -/
theorem regions_agree_linear_satisfiable (live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = []) {incoming : Bindings}
    (satisfiable : ∃ model : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming)
    {name : String} {args : List Atom} {rhs : Atom}
    (consFree : ∀ arg ∈ args, ConsFree arg) (linear : (TypeSubst.typeVarsList args).Nodup) :
    eqRegion live (.expression (.symbol head :: values)) incoming
        (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) =
      pettaCallRegion head values
        (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨he_region_sub_petta live ground consFree linear, fun inPetta => ?_⟩
  have closedQuery : TypeSubst.typeVars (.expression (.symbol head :: values)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff values).mpr ground
  simp only [pettaCallRegion, LiveEquations.equationOfRow, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists] at inPetta
  obtain ⟨⟨sameHead, _⟩, σ', matched⟩ := inPetta
  subst sameHead
  obtain ⟨_, _, instantiated⟩ := sound_list args (fun arg member => sound (consFree arg member))
    [] σ' values matched
  apply he_inside_of_instance_satisfiable live closedQuery (asValuation σ') _ satisfiable
  simp only [applyTypeValuation, List.map_cons, instantiated σ' (Extends.refl _)]

/-- **At HE's entry the two regions agree on symbol-headed equations with linear, `cons`-free
argument patterns**, for a call with variable-free values. -/
theorem regions_agree_linear (live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = [])
    {name : String} {args : List Atom} {rhs : Atom}
    (consFree : ∀ arg ∈ args, ConsFree arg) (linear : (TypeSubst.typeVarsList args).Nodup) :
    eqRegion live (.expression (.symbol head :: values)) Bindings.empty
        (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) =
      pettaCallRegion head values
        (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨he_region_sub_petta live ground consFree linear, fun inPetta => ?_⟩
  have closedQuery : TypeSubst.typeVars (.expression (.symbol head :: values)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff values).mpr ground
  simp only [pettaCallRegion, LiveEquations.equationOfRow, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists] at inPetta
  obtain ⟨⟨sameHead, _⟩, σ', matched⟩ := inPetta
  subst sameHead
  obtain ⟨_, _, instantiated⟩ := sound_list args (fun arg member => sound (consFree arg member))
    [] σ' values matched
  apply he_inside_of_instance live closedQuery (asValuation σ')
  simp only [applyTypeValuation, List.map_cons, instantiated σ' (Extends.refl _)]

/-- `LinearHeads` rows: the two regions of an entry query agree on them. -/
theorem regions_agree_row (live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = []) {row : Atom}
    (fragment : LinearHeads row) :
    eqRegion live (.expression (.symbol head :: values)) Bindings.empty row =
      pettaCallRegion head values row := by
  by_cases isEquation : ∃ lhs rhs, row = .expression [.symbol "=", lhs, rhs]
  · obtain ⟨lhs, rhs, rfl⟩ := isEquation
    obtain ⟨name, args, rfl, consFree, linear⟩ := fragment lhs rhs rfl
    exact regions_agree_linear live ground consFree linear
  · have notEquation : ∀ lhs rhs, row ≠ .expression [.symbol "=", lhs, rhs] :=
      fun lhs rhs same => isEquation ⟨lhs, rhs, same⟩
    rw [eqRegion_not_equation notEquation]
    have none : LiveEquations.equationOfRow row = none := by
      unfold LiveEquations.equationOfRow
      split
      · exact absurd rfl (notEquation _ _)
      · rfl
    exact (pettaCallRegion_not_equation none).symm

/-- **The footprints coincide on programs with linear, `cons`-free, symbol-headed equations**: at
HE's entry, HE's equation query and PeTTa's complete call request read the same positioned rows. -/
theorem footprints_coincide_linear (atoms live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = [])
    (program : ∀ row ∈ atoms, LinearHeads row) :
    regionRows (eqRegion live (.expression (.symbol head :: values)) Bindings.empty)
        (Space.ofList atoms).atoms =
      (completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
        (fun row => (row.atom, row.serial)) :=
  (read_word_triangle atoms live _ Bindings.empty head values).mpr fun row member =>
    regions_agree_row live ground (program row member)

/-- Row by row, under any satisfiable incoming bindings. -/
theorem regions_agree_row_satisfiable (live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = []) {incoming : Bindings}
    (satisfiable : ∃ model : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming)
    {row : Atom} (fragment : LinearHeads row) :
    eqRegion live (.expression (.symbol head :: values)) incoming row =
      pettaCallRegion head values row := by
  by_cases isEquation : ∃ lhs rhs, row = .expression [.symbol "=", lhs, rhs]
  · obtain ⟨lhs, rhs, rfl⟩ := isEquation
    obtain ⟨name, args, rfl, consFree, linear⟩ := fragment lhs rhs rfl
    exact regions_agree_linear_satisfiable live ground satisfiable consFree linear
  · have notEquation : ∀ lhs rhs, row ≠ .expression [.symbol "=", lhs, rhs] :=
      fun lhs rhs same => isEquation ⟨lhs, rhs, same⟩
    rw [eqRegion_not_equation notEquation]
    have none : LiveEquations.equationOfRow row = none := by
      unfold LiveEquations.equationOfRow
      split
      · exact absurd rfl (notEquation _ _)
      · rfl
    exact (pettaCallRegion_not_equation none).symm

/-- **The footprints coincide at every activation frame of HE's machine** on programs of
symbol-headed equations with linear, `cons`-free argument patterns. -/
theorem footprints_coincide_linear_at_activation (atoms live : List Atom) {head : String}
    {values : List Atom} (ground : ∀ value ∈ values, TypeSubst.typeVars value = [])
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame)
    (program : ∀ row ∈ atoms, LinearHeads row) :
    regionRows (eqRegion live (.expression (.symbol head :: values)) activation.bindings)
        (Space.ofList atoms).atoms =
      (completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
        (fun row => (row.atom, row.serial)) :=
  (read_word_triangle atoms live _ activation.bindings head values).mpr fun row member =>
    regions_agree_row_satisfiable live ground activation.certified.satisfiable (program row member)

/-! ## Without linearity -/

/-- **The fragment without linearity**: non-equations, and equations whose left side is a symbol
applied to `cons`-free argument patterns, repeated variables allowed. -/
def ConsFreeHeads (row : Atom) : Prop :=
  ∀ lhs rhs, row = .expression [.symbol "=", lhs, rhs] →
    ∃ name args, lhs = .expression (.symbol name :: args) ∧ ∀ arg ∈ args, ConsFree arg

theorem consistent_nil (valuation : String → Atom) : Consistent valuation [] :=
  fun x a found => by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] at found

/-- **HE's region lies inside PeTTa's on symbol-headed, `cons`-free equations**, repeated variables
included. -/
theorem he_region_sub_petta_consFree (live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = []) {incoming : Bindings}
    {name : String} {args : List Atom} {rhs : Atom} (consFree : ∀ arg ∈ args, ConsFree arg)
    (inside : eqRegion live (.expression (.symbol head :: values)) incoming
      (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) = true) :
    pettaCallRegion head values
      (.expression [.symbol "=", .expression (.symbol name :: args), rhs]) = true := by
  have closedQuery : TypeSubst.typeVars (.expression (.symbol head :: values)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff values).mpr ground
  obtain ⟨valuation, instantiated⟩ := he_hit_instance closedQuery inside
  simp only [applyTypeValuation, List.map_cons, Atom.expression.injEq, List.cons.injEq,
    Atom.symbol.injEq] at instantiated
  obtain ⟨sameHead, sameValues⟩ := instantiated
  subst sameHead sameValues
  obtain ⟨σ', matched, _⟩ := completesConsistent_list valuation args
    (fun arg member => completesConsistent valuation (consFree arg member)) []
    (consistent_nil valuation)
  simp [pettaCallRegion, LiveEquations.equationOfRow, matched]

/-- **The two regions agree on symbol-headed, `cons`-free equations**, at every satisfiable incoming
binding record, repeated variables included. The only rows left out are H2's two separators: a head
that is not a symbol, and a `cons` list view. -/
theorem regions_agree_consFree (live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = []) {incoming : Bindings}
    (satisfiable : ∃ model : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming)
    {row : Atom} (fragment : ConsFreeHeads row) :
    eqRegion live (.expression (.symbol head :: values)) incoming row =
      pettaCallRegion head values row := by
  by_cases isEquation : ∃ lhs rhs, row = .expression [.symbol "=", lhs, rhs]
  · obtain ⟨lhs, rhs, rfl⟩ := isEquation
    obtain ⟨name, args, rfl, consFree⟩ := fragment lhs rhs rfl
    apply Bool.eq_iff_iff.mpr
    refine ⟨he_region_sub_petta_consFree live ground consFree, fun inPetta => ?_⟩
    have closedQuery : TypeSubst.typeVars (.expression (.symbol head :: values)) = [] := by
      simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
      exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff values).mpr ground
    simp only [pettaCallRegion, LiveEquations.equationOfRow, Bool.and_eq_true, beq_iff_eq,
      Option.isSome_iff_exists] at inPetta
    obtain ⟨⟨sameHead, _⟩, σ', matched⟩ := inPetta
    subst sameHead
    obtain ⟨_, _, instantiated⟩ := sound_list args (fun arg member => sound (consFree arg member))
      [] σ' values matched
    apply he_inside_of_instance_satisfiable live closedQuery (asValuation σ') _ satisfiable
    simp only [applyTypeValuation, List.map_cons, instantiated σ' (Extends.refl _)]
  · have notEquation : ∀ lhs rhs, row ≠ .expression [.symbol "=", lhs, rhs] :=
      fun lhs rhs same => isEquation ⟨lhs, rhs, same⟩
    rw [eqRegion_not_equation notEquation]
    have none : LiveEquations.equationOfRow row = none := by
      unfold LiveEquations.equationOfRow
      split
      · exact absurd rfl (notEquation _ _)
      · rfl
    exact (pettaCallRegion_not_equation none).symm

/-- **The footprints coincide at every activation frame** on programs of symbol-headed, `cons`-free
equations: HE's equation query and PeTTa's complete call request read the same positioned rows. -/
theorem footprints_coincide_consFree (atoms live : List Atom) {head : String} {values : List Atom}
    (ground : ∀ value ∈ values, TypeSubst.typeVars value = [])
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame)
    (program : ∀ row ∈ atoms, ConsFreeHeads row) :
    regionRows (eqRegion live (.expression (.symbol head :: values)) activation.bindings)
        (Space.ofList atoms).atoms =
      (completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
        (fun row => (row.atom, row.serial)) :=
  (read_word_triangle atoms live _ activation.bindings head values).mpr fun row member =>
    regions_agree_consFree live ground activation.certified.satisfiable (program row member)

/-- **The whole-run rows agree on programs of symbol-headed, `cons`-free equations**, for a flat
call of data atoms that the program does not declare. -/
theorem whole_run_rows_consFree {atoms : List Atom} {f : String} {args : List Atom}
    (data : ∀ a ∈ Atom.symbol f :: args, EntryToQuery.DataAtom a)
    (undeclared : ∀ a ∈ Atom.symbol f :: args, ∀ row ∈ atoms,
      ServiceFootprints.typeRegion a row = false)
    (program : ∀ row ∈ atoms, ConsFreeHeads row) :
    (WholeRunWords.heRows atoms f args).flatten = WholeRunWords.pettaRows atoms f args := by
  have before := EntryToQuery.entry_rows_empty (atoms := atoms) undeclared
  have query : regionRows (eqRegion [Atom.undefinedType] (.expression (.symbol f :: args))
      Bindings.empty) atoms = WholeRunWords.pettaRows atoms f args :=
    footprints_coincide_consFree atoms [Atom.undefinedType]
      (fun value member => WholeRunWords.data_closed (data value (List.mem_cons_of_mem _ member)))
      Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame.empty program
  have empty : ((EntryToQuery.entryWord ServiceFootprints.rawDeclared f args).map
      fun ρ => regionRows ρ atoms).flatten = [] := by
    apply List.flatten_eq_nil_iff.mpr
    intro rows member
    obtain ⟨ρ, inWord, rfl⟩ := List.mem_map.mp member
    exact before ρ inWord
  simp only [WholeRunWords.heRows, List.map_append, List.flatten_append, empty, List.nil_append,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, query]

/-- **The whole-run rows agree on the larger fragment**: for a flat call of data atoms on a program
of symbol-headed equations with linear, `cons`-free patterns that declares none of the call's atoms,
HE's rows from the entry through the query are PeTTa's request rows. -/
theorem whole_run_rows_linear {atoms : List Atom} {f : String} {args : List Atom}
    (data : ∀ a ∈ Atom.symbol f :: args, EntryToQuery.DataAtom a)
    (undeclared : ∀ a ∈ Atom.symbol f :: args, ∀ row ∈ atoms,
      ServiceFootprints.typeRegion a row = false)
    (program : ∀ row ∈ atoms, LinearHeads row) :
    (WholeRunWords.heRows atoms f args).flatten = WholeRunWords.pettaRows atoms f args := by
  have before := EntryToQuery.entry_rows_empty (atoms := atoms) undeclared
  have query : regionRows (eqRegion [Atom.undefinedType] (.expression (.symbol f :: args))
      Bindings.empty) atoms = WholeRunWords.pettaRows atoms f args :=
    footprints_coincide_linear atoms [Atom.undefinedType]
      (fun value member => WholeRunWords.data_closed (data value (List.mem_cons_of_mem _ member)))
      program
  have empty : ((EntryToQuery.entryWord ServiceFootprints.rawDeclared f args).map
      fun ρ => regionRows ρ atoms).flatten = [] := by
    apply List.flatten_eq_nil_iff.mpr
    intro rows member
    obtain ⟨ρ, inWord, rfl⟩ := List.mem_map.mp member
    exact before ρ inWord
  simp only [WholeRunWords.heRows, List.map_append, List.flatten_append, empty, List.nil_append,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, query]

/-! ## Controls -/

namespace Controls

open Instance (h1_inside)

/-- **Positive control: H1's row is in both regions.** `(= (double $x) (+ $x $x))` is in the
fragment, in HE's region of `(double 4)` (for scopes that do not show `$x`), and so in PeTTa's. -/
theorem h1_row_inside_both (live : List Atom)
    (fresh : ∀ atom ∈ live, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs atom "x") :
    LinearHeads RunsAsFirings.Controls.doubleEquation ∧
      eqRegion live RunsAsFirings.Controls.callDouble Bindings.empty
        RunsAsFirings.Controls.doubleEquation = true ∧
      pettaCallRegion "double" [.grounded (.int 4)] RunsAsFirings.Controls.doubleEquation = true := by
  have inside := h1_inside live fresh
  refine ⟨?_, inside, ?_⟩
  · intro lhs rhs same
    cases same
    exact ⟨"double", [.var "x"], rfl, fun arg member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .var _, by decide⟩
  · exact he_region_sub_petta live (fun value member => by
      simp only [List.mem_singleton] at member
      subst member
      rfl) (fun arg member => by
        simp only [List.mem_singleton] at member
        subst member
        exact .var _) (by decide) inside

/-- H1's program is in the fragment. -/
theorem h1_program_linear : ∀ row ∈ [RunsAsFirings.Controls.p RunsAsFirings.Controls.a,
    RunsAsFirings.Controls.doubleEquation], LinearHeads row := by
  intro row member lhs rhs same
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp [RunsAsFirings.Controls.p] at same
  · cases same
    exact ⟨"double", [.var "x"], rfl, fun arg member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .var _, by decide⟩

/-- **H1's own program over the whole run.** On `{(p a), (= (double $x) (+ $x $x))}` and the call
`(double 4)`, HE's machine runs from its entry configuration to the call with the declared word of
`EntryToQuery`, under any policy and dispatch, and the rows HE reads from the entry through the
query are exactly PeTTa's request rows: the equation at position `1`. H1's `reads_differ` found HE
reading the whole space on this program. -/
theorem h1_whole_run (dispatch : Mettapedia.Languages.MeTTa.HE.Spec.Eval.GroundedDispatch)
    (policy : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Policy) :
    EntryToQuery.Traced ServiceFootprints.rawDeclared dispatch policy
        (entry [RunsAsFirings.Controls.p RunsAsFirings.Controls.a,
          RunsAsFirings.Controls.doubleEquation] RunsAsFirings.Controls.callDouble)
        (EntryToQuery.callConfig [RunsAsFirings.Controls.p RunsAsFirings.Controls.a,
          RunsAsFirings.Controls.doubleEquation] "double" [.grounded (.int 4)])
        (EntryToQuery.entryWord ServiceFootprints.rawDeclared "double" [.grounded (.int 4)]) ∧
      (WholeRunWords.heRows [RunsAsFirings.Controls.p RunsAsFirings.Controls.a,
          RunsAsFirings.Controls.doubleEquation] "double" [.grounded (.int 4)]).flatten =
        [(RunsAsFirings.Controls.doubleEquation, 1)] := by
  have untyped : (Space.ofList [RunsAsFirings.Controls.p RunsAsFirings.Controls.a,
      RunsAsFirings.Controls.doubleEquation]).atoms.filter
        (ServiceFootprints.typeRegion (.symbol "double")) = [] := by
    decide +kernel
  have undeclared : ∀ a ∈ Atom.symbol "double" :: [Atom.grounded (.int 4)],
      ∀ row ∈ [RunsAsFirings.Controls.p RunsAsFirings.Controls.a,
        RunsAsFirings.Controls.doubleEquation], ServiceFootprints.typeRegion a row = false := by
    decide +kernel
  refine ⟨EntryToQuery.entry_traced (dispatch := dispatch) (policy := policy)
    ServiceFootprints.rawDeclared EntryToQuery.raw_answers WholeRunWords.Double.double_data untyped,
    ?_⟩
  rw [whole_run_rows_linear WholeRunWords.Double.double_data undeclared h1_program_linear]
  exact (Instance.h1_triangle [] (by simp)).2

/-- `(= (same $x $x) yes)`: a left side with a repeated variable. -/
def sameRow : Atom :=
  .expression [.symbol "=", .expression [.symbol "same", .var "x", .var "x"], .symbol "yes"]

theorem sameRow_fragment : ConsFreeHeads sameRow := by
  intro lhs rhs same
  cases same
  refine ⟨"same", [.var "x", .var "x"], rfl, fun arg member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst member
  exact .var _

/-- **Positive and negative control without linearity.** On `(= (same $x $x) yes)` HE's region
agrees with PeTTa's for every activation: the call `(same 1 1)` holds the row in both regions, the
call `(same 1 2)` in neither. -/
theorem repeated_variable (live : List Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) :
    eqRegion live (.expression [.symbol "same", .grounded (.int 1), .grounded (.int 1)])
        activation.bindings sameRow = true ∧
      eqRegion live (.expression [.symbol "same", .grounded (.int 1), .grounded (.int 2)])
        activation.bindings sameRow = false := by
  have ground : ∀ (m n : Int), ∀ value ∈ [Atom.grounded (.int m), Atom.grounded (.int n)],
      TypeSubst.typeVars value = [] := by
    intro m n value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  constructor
  · rw [regions_agree_consFree live (ground 1 1) activation.certified.satisfiable sameRow_fragment]
    decide +kernel
  · rw [regions_agree_consFree live (ground 1 2) activation.certified.satisfiable sameRow_fragment]
    decide +kernel

/-- **Negative control: the `cons` list view is outside the fragment**, and there the regions part
the other way: PeTTa's region of `(f (1 2))` holds `(= (f (cons 1 (2))) 5)`, HE's does not. -/
theorem cons_row_outside_fragment (live : List Atom) (incoming : Bindings) :
    ¬ LinearHeads GroundFragment.Controls.consRow ∧
      pettaCallRegion "f" [.expression [.grounded (.int 1), .grounded (.int 2)]]
        GroundFragment.Controls.consRow = true ∧
      eqRegion live GroundFragment.Controls.callList incoming GroundFragment.Controls.consRow =
        false := by
  refine ⟨fun fragment => ?_, (GroundFragment.Controls.cons_view_distinguishes live incoming).1,
    (GroundFragment.Controls.cons_view_distinguishes live incoming).2.1⟩
  obtain ⟨name, args, same, consFree, _⟩ := fragment _ _ rfl
  cases same
  have nested := consFree _ List.mem_cons_self
  cases nested with
  | expression _ notCons _ => exact notCons _ _ rfl

end Controls

#print axioms completes_list
#print axioms completes
#print axioms he_hit_instance
#print axioms he_region_sub_petta
#print axioms he_rows_sub_petta
#print axioms sound_list
#print axioms sound
#print axioms he_inside_of_instance
#print axioms regions_agree_linear
#print axioms footprints_coincide_linear
#print axioms he_inside_of_instance_satisfiable
#print axioms regions_agree_linear_satisfiable
#print axioms footprints_coincide_linear_at_activation
#print axioms whole_run_rows_linear
#print axioms completesConsistent
#print axioms he_region_sub_petta_consFree
#print axioms regions_agree_consFree
#print axioms footprints_coincide_consFree
#print axioms whole_run_rows_consFree
#print axioms Controls.h1_row_inside_both
#print axioms Controls.repeated_variable
#print axioms Controls.h1_whole_run
#print axioms Controls.cons_row_outside_fragment

end RegionsWithVariables

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
