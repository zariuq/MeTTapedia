import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ReadWordTriangle
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.SimpleAgreement
import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-!
# The two footprints coincide on programs with literal equation heads

`ReadWordTriangle.read_word_triangle` reduces the read-word triangle to one question per row: do
HE's region of an equation query and PeTTa's region of the call agree on that row? This module
answers it for a whole fragment.

**The fragment.** Every equation row `(= lhs rhs)` of the program has a **literal** left side: no
variables and no `(cons _ _)` list view (`SpaceSemantics.Literal`); right sides and other rows are
arbitrary. The call is `(head v₁ … vₙ)` with variable-free values, and HE's incoming bindings are
satisfiable (as every activation's are).

* `he_closed_inside`, `he_closed_outside`: on a variable-free left side, HE's region holds the row
  exactly when the left side is the query. Every fresh variant of a variable-free side is itself,
  and a surviving candidate makes the query and the pattern equal in every model of its bindings
  (`UnifyCandidateRel.solutions`).
* `petta_literal_row`: on literal arguments PeTTa's call region holds an equation of `head` exactly
  when its arguments are the values (`SpaceSemantics.matchValue_literal`).
* `regions_agree`: **on the fragment, the two regions agree on every row.**
* `footprints_coincide`: **on the fragment, HE's equation query and PeTTa's complete call request
  read the same positioned rows**; `footprints_coincide_at_activation` for every activation frame.

## Controls

* `Controls.cons_view_distinguishes` (negative): the row `(= (f (cons 1 (2))) 5)` has a `cons` list
  view in its head, outside the fragment. PeTTa's region of `(f (1 2))` holds it (its list view
  matches `(1 2)`), HE's does not, and the evaluators part: PeTTa answers `5`, HE answers
  `(f (1 2))`.
* `Controls.ground_program`: `{(p a), (= (double 4) 8), (= (double 5) 10)}` is in the fragment, and
  both footprints of `(double 4)` are the one row `(= (double 4) 8)` at position `1`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace GroundFragment

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst.typeVars
  TypeSubst.typeVarsList)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (AlphaVariantRel EquationRowResultsRel
  UnifyCandidateRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel MatchListAccRel
  equalityGroundedSemantic semanticLoopFree_empty constraints)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Literal matchValue matchValue_literal)
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings (rowSupply Row)

/-! ## Variable-free atoms on HE's side -/

/-- A literal has no variables. -/
theorem literal_closed {atom : Atom} (literal : Literal atom) : TypeSubst.typeVars atom = [] := by
  induction literal with
  | symbol => rfl
  | grounded => rfl
  | expression items _ _ ih =>
      simp only [TypeSubst.typeVars]
      exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff items).mpr ih

/-- A variable-free atom matches itself, with no bindings. -/
theorem match_refl (query : Atom) (closed : TypeSubst.typeVars query = []) :
    MatchRel equalityGroundedSemantic query query Mettapedia.Languages.MeTTa.HE.Bindings.empty := by
  induction query using Atom.rec (motive_2 := fun atoms => TypeSubst.typeVarsList atoms = [] →
      MatchListAccRel equalityGroundedSemantic atoms atoms
        Mettapedia.Languages.MeTTa.HE.Bindings.empty Mettapedia.Languages.MeTTa.HE.Bindings.empty) with
  | symbol name => exact .symSym name semanticLoopFree_empty
  | var name => simp [TypeSubst.typeVars] at closed
  | grounded value => exact .groundedLeftCustom rfl trivial ⟨rfl, rfl⟩ semanticLoopFree_empty
  | expression atoms ih =>
      simp only [TypeSubst.typeVars] at closed
      exact .expression (ih closed) semanticLoopFree_empty
  | nil => exact .nil
  | cons head tail headIH tailIH =>
      rename_i closed
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at closed
      exact .cons (headIH closed.1)
        (.mk (by simp [constraints, Mettapedia.Languages.MeTTa.HE.Bindings.empty]) .nil)
        (tailIH closed.2)

/-- Every fresh variant of a variable-free side is that side. -/
theorem variant_closed {rename : String → String} {source target : Atom}
    (renamed : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.AlphaRenameAtomRel rename source target)
    (closed : TypeSubst.typeVars source = []) : target = source :=
  (Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamed).trans
    (Mettapedia.Languages.MeTTa.HE.TypeGrounding.renameTypeVars_of_typeVars_nil rename source closed)

/-- **On a variable-free left side that is the query, HE's region holds the row**, for satisfiable
incoming bindings. -/
theorem he_closed_inside (live : List Atom) {query rhs : Atom}
    (closed : TypeSubst.typeVars query = []) {incoming : Mettapedia.Languages.MeTTa.HE.Bindings}
    (satisfiable : ∃ valuation : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation incoming) :
    eqRegion live query incoming (.expression [.symbol "=", query, rhs]) = true := by
  apply eqRegion_of_not_inert
  intro inert
  obtain ⟨pattern, body, alpha⟩ : ∃ pattern body,
      AlphaVariantRel live query incoming query rhs pattern body :=
    ⟨_, _, Mettapedia.Languages.MeTTa.HE.EquationFreshening.freshRule_alphaVariant live query query
      rhs incoming 0⟩
  have shape : pattern = query := by
    obtain ⟨_, _, renamedL, _, _⟩ := alpha
    exact variant_closed renamedL closed
  subst shape
  have merged : Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.LogicalMergeRel
      Mettapedia.Languages.MeTTa.HE.Bindings.empty incoming incoming :=
    ⟨Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _, satisfiable⟩
  have hit := EquationRowResultsRel.hit 0 pattern rhs pattern body
    Mettapedia.Languages.MeTTa.HE.Bindings.empty incoming alpha (match_refl pattern closed) merged
  cases (inert 0 _).mp hit

/-- **On a variable-free left side other than the query, HE's region leaves the row out.** -/
theorem he_closed_outside (live : List Atom) {query lhs rhs : Atom}
    (closedQuery : TypeSubst.typeVars query = []) (closedLeft : TypeSubst.typeVars lhs = [])
    (different : lhs ≠ query) {incoming : Mettapedia.Languages.MeTTa.HE.Bindings} :
    eqRegion live query incoming (.expression [.symbol "=", lhs, rhs]) = false := by
  have noCandidate : ∀ pattern body, AlphaVariantRel live query incoming lhs rhs pattern body →
      ∀ matched output, ¬ (MatchRel equalityGroundedSemantic query pattern matched ∧
        Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.LogicalMergeRel matched
          incoming output) := by
    intro pattern body alpha matched output viable
    obtain ⟨_, _, renamedL, _, _⟩ := alpha
    have shape : pattern = lhs := variant_closed renamedL closedLeft
    rw [shape] at viable
    obtain ⟨valuation, model⟩ := viable.2.2
    have equal := ((UnifyCandidateRel.solutions ⟨matched, viable.1, viable.2⟩ valuation).mp model).1
    rw [Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground valuation closedQuery,
      Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground valuation closedLeft] at equal
    exact different equal.symm
  have inert : Inert live query incoming (.expression [.symbol "=", lhs, rhs]) := by
    intro position block
    constructor
    · intro derived
      cases derived with
      | irrelevant =>
          rename_i notEquation
          exact absurd rfl (notEquation _ _)
      | miss => rfl
      | hit =>
          exact absurd ⟨‹MatchRel _ _ _ _›,
            ‹Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.LogicalMergeRel _ _ _›⟩
            (noCandidate _ _ ‹AlphaVariantRel _ _ _ _ _ _ _› _ _)
    · rintro rfl
      exact .miss position lhs rhs _ _
        (Mettapedia.Languages.MeTTa.HE.EquationFreshening.freshRule_alphaVariant live query lhs rhs
          incoming position) noCandidate
  simpa [eqRegion] using inert

/-! ## Literal arguments on PeTTa's side -/

/-- Matching literal argument patterns is equality. -/
theorem matchValues_literal : ∀ (args values : List Atom)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst), (∀ arg ∈ args, Literal arg) →
      matchValue.matchValues bindings args values = if args = values then some bindings else none
  | [], [], _, _ => by simp [matchValue.matchValues]
  | [], _ :: _, _, _ => by simp [matchValue.matchValues]
  | _ :: _, [], _, _ => by simp [matchValue.matchValues]
  | arg :: args, value :: values, bindings, literals => by
      simp only [matchValue.matchValues]
      rw [matchValue_literal (literals arg List.mem_cons_self)]
      by_cases same : arg = value
      · subst same
        rw [if_pos rfl, Option.bind_eq_bind, Option.bind_some,
          matchValues_literal args values bindings
            (fun item member => literals item (List.mem_cons_of_mem _ member))]
        simp
      · simp [same]

/-- **PeTTa's region on an equation with literal arguments**: a call of `head` with `values` holds
the row exactly when its head is `head` and its arguments are the values. -/
theorem petta_literal_row {head name : String} {args values : List Atom} {body : Atom}
    (literals : ∀ arg ∈ args, Literal arg) :
    pettaCallRegion head values
        (.expression [.symbol "=", .expression (.symbol name :: args), body]) =
      decide (name = head ∧ args = values) := by
  simp only [pettaCallRegion, LiveEquations.equationOfRow, matchValues_literal args values []
    literals]
  by_cases sameHead : name = head <;> by_cases sameArgs : args = values <;> simp_all

/-! ## The regions agree on the fragment -/

/-- **The fragment**: every equation row has a literal left side. -/
def LiteralHeads (row : Atom) : Prop :=
  ∀ lhs rhs, row = .expression [.symbol "=", lhs, rhs] → Literal lhs

/-- **On the fragment, HE's region of an equation query and PeTTa's region of the call agree on
every row.** -/
theorem regions_agree (live : List Atom) {head : String} {values : List Atom}
    (closedValues : ∀ value ∈ values, TypeSubst.typeVars value = [])
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings}
    (satisfiable : ∃ valuation : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation incoming)
    {row : Atom} (literalHeads : LiteralHeads row) :
    eqRegion live (.expression (.symbol head :: values)) incoming row =
      pettaCallRegion head values row := by
  have closedQuery : TypeSubst.typeVars (.expression (.symbol head :: values)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff values).mpr
      closedValues
  by_cases isEquation : ∃ lhs rhs, row = .expression [.symbol "=", lhs, rhs]
  · obtain ⟨lhs, rhs, rfl⟩ := isEquation
    have literal := literalHeads lhs rhs rfl
    have closedLeft := literal_closed literal
    by_cases same : lhs = .expression (.symbol head :: values)
    · subst same
      rw [he_closed_inside live closedQuery satisfiable]
      have literals : ∀ arg ∈ values, Literal arg := by
        cases literal with
        | expression items _ members =>
            exact fun arg member => members arg (List.mem_cons_of_mem _ member)
      rw [petta_literal_row literals]
      simp
    · rw [he_closed_outside live closedQuery closedLeft same]
      cases lhs with
      | expression items =>
          cases items with
          | nil => simp [pettaCallRegion, LiveEquations.equationOfRow]
          | cons first args =>
              cases first with
              | symbol name =>
                  have literals : ∀ arg ∈ args, Literal arg := by
                    cases literal with
                    | expression items _ members =>
                        exact fun arg member => members arg (List.mem_cons_of_mem _ member)
                  rw [petta_literal_row literals]
                  symm
                  apply decide_eq_false
                  rintro ⟨rfl, rfl⟩
                  exact same rfl
              | var name => simp [pettaCallRegion, LiveEquations.equationOfRow]
              | grounded value => simp [pettaCallRegion, LiveEquations.equationOfRow]
              | expression inner => simp [pettaCallRegion, LiveEquations.equationOfRow]
      | symbol name => simp [pettaCallRegion, LiveEquations.equationOfRow]
      | var name => simp [pettaCallRegion, LiveEquations.equationOfRow]
      | grounded value => simp [pettaCallRegion, LiveEquations.equationOfRow]
  · have notEquation : ∀ lhs rhs, row ≠ .expression [.symbol "=", lhs, rhs] :=
      fun lhs rhs same => isEquation ⟨lhs, rhs, same⟩
    rw [eqRegion_not_equation notEquation]
    have none : LiveEquations.equationOfRow row = none := by
      unfold LiveEquations.equationOfRow
      split
      · exact absurd rfl (notEquation _ _)
      · rfl
    exact (pettaCallRegion_not_equation none).symm

/-- **The footprints coincide on the fragment.** For a program whose equations have literal left
sides and a call with variable-free values, HE's equation query and PeTTa's complete call request
read the same positioned rows. -/
theorem footprints_coincide (atoms live : List Atom) {head : String} {values : List Atom}
    (closedValues : ∀ value ∈ values, TypeSubst.typeVars value = [])
    {incoming : Mettapedia.Languages.MeTTa.HE.Bindings}
    (satisfiable : ∃ valuation : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation incoming)
    (program : ∀ row ∈ atoms, LiteralHeads row) :
    regionRows (eqRegion live (.expression (.symbol head :: values)) incoming)
        (Space.ofList atoms).atoms =
      (completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
        (fun row => (row.atom, row.serial)) :=
  (read_word_triangle atoms live _ incoming head values).mpr fun row member =>
    regions_agree live closedValues satisfiable (program row member)

/-- The same at every activation frame of HE's machine, whose bindings are satisfiable. -/
theorem footprints_coincide_at_activation (atoms live : List Atom) {head : String}
    {values : List Atom} (closedValues : ∀ value ∈ values, TypeSubst.typeVars value = [])
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame)
    (program : ∀ row ∈ atoms, LiteralHeads row) :
    regionRows (eqRegion live (.expression (.symbol head :: values)) activation.bindings)
        (Space.ofList atoms).atoms =
      (completeCall rowSupply head values (Row.load 0 atoms)).selection.read.map
        (fun row => (row.atom, row.serial)) :=
  footprints_coincide atoms live closedValues activation.certified.satisfiable program

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

/-- `(p a)`. -/
def pa : Atom := .expression [.symbol "p", .symbol "a"]

/-- `(f (1 2))`. -/
def callList : Atom :=
  .expression [.symbol "f", .expression [.grounded (.int 1), .grounded (.int 2)]]

/-- `(= (f (cons 1 (2))) 5)`: an equation whose head uses PeTTa's list view. -/
def consRow : Atom :=
  .expression [.symbol "=",
    .expression [.symbol "f",
      .expression [.symbol "cons", .grounded (.int 1), .expression [.grounded (.int 2)]]],
    .grounded (.int 5)]

/-- The same equation as PeTTa's registry. -/
def consRegistry : SpaceSemantics.Program :=
  { equations := [⟨"f", [.expression [.symbol "cons", .grounded (.int 1),
      .expression [.grounded (.int 2)]]], .grounded (.int 5)⟩], declarations := [] }

/-- **Negative control: the `cons` list view is outside the fragment.** PeTTa's region of
`(f (1 2))` holds `(= (f (cons 1 (2))) 5)`, since its list view matches `(1 2)`; HE's region leaves
it out, its left side being another variable-free atom; and the evaluators part: PeTTa answers `5`,
HE answers `(f (1 2))`. -/
theorem cons_view_distinguishes (live : List Atom)
    (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) :
    pettaCallRegion "f" [.expression [.grounded (.int 1), .grounded (.int 2)]] consRow = true ∧
      eqRegion live callList incoming consRow = false ∧
      Streaming.values (Streaming.advance consRegistry 30
        (Streaming.enter { state := NamedSpaces.Store.new [consRow] [] } callList)) =
          [.grounded (.int 5)] ∧
      (Mettapedia.Languages.MeTTa.HE.evalAtom (Space.ofList [consRow])
        HEOnTheStep.NamedDifferences.plus callList Atom.undefinedType
          Mettapedia.Languages.MeTTa.HE.Bindings.empty 40).map Prod.fst = [callList] := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  apply he_closed_outside
  · rfl
  · rfl
  · intro same
    cases same

/-- `(= (double 5) 10)`. -/
def doubleTen : Atom :=
  .expression [.symbol "=", .expression [.symbol "double", .grounded (.int 5)], .grounded (.int 10)]

/-- A ground program: `{(p a), (= (double 4) 8), (= (double 5) 10)}`. -/
def groundAtoms : List Atom := [pa, Instance.doubleEight, doubleTen]

/-- **Positive control: a program in the fragment.** Both footprints of `(double 4)` are the one row
`(= (double 4) 8)` at position `1`; `(p a)` and `(= (double 5) 10)` are read by neither. -/
theorem ground_program (live : List Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) :
    regionRows (eqRegion live Instance.doubleFour activation.bindings)
        (Space.ofList groundAtoms).atoms =
      (completeCall rowSupply "double" [.grounded (.int 4)] (Row.load 0 groundAtoms)).selection.read.map
        (fun row => (row.atom, row.serial)) ∧
      (completeCall rowSupply "double" [.grounded (.int 4)] (Row.load 0 groundAtoms)).selection.read.map
        (fun row => (row.atom, row.serial)) = [(Instance.doubleEight, 1)] := by
  have inFragment : ∀ row ∈ groundAtoms, LiteralHeads row := by
    intro row member lhs rhs same
    simp only [groundAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [pa] at same
    · cases same
      exact Literal.constructor "double" [.grounded (.int 4)] (by decide)
        (fun item member => by
          simp only [List.mem_singleton] at member
          subst member
          exact Literal.grounded _)
    · cases same
      exact Literal.constructor "double" [.grounded (.int 5)] (by decide)
        (fun item member => by
          simp only [List.mem_singleton] at member
          subst member
          exact Literal.grounded _)
  refine ⟨footprints_coincide_at_activation groundAtoms live
    (fun value member => by
      simp only [List.mem_singleton] at member
      subst member
      rfl) activation inFragment, ?_⟩
  decide +kernel

end Controls

#print axioms literal_closed
#print axioms match_refl
#print axioms he_closed_inside
#print axioms he_closed_outside
#print axioms matchValues_literal
#print axioms petta_literal_row
#print axioms regions_agree
#print axioms footprints_coincide
#print axioms footprints_coincide_at_activation
#print axioms Controls.cons_view_distinguishes
#print axioms Controls.ground_program

end GroundFragment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
