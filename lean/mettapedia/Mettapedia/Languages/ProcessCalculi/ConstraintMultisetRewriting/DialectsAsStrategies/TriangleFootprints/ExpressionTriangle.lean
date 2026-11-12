import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ReadWordTriangle

/-!
# The triangle for one expression

**This module supersedes `HEOnTheStep.triangle_reached_store` and `HEOnTheStep.triangle_double`.**
Those take an arbitrary HE configuration whose space holds the program. Nothing ties it to the
expression whose PeTTa translation they run, so their two halves are independent facts
(`Untied.untied_is_vacuous`). Here the HE side starts from HE's own entry configuration of the
expression (`entry`, through `RecursiveMachine.Contextual.load`: the expression as fresh pending
work with expected type `%Undefined%`, over the program's space), and the PeTTa side runs the
translation of that same expression (`Translation.translateHE`).

## Results

* `expression_triangle_reached_store` (H1's encoding, corrected): for a program loaded as `atoms` and
  an expression whose translated PeTTa run requests only reads, every run of HE on the step from a
  store representing HE's entry configuration of the expression reaches the world that PeTTa's run
  of the translation reaches.
* `expression_triangle_rows` (honest footprints): the same row for row. The rows reached on HE's
  footprinted step are the positioned rows of PeTTa's reached store.
* `expression_firings_read`: along every run of HE's footprinted step from the entry configuration,
  every firing reads exactly the rows of its region in the loaded program. Its region is the
  footprint of a move from a configuration that HE reaches from the entry, or empty.

## Controls

* `Untied.untied_is_vacuous` (negative): H1's `triangle_double` applies verbatim to an HE
  configuration that evaluates `(remove-atom &self (p a))`, while PeTTa's evaluation of that removal
  takes the row `(p a)` and changes the store. Untied, the statement certifies agreement where there
  is none. The tied statement does not apply there: that evaluation's request is not a read.
* `Tied.double_expression_triangle` (positive instance): `(double 4)` on
  `{(p a), (= (double 4) 8)}`. The translation is the identity, PeTTa's run only reads, and the
  reached stores agree. Every equation query of `(double 4)` that HE's run makes, under any scope
  and activation, reads exactly the one row `(= (double 4) 8)`, which is the row PeTTa's run reads.

Not shown here: that HE's run from the entry configuration reaches that equation query. The run
first passes the type-directed entry of `(double 4)`, whose cast lookup and argument admission are
parameters of the machine. The answer bag of HE's machine is not shown either.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
open Mettapedia.Languages.MeTTa.Translation (translateHE)
open HEOnTheStep (heMachine HEConfig toConfig Config Store StoreStep Represents worldsOf
  he_world_reached read_only_reaches_loaded he_machine_keeps_world Cell)
open MeTTaCalculus.OccurrenceCommits (labels)

/-! ## The tie -/

/-- **HE's entry configuration of an expression** over a loaded program: the expression as fresh
pending work, expected type `%Undefined%`, empty activation. -/
def entry (atoms : List Atom) (expression : Atom) : HEConfig :=
  Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.load (Space.ofList atoms) expression
    Atom.undefinedType

/-- PeTTa's request word for the translation of an expression, against a loaded program. -/
def pettaWord (registry : SpaceSemantics.Program) (atoms : List Atom) (expression : Atom)
    (fuel : ℕ) : List (Interface.OrderedStore.Publication Atom Row) :=
  requests rowSupply registry fuel
    (Streaming.enter { state := NamedSpaces.Store.new atoms [] } (translateHE expression 0).1)
    (Row.load 0 atoms)

/-- The store PeTTa's run of the translation of an expression reaches. -/
def pettaReached (registry : SpaceSemantics.Program) (atoms : List Atom) (expression : Atom)
    (fuel : ℕ) : List Atom :=
  (Streaming.advance registry fuel
    (Streaming.enter { state := NamedSpaces.Store.new atoms [] } (translateHE expression 0).1)).world.state.core

variable {dispatch : Mettapedia.Languages.MeTTa.HE.Spec.Eval.GroundedDispatch} {lookup : CastLookup}
  {policy : Policy}

/-- **The triangle on the store reached, for one expression** (H1's encoding, corrected). When the
PeTTa run of the expression's translation requests only reads, every run of HE on the step from a
store representing HE's entry configuration of that expression reaches the world PeTTa's run
reaches. -/
theorem expression_triangle_reached_store (registry : SpaceSemantics.Program) (atoms : List Atom)
    (expression : Atom) (fuel : ℕ)
    (readOnly : ∀ r ∈ pettaWord registry atoms expression fuel,
      r.selection.taken = [] ∧ r.selection.made = [])
    {S : Store Space Control Continuation Result}
    (represented : Represents S (toConfig (entry atoms expression))) :
    ∀ S', Relation.ReflTransGen (StoreStep (heMachine dispatch lookup policy)) S S' →
      worldsOf (labels Prod.fst S'.present) =
        {Space.ofList (pettaReached registry atoms expression fuel)} := by
  intro S' path
  rw [he_world_reached represented path]
  unfold pettaReached
  rw [read_only_reaches_loaded registry atoms _ fuel readOnly]
  rfl

/-- **The triangle on the rows reached, for one expression** (honest footprints). The rows reached
on HE's footprinted step from the entry configuration are the positioned rows of PeTTa's reached
store. -/
theorem expression_triangle_rows (registry : SpaceSemantics.Program) (atoms : List Atom)
    (expression : Atom) (fuel : ℕ)
    (readOnly : ∀ r ∈ pettaWord registry atoms expression fuel,
      r.selection.taken = [] ∧ r.selection.made = [])
    {S : Store (Atom × ℕ) Control Continuation Result}
    (represented : RowRepresents Space.atoms S (toConfig (entry atoms expression))) :
    ∀ S', Relation.ReflTransGen
        (RowStep (heMachine dispatch lookup policy) Space.atoms (heFoot policy)) S S' →
      rowsOf (labels Prod.fst S'.present) =
        ((pettaReached registry atoms expression fuel).zipIdx : Multiset (Atom × ℕ)) := by
  intro S' path
  obtain ⟨x', run, here⟩ := row_store_path_to_machine he_worldLocal represented path
  rw [here.2, rowsOf_rowEncode, he_machine_keeps_world run]
  unfold pettaReached
  rw [read_only_reaches_loaded registry atoms _ fuel readOnly]
  rfl

/-- **What HE's run of an expression reads.** Along every run of HE's footprinted step from the
entry configuration, every firing reads exactly the rows of its region in the loaded program; its
region is the footprint of a move from a configuration HE reaches from the entry, or empty. -/
theorem expression_firings_read {atoms : List Atom} {expression : Atom}
    {S S' S'' : Store (Atom × ℕ) Control Continuation Result}
    (represented : RowRepresents Space.atoms S (toConfig (entry atoms expression)))
    (path : Relation.ReflTransGen
      (RowStep (heMachine dispatch lookup policy) Space.atoms (heFoot policy)) S S')
    (step : RowStep (heMachine dispatch lookup policy) Space.atoms (heFoot policy) S' S'') :
    ∃ (x' : Config Space Control Continuation Result)
      (rule : RuleInstance (RowCell Atom Control Continuation Result)) (ρ : Atom → Bool),
      Relation.ReflTransGen (heMachine dispatch lookup policy).Step
          (toConfig (entry atoms expression)) x' ∧
        rule.read = (regionRows ρ atoms).map Cell.world ∧
        ((∃ c', ρ = heRegion policy x'.control c') ∨ ρ = fun _ => false) := by
  obtain ⟨x', run, here⟩ := row_store_path_to_machine he_worldLocal represented path
  obtain ⟨rule, ρ, _, reads, region⟩ := row_firing_region here step
  have world : x'.world = Space.ofList atoms := he_machine_keeps_world run
  refine ⟨x', rule, ρ, run, ?_, ?_⟩
  · rw [reads, world]
    rfl
  · rcases region with ⟨_, c', _, rfl⟩ | rfl
    · exact Or.inl ⟨c', rfl⟩
    · exact Or.inr rfl

/-! ## Negative control: untied, the statement is vacuous -/

namespace Untied

open RunsAsFirings.Controls (p a doubling doubleEquation callDouble shape)

/-- `(remove-atom &self (p a))`. -/
def removePa : Atom := .expression [.symbol "remove-atom", .symbol "&self", p a]

/-- **Negative control: untied, the triangle certifies agreement where there is none.** H1's
`triangle_double` applies verbatim to the HE configuration that evaluates
`(remove-atom &self (p a))`, since its space holds H1's program `{(p a), (= (double $x) (+ $x $x))}`;
but PeTTa's evaluation of that removal takes the row `(p a)` and leaves the store
`{(= (double $x) (+ $x $x))}`. The tied statement (`expression_triangle_reached_store`) does not
apply there: its hypothesis fails, as that evaluation's request takes a row. -/
theorem untied_is_vacuous {S : Store Space Control Continuation Result}
    (represented : Represents S (toConfig (entry [p a, doubleEquation] removePa))) :
    ((∀ S', Relation.ReflTransGen (StoreStep (heMachine dispatch lookup policy)) S S' →
        worldsOf (labels Prod.fst S'.present) = {Space.ofList [p a, doubleEquation]}) ∧
      (Streaming.advance doubling 30
        (Streaming.enter { state := NamedSpaces.Store.new [p a, doubleEquation] [] }
          (translateHE callDouble 0).1)).world.state.core = [p a, doubleEquation]) ∧
      (pettaWord doubling [p a, doubleEquation] removePa 30).map shape =
        [([⟨0, .self, p a⟩], [], [])] ∧
      pettaReached doubling [p a, doubleEquation] removePa 30 = [doubleEquation] ∧
      ¬ ∀ r ∈ pettaWord doubling [p a, doubleEquation] removePa 30,
        r.selection.taken = [] ∧ r.selection.made = [] := by
  have translated : translateHE removePa 0 = (removePa, 0) := rfl
  have word : (pettaWord doubling [p a, doubleEquation] removePa 30).map shape =
      [([⟨0, .self, p a⟩], [], [])] := by
    unfold pettaWord
    rw [translated]
    decide +kernel
  have reached : pettaReached doubling [p a, doubleEquation] removePa 30 = [doubleEquation] := by
    unfold pettaReached
    rw [translated]
    decide +kernel
  refine ⟨HEOnTheStep.triangle_double represented rfl, word, reached, ?_⟩
  intro readOnly
  obtain ⟨r, member, shaped⟩ : ∃ r ∈ pettaWord doubling [p a, doubleEquation] removePa 30,
      shape r = ([⟨0, .self, p a⟩], [], []) := by
    have here : ([⟨0, .self, p a⟩], [], []) ∈
        (pettaWord doubling [p a, doubleEquation] removePa 30).map shape := by
      rw [word]
      exact List.mem_singleton_self _
    obtain ⟨r, member, same⟩ := List.mem_map.mp here
    exact ⟨r, member, same⟩
  have taken := (readOnly r member).1
  simp only [shape, Prod.mk.injEq] at shaped
  rw [taken] at shaped
  cases shaped.1

end Untied

/-! ## Positive instance: `(double 4)` -/

namespace Tied

open Instance (doubleFour eight doubleEight program registry doubleFour_matches he_pa_outside)
open RunsAsFirings.Controls (shape)

/-- `(= (double 4) 8)` has no variables: it is its own fresh variant under every incoming binding
state. -/
theorem doubleEight_alpha (live : List Atom) (incoming : Mettapedia.Languages.MeTTa.HE.Bindings) :
    Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.AlphaVariantRel live doubleFour incoming
      doubleFour eight doubleFour eight := by
  refine ⟨id, Function.injective_id,
    .expression (.cons (.symbol "double") (.cons (.grounded (.int 4)) .nil)),
    .grounded (.int 8), ?_⟩
  intro name occurs
  rcases occurs with left | right
  · have used := Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_mem_typeVars left
    simp [doubleFour, Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVarsList] at used
  · cases right

/-- **For every scope and activation, `(= (double 4) 8)` is inside the region of HE's query
`(double 4)`.** -/
theorem he_inside_any (live : List Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) :
    eqRegion live doubleFour activation.bindings doubleEight = true := by
  apply eqRegion_of_not_inert
  intro inert
  have merged : Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.LogicalMergeRel
      Mettapedia.Languages.MeTTa.HE.Bindings.empty activation.bindings activation.bindings :=
    ⟨Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement.refl _, activation.certified.satisfiable⟩
  have hit : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.EquationRowResultsRel live doubleFour
      activation.bindings 1 doubleEight [⟨1, doubleFour, eight, doubleFour, eight, activation.bindings⟩] :=
    .hit 1 doubleFour eight doubleFour eight Mettapedia.Languages.MeTTa.HE.Bindings.empty
      activation.bindings (doubleEight_alpha live activation.bindings) doubleFour_matches merged
  cases (inert 1 _).mp hit

/-- The region rows of HE's query `(double 4)` in the program, for every scope and activation. -/
theorem region_rows_any (live : List Atom)
    (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame) :
    regionRows (eqRegion live doubleFour activation.bindings) program = [(doubleEight, 1)] := by
  simp [regionRows, program, he_inside_any, he_pa_outside]

/-- **The tied triangle on `(double 4)`.** The translation is the identity; PeTTa's run of it is
one read of the row `(= (double 4) 8)`; every run of HE on the step from the entry configuration of
`(double 4)` reaches the world PeTTa's run reaches; and every equation query of `(double 4)` that
HE's run makes, under any scope and activation, reads exactly that same row. -/
theorem double_expression_triangle :
    translateHE doubleFour 0 = (doubleFour, 0) ∧
      (pettaWord registry program doubleFour 30).map shape = [([], [⟨1, .self, doubleEight⟩], [])] ∧
      (∀ {S : Store Space Control Continuation Result},
        Represents S (toConfig (entry program doubleFour)) →
        ∀ S', Relation.ReflTransGen (StoreStep (heMachine dispatch lookup policy)) S S' →
          worldsOf (labels Prod.fst S'.present) =
            {Space.ofList (pettaReached registry program doubleFour 30)}) ∧
      (∀ (live : List Atom) (activation : Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Frame),
        regionRows (eqRegion live doubleFour activation.bindings) program = [(doubleEight, 1)]) := by
  have translated : translateHE doubleFour 0 = (doubleFour, 0) := rfl
  have word : (pettaWord registry program doubleFour 30).map shape =
      [([], [⟨1, .self, doubleEight⟩], [])] := by
    unfold pettaWord
    rw [translated]
    decide +kernel
  have readOnly : ∀ r ∈ pettaWord registry program doubleFour 30,
      r.selection.taken = [] ∧ r.selection.made = [] := by
    intro r member
    have shaped : shape r ∈ [([], [⟨1, .self, doubleEight⟩], [])] := by
      rw [← word]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    simp only [List.mem_singleton, shape, Prod.mk.injEq] at shaped
    exact ⟨shaped.1, shaped.2.2⟩
  refine ⟨translated, word, ?_, region_rows_any⟩
  intro S represented
  exact expression_triangle_reached_store registry program doubleFour 30 readOnly represented

end Tied

#print axioms expression_triangle_reached_store
#print axioms expression_triangle_rows
#print axioms expression_firings_read
#print axioms Untied.untied_is_vacuous
#print axioms Tied.he_inside_any
#print axioms Tied.region_rows_any
#print axioms Tied.double_expression_triangle

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
