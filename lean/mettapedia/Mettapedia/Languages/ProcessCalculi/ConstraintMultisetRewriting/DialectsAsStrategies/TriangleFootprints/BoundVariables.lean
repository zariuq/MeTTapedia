import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EveryRun

/-!
# Bodies that use their pattern variables: HE and PeTTa agree on every complete run

`AnswerBags` and `EveryRun` compared HE and PeTTa on equations whose bodies are closed. Here a body
may use the variables of its left side, repeatedly: `(= (twice $x) (pair $x $x))`.

**The two dialects substitute differently, and agree.**

* **HE** reads the body under the frame its unifier reached *before* evaluating it
  (`LocalStepWith.equationsCons`, `Completed.EquationBodiesRel.cons`): it evaluates the substituted
  instance. `work_read` shows that this read is PeTTa's instance: the readout certificate of the
  unifier's frame (`ReadoutCertificate.forced_read`) fixes every model of the work's bindings, and
  every such model instantiates the fresh pattern to the call
  (`EquationQueryOccurrenceRel.solutions`), so it agrees with PeTTa's matching on the left side's
  variables (`RegionsWithVariables.sound_list`), hence on the body's.
* **PeTTa** runs the body renamed for its use under the matching bindings renamed for that use
  (`Unifying.renamedClauses`), and resolves each variable when it evaluates it
  (`Unifying.Transition.value_variable`); bound values are not evaluated again. `Presents` says
  what such an open body stands for, and `PeTTaOpen` evaluates every open presentation of a term.

**The fragment** (`BoundRow`, `SettlesV`): rows of symbol-headed, `cons`-free equations whose body
uses only variables of its left side and is flat (an item, or a symbol applied to items; an item is
a symbol, a grounded value or a variable). A term settles (`SettlesV`) when it is a data atom other
than `NotReducible`, a constructor call, or an ordinary call with a nonempty region whose bodies
*after substitution* all settle. Like `AnswerBags.Settles`, it is a condition on the program: it
mentions rows, patterns, PeTTa's matching and bodies, never an answer or a run.

## Results

* `settlesV_agree`: for every settling term, one answer list that HE's machine returns and PeTTa's
  streaming machine delivers, for every open presentation.
* `answersV_agree`: HE's complete run publishes the values of PeTTa's run, in order.
* `settlesV_determined`, `every_complete_run_v`, `answer_bags_every_run_v`: **every** complete run
  of HE's machine from the entry publishes exactly the values PeTTa's streaming run yields from
  some fuel on; a complete run exists; so the bags agree.
* `settles_settlesV`: the extension is conservative: every term that settles in `AnswerBags`'s
  sense on such a program settles here.

## Controls

* `Controls.twice_every_run`: `(twice a)` on `{(= (twice $x) (pair $x $x))}`: every complete HE run
  and PeTTa's run give `(pair a a)`.
* `Controls.swap_every_run`, `Controls.wrap_every_run`, `Controls.both_every_run`: two variables
  in swapped order; a body that calls a defined function on its variable; two matching rows.
* `Controls.free_not_bound`: `(= (fresh) $y)` is outside `BoundRow`, the condition is not vacuous.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace BoundVariables

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel
  EquationWork AlphaVariantRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (applyTypeValuation renameTypeVars
  TypeBindingSatisfied)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun

/-! ## Valuations -/

theorem applySubst_eq_valuation (σ : Subst) : ∀ t : Atom,
    applySubst σ t = applyTypeValuation (RegionsWithVariables.asValuation σ) t
  | .var _ => by simp [applySubst, applyTypeValuation, RegionsWithVariables.asValuation]
  | .symbol _ => by simp [applySubst, applyTypeValuation]
  | .grounded _ => by simp [applySubst, applyTypeValuation]
  | .expression items => by
      simp only [applySubst, applyTypeValuation, Atom.expression.injEq]
      exact list items
where
  list : ∀ items : List Atom, applySubst.applySubstList σ items =
      items.map (applyTypeValuation (RegionsWithVariables.asValuation σ))
    | [] => rfl
    | first :: rest => by
        simp only [applySubst.applySubstList, List.map_cons, applySubst_eq_valuation σ first,
          list rest]

/-- Two valuations that instantiate a term to the same atom agree on its variables. -/
theorem agree_of_same (v w : String → Atom) : ∀ (t : Atom),
    applyTypeValuation v t = applyTypeValuation w t → ∀ x ∈ TypeSubst.typeVars t, v x = w x
  | .var name, same, x, member => by
      simp only [TypeSubst.typeVars, List.mem_singleton] at member
      subst member
      simpa [applyTypeValuation] using same
  | .symbol _, _, x, member => by simp [TypeSubst.typeVars] at member
  | .grounded _, _, x, member => by simp [TypeSubst.typeVars] at member
  | .expression items, same, x, member => by
      simp only [applyTypeValuation, Atom.expression.injEq] at same
      simp only [TypeSubst.typeVars] at member
      exact list items same x member
where
  list : ∀ (items : List Atom), items.map (applyTypeValuation v) = items.map (applyTypeValuation w) →
      ∀ x ∈ TypeSubst.typeVarsList items, v x = w x
    | [], _, x, member => by simp [TypeSubst.typeVarsList] at member
    | first :: rest, same, x, member => by
        simp only [List.map_cons, List.cons.injEq] at same
        simp only [TypeSubst.typeVarsList, List.mem_append] at member
        rcases member with inFirst | inRest
        · exact agree_of_same v w first same.1 x inFirst
        · exact list rest same.2 x inRest

/-- An atomic literal: a symbol or a grounded value. -/
inductive Lit : Atom → Prop
  | symbol (name : String) : Lit (.symbol name)
  | grounded (value : GroundedValue) : Lit (.grounded value)

theorem lit_of_data {a : Atom} (data : DataAtom a) : Lit a := by
  cases data with
  | symbol _ _ => exact .symbol _
  | grounded value => exact .grounded value

/-- A valuation that instantiates a term to a literal maps each of its variables to that literal. -/
theorem var_of_lit {v : String → Atom} {t d : Atom} (instantiated : applyTypeValuation v t = d)
    (literal : Lit d) : ∀ x ∈ TypeSubst.typeVars t, v x = d := by
  intro x member
  cases t with
  | var name =>
      simp only [TypeSubst.typeVars, List.mem_singleton] at member
      subst member
      simpa [applyTypeValuation] using instantiated
  | symbol _ => simp [TypeSubst.typeVars] at member
  | grounded _ => simp [TypeSubst.typeVars] at member
  | expression items =>
      simp only [applyTypeValuation] at instantiated
      subst instantiated
      cases literal

theorem vars_of_lits {v : String → Atom} : ∀ {ps ds : List Atom}, ps.map (applyTypeValuation v) = ds →
    (∀ d ∈ ds, DataAtom d) → ∀ x ∈ TypeSubst.typeVarsList ps, DataAtom (v x)
  | [], _, _, _, x, member => by simp [TypeSubst.typeVarsList] at member
  | p :: ps, ds, same, data, x, member => by
      cases ds with
      | nil => simp at same
      | cons d ds =>
          simp only [List.map_cons, List.cons.injEq] at same
          simp only [TypeSubst.typeVarsList, List.mem_append] at member
          rcases member with inFirst | inRest
          · have here := data d List.mem_cons_self
            rw [var_of_lit same.1 (lit_of_data here) x inFirst]
            exact here
          · exact vars_of_lits same.2 (fun e m => data e (List.mem_cons_of_mem _ m)) x inRest

/-- A contextual value whose atom is a data atom is that atom's plain value. -/
theorem value_of_data {value : Entry.Value} {d : Atom} (data : DataAtom d)
    (erased : value.erase = d) : value = Entry.Value.ofAtom d := by
  cases data with
  | symbol _ _ =>
      cases value <;> simp_all [Entry.Value.erase, Entry.Value.ofAtom]
  | grounded _ =>
      cases value <;> simp_all [Entry.Value.erase, Entry.Value.ofAtom]

/-- **Substituting plain values into a plain value keeps it plain**, under both rebuilding
policies: every expression node stays active. -/
theorem substitute_plain (rebuilding : Entry.RebuildPolicy) (env : String → Entry.Value)
    (θ : String → Atom) : ∀ t : Atom, (∀ x ∈ TypeSubst.typeVars t, env x = Entry.Value.ofAtom (θ x)) →
      Entry.Value.substitute rebuilding env (Entry.Value.ofAtom t) =
        Entry.Value.ofAtom (applyTypeValuation θ t)
  | .var name, plain => by
      simpa [Entry.Value.ofAtom, Entry.Value.substitute, applyTypeValuation] using
        plain name (by simp [TypeSubst.typeVars])
  | .symbol _, _ => by simp [Entry.Value.ofAtom, Entry.Value.substitute, applyTypeValuation]
  | .grounded _, _ => by simp [Entry.Value.ofAtom, Entry.Value.substitute, applyTypeValuation]
  | .expression items, plain => by
      have children := list items (by simpa [TypeSubst.typeVars] using plain)
      have status : ∀ before after : Atom,
          Entry.Value.rebuildStatus rebuilding .active before after = .active := by
        intro before after
        cases rebuilding <;> simp [Entry.Value.rebuildStatus]
      simp only [Entry.Value.ofAtom, Entry.Value.substitute, applyTypeValuation, List.map_map]
      rw [status]
      congr 1
      simpa [List.map_map, Function.comp_def] using children
where
  list : ∀ items : List Atom, (∀ x ∈ TypeSubst.typeVarsList items, env x = Entry.Value.ofAtom (θ x)) →
      (items.map Entry.Value.ofAtom).map (Entry.Value.substitute rebuilding env) =
        (items.map (applyTypeValuation θ)).map Entry.Value.ofAtom
    | [], _ => rfl
    | first :: rest, plain => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨substitute_plain rebuilding env θ first fun x member =>
            plain x (by simp [TypeSubst.typeVarsList, member]),
          list rest fun x member => plain x (by simp [TypeSubst.typeVarsList, member])⟩

/-! ## The program condition -/

/-- An item of a flat body: a symbol, a grounded value or a variable. -/
inductive FlatItem : Atom → Prop
  | symbol (name : String) : FlatItem (.symbol name)
  | grounded (value : GroundedValue) : FlatItem (.grounded value)
  | var (name : String) : FlatItem (.var name)

/-- PeTTa's source control heads: a call of one of them may be a special form. -/
def controlHead (g : String) : Bool :=
  g ∈ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match", "once"]

/-- **A flat body**: an item, or a symbol that heads no special form applied to items. Repeated
variables are allowed. -/
inductive FlatBody : Atom → Prop
  | item {b : Atom} : FlatItem b → FlatBody b
  | call (g : String) (items : List Atom) : controlHead g = false → (∀ u ∈ items, FlatItem u) →
      FlatBody (.expression (.symbol g :: items))

/-- **An equation row whose body uses only variables of its left side, in a flat body.** -/
def BoundRow (row : Atom) : Prop :=
  ∀ lhs rhs, row = .expression [.symbol "=", lhs, rhs] →
    (∀ x ∈ TypeSubst.typeVars rhs, x ∈ TypeSubst.typeVars lhs) ∧ FlatBody rhs

/-- The program condition: symbol-headed, `cons`-free equations with bound, flat bodies. -/
def BoundProgram (atoms : List Atom) : Prop :=
  ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row ∧ BoundRow row

theorem bound_consFree {atoms : List Atom} (program : BoundProgram atoms) :
    ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row :=
  fun row member => (program row member).1

/-- A row whose body uses only variables of its left side, whatever the body's shape. -/
def VarsBound (row : Atom) : Prop :=
  ∀ lhs rhs, row = .expression [.symbol "=", lhs, rhs] →
    ∀ x ∈ TypeSubst.typeVars rhs, x ∈ TypeSubst.typeVars lhs

/-- **The condition HE's side uses**: symbol-headed, `cons`-free equations whose bodies use only
their left side's variables. -/
def ScopedProgram (atoms : List Atom) : Prop :=
  ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row ∧ VarsBound row

theorem BoundProgram.scoped {atoms : List Atom} (program : BoundProgram atoms) :
    ScopedProgram atoms :=
  fun row member => ⟨(program row member).1,
    fun lhs rhs same => ((program row member).2 lhs rhs same).1⟩

theorem scoped_consFree {atoms : List Atom} (program : ScopedProgram atoms) :
    ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row :=
  fun row member => (program row member).1

theorem sourceControlForm_of_head {g : String} (notControl : controlHead g = false)
    (items : List Atom) : Unifying.sourceControlForm (.expression (.symbol g :: items)) = false := by
  unfold Unifying.sourceControlForm
  split <;> simp_all [controlHead]

/-! ## Instances of bodies -/

/-- The instance of an equation's body for a call's values: the body under PeTTa's matching of the
argument patterns against the values; `none` when they do not match. -/
def instanceOf (values : List Atom) (e : SpaceSemantics.Equation) : Option Atom :=
  (SpaceSemantics.matchValue.matchValues [] e.arguments values).map fun bound => applySubst bound e.body

/-- **The bodies of a call's region after substitution**, in row order. -/
def regionInstances (atoms : List Atom) (f : String) (args : List Atom) : List Atom :=
  (atoms.filter (pettaCallRegion f args)).filterMap fun row =>
    (LiveEquations.equationOfRow row).bind (instanceOf args)

/-- The instances of the candidate equations whose patterns match the values, in order. -/
def matchingInstances (values : List Atom) (chosen : List SpaceSemantics.Equation) : List Atom :=
  chosen.filterMap (instanceOf values)

theorem regionInstances_eq (atoms : List Atom) (f : String) (args : List Atom) :
    regionInstances atoms f args = matchingInstances args
      (Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f args.length) := by
  induction atoms with
  | nil => rfl
  | cons row rows ih =>
      simp only [regionInstances, matchingInstances, Unifying.candidates] at ih ⊢
      cases found : LiveEquations.equationOfRow row with
      | none =>
          have outside : pettaCallRegion f args row = false := pettaCallRegion_not_equation found
          simp [outside, found, ih]
      | some e =>
          cases matched : SpaceSemantics.matchValue.matchValues [] e.arguments args with
          | none =>
              by_cases selected : (e.head == f && e.arguments.length == args.length) = true
              · simp [pettaCallRegion, found, matched, selected, ih, instanceOf]
              · simp [pettaCallRegion, found, matched, selected, ih]
          | some bound =>
              by_cases selected : (e.head == f && e.arguments.length == args.length) = true
              · simp [pettaCallRegion, found, matched, selected, ih, instanceOf]
              · simp [pettaCallRegion, found, matched, selected, ih]

/-- The sides of an equation row. -/
def sides : Atom → Option (Atom × Atom)
  | .expression [.symbol "=", lhs, rhs] => some (lhs, rhs)
  | _ => none

/-- The sides of the rows in a call's region, in row order. -/
def regionSides (atoms : List Atom) (f : String) (args : List Atom) : List (Atom × Atom) :=
  (atoms.filter (pettaCallRegion f args)).filterMap sides

/-- The instance a pair of sides gives for a call's values. -/
def sidesInstance (args : List Atom) (lr : Atom × Atom) : Option Atom :=
  (LiveEquations.equationOfRow (.expression [.symbol "=", lr.1, lr.2])).bind (instanceOf args)

theorem regionInstances_sides (atoms : List Atom) (f : String) (args : List Atom) :
    regionInstances atoms f args = (regionSides atoms f args).filterMap (sidesInstance args) := by
  induction atoms with
  | nil => rfl
  | cons row rows ih =>
      simp only [regionInstances, regionSides] at ih ⊢
      by_cases inside : pettaCallRegion f args row = true
      · cases found : LiveEquations.equationOfRow row with
        | none =>
            rw [pettaCallRegion_not_equation found] at inside
            cases inside
        | some e =>
            have shape := LiveEquations.equationOfRow_eq_some found
            subst shape
            have readBack : sidesInstance args
                (.expression (.symbol e.head :: e.arguments), e.body) = instanceOf args e := by
              have equation : LiveEquations.equationOfRow
                  (.expression [.symbol "=", .expression (.symbol e.head :: e.arguments), e.body]) =
                    some e := LiveEquations.equationOfRow_toAtom e
              simp only [sidesInstance, equation, Option.bind_some]
            have sidesRow : sides e.toAtom =
                some (.expression (.symbol e.head :: e.arguments), e.body) := rfl
            simp only [List.filter_cons, inside, if_true, List.filterMap_cons, found,
              Option.bind_some, sidesRow, readBack]
            cases instanceOf args e <;> simp [ih]
      · simp [inside, ih]

theorem regionSides_cons (row : Atom) (rows : List Atom) (f : String) (args : List Atom) :
    regionSides (row :: rows) f args =
      (if pettaCallRegion f args row = true then (sides row).toList else []) ++
        regionSides rows f args := by
  unfold regionSides
  by_cases inside : pettaCallRegion f args row = true
  · cases found : sides row <;> simp [inside, found]
  · simp [inside]

/-! ## Terms that settle after substitution -/

/-- **The fragment's terms, with termination and coverage stated on the program, bodies read after
substitution.** A term settles when it is a data atom other than `NotReducible`; a call of a head
with no equation (a constructor); or an ordinary call with at least one row in its region whose
bodies after substitution all settle. -/
inductive SettlesV (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → Prop
  | data {a : Atom} : DataAtom a → a ≠ Atom.notReducible → SettlesV dispatch atoms a
  | constructor {f : String} {args : List Atom} : Ordinary dispatch atoms f args →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      SettlesV dispatch atoms (.expression (.symbol f :: args))
  | call {f : String} {args : List Atom} : Ordinary dispatch atoms f args →
      regionInstances atoms f args ≠ [] →
      (∀ b ∈ regionInstances atoms f args, SettlesV dispatch atoms b) →
      SettlesV dispatch atoms (.expression (.symbol f :: args))

theorem settlesV_facts {dispatch : GroundedDispatch} {atoms : List Atom} {t : Atom}
    (settles : SettlesV dispatch atoms t) : BodyFacts t := by
  cases settles with
  | data data notRefused => exact settles_facts (Settles.data (dispatch := dispatch) (atoms := atoms)
      data notRefused)
  | constructor ordinary _ => exact call_facts ordinary
  | call ordinary _ _ => exact call_facts ordinary

/-! ## HE reads each body as its instance -/

/-- **HE reads a work's body as PeTTa's instance.** For a work of the frontier of a call of data
atoms, on a program of bound rows: the row's sides give an instance, and under every frame whose
bindings are the work's, HE's read of the fresh body is that instance, as a plain value. -/
theorem work_read (policy : Policy) {atoms live : List Atom} {f : String} {args : List Atom}
    {incoming : Bindings} (argsData : ∀ a ∈ args, DataAtom a) (program : ScopedProgram atoms)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works)
    {w : EquationWork} (member : w ∈ works) :
    ∃ i, sidesInstance args (w.left, w.right) = some i ∧
      ∀ output : Frame, output.bindings = w.bindings →
        output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i := by
  obtain ⟨matched, occurrence⟩ := frontier.occurrence member
  have stored : Atom.expression [.symbol "=", w.left, w.right] ∈ atoms :=
    List.mem_of_getElem? occurrence.stored
  obtain ⟨consFree, boundRow⟩ := program _ stored
  obtain ⟨h, ps, leftShape, psFree⟩ := consFree w.left w.right rfl
  have varsBound := boundRow w.left w.right rfl
  obtain ⟨rename, _, renamedLeft, renamedRight, _⟩ := occurrence.selected.1
  have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  have bodyEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedRight
  have groundQuery : TypeSubst.typeVars (.expression (.symbol f :: args)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff args).mpr
      fun a m => HERuns.ground_typeVars (answerable_of_data (argsData a m))
  -- every model of the work's bindings instantiates the left side to the call
  have instantiates : ∀ v, TypeBindingSatisfied v w.bindings →
      applyTypeValuation (v ∘ rename) w.left = .expression (.symbol f :: args) := by
    intro v model
    have equal := ((occurrence.solutions v).mp model).1
    rw [patternEq,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground v groundQuery] at equal
    exact equal.symm
  obtain ⟨model, satisfiedWork⟩ := occurrence.result.1.2
  have first := instantiates model satisfiedWork
  rw [leftShape] at first
  simp only [applyTypeValuation, List.map_cons, Atom.expression.injEq, List.cons.injEq,
    Atom.symbol.injEq] at first
  obtain ⟨sameHead, sameArgs⟩ := first
  -- PeTTa's matching of the patterns against the call's values
  obtain ⟨bound, matchedBound, _⟩ := RegionsWithVariables.completesConsistent_list (model ∘ rename) ps
    (fun p m => RegionsWithVariables.completesConsistent _ (psFree p m)) []
    (RegionsWithVariables.consistent_nil _)
  rw [sameArgs] at matchedBound
  obtain ⟨_, allBound, instanceArgs⟩ := RegionsWithVariables.sound_list ps
    (fun p m => RegionsWithVariables.sound (psFree p m)) [] bound args matchedBound
  have boundInstance := instanceArgs bound (RegionsWithVariables.Extends.refl bound)
  -- every model agrees with PeTTa's matching on the left side's variables
  have agree : ∀ v, TypeBindingSatisfied v w.bindings → ∀ x ∈ TypeSubst.typeVars w.left,
      (v ∘ rename) x = RegionsWithVariables.asValuation bound x := by
    intro v model x member
    apply agree_of_same (v ∘ rename) (RegionsWithVariables.asValuation bound) w.left
      _ x member
    rw [instantiates v model, leftShape]
    simp only [applyTypeValuation, List.map_cons, boundInstance, sameHead]
  have bodyForced : ∀ v, TypeBindingSatisfied v w.bindings →
      applyTypeValuation v w.body = applySubst bound w.right := by
    intro v model
    rw [bodyEq,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      applySubst_eq_valuation]
    exact Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
      w.right fun x member => agree v model x (varsBound x member)
  have equation : LiveEquations.equationOfRow (.expression [.symbol "=", w.left, w.right]) =
      some ⟨f, ps, w.right⟩ := by
    rw [leftShape, sameHead]
    rfl
  refine ⟨applySubst bound w.right, ?_, fun output sameBindings => ?_⟩
  · simp only [sidesInstance, equation, Option.bind_some, instanceOf, matchedBound, Option.map_some]
  · have certified : Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate
        w.bindings (Entry.Value.eraseEnvironment output.environment) := by
      have := output.certified
      rwa [sameBindings] at this
    -- each variable of the fresh body reads as a data atom
    have plain : ∀ x ∈ TypeSubst.typeVars w.body,
        Entry.Value.resolve output.environment x =
          Entry.Value.ofAtom ((Entry.Value.resolve output.environment x).erase) := by
      intro x member
      rw [bodyEq,
        Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
        at member
      obtain ⟨y, inRight, rfl⟩ := List.mem_map.mp member
      have inLeft := varsBound y inRight
      rw [leftShape] at inLeft
      simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append] at inLeft
      have data : DataAtom (RegionsWithVariables.asValuation bound y) :=
        vars_of_lits boundInstance argsData y inLeft
      have inLeftAtom : y ∈ TypeSubst.typeVars w.left := by
        rw [leftShape]
        simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
        exact inLeft
      have forced := certified.forced_read (.var (rename y)) (RegionsWithVariables.asValuation bound y)
        fun v model => by
          have := agree v model y inLeftAtom
          simpa [applyTypeValuation] using this
      have erased : (Entry.Value.resolve output.environment (rename y)).erase =
          RegionsWithVariables.asValuation bound y := by
        rw [Entry.Value.erase_resolve]
        simpa [TypeSubst.apply] using forced
      rw [erased]
      exact value_of_data data erased
    have readPlain := substitute_plain policy.rebuilding (Entry.Value.resolve output.environment)
      (fun x => (Entry.Value.resolve output.environment x).erase) w.body plain
    have readErase : (output.read policy (Entry.Value.ofAtom w.body)).erase = applySubst bound w.right := by
      unfold Completed.Frame.read
      rw [Entry.Value.erase_substitute_environment, Entry.Value.erase_ofAtom]
      exact certified.forced_read w.body _ bodyForced
    unfold Completed.Frame.read at readErase ⊢
    rw [readPlain] at readErase ⊢
    rw [Entry.Value.erase_ofAtom] at readErase
    rw [readErase]

/-- **HE's frontier of a call carries the sides of the call's region, in row order**, on programs of
symbol-headed, `cons`-free equations, at every satisfiable incoming record. -/
theorem frontier_sides {atoms live : List Atom} {f : String} {args : List Atom}
    {incoming : Bindings}
    (ground : ∀ value ∈ args, TypeSubst.typeVars value = [])
    (satisfiable : ∃ model : String → Atom, TypeBindingSatisfied model incoming)
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works) :
    works.map (fun w => (w.left, w.right)) = regionSides atoms f args := by
  suffices key : ∀ (rows : List Atom) (k : Nat) (blocks : List (List EquationWork)),
      (∀ row ∈ rows, RegionsWithVariables.ConsFreeHeads row) →
      List.Forall₂ (fun row block => EquationRowResultsRel live (.expression (.symbol f :: args))
        incoming row.2 row.1 block) (rows.zipIdx k) blocks →
      blocks.flatten.map (fun w => (w.left, w.right)) = regionSides rows f args by
    cases frontier with
    | completed covered => exact key atoms 0 _ program covered
  intro rows
  induction rows with
  | nil =>
      intro k blocks _ covered
      cases covered
      rfl
  | cons row rows ih =>
      intro k blocks program covered
      rw [List.zipIdx_cons] at covered
      cases covered with
      | cons here rest =>
          rename_i block blocks'
          have agree := RegionsWithVariables.regions_agree_consFree (head := f) live ground
            satisfiable (program row List.mem_cons_self)
          rw [regionSides_cons]
          have restEq := ih (k + 1) blocks'
            (fun r member => program r (List.mem_cons_of_mem _ member)) rest
          rw [List.flatten_cons, List.map_append, restEq]
          cases inRegion : pettaCallRegion f args row with
          | false =>
              rw [(HERuns.block_of_region here).1 (agree.trans inRegion)]
              simp
          | true =>
              obtain ⟨left, right, pattern, body, output, rfl, rfl, _⟩ :=
                (HERuns.block_of_region here).2 (agree.trans inRegion)
              simp [sides]

/-! ## HE's machine on bodies read as instances -/

section HE

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **The equation loop on read instances**: each work's body is read as its instance under its
unifier's frame, evaluated, and the batches are concatenated in work order. -/
theorem equations_steps_open {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
        HEEvaluates dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
          HERuns.HESteps dispatch lookup policy
            ⟨Space.ofList atoms, .work (.equations live scope original Atom.undefinedType activation
              works), stack, emitted⟩
            ⟨Space.ofList atoms, .returning results, stack, emitted⟩
  | [], Ls, _, related, stack, emitted => by
      cases related
      exact ⟨[], rfl, .single (.internal .equationsNil)⟩
  | work :: works, Ls, unifiers, related, stack, emitted => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨output, sameBindings, unified⟩ := unifiers work List.mem_cons_self
          obtain ⟨i, readsAs, evaluates, facts⟩ := here
          obtain ⟨R, eraseR, pathR⟩ := evaluates live scope output
            (.append (.boundaryBatch live scope none (.returned original Atom.undefinedType) []) ::
              .append (.equations live scope original Atom.undefinedType activation works) :: stack)
            emitted
          obtain ⟨R', eraseR', pathR'⟩ := equations_steps_open works Ls'
            (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
            (.prepend (R ++ []) :: stack) emitted
          refine ⟨(R ++ []) ++ R', ?_, ?_⟩
          · rw [List.append_nil, List.map_append, eraseR, eraseR', List.flatten_cons]
          · refine .head (.internal (.equationsCons sameBindings unified)) ?_
            rw [readsAs output sameBindings]
            refine .head (.internal (.boundaryProducerRaw (facts.notFunction policy))) ?_
            refine .head (.internal .boundaryBatch) ?_
            refine .head (.internal .boundaryBatchCons) ?_
            refine .head (.internal .boundaryReturned) ?_
            refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
            · rw [Entry.Value.erase_ofAtom]
              exact facts.notRefused
            · rw [Entry.Value.erase_ofAtom]
              exact facts.notStopped
            refine .trans pathR ?_
            refine .head (.internal .append) ?_
            refine .head (.internal .boundaryBatchNil) ?_
            refine .head (.internal .prepend) ?_
            refine .head (.internal .append) ?_
            refine .trans pathR' ?_
            exact .single (.internal .prepend)

theorem forall₂_filterMap {α β : Type} (g : α → Option β) (P : α → β → Prop) :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ y, g x = some y ∧ P x y) →
      List.Forall₂ (fun x y => g x = some y ∧ P x y) xs (xs.filterMap g)
  | [], _ => .nil
  | x :: xs, each => by
      obtain ⟨y, found, holds⟩ := each x List.mem_cons_self
      rw [List.filterMap_cons, found]
      exact .cons ⟨found, holds⟩
        (forall₂_filterMap g P xs fun z member => each z (List.mem_cons_of_mem _ member))

theorem forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, List.Forall₂ R xs ys → List.Forall₂ S ys zs →
      List.Forall₂ (fun x z => ∃ y, R x y ∧ S y z) xs zs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons r rs, .cons s ss => .cons ⟨_, r, s⟩ (forall₂_comp rs ss)

theorem works_instances {atoms live : List Atom} {f : String} {args : List Atom}
    {incoming : Bindings} (argsData : ∀ a ∈ args, DataAtom a) (program : ScopedProgram atoms)
    (satisfiable : ∃ model : String → Atom, TypeBindingSatisfied model incoming)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works) :
    List.Forall₂ (fun w i => sidesInstance args (w.left, w.right) = some i ∧
        ∀ output : Frame, output.bindings = w.bindings →
          output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i)
      works (regionInstances atoms f args) := by
  have ground : ∀ value ∈ args, TypeSubst.typeVars value = [] :=
    fun a m => HERuns.ground_typeVars (answerable_of_data (argsData a m))
  have sidesEq := frontier_sides ground satisfiable (scoped_consFree program) frontier
  have listed := forall₂_filterMap (fun w : EquationWork => sidesInstance args (w.left, w.right))
    (fun w i => ∀ output : Frame, output.bindings = w.bindings →
      output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i)
    works fun w member => work_read policy argsData program frontier member
  have instancesEq : works.filterMap (fun w => sidesInstance args (w.left, w.right)) =
      regionInstances atoms f args := by
    rw [regionInstances_sides, ← sidesEq, List.filterMap_map]
    rfl
  rw [instancesEq] at listed
  exact listed

/-- **HE's equation query on a call of data atoms with a nonempty region of instances**: the query
fires, each work's body is read as its instance and evaluated, and the batches come back in row
order. -/
theorem he_query_open {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (nonempty : regionInstances atoms f args ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluates dispatch lookup policy atoms b L ∧ BodyFacts b ∧
      ∀ a ∈ L, Answerable a) (regionInstances atoms f args) Ls)
    (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value)
    (erased : value.erase = .expression (.symbol f :: args)) (stack : List Continuation)
    (emitted : List Result) :
    ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
      HERuns.HESteps dispatch lookup policy
        ⟨Space.ofList atoms, .work (.call live scope value Atom.undefinedType activation), stack,
          emitted⟩
        ⟨Space.ofList atoms, .returning results, stack, emitted⟩ := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: args)) activation.bindings
  have instances := works_instances (policy := policy) ordinary.arguments program
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using instances.length_eq.symm
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings works := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment value
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
        output.bindings = work.bindings →
          output.read policy (Entry.Value.ofAtom work.body) = Entry.Value.ofAtom i) ∧
      HEEvaluates dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, evaluates, facts, _⟩ := both
      exact ⟨i, reads, evaluates, facts⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_open works Ls unifiers related stack emitted
  exact ⟨R, eraseR, .head (.internal (.callEquations (HERuns.value_not_error ordinary.head erased)
    (HERuns.value_nonGrounded ordinary.notHost ordinary.notInstruction erased) frontier'
    worksNonempty)) pathR⟩

/-- **A call whose region has instances**: HE's query fires, each body is read as its instance and
evaluated, and the batches are published in row order. -/
theorem he_call_open (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : ScopedProgram atoms) {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args) (nonempty : regionInstances atoms f args ≠ [])
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluates dispatch lookup policy atoms b L ∧ BodyFacts b ∧
      ∀ a ∈ L, Answerable a) (regionInstances atoms f args) Ls) :
    HEEvaluates dispatch lookup policy atoms (.expression (.symbol f :: args)) Ls.flatten := by
  intro live scope activation stack emitted
  obtain ⟨R, eraseR, pathR⟩ := he_query_open program ordinary nonempty bodies live scope activation
    _ (callValue_erase f args)
    (.append (.calls live scope Atom.undefinedType []) ::
      .publish (.expression (.symbol f :: args)) :: stack) emitted
  have clean := HERuns.results_answerable (bodies.imp fun _ _ both => ⟨both.1, both.2.2⟩) eraseR
  obtain ⟨published, erased, finish⟩ := HERuns.finish_steps (dispatch := dispatch) (lookup := lookup)
    (policy := policy) (atoms := atoms) (live := live) (scope := scope)
    (.expression (.symbol f :: args)) R clean stack emitted
  refine ⟨published, by rw [erased, eraseR], ?_⟩
  refine .trans (HERuns.call_entry_steps answers (HERuns.ordinary_data ordinary) ordinary.untyped
    live scope activation stack emitted) ?_
  exact pathR.trans finish

end HE

/-! ## PeTTa's machine on open bodies -/

/-- `u` presents the literal `a` under `σ`: it is `a`, or a variable bound to `a`. -/
def PresentsItem (σ : Subst) (u a : Atom) : Prop :=
  Lit a ∧ (u = a ∨ ∃ x, u = .var x ∧ applySubst σ (.var x) = a)

/-- **`b` presents the ground term `t` under `σ`**: a literal presented by an item, or a call of
the same symbol, not a special form, whose arguments are presented item by item. -/
inductive Presents (σ : Subst) : Atom → Atom → Prop
  | item {u a : Atom} : PresentsItem σ u a → Presents σ u a
  | call (g : String) {us as : List Atom} :
      Unifying.sourceControlForm (.expression (.symbol g :: us)) = false →
      List.Forall₂ (PresentsItem σ) us as →
      Presents σ (.expression (.symbol g :: us)) (.expression (.symbol g :: as))

/-- **PeTTa's streaming machine evaluates every open presentation of `t` to the answers `L`**,
under any frames that deliver each of them. -/
def PeTTaOpen (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (frames : List Streaming.Frame) (K : Atom → List Atom), (∀ v ∈ L, Delivers atoms frames K v) →
  ∀ (world : Streaming.World) (σ : Subst), world.state = store atoms → world.privateCode = [] →
    Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (b : Atom), Presents σ b t →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = L.flatMap K ∧
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.evaluate σ b, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

/-- A ground term of the fragment presents itself. -/
theorem presents_self {dispatch : GroundedDispatch} {atoms : List Atom} {t : Atom}
    (settles : SettlesV dispatch atoms t) (σ : Subst) : Presents σ t t := by
  have call : ∀ {f : String} {args : List Atom}, Ordinary dispatch atoms f args →
      Presents σ (.expression (.symbol f :: args)) (.expression (.symbol f :: args)) := by
    intro f args ordinary
    refine .call f ordinary.notControl ?_
    have each : ∀ a ∈ args, PresentsItem σ a a :=
      fun a member => ⟨lit_of_data (ordinary.arguments a member), Or.inl rfl⟩
    clear ordinary
    induction args with
    | nil => exact .nil
    | cons a rest ih =>
        exact .cons (each a List.mem_cons_self) (ih fun b m => each b (List.mem_cons_of_mem _ m))
  cases settles with
  | data data _ => exact .item ⟨lit_of_data data, Or.inl rfl⟩
  | constructor ordinary _ => exact call ordinary
  | call ordinary _ _ => exact call ordinary

theorem petta_of_open {dispatch : GroundedDispatch} {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesV dispatch atoms t) (evaluates : PeTTaOpen atoms t L) :
    PeTTaEvaluates atoms t L :=
  fun frames K deliver world σ state privateCode range fresh older answers next =>
    evaluates frames K deliver world σ state privateCode range fresh t (presents_self settles σ)
      older answers next

namespace PeTTaOpenRuns

open PeTTaRuns

variable {registry : SpaceSemantics.Program}

theorem evaluate_item (world : Streaming.World) (σ : Subst) {u a : Atom}
    (presented : PresentsItem σ u a) (frames : List Streaming.Frame) (older : List Streaming.Job)
    (answers : List Unifying.Answer) (next : Nat) :
    Streaming.Transition registry ⟨world, .execute ⟨.evaluate σ u, frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.returned [⟨a, σ⟩], frames⟩ :: older, answers, next⟩ := by
  obtain ⟨literal, rfl | ⟨x, rfl, bound⟩⟩ := presented
  · cases literal with
    | symbol _ => exact .phase rfl rfl (.symbol rfl) (.plain rfl)
    | grounded _ => exact .phase rfl rfl (.grounded rfl) (.plain rfl)
  · have step : Streaming.Transition registry
        ⟨world, .execute ⟨.evaluate σ (.var x), frames⟩ :: older, answers, next⟩
        ⟨world, .execute ⟨.returned [⟨Unifying.resolve σ (.var x), σ⟩], frames⟩ :: older, answers,
          next⟩ := .phase rfl rfl (.value_variable rfl) (.plain rfl)
    simpa only [Unifying.resolve, bound] using step

/-- One presented argument: evaluated, returned to its frame, and the traversal continued. -/
theorem argument_open (world : Streaming.World) (σ : Subst)
    (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target) {u a : Atom}
    (presented : PresentsItem σ u a) (rest held : List Atom) (index : Nat)
    (demanded : rawDemand registry target index = false)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Unifying.Answer)
    (next : Nat) :
    PSteps registry
      ⟨world, .execute ⟨.arguments σ target (u :: rest) held index, frames⟩ :: older, answers,
        next⟩
      ⟨world, .execute ⟨.arguments σ target rest (held ++ [a]) (index + 1), frames⟩ :: older,
        answers, next⟩ := by
  refine .head (evaluate_argument world σ target u rest held index demanded frames older answers
    next) ?_
  refine .head (evaluate_item world σ presented _ older answers next) ?_
  refine .head (return_argument world ⟨a, σ⟩ target rest held index frames older answers next) ?_
  exact .single (PeTTaRuns.alternatives world _ frames older answers next)

/-- **The argument traversal of presented items.** -/
theorem arguments_open (world : Streaming.World) (σ : Subst)
    (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target)
    (demanded : ∀ index, rawDemand registry target index = false)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Unifying.Answer)
    (next : Nat) :
    ∀ (us as held : List Atom) (index : Nat), List.Forall₂ (PresentsItem σ) us as →
      PSteps registry
        ⟨world, .execute ⟨.arguments σ target us held index, frames⟩ :: older, answers, next⟩
        ⟨world, .execute ⟨.arguments σ target [] (held ++ as) (index + us.length), frames⟩ ::
          older, answers, next⟩
  | [], [], held, index, .nil => by
      simp only [List.append_nil, List.length_nil, Nat.add_zero]
      exact .refl
  | u :: us, a :: as, held, index, .cons here rest => by
      refine .trans (argument_open world σ target here us held index (demanded index) frames older
        answers next) ?_
      have later := arguments_open world σ target demanded frames older answers next us as
        (held ++ [a]) (index + 1) rest
      rw [List.length_cons, show index + (us.length + 1) = index + 1 + us.length by omega]
      simpa only [List.append_assoc, List.singleton_append] using later

theorem lits_ground : ∀ {as : List Atom}, (∀ a ∈ as, Lit a) → ∀ v ∈ as, isGroundAtom v = true
  | [], _, v, member => by cases member
  | a :: as, each, v, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · cases each v List.mem_cons_self <;> rfl
      · exact lits_ground (fun b m => each b (List.mem_cons_of_mem _ m)) v inRest

theorem presented_lits {σ : Subst} : ∀ {us as : List Atom}, List.Forall₂ (PresentsItem σ) us as →
    ∀ a ∈ as, Lit a
  | [], [], .nil, a, member => by cases member
  | _ :: _, _ :: _, .cons here rest, a, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact here.1
      · exact presented_lits rest a inRest

end PeTTaOpenRuns

/-- **A data atom**: every presentation of it, the atom or a variable bound to it, returns it. -/
theorem petta_open_data (atoms : List Atom) {d : Atom} (data : DataAtom d) :
    PeTTaOpen atoms d [d] := by
  intro frames K deliver world σ state privateCode range fresh b presented older answers next
  have item : PresentsItem σ b d := by
    cases presented with
    | item here => exact here
    | call g _ _ => cases data
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver d List.mem_cons_self world σ state
    privateCode range fresh older answers next
  exact ⟨uses, out, grown, by simp [valuesOut],
    .head (PeTTaOpenRuns.evaluate_item world σ item frames older answers next) path⟩

/-- Inverting a presentation of a call. -/
theorem presents_call {σ : Subst} {b : Atom} {f : String} {args : List Atom}
    (presented : Presents σ b (.expression (.symbol f :: args))) :
    ∃ us, b = .expression (.symbol f :: us) ∧
      Unifying.sourceControlForm (.expression (.symbol f :: us)) = false ∧
      List.Forall₂ (PresentsItem σ) us args := by
  cases presented with
  | item here => cases here.1
  | call g notControl items => exact ⟨_, rfl, notControl, items⟩

/-- **A constructor call**: PeTTa builds the expression from its presented items. -/
theorem petta_open_constructor {dispatch : GroundedDispatch} {atoms : List Atom} {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true) :
    PeTTaOpen atoms (.expression (.symbol f :: args)) [.expression (.symbol f :: args)] := by
  intro frames K deliver world σ state privateCode range fresh b presented older answers next
  obtain ⟨us, rfl, notControl, items⟩ := presents_call presented
  have notCallable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      false := by
    rw [privateCode, ordinary.notIO, ordinary.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    apply List.any_eq_false.mpr
    intro e member
    have different := List.all_eq_true.mp noEquation e member
    simpa using different
  have headItem : PresentsItem σ (.symbol f) (.symbol f) := ⟨.symbol f, Or.inl rfl⟩
  have groundItems : ∀ v ∈ Atom.symbol f :: args, isGroundAtom v = true :=
    fun v member => (answerable_of_data (HERuns.ordinary_data ordinary v member)).ground
  obtain ⟨uses, out, grown, valuesOut, path⟩ := PeTTaRuns.petta_construct groundItems frames K
    (deliver _ List.mem_cons_self) world σ state privateCode range fresh
    (0 + (Atom.symbol f :: us).length) older answers next
  refine ⟨uses, out, grown, by simp [valuesOut], ?_⟩
  refine .head (PeTTaRuns.data_enter world σ ordinary.notCollapse ordinary.notOnce notControl
    notCallable frames older answers next) ?_
  have traversed := PeTTaOpenRuns.arguments_open (registry := translate atoms) world σ .data
    (fun _ => rfl) frames older answers next (Atom.symbol f :: us) (Atom.symbol f :: args) [] 0
    (.cons headItem items)
  rw [List.nil_append] at traversed
  exact traversed.trans path

/-! ### The selected clauses, with open bodies -/

/-- **The renamed body presents the instance** under the matching bindings renamed for the use and
followed by the caller's bindings. -/
theorem presents_renamed {use : Nat} {bound σ : Subst} (fresh : Unifying.FreshFor use σ)
    {ps args : List Atom} (argsData : ∀ a ∈ args, DataAtom a)
    (instantiated : ps.map (applyTypeValuation (RegionsWithVariables.asValuation bound)) = args)
    {body : Atom} (flat : FlatBody body)
    (varsBound : ∀ x ∈ TypeSubst.typeVars body, x ∈ TypeSubst.typeVarsList ps) :
    Presents (Unifying.renameKeys use bound ++ σ) (Unifying.rename use body)
      (applySubst bound body) := by
  have item : ∀ u, FlatItem u → (∀ x ∈ TypeSubst.typeVars u, x ∈ TypeSubst.typeVarsList ps) →
      PresentsItem (Unifying.renameKeys use bound ++ σ) (Unifying.rename use u)
        (applySubst bound u) := by
    intro u flatItem uBound
    cases flatItem with
    | symbol name => exact ⟨.symbol name, Or.inl rfl⟩
    | grounded value => exact ⟨.grounded value, Or.inl rfl⟩
    | var name =>
        have inPs := uBound name (by simp [TypeSubst.typeVars])
        have data := vars_of_lits instantiated argsData name inPs
        have read : applySubst bound (.var name) = RegionsWithVariables.asValuation bound name := by
          simp [applySubst, RegionsWithVariables.asValuation]
        refine ⟨by rw [read]; exact lit_of_data data, Or.inr ⟨Unifying.freshName use name, rfl, ?_⟩⟩
        have looked : (Unifying.renameKeys use bound ++ σ).lookup (Unifying.freshName use name) =
            bound.lookup name := Unifying.lookup_append_renamed fresh name
        cases found : bound.lookup name with
        | none =>
            have unbound : RegionsWithVariables.asValuation bound name = .var name := by
              simp [RegionsWithVariables.asValuation, found]
            rw [unbound] at data
            cases data
        | some value =>
            rw [found] at looked
            simp only [applySubst]
            rw [looked, found, Option.getD_some, Option.getD_some]
  cases flat with
  | item flatItem => exact .item (item _ flatItem varsBound)
  | call g items notControl each =>
      have renameList : ∀ xs : List Atom,
          Unifying.rename.renameList use xs = xs.map (Unifying.rename use) := by
        intro xs
        induction xs with
        | nil => simp [Unifying.rename.renameList]
        | cons x xs ih => simp [Unifying.rename.renameList, ih]
      have substList : ∀ xs : List Atom,
          applySubst.applySubstList bound xs = xs.map (applySubst bound) := by
        intro xs
        induction xs with
        | nil => simp [applySubst.applySubstList]
        | cons x xs ih => simp [applySubst.applySubstList, ih]
      have renamed : Unifying.rename use (.expression (.symbol g :: items)) =
          .expression (.symbol g :: items.map (Unifying.rename use)) := by
        simp only [Unifying.rename, Unifying.rename.renameList, renameList]
      have substituted : applySubst bound (.expression (.symbol g :: items)) =
          .expression (.symbol g :: items.map (applySubst bound)) := by
        simp only [applySubst, applySubst.applySubstList, substList]
      rw [renamed, substituted]
      refine .call g (sourceControlForm_of_head notControl _) ?_
      have pointwise : ∀ u ∈ items, PresentsItem (Unifying.renameKeys use bound ++ σ)
          (Unifying.rename use u) (applySubst bound u) := fun u member =>
        item u (each u member) fun x inU => varsBound x (by
          simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
          exact Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
            member x inU)
      clear varsBound each renamed substituted
      induction items with
      | nil => exact .nil
      | cons u rest ih =>
          exact .cons (pointwise u List.mem_cons_self)
            (ih fun v m => pointwise v (List.mem_cons_of_mem _ m))

/-- Each selected equation of a bound program: its sides and its PeTTa match. -/
theorem selected_instance {atoms : List Atom} (program : BoundProgram atoms)
    {e : SpaceSemantics.Equation} (live : e ∈ atoms.filterMap LiveEquations.equationOfRow)
    {args : List Atom} (argsData : ∀ a ∈ args, DataAtom a) {bound : Subst}
    (matched : SpaceSemantics.matchValue.matchValues [] e.arguments args = some bound)
    (use : Nat) {σ : Subst} (fresh : Unifying.FreshFor use σ) :
    Presents (Unifying.renameKeys use bound ++ σ) (Unifying.rename use e.body)
      (applySubst bound e.body) := by
  obtain ⟨row, inAtoms, found⟩ := List.mem_filterMap.mp live
  have shape := LiveEquations.equationOfRow_eq_some found
  obtain ⟨consFree, boundRow⟩ := program row inAtoms
  subst shape
  obtain ⟨varsBound, flat⟩ := boundRow _ e.body rfl
  obtain ⟨h, ps, leftShape, psFree⟩ := consFree _ e.body rfl
  simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at leftShape
  obtain ⟨_, rfl⟩ := leftShape
  obtain ⟨_, _, instanceArgs⟩ := RegionsWithVariables.sound_list e.arguments
    (fun p m => RegionsWithVariables.sound (psFree p m)) [] bound args matched
  exact presents_renamed fresh argsData (instanceArgs bound (RegionsWithVariables.Extends.refl bound))
    flat fun x member => by
      have := varsBound x member
      simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using this

/-- The clauses a call selects run one after another, each open body to its end. -/
theorem run_clauses_open {atoms : List Atom} (program : BoundProgram atoms) {σ : Subst}
    {values : List Atom} (valuesData : ∀ v ∈ values, DataAtom v) (range : Unifying.GroundRange σ)
    (frames : List Streaming.Frame) (K : Atom → List Atom) :
    ∀ (chosen : List SpaceSemantics.Equation) (use : Nat) (Ls : List (List Atom)),
      (∀ e ∈ chosen, e ∈ atoms.filterMap LiveEquations.equationOfRow) →
      List.Forall₂ (fun b L => PeTTaOpen atoms b L) (matchingInstances values chosen) Ls →
      (∀ v ∈ Ls.flatten, Delivers atoms frames K v) →
      ∀ (world : Streaming.World), world.state = store atoms → world.privateCode = [] →
        use + chosen.length ≤ world.uses → (∀ k, Unifying.FreshFor (use + k) σ) →
        ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
          ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
            out.map (fun answer => Unifying.resolve answer.bindings answer.value) =
              Ls.flatten.flatMap K ∧
            PeTTaRuns.PSteps (translate atoms)
              ⟨world, ((Unifying.renamedClauses σ values use chosen).map fun control =>
                .execute ⟨control, frames⟩) ++ older, answers, next⟩
              ⟨{world with uses := uses}, older, answers ++ out, next⟩
  | [], _, Ls, _, related, _, world, _, _, _, _, older, answers, next => by
      cases related
      refine ⟨world.uses, [], le_rfl, rfl, ?_⟩
      simp only [Unifying.renamedClauses, List.map_nil, List.nil_append, List.append_nil]
      exact .refl
  | e :: rest, use, Ls, live, related, deliver, world, state, privateCode, enough, fresh, older,
      answers, next => by
      have enough' : use + 1 + rest.length ≤ world.uses := by
        simp only [List.length_cons] at enough
        omega
      have liveRest : ∀ e' ∈ rest, e' ∈ atoms.filterMap LiveEquations.equationOfRow :=
        fun e' member => live e' (List.mem_cons_of_mem _ member)
      cases matched : SpaceSemantics.matchValue.matchValues [] e.arguments values with
      | none =>
          have skip : matchingInstances values (e :: rest) = matchingInstances values rest := by
            simp [matchingInstances, instanceOf, matched]
          rw [skip] at related
          have clauses : Unifying.renamedClauses σ values use (e :: rest) =
              Unifying.renamedClauses σ values (use + 1) rest := by
            simp [Unifying.renamedClauses, matched]
          rw [clauses]
          exact run_clauses_open program valuesData range frames K rest (use + 1) Ls liveRest related
            deliver world state privateCode enough' (fun k => by
              have shifted := fresh (1 + k)
              rwa [← Nat.add_assoc] at shifted) older answers next
      | some bound =>
          have take : matchingInstances values (e :: rest) =
              applySubst bound e.body :: matchingInstances values rest := by
            simp [matchingInstances, instanceOf, matched]
          rw [take] at related
          cases related with
          | cons here later =>
              rename_i L Ls'
              have clauses : Unifying.renamedClauses σ values use (e :: rest) =
                  .evaluate (Unifying.renameKeys use bound ++ σ) (Unifying.rename use e.body) ::
                    Unifying.renamedClauses σ values (use + 1) rest := by
                simp [Unifying.renamedClauses, matched]
              rw [clauses]
              have groundValues : ∀ v ∈ values, isGroundAtom v = true :=
                fun v member => (answerable_of_data (valuesData v member)).ground
              have boundRange := PeTTaRuns.matchValues_groundRange e.arguments values [] bound
                (fun _ member => by cases member) groundValues matched
              have below : use < world.uses := by omega
              have outerFresh : ∀ k, Unifying.FreshFor (world.uses + k) σ := fun k => by
                have shifted := fresh (world.uses - use + k)
                rwa [show use + (world.uses - use + k) = world.uses + k by omega] at shifted
              have presented := selected_instance program (live e List.mem_cons_self) valuesData
                matched use (by simpa using fresh 0)
              obtain ⟨uses₁, out₁, grown₁, values₁, path₁⟩ := here frames K
                (fun v member => deliver v (by
                  rw [List.flatten_cons]
                  exact List.mem_append_left _ member)) world
                (Unifying.renameKeys use bound ++ σ) state privateCode
                (PeTTaRuns.groundRange_renamed boundRange range)
                (PeTTaRuns.freshFor_renamed below outerFresh) _ presented
                (((Unifying.renamedClauses σ values (use + 1) rest).map fun control =>
                  .execute ⟨control, frames⟩) ++ older) answers next
              obtain ⟨uses₂, out₂, grown₂, values₂, path₂⟩ := run_clauses_open program valuesData
                range frames K rest (use + 1) Ls' liveRest later
                (fun v member => deliver v (by
                  rw [List.flatten_cons]
                  exact List.mem_append_right _ member))
                {world with uses := uses₁} state privateCode (by simp only; omega)
                (fun k => by
                  have shifted := fresh (1 + k)
                  rwa [← Nat.add_assoc] at shifted) older (answers ++ out₁) next
              refine ⟨uses₂, out₁ ++ out₂, grown₁.trans grown₂, ?_, ?_⟩
              · rw [List.map_append, values₁, values₂, List.flatten_cons, List.flatMap_append]
              · simp only [List.map_cons, List.cons_append]
                rw [← List.append_assoc]
                exact path₁.trans path₂

/-- **An application of a defined head to held data values, with open bodies**: PeTTa selects the
matching equations in row order and runs each renamed body to its end. -/
theorem petta_apply_open {atoms : List Atom} (program : BoundProgram atoms) {f : String}
    {vals : List Atom} (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = vals.length)
    (valsData : ∀ v ∈ vals, DataAtom v) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => PeTTaOpen atoms b L) (regionInstances atoms f vals) Ls)
    (frames : List Streaming.Frame) (K : Atom → List Atom)
    (deliver : ∀ v ∈ Ls.flatten, Delivers atoms frames K v)
    (world : Streaming.World) (σ : Subst) (state : world.state = store atoms)
    (privateCode : world.privateCode = []) (range : Unifying.GroundRange σ)
    (fresh : ∀ k, Unifying.FreshFor (world.uses + k) σ) (index : Nat)
    (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat) :
    ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
      out.map (fun answer => Unifying.resolve answer.bindings answer.value) = Ls.flatten.flatMap K ∧
      PeTTaRuns.PSteps (translate atoms)
        ⟨world, .execute ⟨.arguments σ (.function f) [] vals index, frames⟩ :: older, answers, next⟩
        ⟨{world with uses := uses}, older, answers ++ out, next⟩ := by
  obtain ⟨e, live, head, arity⟩ := defined
  have groundVals : ∀ v ∈ vals, isGroundAtom v = true :=
    fun v member => (answerable_of_data (valsData v member)).ground
  have liveEquations : Unifying.codeEquations world.state world.privateCode =
      atoms.filterMap LiveEquations.equationOfRow := by
    rw [state, privateCode]
    simp only [Unifying.codeEquations, List.nil_append, LiveEquations.liveEquations, store_core]
  set chosen := Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f vals.length
    with chosenEq
  have arityKnown : vals.length ∈ Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
      (Unifying.codeRegistry (translate atoms) world.privateCode) f := by
    rw [privateCode]
    simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry, List.nil_append,
      translate_equations]
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [head]⟩, arity⟩
  have applied : Unifying.application (Unifying.codeRegistry (translate atoms) world.privateCode)
      (Unifying.codeEquations world.state world.privateCode) f
      (vals.map (Unifying.resolve σ)) σ world.uses =
      some (.sequence (Unifying.renamedClauses σ vals world.uses chosen) [], chosen.length) := by
    rw [PeTTaRuns.map_resolve_ground σ groundVals, liveEquations]
    unfold Unifying.application
    rw [if_pos arityKnown]
    simp only
    rw [Unifying.selections_eq_renamedClauses range groundVals world.uses _ fresh]
    rfl
  have related : List.Forall₂ (fun b L => PeTTaOpen atoms b L) (matchingInstances vals chosen) Ls := by
    rw [chosenEq, ← regionInstances_eq]
    exact bodies
  have chosenLive : ∀ e' ∈ chosen, e' ∈ atoms.filterMap LiveEquations.equationOfRow :=
    fun e' member => (List.mem_filter.mp member).1
  obtain ⟨uses, out, grown, valuesOut, path⟩ := run_clauses_open program valsData range frames K
    chosen world.uses Ls chosenLive related deliver {world with uses := world.uses + chosen.length}
    state privateCode (by simp only; omega) fresh older answers next
  refine ⟨uses, out, by simp only at grown; omega, valuesOut, ?_⟩
  refine .head (PeTTaRuns.apply_equations world σ vals index notIO notNative applied frames older
    answers next) ?_
  refine .head (PeTTaRuns.alternatives _ _ frames older answers next) ?_
  exact path

/-- **A call of a defined head, every presentation**: PeTTa evaluates the presented arguments,
selects the matching equations, and runs each renamed body to its end. -/
theorem petta_open_call {dispatch : GroundedDispatch} {atoms : List Atom}
    (program : BoundProgram atoms) {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length)
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => PeTTaOpen atoms b L) (regionInstances atoms f args) Ls) :
    PeTTaOpen atoms (.expression (.symbol f :: args)) Ls.flatten := by
  intro frames K deliver world σ state privateCode range fresh b presented older answers next
  obtain ⟨us, rfl, notControl, items⟩ := presents_call presented
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      true := by
    obtain ⟨e, live, head, _⟩ := defined
    rw [privateCode, ordinary.notIO, ordinary.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    exact List.any_eq_true.mpr ⟨e, live, by simp [head]⟩
  obtain ⟨uses, out, grown, valuesOut, path⟩ := petta_apply_open program ordinary.notIO
    ordinary.notNative defined ordinary.arguments bodies frames K deliver world σ state privateCode
    range fresh (0 + us.length) older answers next
  refine ⟨uses, out, grown, valuesOut, ?_⟩
  refine .head (PeTTaRuns.call_enter world σ ordinary.notCollapse ordinary.notOnce notControl
    callable frames older answers next) ?_
  have entered := PeTTaOpenRuns.arguments_open (registry := translate atoms) world σ (.function f)
    (fun index => argumentIsRaw_false ordinary.notNative ordinary.untyped index) frames older
    answers next us args [] 0 items
  rw [List.nil_append] at entered
  exact entered.trans path

/-! ## Both machines on the extended fragment -/

section Joint

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **Both machines evaluate every settling term to the same answer list**, PeTTa on every open
presentation: one induction on the settling derivation. -/
theorem settlesV_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : BoundProgram atoms) {t : Atom} (settles : SettlesV dispatch atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ HEEvaluates dispatch lookup policy atoms t L ∧
      PeTTaOpen atoms t L := by
  induction settles with
  | @data d data _ =>
      refine ⟨[d], fun a member => ?_, HERuns.he_data answers atoms data, petta_open_data atoms data⟩
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        HERuns.he_absent answers (bound_consFree program) ordinary
          (regionBodies_nil_of_no_equation args noEquation),
        petta_open_constructor ordinary noEquation⟩
      rw [List.mem_singleton] at member
      subst member
      exact call_answerable ordinary.head ordinary.arguments
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionInstances atoms f args, ∃ L, SettlesV dispatch atoms b ∧
          (∀ a ∈ L, Answerable a) ∧ HEEvaluates dispatch lookup policy atoms b L ∧
          PeTTaOpen atoms b L := by
        intro b member
        obtain ⟨L, rest⟩ := ih b member
        exact ⟨L, settled b member, rest⟩
      obtain ⟨Ls, related⟩ := forall₂_of_forall_exists _ each
      have defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
          e.arguments.length = args.length := by
        obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
        rw [regionInstances_eq] at inRegion
        obtain ⟨e, chosen, _⟩ := List.mem_filterMap.mp inRegion
        obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
        simp only [Bool.and_eq_true, beq_iff_eq] at selected
        exact ⟨e, live, selected.1, selected.2⟩
      refine ⟨Ls.flatten, ?_, he_call_open answers program.scoped ordinary nonempty
          (related.imp fun _ _ both => ⟨both.2.2.1, settlesV_facts both.1, both.2.1⟩),
        petta_open_call program ordinary defined (related.imp fun _ _ both => both.2.2.2)⟩
      intro a member
      obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
      obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
      exact both.2.1 a inner

/-- **The answers agree on the extended fragment**: HE's machine runs from its entry configuration
to a completed phase, and from some fuel on PeTTa's streaming run of the translation yields exactly
the atoms HE published, in the same order and with the same multiplicities. -/
theorem answersV_agree (dispatch : GroundedDispatch) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (policy : Policy) {atoms : List Atom}
    (program : BoundProgram atoms) {c : Atom} (settles : SettlesV dispatch atoms c) :
    ∃ (heAnswers : List Result) (N : Nat),
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
        ∀ n, N ≤ n →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = heAnswers.map (fun r => r.1.erase) := by
  obtain ⟨L, clean, he, petta⟩ := settlesV_agree (policy := policy) answers program settles
  obtain ⟨R, eraseR, path, observed⟩ := he_complete he
  obtain ⟨N, stable⟩ := petta_complete (settlesV_facts settles).ground clean
    (petta_of_open settles petta)
  exact ⟨R, N, path, observed, fun n bigger => by rw [stable n bigger, eraseR]⟩

end Joint

/-! ## Every complete run -/

section EveryRunV

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- **The batch of an ordinary call, by HE's source semantics**: the call itself when its region is
empty; otherwise the frontier's works carry the region's sides in order, and their bodies give the
batch. -/
theorem callRel_source_open {lookup : CastLookup} {atoms : List Atom}
    (program : ScopedProgram atoms) {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args) {live : List Atom} {scope : List String}
    {after : Frame} {children : List Result}
    (called : Completed.CallRel (Space.ofList atoms) dispatch lookup live scope
      (callValue f args) Atom.undefinedType after children (policy := policy)) :
    (children = [(callValue f args, after)] ∧ regionSides atoms f args = []) ∨
      ∃ works : List EquationWork, works ≠ [] ∧
        EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
          (.expression (.symbol f :: args)) after.bindings works ∧
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch lookup live scope
          (callValue f args) Atom.undefinedType after works children (policy := policy) := by
  have ground : ∀ v ∈ args,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member))
  cases called with
  | error failed => exact absurd failed (call_not_error ordinary.head args)
  | embedded _ _ instruction _ _ =>
      rw [callValue_erase, ordinary.notInstruction] at instruction
      cases instruction
  | absent _ _ frontier =>
      rw [callValue_erase] at frontier
      have sidesEq := frontier_sides ground after.certified.satisfiable (scoped_consFree program)
        frontier
      exact Or.inl ⟨rfl, sidesEq.symm⟩
  | equations _ _ frontier nonempty bodies =>
      rw [callValue_erase] at frontier
      exact Or.inr ⟨_, nonempty, frontier, bodies⟩

/-- **The equation bodies, read as instances**: each body's results are its instance's. -/
theorem bodies_source_open {lookup : CastLookup} {atoms : List Atom} {live : List Atom}
    {scope : List String} {original : Entry.Value} {frame : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
          output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i) ∧
        DeterminedUnder dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ {results : List Result},
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch lookup live scope
          original Atom.undefinedType frame works results (policy := policy) →
        results.map (fun r => r.1.erase) = Ls.flatten
  | [], _, related, _, derived => by
      cases related
      cases derived
      rfl
  | w :: ws, _, related, _, derived => by
      obtain ⟨L, Ls', ⟨i, readsAs, determined, facts⟩, rest, rfl⟩ :=
        List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons sameBindings _ boundary batch later =>
          rw [readsAs _ sameBindings] at boundary
          cases boundary with
          | producerFunction pending _ => exact absurd pending (facts.notFunction policy)
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          exact absurd (by simpa only [Entry.Value.erase_ofAtom] using same)
                            facts.notRefused
                      | stopped stopped =>
                          exact absurd (by simpa only [Entry.Value.erase_ofAtom] using stopped)
                            facts.notStopped
                      | evaluate _ _ evaluated =>
                          rw [List.append_nil, List.map_append, determined _ _ _ _ evaluated,
                            bodies_source_open ws Ls' rest later, List.flatten_cons]

/-- **On the extended fragment, HE's source semantics determines the published atoms**, for every
lookup meeting the contract. -/
theorem settlesV_determined_under {lookup : CastLookup} (contract : LookupContract lookup)
    {atoms : List Atom} (program : BoundProgram atoms) {t : Atom}
    (settles : SettlesV dispatch atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ DeterminedUnder dispatch lookup policy atoms t L := by
  induction settles with
  | @data d data notRefused =>
      refine ⟨[d], fun a member => ?_, fun live scope frame results derived => ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data data
      · obtain ⟨after, rfl⟩ := data_source contract data derived
        simp
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        empty_region_determined contract (bound_consFree program) ordinary
          (regionBodies_nil_of_no_equation args noEquation)⟩
      rw [List.mem_singleton] at member
      subst member
      exact call_answerable ordinary.head ordinary.arguments
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionInstances atoms f args, ∃ L : List Atom,
          SettlesV dispatch atoms b ∧ (∀ a ∈ L, Answerable a) ∧
            DeterminedUnder dispatch lookup policy atoms b L := by
        intro b member
        obtain ⟨L, clean, determined⟩ := ih b member
        exact ⟨L, settled b member, clean, determined⟩
      obtain ⟨Ls, related⟩ := forall₂_of_forall_exists _ each
      have cleanAll : ∀ a ∈ Ls.flatten, Answerable a := by
        intro a member
        obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
        obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
        exact both.2.1 a inner
      refine ⟨Ls.flatten, cleanAll, fun live scope frame results derived => ?_⟩
      obtain ⟨after, children, selected, called, chosen, erased⟩ :=
        call_source contract ordinary derived
      rcases callRel_source_open program.scoped ordinary called with
        ⟨_, empty⟩ | ⟨works, _, frontier, equations⟩
      · apply absurd _ nonempty
        rw [regionInstances_sides, empty]
        rfl
      · have instances := works_instances (policy := policy) ordinary.arguments program.scoped
          after.certified.satisfiable frontier
        have onWorks : List.Forall₂ (fun w L => ∃ i, (∀ output : Frame,
              output.bindings = w.bindings →
                output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i) ∧
            DeterminedUnder dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls :=
          (forall₂_comp instances related).imp fun _ _ both => by
            obtain ⟨i, ⟨_, reads⟩, settlesI, _, determined⟩ := both
            exact ⟨i, reads, determined, settlesV_facts settlesI⟩
        have erasedChildren := bodies_source_open works Ls onWorks equations
        have clean : ∀ r ∈ children, Answerable r.1.erase := by
          intro r member
          apply cleanAll
          rw [← erasedChildren]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        have unchanged : children.map (Completed.readResult policy) = children :=
          map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
        rw [unchanged] at chosen
        have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
          chosen (HERuns.success_all children fun r member => (clean r member).notError)
        rw [erased, same, erasedChildren]

/-- **Every complete run of HE publishes PeTTa's answers, bodies using their variables**, under any
lookup meeting the contract. -/
theorem every_complete_run_v (dispatch : GroundedDispatch) {lookup : CastLookup}
    (answers : AnswersUndefined lookup) (contract : LookupContract lookup) (policy : Policy)
    {atoms : List Atom} (program : BoundProgram atoms) {c : Atom}
    (settles : SettlesV dispatch atoms c) :
    ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        Streaming.values (Streaming.advance (translate atoms) n
          (Streaming.enter { state := store atoms } c)) = emitted.map (fun r => r.1.erase) := by
  obtain ⟨L, _, determined⟩ := settlesV_determined_under (policy := policy) contract program settles
  obtain ⟨heAnswers, N, path, _, agree⟩ := answersV_agree dispatch answers policy program settles
  refine ⟨N, fun n bigger emitted run => ?_⟩
  rw [agree n bigger, determined _ _ _ _ (complete_source path),
    determined _ _ _ _ (complete_source run)]

/-- **The answer bags agree for every complete run, bodies using their variables** (HE's
historical lookup): a complete run exists, and every complete run publishes the bag PeTTa yields. -/
theorem answer_bags_every_run_v (dispatch : GroundedDispatch) (policy : Policy)
    {atoms : List Atom} (program : BoundProgram atoms) {c : Atom}
    (settles : SettlesV dispatch atoms c) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers) ∧
      ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) c Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          ((emitted.map fun r => r.1.erase : List Atom) : Multiset Atom) =
            (Streaming.values (Streaming.advance (translate atoms) n
              (Streaming.enter { state := store atoms } c)) : Multiset Atom) := by
  obtain ⟨heAnswers, _, path, observed, _⟩ :=
    answersV_agree dispatch raw_answers policy program settles
  obtain ⟨N, every⟩ := every_complete_run_v dispatch raw_answers raw_contract policy program settles
  exact ⟨⟨heAnswers, path, observed⟩, N, fun n bigger emitted run => by
    rw [every n bigger emitted run]⟩

end EveryRunV

/-! ## The extension is conservative -/

theorem matchingInstances_of_ground {values : List Atom} :
    ∀ (chosen : List SpaceSemantics.Equation),
      (∀ b ∈ matchingBodies values chosen, isGroundAtom b = true) →
        matchingInstances values chosen = matchingBodies values chosen
  | [], _ => rfl
  | e :: rest, ground => by
      cases matched : SpaceSemantics.matchValue.matchValues [] e.arguments values with
      | none =>
          have skipI : matchingInstances values (e :: rest) = matchingInstances values rest := by
            simp [matchingInstances, instanceOf, matched]
          have skipB : matchingBodies values (e :: rest) = matchingBodies values rest := by
            simp [matchingBodies, matched]
          rw [skipB] at ground
          rw [skipI, skipB]
          exact matchingInstances_of_ground rest ground
      | some bound =>
          have takeI : matchingInstances values (e :: rest) =
              applySubst bound e.body :: matchingInstances values rest := by
            simp [matchingInstances, instanceOf, matched]
          have takeB : matchingBodies values (e :: rest) = e.body :: matchingBodies values rest := by
            simp [matchingBodies, matched]
          rw [takeB] at ground
          rw [takeI, takeB, Unifying.applySubst_ground bound e.body (ground e.body List.mem_cons_self),
            matchingInstances_of_ground rest fun b member => ground b (List.mem_cons_of_mem _ member)]

/-- With closed region bodies, the instances are the bodies. -/
theorem regionInstances_of_ground {atoms : List Atom} {f : String} {args : List Atom}
    (ground : ∀ b ∈ regionBodies atoms f args, isGroundAtom b = true) :
    regionInstances atoms f args = regionBodies atoms f args := by
  rw [regionBodies_eq] at ground
  rw [regionInstances_eq, regionBodies_eq]
  exact matchingInstances_of_ground _ ground

/-- **Conservativity**: every term that settles in `AnswerBags`'s sense settles here. -/
theorem settles_settlesV {dispatch : GroundedDispatch} {atoms : List Atom} {t : Atom}
    (settles : Settles dispatch atoms t) : SettlesV dispatch atoms t := by
  induction settles with
  | data data notRefused => exact .data data notRefused
  | constructor ordinary noEquation => exact .constructor ordinary noEquation
  | @call f args ordinary nonempty settled ih =>
      have same : regionInstances atoms f args = regionBodies atoms f args :=
        regionInstances_of_ground fun b member => (settles_facts (settled b member)).ground
      refine .call ordinary (by rw [same]; exact nonempty) fun b member => ?_
      rw [same] at member
      exact ih b member

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open WholeRunWords.Double (noHost)

/-- `twice`, `swap`, `wrap` and `box`, `both` (two rows), and `id` all use their variables. -/
def varRows : List Atom :=
  [rule (app "twice" [.var "x"]) (app "pair" [.var "x", .var "x"]),
   rule (app "swap" [.var "x", .var "y"]) (app "pair" [.var "y", .var "x"]),
   rule (app "wrap" [.var "x"]) (app "box" [.var "x"]),
   rule (app "box" [.var "y"]) (app "boxed" [.var "y"]),
   rule (app "both" [.var "x"]) (app "left" [.var "x"]),
   rule (app "both" [.var "x"]) (app "right" [.var "x"]),
   rule (app "id" [.var "x"]) (.var "x")]

theorem typeVars_vars : ∀ xs : List String, TypeSubst.typeVarsList (xs.map Atom.var) = xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, TypeSubst.typeVarsList, TypeSubst.typeVars, List.singleton_append,
        typeVars_vars xs]

theorem bound_rule (f : String) (xs : List String) {rhs : Atom}
    (vars : ∀ x ∈ TypeSubst.typeVars rhs, x ∈ xs) (flat : FlatBody rhs) :
    RegionsWithVariables.ConsFreeHeads (rule (app f (xs.map Atom.var)) rhs) ∧
      BoundRow (rule (app f (xs.map Atom.var)) rhs) := by
  refine ⟨rule_consFree fun a member => ?_, fun lhs rhs' same => ?_⟩
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
    exact .var x
  · cases same
    refine ⟨fun x member => ?_, flat⟩
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append, typeVars_vars]
    exact vars x member

theorem var_items (names : List String) : ∀ u ∈ names.map Atom.var, FlatItem u := by
  intro u member
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
  exact .var x

theorem var_program : BoundProgram varRows := by
  intro row member
  simp only [varRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bound_rule "twice" ["x"] (by decide)
      (.call "pair" [.var "x", .var "x"] (by decide) (var_items ["x", "x"]))
  · exact bound_rule "swap" ["x", "y"] (by decide)
      (.call "pair" [.var "y", .var "x"] (by decide) (var_items ["y", "x"]))
  · exact bound_rule "wrap" ["x"] (by decide) (.call "box" [.var "x"] (by decide) (var_items ["x"]))
  · exact bound_rule "box" ["y"] (by decide) (.call "boxed" [.var "y"] (by decide) (var_items ["y"]))
  · exact bound_rule "both" ["x"] (by decide) (.call "left" [.var "x"] (by decide) (var_items ["x"]))
  · exact bound_rule "both" ["x"] (by decide)
      (.call "right" [.var "x"] (by decide) (var_items ["x"]))
  · exact bound_rule "id" ["x"] (by decide) (.item (.var "x"))

theorem sym_data (name : String) (notEmpty : name ≠ "Empty") (notError : name ≠ "Error") :
    DataAtom (sym name) :=
  .symbol notEmpty notError

theorem a_data : ∀ v ∈ [sym "a"], DataAtom v := by
  intro v member
  simp only [List.mem_singleton] at member
  subst member
  exact sym_data "a" (by decide) (by decide)

theorem ab_data (first second : String) (one : first ≠ "Empty" ∧ first ≠ "Error")
    (two : second ≠ "Empty" ∧ second ≠ "Error") : ∀ v ∈ [sym first, sym second], DataAtom v := by
  intro v member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact sym_data first one.1 one.2
  · exact sym_data second two.1 two.2

/-- **Positive control helper**: a settling call whose PeTTa run has finished at `fuel` with
`expected`: a complete HE run exists, and every complete HE run publishes `expected`. -/
theorem every_run_control {atoms : List Atom} {c : Atom} (program : BoundProgram atoms)
    (settles : SettlesV noHost atoms c) (fuel : Nat) {expected : List Atom}
    (computed : Streaming.values (Streaming.advance (translate atoms) fuel
      (Streaming.enter { state := store atoms } c)) = expected)
    (finished : (Streaming.advance (translate atoms) fuel
      (Streaming.enter { state := store atoms } c)).agenda.length = 0) (policy : Policy) :
    (∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList atoms) c Atom.undefinedType)
        ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = expected := by
  obtain ⟨⟨heAnswers, path, _⟩, _⟩ := answer_bags_every_run_v noHost policy program settles
  obtain ⟨N, every⟩ := every_complete_run_v noHost raw_answers raw_contract policy program settles
  refine ⟨⟨heAnswers, path⟩, fun emitted run => ?_⟩
  have later := every (max N fuel) (le_max_left _ _) emitted run
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

theorem pair_constructor (args : List Atom) (data : ∀ v ∈ args, DataAtom v)
    (untyped : (Space.ofList varRows).atoms.filter (typeRegion (.symbol "pair")) = [])
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol "pair" :: args)) = false)
    (notControl : Unifying.sourceControlForm (.expression (.symbol "pair" :: args)) = false) :
    SettlesV noHost varRows (app "pair" args) :=
  .constructor ⟨sym_data "pair" (by decide) (by decide), data, untyped, fun impossible => impossible,
    notInstruction, by decide, by decide, notControl, by decide, by decide⟩ (by decide +kernel)

/-- **`(twice a)` settles after substitution**: its one instance is `(pair a a)`. -/
theorem twice_settles : SettlesV noHost varRows (app "twice" [sym "a"]) := by
  have instances : regionInstances varRows "twice" [sym "a"] = [app "pair" [sym "a", sym "a"]] := by
    decide +kernel
  refine .call ⟨sym_data "twice" (by decide) (by decide), a_data, by decide +kernel,
    fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
    by decide, by decide⟩ (by rw [instances]; simp) ?_
  rw [instances]
  intro b member
  simp only [List.mem_singleton] at member
  subst member
  exact pair_constructor _ (ab_data "a" "a" ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Positive control: a repeated variable.** `(twice a)` on `{(= (twice $x) (pair $x $x)), …}`:
a complete HE run exists, every complete HE run publishes `(pair a a)`, and PeTTa's run gives
`(pair a a)`. -/
theorem twice_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList varRows) (app "twice" [sym "a"]) Atom.undefinedType)
        ⟨Space.ofList varRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList varRows) (app "twice" [sym "a"]) Atom.undefinedType)
          ⟨Space.ofList varRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "pair" [sym "a", sym "a"]]) ∧
      Streaming.values (Streaming.advance (translate varRows) 60
        (Streaming.enter { state := store varRows } (app "twice" [sym "a"]))) =
        [app "pair" [sym "a", sym "a"]] := by
  have computed : Streaming.values (Streaming.advance (translate varRows) 60
      (Streaming.enter { state := store varRows } (app "twice" [sym "a"]))) =
      [app "pair" [sym "a", sym "a"]] := by decide +kernel
  exact ⟨every_run_control var_program twice_settles 60 computed (by decide +kernel) policy, computed⟩

/-- **Positive control: two variables used in the other order.** `(swap a b)` gives `(pair b a)`
on every complete HE run and in PeTTa. -/
theorem swap_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList varRows) (app "swap" [sym "a", sym "b"]) Atom.undefinedType)
        ⟨Space.ofList varRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList varRows) (app "swap" [sym "a", sym "b"]) Atom.undefinedType)
          ⟨Space.ofList varRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "pair" [sym "b", sym "a"]]) ∧
      Streaming.values (Streaming.advance (translate varRows) 60
        (Streaming.enter { state := store varRows } (app "swap" [sym "a", sym "b"]))) =
        [app "pair" [sym "b", sym "a"]] := by
  have instances : regionInstances varRows "swap" [sym "a", sym "b"] =
      [app "pair" [sym "b", sym "a"]] := by decide +kernel
  have settles : SettlesV noHost varRows (app "swap" [sym "a", sym "b"]) := by
    refine .call ⟨sym_data "swap" (by decide) (by decide),
      ab_data "a" "b" ⟨by decide, by decide⟩ ⟨by decide, by decide⟩, by decide +kernel,
      fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
      by decide, by decide⟩ (by rw [instances]; simp) ?_
    rw [instances]
    intro b member
    simp only [List.mem_singleton] at member
    subst member
    exact pair_constructor _ (ab_data "b" "a" ⟨by decide, by decide⟩ ⟨by decide, by decide⟩)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have computed : Streaming.values (Streaming.advance (translate varRows) 60
      (Streaming.enter { state := store varRows } (app "swap" [sym "a", sym "b"]))) =
      [app "pair" [sym "b", sym "a"]] := by decide +kernel
  exact ⟨every_run_control var_program settles 60 computed (by decide +kernel) policy, computed⟩

/-- **Positive control: a body that calls a defined function on its variable.** `(wrap a)` reads
`(box a)`, whose instance is `(boxed a)`: every complete HE run and PeTTa give `(boxed a)`. -/
theorem wrap_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList varRows) (app "wrap" [sym "a"]) Atom.undefinedType)
        ⟨Space.ofList varRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList varRows) (app "wrap" [sym "a"]) Atom.undefinedType)
          ⟨Space.ofList varRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "boxed" [sym "a"]]) ∧
      Streaming.values (Streaming.advance (translate varRows) 80
        (Streaming.enter { state := store varRows } (app "wrap" [sym "a"]))) =
        [app "boxed" [sym "a"]] := by
  have wrapInstances : regionInstances varRows "wrap" [sym "a"] = [app "box" [sym "a"]] := by
    decide +kernel
  have boxInstances : regionInstances varRows "box" [sym "a"] = [app "boxed" [sym "a"]] := by
    decide +kernel
  have boxSettles : SettlesV noHost varRows (app "box" [sym "a"]) := by
    refine .call ⟨sym_data "box" (by decide) (by decide), a_data, by decide +kernel,
      fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
      by decide, by decide⟩ (by rw [boxInstances]; simp) ?_
    rw [boxInstances]
    intro b member
    simp only [List.mem_singleton] at member
    subst member
    exact .constructor ⟨sym_data "boxed" (by decide) (by decide), a_data, by decide +kernel,
      fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
      by decide, by decide⟩ (by decide +kernel)
  have settles : SettlesV noHost varRows (app "wrap" [sym "a"]) := by
    refine .call ⟨sym_data "wrap" (by decide) (by decide), a_data, by decide +kernel,
      fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
      by decide, by decide⟩ (by rw [wrapInstances]; simp) ?_
    rw [wrapInstances]
    intro b member
    simp only [List.mem_singleton] at member
    subst member
    exact boxSettles
  have computed : Streaming.values (Streaming.advance (translate varRows) 80
      (Streaming.enter { state := store varRows } (app "wrap" [sym "a"]))) =
      [app "boxed" [sym "a"]] := by decide +kernel
  exact ⟨every_run_control var_program settles 80 computed (by decide +kernel) policy, computed⟩

/-- **Positive control: two matching rows use the same variable.** `(both a)` gives `(left a)` and
`(right a)`, in row order, on every complete HE run and in PeTTa. -/
theorem both_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList varRows) (app "both" [sym "a"]) Atom.undefinedType)
        ⟨Space.ofList varRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList varRows) (app "both" [sym "a"]) Atom.undefinedType)
          ⟨Space.ofList varRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "left" [sym "a"], app "right" [sym "a"]]) ∧
      Streaming.values (Streaming.advance (translate varRows) 80
        (Streaming.enter { state := store varRows } (app "both" [sym "a"]))) =
        [app "left" [sym "a"], app "right" [sym "a"]] := by
  have instances : regionInstances varRows "both" [sym "a"] =
      [app "left" [sym "a"], app "right" [sym "a"]] := by decide +kernel
  have settles : SettlesV noHost varRows (app "both" [sym "a"]) := by
    refine .call ⟨sym_data "both" (by decide) (by decide), a_data, by decide +kernel,
      fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
      by decide, by decide⟩ (by rw [instances]; simp) ?_
    rw [instances]
    intro b member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .constructor ⟨sym_data "left" (by decide) (by decide), a_data, by decide +kernel,
        fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
        by decide, by decide⟩ (by decide +kernel)
    · exact .constructor ⟨sym_data "right" (by decide) (by decide), a_data, by decide +kernel,
        fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
        by decide, by decide⟩ (by decide +kernel)
  have computed : Streaming.values (Streaming.advance (translate varRows) 80
      (Streaming.enter { state := store varRows } (app "both" [sym "a"]))) =
      [app "left" [sym "a"], app "right" [sym "a"]] := by decide +kernel
  exact ⟨every_run_control var_program settles 80 computed (by decide +kernel) policy, computed⟩

/-- **Positive control: a body that is a bare variable.** `(id a)` gives `a`. -/
theorem id_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList varRows) (app "id" [sym "a"]) Atom.undefinedType)
        ⟨Space.ofList varRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList varRows) (app "id" [sym "a"]) Atom.undefinedType)
          ⟨Space.ofList varRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "a"]) ∧
      Streaming.values (Streaming.advance (translate varRows) 40
        (Streaming.enter { state := store varRows } (app "id" [sym "a"]))) = [sym "a"] := by
  have instances : regionInstances varRows "id" [sym "a"] = [sym "a"] := by decide +kernel
  have settles : SettlesV noHost varRows (app "id" [sym "a"]) := by
    refine .call ⟨sym_data "id" (by decide) (by decide), a_data, by decide +kernel,
      fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
      by decide, by decide⟩ (by rw [instances]; simp) ?_
    rw [instances]
    intro b member
    simp only [List.mem_singleton] at member
    subst member
    exact .data (sym_data "a" (by decide) (by decide)) (by decide)
  have computed : Streaming.values (Streaming.advance (translate varRows) 40
      (Streaming.enter { state := store varRows } (app "id" [sym "a"]))) = [sym "a"] := by
    decide +kernel
  exact ⟨every_run_control var_program settles 40 computed (by decide +kernel) policy, computed⟩

/-- **Negative control: the extension is strict.** `(twice a)` does not settle in `AnswerBags`'s
sense: its raw body `(pair $x $x)` has variables. -/
theorem twice_not_settles : ¬ Settles noHost varRows (app "twice" [sym "a"]) := by
  have bodies : regionBodies varRows "twice" [sym "a"] = [app "pair" [.var "x", .var "x"]] := by
    decide +kernel
  have defined : (varRows.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != "twice") = false := by decide +kernel
  intro settles
  cases settles with
  | data data _ => cases data
  | constructor _ noEquation =>
      rw [defined] at noEquation
      cases noEquation
  | call _ _ settled =>
      have body := settled (app "pair" [.var "x", .var "x"]) (by rw [bodies]; simp)
      cases body with
      | data data _ => cases data
      | constructor ordinary _ => cases ordinary.arguments (.var "x") (by simp)
      | call ordinary _ _ => cases ordinary.arguments (.var "x") (by simp)

/-- **Negative control: the program condition is not vacuous.** A body variable that its left side
does not bind, `(= (fresh) $y)`, is outside `BoundRow`. -/
theorem free_not_bound : ¬ BoundRow (rule (app "fresh" []) (.var "y")) := by
  intro bound
  have inside := (bound _ _ rfl).1 "y" (by simp [TypeSubst.typeVars])
  simp [TypeSubst.typeVars, TypeSubst.typeVarsList] at inside

end Controls

#print axioms work_read
#print axioms frontier_sides
#print axioms equations_steps_open
#print axioms he_query_open
#print axioms he_call_open
#print axioms presents_renamed
#print axioms run_clauses_open
#print axioms petta_open_call
#print axioms settlesV_agree
#print axioms answersV_agree
#print axioms callRel_source_open
#print axioms bodies_source_open
#print axioms settlesV_determined_under
#print axioms every_complete_run_v
#print axioms answer_bags_every_run_v
#print axioms settles_settlesV
#print axioms Controls.twice_every_run
#print axioms Controls.swap_every_run
#print axioms Controls.wrap_every_run
#print axioms Controls.both_every_run
#print axioms Controls.id_every_run
#print axioms Controls.twice_not_settles
#print axioms Controls.free_not_bound

end BoundVariables

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
