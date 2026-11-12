import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.MarkedValues

/-!
# Variables bound to compound values: recursion over data, on every run

`NestedCalls` compares HE and PeTTa on bodies that are trees of calls, but only on calls whose
arguments are data atoms. The classic recursive program is excluded: Peano addition

  `(= (add Z $y) $y)`, `(= (add (S $x) $y) (S (add $x $y)))`, `(add (S (S Z)) (S Z))`

binds `$x` to `(S Z)` and `$y` to `(S Z)`, values that are themselves expressions.

* **HE** evaluates the arguments first; their results carry evaluation marks (under `Policy.ready`
  every successful expression result is held), the unifier binds `$x` to a marked sub-value, and the
  read body keeps those marks. `MarkedValues` shows that the read is a *marked value* of PeTTa's
  instance (`work_read_K`) and that HE's evaluation and its source semantics are the same on every
  marked presentation (`HEEvaluatesM`, `DeterminedM`).
* **PeTTa** matches `(S $x)` against `(S (S Z))`, binds `$x` to `(S Z)`, and runs the renamed body;
  a variable bound to a value returns it without evaluating it again (`Unifying.Transition
  .value_variable`). `ShowsK` presents a tree whose variables are bound to values; `PeTTaOverK`
  evaluates every such presentation under every extension of a floor of bindings.

## Results

* `SettlesK t L`: `t` settles with answers `L`: a data atom; a constructor node over settling
  arguments; a call of a defined head over settling arguments whose every combination of answers
  has a nonempty region of settling instances. The answers of arguments may be any values of the
  program (`settlesK_values`); `NestedCalls.SettlesC` asked for data atoms. A condition on the program
  only, never on a run or an answer.
* `settlesK_agree`: HE evaluates every marked presentation of `t` to `L`, PeTTa every presentation.
* `settlesK_determined`: every derivation of HE's completed relation from every marked presentation
  returns `L`.
* `every_complete_run_k`: a complete HE run exists; every complete HE run (historical lookup, any
  policy) publishes `L`; PeTTa's streaming run yields `L` from some fuel on.
* `settlesC_settlesK`: the extension is conservative.

## Controls

* `Controls.add_every_run` (positive): `(add (S (S Z)) (S Z))` gives `(S (S (S Z)))` on every
  complete HE run, under every policy, and in PeTTa (fuel 80, computed by the kernel).
* `Controls.add_not_settlesC` (negative): the same call lies outside `NestedCalls`'s fragment, so the
  extension is strict.
* `Controls.add_z_every_run` (positive): the body `$y` alone, bound to `(S Z)`, is delivered or
  evaluated, never re-entered wrongly: `(add Z (S Z))` gives `(S Z)` on every run.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace CompoundBindings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load observe)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (applyTypeValuation renameTypeVars)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues

variable {dispatch : GroundedDispatch}

/-! ## Lists -/

theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ S l m
  | [], [], .nil, _ => .nil
  | a :: _, b :: _, .cons here rest, each =>
      .cons (each a List.mem_cons_self b here)
        (forall₂_imp_mem rest fun a' member => each a' (List.mem_cons_of_mem _ member))

theorem zip_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ p ∈ l.zip m, R p.1 p.2
  | [], [], .nil, p, member => by cases member
  | a :: _, b :: _, .cons here rest, p, member => by
      rw [List.zip_cons_cons] at member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact here
      · exact zip_of_forall₂ rest p inRest

/-- Every member of a combination comes from the corresponding answer list. -/
theorem combos_all {P : Atom → Prop} : ∀ {Ls : List (List Atom)}, (∀ L ∈ Ls, ∀ a ∈ L, P a) →
    ∀ c ∈ combos Ls, ∀ a ∈ c, P a
  | [], _, c, member => by
      simp only [combos, List.mem_singleton] at member
      subst member
      intro a inside
      cases inside
  | L :: Ls, each, c, member => by
      obtain ⟨r, here, inner⟩ := List.mem_flatMap.mp member
      obtain ⟨c', later, rfl⟩ := List.mem_map.mp inner
      intro a inside
      rcases List.mem_cons.mp inside with rfl | inRest
      · exact each L List.mem_cons_self a here
      · exact combos_all (fun L' member' => each L' (List.mem_cons_of_mem _ member')) c' later a
          inRest

/-! ## Trees whose variables are bound to values -/

/-- **`b` shows the ground term `t` under `σ`**: a tree whose variables are bound to values of the
program, instantiated to `t`. -/
structure ShowsK (dispatch : GroundedDispatch) (atoms : List Atom) (σ : Subst) (b t : Atom) : Prop where
  tree : TreeBody b
  bound : ∀ x ∈ TypeSubst.typeVars b, NestedValues.Value dispatch atoms (applySubst σ (.var x))
  instantiates : applySubst σ b = t

theorem lookup_of_value {atoms : List Atom} {σ : Subst} {x : String}
    (value : NestedValues.Value dispatch atoms (applySubst σ (.var x))) :
    σ.lookup x = some (applySubst σ (.var x)) := by
  rw [read_var] at value ⊢
  cases found : σ.lookup x with
  | none =>
      simp only [found, Option.getD_none] at value
      exact (value_not_var value).elim
  | some a => rfl

theorem read_kept_K {atoms : List Atom} {σ σ' : Subst} (keeps : Keeps σ σ') {x : String}
    (value : NestedValues.Value dispatch atoms (applySubst σ (.var x))) :
    applySubst σ' (.var x) = applySubst σ (.var x) := by
  rw [read_var σ' x, keeps x _ (lookup_of_value value), Option.getD_some]

/-- Bindings that keep `σ` read a tree bound under `σ` to values as `σ` does. -/
theorem applySubst_keeps_K {atoms : List Atom} {σ σ' : Subst} (keeps : Keeps σ σ') :
    ∀ {b : Atom}, TreeBody b →
      (∀ x ∈ TypeSubst.typeVars b, NestedValues.Value dispatch atoms (applySubst σ (.var x))) →
      applySubst σ' b = applySubst σ b := by
  intro b tree
  induction tree with
  | @item u flat =>
      intro bound
      cases flat with
      | symbol name => simp [applySubst]
      | grounded value => simp [applySubst]
      | var name => exact read_kept_K keeps (bound name (by simp [TypeSubst.typeVars]))
  | @node g us _ _ ih =>
      intro bound
      rw [applySubst_node, applySubst_node]
      congr 2
      exact List.map_congr_left fun u member =>
        ih u member fun x inU => bound x (mem_node_vars member inU)

theorem ShowsK.keeps {atoms : List Atom} {σ σ' : Subst} {b t : Atom}
    (shown : ShowsK dispatch atoms σ b t) (keeps : Keeps σ σ') : ShowsK dispatch atoms σ' b t := by
  refine ⟨shown.tree, fun x member => ?_, ?_⟩
  · rw [read_kept_K keeps (shown.bound x member)]
    exact shown.bound x member
  · rw [applySubst_keeps_K keeps shown.tree shown.bound]
    exact shown.instantiates

/-- A tree showing a literal is the literal or a variable bound to it. -/
theorem ShowsK.item {atoms : List Atom} {σ : Subst} {b d : Atom}
    (shown : ShowsK dispatch atoms σ b d) (literal : Lit d) : PresentsItem σ b d := by
  have instantiates := shown.instantiates
  cases shown.tree with
  | item flat =>
      cases flat with
      | symbol name =>
          have same : applySubst σ (.symbol name) = .symbol name := by simp [applySubst]
          rw [same] at instantiates
          exact ⟨literal, Or.inl instantiates⟩
      | grounded value =>
          have same : applySubst σ (.grounded value) = .grounded value := by simp [applySubst]
          rw [same] at instantiates
          exact ⟨literal, Or.inl instantiates⟩
      | var name => exact ⟨literal, Or.inr ⟨name, rfl, instantiates⟩⟩
  | node _ _ =>
      rw [applySubst_node] at instantiates
      subst instantiates
      cases literal

/-- **A tree showing a call is a node of the same head whose children show its arguments, or a
variable bound to the call, which is then a value.** -/
theorem ShowsK.node_or_var {atoms : List Atom} {σ : Subst} {b : Atom} {f : String}
    {ts : List Atom} (shown : ShowsK dispatch atoms σ b (.expression (.symbol f :: ts))) :
    (∃ us, b = .expression (.symbol f :: us) ∧ controlHead f = false ∧
        List.Forall₂ (ShowsK dispatch atoms σ) us ts) ∨
      (∃ x, b = .var x ∧ applySubst σ (.var x) = .expression (.symbol f :: ts) ∧
        NestedValues.Value dispatch atoms (.expression (.symbol f :: ts))) := by
  have instantiates := shown.instantiates
  have bound := shown.bound
  cases shown.tree with
  | item flat =>
      cases flat with
      | symbol name => simp [applySubst] at instantiates
      | grounded value => simp [applySubst] at instantiates
      | var name =>
          have value := bound name (by simp [TypeSubst.typeVars])
          rw [instantiates] at value
          exact Or.inr ⟨name, rfl, instantiates, value⟩
  | @node g us notControl children =>
      rw [applySubst_node] at instantiates
      simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at instantiates
      obtain ⟨rfl, rfl⟩ := instantiates
      refine Or.inl ⟨us, rfl, notControl, forall₂_map_self fun u member =>
        ⟨children u member, fun x inU => bound x (mem_node_vars member inU), rfl⟩⟩

theorem shows_ground_K {atoms : List Atom} {σ : Subst} {t : Atom} (tree : TreeBody t)
    (answerable : Answerable t) : ShowsK dispatch atoms σ t t :=
  ⟨tree, fun x member => by
      rw [HERuns.ground_typeVars answerable] at member
      simp at member,
    Unifying.applySubst_ground σ _ answerable.ground⟩

/-! ## PeTTa's evaluation of presentations bound to values -/

/-- **PeTTa evaluates every presentation of `t` whose variables are bound to values to `L`**, under
every frames that deliver each answer under every extension of a floor `σ₀`. -/
def PeTTaOverK (dispatch : GroundedDispatch) (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (σ₀ : Subst) (frames : List Streaming.Frame) (K : Atom → List Atom),
    (∀ v ∈ L, DeliversFrom atoms σ₀ frames K v) →
  ∀ (world : Streaming.World) (σ : Subst), Keeps σ₀ σ → world.state = store atoms →
    world.privateCode = [] → Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (b : Atom), ShowsK dispatch atoms σ b t →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = L.flatMap K ∧
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.evaluate σ b, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

/-- At the root, with frames that deliver under all bindings, `PeTTaOverK` is `PeTTaEvaluates`. -/
theorem over_root_K {atoms : List Atom} {t : Atom} {L : List Atom}
    (evaluates : PeTTaOverK dispatch atoms t L) (self : ∀ σ, ShowsK dispatch atoms σ t t) :
    PeTTaEvaluates atoms t L :=
  fun frames K deliver world σ state privateCode range fresh older answers next =>
    evaluates σ frames K (fun v member world' σ' _ => deliver v member world' σ') world σ
      (Keeps.refl σ) state privateCode range fresh t (self σ) older answers next

/-- **A data atom, every presentation.** -/
theorem over_data_K (atoms : List Atom) {d : Atom} (data : DataAtom d) :
    PeTTaOverK dispatch atoms d [d] := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh b shown older answers next
  have item := shown.item (lit_of_data data)
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver d List.mem_cons_self world σ keeps state
    privateCode range fresh older answers next
  exact ⟨uses, out, grown, by simp [valuesOut],
    .head (PeTTaOpenRuns.evaluate_item world σ item frames older answers next) path⟩

/-- **A variable bound to a value returns it**, without evaluating it again, and the frames deliver
it. -/
theorem petta_var_value {atoms : List Atom} {t : Atom} {σ₀ : Subst} {frames : List Streaming.Frame}
    {K : Atom → List Atom} (deliver : DeliversFrom atoms σ₀ frames K t) {world : Streaming.World}
    {σ : Subst} (keeps : Keeps σ₀ σ) (state : world.state = store atoms)
    (privateCode : world.privateCode = []) (range : Unifying.GroundRange σ)
    (fresh : ∀ k, Unifying.FreshFor (world.uses + k) σ) {x : String}
    (bound : applySubst σ (.var x) = t) (older : List Streaming.Job)
    (answers : List Unifying.Answer) (next : Nat) :
    ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
      out.map (fun answer => Unifying.resolve answer.bindings answer.value) = [t].flatMap K ∧
      PeTTaRuns.PSteps (translate atoms)
        ⟨world, .execute ⟨.evaluate σ (.var x), frames⟩ :: older, answers, next⟩
        ⟨{world with uses := uses}, older, answers ++ out, next⟩ := by
  have step : Streaming.Transition (translate atoms)
      ⟨world, .execute ⟨.evaluate σ (.var x), frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.returned [⟨Unifying.resolve σ (.var x), σ⟩], frames⟩ :: older, answers,
        next⟩ := .phase rfl rfl (.value_variable rfl) (.plain rfl)
  have resolved : Unifying.resolve σ (.var x) = t := bound
  rw [resolved] at step
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver world σ keeps state privateCode range fresh
    older answers next
  exact ⟨uses, out, grown, by simp [valuesOut], .head step path⟩

/-! ## The renamed bodies, with variables bound to values -/

/-- **A renamed tree shows its instance**, under the matching bindings renamed for the use and
followed by the caller's, when the call's arguments are values. -/
theorem shows_renamed_K {atoms : List Atom} {use : Nat} {bound σ : Subst}
    (fresh : Unifying.FreshFor use σ) {ps args : List Atom}
    (argsValues : ∀ a ∈ args, NestedValues.Value dispatch atoms a)
    (instantiated : ps.map (applyTypeValuation (RegionsWithVariables.asValuation bound)) = args) :
    ∀ {body : Atom}, TreeBody body →
      (∀ x ∈ TypeSubst.typeVars body, x ∈ TypeSubst.typeVarsList ps) →
      ShowsK dispatch atoms (Unifying.renameKeys use bound ++ σ) (Unifying.rename use body)
        (applySubst bound body) := by
  intro body tree
  induction tree with
  | @item u flat =>
      intro varsBound
      cases flat with
      | symbol name =>
          have renamedSymbol : Unifying.rename use (.symbol name) = .symbol name := by
            simp [Unifying.rename]
          rw [renamedSymbol]
          refine ⟨.item (.symbol name), fun x member => ?_, by simp [applySubst]⟩
          simp [TypeSubst.typeVars] at member
      | grounded value =>
          have renamedGrounded : Unifying.rename use (.grounded value) = .grounded value := by
            simp [Unifying.rename]
          rw [renamedGrounded]
          refine ⟨.item (.grounded value), fun x member => ?_, by simp [applySubst]⟩
          simp [TypeSubst.typeVars] at member
      | var name =>
          have renamedVar : Unifying.rename use (.var name) = .var (Unifying.freshName use name) := by
            simp [Unifying.rename]
          rw [renamedVar]
          have inPs := varsBound name (by simp [TypeSubst.typeVars])
          have value := vars_of_values instantiated argsValues name inPs
          have looked : (Unifying.renameKeys use bound ++ σ).lookup (Unifying.freshName use name) =
              bound.lookup name := Unifying.lookup_append_renamed fresh name
          obtain ⟨held, found⟩ : ∃ held, bound.lookup name = some held := by
            cases found : bound.lookup name with
            | none =>
                have unbound : RegionsWithVariables.asValuation bound name = .var name := by
                  simp [RegionsWithVariables.asValuation, found]
                rw [unbound] at value
                exact (value_not_var value).elim
            | some held => exact ⟨held, rfl⟩
          have readRenamed : applySubst (Unifying.renameKeys use bound ++ σ)
              (.var (Unifying.freshName use name)) = held := by
            rw [read_var, looked, found, Option.getD_some]
          have readBound : applySubst bound (.var name) = held := by
            rw [read_var, found, Option.getD_some]
          have heldValue : NestedValues.Value dispatch atoms held := by
            simpa [RegionsWithVariables.asValuation, found] using value
          refine ⟨.item (.var _), fun x member => ?_, by rw [readRenamed, readBound]⟩
          simp only [TypeSubst.typeVars, List.mem_singleton] at member
          subst member
          rw [readRenamed]
          exact heldValue
  | @node g us notControl children ih =>
      intro varsBound
      have childBound : ∀ u ∈ us, ∀ x ∈ TypeSubst.typeVars u, x ∈ TypeSubst.typeVarsList ps :=
        fun u member x inU => varsBound x (mem_node_vars member inU)
      have each := fun u member => ih u member (childBound u member)
      have renameList : ∀ xs : List Atom,
          Unifying.rename.renameList use xs = xs.map (Unifying.rename use) := by
        intro xs
        induction xs with
        | nil => simp [Unifying.rename.renameList]
        | cons x xs restIh => simp [Unifying.rename.renameList, restIh]
      have renamed : Unifying.rename use (.expression (.symbol g :: us)) =
          .expression (.symbol g :: us.map (Unifying.rename use)) := by
        simp only [Unifying.rename, Unifying.rename.renameList, renameList]
      rw [renamed, applySubst_node]
      refine ⟨.node notControl fun u member => ?_, fun x member => ?_, ?_⟩
      · obtain ⟨w, inUs, rfl⟩ := List.mem_map.mp member
        exact (each w inUs).tree
      · simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append] at member
        obtain ⟨u, inMapped, inU⟩ := mem_typeVarsList member
        obtain ⟨w, inUs, rfl⟩ := List.mem_map.mp inMapped
        exact (each w inUs).bound x inU
      · rw [applySubst_node, List.map_map]
        congr 2
        exact List.map_congr_left fun w member => (each w member).instantiates

/-- Each selected equation of a call program shows its instance, for value arguments. -/
theorem selected_shows_K {atoms : List Atom} (program : CallProgram atoms)
    {e : SpaceSemantics.Equation} (live : e ∈ atoms.filterMap LiveEquations.equationOfRow)
    {args : List Atom} (argsValues : ∀ a ∈ args, NestedValues.Value dispatch atoms a)
    {bound : Subst}
    (matched : SpaceSemantics.matchValue.matchValues [] e.arguments args = some bound)
    (use : Nat) {σ : Subst} (fresh : Unifying.FreshFor use σ) :
    ShowsK dispatch atoms (Unifying.renameKeys use bound ++ σ) (Unifying.rename use e.body)
      (applySubst bound e.body) := by
  obtain ⟨row, inAtoms, found⟩ := List.mem_filterMap.mp live
  have shape := LiveEquations.equationOfRow_eq_some found
  obtain ⟨consFree, callRow⟩ := program row inAtoms
  subst shape
  obtain ⟨varsBound, tree⟩ := callRow _ e.body rfl
  obtain ⟨h, ps, leftShape, psFree⟩ := consFree _ e.body rfl
  simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at leftShape
  obtain ⟨_, rfl⟩ := leftShape
  obtain ⟨_, _, instanceArgs⟩ := RegionsWithVariables.sound_list e.arguments
    (fun p m => RegionsWithVariables.sound (psFree p m)) [] bound args matched
  have inArgs : ∀ x ∈ TypeSubst.typeVars e.body, x ∈ TypeSubst.typeVarsList e.arguments :=
    fun x member => by
      have := varsBound x member
      simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using this
  exact shows_renamed_K fresh argsValues
    (instanceArgs bound (RegionsWithVariables.Extends.refl bound)) tree inArgs

theorem run_clauses_K {atoms : List Atom} (program : CallProgram atoms) {σ₀ σ : Subst}
    (keeps : Keeps σ₀ σ) {values : List Atom}
    (valuesValues : ∀ v ∈ values, NestedValues.Value dispatch atoms v)
    (range : Unifying.GroundRange σ) (frames : List Streaming.Frame) (K : Atom → List Atom) :
    ∀ (chosen : List SpaceSemantics.Equation) (use : Nat) (Ls : List (List Atom)),
      (∀ e ∈ chosen, e ∈ atoms.filterMap LiveEquations.equationOfRow) →
      List.Forall₂ (fun b L => PeTTaOverK dispatch atoms b L) (matchingInstances values chosen) Ls →
      (∀ v ∈ Ls.flatten, DeliversFrom atoms σ₀ frames K v) →
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
          exact run_clauses_K program keeps valuesValues range frames K rest (use + 1) Ls liveRest
            related deliver world state privateCode enough' (fun k => by
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
                fun v member => (value_answerable (valuesValues v member)).ground
              have boundRange := PeTTaRuns.matchValues_groundRange e.arguments values [] bound
                (fun _ member => by cases member) groundValues matched
              have below : use < world.uses := by omega
              have outerFresh : ∀ k, Unifying.FreshFor (world.uses + k) σ := fun k => by
                have shifted := fresh (world.uses - use + k)
                rwa [show use + (world.uses - use + k) = world.uses + k by omega] at shifted
              have useFresh : Unifying.FreshFor use σ := by simpa using fresh 0
              have presented := selected_shows_K program (live e List.mem_cons_self) valuesValues
                matched use useFresh
              obtain ⟨uses₁, out₁, grown₁, values₁, path₁⟩ := here σ₀ frames K
                (fun v member => deliver v (by
                  rw [List.flatten_cons]
                  exact List.mem_append_left _ member)) world
                (Unifying.renameKeys use bound ++ σ) (keeps.trans (keeps_renamed useFresh)) state
                privateCode (PeTTaRuns.groundRange_renamed boundRange range)
                (PeTTaRuns.freshFor_renamed below outerFresh) _ presented
                (((Unifying.renamedClauses σ values (use + 1) rest).map fun control =>
                  .execute ⟨control, frames⟩) ++ older) answers next
              obtain ⟨uses₂, out₂, grown₂, values₂, path₂⟩ := run_clauses_K program keeps
                valuesValues range frames K rest (use + 1) Ls' liveRest later
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

/-- **An application of a defined head to values**: PeTTa selects the matching clauses and runs
each renamed body, in row order. -/
theorem applies_defined_K {atoms : List Atom} (program : CallProgram atoms) {f : String}
    {vals : List Atom} (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (valsValues : ∀ v ∈ vals, NestedValues.Value dispatch atoms v)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = vals.length)
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => PeTTaOverK dispatch atoms b L)
      (regionInstances atoms f vals) Ls) :
    AppliesOver atoms (.function f) vals Ls.flatten := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh index older answers next
  obtain ⟨e, live, eHead, arity⟩ := defined
  have groundVals : ∀ v ∈ vals, isGroundAtom v = true :=
    fun v member => (value_answerable (valsValues v member)).ground
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
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [eHead]⟩, arity⟩
  have related : List.Forall₂ (fun b L => PeTTaOverK dispatch atoms b L)
      (matchingInstances vals chosen) Ls := by
    rw [chosenEq, ← regionInstances_eq]
    exact bodies
  have chosenLive : ∀ e' ∈ chosen, e' ∈ atoms.filterMap LiveEquations.equationOfRow :=
    fun e' member => (List.mem_filter.mp member).1
  obtain ⟨uses, out, grown, valuesOut, path⟩ := run_clauses_K program keeps valsValues range frames
    K chosen world.uses Ls chosenLive related deliver
    {world with uses := world.uses + chosen.length} state privateCode (by simp only; omega) fresh
    older answers next
  refine ⟨uses, out, by simp only at grown; omega, valuesOut, ?_⟩
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
  refine .head (PeTTaRuns.apply_equations world σ vals index notIO notNative applied frames older
    answers next) ?_
  refine .head (PeTTaRuns.alternatives _ _ frames older answers next) ?_
  exact path

/-! ## PeTTa's argument traversal, calls and constructor nodes -/

/-- **PeTTa's argument traversal streams, under extending bindings**, on presentations whose
variables are bound to values. -/
theorem args_over_K (atoms : List Atom) (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target)
    (demanded : ∀ i, PeTTaRuns.rawDemand (translate atoms) target i = false) :
    ∀ (ts : List Atom) (Ls : List (List Atom)),
      List.Forall₂ (fun t L => PeTTaOverK dispatch atoms t L) ts Ls →
      ∀ (held : List Atom) (A : List Atom → List Atom),
        (∀ c ∈ combos Ls, AppliesOver atoms target (held ++ c) (A c)) →
        ∀ (σ₀ : Subst) (frames : List Streaming.Frame) (K : Atom → List Atom),
          (∀ c ∈ combos Ls, ∀ v ∈ A c, DeliversFrom atoms σ₀ frames K v) →
          ∀ (world : Streaming.World) (σ : Subst), Keeps σ₀ σ → world.state = store atoms →
            world.privateCode = [] → Unifying.GroundRange σ →
            (∀ k, Unifying.FreshFor (world.uses + k) σ) →
            ∀ (us : List Atom), List.Forall₂ (ShowsK dispatch atoms σ) us ts →
            ∀ (index : Nat) (older : List Streaming.Job) (answers : List Unifying.Answer)
              (next : Nat),
              ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
                out.map (fun answer => Unifying.resolve answer.bindings answer.value) =
                  ((combos Ls).flatMap A).flatMap K ∧
                PeTTaRuns.PSteps (translate atoms)
                  ⟨world, .execute ⟨.arguments σ target us held index, frames⟩ :: older, answers,
                    next⟩
                  ⟨{world with uses := uses}, older, answers ++ out, next⟩
  | [], Ls, related, held, A, apps, σ₀, frames, K, deliver, world, σ, keeps, state, privateCode,
      range, fresh, us, shown, index, older, answers, next => by
      cases related
      cases shown
      have only : ([] : List Atom) ∈ combos [] := by simp [combos]
      have app := apps [] only
      rw [List.append_nil] at app
      obtain ⟨uses, out, grown, valuesOut, path⟩ := app σ₀ frames K
        (fun v member => deliver [] only v member) world σ keeps state privateCode range fresh index
        older answers next
      exact ⟨uses, out, grown, by rw [valuesOut]; simp [combos], path⟩
  | t :: ts, Ls, related, held, A, apps, σ₀, frames, K, deliver, world, σ, keeps, state,
      privateCode, range, fresh, us, shown, index, older, answers, next => by
      obtain ⟨L, Ls', here, later, rfl⟩ := List.forall₂_cons_left_iff.mp related
      obtain ⟨u, us', first, rest, rfl⟩ := List.forall₂_cons_right_iff.mp shown
      have deliverArg : ∀ r ∈ L, DeliversFrom atoms σ
          (.source (.argument target us' held index) :: frames)
          (fun r => ((combos Ls').flatMap fun c => A (r :: c)).flatMap K) r := by
        intro r rMem world' σ' keeps' state' privateCode' range' fresh' older' answers' next'
        obtain ⟨uses, out, grown, valuesOut, path⟩ := args_over_K atoms target demanded ts Ls'
          later (held ++ [r]) (fun c => A (r :: c))
          (fun c cMem => by
            have app := apps (r :: c) (mem_combos_cons rMem cMem)
            rwa [List.append_cons] at app)
          σ₀ frames K (fun c cMem v vMem => deliver (r :: c) (mem_combos_cons rMem cMem) v vMem)
          world' σ' (keeps.trans keeps') state' privateCode' range' fresh' us'
          (rest.imp fun _ _ shownRest => shownRest.keeps keeps') (index + 1) older' answers' next'
        refine ⟨uses, out, grown, valuesOut, ?_⟩
        refine .head (PeTTaRuns.return_argument world' ⟨r, σ'⟩ target us' held index frames older'
          answers' next') ?_
        refine .head (PeTTaRuns.alternatives world' _ frames older' answers' next') ?_
        exact path
      obtain ⟨uses, out, grown, valuesOut, path⟩ := here σ _ _ deliverArg world σ (Keeps.refl σ)
        state privateCode range fresh u first older answers next
      refine ⟨uses, out, grown, by rw [valuesOut, flatMap_combos], ?_⟩
      exact .head (PeTTaRuns.evaluate_argument world σ target u us' held index (demanded index)
        frames older answers next) path

/-- A value is never a call of a head with an equation. -/
theorem value_not_defined {atoms : List Atom} {f : String} {ts : List Atom}
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (value : NestedValues.Value dispatch atoms (.expression (.symbol f :: ts))) : False := by
  obtain ⟨e, live, eHead⟩ := defined
  cases value with
  | data data => cases data
  | node head _ =>
      have different := List.all_eq_true.mp head.noEquation e live
      simp [eHead] at different

/-- **A call of a defined head, every presentation**: a variable cannot present it (it is no value);
a node runs the call entry, the streaming argument traversal and the application. -/
theorem over_call_K {atoms : List Atom} {f : String} {ts : List Atom} {Ls : List (List Atom)}
    (head : NodeHead dispatch atoms f)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (args : List.Forall₂ (fun t L => PeTTaOverK dispatch atoms t L) ts Ls) (A : List Atom → List Atom)
    (apps : ∀ c ∈ combos Ls, AppliesOver atoms (.function f) c (A c)) :
    PeTTaOverK dispatch atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap A) := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh b shown older answers next
  rcases shown.node_or_var with ⟨us, rfl, notControl, shownArgs⟩ | ⟨x, rfl, _, value⟩
  · have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
        (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
        true := by
      obtain ⟨e, live, eHead⟩ := defined
      rw [privateCode, head.notIO, head.notNative]
      simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
      exact List.any_eq_true.mpr ⟨e, live, by simp [eHead]⟩
    obtain ⟨uses, out, grown, valuesOut, path⟩ := args_over_K atoms (.function f)
      (fun index => argumentIsRaw_false head.notNative head.untyped index) ts Ls args [] A
      (fun c cMem => by
        rw [List.nil_append]
        exact apps c cMem)
      σ₀ frames K (fun c cMem v vMem => deliver v (List.mem_flatMap.mpr ⟨c, cMem, vMem⟩)) world σ
      keeps state privateCode range fresh us shownArgs 0 older answers next
    exact ⟨uses, out, grown, valuesOut,
      .head (PeTTaRuns.call_enter world σ head.notCollapse head.notOnce
        (sourceControlForm_of_head notControl us) callable frames older answers next) path⟩
  · exact (value_not_defined defined value).elim

/-- **A constructor node, every presentation**: a node evaluates its head and arguments in turn and
builds each combination; a variable bound to the node, which is then a value, returns it. -/
theorem over_build_K {atoms : List Atom} {f : String} {ts : List Atom} {Ls : List (List Atom)}
    (head : NodeHead dispatch atoms f)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true)
    (args : List.Forall₂ (fun t L => PeTTaOverK dispatch atoms t L ∧ ∀ a ∈ L, Answerable a) ts Ls)
    (self : NestedValues.Value dispatch atoms (.expression (.symbol f :: ts)) →
      (combos Ls).flatMap (fun vals => [Atom.expression (Atom.symbol f :: vals)]) =
        [Atom.expression (Atom.symbol f :: ts)]) :
    PeTTaOverK dispatch atoms (.expression (.symbol f :: ts))
      ((combos Ls).flatMap fun vals => [Atom.expression (Atom.symbol f :: vals)]) := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh b shown older answers next
  rcases shown.node_or_var with ⟨us, rfl, notControl, shownArgs⟩ | ⟨x, rfl, bound, value⟩
  · have notCallable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
        (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
        false := by
      rw [privateCode, head.notIO, head.notNative]
      simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
      apply List.any_eq_false.mpr
      intro e member
      have different := List.all_eq_true.mp noEquation e member
      simpa using different
    have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
      intro L member a inside
      obtain ⟨t, both⟩ := forall₂_right_exists args L member
      exact both.2 a inside
    obtain ⟨uses, out, grown, valuesOut, path⟩ := args_over_K atoms .data (fun _ => rfl) ts Ls
      (args.imp fun _ _ both => both.1) [.symbol f] (fun c => [.expression (.symbol f :: c)])
      (fun c cMem => by
        have ground : ∀ v ∈ [Atom.symbol f] ++ c, isGroundAtom v = true := by
          intro v member
          rcases List.mem_append.mp member with inHead | inC
          · rw [List.mem_singleton] at inHead
            subst inHead
            rfl
          · exact (combos_answerable allClean c cMem v inC).ground
        have app := applies_construct atoms ground
        simpa only [List.singleton_append] using app)
      σ₀ frames K (fun c cMem v vMem => deliver v (List.mem_flatMap.mpr ⟨c, cMem, vMem⟩)) world σ
      keeps state privateCode range fresh us shownArgs 1 older answers next
    have entered := PeTTaOpenRuns.argument_open (registry := translate atoms) world σ .data
      (⟨.symbol f, Or.inl rfl⟩ : PresentsItem σ (.symbol f) (.symbol f)) us [] 0 rfl frames older
      answers next
    rw [List.nil_append, Nat.zero_add] at entered
    exact ⟨uses, out, grown, valuesOut,
      .head (PeTTaRuns.data_enter world σ head.notCollapse head.notOnce
        (sourceControlForm_of_head notControl us) notCallable frames older answers next)
        (entered.trans path)⟩
  · have selfEq := self value
    have deliverT : DeliversFrom atoms σ₀ frames K (.expression (.symbol f :: ts)) :=
      deliver _ (by rw [selfEq]; exact List.mem_singleton_self _)
    obtain ⟨uses, out, grown, valuesOut, path⟩ := petta_var_value deliverT keeps state privateCode
      range fresh bound older answers next
    exact ⟨uses, out, grown, by rw [valuesOut, selfEq], path⟩

/-! ## The terms that settle -/

/-- **`t` settles with the answers `L`**: a data atom; a constructor node over settling arguments,
one answer per combination of theirs; a call of a defined head over settling arguments whose every
combination of answers has a nonempty region of settling instances. The arguments' answers may be
any values of the program. A condition on the program, never on a result. -/
inductive SettlesK (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → List Atom → Prop
  | data {d : Atom} : DataAtom d → d ≠ Atom.notReducible → SettlesK dispatch atoms d [d]
  | build {f : String} {ts : List Atom} {Ls : List (List Atom)} : NodeHead dispatch atoms f →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesK dispatch atoms p.1 p.2) →
      SettlesK dispatch atoms (.expression (.symbol f :: ts))
        ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)])
  | call {f : String} {ts : List Atom} {Ls : List (List Atom)} (R : List Atom → List (List Atom)) :
      NodeHead dispatch atoms f →
      (∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f) →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesK dispatch atoms p.1 p.2) →
      (∀ vals ∈ combos Ls, regionInstances atoms f vals ≠ []) →
      (∀ vals ∈ combos Ls, (regionInstances atoms f vals).length = (R vals).length) →
      (∀ vals ∈ combos Ls, ∀ p ∈ (regionInstances atoms f vals).zip (R vals),
        SettlesK dispatch atoms p.1 p.2) →
      SettlesK dispatch atoms (.expression (.symbol f :: ts))
        ((combos Ls).flatMap fun vals => (R vals).flatten)

theorem SettlesK.of_eq {atoms : List Atom} {t : Atom} {L L' : List Atom}
    (settles : SettlesK dispatch atoms t L) (same : L = L') : SettlesK dispatch atoms t L' :=
  same ▸ settles

/-- A node head with no equation is a constructor head. -/
theorem constructor_of_node {atoms : List Atom} {f : String} (head : NodeHead dispatch atoms f)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true) : ConstructorHead dispatch atoms f :=
  ⟨head.head, head.untyped, head.notHost, head.notInstruction, head.notIO, head.notNative,
    head.notControl, noEquation⟩

/-- What every settling term and its answers are: `NestedCalls.Shape`, and every answer is a value. -/
theorem settlesK_shape {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) :
    Shape t L ∧ ∀ a ∈ L, NestedValues.Value dispatch atoms a := by
  induction settles with
  | @data d data _ =>
      refine ⟨⟨answerable_of_data data, ?_, fun rename => ?_, fun a member => ?_⟩, fun a member => ?_⟩
      · cases data with
        | symbol _ _ => exact .item (.symbol _)
        | grounded value => exact .item (.grounded value)
      · cases data <;> simp [renameTypeVars]
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data data
      · rw [List.mem_singleton] at member
        subst member
        exact .data data
  | @build f ts Ls head noEquation length _ ih =>
      have args := forall₂_of_zip
        (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value dispatch atoms a) length ih
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, shape⟩ := forall₂_right_exists args L member
        exact shape.1.answers a inside
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value dispatch atoms a := by
        intro L member a inside
        obtain ⟨t, shape⟩ := forall₂_right_exists args L member
        exact shape.2 a inside
      refine ⟨node_shape head (fun t member => ⟨_, (forall₂_left_exists args t member).choose_spec.1⟩)
        ?_, ?_⟩
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        rw [List.mem_singleton] at inner
        subst inner
        exact app_answerable head.head (combos_answerable allClean vals valsMem)
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        rw [List.mem_singleton] at inner
        subst inner
        exact .node (constructor_of_node head noEquation) (combos_all allValues vals valsMem)
  | @call f ts Ls R head _ length _ _ lengths _ ihArgs ihBodies =>
      have args := forall₂_of_zip
        (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value dispatch atoms a) length ihArgs
      refine ⟨node_shape head (fun t member => ⟨_, (forall₂_left_exists args t member).choose_spec.1⟩)
        ?_, ?_⟩
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        obtain ⟨L, inR, inL⟩ := List.mem_flatten.mp inner
        have regions := forall₂_of_zip
          (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value dispatch atoms a)
          (lengths vals valsMem) (ihBodies vals valsMem)
        obtain ⟨b, shape⟩ := forall₂_right_exists regions L inR
        exact shape.1.answers a inL
      · intro a member
        obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        obtain ⟨L, inR, inL⟩ := List.mem_flatten.mp inner
        have regions := forall₂_of_zip
          (R := fun t L => Shape t L ∧ ∀ a ∈ L, NestedValues.Value dispatch atoms a)
          (lengths vals valsMem) (ihBodies vals valsMem)
        obtain ⟨b, shape⟩ := forall₂_right_exists regions L inR
        exact shape.2 a inL

theorem settlesK_facts {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) : BodyFacts t := by
  have shape := (settlesK_shape settles).1
  have node : ∀ {f : String} {ts : List Atom}, NodeHead dispatch atoms f →
      Shape (.expression (.symbol f :: ts)) L → BodyFacts (.expression (.symbol f :: ts)) := by
    intro f ts head shape
    refine ⟨shape.answerable.closed, fun policy pending => ?_, (fun same => by cases same),
      shape.answerable.notStopped, shape.fixed, shape.answerable.ground⟩
    obtain ⟨⟨body, same⟩, _⟩ := pending
    rw [Entry.Value.erase_ofAtom] at same
    simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact head.notFunction same.1
  cases settles with
  | data data notRefused =>
      exact settles_facts (Settles.data (dispatch := dispatch) (atoms := atoms) data notRefused)
  | build head _ _ _ => exact node head shape
  | call _ head _ _ _ _ _ _ => exact node head shape

theorem zip_singletons : ∀ {ts : List Atom} {Ls : List (List Atom)}, ts.length = Ls.length →
    (∀ p ∈ ts.zip Ls, p.2 = [p.1]) → Ls = ts.map fun t => [t]
  | [], [], _, _ => rfl
  | [], _ :: _, length, _ => by simp at length
  | _ :: _, [], length, _ => by simp at length
  | t :: ts, L :: Ls, length, each => by
      have here := each (t, L) (by simp)
      have rest := zip_singletons (ts := ts) (Ls := Ls) (by simpa using length)
        (fun p member => each p (by simp [member]))
      simp only at here
      rw [here, rest, List.map_cons]

/-- **A value settles only with itself.** -/
theorem settlesK_value_self {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) : NestedValues.Value dispatch atoms t → L = [t] := by
  induction settles with
  | data _ _ => intro _; rfl
  | @build f ts Ls head noEquation length _ ih =>
      intro value
      have each : ∀ t ∈ ts, NestedValues.Value dispatch atoms t := fun t member =>
        value_children value t (List.mem_cons_of_mem _ member)
      have singles : Ls = ts.map fun t => [t] := zip_singletons length fun p member =>
        ih p member (each p.1 (List.of_mem_zip member).1)
      subst singles
      rw [combos_singletons]
      simp
  | call _ _ defined _ _ _ _ _ _ _ =>
      intro value
      exact (value_not_defined defined value).elim

/-- **The extension is conservative**: `NestedCalls`'s settling terms settle here, with the same
answers. -/
theorem settlesC_settlesK {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesC dispatch atoms t L) : SettlesK dispatch atoms t L := by
  induction settles with
  | data data notRefused => exact .data data notRefused
  | build head noEquation length _ ih => exact .build head noEquation length ih
  | call R head defined length _ _ nonempty lengths _ ihArgs ihBodies =>
      exact .call R head defined length ihArgs nonempty lengths ihBodies

/-! ## Both machines -/

section Joint

variable {lookup : CastLookup} {policy : Policy}

/-- **Both machines evaluate every settling term to its answers**: HE every marked presentation,
PeTTa every presentation under extending bindings. -/
theorem settlesK_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : CallProgram atoms) {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) :
    HEEvaluatesM dispatch lookup policy atoms t L ∧ PeTTaOverK dispatch atoms t L := by
  induction settles with
  | @data d data _ => exact ⟨he_data_M answers atoms data, over_data_K atoms data⟩
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesK.build head noEquation length settled
      have args : List.Forall₂ (fun t L => SettlesK dispatch atoms t L ∧
          (HEEvaluatesM dispatch lookup policy atoms t L ∧ PeTTaOverK dispatch atoms t L)) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists args L member
        exact (settlesK_shape both.1).1.answers a inside
      have closed := (settlesK_shape whole).1.answerable.closed
      have query : ∀ vals ∈ combos Ls, HEQuery dispatch lookup policy atoms f vals
          [.expression (.symbol f :: vals)] ∧
          ∀ a ∈ [Atom.expression (.symbol f :: vals)], Answerable a := by
        intro vals member
        have valsClean := combos_answerable allClean vals member
        refine ⟨fun live scope activation value erased stack emitted => ?_, fun a inside => ?_⟩
        · refine ⟨[(value, activation)], by simp [erased], ?_⟩
          exact HERuns.he_query_absent (scoped_consFree program.scoped) head.head head.notHost
            (head.instruction vals) (fun v inside => HERuns.ground_typeVars (valsClean v inside))
            (regionBodies_nil_of_no_equation vals noEquation) live scope activation value erased
            stack emitted
        · rw [List.mem_singleton] at inside
          subst inside
          exact app_answerable head.head valsClean
      refine ⟨fun v erased marked => ?_, over_build_K head noEquation
        (args.imp fun _ _ both => ⟨both.2.2, (settlesK_shape both.1).1.answers⟩)
        (fun value => settlesK_value_self whole value)⟩
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have argRuns : List.Forall₂ (fun v L => HERunsTo dispatch lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp args) fun w member L both =>
          ⟨both.2.1 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesK_shape both.1).1.answers⟩
      have eraseList : (Entry.Value.symbol f :: vs).map Entry.Value.erase =
          .symbol f :: vs.map Entry.Value.erase := by
        simp only [List.map_cons, Entry.Value.erase]
      by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
      · obtain ⟨reuses, rfl⟩ := reusedHeld
        have value := marked.held_value
        rw [eraseList] at value
        rw [settlesK_value_self whole value]
        have runs := he_held (dispatch := dispatch) (lookup := lookup) atoms reuses
          (children := .symbol f :: vs) (by rw [eraseList]; exact closed)
          (by rw [eraseList]; exact call_not_stopped head.head)
        rwa [eraseList] at runs
      · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
          cases reentry : policy.reentry <;> cases readiness <;> simp_all
        exact he_nested_M answers head.head head.untyped closed interpreted rfl argRuns _ query
  | @call f ts Ls R head defined length settled nonempty lengths bodies ihArgs ihBodies =>
      have whole := SettlesK.call R head defined length settled nonempty lengths bodies
      have args : List.Forall₂ (fun t L => SettlesK dispatch atoms t L ∧
          (HEEvaluatesM dispatch lookup policy atoms t L ∧ PeTTaOverK dispatch atoms t L)) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ihArgs p member⟩
      have regions : ∀ vals ∈ combos Ls, List.Forall₂ (fun b L => SettlesK dispatch atoms b L ∧
          (HEEvaluatesM dispatch lookup policy atoms b L ∧ PeTTaOverK dispatch atoms b L))
          (regionInstances atoms f vals) (R vals) :=
        fun vals member => forall₂_of_zip (lengths vals member) fun p inside =>
          ⟨bodies vals member p inside, ihBodies vals member p inside⟩
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value dispatch atoms a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists args L member
        exact (settlesK_shape both.1).2 a inside
      have valsValues : ∀ vals ∈ combos Ls, ∀ v ∈ vals, NestedValues.Value dispatch atoms v :=
        combos_all allValues
      have closed := (settlesK_shape whole).1.answerable.closed
      have query : ∀ vals ∈ combos Ls, HEQuery dispatch lookup policy atoms f vals (R vals).flatten ∧
          ∀ a ∈ (R vals).flatten, Answerable a := by
        intro vals member
        refine ⟨he_query_K program.scoped head (valsValues vals member) (nonempty vals member)
            ((regions vals member).imp fun _ _ both => ⟨both.2.1, settlesK_facts both.1⟩),
          fun a inside => ?_⟩
        obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
        obtain ⟨b, both⟩ := forall₂_right_exists (regions vals member) L inR
        exact (settlesK_shape both.1).1.answers a inner
      have applies : ∀ vals ∈ combos Ls, AppliesOver atoms (.function f) vals (R vals).flatten := by
        intro vals member
        have definedHere : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
            e.arguments.length = vals.length := by
          obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ (nonempty vals member)
          rw [regionInstances_eq] at inRegion
          obtain ⟨e, chosen, _⟩ := List.mem_filterMap.mp inRegion
          obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
          simp only [Bool.and_eq_true, beq_iff_eq] at selected
          exact ⟨e, live, selected.1, selected.2⟩
        exact applies_defined_K program head.notIO head.notNative (valsValues vals member)
          definedHere ((regions vals member).imp fun _ _ both => both.2.2)
      refine ⟨fun v erased marked => ?_,
        over_call_K head defined (args.imp fun _ _ both => both.2.2) _ applies⟩
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have argRuns : List.Forall₂ (fun v L => HERunsTo dispatch lookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp args) fun w member L both =>
          ⟨both.2.1 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesK_shape both.1).1.answers⟩
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact (value_not_defined defined value).elim
      | active =>
          exact he_nested_M answers head.head head.untyped closed (Or.inr rfl) rfl argRuns _ query

end Joint

/-! ## Every complete run -/

/-- **HE's source semantics determines the answers of every settling term**, on every marked
presentation (historical lookup). -/
theorem settlesK_determined {policy : Policy} {atoms : List Atom} (program : CallProgram atoms)
    {t : Atom} {L : List Atom} (settles : SettlesK dispatch atoms t L) :
    DeterminedM dispatch policy atoms t L := by
  induction settles with
  | @data d data _ => exact data_determined_M data
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesK.build head noEquation length settled
      have argsT : List.Forall₂ (fun t L => SettlesK dispatch atoms t L ∧
          DeterminedM dispatch policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesK_shape both.1).1.answers a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesK_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
          RunsDetermined dispatch policy atoms v L) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT)
          fun w member L both => ⟨(settlesK_shape both.1).1.answers,
            both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member))⟩
      exact nested_determined_M head.head head.untyped closed rfl args
        (fun vals => [.expression (.symbol f :: vals)])
        (fun vals member => ⟨fun a inside => by
            rw [List.mem_singleton] at inside
            subst inside
            exact app_answerable head.head (combos_answerable allClean vals member),
          query_absent (scoped_consFree program.scoped) head.head (head.instruction vals)
            (combos_answerable allClean vals member)
            (regionBodies_nil_of_no_equation vals noEquation)⟩)
        (fun isHeld _ => by
          subst isHeld
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact settlesK_value_self whole value)
  | @call f ts Ls R head defined length settled nonempty lengths bodies ihArgs ihBodies =>
      have whole := SettlesK.call R head defined length settled nonempty lengths bodies
      have argsT : List.Forall₂ (fun t L => SettlesK dispatch atoms t L ∧
          DeterminedM dispatch policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ihArgs p member⟩
      have allValues : ∀ L ∈ Ls, ∀ a ∈ L, NestedValues.Value dispatch atoms a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesK_shape both.1).2 a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesK_shape whole).1.answerable.closed
      have args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
          RunsDetermined dispatch policy atoms v L) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT)
          fun w member L both => ⟨(settlesK_shape both.1).1.answers,
            both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member))⟩
      exact nested_determined_M head.head head.untyped closed rfl args
        (fun vals => (R vals).flatten)
        (fun vals member => ⟨fun a inside => by
            obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
            have regions := forall₂_of_zip (lengths vals member) (bodies vals member)
            obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inR
            exact (settlesK_shape settlesB).1.answers a inner,
          query_determined_K program.scoped head (combos_all allValues vals member)
            (nonempty vals member)
            (forall₂_of_zip (lengths vals member) fun p inside =>
              ⟨ihBodies vals member p inside, settlesK_facts (bodies vals member p inside)⟩)⟩)
        (fun isHeld _ => by
          subst isHeld
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          exact (value_not_defined defined value).elim)

/-- **Every complete run of HE publishes PeTTa's answers, with variables bound to compound values**
(historical lookup, any policy): a complete run exists; from some fuel on PeTTa's streaming run
yields `L`; every complete run of HE publishes `L`. -/
theorem every_complete_run_k (policy : Policy) {atoms : List Atom} (program : CallProgram atoms)
    {c : Atom} {L : List Atom} (settles : SettlesK dispatch atoms c L) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∃ N : Nat, ∀ n, N ≤ n →
        Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = L ∧
          ∀ emitted : List Result,
            Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
                (load (Space.ofList atoms) c Atom.undefinedType)
                ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
              emitted.map (fun r => r.1.erase) = L := by
  obtain ⟨he, petta⟩ := settlesK_agree (lookup := Completed.rawLookup) (policy := policy)
    raw_answers program settles
  have shape := (settlesK_shape settles).1
  obtain ⟨R, _, path, _⟩ := he_complete he.plain
  obtain ⟨N, stable⟩ := petta_complete shape.answerable.ground shape.answers
    (over_root_K petta fun σ => shows_ground_K shape.tree shape.answerable)
  have determined := (settlesK_determined (policy := policy) program settles).plain
  exact ⟨⟨R, path⟩, N, fun n bigger =>
    ⟨stable n bigger, fun emitted run => determined _ _ _ _ (complete_source run)⟩⟩

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open BoundVariables.Controls (sym_data)
open NestedCalls.Controls (one_consFree)
open WholeRunWords.Double (noHost)

/-- **Peano addition**: `(= (add Z $y) $y)`, `(= (add (S $x) $y) (S (add $x $y)))`. -/
def peanoRows : List Atom :=
  [rule (app "add" [sym "Z", .var "y"]) (.var "y"),
   rule (app "add" [app "S" [.var "x"], .var "y"]) (app "S" [app "add" [.var "x", .var "y"]])]

abbrev Z : Atom := sym "Z"
abbrev SZ : Atom := app "S" [Z]
abbrev SSZ : Atom := app "S" [SZ]
abbrev SSSZ : Atom := app "S" [SSZ]

theorem two_consFree (a b : Atom) (first : RegionsWithVariables.ConsFree a)
    (second : RegionsWithVariables.ConsFree b) : ∀ c ∈ [a, b], RegionsWithVariables.ConsFree c := by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact first
  · exact second

theorem peano_program : CallProgram peanoRows := by
  intro row member
  simp only [peanoRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨rule_consFree (two_consFree _ _ (.symbol _) (.var _)), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .item (.var _)⟩
  · refine ⟨rule_consFree (two_consFree _ _
      (.expression _ (by intro first rest same; simp at same) fun item inside => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · exact .symbol _
        · exact .var _) (.var _)), fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .node (by decide) fun u member => ?_⟩
    rw [List.mem_singleton] at member
    subst member
    exact .node (by decide) fun w inner => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inner
      rcases inner with rfl | rfl <;> exact .item (.var _)

theorem s_head : NodeHead noHost peanoRows "S" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem add_head : NodeHead noHost peanoRows "add" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem s_noEquation : (peanoRows.filterMap LiveEquations.equationOfRow).all
    (fun equation => equation.head != "S") = true := by
  decide +kernel

theorem add_defined : ∃ e ∈ peanoRows.filterMap LiveEquations.equationOfRow, e.head = "add" := by
  decide +kernel

/-- A constructor node over arguments that each settle with one value. -/
theorem build_values {atoms : List Atom} {f : String} {ts vs : List Atom}
    (head : NodeHead dispatch atoms f)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true)
    (args : List.Forall₂ (fun t v => SettlesK dispatch atoms t [v]) ts vs) :
    SettlesK dispatch atoms (.expression (.symbol f :: ts)) [.expression (.symbol f :: vs)] := by
  have mapped : List.Forall₂ (SettlesK dispatch atoms) ts (vs.map fun v => [v]) :=
    List.forall₂_map_right_iff.mpr args
  have built := SettlesK.build head noEquation mapped.length_eq (zip_of_forall₂ mapped)
  rw [combos_singletons] at built
  simpa using built

/-- A call of a defined head whose arguments' answers give one combination, with one instance. -/
theorem call_single {atoms : List Atom} {f : String} {ts : List Atom} {Ls : List (List Atom)}
    {vals : List Atom} {b : Atom} {Lb : List Atom} (head : NodeHead dispatch atoms f)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (args : List.Forall₂ (SettlesK dispatch atoms) ts Ls) (only : combos Ls = [vals])
    (instances : regionInstances atoms f vals = [b]) (body : SettlesK dispatch atoms b Lb) :
    SettlesK dispatch atoms (.expression (.symbol f :: ts)) Lb := by
  have built := SettlesK.call (fun _ => [Lb]) head defined args.length_eq (zip_of_forall₂ args)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      simp)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      rfl)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      intro p inside
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
      subst inside
      exact body)
  rw [only] at built
  simpa using built

theorem z_settles : SettlesK noHost peanoRows Z [Z] := .data (sym_data "Z" (by decide) (by decide))
  (by decide)

theorem sz_settles : SettlesK noHost peanoRows SZ [SZ] :=
  build_values s_head s_noEquation (.cons z_settles .nil)

theorem ssz_settles : SettlesK noHost peanoRows SSZ [SSZ] :=
  build_values s_head s_noEquation (.cons sz_settles .nil)

/-- `(add Z (S Z))` settles with `(S Z)`: the first row, body `$y` bound to `(S Z)`. -/
theorem add_z_sz : SettlesK noHost peanoRows (app "add" [Z, SZ]) [SZ] := by
  have instances : regionInstances peanoRows "add" [Z, SZ] = [SZ] := by decide +kernel
  exact call_single add_head add_defined (.cons z_settles (.cons sz_settles .nil)) rfl instances
    sz_settles

theorem add_sz_sz : SettlesK noHost peanoRows (app "add" [SZ, SZ]) [SSZ] := by
  have instances : regionInstances peanoRows "add" [SZ, SZ] = [app "S" [app "add" [Z, SZ]]] := by
    decide +kernel
  exact call_single add_head add_defined (.cons sz_settles (.cons sz_settles .nil)) rfl instances
    (build_values s_head s_noEquation (.cons add_z_sz .nil))

/-- **`(add (S (S Z)) (S Z))` settles with `(S (S (S Z)))`**: `$x` is bound to `(S Z)`, then to
`Z`, and `$y` to `(S Z)` throughout. -/
theorem add_ssz_sz : SettlesK noHost peanoRows (app "add" [SSZ, SZ]) [SSSZ] := by
  have instances : regionInstances peanoRows "add" [SSZ, SZ] = [app "S" [app "add" [SZ, SZ]]] := by
    decide +kernel
  exact call_single add_head add_defined (.cons ssz_settles (.cons sz_settles .nil)) rfl instances
    (build_values s_head s_noEquation (.cons add_sz_sz .nil))

/-- PeTTa's run of `(add (S (S Z)) (S Z))` from the translation's loader, at fuel 80. -/
theorem add_value : Streaming.values (Streaming.advance (translate peanoRows) 80
    (Streaming.enter { state := store peanoRows } (app "add" [SSZ, SZ]))) = [SSSZ] := by
  decide +kernel

/-- PeTTa's run of `(add Z (S Z))`, at fuel 80. -/
theorem add_z_value : Streaming.values (Streaming.advance (translate peanoRows) 80
    (Streaming.enter { state := store peanoRows } (app "add" [Z, SZ]))) = [SZ] := by
  decide +kernel

/-- **Positive control: recursion over compound data.** `(add (S (S Z)) (S Z))` on Peano addition:
a complete HE run exists, every complete HE run publishes `(S (S (S Z)))` under every policy (the
argument values' evaluation marks included), and PeTTa's run gives it. -/
theorem add_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList peanoRows) (app "add" [SSZ, SZ]) Atom.undefinedType)
        ⟨Space.ofList peanoRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList peanoRows) (app "add" [SSZ, SZ]) Atom.undefinedType)
          ⟨Space.ofList peanoRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [SSSZ]) ∧
      Streaming.values (Streaming.advance (translate peanoRows) 80
        (Streaming.enter { state := store peanoRows } (app "add" [SSZ, SZ]))) = [SSSZ] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_k policy peano_program add_ssz_sz
  exact ⟨⟨complete, (every N le_rfl).2⟩, add_value⟩

/-- **Positive control: a body that is a variable bound to a compound value.** `(add Z (S Z))`
gives `(S Z)` on every complete HE run and in PeTTa. -/
theorem add_z_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList peanoRows) (app "add" [Z, SZ]) Atom.undefinedType)
        ⟨Space.ofList peanoRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList peanoRows) (app "add" [Z, SZ]) Atom.undefinedType)
          ⟨Space.ofList peanoRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [SZ]) ∧
      Streaming.values (Streaming.advance (translate peanoRows) 80
        (Streaming.enter { state := store peanoRows } (app "add" [Z, SZ]))) = [SZ] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_k policy peano_program add_z_sz
  exact ⟨⟨complete, (every N le_rfl).2⟩, add_z_value⟩

/-- **Negative control: the extension is strict.** `(add (S (S Z)) (S Z))` does not settle in
`NestedCalls`'s sense: its argument combination holds `(S (S Z))`, which is no data atom. -/
theorem add_not_settlesC (L : List Atom) : ¬ SettlesC noHost peanoRows (app "add" [SSZ, SZ]) L := by
  have defined : (peanoRows.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != "add") = false := by decide +kernel
  intro settles
  cases settles with
  | data data _ => cases data
  | build _ noEquation _ _ =>
      rw [defined] at noEquation
      cases noEquation
  | @call _ _ Ls _ _ _ length settled valsData _ _ _ =>
      obtain ⟨L1, L2, rfl⟩ : ∃ L1 L2, Ls = [L1, L2] := by
        match Ls, length with
        | [L1, L2], _ => exact ⟨L1, L2, rfl⟩
      have first : SettlesC noHost peanoRows SSZ L1 := settled (SSZ, L1) (by simp)
      have second : SettlesC noHost peanoRows SZ L2 := settled (SZ, L2) (by simp)
      have sValue : ConstructorHead noHost peanoRows "S" := constructor_of_node s_head s_noEquation
      have zValue : NestedValues.Value noHost peanoRows Z := .data (sym_data "Z" (by decide) (by decide))
      have szValue : NestedValues.Value noHost peanoRows SZ := .node sValue fun v member => by
        rw [List.mem_singleton] at member
        subst member
        exact zValue
      have sszValue : NestedValues.Value noHost peanoRows SSZ := .node sValue fun v member => by
        rw [List.mem_singleton] at member
        subst member
        exact szValue
      have L1Eq := settlesK_value_self (settlesC_settlesK first) sszValue
      have L2Eq := settlesK_value_self (settlesC_settlesK second) szValue
      subst L1Eq L2Eq
      have notData := valsData [SSZ, SZ] (by simp [combos]) SSZ (by simp)
      cases notData

end Controls

#print axioms shows_renamed_K
#print axioms run_clauses_K
#print axioms applies_defined_K
#print axioms args_over_K
#print axioms over_call_K
#print axioms over_build_K
#print axioms settlesK_shape
#print axioms settlesK_value_self
#print axioms settlesC_settlesK
#print axioms settlesK_agree
#print axioms settlesK_determined
#print axioms every_complete_run_k
#print axioms Controls.add_ssz_sz
#print axioms Controls.add_value
#print axioms Controls.add_every_run
#print axioms Controls.add_z_every_run
#print axioms Controls.add_not_settlesC

end CompoundBindings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
