import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedValues

/-!
# Nested calls in bodies that use their variables

`BoundVariables` takes flat bodies and `NestedValues` bodies that build values. Here a body is any
tree of calls over items, `(= (id2 $x) (neg (neg $x)))`, `(= (keep $x) (pair (neg $x) $x))`: a
variable may sit under a call of a defined head, and further variables may follow that call.

* **HE** reads each body as its instance (`BoundVariables.work_read`) and evaluates the instance as
  a nested call: the whole argument product first, then the query of each combination
  (`NestedArguments.HENested.he_nested`, `NestedEveryRun.nested_determined`); a combination's query
  reads its own bodies as instances again (`BoundVariables.he_query_open`, `query_open_determined`).
* **PeTTa** runs the renamed open tree. An argument that is a call of a defined head returns each
  answer with the bindings of the clause that produced it, and the remaining arguments are evaluated
  under those bindings. Those bindings only ever extend the caller's (each clause adds the keys of a
  fresh use), so every variable further right still reads the call's matching. `PeTTaOver` states
  PeTTa's evaluation for every frame that delivers under every extension (`Keeps`) of a floor of
  bindings, and every presentation of the term as an instantiated tree (`Shows`).

## Results

* `SettlesC t L`: `t` settles with answers `L`: a data atom; a constructor node over settling
  arguments (`build`); a call of a defined head over settling arguments whose every combination of
  answers is a list of data atoms and has a nonempty region of settling instances (`call`).
* `settlesC_agree`: HE evaluates `t` to `L`, PeTTa evaluates every presentation of `t` to `L`.
* `settlesC_determined`, `every_complete_run_c`: every complete run of HE (historical lookup)
  publishes `L`, which PeTTa's run yields from some fuel on.
* Controls: `(id2 Yes)` gives `Yes`, `(keep Yes)` gives `(pair No Yes)`, `(tag Yes)` gives
  `(pair a Yes)`, `(pair b Yes)` (a variable after a call with two answers) on every run;
  `(id2 Yes)` lies outside `NestedValues`'s fragment.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace NestedCalls

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
  NestedEveryRun NestedValues

/-! ## Bindings that keep a substitution -/

/-- `σ'` keeps every binding of `σ`. -/
def Keeps (σ σ' : Subst) : Prop :=
  ∀ x a, σ.lookup x = some a → σ'.lookup x = some a

theorem Keeps.refl (σ : Subst) : Keeps σ σ := fun _ _ found => found

theorem Keeps.trans {σ σ' σ'' : Subst} (first : Keeps σ σ') (second : Keeps σ' σ'') :
    Keeps σ σ'' :=
  fun x a found => second x a (first x a found)

/-- **A clause's bindings keep the caller's**: the matching bindings, renamed for a use the
caller leaves fresh, followed by the caller's. -/
theorem keeps_renamed {use : Nat} {bound σ : Subst} (fresh : Unifying.FreshFor use σ) :
    Keeps σ (Unifying.renameKeys use bound ++ σ) := by
  intro x a found
  have missing : (Unifying.renameKeys use bound).find? (fun p => p.1 == x) = none := by
    rw [List.find?_eq_none]
    intro p member
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp member
    simp only [beq_iff_eq]
    intro same
    have free : σ.lookup x = none := by
      have outer := fresh q.1
      rwa [show Unifying.freshName use q.1 = x from same] at outer
    rw [free] at found
    cases found
  unfold Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup at found ⊢
  rw [List.find?_append, missing, Option.none_or]
  exact found

theorem read_var (σ : Subst) (x : String) : applySubst σ (.var x) = (σ.lookup x).getD (.var x) := by
  simp only [applySubst]

theorem lookup_of_lit {σ : Subst} {x : String} (lit : Lit (applySubst σ (.var x))) :
    σ.lookup x = some (applySubst σ (.var x)) := by
  rw [read_var] at lit ⊢
  cases found : σ.lookup x with
  | none =>
      simp only [found, Option.getD_none] at lit
      cases lit
  | some a => rfl

theorem read_kept {σ σ' : Subst} (keeps : Keeps σ σ') {x : String}
    (lit : Lit (applySubst σ (.var x))) : applySubst σ' (.var x) = applySubst σ (.var x) := by
  rw [read_var σ' x, keeps x _ (lookup_of_lit lit), Option.getD_some]

/-! ## Trees and their presentations -/

/-- **A tree body**: items (symbols, grounded values, variables) under nodes whose heads begin no
special form. -/
inductive TreeBody : Atom → Prop
  | item {u : Atom} : FlatItem u → TreeBody u
  | node {g : String} {us : List Atom} : controlHead g = false → (∀ u ∈ us, TreeBody u) →
      TreeBody (.expression (.symbol g :: us))

theorem mem_node_vars {g : String} {us : List Atom} {u : Atom} (member : u ∈ us) {x : String}
    (inU : x ∈ TypeSubst.typeVars u) : x ∈ TypeSubst.typeVars (.expression (.symbol g :: us)) := by
  simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
  exact Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
    member x inU

/-- **`b` shows the ground term `t` under `σ`**: a tree whose variables are bound to literals,
instantiated to `t`. -/
structure Shows (σ : Subst) (b t : Atom) : Prop where
  tree : TreeBody b
  bound : ∀ x ∈ TypeSubst.typeVars b, Lit (applySubst σ (.var x))
  instantiates : applySubst σ b = t

/-- Bindings that keep `σ` read a tree bound under `σ` as `σ` does. -/
theorem applySubst_keeps {σ σ' : Subst} (keeps : Keeps σ σ') :
    ∀ {b : Atom}, TreeBody b → (∀ x ∈ TypeSubst.typeVars b, Lit (applySubst σ (.var x))) →
      applySubst σ' b = applySubst σ b := by
  intro b tree
  induction tree with
  | @item u flat =>
      intro bound
      cases flat with
      | symbol name => simp [applySubst]
      | grounded value => simp [applySubst]
      | var name => exact read_kept keeps (bound name (by simp [TypeSubst.typeVars]))
  | @node g us _ _ ih =>
      intro bound
      rw [applySubst_node, applySubst_node]
      congr 2
      exact List.map_congr_left fun u member =>
        ih u member fun x inU => bound x (mem_node_vars member inU)

theorem Shows.keeps {σ σ' : Subst} {b t : Atom} (shown : Shows σ b t) (keeps : Keeps σ σ') :
    Shows σ' b t := by
  refine ⟨shown.tree, fun x member => ?_, ?_⟩
  · rw [read_kept keeps (shown.bound x member)]
    exact shown.bound x member
  · rw [applySubst_keeps keeps shown.tree shown.bound]
    exact shown.instantiates

/-- A tree showing a literal is the literal or a variable bound to it. -/
theorem Shows.item {σ : Subst} {b d : Atom} (shown : Shows σ b d) (literal : Lit d) :
    PresentsItem σ b d := by
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

theorem forall₂_map_self {α β : Type} {R : α → β → Prop} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, R a (g a)) → List.Forall₂ R l (l.map g)
  | [], _ => .nil
  | a :: _, each =>
      .cons (each a List.mem_cons_self) (forall₂_map_self fun b m => each b (List.mem_cons_of_mem _ m))

/-- A tree showing a call is a node of the same head whose children show its arguments. -/
theorem Shows.node {σ : Subst} {b : Atom} {f : String} {ts : List Atom}
    (shown : Shows σ b (.expression (.symbol f :: ts))) :
    ∃ us, b = .expression (.symbol f :: us) ∧ controlHead f = false ∧
      List.Forall₂ (Shows σ) us ts := by
  have instantiates := shown.instantiates
  have bound := shown.bound
  cases shown.tree with
  | item flat =>
      exfalso
      cases flat with
      | symbol name => simp [applySubst] at instantiates
      | grounded value => simp [applySubst] at instantiates
      | var name =>
          have lit := bound name (by simp [TypeSubst.typeVars])
          rw [instantiates] at lit
          cases lit
  | @node g us notControl children =>
      rw [applySubst_node] at instantiates
      simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at instantiates
      obtain ⟨rfl, rfl⟩ := instantiates
      refine ⟨us, rfl, notControl, forall₂_map_self fun u member =>
        ⟨children u member, fun x inU => bound x (mem_node_vars member inU), rfl⟩⟩

theorem shows_ground {σ : Subst} {t : Atom} (tree : TreeBody t) (answerable : Answerable t) :
    Shows σ t t :=
  ⟨tree, fun x member => by
      rw [HERuns.ground_typeVars answerable] at member
      simp at member,
    Unifying.applySubst_ground σ _ answerable.ground⟩

/-! ## PeTTa's evaluation over extending bindings -/

open PeTTaRuns in
/-- **The frames deliver `v` as `K v` under every extension of `σ₀`**: from any reached world over
the translation's store, with bindings that keep `σ₀`, are ground and leave every later use fresh. -/
def DeliversFrom (atoms : List Atom) (σ₀ : Subst) (frames : List Streaming.Frame)
    (K : Atom → List Atom) (v : Atom) : Prop :=
  ∀ (world : Streaming.World) (σ : Subst), Keeps σ₀ σ → world.state = store atoms →
    world.privateCode = [] → Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = K v ∧
        PSteps (translate atoms)
          ⟨world, .execute ⟨.returned [⟨v, σ⟩], frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

/-- **PeTTa evaluates every presentation of `t` to `L`**, under every frames that deliver each
answer under every extension of a floor `σ₀`, from bindings that keep `σ₀`. -/
def PeTTaOver (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (σ₀ : Subst) (frames : List Streaming.Frame) (K : Atom → List Atom),
    (∀ v ∈ L, DeliversFrom atoms σ₀ frames K v) →
  ∀ (world : Streaming.World) (σ : Subst), Keeps σ₀ σ → world.state = store atoms →
    world.privateCode = [] → Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (b : Atom), Shows σ b t →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = L.flatMap K ∧
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.evaluate σ b, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

/-- **PeTTa applies the target to the held values with answers `A`**, in the same sense. -/
def AppliesOver (atoms : List Atom) (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target)
    (held : List Atom) (A : List Atom) : Prop :=
  ∀ (σ₀ : Subst) (frames : List Streaming.Frame) (K : Atom → List Atom),
    (∀ v ∈ A, DeliversFrom atoms σ₀ frames K v) →
  ∀ (world : Streaming.World) (σ : Subst), Keeps σ₀ σ → world.state = store atoms →
    world.privateCode = [] → Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (index : Nat) (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = A.flatMap K ∧
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.arguments σ target [] held index, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

/-- At the root, with frames that deliver under all bindings, `PeTTaOver` is `PeTTaEvaluates`. -/
theorem over_root {atoms : List Atom} {t : Atom} {L : List Atom} (evaluates : PeTTaOver atoms t L)
    (self : ∀ σ, Shows σ t t) : PeTTaEvaluates atoms t L :=
  fun frames K deliver world σ state privateCode range fresh older answers next =>
    evaluates σ frames K (fun v member world' σ' _ => deliver v member world' σ') world σ
      (Keeps.refl σ) state privateCode range fresh t (self σ) older answers next

/-- **A data atom, every presentation.** -/
theorem over_data (atoms : List Atom) {d : Atom} (data : DataAtom d) : PeTTaOver atoms d [d] := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh b shown older answers next
  have item := shown.item (lit_of_data data)
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver d List.mem_cons_self world σ keeps state
    privateCode range fresh older answers next
  exact ⟨uses, out, grown, by simp [valuesOut],
    .head (PeTTaOpenRuns.evaluate_item world σ item frames older answers next) path⟩

/-- **A constructor application**: PeTTa builds the expression of the held values. -/
theorem applies_construct (atoms : List Atom) {held : List Atom}
    (ground : ∀ v ∈ held, isGroundAtom v = true) :
    AppliesOver atoms .data held [.expression held] := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh index older answers next
  have step := PeTTaRuns.construct (registry := translate atoms) world σ held index frames older
    answers next
  rw [PeTTaRuns.map_resolve_ground σ ground] at step
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver _ List.mem_cons_self world σ keeps state
    privateCode range fresh older answers next
  exact ⟨uses, out, grown, by simp [valuesOut], .head step path⟩

/-! ## The program condition and the renamed bodies -/

/-- **A row whose body uses only its left side's variables, as a tree.** -/
def CallRow (row : Atom) : Prop :=
  ∀ lhs rhs, row = .expression [.symbol "=", lhs, rhs] →
    (∀ x ∈ TypeSubst.typeVars rhs, x ∈ TypeSubst.typeVars lhs) ∧ TreeBody rhs

/-- The program condition: symbol-headed, `cons`-free equations whose bodies are trees using only
their left side's variables. -/
def CallProgram (atoms : List Atom) : Prop :=
  ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row ∧ CallRow row

theorem CallProgram.scoped {atoms : List Atom} (program : CallProgram atoms) :
    ScopedProgram atoms :=
  fun row member => ⟨(program row member).1,
    fun lhs rhs same => ((program row member).2 lhs rhs same).1⟩

/-- **A renamed tree shows its instance**, under the matching bindings renamed for the use and
followed by the caller's. -/
theorem shows_renamed {use : Nat} {bound σ : Subst}
    (fresh : Unifying.FreshFor use σ) {ps args : List Atom} (argsData : ∀ a ∈ args, DataAtom a)
    (instantiated : ps.map (applyTypeValuation (RegionsWithVariables.asValuation bound)) = args) :
    ∀ {body : Atom}, TreeBody body →
      (∀ x ∈ TypeSubst.typeVars body, x ∈ TypeSubst.typeVarsList ps) →
      Shows (Unifying.renameKeys use bound ++ σ) (Unifying.rename use body)
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
          have data := vars_of_lits instantiated argsData name inPs
          have looked : (Unifying.renameKeys use bound ++ σ).lookup (Unifying.freshName use name) =
              bound.lookup name := Unifying.lookup_append_renamed fresh name
          obtain ⟨value, found⟩ : ∃ value, bound.lookup name = some value := by
            cases found : bound.lookup name with
            | none =>
                have unbound : RegionsWithVariables.asValuation bound name = .var name := by
                  simp [RegionsWithVariables.asValuation, found]
                rw [unbound] at data
                cases data
            | some value => exact ⟨value, rfl⟩
          have readRenamed : applySubst (Unifying.renameKeys use bound ++ σ)
              (.var (Unifying.freshName use name)) = value := by
            rw [read_var, looked, found, Option.getD_some]
          have readBound : applySubst bound (.var name) = value := by
            rw [read_var, found, Option.getD_some]
          have valueLit : Lit value := by
            have lit := lit_of_data data
            simpa [RegionsWithVariables.asValuation, found] using lit
          refine ⟨.item (.var _), fun x member => ?_, by rw [readRenamed, readBound]⟩
          simp only [TypeSubst.typeVars, List.mem_singleton] at member
          subst member
          rw [readRenamed]
          exact valueLit
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

/-- Each selected equation of a call program shows its instance. -/
theorem selected_shows {atoms : List Atom} (program : CallProgram atoms)
    {e : SpaceSemantics.Equation} (live : e ∈ atoms.filterMap LiveEquations.equationOfRow)
    {args : List Atom} (argsData : ∀ a ∈ args, DataAtom a) {bound : Subst}
    (matched : SpaceSemantics.matchValue.matchValues [] e.arguments args = some bound)
    (use : Nat) {σ : Subst} (fresh : Unifying.FreshFor use σ) :
    Shows (Unifying.renameKeys use bound ++ σ) (Unifying.rename use e.body)
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
  exact shows_renamed fresh argsData (instanceArgs bound (RegionsWithVariables.Extends.refl bound))
    tree inArgs

/-! ## PeTTa's selected clauses and applications -/

theorem run_clauses_over {atoms : List Atom} (program : CallProgram atoms) {σ₀ σ : Subst}
    (keeps : Keeps σ₀ σ) {values : List Atom} (valuesData : ∀ v ∈ values, DataAtom v)
    (range : Unifying.GroundRange σ) (frames : List Streaming.Frame) (K : Atom → List Atom) :
    ∀ (chosen : List SpaceSemantics.Equation) (use : Nat) (Ls : List (List Atom)),
      (∀ e ∈ chosen, e ∈ atoms.filterMap LiveEquations.equationOfRow) →
      List.Forall₂ (fun b L => PeTTaOver atoms b L) (matchingInstances values chosen) Ls →
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
          exact run_clauses_over program keeps valuesData range frames K rest (use + 1) Ls liveRest
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
                fun v member => (answerable_of_data (valuesData v member)).ground
              have boundRange := PeTTaRuns.matchValues_groundRange e.arguments values [] bound
                (fun _ member => by cases member) groundValues matched
              have below : use < world.uses := by omega
              have outerFresh : ∀ k, Unifying.FreshFor (world.uses + k) σ := fun k => by
                have shifted := fresh (world.uses - use + k)
                rwa [show use + (world.uses - use + k) = world.uses + k by omega] at shifted
              have useFresh : Unifying.FreshFor use σ := by simpa using fresh 0
              have presented := selected_shows program (live e List.mem_cons_self) valuesData
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
              obtain ⟨uses₂, out₂, grown₂, values₂, path₂⟩ := run_clauses_over program keeps
                valuesData range frames K rest (use + 1) Ls' liveRest later
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

/-- **An application of a defined head to data atoms**: PeTTa selects the matching clauses and
runs each renamed body, in row order. -/
theorem applies_defined {atoms : List Atom} (program : CallProgram atoms) {f : String}
    {vals : List Atom} (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false) (valsData : ∀ v ∈ vals, DataAtom v)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = vals.length)
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => PeTTaOver atoms b L) (regionInstances atoms f vals) Ls) :
    AppliesOver atoms (.function f) vals Ls.flatten := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh index older answers next
  obtain ⟨e, live, eHead, arity⟩ := defined
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
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [eHead]⟩, arity⟩
  have related : List.Forall₂ (fun b L => PeTTaOver atoms b L) (matchingInstances vals chosen) Ls := by
    rw [chosenEq, ← regionInstances_eq]
    exact bodies
  have chosenLive : ∀ e' ∈ chosen, e' ∈ atoms.filterMap LiveEquations.equationOfRow :=
    fun e' member => (List.mem_filter.mp member).1
  obtain ⟨uses, out, grown, valuesOut, path⟩ := run_clauses_over program keeps valsData range frames
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

/-! ## PeTTa's argument traversal under extending bindings -/

/-- **PeTTa's argument traversal streams, under extending bindings**: each answer of an argument
returns into its argument frame with the bindings that produced it, and the remaining arguments,
shown under the caller's bindings, are evaluated under those. -/
theorem args_over (atoms : List Atom) (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target)
    (demanded : ∀ i, PeTTaRuns.rawDemand (translate atoms) target i = false) :
    ∀ (ts : List Atom) (Ls : List (List Atom)),
      List.Forall₂ (fun t L => PeTTaOver atoms t L) ts Ls →
      ∀ (held : List Atom) (A : List Atom → List Atom),
        (∀ c ∈ combos Ls, AppliesOver atoms target (held ++ c) (A c)) →
        ∀ (σ₀ : Subst) (frames : List Streaming.Frame) (K : Atom → List Atom),
          (∀ c ∈ combos Ls, ∀ v ∈ A c, DeliversFrom atoms σ₀ frames K v) →
          ∀ (world : Streaming.World) (σ : Subst), Keeps σ₀ σ → world.state = store atoms →
            world.privateCode = [] → Unifying.GroundRange σ →
            (∀ k, Unifying.FreshFor (world.uses + k) σ) →
            ∀ (us : List Atom), List.Forall₂ (Shows σ) us ts →
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
        obtain ⟨uses, out, grown, valuesOut, path⟩ := args_over atoms target demanded ts Ls'
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

/-! ## Node heads, and PeTTa on nodes -/

/-- **A head that begins a node**: undeclared, no host operation, no instruction, no PeTTa
primitive or I/O head, no special form. -/
structure NodeHead (dispatch : GroundedDispatch) (atoms : List Atom) (f : String) : Prop where
  head : DataAtom (.symbol f)
  untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = []
  notHost : ¬ dispatch.executable (.symbol f)
  notInstruction : Minimal.embeddedInstruction (.expression [.symbol f]) = false
  notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false
  notNative : StdLib.known f = false
  notControl : controlHead f = false

namespace NodeHead

variable {dispatch : GroundedDispatch} {atoms : List Atom} {f : String}

theorem notCollapse (head : NodeHead dispatch atoms f) : f ≠ "collapse" := by
  intro same
  have control := head.notControl
  rw [same] at control
  simp [controlHead] at control

theorem notOnce (head : NodeHead dispatch atoms f) : f ≠ "once" := by
  intro same
  have control := head.notControl
  rw [same] at control
  simp [controlHead] at control

theorem instruction (head : NodeHead dispatch atoms f) (items : List Atom) :
    Minimal.embeddedInstruction (.expression (.symbol f :: items)) = false :=
  head.notInstruction

theorem notFunction (head : NodeHead dispatch atoms f) : f ≠ "function" := by
  intro same
  have instruction := head.notInstruction
  rw [same] at instruction
  simp [Minimal.embeddedInstruction] at instruction

theorem ordinary (head : NodeHead dispatch atoms f) {vals : List Atom}
    (data : ∀ v ∈ vals, DataAtom v) : Ordinary dispatch atoms f vals :=
  ⟨head.head, data, head.untyped, head.notHost, head.instruction vals, head.notIO, head.notNative,
    sourceControlForm_of_head head.notControl vals, head.notCollapse, head.notOnce⟩

end NodeHead

variable {dispatch : GroundedDispatch}

/-- **A call of a defined head, every presentation**: the call entry, the streaming argument
traversal under extending bindings, and the application on each combination. -/
theorem over_call {atoms : List Atom} {f : String} {ts : List Atom} {Ls : List (List Atom)}
    (head : NodeHead dispatch atoms f)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (args : List.Forall₂ (fun t L => PeTTaOver atoms t L) ts Ls) (A : List Atom → List Atom)
    (apps : ∀ c ∈ combos Ls, AppliesOver atoms (.function f) c (A c)) :
    PeTTaOver atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap A) := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh b shown older answers next
  obtain ⟨us, rfl, notControl, shownArgs⟩ := shown.node
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      true := by
    obtain ⟨e, live, eHead⟩ := defined
    rw [privateCode, head.notIO, head.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    exact List.any_eq_true.mpr ⟨e, live, by simp [eHead]⟩
  obtain ⟨uses, out, grown, valuesOut, path⟩ := args_over atoms (.function f)
    (fun index => argumentIsRaw_false head.notNative head.untyped index) ts Ls args [] A
    (fun c cMem => by
      rw [List.nil_append]
      exact apps c cMem)
    σ₀ frames K (fun c cMem v vMem => deliver v (List.mem_flatMap.mpr ⟨c, cMem, vMem⟩)) world σ keeps
    state privateCode range fresh us shownArgs 0 older answers next
  exact ⟨uses, out, grown, valuesOut,
    .head (PeTTaRuns.call_enter world σ head.notCollapse head.notOnce
      (sourceControlForm_of_head notControl us) callable frames older answers next) path⟩

/-- **A constructor node, every presentation**: the head and the arguments are evaluated in turn,
streaming, and each combination is built. -/
theorem over_build {atoms : List Atom} {f : String} {ts : List Atom} {Ls : List (List Atom)}
    (head : NodeHead dispatch atoms f)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true)
    (args : List.Forall₂ (fun t L => PeTTaOver atoms t L ∧ ∀ a ∈ L, Answerable a) ts Ls) :
    PeTTaOver atoms (.expression (.symbol f :: ts))
      ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)]) := by
  intro σ₀ frames K deliver world σ keeps state privateCode range fresh b shown older answers next
  obtain ⟨us, rfl, notControl, shownArgs⟩ := shown.node
  have notCallable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
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
  obtain ⟨uses, out, grown, valuesOut, path⟩ := args_over atoms .data (fun _ => rfl) ts Ls
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
    σ₀ frames K (fun c cMem v vMem => deliver v (List.mem_flatMap.mpr ⟨c, cMem, vMem⟩)) world σ keeps
    state privateCode range fresh us shownArgs 1 older answers next
  have entered := PeTTaOpenRuns.argument_open (registry := translate atoms) world σ .data
    (⟨.symbol f, Or.inl rfl⟩ : PresentsItem σ (.symbol f) (.symbol f)) us [] 0 rfl frames older
    answers next
  rw [List.nil_append, Nat.zero_add] at entered
  exact ⟨uses, out, grown, valuesOut,
    .head (PeTTaRuns.data_enter world σ head.notCollapse head.notOnce
      (sourceControlForm_of_head notControl us) notCallable frames older answers next)
      (entered.trans path)⟩

/-! ## The terms that settle -/

/-- **`t` settles with the answers `L`**: a data atom; a constructor node over settling arguments,
one answer per combination of theirs; a call of a defined head over settling arguments whose every
combination of answers is a list of data atoms with a nonempty region of settling instances. A
condition on the program, never on a result. -/
inductive SettlesC (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → List Atom → Prop
  | data {d : Atom} : DataAtom d → d ≠ Atom.notReducible → SettlesC dispatch atoms d [d]
  | build {f : String} {ts : List Atom} {Ls : List (List Atom)} : NodeHead dispatch atoms f →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesC dispatch atoms p.1 p.2) →
      SettlesC dispatch atoms (.expression (.symbol f :: ts))
        ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)])
  | call {f : String} {ts : List Atom} {Ls : List (List Atom)} (R : List Atom → List (List Atom)) :
      NodeHead dispatch atoms f →
      (∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f) →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesC dispatch atoms p.1 p.2) →
      (∀ vals ∈ combos Ls, ∀ v ∈ vals, DataAtom v) →
      (∀ vals ∈ combos Ls, regionInstances atoms f vals ≠ []) →
      (∀ vals ∈ combos Ls, (regionInstances atoms f vals).length = (R vals).length) →
      (∀ vals ∈ combos Ls, ∀ p ∈ (regionInstances atoms f vals).zip (R vals),
        SettlesC dispatch atoms p.1 p.2) →
      SettlesC dispatch atoms (.expression (.symbol f :: ts))
        ((combos Ls).flatMap fun vals => (R vals).flatten)

theorem SettlesC.of_eq {atoms : List Atom} {t : Atom} {L L' : List Atom}
    (settles : SettlesC dispatch atoms t L) (same : L = L') : SettlesC dispatch atoms t L' :=
  same ▸ settles

theorem forall₂_of_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → (∀ p ∈ l₁.zip l₂, R p.1 p.2) →
      List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | [], _ :: _, length, _ => by simp at length
  | _ :: _, [], length, _ => by simp at length
  | a :: l₁, b :: l₂, length, each => by
      refine .cons (each (a, b) (by simp)) (forall₂_of_zip (by simpa using length) fun p member => ?_)
      exact each p (by simp [member])

/-- What every settling term and its answers are. -/
structure Shape (t : Atom) (L : List Atom) : Prop where
  answerable : Answerable t
  tree : TreeBody t
  fixed : ∀ rename : String → String, renameTypeVars rename t = t
  answers : ∀ a ∈ L, Answerable a

theorem node_shape {atoms : List Atom} {f : String} {ts : List Atom} {L : List Atom}
    (head : NodeHead dispatch atoms f) (each : ∀ t ∈ ts, ∃ L, Shape t L)
    (answers : ∀ a ∈ L, Answerable a) : Shape (.expression (.symbol f :: ts)) L := by
  refine ⟨app_answerable head.head fun t member => (each t member).choose_spec.answerable,
    .node head.notControl fun t member => (each t member).choose_spec.tree, fun rename => ?_,
    answers⟩
  simp only [renameTypeVars, List.map_cons]
  rw [map_fixed fun t member => (each t member).choose_spec.fixed rename]

theorem settlesC_shape {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesC dispatch atoms t L) : Shape t L := by
  induction settles with
  | @data d data _ =>
      refine ⟨answerable_of_data data, ?_, fun rename => ?_, fun a member => ?_⟩
      · cases data with
        | symbol _ _ => exact .item (.symbol _)
        | grounded value => exact .item (.grounded value)
      · cases data <;> simp [renameTypeVars]
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data data
  | @build f ts Ls head _ length _ ih =>
      have args := forall₂_of_zip length ih
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, shape⟩ := forall₂_right_exists args L member
        exact shape.answers a inside
      refine node_shape head (fun t member => forall₂_left_exists args t member) ?_
      intro a member
      obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
      rw [List.mem_singleton] at inner
      subst inner
      exact app_answerable head.head (combos_answerable allClean vals valsMem)
  | @call f ts Ls R head _ length _ _ _ lengths _ ihArgs ihBodies =>
      have args := forall₂_of_zip length ihArgs
      refine node_shape head (fun t member => forall₂_left_exists args t member) ?_
      intro a member
      obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
      obtain ⟨L, inR, inL⟩ := List.mem_flatten.mp inner
      have regions := forall₂_of_zip (lengths vals valsMem) (ihBodies vals valsMem)
      obtain ⟨b, shape⟩ := forall₂_right_exists regions L inR
      exact shape.answers a inL

theorem settlesC_facts {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesC dispatch atoms t L) : BodyFacts t := by
  have shape := settlesC_shape settles
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
  | call _ head _ _ _ _ _ _ _ => exact node head shape

/-! ## HE: queries with open bodies, determined -/

section HEQueries

variable {policy : Policy}

theorem works_bodies {atoms live : List Atom} {scope : List String} {value : Entry.Value}
    {frame : Frame} {f : String} {vals : List Atom} (ordinary : Ordinary dispatch atoms f vals)
    (program : ScopedProgram atoms) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => Determined dispatch policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      (.expression (.symbol f :: vals)) frame.bindings works)
    {children : List Result}
    (equations : Completed.EquationBodiesRel (Space.ofList atoms) dispatch Completed.rawLookup live
      scope value Atom.undefinedType frame works children (policy := policy)) :
    children.map (fun r => r.1.erase) = Ls.flatten := by
  have instances := works_instances (policy := policy) ordinary.arguments program
    frame.certified.satisfiable frontier
  have onWorks : List.Forall₂ (fun w L => ∃ i, (∀ output : Frame,
        output.bindings = w.bindings →
          output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i) ∧
      DeterminedUnder dispatch Completed.rawLookup policy atoms i L ∧ BodyFacts i) works Ls :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, determined, facts⟩ := both
      exact ⟨i, reads, determined, facts⟩
  exact bodies_source_open works Ls onWorks equations

/-- **HE's query of a call of data atoms with open bodies is determined**: every derivation of the
call relation, on every call value of `(f vals)`, returns the instances' answers in row order. -/
theorem query_open_determined {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {vals : List Atom} (ordinary : Ordinary dispatch atoms f vals)
    (nonempty : regionInstances atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => Determined dispatch policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    QueryDetermined dispatch policy atoms f vals Ls.flatten := by
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member))
  intro live scope value frame children erased called
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error ordinary.head erased)
  | embedded _ _ instruction _ _ =>
      rw [erased, ordinary.notInstruction] at instruction
      cases instruction
  | absent _ _ frontier =>
      rw [erased] at frontier
      have sidesEq := frontier_sides ground frame.certified.satisfiable (scoped_consFree program)
        frontier
      apply absurd _ nonempty
      rw [regionInstances_sides, ← sidesEq]
      rfl
  | equations _ _ frontier _ equations =>
      rw [erased] at frontier
      exact works_bodies ordinary program bodies frontier equations

end HEQueries

/-! ## Both machines -/

section Joint

variable {lookup : CastLookup} {policy : Policy}

/-- **Both machines evaluate every settling term to its answers**, PeTTa on every presentation
under extending bindings. -/
theorem settlesC_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : CallProgram atoms) {t : Atom} {L : List Atom} (settles : SettlesC dispatch atoms t L) :
    HEEvaluates dispatch lookup policy atoms t L ∧ PeTTaOver atoms t L := by
  induction settles with
  | @data d data _ => exact ⟨HERuns.he_data answers atoms data, over_data atoms data⟩
  | @build f ts Ls head noEquation length settled ih =>
      have args : List.Forall₂ (fun t L => SettlesC dispatch atoms t L ∧
          (HEEvaluates dispatch lookup policy atoms t L ∧ PeTTaOver atoms t L)) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists args L member
        exact (settlesC_shape both.1).answers a inside
      have closed := (settlesC_shape (SettlesC.build head noEquation length settled)).answerable.closed
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
      exact ⟨HENested.he_nested answers head.head head.untyped closed
          (args.imp fun _ _ both => ⟨both.2.1, (settlesC_shape both.1).answers⟩) _ query,
        over_build head noEquation
          (args.imp fun _ _ both => ⟨both.2.2, (settlesC_shape both.1).answers⟩)⟩
  | @call f ts Ls R head defined length settled valsData nonempty lengths bodies ihArgs ihBodies =>
      have args : List.Forall₂ (fun t L => SettlesC dispatch atoms t L ∧
          (HEEvaluates dispatch lookup policy atoms t L ∧ PeTTaOver atoms t L)) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ihArgs p member⟩
      have regions : ∀ vals ∈ combos Ls, List.Forall₂ (fun b L => SettlesC dispatch atoms b L ∧
          (HEEvaluates dispatch lookup policy atoms b L ∧ PeTTaOver atoms b L))
          (regionInstances atoms f vals) (R vals) :=
        fun vals member => forall₂_of_zip (lengths vals member) fun p inside =>
          ⟨bodies vals member p inside, ihBodies vals member p inside⟩
      have closed := (settlesC_shape (SettlesC.call R head defined length settled valsData nonempty
        lengths bodies)).answerable.closed
      have query : ∀ vals ∈ combos Ls, HEQuery dispatch lookup policy atoms f vals (R vals).flatten ∧
          ∀ a ∈ (R vals).flatten, Answerable a := by
        intro vals member
        refine ⟨fun live scope activation value erased stack emitted =>
          he_query_open program.scoped (head.ordinary (valsData vals member)) (nonempty vals member)
            ((regions vals member).imp fun _ _ both =>
              ⟨both.2.1, settlesC_facts both.1, (settlesC_shape both.1).answers⟩)
            live scope activation value erased stack emitted, fun a inside => ?_⟩
        obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
        obtain ⟨b, both⟩ := forall₂_right_exists (regions vals member) L inR
        exact (settlesC_shape both.1).answers a inner
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
        exact applies_defined program head.notIO head.notNative (valsData vals member) definedHere
          ((regions vals member).imp fun _ _ both => both.2.2)
      exact ⟨HENested.he_nested answers head.head head.untyped closed
          (args.imp fun _ _ both => ⟨both.2.1, (settlesC_shape both.1).answers⟩) _ query,
        over_call head defined (args.imp fun _ _ both => both.2.2) _ applies⟩

end Joint

/-! ## Every complete run -/

/-- **HE's source semantics determines the answers of every settling term** (historical lookup). -/
theorem settlesC_determined {policy : Policy} {atoms : List Atom} (program : CallProgram atoms)
    {t : Atom} {L : List Atom} (settles : SettlesC dispatch atoms t L) :
    Determined dispatch policy atoms t L := by
  induction settles with
  | @data d data _ =>
      exact (data_settled (dispatch := dispatch) (policy := policy) (atoms := atoms) data).2
  | @build f ts Ls head noEquation length settled ih =>
      have args : List.Forall₂ (Settled dispatch policy atoms) ts Ls :=
        forall₂_of_zip length fun p member => ⟨(settlesC_shape (settled p member)).answers, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists args L member
        exact both.1 a inside
      have closed := (settlesC_shape (SettlesC.build head noEquation length settled)).answerable.closed
      exact (nested_determined head.head head.untyped closed args
        (fun vals => [.expression (.symbol f :: vals)]) fun vals member =>
          ⟨fun a inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact app_answerable head.head (combos_answerable allClean vals member),
            query_absent (scoped_consFree program.scoped) head.head (head.instruction vals)
              (combos_answerable allClean vals member)
              (regionBodies_nil_of_no_equation vals noEquation)⟩).2
  | @call f ts Ls R head defined length settled valsData nonempty lengths bodies ihArgs ihBodies =>
      have args : List.Forall₂ (Settled dispatch policy atoms) ts Ls :=
        forall₂_of_zip length fun p member =>
          ⟨(settlesC_shape (settled p member)).answers, ihArgs p member⟩
      have closed := (settlesC_shape (SettlesC.call R head defined length settled valsData nonempty
        lengths bodies)).answerable.closed
      exact (nested_determined head.head head.untyped closed args (fun vals => (R vals).flatten)
        fun vals member => ⟨fun a inside => by
            obtain ⟨L, inR, inner⟩ := List.mem_flatten.mp inside
            have regions := forall₂_of_zip (lengths vals member) (bodies vals member)
            obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inR
            exact (settlesC_shape settlesB).answers a inner,
          query_open_determined program.scoped (head.ordinary (valsData vals member))
            (nonempty vals member)
            (forall₂_of_zip (lengths vals member) fun p inside =>
              ⟨ihBodies vals member p inside, settlesC_facts (bodies vals member p inside)⟩)⟩).2

/-- **Every complete run of HE publishes PeTTa's answers, with nested calls in bodies** (historical
lookup): a complete run exists; from some fuel on PeTTa's streaming run yields `L`; every complete
run of HE publishes `L`. -/
theorem every_complete_run_c (policy : Policy) {atoms : List Atom} (program : CallProgram atoms)
    {c : Atom} {L : List Atom} (settles : SettlesC dispatch atoms c L) :
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
  obtain ⟨he, petta⟩ := settlesC_agree (lookup := Completed.rawLookup) (policy := policy)
    raw_answers program settles
  have shape := settlesC_shape settles
  obtain ⟨R, _, path, _⟩ := he_complete he
  obtain ⟨N, stable⟩ := petta_complete shape.answerable.ground shape.answers
    (over_root petta fun σ => shows_ground shape.tree shape.answerable)
  have determined := settlesC_determined (policy := policy) program settles
  exact ⟨⟨R, path⟩, N, fun n bigger =>
    ⟨stable n bigger, fun emitted run => determined _ _ _ _ (complete_source run)⟩⟩

/-! ## Flat calls -/

theorem singletons_settle {atoms : List Atom} : ∀ (vs : List Atom),
    (∀ v ∈ vs, DataAtom v ∧ v ≠ Atom.notReducible) →
    ∀ p ∈ vs.zip (vs.map fun v => [v]), SettlesC dispatch atoms p.1 p.2
  | [], _, p, member => by cases member
  | v :: rest, each, p, member => by
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | inRest
      · exact .data (each v List.mem_cons_self).1 (each v List.mem_cons_self).2
      · exact singletons_settle rest (fun w m => each w (List.mem_cons_of_mem _ m)) p inRest

/-- **A flat call of data atoms** settles with the answers of its region's instances. -/
theorem flat_call {atoms : List Atom} {f : String} {vals : List Atom}
    (head : NodeHead dispatch atoms f)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (data : ∀ v ∈ vals, DataAtom v) (notRefused : ∀ v ∈ vals, v ≠ Atom.notReducible)
    {Lb : List (List Atom)} (nonempty : regionInstances atoms f vals ≠ [])
    (lengths : (regionInstances atoms f vals).length = Lb.length)
    (bodies : ∀ p ∈ (regionInstances atoms f vals).zip Lb, SettlesC dispatch atoms p.1 p.2) :
    SettlesC dispatch atoms (.expression (.symbol f :: vals)) Lb.flatten := by
  have only : combos (vals.map fun v => [v]) = [vals] := combos_singletons vals
  have built := SettlesC.call (fun _ => Lb) head defined (by simp)
    (singletons_settle vals fun v m => ⟨data v m, notRefused v m⟩)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      exact data)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      exact nonempty)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      exact lengths)
    (by
      rw [only]
      intro c member
      rw [List.mem_singleton] at member
      subst member
      exact bodies)
  rw [only] at built
  simpa using built

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open BoundVariables.Controls (sym_data)
open WholeRunWords.Double (noHost)

/-- `id2` calls `neg` on a call of `neg` of its variable; `keep` uses its variable after a call
of `neg` on it. (`not` is a PeTTa primitive, so a program defining it is not ordinary.) -/
def negRows : List Atom :=
  [rule (app "neg" [sym "Yes"]) (sym "No"),
   rule (app "neg" [sym "No"]) (sym "Yes"),
   rule (app "id2" [.var "x"]) (app "neg" [app "neg" [.var "x"]]),
   rule (app "keep" [.var "x"]) (app "pair" [app "neg" [.var "x"], .var "x"])]

theorem one_consFree (a : Atom) (free : RegionsWithVariables.ConsFree a) :
    ∀ b ∈ [a], RegionsWithVariables.ConsFree b := by
  intro b member
  rw [List.mem_singleton] at member
  subst member
  exact free

theorem neg_program : CallProgram negRows := by
  intro row member
  simp only [negRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨rule_consFree (one_consFree _ (.symbol _)), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .item (.symbol _)⟩
  · refine ⟨rule_consFree (one_consFree _ (.symbol _)), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .item (.symbol _)⟩
  · refine ⟨rule_consFree (one_consFree _ (.var _)), fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .node (by decide) fun u member => ?_⟩
    rw [List.mem_singleton] at member
    subst member
    exact .node (by decide) fun w inner => by
      rw [List.mem_singleton] at inner
      subst inner
      exact .item (.var _)
  · refine ⟨rule_consFree (one_consFree _ (.var _)), fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .node (by decide) fun u member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .node (by decide) fun w inner => by
        rw [List.mem_singleton] at inner
        subst inner
        exact .item (.var _)
    · exact .item (.var _)

theorem node_head (name : String) (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (untyped : (Space.ofList negRows).atoms.filter (typeRegion (.symbol name)) = [])
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead name = false)
    (notNative : StdLib.known name = false) (notControl : controlHead name = false) :
    NodeHead noHost negRows name :=
  ⟨.symbol notEmpty notError, untyped, fun impossible => impossible, notInstruction, notIO,
    notNative, notControl⟩

theorem neg_head : NodeHead noHost negRows "neg" :=
  node_head "neg" (by decide) (by decide) (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide)

theorem id2_head : NodeHead noHost negRows "id2" :=
  node_head "id2" (by decide) (by decide) (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide)

theorem keep_head : NodeHead noHost negRows "keep" :=
  node_head "keep" (by decide) (by decide) (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide)

theorem pair_head : NodeHead noHost negRows "pair" :=
  node_head "pair" (by decide) (by decide) (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide)

theorem yes_data : DataAtom (sym "Yes") := sym_data "Yes" (by decide) (by decide)

theorem no_data : DataAtom (sym "No") := sym_data "No" (by decide) (by decide)

theorem neg_defined : ∃ e ∈ negRows.filterMap LiveEquations.equationOfRow, e.head = "neg" := by
  decide +kernel

theorem id2_defined : ∃ e ∈ negRows.filterMap LiveEquations.equationOfRow, e.head = "id2" := by
  decide +kernel

theorem keep_defined : ∃ e ∈ negRows.filterMap LiveEquations.equationOfRow, e.head = "keep" := by
  decide +kernel

theorem one_data {d : Atom} (data : DataAtom d) : ∀ v ∈ [d], DataAtom v := by
  intro v member
  rw [List.mem_singleton] at member
  subst member
  exact data

theorem one_kept {d : Atom} (kept : d ≠ Atom.notReducible) : ∀ v ∈ [d], v ≠ Atom.notReducible := by
  intro v member
  rw [List.mem_singleton] at member
  subst member
  exact kept

/-- `(neg Yes)` settles with `No`. -/
theorem neg_yes : SettlesC noHost negRows (app "neg" [sym "Yes"]) [sym "No"] := by
  have instances : regionInstances negRows "neg" [sym "Yes"] = [sym "No"] := by decide +kernel
  have built := flat_call (Lb := [[sym "No"]]) neg_head neg_defined (one_data yes_data)
    (one_kept (by decide)) (by rw [instances]; simp) (by rw [instances]; rfl)
    (by
      rw [instances]
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
      subst member
      exact .data no_data (by decide))
  simpa using built

/-- `(neg (neg Yes))` settles with `Yes`: the argument's answer `No` is queried again. -/
theorem neg_neg_yes :
    SettlesC noHost negRows (app "neg" [app "neg" [sym "Yes"]]) [sym "Yes"] := by
  have instances : regionInstances negRows "neg" [sym "No"] = [sym "Yes"] := by decide +kernel
  have only : combos [[sym "No"]] = [[sym "No"]] := rfl
  have built := SettlesC.call (dispatch := noHost) (atoms := negRows)
    (ts := [app "neg" [sym "Yes"]]) (Ls := [[sym "No"]]) (fun _ => [[sym "Yes"]]) neg_head
    neg_defined rfl
    (by
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
      subst member
      exact neg_yes)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      exact one_data no_data)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      simp)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      rfl)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      intro p inside
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
      subst inside
      exact .data yes_data (by decide))
  rw [only] at built
  simpa using built

/-- `(id2 Yes)` settles with `Yes`. -/
theorem id2_yes : SettlesC noHost negRows (app "id2" [sym "Yes"]) [sym "Yes"] := by
  have instances : regionInstances negRows "id2" [sym "Yes"] =
      [app "neg" [app "neg" [sym "Yes"]]] := by decide +kernel
  have built := flat_call (Lb := [[sym "Yes"]]) id2_head id2_defined (one_data yes_data)
    (one_kept (by decide)) (by rw [instances]; simp) (by rw [instances]; rfl)
    (by
      rw [instances]
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
      subst member
      exact neg_neg_yes)
  simpa using built

theorem pair_noEquation : (negRows.filterMap LiveEquations.equationOfRow).all
    (fun equation => equation.head != "pair") = true := by
  decide +kernel

/-- `(pair (neg Yes) Yes)` settles with `(pair No Yes)`. -/
theorem pair_built :
    SettlesC noHost negRows (app "pair" [app "neg" [sym "Yes"], sym "Yes"])
      [app "pair" [sym "No", sym "Yes"]] := by
  have only : combos [[sym "No"], [sym "Yes"]] = [[sym "No", sym "Yes"]] := rfl
  have built := SettlesC.build (dispatch := noHost) (atoms := negRows)
    (ts := [app "neg" [sym "Yes"], sym "Yes"]) (Ls := [[sym "No"], [sym "Yes"]]) pair_head
    pair_noEquation rfl
    (by
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact neg_yes
      · exact .data yes_data (by decide))
  rw [only] at built
  simpa using built

/-- `(keep Yes)` settles with `(pair No Yes)`. -/
theorem keep_yes :
    SettlesC noHost negRows (app "keep" [sym "Yes"]) [app "pair" [sym "No", sym "Yes"]] := by
  have instances : regionInstances negRows "keep" [sym "Yes"] =
      [app "pair" [app "neg" [sym "Yes"], sym "Yes"]] := by decide +kernel
  have built := flat_call (Lb := [[app "pair" [sym "No", sym "Yes"]]]) keep_head keep_defined
    (one_data yes_data) (one_kept (by decide)) (by rw [instances]; simp) (by rw [instances]; rfl)
    (by
      rw [instances]
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
      subst member
      exact pair_built)
  simpa using built

/-- PeTTa's run of `(id2 Yes)` from the translation's loader, at fuel 120. -/
theorem id2_value : Streaming.values (Streaming.advance (translate negRows) 120
    (Streaming.enter { state := store negRows } (app "id2" [sym "Yes"]))) = [sym "Yes"] := by
  decide +kernel

/-- PeTTa's run of `(keep Yes)` from the translation's loader, at fuel 120. -/
theorem keep_value : Streaming.values (Streaming.advance (translate negRows) 120
    (Streaming.enter { state := store negRows } (app "keep" [sym "Yes"]))) =
    [app "pair" [sym "No", sym "Yes"]] := by
  decide +kernel

/-- **Positive control: a variable under a call of a call.** `(id2 Yes)` on
`{(= (neg Yes) No), (= (neg No) Yes), (= (id2 $x) (neg (neg $x))), …}`: a complete HE run
exists, every complete HE run publishes `Yes`, and PeTTa's run gives `Yes`. -/
theorem id2_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList negRows) (app "id2" [sym "Yes"]) Atom.undefinedType)
        ⟨Space.ofList negRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList negRows) (app "id2" [sym "Yes"]) Atom.undefinedType)
          ⟨Space.ofList negRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "Yes"]) ∧
      Streaming.values (Streaming.advance (translate negRows) 120
        (Streaming.enter { state := store negRows } (app "id2" [sym "Yes"]))) = [sym "Yes"] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_c policy neg_program id2_yes
  exact ⟨⟨complete, (every N le_rfl).2⟩, id2_value⟩

/-- **Positive control: a variable after a call that extends PeTTa's bindings.** `(keep Yes)` on
`{…, (= (keep $x) (pair (neg $x) $x))}`: every complete HE run publishes `(pair No Yes)`, and
PeTTa's run gives it; the `$x` after `(neg $x)` still reads `Yes`. -/
theorem keep_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList negRows) (app "keep" [sym "Yes"]) Atom.undefinedType)
        ⟨Space.ofList negRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList negRows) (app "keep" [sym "Yes"]) Atom.undefinedType)
          ⟨Space.ofList negRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "pair" [sym "No", sym "Yes"]]) ∧
      Streaming.values (Streaming.advance (translate negRows) 120
        (Streaming.enter { state := store negRows } (app "keep" [sym "Yes"]))) =
        [app "pair" [sym "No", sym "Yes"]] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_c policy neg_program keep_yes
  exact ⟨⟨complete, (every N le_rfl).2⟩, keep_value⟩

/-- **Negative control: the extension is strict.** `(id2 Yes)` does not settle in
`NestedValues`'s sense: its instance calls `neg` on a call. -/
theorem id2_not_settlesN : ¬ NestedValues.SettlesN noHost negRows (app "id2" [sym "Yes"]) := by
  have instances : regionInstances negRows "id2" [sym "Yes"] =
      [app "neg" [app "neg" [sym "Yes"]]] := by decide +kernel
  have idDefined : (negRows.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != "id2") = false := by decide +kernel
  have negDefined : (negRows.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != "neg") = false := by decide +kernel
  intro settles
  cases settles with
  | data data _ => cases data
  | constructor _ noEquation =>
      rw [idDefined] at noEquation
      cases noEquation
  | call _ _ settled =>
      have body := settled (app "neg" [app "neg" [sym "Yes"]]) (by rw [instances]; simp)
      cases body with
      | data data _ => cases data
      | constructor ordinary _ =>
          cases ordinary.arguments (app "neg" [sym "Yes"]) (by simp)
      | call ordinary _ _ =>
          cases ordinary.arguments (app "neg" [sym "Yes"]) (by simp)
      | value head _ =>
          have different := head.noEquation
          rw [negDefined] at different
          cases different
  | value head _ =>
      have different := head.noEquation
      rw [idDefined] at different
      cases different

/-! ### A nondeterministic call followed by a variable -/

/-- `tag` pairs a call with two answers and its variable. -/
def chooseRows : List Atom :=
  [rule (app "choose" []) (sym "a"),
   rule (app "choose" []) (sym "b"),
   rule (app "tag" [.var "x"]) (app "pair" [app "choose" [], .var "x"])]

theorem choose_program : CallProgram chooseRows := by
  intro row member
  simp only [chooseRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨rule_consFree (fun _ member => by cases member), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .item (.symbol _)⟩
  · refine ⟨rule_consFree (fun _ member => by cases member), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .item (.symbol _)⟩
  · refine ⟨rule_consFree (one_consFree _ (.var _)), fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .node (by decide) fun u member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .node (by decide) fun w inner => by cases inner
    · exact .item (.var _)

theorem choose_head : NodeHead noHost chooseRows "choose" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem tag_head : NodeHead noHost chooseRows "tag" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem pair_head_choose : NodeHead noHost chooseRows "pair" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem choose_defined :
    ∃ e ∈ chooseRows.filterMap LiveEquations.equationOfRow, e.head = "choose" := by
  decide +kernel

theorem tag_defined : ∃ e ∈ chooseRows.filterMap LiveEquations.equationOfRow, e.head = "tag" := by
  decide +kernel

theorem a_data' : DataAtom (sym "a") := sym_data "a" (by decide) (by decide)

theorem b_data' : DataAtom (sym "b") := sym_data "b" (by decide) (by decide)

/-- `(choose)` settles with `a`, `b`, in row order. -/
theorem choose_settles : SettlesC noHost chooseRows (app "choose" []) [sym "a", sym "b"] := by
  have instances : regionInstances chooseRows "choose" [] = [sym "a", sym "b"] := by decide +kernel
  have only : combos ([] : List (List Atom)) = [[]] := rfl
  have built := SettlesC.call (dispatch := noHost) (atoms := chooseRows) (ts := []) (Ls := [])
    (fun _ => [[sym "a"], [sym "b"]]) choose_head choose_defined rfl
    (fun p member => by cases member)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      intro v inside
      cases inside)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      simp)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      rfl)
    (by
      rw [only]
      intro vals member
      rw [List.mem_singleton] at member
      subst member
      rw [instances]
      intro p inside
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
        or_false] at inside
      rcases inside with rfl | rfl
      · exact .data a_data' (by decide)
      · exact .data b_data' (by decide))
  rw [only] at built
  simpa using built

theorem pair_noEquation_choose : (chooseRows.filterMap LiveEquations.equationOfRow).all
    (fun equation => equation.head != "pair") = true := by
  decide +kernel

/-- `(pair (choose) Yes)` settles with `(pair a Yes)`, `(pair b Yes)`. -/
theorem tag_pair :
    SettlesC noHost chooseRows (app "pair" [app "choose" [], sym "Yes"])
      [app "pair" [sym "a", sym "Yes"], app "pair" [sym "b", sym "Yes"]] := by
  have only : combos [[sym "a", sym "b"], [sym "Yes"]] =
      [[sym "a", sym "Yes"], [sym "b", sym "Yes"]] := rfl
  have built := SettlesC.build (dispatch := noHost) (atoms := chooseRows)
    (ts := [app "choose" [], sym "Yes"]) (Ls := [[sym "a", sym "b"], [sym "Yes"]]) pair_head_choose
    pair_noEquation_choose rfl
    (by
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact choose_settles
      · exact .data yes_data (by decide))
  rw [only] at built
  simpa using built

/-- `(tag Yes)` settles with `(pair a Yes)`, `(pair b Yes)`. -/
theorem tag_yes :
    SettlesC noHost chooseRows (app "tag" [sym "Yes"])
      [app "pair" [sym "a", sym "Yes"], app "pair" [sym "b", sym "Yes"]] := by
  have instances : regionInstances chooseRows "tag" [sym "Yes"] =
      [app "pair" [app "choose" [], sym "Yes"]] := by decide +kernel
  have built := flat_call
    (Lb := [[app "pair" [sym "a", sym "Yes"], app "pair" [sym "b", sym "Yes"]]]) tag_head
    tag_defined (one_data yes_data) (one_kept (by decide)) (by rw [instances]; simp)
    (by rw [instances]; rfl)
    (by
      rw [instances]
      intro p member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at member
      subst member
      exact tag_pair)
  simpa using built

/-- PeTTa's run of `(tag Yes)` from the translation's loader, at fuel 120. -/
theorem tag_value : Streaming.values (Streaming.advance (translate chooseRows) 120
    (Streaming.enter { state := store chooseRows } (app "tag" [sym "Yes"]))) =
    [app "pair" [sym "a", sym "Yes"], app "pair" [sym "b", sym "Yes"]] := by
  decide +kernel

/-- **Positive control: a variable after a call with two answers.** `(tag Yes)` on
`{(= (choose) a), (= (choose) b), (= (tag $x) (pair (choose) $x))}`: PeTTa answers each clause of
`(choose)` under that clause's bindings and still reads `$x` as `Yes` after each; every complete HE
run publishes `(pair a Yes)`, `(pair b Yes)`, in that order, as PeTTa does. -/
theorem tag_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList chooseRows) (app "tag" [sym "Yes"]) Atom.undefinedType)
        ⟨Space.ofList chooseRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList chooseRows) (app "tag" [sym "Yes"]) Atom.undefinedType)
          ⟨Space.ofList chooseRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) =
          [app "pair" [sym "a", sym "Yes"], app "pair" [sym "b", sym "Yes"]]) ∧
      Streaming.values (Streaming.advance (translate chooseRows) 120
        (Streaming.enter { state := store chooseRows } (app "tag" [sym "Yes"]))) =
        [app "pair" [sym "a", sym "Yes"], app "pair" [sym "b", sym "Yes"]] := by
  obtain ⟨complete, N, every⟩ := every_complete_run_c policy choose_program tag_yes
  exact ⟨⟨complete, (every N le_rfl).2⟩, tag_value⟩

end Controls

#print axioms keeps_renamed
#print axioms Shows.keeps
#print axioms args_over
#print axioms run_clauses_over
#print axioms applies_defined
#print axioms over_call
#print axioms over_build
#print axioms query_open_determined
#print axioms settlesC_agree
#print axioms settlesC_determined
#print axioms every_complete_run_c
#print axioms Controls.id2_every_run
#print axioms Controls.keep_every_run
#print axioms Controls.id2_not_settlesN
#print axioms Controls.tag_every_run

end NestedCalls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
