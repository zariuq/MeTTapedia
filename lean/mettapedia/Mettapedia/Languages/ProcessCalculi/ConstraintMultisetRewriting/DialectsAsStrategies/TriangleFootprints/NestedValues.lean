import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedEveryRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.BoundVariables

/-!
# Nested uses of a variable: bodies that build values

`BoundVariables` takes flat bodies: a variable occurs as an argument of the body's head. Here a
variable may occur at any depth of a value the body builds: `(= (nest $x) (pair (pair $x $x) $x))`,
`(= (dup $x) (Cons $x (Cons $x Nil)))`.

* **HE** reads the body as its instance, a ground value (`BoundVariables.work_read`, which needs
  only that the body's variables are bound), and evaluates that value as a nested call of
  constructors (`NestedArguments.nested_constructor_agree`, `NestedEveryRun.nested_determined`).
* **PeTTa** runs the renamed open tree: each inner node is a constructor (not callable), so it
  enters it as data, evaluates its items, resolving each variable when it reaches it, and builds the
  node under the same bindings (`value_run`). No binding is added inside a value, so the variables
  further right still read the call's matching.

## Results

* `SettlesN`: `SettlesV` with a fourth case, a value: a constructor head applied to values.
* `settlesN_agree`, `answersN_agree`: both machines evaluate every settling term to the same answer
  list, PeTTa for every open presentation.
* `settlesN_determined`, `every_complete_run_n`: every complete run of HE (historical lookup)
  publishes PeTTa's values.
* Controls `nest_every_run`, `dup_every_run`; `nest_not_settlesV` (the extension is strict).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace NestedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load observe)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (applyTypeValuation)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun

/-! ## Constructor heads, value trees and values -/

/-- **A constructor head of the program**: undeclared, no host operation, no instruction, no
PeTTa primitive or I/O head, no special form, and no equation. -/
structure ConstructorHead (dispatch : GroundedDispatch) (atoms : List Atom) (g : String) : Prop where
  head : DataAtom (.symbol g)
  untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol g)) = []
  notHost : ¬ dispatch.executable (.symbol g)
  notInstruction : Minimal.embeddedInstruction (.expression [.symbol g]) = false
  notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead g = false
  notNative : StdLib.known g = false
  notControl : controlHead g = false
  noEquation : (atoms.filterMap LiveEquations.equationOfRow).all (fun e => e.head != g) = true

namespace ConstructorHead

variable {dispatch : GroundedDispatch} {atoms : List Atom} {g : String}

theorem notCollapse (head : ConstructorHead dispatch atoms g) : g ≠ "collapse" := by
  intro same
  have control := head.notControl
  rw [same] at control
  simp [controlHead] at control

theorem notOnce (head : ConstructorHead dispatch atoms g) : g ≠ "once" := by
  intro same
  have control := head.notControl
  rw [same] at control
  simp [controlHead] at control

theorem instruction (head : ConstructorHead dispatch atoms g) (items : List Atom) :
    Minimal.embeddedInstruction (.expression (.symbol g :: items)) = false :=
  head.notInstruction

theorem notFunction (head : ConstructorHead dispatch atoms g) : g ≠ "function" := by
  intro same
  have instruction := head.notInstruction
  rw [same] at instruction
  simp [Minimal.embeddedInstruction] at instruction

end ConstructorHead

/-- **A value tree**: a body built from items (symbols, grounded values, variables) by constructor
heads. -/
inductive ValueTree (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → Prop
  | item {u : Atom} : FlatItem u → ValueTree dispatch atoms u
  | node {g : String} {us : List Atom} : ConstructorHead dispatch atoms g →
      (∀ u ∈ us, ValueTree dispatch atoms u) →
      ValueTree dispatch atoms (.expression (.symbol g :: us))

/-- **A ground value**: a data atom, or a constructor head applied to ground values. -/
inductive Value (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → Prop
  | data {a : Atom} : DataAtom a → Value dispatch atoms a
  | node {g : String} {vs : List Atom} : ConstructorHead dispatch atoms g →
      (∀ v ∈ vs, Value dispatch atoms v) → Value dispatch atoms (.expression (.symbol g :: vs))

variable {dispatch : GroundedDispatch}

theorem forall₂_left_exists' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ a ∈ l, ∃ b, b ∈ m ∧ R a b
  | [], [], .nil, a, member => by cases member
  | _ :: _, _ :: _, .cons here rest, a, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, List.mem_cons_self, here⟩
      · obtain ⟨b, inM, related⟩ := forall₂_left_exists' rest a inRest
        exact ⟨b, List.mem_cons_of_mem _ inM, related⟩

theorem mem_typeVarsList {x : String} : ∀ {items : List Atom},
    x ∈ TypeSubst.typeVarsList items → ∃ u ∈ items, x ∈ TypeSubst.typeVars u
  | [], member => by simp [TypeSubst.typeVarsList] at member
  | u :: rest, member => by
      simp only [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with here | later
      · exact ⟨u, List.mem_cons_self, here⟩
      · obtain ⟨w, inRest, inW⟩ := mem_typeVarsList later
        exact ⟨w, List.mem_cons_of_mem _ inRest, inW⟩

theorem value_answerable {atoms : List Atom} {v : Atom} (value : Value dispatch atoms v) :
    Answerable v := by
  induction value with
  | data data => exact answerable_of_data data
  | node head _ ih => exact app_answerable head.head ih

theorem value_fixed {atoms : List Atom} {v : Atom} (value : Value dispatch atoms v)
    (rename : String → String) :
    Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename v = v := by
  induction value with
  | data data =>
      cases data <;> simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  | @node g vs _ _ ih =>
      simp only [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars,
        List.map_cons]
      rw [map_fixed ih]

/-- What HE needs of a value body. -/
theorem value_facts {atoms : List Atom} {g : String} {vs : List Atom}
    (head : ConstructorHead dispatch atoms g) (each : ∀ v ∈ vs, Value dispatch atoms v) :
    BodyFacts (.expression (.symbol g :: vs)) := by
  have answerable := value_answerable (Value.node head each)
  refine ⟨answerable.closed, fun policy pending => ?_, (fun same => by cases same), ?_,
    value_fixed (Value.node head each), answerable.ground⟩
  · obtain ⟨⟨body, same⟩, _⟩ := pending
    rw [Entry.Value.erase_ofAtom] at same
    simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact head.notFunction same.1
  · exact answerable.notStopped

theorem combos_singletons : ∀ (vs : List Atom), combos (vs.map fun v => [v]) = [vs]
  | [] => rfl
  | v :: vs => by
      simp only [List.map_cons, combos, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        combos_singletons vs, List.map_cons, List.map_nil]

/-! ## HE on values -/

/-- **HE and PeTTa (closed presentation) evaluate a value to itself**, by
`NestedArguments.nested_constructor_agree`. -/
theorem value_joint {lookup : CastLookup} {policy : Policy} (answers : AnswersUndefined lookup)
    {atoms : List Atom} (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    {v : Atom} (value : Value dispatch atoms v) : Joint dispatch lookup policy atoms v [v] := by
  induction value with
  | data data => exact joint_data answers atoms data
  | @node g vs head each ih =>
      have args : List.Forall₂ (Joint dispatch lookup policy atoms) vs (vs.map fun v => [v]) := by
        clear each
        induction vs with
        | nil => exact .nil
        | cons v rest restIh =>
            exact .cons (ih v List.mem_cons_self)
              (restIh fun w member => ih w (List.mem_cons_of_mem _ member))
      have joint := nested_constructor_agree answers program head.head head.untyped head.notHost
        head.notInstruction head.notCollapse head.notOnce
        (sourceControlForm_of_head head.notControl _) head.notIO head.notNative
        (value_answerable (Value.node head each)).closed head.noEquation args
      rw [combos_singletons] at joint
      simpa using joint

/-- **HE's source semantics determines a value's answer**, itself (historical lookup). -/
theorem value_settled {policy : Policy} {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {v : Atom}
    (value : Value dispatch atoms v) : Settled dispatch policy atoms v [v] := by
  induction value with
  | data data => exact data_settled data
  | @node g vs head each ih =>
      have args : List.Forall₂ (Settled dispatch policy atoms) vs (vs.map fun v => [v]) := by
        clear each
        induction vs with
        | nil => exact .nil
        | cons v rest restIh =>
            exact .cons (ih v List.mem_cons_self)
              (restIh fun w member => ih w (List.mem_cons_of_mem _ member))
      have settled := nested_determined (dispatch := dispatch) (policy := policy) head.head
        head.untyped (value_answerable (Value.node head each)).closed args
        (fun vals => [.expression (.symbol g :: vals)]) (fun vals member => by
          rw [combos_singletons, List.mem_singleton] at member
          subst member
          exact ⟨fun a inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact value_answerable (Value.node head each),
            query_absent program head.head (head.instruction _)
              (fun w member => value_answerable (each w member))
              (regionBodies_nil_of_no_equation _ head.noEquation)⟩)
      rw [combos_singletons] at settled
      simpa using settled

/-! ## PeTTa on value trees -/

/-- `u` presents the ground term `v` as a value under `σ`: a value tree whose variables are bound
to literals, instantiated to `v`. -/
structure ValuePresents (dispatch : GroundedDispatch) (atoms : List Atom) (σ : Subst)
    (u v : Atom) : Prop where
  tree : ValueTree dispatch atoms u
  bound : ∀ x ∈ TypeSubst.typeVars u, Lit (applySubst σ (.var x))
  instantiates : applySubst σ u = v

theorem substList_map (σ : Subst) : ∀ xs : List Atom,
    applySubst.applySubstList σ xs = xs.map (applySubst σ)
  | [] => rfl
  | x :: xs => by simp [applySubst.applySubstList, substList_map σ xs]

theorem applySubst_node (σ : Subst) (g : String) (us : List Atom) :
    applySubst σ (.expression (.symbol g :: us)) = .expression (.symbol g :: us.map (applySubst σ)) := by
  simp only [applySubst, applySubst.applySubstList, substList_map]

/-- **PeTTa runs a value tree to its value**, under the same bindings: each node is entered as
data, its items are evaluated (each variable resolved when reached), and the node is built. -/
theorem value_run {atoms : List Atom} (world : Streaming.World)
    (privateCode : world.privateCode = []) (σ : Subst) (range : Unifying.GroundRange σ) :
    ∀ {u : Atom}, ValueTree dispatch atoms u →
      (∀ x ∈ TypeSubst.typeVars u, Lit (applySubst σ (.var x))) →
      ∀ (frames : List Streaming.Frame) (older : List Streaming.Job)
        (answers : List Unifying.Answer) (next : Nat),
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.evaluate σ u, frames⟩ :: older, answers, next⟩
          ⟨world, .execute ⟨.returned [⟨applySubst σ u, σ⟩], frames⟩ :: older, answers, next⟩ := by
  intro u tree
  induction tree with
  | @item u flat =>
      intro bound frames older answers next
      have presented : PresentsItem σ u (applySubst σ u) := by
        cases flat with
        | symbol name =>
            have same : applySubst σ (.symbol name) = .symbol name := by simp [applySubst]
            rw [same]
            exact ⟨.symbol name, Or.inl rfl⟩
        | grounded value =>
            have same : applySubst σ (.grounded value) = .grounded value := by simp [applySubst]
            rw [same]
            exact ⟨.grounded value, Or.inl rfl⟩
        | var name =>
            exact ⟨bound name (by simp [TypeSubst.typeVars]), Or.inr ⟨name, rfl, rfl⟩⟩
      exact .single (PeTTaOpenRuns.evaluate_item world σ presented frames older answers next)
  | @node g us head children ih =>
      intro bound frames older answers next
      have childBound : ∀ u ∈ us, ∀ x ∈ TypeSubst.typeVars u, Lit (applySubst σ (.var x)) :=
        fun u member x inU => bound x (by
          simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
          exact Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
            member x inU)
      have notCallable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead g || StdLib.known g ||
          (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == g)) =
          false := by
        rw [privateCode, head.notIO, head.notNative]
        simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
        apply List.any_eq_false.mpr
        intro e member
        have different := List.all_eq_true.mp head.noEquation e member
        simpa using different
      -- the items, each run to its value under the same bindings
      have values : ∀ (rest : List Atom), (∀ u ∈ rest, u ∈ us) →
          ∀ (held : List Atom) (index : Nat) (frames' : List Streaming.Frame)
            (older' : List Streaming.Job) (answers' : List Unifying.Answer) (next' : Nat),
          PeTTaRuns.PSteps (translate atoms)
            ⟨world, .execute ⟨.arguments σ .data rest held index, frames'⟩ :: older', answers', next'⟩
            ⟨world, .execute ⟨.arguments σ .data [] (held ++ rest.map (applySubst σ))
              (index + rest.length), frames'⟩ :: older', answers', next'⟩ := by
        intro rest
        induction rest with
        | nil =>
            intro _ held index frames' older' answers' next'
            simp only [List.map_nil, List.append_nil, List.length_nil, Nat.add_zero]
            exact .refl
        | cons u rest restIh =>
            intro within held index frames' older' answers' next'
            have inUs := within u List.mem_cons_self
            have first : PeTTaRuns.PSteps (translate atoms)
                ⟨world, .execute ⟨.arguments σ .data (u :: rest) held index, frames'⟩ :: older',
                  answers', next'⟩
                ⟨world, .execute ⟨.arguments σ .data rest (held ++ [applySubst σ u]) (index + 1),
                  frames'⟩ :: older', answers', next'⟩ := by
              refine .head (PeTTaRuns.evaluate_argument world σ .data u rest held index rfl frames'
                older' answers' next') ?_
              refine .trans (ih u inUs (childBound u inUs) _ older' answers' next') ?_
              refine .head (PeTTaRuns.return_argument world ⟨applySubst σ u, σ⟩ .data rest held index
                frames' older' answers' next') ?_
              exact .single (PeTTaRuns.alternatives world _ frames' older' answers' next')
            have later := restIh (fun w member => within w (List.mem_cons_of_mem _ member))
              (held ++ [applySubst σ u]) (index + 1) frames' older' answers' next'
            refine first.trans ?_
            simp only [List.map_cons, List.length_cons]
            rw [show index + (rest.length + 1) = index + 1 + rest.length by omega]
            simpa only [List.append_assoc, List.singleton_append] using later
      refine .head (PeTTaRuns.data_enter world σ head.notCollapse head.notOnce
        (sourceControlForm_of_head head.notControl us) notCallable frames older answers next) ?_
      refine .trans (PeTTaOpenRuns.argument_open world σ .data
        (⟨.symbol g, Or.inl rfl⟩ : PresentsItem σ (.symbol g) (.symbol g)) us [] 0 rfl frames older
        answers next) ?_
      refine .trans (values us (fun _ member => member) ([] ++ [.symbol g]) (0 + 1) frames older
        answers next) ?_
      have built := PeTTaRuns.construct (registry := translate atoms) world σ
        (([] ++ [Atom.symbol g]) ++ us.map (applySubst σ)) (0 + 1 + us.length) frames older answers
        next
      have resolved : (([] ++ [Atom.symbol g]) ++ us.map (applySubst σ)).map (Unifying.resolve σ) =
          Atom.symbol g :: us.map (applySubst σ) := by
        rw [List.nil_append, List.singleton_append, List.map_cons, List.map_map]
        have headSame : Unifying.resolve σ (.symbol g) = .symbol g := by
          simp [Unifying.resolve, applySubst]
        rw [headSame]
        congr 1
        exact List.map_congr_left fun u _ => Unifying.resolve_resolve range u
      rw [resolved, ← applySubst_node] at built
      exact .single built

/-! ## Presentations, flat or as value trees -/

/-- **`b` presents `t` under `σ`**, flatly (`Presents`) or as a value tree. -/
def PresentsN (dispatch : GroundedDispatch) (atoms : List Atom) (σ : Subst) (b t : Atom) : Prop :=
  Presents σ b t ∨ ValuePresents dispatch atoms σ b t

/-- **PeTTa's streaming machine evaluates every flat or value presentation of `t` to `L`.** -/
def PeTTaOpenN (dispatch : GroundedDispatch) (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ (frames : List Streaming.Frame) (K : Atom → List Atom), (∀ v ∈ L, Delivers atoms frames K v) →
  ∀ (world : Streaming.World) (σ : Subst), world.state = store atoms → world.privateCode = [] →
    Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (b : Atom), PresentsN dispatch atoms σ b t →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = L.flatMap K ∧
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.evaluate σ b, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

/-- A value presentation of `v` runs to `v` and delivers it. -/
theorem petta_value_presented {atoms : List Atom} {t : Atom} {frames : List Streaming.Frame}
    {K : Atom → List Atom} (deliver : Delivers atoms frames K t) {world : Streaming.World}
    {σ : Subst} (state : world.state = store atoms) (privateCode : world.privateCode = [])
    (range : Unifying.GroundRange σ) (fresh : ∀ k, Unifying.FreshFor (world.uses + k) σ) {b : Atom}
    (presented : ValuePresents dispatch atoms σ b t) (older : List Streaming.Job)
    (answers : List Unifying.Answer) (next : Nat) :
    ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
      out.map (fun answer => Unifying.resolve answer.bindings answer.value) = [t].flatMap K ∧
      PeTTaRuns.PSteps (translate atoms)
        ⟨world, .execute ⟨.evaluate σ b, frames⟩ :: older, answers, next⟩
        ⟨{world with uses := uses}, older, answers ++ out, next⟩ := by
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver world σ state privateCode range fresh older
    answers next
  have run := value_run world privateCode σ range presented.tree presented.bound frames older
    answers next
  rw [presented.instantiates] at run
  exact ⟨uses, out, grown, by simp [valuesOut], run.trans path⟩

/-- **A data atom, every presentation.** -/
theorem petta_openN_data (atoms : List Atom) {d : Atom} (data : DataAtom d) :
    PeTTaOpenN dispatch atoms d [d] := by
  intro frames K deliver world σ state privateCode range fresh b presented older answers next
  rcases presented with flat | tree
  · exact petta_open_data atoms data frames K deliver world σ state privateCode range fresh b flat
      older answers next
  · exact petta_value_presented (deliver d List.mem_cons_self) state privateCode range fresh tree
      older answers next

/-- **A constructor call, every presentation.** -/
theorem petta_openN_constructor {atoms : List Atom} {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true) :
    PeTTaOpenN dispatch atoms (.expression (.symbol f :: args)) [.expression (.symbol f :: args)] := by
  intro frames K deliver world σ state privateCode range fresh b presented older answers next
  rcases presented with flat | tree
  · exact petta_open_constructor ordinary noEquation frames K deliver world σ state privateCode
      range fresh b flat older answers next
  · exact petta_value_presented (deliver _ List.mem_cons_self) state privateCode range fresh tree
      older answers next

theorem items_flat {σ : Subst} : ∀ {us vs : List Atom}, List.Forall₂ (PresentsItem σ) us vs →
    ∀ u ∈ us, FlatItem u
  | [], [], .nil, u, member => by cases member
  | _ :: _, _ :: _, .cons here rest, u, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · rcases here.2 with rfl | ⟨x, rfl, _⟩
        · cases here.1 with
          | symbol name => exact .symbol name
          | grounded value => exact .grounded value
        · exact .var x
      · exact items_flat rest u inRest

theorem items_bound {σ : Subst} : ∀ {us vs : List Atom}, List.Forall₂ (PresentsItem σ) us vs →
    ∀ u ∈ us, ∀ x ∈ TypeSubst.typeVars u, Lit (applySubst σ (.var x))
  | [], [], .nil, u, member => by cases member
  | _ :: _, _ :: _, .cons here rest, u, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · intro x inU
        rcases here.2 with rfl | ⟨y, rfl, bound⟩
        · cases here.1 <;> simp [TypeSubst.typeVars] at inU
        · simp only [TypeSubst.typeVars, List.mem_singleton] at inU
          subst inU
          rw [bound]
          exact here.1
      · exact items_bound rest u inRest

theorem items_instantiate {σ : Subst} : ∀ {us vs : List Atom}, List.Forall₂ (PresentsItem σ) us vs →
    us.map (applySubst σ) = vs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons here rest => by
      rw [List.map_cons, items_instantiate rest]
      congr 1
      rcases here.2 with rfl | ⟨y, rfl, bound⟩
      · cases here.1 <;> simp [applySubst]
      · exact bound

/-- **A value, every presentation.** -/
theorem petta_openN_value {atoms : List Atom} {g : String} {vs : List Atom}
    (head : ConstructorHead dispatch atoms g) :
    PeTTaOpenN dispatch atoms (.expression (.symbol g :: vs)) [.expression (.symbol g :: vs)] := by
  intro frames K deliver world σ state privateCode range fresh b presented older answers next
  rcases presented with flat | tree
  · obtain ⟨us, rfl, _, items⟩ := presents_call flat
    have asTree : ValuePresents dispatch atoms σ (.expression (.symbol g :: us))
        (.expression (.symbol g :: vs)) := by
      refine ⟨.node head fun u member => .item (items_flat items u member), fun x member => ?_, ?_⟩
      · simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append] at member
        obtain ⟨u, inUs, inU⟩ := mem_typeVarsList member
        exact items_bound items u inUs x inU
      · rw [applySubst_node, items_instantiate items]
    exact petta_value_presented (deliver _ List.mem_cons_self) state privateCode range fresh asTree
      older answers next
  · exact petta_value_presented (deliver _ List.mem_cons_self) state privateCode range fresh tree
      older answers next

/-! ## The program condition and the renamed bodies -/

/-- **A row whose body uses only its left side's variables, and is flat or a value tree.** -/
def NestedRow (dispatch : GroundedDispatch) (atoms : List Atom) (row : Atom) : Prop :=
  ∀ lhs rhs, row = .expression [.symbol "=", lhs, rhs] →
    (∀ x ∈ TypeSubst.typeVars rhs, x ∈ TypeSubst.typeVars lhs) ∧
      (FlatBody rhs ∨ ValueTree dispatch atoms rhs)

/-- The program condition: symbol-headed, `cons`-free equations whose bodies use only their left
side's variables, flat or as value trees. -/
def NestedProgram (dispatch : GroundedDispatch) (atoms : List Atom) : Prop :=
  ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row ∧ NestedRow dispatch atoms row

theorem NestedProgram.scoped {atoms : List Atom} (program : NestedProgram dispatch atoms) :
    ScopedProgram atoms :=
  fun row member => ⟨(program row member).1,
    fun lhs rhs same => ((program row member).2 lhs rhs same).1⟩

/-- **A renamed value tree presents its instance**, under the matching bindings renamed for the use
and followed by the caller's. -/
theorem tree_renamed {atoms : List Atom} {use : Nat} {bound σ : Subst}
    (fresh : Unifying.FreshFor use σ) {ps args : List Atom} (argsData : ∀ a ∈ args, DataAtom a)
    (instantiated : ps.map (applyTypeValuation (RegionsWithVariables.asValuation bound)) = args) :
    ∀ {body : Atom}, ValueTree dispatch atoms body →
      (∀ x ∈ TypeSubst.typeVars body, x ∈ TypeSubst.typeVarsList ps) →
      ValuePresents dispatch atoms (Unifying.renameKeys use bound ++ σ) (Unifying.rename use body)
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
            simp only [applySubst]
            rw [looked, found, Option.getD_some]
          have readBound : applySubst bound (.var name) = value := by
            simp only [applySubst]
            rw [found, Option.getD_some]
          have valueLit : Lit value := by
            have lit := lit_of_data data
            simpa [RegionsWithVariables.asValuation, found] using lit
          refine ⟨.item (.var _), fun x member => ?_, by rw [readRenamed, readBound]⟩
          simp only [TypeSubst.typeVars, List.mem_singleton] at member
          subst member
          rw [readRenamed]
          exact valueLit
  | @node g us head children ih =>
      intro varsBound
      have childBound : ∀ u ∈ us, ∀ x ∈ TypeSubst.typeVars u, x ∈ TypeSubst.typeVarsList ps :=
        fun u member x inU => varsBound x (by
          simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
          exact Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
            member x inU)
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
      refine ⟨.node head fun u member => ?_, fun x member => ?_, ?_⟩
      · obtain ⟨w, inUs, rfl⟩ := List.mem_map.mp member
        exact (each w inUs).tree
      · simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append] at member
        obtain ⟨u, inMapped, inU⟩ := mem_typeVarsList member
        obtain ⟨w, inUs, rfl⟩ := List.mem_map.mp inMapped
        exact (each w inUs).bound x inU
      · rw [applySubst_node, List.map_map]
        congr 2
        exact List.map_congr_left fun w member => (each w member).instantiates

/-- Each selected equation of a nested program presents its instance, flatly or as a value tree. -/
theorem selected_instance_N {atoms : List Atom} (program : NestedProgram dispatch atoms)
    {e : SpaceSemantics.Equation} (live : e ∈ atoms.filterMap LiveEquations.equationOfRow)
    {args : List Atom} (argsData : ∀ a ∈ args, DataAtom a) {bound : Subst}
    (matched : SpaceSemantics.matchValue.matchValues [] e.arguments args = some bound)
    (use : Nat) {σ : Subst} (fresh : Unifying.FreshFor use σ) :
    PresentsN dispatch atoms (Unifying.renameKeys use bound ++ σ) (Unifying.rename use e.body)
      (applySubst bound e.body) := by
  obtain ⟨row, inAtoms, found⟩ := List.mem_filterMap.mp live
  have shape := LiveEquations.equationOfRow_eq_some found
  obtain ⟨consFree, nestedRow⟩ := program row inAtoms
  subst shape
  obtain ⟨varsBound, shapeBody⟩ := nestedRow _ e.body rfl
  obtain ⟨h, ps, leftShape, psFree⟩ := consFree _ e.body rfl
  simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at leftShape
  obtain ⟨_, rfl⟩ := leftShape
  obtain ⟨_, _, instanceArgs⟩ := RegionsWithVariables.sound_list e.arguments
    (fun p m => RegionsWithVariables.sound (psFree p m)) [] bound args matched
  have inArgs : ∀ x ∈ TypeSubst.typeVars e.body, x ∈ TypeSubst.typeVarsList e.arguments :=
    fun x member => by
      have := varsBound x member
      simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using this
  rcases shapeBody with flat | tree
  · exact .inl (presents_renamed fresh argsData
      (instanceArgs bound (RegionsWithVariables.Extends.refl bound)) flat inArgs)
  · exact .inr (tree_renamed fresh argsData
      (instanceArgs bound (RegionsWithVariables.Extends.refl bound)) tree inArgs)

/-! ## PeTTa's selected clauses, with flat or value bodies -/

theorem run_clauses_N {atoms : List Atom} (program : NestedProgram dispatch atoms) {σ : Subst}
    {values : List Atom} (valuesData : ∀ v ∈ values, DataAtom v) (range : Unifying.GroundRange σ)
    (frames : List Streaming.Frame) (K : Atom → List Atom) :
    ∀ (chosen : List SpaceSemantics.Equation) (use : Nat) (Ls : List (List Atom)),
      (∀ e ∈ chosen, e ∈ atoms.filterMap LiveEquations.equationOfRow) →
      List.Forall₂ (fun b L => PeTTaOpenN dispatch atoms b L) (matchingInstances values chosen) Ls →
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
          exact run_clauses_N program valuesData range frames K rest (use + 1) Ls liveRest related
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
              have presented := selected_instance_N program (live e List.mem_cons_self) valuesData
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
              obtain ⟨uses₂, out₂, grown₂, values₂, path₂⟩ := run_clauses_N program valuesData
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

/-- **A call of a defined head, every flat or value presentation.** -/
theorem petta_openN_call {atoms : List Atom} (program : NestedProgram dispatch atoms) {f : String}
    {args : List Atom} (ordinary : Ordinary dispatch atoms f args)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length)
    {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => PeTTaOpenN dispatch atoms b L) (regionInstances atoms f args)
      Ls) :
    PeTTaOpenN dispatch atoms (.expression (.symbol f :: args)) Ls.flatten := by
  intro frames K deliver world σ state privateCode range fresh b presented older answers next
  obtain ⟨e, live, eHead, arity⟩ := defined
  have flat : Presents σ b (.expression (.symbol f :: args)) := by
    rcases presented with flat | tree
    · exact flat
    · exfalso
      have shaped := tree.instantiates
      cases tree.tree with
      | item flat =>
          cases flat with
          | symbol name => simp [applySubst] at shaped
          | grounded value => simp [applySubst] at shaped
          | var name =>
              have lit := tree.bound name (by simp [TypeSubst.typeVars])
              rw [shaped] at lit
              cases lit
      | node head _ =>
          rw [applySubst_node] at shaped
          simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at shaped
          rw [shaped.1] at head
          have different := List.all_eq_true.mp head.noEquation e live
          simp [eHead] at different
  obtain ⟨us, rfl, notControl, items⟩ := presents_call flat
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      true := by
    rw [privateCode, ordinary.notIO, ordinary.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    exact List.any_eq_true.mpr ⟨e, live, by simp [eHead]⟩
  have groundVals : ∀ v ∈ args, isGroundAtom v = true :=
    fun v member => (answerable_of_data (ordinary.arguments v member)).ground
  have liveEquations : Unifying.codeEquations world.state world.privateCode =
      atoms.filterMap LiveEquations.equationOfRow := by
    rw [state, privateCode]
    simp only [Unifying.codeEquations, List.nil_append, LiveEquations.liveEquations, store_core]
  set chosen := Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f args.length
    with chosenEq
  have arityKnown : args.length ∈ Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
      (Unifying.codeRegistry (translate atoms) world.privateCode) f := by
    rw [privateCode]
    simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry, List.nil_append,
      translate_equations]
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [eHead]⟩, arity⟩
  have related : List.Forall₂ (fun b L => PeTTaOpenN dispatch atoms b L)
      (matchingInstances args chosen) Ls := by
    rw [chosenEq, ← regionInstances_eq]
    exact bodies
  have chosenLive : ∀ e' ∈ chosen, e' ∈ atoms.filterMap LiveEquations.equationOfRow :=
    fun e' member => (List.mem_filter.mp member).1
  have entered := PeTTaOpenRuns.arguments_open (registry := translate atoms) world σ (.function f)
    (fun index => argumentIsRaw_false ordinary.notNative ordinary.untyped index) frames older
    answers next us args [] 0 items
  rw [List.nil_append] at entered
  obtain ⟨uses, out, grown, valuesOut, path⟩ := run_clauses_N program ordinary.arguments range frames
    K chosen world.uses Ls chosenLive related deliver
    {world with uses := world.uses + chosen.length} state privateCode (by simp only; omega) fresh
    older answers next
  refine ⟨uses, out, by simp only at grown; omega, valuesOut, ?_⟩
  refine .head (PeTTaRuns.call_enter world σ ordinary.notCollapse ordinary.notOnce notControl
    callable frames older answers next) ?_
  refine entered.trans ?_
  have applied : Unifying.application (Unifying.codeRegistry (translate atoms) world.privateCode)
      (Unifying.codeEquations world.state world.privateCode) f
      (args.map (Unifying.resolve σ)) σ world.uses =
      some (.sequence (Unifying.renamedClauses σ args world.uses chosen) [], chosen.length) := by
    rw [PeTTaRuns.map_resolve_ground σ groundVals, liveEquations]
    unfold Unifying.application
    rw [if_pos arityKnown]
    simp only
    rw [Unifying.selections_eq_renamedClauses range groundVals world.uses _ fresh]
    rfl
  refine .head (PeTTaRuns.apply_equations world σ args (0 + us.length) ordinary.notIO
    ordinary.notNative applied frames older answers next) ?_
  refine .head (PeTTaRuns.alternatives _ _ frames older answers next) ?_
  exact path

/-! ## The terms that settle, with value bodies -/

/-- **The fragment with values.** `SettlesV`'s three cases, and a value: a constructor head applied
to values. Still a condition on the program. -/
inductive SettlesN (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → Prop
  | data {a : Atom} : DataAtom a → a ≠ Atom.notReducible → SettlesN dispatch atoms a
  | constructor {f : String} {args : List Atom} : Ordinary dispatch atoms f args →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      SettlesN dispatch atoms (.expression (.symbol f :: args))
  | call {f : String} {args : List Atom} : Ordinary dispatch atoms f args →
      regionInstances atoms f args ≠ [] →
      (∀ b ∈ regionInstances atoms f args, SettlesN dispatch atoms b) →
      SettlesN dispatch atoms (.expression (.symbol f :: args))
  | value {g : String} {vs : List Atom} : ConstructorHead dispatch atoms g →
      (∀ v ∈ vs, Value dispatch atoms v) → SettlesN dispatch atoms (.expression (.symbol g :: vs))

theorem settlesN_facts {atoms : List Atom} {t : Atom} (settles : SettlesN dispatch atoms t) :
    BodyFacts t := by
  cases settles with
  | data data notRefused => exact settles_facts (Settles.data (dispatch := dispatch) (atoms := atoms)
      data notRefused)
  | constructor ordinary _ => exact call_facts ordinary
  | call ordinary _ _ => exact call_facts ordinary
  | value head each => exact value_facts head each

theorem value_tree {atoms : List Atom} {v : Atom} (value : Value dispatch atoms v) :
    ValueTree dispatch atoms v := by
  induction value with
  | data data =>
      cases data with
      | symbol _ _ => exact .item (.symbol _)
      | grounded value => exact .item (.grounded value)
  | node head _ ih => exact .node head ih

/-- A ground term of the fragment presents itself. -/
theorem presentsN_self {atoms : List Atom} {t : Atom} (settles : SettlesN dispatch atoms t)
    (σ : Subst) : PresentsN dispatch atoms σ t t := by
  have items : ∀ (args : List Atom), (∀ a ∈ args, DataAtom a) →
      List.Forall₂ (PresentsItem σ) args args := by
    intro args data
    induction args with
    | nil => exact .nil
    | cons a rest ih =>
        exact .cons ⟨lit_of_data (data a List.mem_cons_self), Or.inl rfl⟩
          (ih fun b member => data b (List.mem_cons_of_mem _ member))
  cases settles with
  | data data _ => exact .inl (.item ⟨lit_of_data data, Or.inl rfl⟩)
  | constructor ordinary _ => exact .inl (.call _ ordinary.notControl (items _ ordinary.arguments))
  | call ordinary _ _ => exact .inl (.call _ ordinary.notControl (items _ ordinary.arguments))
  | @value g vs head each =>
      have answerable := value_answerable (Value.node head each)
      have noVars : ∀ x ∈ TypeSubst.typeVars (.expression (.symbol g :: vs)),
          Lit (applySubst σ (.var x)) := by
        intro x member
        rw [HERuns.ground_typeVars answerable] at member
        simp at member
      exact .inr ⟨value_tree (Value.node head each), noVars,
        Unifying.applySubst_ground σ _ answerable.ground⟩

/-! ## Both machines -/

section Joint

variable {lookup : CastLookup} {policy : Policy}

/-- **Both machines evaluate every settling term to the same answer list**, PeTTa on every flat or
value presentation. -/
theorem settlesN_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : NestedProgram dispatch atoms) {t : Atom} (settles : SettlesN dispatch atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ HEEvaluates dispatch lookup policy atoms t L ∧
      PeTTaOpenN dispatch atoms t L := by
  induction settles with
  | @data d data _ =>
      refine ⟨[d], fun a member => ?_, HERuns.he_data answers atoms data,
        petta_openN_data atoms data⟩
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        HERuns.he_absent answers (scoped_consFree program.scoped) ordinary
          (regionBodies_nil_of_no_equation args noEquation),
        petta_openN_constructor ordinary noEquation⟩
      rw [List.mem_singleton] at member
      subst member
      exact call_answerable ordinary.head ordinary.arguments
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionInstances atoms f args, ∃ L, SettlesN dispatch atoms b ∧
          (∀ a ∈ L, Answerable a) ∧ HEEvaluates dispatch lookup policy atoms b L ∧
          PeTTaOpenN dispatch atoms b L := by
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
          (related.imp fun _ _ both => ⟨both.2.2.1, settlesN_facts both.1, both.2.1⟩),
        petta_openN_call program ordinary defined (related.imp fun _ _ both => both.2.2.2)⟩
      intro a member
      obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
      obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
      exact both.2.1 a inner
  | @value g vs head each =>
      have joint := value_joint (policy := policy) answers (scoped_consFree program.scoped)
        (Value.node head each)
      exact ⟨[.expression (.symbol g :: vs)], joint.1, joint.2.1, petta_openN_value head⟩

/-- **The answers agree with value bodies**: HE's complete run from its entry configuration and,
from some fuel on, PeTTa's streaming run give the same atoms, in order. -/
theorem answersN_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : NestedProgram dispatch atoms) {c : Atom} (settles : SettlesN dispatch atoms c) :
    ∃ (heAnswers : List Result) (N : Nat),
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
        ∀ n, N ≤ n →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = heAnswers.map (fun r => r.1.erase) := by
  obtain ⟨L, clean, he, petta⟩ := settlesN_agree (policy := policy) answers program settles
  obtain ⟨R, eraseR, path, observed⟩ := he_complete he
  obtain ⟨N, stable⟩ := petta_complete (settlesN_facts settles).ground clean
    (fun frames K deliver world σ state privateCode range fresh older answers next =>
      petta frames K deliver world σ state privateCode range fresh c (presentsN_self settles σ)
        older answers next)
  exact ⟨R, N, path, observed, fun n bigger => by rw [stable n bigger, eraseR]⟩

end Joint

/-! ## Every complete run -/

/-- **HE's source semantics determines the atoms of every settling term** (historical lookup). -/
theorem settlesN_determined {policy : Policy} {atoms : List Atom}
    (program : NestedProgram dispatch atoms) {t : Atom} (settles : SettlesN dispatch atoms t) :
    ∃ L : List Atom, (∀ a ∈ L, Answerable a) ∧ Determined dispatch policy atoms t L := by
  induction settles with
  | @data d data notRefused =>
      have settled := data_settled (dispatch := dispatch) (policy := policy) (atoms := atoms) data
      exact ⟨[d], settled.1, settled.2⟩
  | @constructor f args ordinary noEquation =>
      refine ⟨[.expression (.symbol f :: args)], fun a member => ?_,
        empty_region_determined raw_contract (scoped_consFree program.scoped) ordinary
          (regionBodies_nil_of_no_equation args noEquation)⟩
      rw [List.mem_singleton] at member
      subst member
      exact call_answerable ordinary.head ordinary.arguments
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionInstances atoms f args, ∃ L : List Atom,
          SettlesN dispatch atoms b ∧ (∀ a ∈ L, Answerable a) ∧ Determined dispatch policy atoms b L := by
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
        call_source raw_contract ordinary derived
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
            DeterminedUnder dispatch Completed.rawLookup policy atoms i L ∧ BodyFacts i) works Ls :=
          (forall₂_comp instances related).imp fun _ _ both => by
            obtain ⟨i, ⟨_, reads⟩, settlesI, _, determined⟩ := both
            exact ⟨i, reads, determined, settlesN_facts settlesI⟩
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
  | @value g vs head each =>
      exact ⟨_, value_settled (policy := policy) (scoped_consFree program.scoped)
        (Value.node head each)⟩

/-- **Every complete run of HE publishes PeTTa's answers, with value bodies** (historical lookup): a
complete run exists, and every complete run publishes the bag PeTTa yields from some fuel on. -/
theorem every_complete_run_n (policy : Policy) {atoms : List Atom}
    (program : NestedProgram dispatch atoms) {c : Atom} (settles : SettlesN dispatch atoms c) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      ∃ N : Nat, ∀ n, N ≤ n → ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) c Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = emitted.map (fun r => r.1.erase) := by
  obtain ⟨L, _, determined⟩ := settlesN_determined (policy := policy) program settles
  obtain ⟨heAnswers, N, path, _, agree⟩ := answersN_agree (policy := policy) raw_answers program
    settles
  refine ⟨⟨heAnswers, path⟩, N, fun n bigger emitted run => ?_⟩
  rw [agree n bigger, determined _ _ _ _ (complete_source path),
    determined _ _ _ _ (complete_source run)]

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule rule_consFree)
open BoundVariables.Controls (sym_data a_data)
open WholeRunWords.Double (noHost)

/-- `nest` and `dup` use their variable inside the values they build. -/
def nestRows : List Atom :=
  [rule (app "nest" [.var "x"]) (app "pair" [app "pair" [.var "x", .var "x"], .var "x"]),
   rule (app "dup" [.var "x"]) (app "Cons" [.var "x", app "Cons" [.var "x", sym "Nil"]])]

theorem pair_head : ConstructorHead noHost nestRows "pair" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide, by decide +kernel⟩

theorem cons_head : ConstructorHead noHost nestRows "Cons" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide, by decide +kernel⟩

theorem x_consFree : ∀ a ∈ [Atom.var "x"], RegionsWithVariables.ConsFree a := by
  intro a member
  simp only [List.mem_singleton] at member
  subst member
  exact .var _

theorem nest_program : NestedProgram noHost nestRows := by
  intro row member
  simp only [nestRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨rule_consFree x_consFree, fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .inr (.node pair_head fun u member => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .node pair_head fun w inner => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inner
        rcases inner with rfl | rfl <;> exact .item (.var _)
    · exact .item (.var _)
  · refine ⟨rule_consFree x_consFree, fun lhs rhs same => ?_⟩
    cases same
    refine ⟨by decide, .inr (.node cons_head fun u member => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .item (.var _)
    · exact .node cons_head fun w inner => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inner
        rcases inner with rfl | rfl
        · exact .item (.var _)
        · exact .item (.symbol _)

theorem a_value : Value noHost nestRows (sym "a") := .data (sym_data "a" (by decide) (by decide))

/-- **`(nest a)` settles**: its one instance is the value `(pair (pair a a) a)`. -/
theorem nest_settles : SettlesN noHost nestRows (app "nest" [sym "a"]) := by
  have instances : regionInstances nestRows "nest" [sym "a"] =
      [app "pair" [app "pair" [sym "a", sym "a"], sym "a"]] := by decide +kernel
  refine .call ⟨sym_data "nest" (by decide) (by decide), a_data, by decide +kernel,
    fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
    by decide, by decide⟩ (by rw [instances]; simp) ?_
  rw [instances]
  intro b member
  simp only [List.mem_singleton] at member
  subst member
  exact .value pair_head fun v member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .node pair_head fun w inner => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inner
        rcases inner with rfl | rfl <;> exact a_value
    · exact a_value

/-- **`(dup a)` settles**: its one instance is the value `(Cons a (Cons a Nil))`. -/
theorem dup_settles : SettlesN noHost nestRows (app "dup" [sym "a"]) := by
  have instances : regionInstances nestRows "dup" [sym "a"] =
      [app "Cons" [sym "a", app "Cons" [sym "a", sym "Nil"]]] := by decide +kernel
  refine .call ⟨sym_data "dup" (by decide) (by decide), a_data, by decide +kernel,
    fun impossible => impossible, by decide +kernel, by decide, by decide, by decide +kernel,
    by decide, by decide⟩ (by rw [instances]; simp) ?_
  rw [instances]
  intro b member
  simp only [List.mem_singleton] at member
  subst member
  exact .value cons_head fun v member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact a_value
    · exact .node cons_head fun w inner => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inner
        rcases inner with rfl | rfl
        · exact a_value
        · exact .data (sym_data "Nil" (by decide) (by decide))

/-- **Positive control: a variable used under a nested constructor.** `(nest a)` on
`{(= (nest $x) (pair (pair $x $x) $x)), …}`: a complete HE run exists, every complete HE run
publishes `(pair (pair a a) a)`, and PeTTa's run gives it. -/
theorem nest_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList nestRows) (app "nest" [sym "a"]) Atom.undefinedType)
        ⟨Space.ofList nestRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList nestRows) (app "nest" [sym "a"]) Atom.undefinedType)
          ⟨Space.ofList nestRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "pair" [app "pair" [sym "a", sym "a"], sym "a"]]) ∧
      Streaming.values (Streaming.advance (translate nestRows) 80
        (Streaming.enter { state := store nestRows } (app "nest" [sym "a"]))) =
        [app "pair" [app "pair" [sym "a", sym "a"], sym "a"]] := by
  have computed : Streaming.values (Streaming.advance (translate nestRows) 80
      (Streaming.enter { state := store nestRows } (app "nest" [sym "a"]))) =
      [app "pair" [app "pair" [sym "a", sym "a"], sym "a"]] := by decide +kernel
  have finished : (Streaming.advance (translate nestRows) 80
      (Streaming.enter { state := store nestRows } (app "nest" [sym "a"]))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨⟨heAnswers, path⟩, N, every⟩ := every_complete_run_n policy nest_program nest_settles
  refine ⟨⟨⟨heAnswers, path⟩, fun emitted run => ?_⟩, computed⟩
  have later := every (max N 80) (le_max_left _ _) emitted run
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

/-- **Positive control: a list built from the variable.** `(dup a)` gives `(Cons a (Cons a Nil))` on
every complete HE run and in PeTTa. -/
theorem dup_every_run (policy : Policy) :
    ((∃ heAnswers : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
        (load (Space.ofList nestRows) (app "dup" [sym "a"]) Atom.undefinedType)
        ⟨Space.ofList nestRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList nestRows) (app "dup" [sym "a"]) Atom.undefinedType)
          ⟨Space.ofList nestRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "Cons" [sym "a", app "Cons" [sym "a", sym "Nil"]]]) ∧
      Streaming.values (Streaming.advance (translate nestRows) 80
        (Streaming.enter { state := store nestRows } (app "dup" [sym "a"]))) =
        [app "Cons" [sym "a", app "Cons" [sym "a", sym "Nil"]]] := by
  have computed : Streaming.values (Streaming.advance (translate nestRows) 80
      (Streaming.enter { state := store nestRows } (app "dup" [sym "a"]))) =
      [app "Cons" [sym "a", app "Cons" [sym "a", sym "Nil"]]] := by decide +kernel
  have finished : (Streaming.advance (translate nestRows) 80
      (Streaming.enter { state := store nestRows } (app "dup" [sym "a"]))).agenda.length = 0 := by
    decide +kernel
  obtain ⟨⟨heAnswers, path⟩, N, every⟩ := every_complete_run_n policy nest_program dup_settles
  refine ⟨⟨⟨heAnswers, path⟩, fun emitted run => ?_⟩, computed⟩
  have later := every (max N 80) (le_max_left _ _) emitted run
  rw [advance_stable (List.eq_nil_of_length_eq_zero finished) _ (le_max_right _ _), computed] at later
  exact later.symm

/-- **Negative control: the extension is strict.** `(nest a)` does not settle in `BoundVariables`'s
sense: its instance has a call as an argument. -/
theorem nest_not_settlesV : ¬ SettlesV noHost nestRows (app "nest" [sym "a"]) := by
  have instances : regionInstances nestRows "nest" [sym "a"] =
      [app "pair" [app "pair" [sym "a", sym "a"], sym "a"]] := by decide +kernel
  have defined : (nestRows.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != "nest") = false := by decide +kernel
  intro settles
  cases settles with
  | data data _ => cases data
  | constructor _ noEquation =>
      rw [defined] at noEquation
      cases noEquation
  | call _ _ settled =>
      have body := settled (app "pair" [app "pair" [sym "a", sym "a"], sym "a"])
        (by rw [instances]; simp)
      cases body with
      | data data _ => cases data
      | constructor ordinary _ =>
          cases ordinary.arguments (app "pair" [sym "a", sym "a"]) (by simp)
      | call ordinary _ _ =>
          cases ordinary.arguments (app "pair" [sym "a", sym "a"]) (by simp)

end Controls

#print axioms value_joint
#print axioms value_settled
#print axioms value_run
#print axioms tree_renamed
#print axioms run_clauses_N
#print axioms petta_openN_call
#print axioms settlesN_agree
#print axioms answersN_agree
#print axioms settlesN_determined
#print axioms every_complete_run_n
#print axioms Controls.nest_every_run
#print axioms Controls.dup_every_run
#print axioms Controls.nest_not_settlesV

end NestedValues

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
