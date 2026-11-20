import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Syntax

/-!
# The reference small-step semantics of the core

**Knowledge.** Each alternative keeps its own store of equations between data. A solution is a
contextual assignment of the names into any later family (`Models`); a store is live when it has one
(`Solvable`); it reads a datum `t` as a closed datum `g` when some solution sends `t` to `g`
(`Reads`). Unification is two-way: an equation `lhs ≐ call` constrains the call's names as well as
the equation's; matching is the special case of a closed call.

**Moves** (`Move`) of one live alternative, over the shared world:
* `apply`: one alternative per equation, each with the copied left-hand side equated to the call;
  copies at a fresh scope, so the equation's names are fresh at every use. An alternative whose store
  is unsolvable is dead (it never moves and never answers). When no equation matches, the call is
  returned as data (`unmatched`): unknown heads stay inert.
* `run` reads text as code by the program's `reflect`, after dereferencing the text by an idempotent
  most general solution of the store (`Principal`); where the store has none, `run` waits, and the
  observation shows it (`Observation`). Two such solutions give texts that are instances of each other
  and that the store entails equal (`Hygiene.principal_texts`). The code's arrows rename names of
  their sites at their binds; a hygienic reading keeps those sites apart from the names of the text it
  reads (`Hygiene.ReadingHygienic`, satisfied by the elaboration's reading). `ret` holds.
* `let_`: the bound computation runs in the enclosing scope; each answer is equated to the pattern
  with the arrow's own names opened at a fresh scope; names of the pattern from outside cross.
* `choice` splits; `fail` drops the alternative.
* `query` makes one alternative per row of the addressed space (multiplicity kept), the row renamed
  apart with its stored equations; the pattern's names are the alternative's own (a relation
  introduces nothing). `add` stores the atom with the alternative's store; `remove` takes one row that
  unifies, or none when none does. A space operation moves only when the store determines its
  address. `new` binds its handle to the supply's value at the handle counter: a space no other `new`
  of the run has made when the supply is injective, and an empty one only if, further, nothing else
  addresses the supply's values (`ExampleNew`).
* `check` asks the discipline at every reading of the answer: admitted when all readings are,
  refused when none is; otherwise the alternative waits (no move).
* `delay` registers a shared cell; `force` runs the pending cell its argument is bound to, once, and
  records its value; a cell no longer pending is read through the store.

**Steps** (`Step`) choose one live alternative of the bag and replace it by the bag its move makes.
The answers of a configuration are the reading sets of its finished live alternatives, as a bag.
Alternatives share the world (the scope counter, the handle counter and the spaces), so two runs of
one query that move the alternatives in different orders can end with different bags when an
alternative writes a space another one reads (`ExampleRace`): what a program answers is the set of
the bags of its quiescent runs (`Outcomes`). A live alternative that cannot move waits; it is not an
answer and not a failure, and `Observation.observe` shows it with its reason.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

/-! ## Knowledge -/

/-- `σ` solves every equation of the store. -/
def Models {X : Type} {target : X → MetaArity S} (σ : Assignment (fam κ) target)
    (store : List (Constraint κ Γ star)) : Prop :=
  ∀ e ∈ store, instantiate σ e.1 = instantiate σ e.2

/-- The store has a solution in some later family. -/
def Solvable (store : List (Constraint κ Γ star)) : Prop :=
  ∃ (X : Type) (target : X → MetaArity S) (σ : Assignment (fam κ) target), Models σ store

/-- Some solution of the store reads `t` as the closed datum `g`. -/
def Reads (store : List (Constraint κ Γ star)) (t : Data κ Γ star) (g : Term S Γ star) : Prop :=
  ∃ (X : Type) (target : X → MetaArity S) (σ : Assignment (fam κ) target),
    Models σ store ∧ instantiate σ t = Rigid.includeTerm target g

/-- The store is live and every solution reads `t` as `g`. -/
def Determines (store : List (Constraint κ Γ star)) (t : Data κ Γ star) (g : Term S Γ star) : Prop :=
  Solvable store ∧ ∀ {X : Type} (target : X → MetaArity S) (σ : Assignment (fam κ) target),
    Models σ store → instantiate σ t = Rigid.includeTerm target g

/-- Every solution of the store equates `a` and `b`. -/
def EntailsEq (store : List (Constraint κ Γ star)) (a b : Data κ Γ star) : Prop :=
  ∀ {X : Type} (target : X → MetaArity S) (σ : Assignment (fam κ) target),
    Models σ store → instantiate σ a = instantiate σ b

/-- **An idempotent most general solution within the names**: `θ` solves the store, and every
solution is unchanged by first applying `θ`. Text is run as its instance under such a solution
(dereferencing), so that the reading of text as code sees what the store has bound. -/
def Principal (store : List (Constraint κ Γ star)) (θ : Assignment (fam κ) (fam κ)) : Prop :=
  Models θ store ∧ ∀ {X : Type} (target : X → MetaArity S) (σ : Assignment (fam κ) target),
    Models σ store → ∀ name, instantiate σ (θ name) = σ name

/-- A store copied at scope `n`. -/
def copyStore (n : ℕ) (store : List (Constraint κ Γ star)) : List (Constraint κ Γ star) :=
  store.map fun e => (instantiate (copyAt κ n) e.1, instantiate (copyAt κ n) e.2)

theorem models_append {X : Type} {target : X → MetaArity S} (σ : Assignment (fam κ) target)
    (one two : List (Constraint κ Γ star)) :
    Models σ (one ++ two) ↔ Models σ one ∧ Models σ two := by
  simp only [Models, List.mem_append]
  constructor
  · intro all
    exact ⟨fun e member => all e (Or.inl member), fun e member => all e (Or.inr member)⟩
  · rintro ⟨first, second⟩ e (member | member)
    · exact first e member
    · exact second e member

theorem models_singleton {X : Type} {target : X → MetaArity S} (σ : Assignment (fam κ) target)
    (e : Constraint κ Γ star) : Models σ [e] ↔ instantiate σ e.1 = instantiate σ e.2 := by
  simp [Models]

theorem solvable_of_append {one two : List (Constraint κ Γ star)} (live : Solvable (one ++ two)) :
    Solvable one := by
  obtain ⟨X, target, σ, solved⟩ := live
  exact ⟨X, target, σ, ((models_append σ one two).mp solved).1⟩

/-- Readings through a longer store are readings through the shorter one. -/
theorem reads_of_append {one two : List (Constraint κ Γ star)} {t : Data κ Γ star} {g : Term S Γ star}
    (reads : Reads (one ++ two) t g) : Reads one t g := by
  obtain ⟨X, target, σ, solved, read⟩ := reads
  exact ⟨X, target, σ, ((models_append σ one two).mp solved).1, read⟩

/-- A determined datum reads only as what determines it. -/
theorem Determines.reads_iff {store : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {g : Term S Γ star} (determined : Determines store t g) (g' : Term S Γ star) :
    Reads store t g' ↔ g' = g := by
  constructor
  · rintro ⟨X, target, σ, solved, read⟩
    exact Rigid.include_injective target g' g (read.symm.trans (determined.2 target σ solved))
  · rintro rfl
    obtain ⟨X, target, σ, solved⟩ := determined.1
    exact ⟨X, target, σ, solved, determined.2 target σ solved⟩

/-! ## The world -/

open Classical in
/-- Replace the bag of the space `h`. -/
noncomputable def setSpace (spaces : Term S Γ star → Multiset (Row κ Γ star)) (h : Term S Γ star)
    (bag : Multiset (Row κ Γ star)) : Term S Γ star → Multiset (Row κ Γ star) :=
  fun h' => if h' = h then bag else spaces h'

theorem setSpace_same (spaces : Term S Γ star → Multiset (Row κ Γ star)) (h : Term S Γ star)
    (bag : Multiset (Row κ Γ star)) : setSpace spaces h bag h = bag := by
  simp [setSpace]

theorem setSpace_other (spaces : Term S Γ star → Multiset (Row κ Γ star)) {h h' : Term S Γ star}
    (bag : Multiset (Row κ Γ star)) (other : h' ≠ h) : setSpace spaces h bag h' = spaces h' := by
  simp [setSpace, other]

/-- The world after consuming one fresh scope. -/
def World.fresh (w : World κ Γ star) : World κ Γ star := ⟨w.scope + 1, w.handles, w.spaces⟩

/-! ## Moves and steps -/

variable (D : Discipline S Γ star) (P : Program κ Γ star D.Ty) (supply : ℕ → Term S Γ star)

/-- The equation of a stored row used at scope `n` against an atom: the row's own store and the
unification of the atom with the row, both renamed apart. -/
def rowUse (n : ℕ) (r : Row κ Γ star) (atom : Data κ Γ star) : List (Constraint κ Γ star) :=
  copyStore n r.store ++ [(atom, instantiate (copyAt κ n) r.atom)]

/-- The alternative made by one equation for the call `t` at scope `n`. -/
def callBranch (n : ℕ) (K : List (Constraint κ Γ star)) (t : Data κ Γ star)
    (fs : List (Frame κ Γ star D.Ty)) (ps : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (e : Equation κ Γ star D.Ty) : Branch κ Γ star D.Ty :=
  ⟨K ++ [(instantiate (copyAt κ n) e.lhs, t)], .eval (e.rhs.inst (copyAt κ n)), fs, ps⟩

/-- **One move of one alternative**, over the shared world. -/
inductive Move : World κ Γ star → Branch κ Γ star D.Ty → World κ Γ star →
    Multiset (Branch κ Γ star D.Ty) → Prop
  | ret (w : World κ Γ star) (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps) :
      Move w ⟨K, .eval (.ret t), fs, ps⟩ w {⟨K, .value t, fs, ps⟩}
  | apply (w : World κ Γ star) (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps)
      (matched : ∃ e ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])) :
      Move w ⟨K, .eval (.apply t), fs, ps⟩ w.fresh
        ((P.equations.map (callBranch D w.scope K t fs ps) : List (Branch κ Γ star D.Ty)) :
          Multiset (Branch κ Γ star D.Ty))
  | unmatched (w : World κ Γ star) (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps)
      (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])) :
      Move w ⟨K, .eval (.apply t), fs, ps⟩ w {⟨K, .value t, fs, ps⟩}
  | run (w : World κ Γ star) (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps)
      (θ : Assignment (fam κ) (fam κ)) (principal : Principal K θ) :
      Move w ⟨K, .eval (.run t), fs, ps⟩ w {⟨K, .eval (P.reflect (instantiate θ t)), fs, ps⟩}
  | letStart (w : World κ Γ star) (K : List (Constraint κ Γ star)) (s : κ.Site) (p : Data κ Γ star)
      (c k : Comp κ Γ star D.Ty) (fs ps) :
      Move w ⟨K, .eval (.let_ s p c k), fs, ps⟩ w {⟨K, .eval c, .bindTo s p k :: fs, ps⟩}
  | letBind (w : World κ Γ star) (K : List (Constraint κ Γ star)) (v : Data κ Γ star) (s : κ.Site)
      (p : Data κ Γ star) (k : Comp κ Γ star D.Ty) (fs ps) :
      Move w ⟨K, .value v, .bindTo s p k :: fs, ps⟩ w.fresh
        {⟨K ++ [(instantiate (openAt κ s w.scope) p, v)], .eval (k.inst (openAt κ s w.scope)), fs, ps⟩}
  | choice (w : World κ Γ star) (K : List (Constraint κ Γ star)) (c d : Comp κ Γ star D.Ty) (fs ps) :
      Move w ⟨K, .eval (.choice c d), fs, ps⟩ w {⟨K, .eval c, fs, ps⟩, ⟨K, .eval d, fs, ps⟩}
  | fail (w : World κ Γ star) (K : List (Constraint κ Γ star)) (fs ps) :
      Move w ⟨K, .eval .fail, fs, ps⟩ w 0
  | query (w : World κ Γ star) (K : List (Constraint κ Γ star)) (sp p : Data κ Γ star)
      (k : Comp κ Γ star D.Ty) (fs ps) (h : Term S Γ star) (addressed : Determines K sp h) :
      Move w ⟨K, .eval (.query sp p k), fs, ps⟩ w.fresh
        ((w.spaces h).map fun r => ⟨K ++ rowUse w.scope r p, .eval k, fs, ps⟩)
  | add (w : World κ Γ star) (K : List (Constraint κ Γ star)) (sp t : Data κ Γ star)
      (k : Comp κ Γ star D.Ty) (fs ps) (h : Term S Γ star) (addressed : Determines K sp h) :
      Move w ⟨K, .eval (.add sp t k), fs, ps⟩
        ⟨w.scope, w.handles, setSpace w.spaces h (w.spaces h + {⟨t, K⟩})⟩ {⟨K, .eval k, fs, ps⟩}
  | remove (w : World κ Γ star) (K : List (Constraint κ Γ star)) (sp t : Data κ Γ star)
      (k : Comp κ Γ star D.Ty) (fs ps) (h : Term S Γ star) (addressed : Determines K sp h)
      (r : Row κ Γ star) (rest : Multiset (Row κ Γ star)) (split : w.spaces h = r ::ₘ rest)
      (fits : Solvable (K ++ rowUse w.scope r t)) :
      Move w ⟨K, .eval (.remove sp t k), fs, ps⟩ ⟨w.scope + 1, w.handles, setSpace w.spaces h rest⟩
        {⟨K ++ rowUse w.scope r t, .eval k, fs, ps⟩}
  | removeMissing (w : World κ Γ star) (K : List (Constraint κ Γ star)) (sp t : Data κ Γ star)
      (k : Comp κ Γ star D.Ty) (fs ps) (h : Term S Γ star) (addressed : Determines K sp h)
      (none : ∀ r ∈ w.spaces h, ¬ Solvable (K ++ rowUse w.scope r t)) :
      Move w ⟨K, .eval (.remove sp t k), fs, ps⟩ w {⟨K, .eval k, fs, ps⟩}
  | new (w : World κ Γ star) (K : List (Constraint κ Γ star)) (s : κ.Site) (x : Data κ Γ star)
      (k : Comp κ Γ star D.Ty) (fs ps) :
      Move w ⟨K, .eval (.new s x k), fs, ps⟩ ⟨w.scope + 1, w.handles + 1, w.spaces⟩
        {⟨K ++ [(instantiate (openAt κ s w.scope) x, Rigid.includeTerm (fam κ) (supply w.handles))],
          .eval (k.inst (openAt κ s w.scope)), fs, ps⟩}
  | checkStart (w : World κ Γ star) (K : List (Constraint κ Γ star)) (T : D.Ty) (c : Comp κ Γ star D.Ty)
      (fs ps) :
      Move w ⟨K, .eval (.check T c), fs, ps⟩ w {⟨K, .eval c, .checkAt T :: fs, ps⟩}
  | admitted (w : World κ Γ star) (K : List (Constraint κ Γ star)) (v : Data κ Γ star) (T : D.Ty) (fs ps)
      (all : ∀ g, Reads K v g → D.admits T g) :
      Move w ⟨K, .value v, .checkAt T :: fs, ps⟩ w {⟨K, .value v, fs, ps⟩}
  | refused (w : World κ Γ star) (K : List (Constraint κ Γ star)) (v : Data κ Γ star) (T : D.Ty) (fs ps)
      (none : ∀ g, Reads K v g → ¬ D.admits T g) :
      Move w ⟨K, .value v, .checkAt T :: fs, ps⟩ w {⟨K, .refused v T, [], ps⟩}
  | delay (w : World κ Γ star) (K : List (Constraint κ Γ star)) (s : κ.Site) (x : Data κ Γ star)
      (c k : Comp κ Γ star D.Ty) (fs ps) :
      Move w ⟨K, .eval (.delay s x c k), fs, ps⟩ w.fresh
        {⟨K, .eval (k.inst (openAt κ s w.scope)), fs, (instantiate (openAt κ s w.scope) x, c) :: ps⟩}
  | forcePending (w : World κ Γ star) (K : List (Constraint κ Γ star)) (x cell : Data κ Γ star)
      (c : Comp κ Γ star D.Ty) (fs before after) (bound : EntailsEq K x cell) :
      Move w ⟨K, .eval (.force x), fs, before ++ (cell, c) :: after⟩ w
        {⟨K, .eval c, .memo cell :: fs, before ++ after⟩}
  | forceDone (w : World κ Γ star) (K : List (Constraint κ Γ star)) (x : Data κ Γ star) (fs ps)
      (none : ∀ e ∈ ps, ¬ EntailsEq K x e.1) :
      Move w ⟨K, .eval (.force x), fs, ps⟩ w {⟨K, .value x, fs, ps⟩}
  | memo (w : World κ Γ star) (K : List (Constraint κ Γ star)) (v x : Data κ Γ star) (fs ps) :
      Move w ⟨K, .value v, .memo x :: fs, ps⟩ w {⟨K ++ [(x, v)], .value v, fs, ps⟩}

/-- **One step**: a live alternative moves, and the bag it makes replaces it. -/
inductive Step : Config κ Γ star D.Ty → Config κ Γ star D.Ty → Prop
  | move (w w' : World κ Γ star) (b : Branch κ Γ star D.Ty) (rest bs : Multiset (Branch κ Γ star D.Ty))
      (live : Solvable b.store) (moved : Move D P supply w b w' bs) :
      Step ⟨w, b ::ₘ rest⟩ ⟨w', bs + rest⟩

/-- Runs: the reflexive-transitive closure of steps. -/
abbrev Runs := Relation.ReflTransGen (Step D P supply)

variable {D P supply}

/-- A step with the chosen alternative anywhere in the bag. -/
theorem Step.of_eq {w w' : World κ Γ star} {B B' rest bs : Multiset (Branch κ Γ star D.Ty)}
    {b : Branch κ Γ star D.Ty} (hB : B = b ::ₘ rest) (hB' : B' = bs + rest) (live : Solvable b.store)
    (moved : Move D P supply w b w' bs) : Step D P supply ⟨w, B⟩ ⟨w', B'⟩ := by
  subst hB hB'
  exact .move w w' b rest bs live moved

/-- **Steps are local**: alternatives beside the ones that move are carried along. -/
theorem Step.frame {C C' : Config κ Γ star D.Ty} (step : Step D P supply C C')
    (R : Multiset (Branch κ Γ star D.Ty)) :
    Step D P supply ⟨C.world, C.branches + R⟩ ⟨C'.world, C'.branches + R⟩ := by
  cases step with
  | move w w' b rest bs live moved =>
      exact Step.of_eq (by rw [Multiset.cons_add]) (by rw [add_assoc]) live moved

theorem Runs.frame {C C' : Config κ Γ star D.Ty} (runs : Runs D P supply C C')
    (R : Multiset (Branch κ Γ star D.Ty)) :
    Runs D P supply ⟨C.world, C.branches + R⟩ ⟨C'.world, C'.branches + R⟩ := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.frame R)

variable (D P supply)

/-! ## Answers -/

variable {D}

/-- A finished alternative: a value and no frames. -/
def Branch.Finished (b : Branch κ Γ star D.Ty) : Prop := b.frames = [] ∧ ∃ t, b.focus = .value t

/-- The closed data a finished alternative answers: its readings. -/
def Branch.answer (b : Branch κ Γ star D.Ty) : Set (Term S Γ star) :=
  {g | ∃ t, b.focus = .value t ∧ Reads b.store t g}

open Classical in
/-- **The answers of a configuration**: the bag of the reading sets of its finished live
alternatives. A live alternative that waits is not counted; `Observation.observe` shows it. -/
noncomputable def Config.answers (C : Config κ Γ star D.Ty) : Multiset (Set (Term S Γ star)) :=
  (C.branches.filter fun b => b.Finished ∧ Solvable b.store).map Branch.answer

/-- A configuration is quiescent when no live alternative can move. -/
def Config.Quiescent (C : Config κ Γ star D.Ty) : Prop :=
  ∀ b ∈ C.branches, Solvable b.store → ∀ w' bs, ¬ Move D P supply C.world b w' bs

/-! ## Reading runs and answers off one alternative -/

variable {P supply}

/-- A step of the only alternative. -/
theorem Step.single {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (live : Solvable b.store) (moved : Move D P supply w b w' bs) : Step D P supply ⟨w, {b}⟩ ⟨w', bs⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero bs).symm live moved

/-- An alternative with a value and no frames does not move. -/
theorem Move.value_still {w w' : World κ Γ star} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {ps : List (Data κ Γ star × Comp κ Γ star D.Ty)} {bs : Multiset (Branch κ Γ star D.Ty)} :
    ¬ Move D P supply w ⟨K, .value t, [], ps⟩ w' bs := by
  intro moved
  cases moved

/-- A refused alternative does not move. -/
theorem Move.refused_still {w w' : World κ Γ star} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {T : D.Ty} {fs : List (Frame κ Γ star D.Ty)} {ps : List (Data κ Γ star × Comp κ Γ star D.Ty)}
    {bs : Multiset (Branch κ Γ star D.Ty)} : ¬ Move D P supply w ⟨K, .refused t T, fs, ps⟩ w' bs := by
  intro moved
  cases moved

/-- **A configuration whose live alternatives are all finished has ended**: it is quiescent. -/
theorem Config.quiescent_of_finished {C : Config κ Γ star D.Ty}
    (finished : ∀ b ∈ C.branches, Solvable b.store → b.Finished) : C.Quiescent P supply := by
  intro b member live w' bs moved
  obtain ⟨frames, t, focus⟩ := finished b member live
  rcases b with ⟨K, f, fr, ps⟩
  simp only at frames focus
  subst frames focus
  exact Move.value_still moved

/-- A configuration of one finished alternative has ended. -/
theorem Config.quiescent_single {w : World κ Γ star} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {ps : List (Data κ Γ star × Comp κ Γ star D.Ty)} :
    Config.Quiescent P supply (⟨w, {⟨K, .value t, [], ps⟩}⟩ : Config κ Γ star D.Ty) :=
  Config.quiescent_of_finished fun b member _ => by
    rw [Multiset.mem_singleton.mp member]
    exact ⟨rfl, _, rfl⟩

theorem Config.answers_cons_of_finished {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {rest : Multiset (Branch κ Γ star D.Ty)} (finished : b.Finished) (live : Solvable b.store) :
    Config.answers (⟨w, b ::ₘ rest⟩ : Config κ Γ star D.Ty) =
      b.answer ::ₘ Config.answers (⟨w, rest⟩ : Config κ Γ star D.Ty) := by
  classical
  simp only [Config.answers]
  rw [Multiset.filter_cons_of_pos _ ⟨finished, live⟩, Multiset.map_cons]

theorem Config.answers_cons_of_dead {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {rest : Multiset (Branch κ Γ star D.Ty)} (dead : ¬ Solvable b.store) :
    Config.answers (⟨w, b ::ₘ rest⟩ : Config κ Γ star D.Ty) =
      Config.answers (⟨w, rest⟩ : Config κ Γ star D.Ty) := by
  classical
  simp only [Config.answers]
  rw [Multiset.filter_cons_of_neg _ (fun h => dead h.2)]

theorem Config.answers_of_zero {w : World κ Γ star} : Config.answers (⟨w, 0⟩ : Config κ Γ star D.Ty) = 0 := by
  classical
  simp [Config.answers]

theorem Config.answers_of_finished {w : World κ Γ star} {b : Branch κ Γ star D.Ty} (finished : b.Finished)
    (live : Solvable b.store) : Config.answers (⟨w, {b}⟩ : Config κ Γ star D.Ty) = {b.answer} := by
  show Config.answers (⟨w, b ::ₘ 0⟩ : Config κ Γ star D.Ty) = _
  rw [Config.answers_cons_of_finished finished live, Config.answers_of_zero]
  rfl

theorem Config.answers_of_dead {w : World κ Γ star} {b : Branch κ Γ star D.Ty} (dead : ¬ Solvable b.store) :
    Config.answers (⟨w, {b}⟩ : Config κ Γ star D.Ty) = 0 := by
  show Config.answers (⟨w, b ::ₘ 0⟩ : Config κ Γ star D.Ty) = _
  rw [Config.answers_cons_of_dead dead, Config.answers_of_zero]

/-- The answer of a finished alternative whose value is determined. -/
theorem Branch.answer_of_determines {b : Branch κ Γ star D.Ty} {t : Data κ Γ star} {g : Term S Γ star}
    (focus : b.focus = .value t) (determined : Determines b.store t g) : b.answer = {g} := by
  ext g'
  constructor
  · rintro ⟨t', same, reads⟩
    rw [focus, Focus.value.injEq] at same
    subst same
    exact (determined.reads_iff g').mp reads
  · intro member
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨t, focus, (determined.reads_iff _).mpr rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage
