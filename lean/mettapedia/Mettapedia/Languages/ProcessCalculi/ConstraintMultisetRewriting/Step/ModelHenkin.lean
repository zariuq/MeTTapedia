import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelPresheaf

/-!
# Henkin models of the frames: the complete class, closed points, and the step's transitions

**A Henkin model** (`Frames.HenkinModel`) of a category of frames gives each frame a type of points
(environments), pulls points back along morphisms, and evaluates terms at points into one type of
values, naturally (`eval_act`) and respecting the frame equivalence (`eval_E`). The points form a
presheaf on the frames, functorial at the level of evaluation. A point satisfies an equation when
both sides evaluate alike (`HenkinModel.kernel`), and a guard formula is read through that relation.

* **Points.** A point of a frame is an environment of the model at that frame: an element of
  `Pt a`. It is not a point of a topos; no correspondence between these models and points of a
  classifying topos is claimed here, and one would need its own classifying theorem.
* **Free models**: every point is realized by a syntactic solution, i.e. has the kernel of one
  (`HenkinModel.Free`). **Soundness** (`HenkinModel.sound`): in a free model, the ask of a guard
  holds at every point satisfying the store.
* **The generic model** (`Frames.generic`): points are all solutions `⟨b, f⟩`, values are terms of
  the solution's frame up to the equivalence. It is free (`generic_free`), and **completeness**
  (`complete`) is Yoneda at it: reading the ask in the generic model is the ask.
  `entails_iff_free`: the free Henkin models are a sound and complete class for the semantic asks
  `Entails`. A proof logic with this model class is in `ModelDerivation`.
  `solvable_iff_generic`: a store is solvable exactly when it has a generic point.
* **Every model realizes solvable stores** (`exists_point_of_solvable`): a solvable store has a point
  in every model with points at every frame. Positive guards transfer to pulled-back points
  (`satisfies_pull_of_positive`). Absence and count do not, in a model that identifies more than the
  syntax (controls in `ModelControls`).
* **Stage models** (`Frames.stage`): the points are the solutions into one frame. At a designated
  closed frame they are the closed points: closed asks are validity in the stage
  (`closedEvery_iff_stage`, `closedSome_iff_stage`).
* **The step**: semantic refinement gives a transition in every free model
  (`Step.model_transition_free`). Literal information transport and literal result knowledge give
  the stronger all-model result (`Step.model_transition`). A point after the firing, satisfying
  its knowledge, pulls back to a point of the firing's information and of the source knowledge.
  The free-model hypothesis is necessary in general; `ModelRefinementControls` separates it even
  for an exact step. In a free model the pulled-back point also satisfies the
  firing's guards when they are written in the guard syntax (`model_transition_guards`). With points
  at every frame, every admitted firing has a point of its information (`realized`), with its guards
  in a free model (`realized_guards`).
* **Runs map functorially** (`Step.pullRun`): a run pulls a point at its end back to its start,
  through the knowledge of every state (`models_pullRun_free` for free models,
  `models_pullRun` for the literal profile). The pullback evaluates as the run's
  morphism (`eval_pullRun`), and the pullback along a concatenation is the composite of the
  pullbacks (`eval_pullRun_append`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uV uP uS uF

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A Henkin model of the frames**: a presheaf of points with a natural evaluation of terms that
respects the frame equivalence. -/
structure HenkinModel (X : Frames Tm Hom) (Val : Type uV) (Pt : Obj → Type uP) where
  eval : {a : Obj} → Tm a → Pt a → Val
  pull : {a b : Obj} → Hom a b → Pt b → Pt a
  eval_act : ∀ {a b : Obj} (f : Hom a b) (t : Tm a) (q : Pt b), eval (X.act f t) q = eval t (pull f q)
  eval_E : ∀ {a : Obj} {s t : Tm a}, X.E s t → ∀ q : Pt a, eval s q = eval t q

namespace HenkinModel

variable {X : Frames Tm Hom} {Val : Type uV} {Pt : Obj → Type uP} (M : X.HenkinModel Val Pt) {O : Type uOcc}

/-- The equations a point makes hold. -/
def kernel {a : Obj} (q : Pt a) (s t : Tm a) : Prop := M.eval s q = M.eval t q

/-- A point satisfying a store. -/
def Models {a : Obj} (q : Pt a) (store : EquationStore (Tm a)) : Prop :=
  ∀ e ∈ store, M.kernel q e.1 e.2

/-- A guard read at a point. -/
def Satisfies {a : Obj} (q : Pt a) (φ : GuardFormula (Tm a) O) : Prop := φ.Sat (M.kernel q)

/-- A point realized by a syntactic solution: it has that solution's kernel. -/
def Realizes {a b : Obj} (q : Pt a) (f : Hom a b) : Prop := ∀ s t : Tm a, M.kernel q s t ↔ X.kernel f s t

/-- **A free model**: every point is realized by a syntactic solution. -/
def Free : Prop := ∀ (a : Obj) (q : Pt a), ∃ (b : Obj) (f : Hom a b), M.Realizes q f


variable {M}

theorem kernel_pull {a b : Obj} (f : Hom a b) (q : Pt b) (s t : Tm a) :
    M.kernel (M.pull f q) s t ↔ M.kernel q (X.act f s) (X.act f t) := by
  unfold kernel
  rw [M.eval_act, M.eval_act]

/-- A point satisfies a transported store exactly when its pullback satisfies the store. -/
theorem models_applyStore {a b : Obj} (f : Hom a b) (q : Pt b) (store : EquationStore (Tm a)) :
    M.Models q (X.applyStore f store) ↔ M.Models (M.pull f q) store := by
  unfold Models applyStore
  rw [List.forall_mem_map]
  exact forall₂_congr fun e _ => (kernel_pull f q e.1 e.2).symm

/-- **A solution pulls every point back to a point of the store.** -/
theorem models_pull {a b : Obj} {f : Hom a b} {store : EquationStore (Tm a)}
    (solved : X.Models f store) (r : Pt b) : M.Models (M.pull f r) store :=
  fun e member => (kernel_pull f r e.1 e.2).mpr (M.eval_E (solved e member) r)

/-- **Positive guards transfer to pulled-back points.** -/
theorem satisfies_pull_of_positive {a b : Obj} {f : Hom a b} {φ : GuardFormula (Tm a) O}
    (positive : φ.Positive) (held : X.Satisfies f φ) (r : Pt b) : M.Satisfies (M.pull f r) φ :=
  positive.mono (fun s t h => (kernel_pull f r s t).mpr (M.eval_E h r)) held

/-- **Every model realizes solvable stores**: a solvable store has a point in every model with points
at every frame. -/
theorem exists_point_of_solvable (inhabited : ∀ a : Obj, Nonempty (Pt a)) {a : Obj} {store : EquationStore (Tm a)}
    (solvable : X.Solvable store) : ∃ q : Pt a, M.Models q store := by
  obtain ⟨b, f, solved⟩ := solvable
  obtain ⟨r⟩ := inhabited b
  exact ⟨M.pull f r, models_pull solved r⟩

theorem models_iff_of_realizes {a b : Obj} {q : Pt a} {f : Hom a b} (realized : M.Realizes q f)
    (store : EquationStore (Tm a)) : M.Models q store ↔ X.Models f store :=
  forall₂_congr fun e _ => realized e.1 e.2

theorem satisfies_iff_of_realizes {a b : Obj} {q : Pt a} {f : Hom a b} (realized : M.Realizes q f)
    (φ : GuardFormula (Tm a) O) : M.Satisfies q φ ↔ X.Satisfies f φ :=
  GuardFormula.sat_congr realized φ

/-- **Soundness**: in a free model, the ask of a guard holds at every point satisfying the store. -/
theorem sound (free : M.Free) {a : Obj} {store : EquationStore (Tm a)} {φ : GuardFormula (Tm a) O}
    (asked : X.Entails store fun _ f => X.Satisfies f φ) (q : Pt a) (known : M.Models q store) :
    M.Satisfies q φ := by
  obtain ⟨b, f, realized⟩ := free a q
  exact (satisfies_iff_of_realizes realized φ).mpr (asked b f ((models_iff_of_realizes realized store).mp known))

end HenkinModel

/-! ## The generic model and completeness -/

variable (X : Frames Tm Hom)

/-- The terms of a frame up to the frame equivalence. -/
def termSetoid (b : Obj) : Setoid (Tm b) := ⟨X.E, X.equivalence b⟩

/-- **The generic model**: points are all solutions, values are terms of the solution's frame up to
the equivalence. -/
def generic : X.HenkinModel (Σ b : Obj, Quotient (X.termSetoid b)) (fun a => Σ b : Obj, Hom a b) where
  eval t q := ⟨q.1, Quotient.mk (X.termSetoid q.1) (X.act q.2 t)⟩
  pull f q := ⟨q.1, X.comp q.2 f⟩
  eval_act f t q := by
    show (⟨q.1, Quotient.mk (X.termSetoid q.1) (X.act q.2 (X.act f t))⟩ : Σ b : Obj, Quotient (X.termSetoid b)) =
      ⟨q.1, Quotient.mk (X.termSetoid q.1) (X.act (X.comp q.2 f) t)⟩
    rw [X.act_comp]
  eval_E same q := congrArg (Sigma.mk q.1) (Quotient.sound (X.preserves q.2 same))

/-- **The stage model at a frame**: points are the solutions into it. -/
def stage (c : Obj) : X.HenkinModel (Quotient (X.termSetoid c)) (fun a => Hom a c) where
  eval t f := Quotient.mk (X.termSetoid c) (X.act f t)
  pull f g := X.comp g f
  eval_act f t g := by
    show Quotient.mk (X.termSetoid c) (X.act g (X.act f t)) = Quotient.mk (X.termSetoid c) (X.act (X.comp g f) t)
    rw [X.act_comp]
  eval_E same g := Quotient.sound (X.preserves g same)

variable {X}

theorem generic_kernel {a b : Obj} (f : Hom a b) (s t : Tm a) :
    (generic X).kernel (⟨b, f⟩ : Σ b : Obj, Hom a b) s t ↔ X.kernel f s t := by
  show (⟨b, Quotient.mk (X.termSetoid b) (X.act f s)⟩ : Σ b : Obj, Quotient (X.termSetoid b)) =
      ⟨b, Quotient.mk (X.termSetoid b) (X.act f t)⟩ ↔ X.E (X.act f s) (X.act f t)
  constructor
  · intro same
    exact Quotient.exact (eq_of_heq (Sigma.mk.inj same).2)
  · intro same
    exact congrArg (Sigma.mk b) (Quotient.sound same)

/-- **The generic model is free.** -/
theorem generic_free : (generic X).Free := fun _ q => ⟨q.1, q.2, generic_kernel q.2⟩

theorem generic_models_iff {a b : Obj} (f : Hom a b) (store : EquationStore (Tm a)) :
    (generic X).Models (⟨b, f⟩ : Σ b : Obj, Hom a b) store ↔ X.Models f store :=
  HenkinModel.models_iff_of_realizes (generic_kernel f) store

theorem generic_satisfies_iff {O : Type uOcc} {a b : Obj} (f : Hom a b) (φ : GuardFormula (Tm a) O) :
    (generic X).Satisfies (⟨b, f⟩ : Σ b : Obj, Hom a b) φ ↔ X.Satisfies f φ :=
  HenkinModel.satisfies_iff_of_realizes (generic_kernel f) φ

/-- **Completeness, by Yoneda**: an ask valid in the generic model is entailed. -/
theorem complete {O : Type uOcc} {a : Obj} {store : EquationStore (Tm a)} {φ : GuardFormula (Tm a) O}
    (valid : ∀ q : (Σ b : Obj, Hom a b), (generic X).Models q store → (generic X).Satisfies q φ) :
    X.Entails store fun _ f => X.Satisfies f φ :=
  fun b f solved => (generic_satisfies_iff f φ).mp (valid ⟨b, f⟩ ((generic_models_iff f store).mpr solved))

/-- **The free Henkin models are a sound and complete class for asks.** -/
theorem entails_iff_free {O : Type uOcc} {a : Obj} (store : EquationStore (Tm a)) (φ : GuardFormula (Tm a) O) :
    X.Entails store (fun _ f => X.Satisfies f φ) ↔
      ∀ (V : Type (max uO uT)) (Q : Obj → Type (max uO uH)) (M : X.HenkinModel V Q), M.Free →
        ∀ q : Q a, M.Models q store → M.Satisfies q φ :=
  ⟨fun asked _ _ _ free q known => HenkinModel.sound free asked q known,
    fun valid => complete (valid _ _ (generic X) generic_free)⟩

/-- **Consistency is a generic point.** -/
theorem solvable_iff_generic {a : Obj} (store : EquationStore (Tm a)) :
    X.Solvable store ↔ ∃ q : (Σ b : Obj, Hom a b), (generic X).Models q store :=
  ⟨fun ⟨b, f, solved⟩ => ⟨⟨b, f⟩, (generic_models_iff f store).mpr solved⟩,
    fun ⟨q, known⟩ => ⟨q.1, q.2, (generic_models_iff q.2 store).mp known⟩⟩

theorem stage_kernel {a c : Obj} (f : Hom a c) (s t : Tm a) :
    (stage X c).kernel f s t ↔ X.kernel f s t := by
  show Quotient.mk (X.termSetoid c) (X.act f s) = Quotient.mk (X.termSetoid c) (X.act f t) ↔
    X.E (X.act f s) (X.act f t)
  exact ⟨Quotient.exact, fun same => Quotient.sound same⟩

/-- **A stage model is free.** -/
theorem stage_free (c : Obj) : (stage X c).Free := fun _ f => ⟨c, f, stage_kernel f⟩

/-- **Closed asks at every closed solution are validity in the closed stage.** -/
theorem closedEvery_iff_stage {O : Type uOcc} (point : Obj) {a : Obj} (store : EquationStore (Tm a))
    (φ : GuardFormula (Tm a) O) :
    X.Asks point store (.closedEvery φ) ↔
      ∀ q : Hom a point, (stage X point).Models q store → (stage X point).Satisfies q φ :=
  forall_congr' fun f => imp_congr (HenkinModel.models_iff_of_realizes (stage_kernel f) store).symm
    (HenkinModel.satisfies_iff_of_realizes (stage_kernel f) φ).symm

/-- **Closed asks at some closed solution are a point of the closed stage.** -/
theorem closedSome_iff_stage {O : Type uOcc} (point : Obj) {a : Obj} (store : EquationStore (Tm a))
    (φ : GuardFormula (Tm a) O) :
    X.Asks point store (.closedSome φ) ↔
      ∃ q : Hom a point, (stage X point).Models q store ∧ (stage X point).Satisfies q φ :=
  exists_congr fun f => and_congr (HenkinModel.models_iff_of_realizes (stage_kernel f) store).symm
    (HenkinModel.satisfies_iff_of_realizes (stage_kernel f) φ).symm

end Frames

/-! ## The step in a Henkin model -/

namespace Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing) {Val : Type uV} {Pt : Obj → Type uP} (M : X.HenkinModel Val Pt)

/-- **An admitted firing gives a model transition**: a point after it pulls back to a point of its
information and to a point of the knowledge before it. -/
theorem model_transition [P.LiteralInformation] [P.LiteralKnowledge]
    {s : State} {f : Firing s} (admitted : P.Admits f)
    (q : Pt (P.frame (P.result f admitted))) (known : M.Models q (P.knowledge (P.result f admitted))) :
    M.Models (M.pull (P.settle f admitted) q) (P.information f) ∧
      M.Models (M.pull (P.along f admitted) q) (P.knowledge s) := by
  have information : M.Models (M.pull (P.settle f admitted) q) (P.information f) := by
    rw [← Frames.HenkinModel.models_applyStore, ← P.knowledge_result f admitted]
    exact known
  refine ⟨information, fun e member => ?_⟩
  have along : ∀ t, M.eval t (M.pull (P.along f admitted) q) =
      M.eval (X.act (P.extension f) t) (M.pull (P.settle f admitted) q) := fun t => by
    rw [← M.eval_act, ← M.eval_act]
    exact congrArg (fun u => M.eval u q) (X.act_comp (P.settle f admitted) (P.extension f) t)
  show M.eval e.1 (M.pull (P.along f admitted) q) = M.eval e.2 (M.pull (P.along f admitted) q)
  rw [along, along]
  exact information _ (P.transported f e member)

/-- Semantic refinement transfers to a free Henkin model without literal
store transport or exactness. Freeness realizes the observed point by a frame
morphism; arbitrary Henkin interpretations need a separate transfer contract. -/
theorem model_transition_free (free : M.Free)
    {s : State} {f : Firing s} (admitted : P.Admits f)
    (q : Pt (P.frame (P.result f admitted))) (known : M.Models q (P.knowledge (P.result f admitted))) :
    M.Models (M.pull (P.settle f admitted) q) (P.information f) ∧
      M.Models (M.pull (P.along f admitted) q) (P.knowledge s) := by
  obtain ⟨b, σ, realizes⟩ := free _ q
  have solved := (M.models_iff_of_realizes realizes _).mp known
  constructor
  · apply (M.models_applyStore (P.settle f admitted) q _).mp
    apply (M.models_iff_of_realizes realizes _).mpr
    exact (Frames.models_applyStore _ _ _).mpr
      (P.result_refines f (P.prepares admitted) σ solved)
  · apply (M.models_applyStore (P.along f admitted) q _).mp
    apply (M.models_iff_of_realizes realizes _).mpr
    exact (Frames.models_applyStore _ _ _).mpr (P.models_along admitted σ solved)

/-- **In a free model the transition also satisfies the firing's guards**, when they are written in
the guard syntax. -/
theorem model_transition_guards [P.Guarded] (free : M.Free)
    {guard : ∀ {s : State} (f : Firing s), GuardFormula (Tm (P.target f)) O} (guarded : P.GuardedBy guard)
    {s : State} {f : Firing s} (admitted : P.Admits f) (q : Pt (P.frame (P.result f admitted)))
    (known : M.Models q (P.knowledge (P.result f admitted))) :
    M.Satisfies (M.pull (P.settle f admitted) q) (guard f) := by
  have asked : X.Entails (P.information f) fun _ σ => X.Satisfies σ (guard f) :=
    fun b σ solved => (guarded f b σ).mp (((P.admits_iff f).mp admitted).2.2.2 b σ solved)
  exact Frames.HenkinModel.sound free asked _ (P.model_transition_free M free admitted q known).1

/-- **Every admitted firing is realized** in a model with points at every frame. -/
theorem realized (inhabited : ∀ a : Obj, Nonempty (Pt a)) {s : State} {f : Firing s} (admitted : P.Admits f) :
    ∃ q : Pt (P.target f), M.Models q (P.information f) :=
  Frames.HenkinModel.exists_point_of_solvable inhabited (P.solvable_information admitted)

/-- **In a free model with points at every frame, every admitted firing is realized with its
guards.** -/
theorem realized_guards [P.Guarded] (inhabited : ∀ a : Obj, Nonempty (Pt a)) (free : M.Free)
    {guard : ∀ {s : State} (f : Firing s), GuardFormula (Tm (P.target f)) O} (guarded : P.GuardedBy guard)
    {s : State} {f : Firing s} (admitted : P.Admits f) :
    ∃ q : Pt (P.target f), M.Models q (P.information f) ∧ M.Satisfies q (guard f) := by
  obtain ⟨q, known⟩ := P.realized M inhabited admitted
  have asked : X.Entails (P.information f) fun _ σ => X.Satisfies σ (guard f) :=
    fun b σ solved => (guarded f b σ).mp (((P.admits_iff f).mp admitted).2.2.2 b σ solved)
  exact ⟨q, known, Frames.HenkinModel.sound free asked q known⟩

/-- **A run pulls a point at its end back to its start.** -/
def pullRun : {s : State} → (r : P.Run s) → Pt (P.frame r.last) → Pt (P.frame s)
  | _, .nil _, q => q
  | _, .cons f admitted rest, q => M.pull (P.along f admitted) (pullRun rest q)

/-- **The pullback along a run evaluates as the run's morphism.** -/
theorem eval_pullRun : ∀ {s : State} (r : P.Run s) (q : Pt (P.frame r.last)) (t : Tm (P.frame s)),
    M.eval t (P.pullRun M r q) = M.eval (X.act r.toLast t) q
  | _, .nil _, q, t => by
      show M.eval t q = M.eval (X.act (X.id _) t) q
      rw [X.act_id]
  | _, .cons f admitted rest, q, t => by
      show M.eval t (M.pull (P.along f admitted) (P.pullRun M rest q)) =
        M.eval (X.act (X.comp rest.toLast (P.along f admitted)) t) q
      rw [← M.eval_act, eval_pullRun rest q, X.act_comp]

/-- **A run's pullback passes through the knowledge of its start.** -/
theorem models_pullRun [P.LiteralInformation] [P.LiteralKnowledge] :
    ∀ {s : State} (r : P.Run s) (q : Pt (P.frame r.last)),
    M.Models q (P.knowledge r.last) → M.Models (P.pullRun M r q) (P.knowledge s)
  | _, .nil _, _, known => known
  | _, .cons _ admitted rest, q, known =>
      (P.model_transition M admitted (P.pullRun M rest q) (models_pullRun rest q known)).2

/-- Run preservation for the semantic core in any free Henkin model. -/
theorem models_pullRun_free (free : M.Free) :
    ∀ {s : State} (r : P.Run s) (q : Pt (P.frame r.last)),
    M.Models q (P.knowledge r.last) → M.Models (P.pullRun M r q) (P.knowledge s)
  | _, .nil _, _, known => known
  | _, .cons _ admitted rest, q, known =>
      (P.model_transition_free M free admitted (P.pullRun M rest q)
        (models_pullRun_free free rest q known)).2

/-- **Runs map functorially**: the pullback along a concatenation is the composite of the
pullbacks. -/
theorem eval_pullRun_append : ∀ {s : State} (r : P.Run s) (later : P.Run r.last)
    (q : Pt (P.frame later.last)) (q' : Pt (P.frame (r.append later).last)), HEq q' q →
    ∀ t : Tm (P.frame s), M.eval t (P.pullRun M (r.append later) q') = M.eval t (P.pullRun M r (P.pullRun M later q))
  | _, .nil _, later, q, q', same, t => by
      show M.eval t (P.pullRun M later q') = M.eval t (P.pullRun M later q)
      rw [eq_of_heq same]
  | _, .cons f admitted rest, later, q, q', same, t => by
      show M.eval t (M.pull (P.along f admitted) (P.pullRun M (rest.append later) q')) =
        M.eval t (M.pull (P.along f admitted) (P.pullRun M rest (P.pullRun M later q)))
      rw [← M.eval_act, ← M.eval_act]
      exact eval_pullRun_append rest later q q' same _

end Step

#print axioms Frames.HenkinModel.models_applyStore
#print axioms Frames.HenkinModel.models_pull
#print axioms Frames.HenkinModel.satisfies_pull_of_positive
#print axioms Frames.HenkinModel.exists_point_of_solvable
#print axioms Frames.HenkinModel.sound
#print axioms Frames.generic
#print axioms Frames.generic_free
#print axioms Frames.complete
#print axioms Frames.entails_iff_free
#print axioms Frames.solvable_iff_generic
#print axioms Frames.stage_free
#print axioms Frames.closedEvery_iff_stage
#print axioms Frames.closedSome_iff_stage
#print axioms Step.model_transition
#print axioms Step.model_transition_guards
#print axioms Step.realized
#print axioms Step.realized_guards
#print axioms Step.eval_pullRun
#print axioms Step.models_pullRun
#print axioms Step.eval_pullRun_append

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
