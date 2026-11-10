import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Dispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalStep

/-!
# Dispatch from rational trees to the occurs-checked unifier

**The edge** (`finiteToRational`): finite terms are rational trees, finite substitutions are
substitutions of trees. It reflects the equivalence (`finiteToRational_reflects`).

**The license is exactly acyclicity** (`finiteToRational_licensedAt_iff`). A store is acyclic
(`Acyclic`) when the rational principal answers of its image take finite values; equivalently it is
finitely solvable or rationally refuted (`acyclic_iff`). So:
* **every finite principal answer dispatches**: finitely solvable stores are covered, and the
  finite principal answer stays principal among rational solutions
  (`finiteToRational_coversAt_of_consistent`);
* **finite refutations dispatch exactly on acyclic stores**: `X = f(X)` is refuted by the occurs
  check and solved by `f(f(f(…)))` (`DispatchControls`).

**Matching against ground data is acyclic** (`acyclic_of_groundSided`): when every equation has a
ground side, a rational solution has a finite part that solves the store (`finitize`,
`finitize_applyTerm`). This is a class decided on the source side alone, refutations included
(`finiteToRational_licensedOn_groundSided`).

**The step.** A finite firing whose checks are equalities, read over rational trees
(`liftFiring`, `liftConfig`), is a dispatched firing of the rational-tree step (`dispatched`). On an
acyclic problem its admission is computed by the occurs-checked unifier `unifyTotal`, read as a
decision procedure of the finite-tree frames (`unifyDecider`, `lift_admits_iff`); at a finite
principal answer no acyclicity is needed (`lift_admits_iff_of_principal`); a finite refutation of an
acyclic problem refuses (`lift_refused`).

**The join, both ways** (`lift_admits_iff_admits`, `admits_iff_lift_acyclic`): on acyclic problems the
rational-tree step admits a lifted firing exactly when the finite-tree step admits the firing; so
rational unification followed by the acyclicity check decides the finite-tree step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP
open Interface (Frames)
open Interface.Translation (FrameMap)
open AnnotatedRuns (Firing firstOrder)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

variable {σ : LPSignature}

/-! ## The edge -/

variable (σ) in
/-- **The finite-tree frames**: the one-frame category of the occurs-checked first-order action. -/
abbrev finiteFrames := Frames.ofSubstitution (FirstOrder.action σ)

variable (σ) in
/-- **Finite trees inside rational trees**, as a map of frame instances. -/
def finiteToRational : FrameMap (finiteFrames σ) (rationalFrames σ) where
  obj _ := PUnit.unit
  tm t := RTree.ofTerm t
  hom θ := ofSubst θ
  act θ t := (subst_ofTerm θ t).symm
  preserves same := congrArg RTree.ofTerm same

theorem finiteToRational_store (K : EquationStore (Term σ)) :
    (finiteToRational σ).store (a := PUnit.unit) K = ofStore K := rfl

/-- **The edge reflects the equivalence.** -/
theorem finiteToRational_reflects : (finiteToRational σ).Reflects :=
  fun same => RTree.ofTerm_injective same

/-! ## The license is acyclicity -/

/-- **An acyclic store**: the rational principal answers of its image take finite values. -/
def Acyclic (K : EquationStore (Term σ)) : Prop :=
  ∀ θ : RSubst σ, (rationalAction σ).Principal (ofStore K) θ → ∀ v, IsFinite (θ v)

/-- **Acyclic stores are the finitely solvable ones and the rationally refuted ones.** -/
theorem acyclic_iff (K : EquationStore (Term σ)) :
    Acyclic K ↔ (FirstOrder.action σ).Consistent K ∨ ¬ (rationalAction σ).Consistent (ofStore K) := by
  constructor
  · intro acyclic
    by_cases rational : (rationalAction σ).Consistent (ofStore K)
    · have principal := mgu_principal ((consistent_iff_not_refuted _).mp rational)
      exact Or.inl ((consistent_iff_acyclic K).mpr ⟨_, principal, acyclic _ principal⟩)
    · exact Or.inr rational
  · rintro (consistent | refuted) θ principal
    · exact principal_finite consistent principal
    · exact absurd ⟨θ, principal.sound⟩ refuted

/-- **Finitely solvable stores are covered**: the finite principal answer stays principal among
the rational solutions. -/
theorem finiteToRational_coversAt_of_consistent {K : EquationStore (Term σ)}
    (consistent : (FirstOrder.action σ).Consistent K) :
    (finiteToRational σ).CoversAt (a := PUnit.unit) K := by
  obtain ⟨θ, -, principal⟩ := finite_principal_of_consistent consistent
  exact FrameMap.coversAt_of_principal (Φ := finiteToRational σ) (m := PUnit.unit) principal.sound
    ((Frames.ofSubstitution_principal_iff _ _ _).mpr (principal_ofSubst principal))

theorem finiteToRational_licensedAt_of_acyclic {K : EquationStore (Term σ)} (acyclic : Acyclic K) :
    (finiteToRational σ).LicensedAt (a := PUnit.unit) K := by
  rcases (acyclic_iff K).mp acyclic with consistent | refuted
  · exact (finiteToRational_coversAt_of_consistent consistent).licensedAt
  · exact (FrameMap.coversAt_of_refuted (Φ := finiteToRational σ) (a := PUnit.unit) fun solvable =>
      refuted ((Frames.ofSubstitution_solvable_iff _ _).mp solvable)).licensedAt

/-- **The license holds exactly at the acyclic stores.** -/
theorem finiteToRational_licensedAt_iff (K : EquationStore (Term σ)) :
    (finiteToRational σ).LicensedAt (a := PUnit.unit) K ↔ Acyclic K := by
  refine ⟨fun licensed => (acyclic_iff K).mpr ?_, finiteToRational_licensedAt_of_acyclic⟩
  by_cases consistent : (FirstOrder.action σ).Consistent K
  · exact Or.inl consistent
  · refine Or.inr fun rational => consistent ?_
    exact (Frames.ofSubstitution_solvable_iff _ _).mp (licensed.reflects_solvable
      ((Frames.ofSubstitution_solvable_iff (rationalAction σ) (ofStore K)).mpr rational))

theorem finiteToRational_licensedOn : (finiteToRational σ).LicensedOn (fun _ K => Acyclic K) :=
  fun _ _ acyclic => finiteToRational_licensedAt_of_acyclic acyclic

/-! ## Matching against ground data -/

/-- Substitution fixes a ground tree. -/
theorem Raw.subst_ofTerm_ground (θ : σ.vars → Raw σ) (g : Term σ) (ground : g.isGround) :
    Raw.subst θ (Raw.ofTerm g) = Raw.ofTerm g := by
  induction g with
  | var v => exact (ground : False).elim
  | const c =>
    show Raw.subst θ (Raw.node (.const c) fun _ => Raw.bot) = Raw.node (.const c) fun _ => Raw.bot
    rw [Raw.subst_node _ (fun v same => by cases same)]
    simp
  | app f ts ih =>
    show Raw.subst θ (Raw.node (.fn f) fun i =>
        if h : i < σ.functionArity f then Raw.ofTerm (ts ⟨i, h⟩) else Raw.bot) =
      Raw.node (.fn f) fun i => if h : i < σ.functionArity f then Raw.ofTerm (ts ⟨i, h⟩) else Raw.bot
    rw [Raw.subst_node _ (fun v same => by cases same)]
    congr 1
    funext i
    split_ifs with inside
    · exact ih _ (ground _)
    · exact Raw.subst_bot _

theorem RTree.subst_ofTerm_ground (δ : RSubst σ) {g : Term σ} (ground : g.isGround) :
    RTree.subst δ (RTree.ofTerm g) = RTree.ofTerm g :=
  RTree.ext (Raw.subst_ofTerm_ground _ g ground)

open Classical in
/-- **The finite part of a rational substitution**: finite values are kept, every other variable
is sent to itself. -/
noncomputable def finitize (δ : RSubst σ) : Subst σ := fun v =>
  if h : IsFinite (δ v) then Classical.choose h else .var v

theorem ofTerm_finitize {δ : RSubst σ} {v : σ.vars} (finite : IsFinite (δ v)) :
    RTree.ofTerm (finitize δ v) = δ v := by
  unfold finitize
  rw [dif_pos finite]
  exact Classical.choose_spec finite

/-- **Where a rational substitution sends a finite term to a finite tree, its finite part does the
same.** -/
theorem finitize_applyTerm {δ : RSubst σ} :
    ∀ (p u : Term σ), RTree.subst δ (RTree.ofTerm p) = RTree.ofTerm u →
      (finitize δ).applyTerm p = u := by
  intro p
  induction p with
  | var v =>
    intro u same
    have value : δ v = RTree.ofTerm u := by
      rw [← RTree.subst_leaf δ v]
      exact same
    exact RTree.ofTerm_injective ((ofTerm_finitize ⟨u, value.symm⟩).trans value)
  | const c =>
    intro u same
    rw [RTree.subst_ofTerm_ground δ (g := .const c) trivial] at same
    exact RTree.ofTerm_injective same
  | app f ts ih =>
    intro u same
    have raw := congrArg Subtype.val same
    change Raw.subst (fun v => (δ v).1) (Raw.ofTerm (.app f ts)) = Raw.ofTerm u at raw
    have notVar := Raw.notVar_of_rigid (t := Raw.ofTerm (.app f ts)) rfl (Raw.rigid_fn f)
    have heads := congrFun raw []
    rw [Raw.subst_nil notVar] at heads
    cases u with
    | var w => simp [Raw.ofTerm, Raw.leaf, Raw.node] at heads
    | const c => simp [Raw.ofTerm, Raw.node] at heads
    | app g us =>
      have same' : f = g := by simpa [Raw.ofTerm, Raw.node] using heads
      subst same'
      have kids : ∀ i, (finitize δ).applyTerm (ts i) = us i := by
        intro i
        refine ih i (us i) (RTree.ext ?_)
        have kid := congrArg (Raw.child i) raw
        rw [Raw.child_subst notVar, Raw.ofTerm_app_child, Raw.ofTerm_app_child] at kid
        exact kid
      show Term.app f (fun i => (finitize δ).applyTerm (ts i)) = Term.app f us
      rw [funext kids]

/-- **A store matched against ground data**: every equation has a ground side. -/
def GroundSided (K : EquationStore (Term σ)) : Prop := ∀ e ∈ K, e.1.isGround ∨ e.2.isGround

/-- **Rational solutions of a ground-sided store have finite parts solving it.** -/
theorem consistent_of_groundSided {K : EquationStore (Term σ)} (ground : GroundSided K)
    (rational : (rationalAction σ).Consistent (ofStore K)) : (FirstOrder.action σ).Consistent K := by
  obtain ⟨δ, solved⟩ := rational
  refine ⟨finitize δ, fun e member => ?_⟩
  have equation : RTree.subst δ (RTree.ofTerm e.1) = RTree.subst δ (RTree.ofTerm e.2) :=
    solved _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  show (finitize δ).applyTerm e.1 = (finitize δ).applyTerm e.2
  rcases ground e member with left | right
  · rw [FirstOrder.ground_fixed _ _ left,
      finitize_applyTerm e.2 e.1 (equation.symm.trans (RTree.subst_ofTerm_ground δ left))]
  · rw [FirstOrder.ground_fixed _ _ right,
      finitize_applyTerm e.1 e.2 (equation.trans (RTree.subst_ofTerm_ground δ right))]

/-- **Ground-sided stores are acyclic.** -/
theorem acyclic_of_groundSided {K : EquationStore (Term σ)} (ground : GroundSided K) : Acyclic K := by
  rw [acyclic_iff]
  by_cases rational : (rationalAction σ).Consistent (ofStore K)
  · exact Or.inl (consistent_of_groundSided ground rational)
  · exact Or.inr rational

/-- **The license on matching against ground data**, decided on the source side alone. -/
theorem finiteToRational_licensedOn_groundSided :
    (finiteToRational σ).LicensedOn (fun _ K => GroundSided K) :=
  fun _ _ ground => finiteToRational_licensedAt_of_acyclic (acyclic_of_groundSided ground)

/-! ## The occurs-checked unifier as a decision procedure -/

section Decider

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- **`unifyTotal` decides every store of the finite-tree frames.** -/
def unifyDecider : (finiteFrames σ).Decider := fun K =>
  match accepted : unifyTotal K with
  | some θ => .principal PUnit.unit θ
      ((Frames.ofSubstitution_principal_iff _ _ _).mpr (FirstOrder.accepted_principal K θ accepted))
  | none => .refuted fun solvable =>
      (FirstOrder.refused_iff_inconsistent K).mp accepted ((Frames.ofSubstitution_solvable_iff _ _).mp solvable)

end Decider

/-! ## The rational-tree step at lifted firings -/

section Step

variable {O : Type} [DecidableEq O]

/-- A finite firing read over rational trees, without predicate queries. -/
def liftFiring (f : Firing (Term σ) (Subst σ) O) : Firing (RTree σ) (RSubst σ) O :=
  ⟨f.rule.map RTree.ofTerm, [], f.selection⟩

/-- A finite configuration read over rational trees. -/
def liftConfig (C : Configuration (Term σ) O) : Configuration (RTree σ) O :=
  ⟨ofStore C.equations, C.present⟩

/-- The equations of the equality checks. -/
def equalityGuards {T : Type*} : List (Check T) → EquationStore T
  | [] => []
  | .equal l r :: rest => (l, r) :: equalityGuards rest
  | .absent _ :: rest => equalityGuards rest
  | .count _ _ :: rest => equalityGuards rest

theorem mem_equalityGuards {T : Type*} {e : T × T} (checks : List (Check T)) :
    e ∈ equalityGuards checks ↔ Check.equal e.1 e.2 ∈ checks := by
  induction checks with
  | nil => simp [equalityGuards]
  | cons c rest ih =>
    cases c with
    | equal l r =>
      obtain ⟨e₁, e₂⟩ := e
      simp [equalityGuards, ih]
    | absent p => simp [equalityGuards, ih]
    | count p n => simp [equalityGuards, ih]

theorem ofStore_append (K L : EquationStore (Term σ)) : ofStore (K ++ L) = ofStore K ++ ofStore L :=
  List.map_append

omit [DecidableEq O] in
theorem equations_lift (label : O → Term σ) : ∀ (ps : List (Term σ)) (sel : List O),
    Selection.equations (fun o => RTree.ofTerm (label o)) (ps.map RTree.ofTerm) sel =
      ofStore (Selection.equations label ps sel)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ps, _ :: sel => congrArg (_ :: ·) (equations_lift label ps sel)

omit [DecidableEq O] in
/-- **The information of a lifted firing is the lifted problem.** -/
theorem problem_lift (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) :
    (liftFiring f).selection.problem (fun o => RTree.ofTerm (label o)) (liftFiring f).rule
        (liftConfig C) = ofStore (f.selection.problem label f.rule C) := by
  show ofStore C.equations ++
      Selection.equations (fun o => RTree.ofTerm (label o)) (f.rule.take.map RTree.ofTerm)
        f.selection.taken ++
      Selection.equations (fun o => RTree.ofTerm (label o)) (f.rule.read.map RTree.ofTerm)
        f.selection.read ++ ofStore f.rule.tell = _
  rw [equations_lift, equations_lift]
  simp only [Selection.problem, ofStore_append]

/-- **The checks of a lifted firing with equality checks are its lifted equation guards.** -/
theorem holds_lift_iff (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r)
    (b : PUnit) (g : RSubst σ) :
    (rationalStep σ (fun o => RTree.ofTerm (label o))).Holds (s := liftConfig C) (liftFiring f) b g ↔
      (rationalFrames σ).Models (a := PUnit.unit) (b := b) g (ofStore (equalityGuards f.rule.checks)) := by
  constructor
  · rintro ⟨checks, -⟩ e member
    obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp member
    exact checks _ (List.mem_map.mpr ⟨_, (mem_equalityGuards _).mp inside, rfl⟩)
  · intro models
    refine ⟨fun check member => ?_, fun query member => by cases member⟩
    obtain ⟨c, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨l, r, rfl⟩ := onlyEqual c inside
    exact models _ (List.mem_map.mpr ⟨(l, r), (mem_equalityGuards _).mpr inside, rfl⟩)

/-- **A lifted firing is a dispatched firing of the rational-tree step.** -/
def dispatched (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O) (C : Configuration (Term σ) O)
    (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r) :
    (finiteToRational σ).Dispatched (rationalStep σ (fun o => RTree.ofTerm (label o))).toStep
      (s := liftConfig C) (liftFiring f) where
  source := PUnit.unit
  frame := rfl
  problem := f.selection.problem label f.rule C
  guards := equalityGuards f.rule.checks
  information := by
    intro b g
    show (rationalFrames σ).Models g ((liftFiring f).selection.problem (fun o => RTree.ofTerm (label o))
        (liftFiring f).rule (liftConfig C)) ↔
      (rationalFrames σ).Models g (ofStore (f.selection.problem label f.rule C))
    rw [problem_lift]
  holds := holds_lift_iff label f C onlyEqual

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- **On an acyclic problem the rational-tree step's admission is computed by `unifyTotal`.** -/
theorem lift_admits_iff (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r)
    (acyclic : Acyclic (f.selection.problem label f.rule C)) :
    (rationalStep σ (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig C) (liftFiring f) ↔
      (rationalStep σ (fun o => RTree.ofTerm (label o))).Shapes (s := liftConfig C) (liftFiring f) ∧
      Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) ∧
      (unifyDecider (a := PUnit.unit) (f.selection.problem label f.rule C)).Accepts
        (equalityGuards f.rule.checks) :=
  FrameMap.dispatch_admits_iff_decider finiteToRational_reflects unifyDecider _
    (dispatched label f C onlyEqual) (finiteToRational_licensedAt_of_acyclic acyclic)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- **At a finite principal answer the rational-tree step's admission is the guards at the
answer**, with no acyclicity hypothesis. -/
theorem lift_admits_iff_of_principal (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r)
    {θ : Subst σ} (principal : (FirstOrder.action σ).Principal (f.selection.problem label f.rule C) θ) :
    (rationalStep σ (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig C) (liftFiring f) ↔
      (rationalStep σ (fun o => RTree.ofTerm (label o))).Shapes (s := liftConfig C) (liftFiring f) ∧
      Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) ∧
      (FirstOrder.action σ).Models θ (equalityGuards f.rule.checks) :=
  FrameMap.dispatch_admits_iff_of_principal finiteToRational_reflects _ (dispatched label f C onlyEqual)
    (finiteToRational_coversAt_of_consistent ⟨θ, principal.sound⟩).licensedAt (m := PUnit.unit)
    ((Frames.ofSubstitution_principal_iff _ _ _).mpr principal)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- **A finite refutation of an acyclic problem refuses the lifted firing.** -/
theorem lift_refused (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r)
    (acyclic : Acyclic (f.selection.problem label f.rule C))
    (refuted : ¬ (FirstOrder.action σ).Consistent (f.selection.problem label f.rule C)) :
    ¬ (rationalStep σ (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig C) (liftFiring f) :=
  FrameMap.dispatch_refused _ (dispatched label f C onlyEqual)
    (finiteToRational_licensedAt_of_acyclic acyclic)
    fun solvable => refuted ((Frames.ofSubstitution_solvable_iff _ _).mp solvable)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- The checks of a finite firing with equality checks and no predicate queries are its equation
guards. -/
theorem holds_finite_iff (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r)
    (noQueries : f.queries = []) (b : PUnit) (g : Subst σ) :
    (firstOrder (FirstOrder.action σ) label).Holds (s := C) f b g ↔
      (finiteFrames σ).Models (a := PUnit.unit) (b := b) g (equalityGuards f.rule.checks) := by
  constructor
  · rintro ⟨checks, -⟩ e member
    exact checks _ ((mem_equalityGuards _).mp member)
  · intro models
    refine ⟨fun check member => ?_, fun query member => ?_⟩
    · obtain ⟨l, r, rfl⟩ := onlyEqual check member
      exact models _ ((mem_equalityGuards (e := (l, r)) _).mpr member)
    · rw [noQueries] at member
      cases member

/-- **On acyclic problems the rational-tree step simulates the finite-tree step**: a finite firing
with equality checks and no predicate queries is admitted exactly when its reading over rational
trees is. -/
theorem lift_admits_iff_admits (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r)
    (noQueries : f.queries = []) (acyclic : Acyclic (f.selection.problem label f.rule C)) :
    (rationalStep σ (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig C) (liftFiring f) ↔
      (firstOrder (FirstOrder.action σ) label).Admits (s := C) f := by
  rw [FrameMap.dispatch_admits_iff finiteToRational_reflects _ (dispatched label f C onlyEqual)
      (finiteToRational_licensedAt_of_acyclic acyclic) (unifyDecider (a := PUnit.unit) _).decides,
    (firstOrder (FirstOrder.action σ) label).admits_iff (s := C) f]
  have holds : (finiteFrames σ).Entails (a := PUnit.unit) (f.selection.problem label f.rule C)
        ((firstOrder (FirstOrder.action σ) label).Holds (s := C) f) ↔
      (finiteFrames σ).Entails (a := PUnit.unit) (f.selection.problem label f.rule C)
        (fun _ g => (finiteFrames σ).Models g (equalityGuards f.rule.checks)) :=
    ⟨fun asked b g solved => (holds_finite_iff label f C onlyEqual noQueries b g).mp (asked b g solved),
      fun asked b g solved => (holds_finite_iff label f C onlyEqual noQueries b g).mpr (asked b g solved)⟩
  refine and_congr ?_ (and_congr Iff.rfl (and_congr Iff.rfl holds.symm))
  have produced : f.selection.made.map (fun o => RTree.ofTerm (label o)) = f.rule.produce.map RTree.ofTerm ↔
      f.selection.made.map label = f.rule.produce := by
    rw [show f.selection.made.map (fun o => RTree.ofTerm (label o)) =
      (f.selection.made.map label).map RTree.ofTerm from by rw [List.map_map]; rfl]
    exact (List.map_injective_iff.mpr RTree.ofTerm_injective).eq_iff
  show (_ ∧ _ ∧ (f.rule.take.map RTree.ofTerm).length = _ ∧ (f.rule.read.map RTree.ofTerm).length = _ ∧
    f.selection.made.map (fun o => RTree.ofTerm (label o)) = f.rule.produce.map RTree.ofTerm) ↔ _
  rw [List.length_map, List.length_map, produced]
  exact Iff.rfl

/-- **Rational unification followed by the acyclicity check decides the finite-tree step.** -/
theorem admits_iff_lift_acyclic (label : O → Term σ) (f : Firing (Term σ) (Subst σ) O)
    (C : Configuration (Term σ) O) (onlyEqual : ∀ c ∈ f.rule.checks, ∃ l r, c = .equal l r)
    (noQueries : f.queries = []) :
    (firstOrder (FirstOrder.action σ) label).Admits (s := C) f ↔
      (rationalStep σ (fun o => RTree.ofTerm (label o))).Admits (s := liftConfig C) (liftFiring f) ∧
        Acyclic (f.selection.problem label f.rule C) := by
  constructor
  · intro admitted
    have acyclic : Acyclic (f.selection.problem label f.rule C) :=
      (acyclic_iff _).mpr (Or.inl ((Frames.ofSubstitution_solvable_iff _ _).mp
        ((firstOrder (FirstOrder.action σ) label).solvable_information admitted)))
    exact ⟨(lift_admits_iff_admits label f C onlyEqual noQueries acyclic).mpr admitted, acyclic⟩
  · rintro ⟨admitted, acyclic⟩
    exact (lift_admits_iff_admits label f C onlyEqual noQueries acyclic).mp admitted

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.finiteToRational
#print axioms Rational.finiteToRational_reflects
#print axioms Rational.acyclic_iff
#print axioms Rational.finiteToRational_coversAt_of_consistent
#print axioms Rational.finiteToRational_licensedAt_of_acyclic
#print axioms Rational.finiteToRational_licensedAt_iff
#print axioms Rational.finiteToRational_licensedOn
#print axioms Rational.Raw.subst_ofTerm_ground
#print axioms Rational.finitize_applyTerm
#print axioms Rational.consistent_of_groundSided
#print axioms Rational.acyclic_of_groundSided
#print axioms Rational.finiteToRational_licensedOn_groundSided
#print axioms Rational.unifyDecider
#print axioms Rational.problem_lift
#print axioms Rational.holds_lift_iff
#print axioms Rational.dispatched
#print axioms Rational.lift_admits_iff
#print axioms Rational.lift_admits_iff_of_principal
#print axioms Rational.lift_refused
#print axioms Rational.holds_finite_iff
#print axioms Rational.lift_admits_iff_admits
#print axioms Rational.admits_iff_lift_acyclic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
