import Mathlib.Data.Finset.Card
import Mettapedia.Languages.MeTTa.FreshFrameOccursCheck

/-!
# Variable shunting in the region collector

The compiled open equation tier keeps its logical variables as cells of a
region.  A cell is unbound or bound to a term, which may mention other cells.
Bindings are undone by a trail: every entry names a cell, a choice point
(frame) records the trail length when it was pushed, and restoring a frame
unbinds the cells named at trail positions from its mark on.  The region
collector copies what is live and, while copying, replaces every bound cell
that no live frame can unbind by its value, following chains of such cells
(variable shunting).  A cell is revocable when the trail names it at a position
from the oldest live frame's mark on; with no live frame nothing is revocable.

**Model.**  Terms are `OSLFCore.Atom`s, cells are their variables, and a cell
store is a `SubstitutionAlgebra.Subst`.  A `Region` has cells, a trail (oldest
entry first) and the marks of its live frames (newest first).  `Step` is one
operation of the machine: an occurs-checked binding of an unbound cell, with or
without a trail entry; pushing a frame; restoring the newest frame; popping it.
The occurs check is `FreshFrameOccursCheck.Reaches`, the reachability the C
unifier walks.

**Termination.**  `Child σ y x` says that `y` occurs in the value bound to `x`;
`Terminating σ` says that `Child σ` is well founded, i.e. following bindings
terminates.  It implies `FreshFrameOccursCheck.Acyclic` (`Terminating.acyclic`);
conversely an acyclic store that binds finitely many cells, as a region does,
terminates (`Terminating.of_acyclic`), and finiteness is needed
(`Canary.acyclic_infinite_store_does_not_terminate`).  Termination is
preserved by occurs-checked binding (`Terminating.bind`, which needs no
hypothesis on the cell's previous state) and by unbinding
(`Terminating.unbindAll`), hence by every step (`Region.Valid.step`).

**Shunting and resolution.**  `shunt σ R` replaces every bound cell outside
`R` by the shunting of its value, recursively; it is defined by well-founded
recursion on `Child σ`.  Resolution, the answer resolver's replacement of every
bound cell, is shunting with nothing excluded (`resolve`).

**Results.**

* `resolve_shunt_of_agree`: if a store agrees with `σ` on every binding outside
  `R`, then resolving the shunted term under it is resolving the term.
* `Region.Reachable.permanent_fixed`: along any sequence of steps from a valid
  region, every bound cell that is not revocable keeps its binding.  No restore
  of a live frame pops the trail below the oldest frame's mark, and no later
  entry names such a cell, since only unbound cells are bound.
* `Region.shunt_resolve` (keystone): for every region reachable from a valid
  one by bindings, pushes, restores of live frames and pops, the resolution of
  every term shunted at the origin equals the resolution of the term itself.
* The collector also replaces every binding's value by its shunted copy.
  `resolve_shuntCells`: resolving a shunted term under that image store is
  resolving the term under the store; the image store is terminating
  (`Terminating.shuntCells`).  `Region.collected_step`: every step of a region
  reachable from the origin is matched by a step of its image that binds the
  shunted term, with the same unboundness and occurs-check verdicts
  (`reaches_shuntCells_iff`), so `Region.resolve_collected` holds along the
  whole future of the collected region.
* `reaches_iff_mem_vars_resolve`: the occurs check, which walks the cells a
  term reaches through bindings, is membership of the unbound cell in the
  term's resolution.

**Negative witnesses.**  Shunting a revocable binding changes a term's
resolution after its frame is restored (`Canary.shunting_revocable_is_unsound`).
Judging revocability from the newest frame's mark instead of the oldest is
unsound as soon as the newest frame is popped
(`Canary.newest_mark_is_unsound`).  Binding without the occurs check creates a
chain that does not terminate (`Canary.unchecked_binding_does_not_terminate`).
A binding made before the oldest frame is shunted soundly
(`Canary.binding_below_oldest_mark_survives`).

**Correspondence with the C region.**  The unifier checks occurrence before
every binding, and the head binds only a literal or a node of fresh cells,
which pass that check trivially; every C binding is therefore a `Step.bind`.
A binding records its cell on the trail only when the cell is older than the
newest frame; the model allows a binding
with or without an entry, and the theorems hold for every such choice.  A
restore also resets the region's allocation and discards the cells created
after the frame, whose indices are then reused.  The model never reuses a cell
name, so a discarded cell simply keeps its binding: after the restore no live
term mentions it, because every term the restored frame reaches was built before
the cell existed, and every older cell bound to a term mentioning it was bound
after the frame and is unbound by the restore.  That reachability argument is
the collector's own and is not formalized here; it requires that the collector
trace no slot holding a term built after a frame that has since been restored,
which the store trail of first-occurrence stores guarantees
(`FirstOccurrenceStores.storeTrailed_collector_safe`).  The collector computes
revocability exactly as `Region.Revocable` does, from the oldest frame's mark,
or from the trail's length when no frame is live.  It follows the chain of
non-revocable bound cells at every node it visits and copies the young
generation's structure, which is `shunt`; atoms of the old generation it keeps
as they are, having followed only the chain that reached them.  Such a partial
shunting is covered by `shunt_value` (replacing a non-revocable bound cell by
its value, unshunted, keeps a term's shunting, and shunting is a substitution,
so the replacement may happen anywhere in a term) and
`Region.resolve_eq_of_shunt_eq` (terms with the same shunting resolve alike in
every reachable region).

**Not covered.**  The renaming of reached cells to consecutive indices, the
compaction of the trail and of frame marks, and the copying of region memory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegionVariableShunting

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Var Subst vars subst comp)
open Mettapedia.Languages.MeTTa.FreshFrameOccursCheck (Reaches Acyclic)

/-! ## Binding chains -/

/-- `y` occurs in the value bound to `x`: following `x` leads to `y`. -/
def Child (σ : Subst) (y x : Var) : Prop :=
  ∃ u, σ x = some u ∧ y ∈ vars u

/-- Following bindings terminates. -/
abbrev Terminating (σ : Subst) : Prop :=
  WellFounded (Child σ)

/-- Unbind every cell of a list. -/
def unbindAll (σ : Subst) (cells : List Var) : Subst :=
  fun x => if x ∈ cells then none else σ x

theorem reaches_var_self (σ : Subst) (x : Var) : Reaches σ (.var x) x :=
  .here (by simp [vars])

/-- A variable of a term that reaches `x` makes the term reach `x`. -/
theorem reaches_of_mem_of_reaches_var {σ : Subst} {t : Atom} {y x : Var}
    (member : y ∈ vars t) (reach : Reaches σ (.var y) x) : Reaches σ t x := by
  cases reach with
  | here occurs =>
      have same : x = y := by simpa [vars] using occurs
      subst same
      exact .here member
  | @through _ u z _ occurs bound rest =>
      have same : z = y := by simpa [vars] using occurs
      subst same
      exact .through member bound rest

/-- A cell reaches what its children reach. -/
theorem reaches_of_child {σ : Subst} {y z x : Var} (child : Child σ y z)
    (reach : Reaches σ (.var y) x) : Reaches σ (.var z) x := by
  obtain ⟨u, bound, member⟩ := child
  exact .through (by simp [vars]) bound (reaches_of_mem_of_reaches_var member reach)

/-- A reachability path out of the value of `x` is a path of children. -/
theorem transGen_of_reaches {σ : Subst} {t : Atom} {y : Var}
    (reach : Reaches σ t y) :
    ∀ x, (∀ z ∈ vars t, Child σ z x) → Relation.TransGen (Child σ) y x := by
  induction reach with
  | here member =>
      intro x children
      exact .single (children _ member)
  | @through t u z y member bound _ inductionHypothesis =>
      intro x children
      exact (inductionHypothesis z fun w occurs => ⟨u, bound, occurs⟩).tail
        (children z member)

/-- A terminating store has no cycle. -/
theorem Terminating.acyclic {σ : Subst} (terminating : Terminating σ) :
    Acyclic σ := by
  intro x u bound reach
  have cycle : Relation.TransGen (Child σ) x x :=
    transGen_of_reaches reach x fun z member => ⟨u, bound, member⟩
  exact terminating.transGen.asymmetric x x cycle cycle

/-- A cell with a descendant is bound. -/
theorem bound_of_transGen {σ : Subst} {y x : Var}
    (descendant : Relation.TransGen (Child σ) y x) : ∃ u, σ x = some u := by
  cases descendant with
  | single child => exact ⟨child.choose, child.choose_spec.1⟩
  | tail _ child => exact ⟨child.choose, child.choose_spec.1⟩

/-- A descendant of a bound cell is reached from its value. -/
theorem reaches_of_transGen {σ : Subst} {y x : Var}
    (descendant : Relation.TransGen (Child σ) y x) {u : Atom} (bound : σ x = some u) :
    Reaches σ u y := by
  induction descendant generalizing u with
  | single child =>
      obtain ⟨u', bound', member⟩ := child
      rw [bound] at bound'
      cases bound'
      exact .here member
  | @tail z x earlier child inductionHypothesis =>
      obtain ⟨u', bound', member⟩ := child
      rw [bound] at bound'
      cases bound'
      obtain ⟨v, zBound⟩ := bound_of_transGen earlier
      exact .through member zBound (inductionHypothesis zBound)

/-- **Acyclic finite stores terminate.**  A store that binds only cells of a
finite list, and in which no binding's value reaches its own cell, has no
infinite chain of bindings: each child of a cell has strictly fewer bound
descendants than the cell. -/
theorem Terminating.of_acyclic {σ : Subst} (acyclic : Acyclic σ) (cells : List Var)
    (listed : ∀ x u, σ x = some u → x ∈ cells) : Terminating σ := by
  classical
  let below : Var → Nat := fun x =>
    (cells.toFinset.filter fun z => Relation.TransGen (Child σ) z x).card
  have irreflexive : ∀ x, ¬ Relation.TransGen (Child σ) x x := by
    intro x loop
    obtain ⟨u, bound⟩ := bound_of_transGen loop
    exact acyclic x u bound (reaches_of_transGen loop bound)
  have decreasing : ∀ y x, Child σ y x → (∃ v, σ y = some v) → below y < below x := by
    intro y x child ⟨v, yBound⟩
    apply Finset.card_lt_card
    refine ⟨fun z member => ?_, fun contains => ?_⟩
    · simp only [Finset.mem_filter] at member ⊢
      exact ⟨member.1, member.2.tail child⟩
    · have yListed : y ∈ cells.toFinset.filter fun z => Relation.TransGen (Child σ) z x :=
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (listed y v yBound), .single child⟩
      exact irreflexive y (Finset.mem_filter.mp (contains yListed)).2
  refine ⟨fun x => ?_⟩
  induction hx : below x using Nat.strong_induction_on generalizing x with
  | _ n inductionHypothesis =>
      refine Acc.intro x fun y child => ?_
      cases yBound : σ y with
      | none =>
          exact Acc.intro y fun z grandchild => by
            obtain ⟨w, bound, _⟩ := grandchild
            rw [yBound] at bound
            cases bound
      | some v =>
          exact inductionHypothesis (below y) (hx ▸ decreasing y x child ⟨v, yBound⟩) y rfl

/-- **Occurs-checked binding keeps chains terminating.**  The cell's previous
state is irrelevant: its old children are dropped, and its new children cannot
lead back to it. -/
theorem Terminating.bind {σ : Subst} (terminating : Terminating σ) {x : Var}
    {t : Atom} (occurs : ¬ Reaches σ t x) :
    Terminating (FreshFrameOccursCheck.bind σ x t) := by
  have avoiding : ∀ z, ¬ Reaches σ (.var z) x →
      Acc (Child (FreshFrameOccursCheck.bind σ x t)) z := by
    intro z
    refine terminating.induction z (C := fun z => ¬ Reaches σ (.var z) x →
      Acc (Child (FreshFrameOccursCheck.bind σ x t)) z) ?_
    intro z inductionHypothesis noPath
    refine Acc.intro z fun y child => ?_
    have distinct : z ≠ x := fun same => noPath (same ▸ reaches_var_self σ x)
    obtain ⟨u, bound, member⟩ := child
    rw [FreshFrameOccursCheck.bind_other σ t distinct] at bound
    exact inductionHypothesis y ⟨u, bound, member⟩
      fun reach => noPath (reaches_of_child ⟨u, bound, member⟩ reach)
  refine ⟨fun z => terminating.induction z (C := fun z =>
    Acc (Child (FreshFrameOccursCheck.bind σ x t)) z) ?_⟩
  intro z inductionHypothesis
  refine Acc.intro z fun y child => ?_
  obtain ⟨u, bound, member⟩ := child
  by_cases same : z = x
  · subst same
    rw [FreshFrameOccursCheck.bind_self] at bound
    cases bound
    exact avoiding y fun reach => occurs (reaches_of_mem_of_reaches_var member reach)
  · rw [FreshFrameOccursCheck.bind_other σ t same] at bound
    exact inductionHypothesis y ⟨u, bound, member⟩

/-- Unbinding keeps chains terminating. -/
theorem Terminating.unbindAll {σ : Subst} (terminating : Terminating σ)
    (cells : List Var) : Terminating (unbindAll σ cells) := by
  refine Subrelation.wf (fun {y x} child => ?_) terminating
  obtain ⟨u, bound, member⟩ := child
  unfold RegionVariableShunting.unbindAll at bound
  split at bound
  · cases bound
  · exact ⟨u, bound, member⟩

/-! ## Shunting and resolution -/

section Shunting

variable (σ : Subst) (terminating : Terminating σ) (R : Var → Prop)
  [DecidablePred R]

/-- The shunting of a cell: a bound cell outside `R` stands for the shunting of
its value; any other cell stays itself. -/
def shuntVar : Var → Atom :=
  terminating.fix fun x shuntChild =>
    match bound : σ x with
    | none => .var x
    | some u =>
        if R x then .var x
        else
          subst (fun y => if member : y ∈ vars u
            then some (shuntChild y ⟨u, bound, member⟩) else none) u

/-- Shunt every cell of a term. -/
def shunt (t : Atom) : Atom :=
  subst (fun y => some (shuntVar σ terminating R y)) t

variable {σ} {R}

theorem shuntVar_of_none {x : Var} (unbound : σ x = none) :
    shuntVar σ terminating R x = .var x := by
  rw [shuntVar, WellFounded.fix_eq]
  split
  · rfl
  · next u bound => rw [unbound] at bound; cases bound

theorem shuntVar_of_mem {x : Var} (excluded : R x) :
    shuntVar σ terminating R x = .var x := by
  rw [shuntVar, WellFounded.fix_eq]
  split
  · rfl
  · next u' _ => simp [excluded]

theorem shuntVar_of_not_mem {x : Var} {u : Atom} (bound : σ x = some u)
    (included : ¬ R x) : shuntVar σ terminating R x = shunt σ terminating R u := by
  rw [shuntVar, WellFounded.fix_eq]
  split
  · next unbound => rw [bound] at unbound; cases unbound
  · next u' bound' =>
      rw [bound] at bound'
      cases bound'
      simp only [included, if_false]
      apply SubstitutionAlgebra.subst_congr_on_vars
      intro y member
      simp [member, shuntVar]

@[simp] theorem shunt_var (x : Var) :
    shunt σ terminating R (.var x) = shuntVar σ terminating R x := by
  simp [shunt, subst]

end Shunting

/-- Resolution: every bound cell replaced, recursively, by the resolution of
its value.  It is shunting with no cell excluded. -/
def resolve (σ : Subst) (terminating : Terminating σ) (t : Atom) : Atom :=
  shunt σ terminating (fun _ => False) t

section Resolution

variable {σ : Subst} (terminating : Terminating σ)

theorem resolve_var_of_none {x : Var} (unbound : σ x = none) :
    resolve σ terminating (.var x) = .var x := by
  rw [resolve, shunt_var, shuntVar_of_none terminating unbound]

theorem resolve_var_of_some {x : Var} {u : Atom} (bound : σ x = some u) :
    resolve σ terminating (.var x) = resolve σ terminating u := by
  rw [resolve, shunt_var, shuntVar_of_not_mem terminating bound (fun impossible => impossible)]
  rfl

/-- Resolution distributes over a substitution. -/
theorem resolve_subst (f : Var → Atom) (t : Atom) :
    resolve σ terminating (subst (fun y => some (f y)) t) =
      subst (fun y => some (resolve σ terminating (f y))) t := by
  change subst _ (subst _ t) = _
  rw [SubstitutionAlgebra.subst_subst]
  rfl

end Resolution

/-! ## Shunting commutes with resolution -/

section Commutation

variable {σ σ' : Subst} (terminating : Terminating σ)
  (terminating' : Terminating σ') {R : Var → Prop} [DecidablePred R]

/-- The bindings outside `R` of `σ` are bindings of `σ'`. -/
def AgreesOutside (σ : Subst) (R : Var → Prop) (σ' : Subst) : Prop :=
  ∀ x u, σ x = some u → ¬ R x → σ' x = some u

/-- **Shunting is invisible to resolution.**  Under a store that keeps every
binding shunting followed, resolving a shunted term is resolving the term. -/
theorem resolve_shunt_of_agree (agree : AgreesOutside σ R σ') (t : Atom) :
    resolve σ' terminating' (shunt σ terminating R t) = resolve σ' terminating' t := by
  have cells : ∀ x, resolve σ' terminating' (shuntVar σ terminating R x) =
      resolve σ' terminating' (.var x) := by
    intro x
    refine terminating.induction x (C := fun x =>
      resolve σ' terminating' (shuntVar σ terminating R x) =
        resolve σ' terminating' (.var x)) ?_
    intro x inductionHypothesis
    cases bound : σ x with
    | none => rw [shuntVar_of_none terminating bound]
    | some u =>
        by_cases excluded : R x
        · rw [shuntVar_of_mem terminating excluded]
        · rw [shuntVar_of_not_mem terminating bound excluded,
            resolve_var_of_some terminating' (agree x u bound excluded)]
          unfold shunt
          rw [resolve_subst]
          apply SubstitutionAlgebra.subst_congr_on_vars
          intro y member
          rw [inductionHypothesis y ⟨u, bound, member⟩]
          simp [resolve]
  unfold shunt
  rw [resolve_subst]
  apply SubstitutionAlgebra.subst_congr_on_vars
  intro y _
  rw [cells y]
  simp [resolve]

/-- Terms with the same shunting resolve alike under every store that keeps
the bindings shunting followed. -/
theorem resolve_eq_of_shunt_eq (agree : AgreesOutside σ R σ') {t t' : Atom}
    (same : shunt σ terminating R t = shunt σ terminating R t') :
    resolve σ' terminating' t = resolve σ' terminating' t' := by
  rw [← resolve_shunt_of_agree terminating terminating' agree t, same,
    resolve_shunt_of_agree terminating terminating' agree t']

/-- Replacing a bound cell outside `R` by its value, unshunted, keeps the
shunting: a partial shunting has the shunting of the term. -/
theorem shunt_value {x : Var} {u : Atom} (bound : σ x = some u) (included : ¬ R x) :
    shunt σ terminating R u = shunt σ terminating R (.var x) := by
  rw [shunt_var, shuntVar_of_not_mem terminating bound included]

end Commutation

/-! ## Variables of substituted and resolved terms -/

theorem mem_vars_expression_iff {es : List Atom} {w : Var} :
    w ∈ vars (.expression es) ↔ ∃ a ∈ es, w ∈ vars a := by
  induction es with
  | nil => simp [vars, vars.varsList]
  | cons b bs inductionHypothesis =>
      have unfolded : vars (.expression (b :: bs)) =
          vars b ++ vars (.expression bs) := by
        simp [vars, vars.varsList]
      rw [unfolded, List.mem_append, inductionHypothesis]
      simp

theorem substList_eq_map (τ : Subst) (es : List Atom) :
    subst.substList τ es = es.map (subst τ) := by
  induction es with
  | nil => rfl
  | cons a as inductionHypothesis =>
      simp [subst.substList, inductionHypothesis]

/-- A variable of a substituted term comes from the image of one of the term's
variables. -/
theorem mem_vars_subst {f : Var → Atom} {y : Var} :
    ∀ t : Atom, y ∈ vars (subst (fun w => some (f w)) t) →
      ∃ w ∈ vars t, y ∈ vars (f w)
  | .symbol _, member => by simp [subst, vars] at member
  | .grounded _, member => by simp [subst, vars] at member
  | .var v, member => ⟨v, by simp [vars], by simpa [subst] using member⟩
  | .expression es, member => by
      have unfolded : subst (fun w => some (f w)) (.expression es) =
          .expression (es.map (subst fun w => some (f w))) := by
        simp [subst, substList_eq_map]
      rw [unfolded, mem_vars_expression_iff] at member
      obtain ⟨image, imageMember, occurs⟩ := member
      obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp imageMember
      obtain ⟨w, wMember, fMember⟩ := mem_vars_subst a occurs
      exact ⟨w, mem_vars_expression_iff.mpr ⟨a, aMember, wMember⟩, fMember⟩
termination_by t => sizeOf t

/-- Every variable of the image of a term's variable occurs in the substituted
term. -/
theorem mem_vars_subst_of_mem {f : Var → Atom} {y w : Var} :
    ∀ t : Atom, w ∈ vars t → y ∈ vars (f w) →
      y ∈ vars (subst (fun w => some (f w)) t)
  | .symbol _, member, _ => by simp [vars] at member
  | .grounded _, member, _ => by simp [vars] at member
  | .var v, member, occurs => by
      have same : w = v := by simpa [vars] using member
      subst same
      simpa [subst] using occurs
  | .expression es, member, occurs => by
      have unfolded : subst (fun w => some (f w)) (.expression es) =
          .expression (es.map (subst fun w => some (f w))) := by
        simp [subst, substList_eq_map]
      rw [unfolded, mem_vars_expression_iff]
      obtain ⟨a, aMember, wMember⟩ := mem_vars_expression_iff.mp member
      exact ⟨_, List.mem_map_of_mem aMember, mem_vars_subst_of_mem a wMember occurs⟩
termination_by t => sizeOf t

/-- The cells a resolution mentions are reached. -/
theorem reaches_of_mem_vars_resolve {σ : Subst} (terminating : Terminating σ)
    {x : Var} : ∀ w, x ∈ vars (resolve σ terminating (.var w)) →
      Reaches σ (.var w) x := by
  intro w
  refine terminating.induction w (C := fun w =>
    x ∈ vars (resolve σ terminating (.var w)) → Reaches σ (.var w) x) ?_
  intro w inductionHypothesis member
  cases bound : σ w with
  | none =>
      rw [resolve_var_of_none terminating bound] at member
      have same : x = w := by simpa [vars] using member
      exact same ▸ reaches_var_self σ x
  | some u =>
      rw [resolve_var_of_some terminating bound] at member
      obtain ⟨w', w'Member, occurs⟩ := mem_vars_subst u member
      have occurs' : x ∈ vars (resolve σ terminating (.var w')) := by
        simpa [resolve] using occurs
      exact reaches_of_child ⟨u, bound, w'Member⟩
        (inductionHypothesis w' ⟨u, bound, w'Member⟩ occurs')

/-- **The occurs check is membership in the resolution.**  An unbound cell is
reached from a term exactly when it occurs in the term's resolution. -/
theorem reaches_iff_mem_vars_resolve {σ : Subst} (terminating : Terminating σ)
    {t : Atom} {x : Var} (unbound : σ x = none) :
    Reaches σ t x ↔ x ∈ vars (resolve σ terminating t) := by
  constructor
  · intro reach
    induction reach with
    | here member =>
        refine mem_vars_subst_of_mem _ member ?_
        have resolved := resolve_var_of_none terminating unbound
        simp only [resolve, shunt_var] at resolved
        rw [resolved]
        simp [vars]
    | @through t u z _ member bound _ inductionHypothesis =>
        refine mem_vars_subst_of_mem _ member ?_
        have resolved := resolve_var_of_some terminating bound
        simp only [resolve, shunt_var] at resolved
        rw [resolved]
        exact inductionHypothesis unbound
  · intro member
    obtain ⟨w, wMember, occurs⟩ := mem_vars_subst t member
    exact reaches_of_mem_of_reaches_var wMember
      (reaches_of_mem_vars_resolve terminating w (by simpa [resolve] using occurs))

/-! ## The collector's image store -/

section Collector

variable {σ σ' : Subst} (terminating : Terminating σ) {R : Var → Prop}
  [DecidablePred R]

/-- The collector's image of a store: every binding's value shunted. -/
def shuntCells (σ : Subst) (terminating : Terminating σ) (R : Var → Prop)
    [DecidablePred R] (σ' : Subst) : Subst :=
  fun x => (σ' x).map (shunt σ terminating R)

/-- The cells a shunted cell mentions are reached by binding chains of any
store that keeps the bindings shunting followed. -/
theorem vars_shuntVar (agree : AgreesOutside σ R σ') :
    ∀ z, ∀ y ∈ vars (shuntVar σ terminating R z),
      Relation.ReflTransGen (Child σ') y z := by
  intro z
  refine terminating.induction z (C := fun z => ∀ y ∈ vars (shuntVar σ terminating R z),
    Relation.ReflTransGen (Child σ') y z) ?_
  intro z inductionHypothesis y member
  cases bound : σ z with
  | none =>
      rw [shuntVar_of_none terminating bound] at member
      have same : y = z := by simpa [vars] using member
      exact same ▸ .refl
  | some u =>
      by_cases excluded : R z
      · rw [shuntVar_of_mem terminating excluded] at member
        have same : y = z := by simpa [vars] using member
        exact same ▸ .refl
      · rw [shuntVar_of_not_mem terminating bound excluded] at member
        obtain ⟨w, wMember, occurs⟩ := mem_vars_subst u member
        exact (inductionHypothesis w ⟨u, bound, wMember⟩ y occurs).tail
          ⟨u, agree z u bound excluded, wMember⟩

/-- The image store is terminating. -/
theorem Terminating.shuntCells (terminating' : Terminating σ')
    (agree : AgreesOutside σ R σ') :
    Terminating (RegionVariableShunting.shuntCells σ terminating R σ') := by
  refine Subrelation.wf (fun {y x} child => ?_) terminating'.transGen
  obtain ⟨v, bound, member⟩ := child
  obtain ⟨u, original, rfl⟩ := Option.map_eq_some_iff.mp bound
  obtain ⟨w, wMember, occurs⟩ := mem_vars_subst u member
  exact Relation.TransGen.tail' (vars_shuntVar terminating agree w y occurs)
    ⟨u, original, wMember⟩

/-- **The collector preserves every resolution.**  Resolving a shunted term
under the image store is resolving the term under the store. -/
theorem resolve_shuntCells (terminating' : Terminating σ')
    (agree : AgreesOutside σ R σ')
    (image : Terminating (RegionVariableShunting.shuntCells σ terminating R σ'))
    (t : Atom) :
    resolve (RegionVariableShunting.shuntCells σ terminating R σ') image
        (shunt σ terminating R t) =
      resolve σ' terminating' t := by
  have cells : ∀ x, resolve (RegionVariableShunting.shuntCells σ terminating R σ') image
      (shuntVar σ terminating R x) = resolve σ' terminating' (.var x) := by
    intro x
    refine terminating'.induction x (C := fun x =>
      resolve (RegionVariableShunting.shuntCells σ terminating R σ') image
        (shuntVar σ terminating R x) = resolve σ' terminating' (.var x)) ?_
    intro x inductionHypothesis
    have value : ∀ u, σ' x = some u →
        resolve (RegionVariableShunting.shuntCells σ terminating R σ') image
          (shunt σ terminating R u) = resolve σ' terminating' u := by
      intro u bound'
      unfold shunt
      rw [resolve_subst]
      apply SubstitutionAlgebra.subst_congr_on_vars
      intro w member
      rw [inductionHypothesis w ⟨u, bound', member⟩]
      simp [resolve]
    by_cases permanent : ∃ u, σ x = some u ∧ ¬ R x
    · obtain ⟨u, bound, included⟩ := permanent
      have bound' := agree x u bound included
      rw [shuntVar_of_not_mem terminating bound included, value u bound',
        resolve_var_of_some terminating' bound']
    · have kept : shuntVar σ terminating R x = .var x := by
        cases bound : σ x with
        | none => exact shuntVar_of_none terminating bound
        | some u =>
            have excluded : R x := by
              by_contra included
              exact permanent ⟨u, bound, included⟩
            exact shuntVar_of_mem terminating excluded
      rw [kept]
      cases bound' : σ' x with
      | none =>
          have imageUnbound :
              RegionVariableShunting.shuntCells σ terminating R σ' x = none := by
            simp [RegionVariableShunting.shuntCells, bound']
          rw [resolve_var_of_none image imageUnbound,
            resolve_var_of_none terminating' bound']
      | some u =>
          have imageBound : RegionVariableShunting.shuntCells σ terminating R σ' x =
              some (shunt σ terminating R u) := by
            simp [RegionVariableShunting.shuntCells, bound']
          rw [resolve_var_of_some image imageBound, value u bound',
            resolve_var_of_some terminating' bound']
  unfold shunt
  rw [resolve_subst]
  apply SubstitutionAlgebra.subst_congr_on_vars
  intro y _
  rw [cells y]
  simp [resolve]

theorem shuntCells_bind (x : Var) (t : Atom) :
    RegionVariableShunting.shuntCells σ terminating R
        (FreshFrameOccursCheck.bind σ' x t) =
      FreshFrameOccursCheck.bind
        (RegionVariableShunting.shuntCells σ terminating R σ') x
        (shunt σ terminating R t) := by
  funext y
  by_cases same : y = x
  · subst same
    simp [RegionVariableShunting.shuntCells, FreshFrameOccursCheck.bind_self]
  · simp [RegionVariableShunting.shuntCells, FreshFrameOccursCheck.bind_other _ _ same]

theorem shuntCells_unbindAll (cells : List Var) :
    RegionVariableShunting.shuntCells σ terminating R (unbindAll σ' cells) =
      unbindAll (RegionVariableShunting.shuntCells σ terminating R σ') cells := by
  funext y
  unfold RegionVariableShunting.shuntCells unbindAll
  split <;> simp

theorem shuntCells_eq_none_iff (x : Var) :
    RegionVariableShunting.shuntCells σ terminating R σ' x = none ↔ σ' x = none := by
  simp [RegionVariableShunting.shuntCells]

/-- The occurs check gives the same verdict on a shunted term in the image
store as on the term in the store. -/
theorem reaches_shuntCells_iff (terminating' : Terminating σ')
    (agree : AgreesOutside σ R σ') {x : Var} (unbound : σ' x = none) (t : Atom) :
    Reaches (RegionVariableShunting.shuntCells σ terminating R σ')
        (shunt σ terminating R t) x ↔
      Reaches σ' t x := by
  have image := Terminating.shuntCells terminating terminating' agree
  rw [reaches_iff_mem_vars_resolve image ((shuntCells_eq_none_iff terminating x).mpr unbound),
    resolve_shuntCells terminating terminating' agree image,
    ← reaches_iff_mem_vars_resolve terminating' unbound]

end Collector

/-! ## Regions -/

/-- A region: cell bindings, the trail (oldest entry first) and the trail marks
of the live frames (newest first). -/
structure Region where
  cells : Subst
  trail : List Var
  frames : List Nat

namespace Region

/-- The oldest live frame's mark, or the trail's length when no frame is
live: restoring any live frame pops the trail at most down to it. -/
def floor (r : Region) : Nat :=
  r.frames.getLast?.getD r.trail.length

/-- A cell some live frame's restore can unbind. -/
def Revocable (r : Region) (x : Var) : Prop :=
  x ∈ r.trail.drop r.floor

instance (r : Region) : DecidablePred r.Revocable :=
  fun x => inferInstanceAs (Decidable (x ∈ r.trail.drop r.floor))

/-- Frames are ordered and their marks lie within the trail, and following
bindings terminates. -/
structure Valid (r : Region) : Prop where
  terminating : Terminating r.cells
  ordered : r.frames.Pairwise (· ≥ ·)
  bounded : ∀ m ∈ r.frames, m ≤ r.trail.length

/-- One operation of the region. -/
inductive Step : Region → Region → Prop
  /-- Bind an unbound cell to a term that does not reach it; `logged` says
  whether the binding is recorded on the trail. -/
  | bind (r : Region) (x : Var) (t : Atom) (logged : Bool)
      (unbound : r.cells x = none) (occurs : ¬ Reaches r.cells t x) :
      Step r ⟨FreshFrameOccursCheck.bind r.cells x t,
        if logged then r.trail ++ [x] else r.trail, r.frames⟩
  /-- Push a frame at the current trail length. -/
  | push (r : Region) : Step r ⟨r.cells, r.trail, r.trail.length :: r.frames⟩
  /-- Restore the newest frame: unbind the cells named from its mark on. -/
  | restore (r : Region) (m : Nat) (older : List Nat) (top : r.frames = m :: older) :
      Step r ⟨unbindAll r.cells (r.trail.drop m), r.trail.take m, r.frames⟩
  /-- Pop the newest frame. -/
  | pop (r : Region) (m : Nat) (older : List Nat) (top : r.frames = m :: older) :
      Step r ⟨r.cells, r.trail, older⟩

/-- The regions reachable by any sequence of steps. -/
abbrev Reachable (r r' : Region) : Prop :=
  Relation.ReflTransGen Step r r'

theorem floor_le_of_mem {r : Region} (valid : r.Valid) {m : Nat}
    (member : m ∈ r.frames) : r.floor ≤ m := by
  have nonempty : r.frames ≠ [] := List.ne_nil_of_mem member
  have split := List.dropLast_append_getLast nonempty
  unfold floor
  rw [List.getLast?_eq_some_getLast nonempty, Option.getD_some]
  have ordered := valid.ordered
  rw [← split, List.pairwise_append] at ordered
  rw [← split, List.mem_append, List.mem_singleton] at member
  rcases member with early | last
  · exact ordered.2.2 m early _ (List.mem_singleton_self _)
  · exact le_of_eq last.symm

theorem floor_le_length {r : Region} (valid : r.Valid) :
    r.floor ≤ r.trail.length := by
  unfold floor
  cases last : r.frames.getLast? with
  | none => rfl
  | some m => exact valid.bounded m (List.mem_of_getLast? last)

/-- Every step keeps a region valid. -/
theorem Valid.step {r r' : Region} (valid : r.Valid) (step : Step r r') :
    r'.Valid := by
  cases step with
  | bind x t logged unbound occurs =>
      refine ⟨valid.terminating.bind occurs, valid.ordered, fun m member => ?_⟩
      have bounded := valid.bounded m member
      split <;> simp <;> omega
  | push =>
      refine ⟨valid.terminating, ?_, ?_⟩
      · exact List.Pairwise.cons (fun m member => valid.bounded m member) valid.ordered
      · intro m member
        rcases List.mem_cons.mp member with same | older
        · exact le_of_eq same
        · exact valid.bounded m older
  | restore m older top =>
      refine ⟨valid.terminating.unbindAll _, valid.ordered, fun k member => ?_⟩
      have newest : k ≤ m := by
        have ordered := valid.ordered
        rw [top] at ordered member
        rcases List.mem_cons.mp member with same | earlier
        · exact le_of_eq same
        · exact (List.pairwise_cons.mp ordered).1 k earlier
      have bounded := valid.bounded m (by rw [top]; exact List.mem_cons_self)
      rw [List.length_take]
      omega
  | pop m older top =>
      have ordered := valid.ordered
      rw [top] at ordered
      exact ⟨valid.terminating, (List.pairwise_cons.mp ordered).2,
        fun k member => valid.bounded k (by rw [top]; exact List.mem_cons_of_mem _ member)⟩

theorem Valid.reachable {r r' : Region} (valid : r.Valid) (reach : Reachable r r') :
    r'.Valid := by
  induction reach with
  | refl => exact valid
  | tail _ step inductionHypothesis => exact inductionHypothesis.step step

/-- A bound cell no live frame can unbind. -/
def Permanent (r : Region) (x : Var) : Prop :=
  (∃ u, r.cells x = some u) ∧ ¬ r.Revocable x

/-- What a region keeps of its origin: frames at or above the origin's floor, a
trail that reaches it, no trail entry from it on that names a permanent cell of
the origin, and every such cell bound as it was. -/
structure Keeps (origin r : Region) : Prop where
  frames_above : ∀ m ∈ r.frames, origin.floor ≤ m
  floor_le : origin.floor ≤ r.trail.length
  suffix_clear : ∀ x ∈ r.trail.drop origin.floor, ¬ origin.Permanent x
  permanent_fixed : ∀ x, origin.Permanent x → r.cells x = origin.cells x

theorem keeps_self {origin : Region} (valid : origin.Valid) : Keeps origin origin where
  frames_above _ member := floor_le_of_mem valid member
  floor_le := floor_le_length valid
  suffix_clear _ member permanent := permanent.2 member
  permanent_fixed _ _ := rfl

theorem mem_drop_of_le {l : List Var} {x : Var} {low high : Nat} (le : low ≤ high)
    (member : x ∈ l.drop high) : x ∈ l.drop low := by
  have split : l.drop high = (l.drop low).drop (high - low) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [split] at member
  exact List.mem_of_mem_drop member

theorem Keeps.step {origin r r' : Region} (keeps : Keeps origin r) (step : Step r r') :
    Keeps origin r' := by
  cases step with
  | bind x t logged unbound occurs =>
      have fresh : ¬ origin.Permanent x := by
        intro permanent
        obtain ⟨u, bound⟩ := permanent.1
        rw [← keeps.permanent_fixed x permanent, unbound] at bound
        cases bound
      refine ⟨keeps.frames_above, ?_, ?_, ?_⟩
      · split <;> simp <;> have := keeps.floor_le <;> omega
      · intro y member
        split at member
        · rw [List.drop_append, List.mem_append] at member
          rcases member with old | new
          · exact keeps.suffix_clear y old
          · have same : y = x := List.mem_singleton.mp (List.mem_of_mem_drop new)
            exact same ▸ fresh
        · exact keeps.suffix_clear y member
      · intro y permanent
        have distinct : y ≠ x := fun same => fresh (same ▸ permanent)
        change FreshFrameOccursCheck.bind r.cells x t y = origin.cells y
        rw [FreshFrameOccursCheck.bind_other r.cells t distinct]
        exact keeps.permanent_fixed y permanent
  | push =>
      refine ⟨fun m member => ?_, keeps.floor_le, keeps.suffix_clear,
        keeps.permanent_fixed⟩
      rcases List.mem_cons.mp member with same | older
      · rw [same]; exact keeps.floor_le
      · exact keeps.frames_above m older
  | restore m older top =>
      have above : origin.floor ≤ m := keeps.frames_above m (by rw [top]; exact List.mem_cons_self)
      refine ⟨keeps.frames_above, ?_, ?_, ?_⟩
      · rw [List.length_take]
        have := keeps.floor_le
        omega
      · intro y member
        rw [List.drop_take] at member
        exact keeps.suffix_clear y (List.take_subset _ _ member)
      · intro y permanent
        change unbindAll r.cells (r.trail.drop m) y = origin.cells y
        unfold unbindAll
        rw [if_neg (fun member => keeps.suffix_clear y (mem_drop_of_le above member) permanent)]
        exact keeps.permanent_fixed y permanent
  | pop m older top =>
      exact ⟨fun k member => keeps.frames_above k (by rw [top]; exact List.mem_cons_of_mem _ member),
        keeps.floor_le, keeps.suffix_clear, keeps.permanent_fixed⟩

/-- **Permanent bindings are permanent.**  Along any sequence of steps from a
valid region, a bound cell the origin's live frames cannot unbind keeps its
binding. -/
theorem Reachable.permanent_fixed {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) {x : Var} (permanent : origin.Permanent x) :
    r.cells x = origin.cells x := by
  have keeps : Keeps origin r := by
    induction reach with
    | refl => exact keeps_self valid
    | tail _ step inductionHypothesis => exact inductionHypothesis.step step
  exact keeps.permanent_fixed x permanent

/-- The bindings shunting follows are kept by every reachable region. -/
theorem Reachable.agreesOutside {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) :
    AgreesOutside origin.cells origin.Revocable r.cells := by
  intro x u bound revocable
  rw [Reachable.permanent_fixed valid reach ⟨⟨u, bound⟩, revocable⟩]
  exact bound

/-- **Shunting commutes with resolution in every reachable future.**  Shunt a
term at a valid region; after any sequence of bindings, pushes, restores of
live frames and pops, the shunted term resolves exactly as the term does. -/
theorem shunt_resolve {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) (terminating : Terminating r.cells) (t : Atom) :
    resolve r.cells terminating
        (shunt origin.cells valid.terminating origin.Revocable t) =
      resolve r.cells terminating t :=
  resolve_shunt_of_agree valid.terminating terminating
    (Reachable.agreesOutside valid reach) t

/-- Terms with the same shunting at the origin resolve alike in every
reachable region: the license for a partial shunting, which replaces some
occurrences of non-revocable bound cells by their values. -/
theorem resolve_eq_of_shunt_eq {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) (terminating : Terminating r.cells) {t t' : Atom}
    (same : shunt origin.cells valid.terminating origin.Revocable t =
      shunt origin.cells valid.terminating origin.Revocable t') :
    resolve r.cells terminating t = resolve r.cells terminating t' :=
  RegionVariableShunting.resolve_eq_of_shunt_eq valid.terminating terminating
    (Reachable.agreesOutside valid reach) same

/-- The same statement with the reachable region's own termination proof. -/
theorem shunt_resolve_reachable {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) (t : Atom) :
    resolve r.cells (valid.reachable reach).terminating
        (shunt origin.cells valid.terminating origin.Revocable t) =
      resolve r.cells (valid.reachable reach).terminating t :=
  shunt_resolve valid reach _ t

/-! ### The collector's image of a region -/

/-- The collector's image of a region, with every binding's value shunted as
at the origin, where the collection ran. -/
def collected {origin : Region} (valid : origin.Valid) (r : Region) : Region :=
  ⟨shuntCells origin.cells valid.terminating origin.Revocable r.cells, r.trail, r.frames⟩

theorem collected_terminating {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) : Terminating (collected valid r).cells :=
  Terminating.shuntCells valid.terminating (valid.reachable reach).terminating
    (Reachable.agreesOutside valid reach)

/-- **The collected region keeps every meaning.**  In every region reachable
from the origin, the image store resolves each shunted term as the region
resolves the term. -/
theorem resolve_collected {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) (image : Terminating (collected valid r).cells)
    (t : Atom) :
    resolve (collected valid r).cells image
        (shunt origin.cells valid.terminating origin.Revocable t) =
      resolve r.cells (valid.reachable reach).terminating t :=
  resolve_shuntCells valid.terminating (valid.reachable reach).terminating
    (Reachable.agreesOutside valid reach) image t

/-- **The collected region follows every future.**  Each step of a region
reachable from the origin is matched by a step of its image, binding the
shunted term, with the same unboundness and occurs-check verdicts. -/
theorem collected_step {origin r r' : Region} (valid : origin.Valid)
    (reach : Reachable origin r) (step : Step r r') :
    Step (collected valid r) (collected valid r') := by
  have agree := Reachable.agreesOutside valid reach
  have terminating := (valid.reachable reach).terminating
  cases step with
  | bind x t logged unbound occurs =>
      unfold collected
      rw [shuntCells_bind]
      exact Step.bind _ x _ logged
        ((shuntCells_eq_none_iff valid.terminating x).mpr unbound)
        (fun reaches => occurs
          ((reaches_shuntCells_iff valid.terminating terminating agree unbound t).mp
            reaches))
  | push => exact Step.push _
  | restore m older top =>
      unfold collected
      rw [shuntCells_unbindAll]
      exact Step.restore _ m older top
  | pop m older top => exact Step.pop _ m older top

theorem collected_reachable {origin r : Region} (valid : origin.Valid)
    (reach : Reachable origin r) :
    Reachable (collected valid origin) (collected valid r) := by
  induction reach with
  | refl => exact .refl
  | @tail middle last reach step inductionHypothesis =>
      exact inductionHypothesis.tail (collected_step valid reach step)

end Region

/-! ## Positive and negative witnesses -/

namespace Canary

open Region

/-- A store with no binding that mentions a cell terminates. -/
theorem terminating_of_no_child {σ : Subst} (none_child : ∀ y x, ¬ Child σ y x) :
    Terminating σ :=
  ⟨fun x => Acc.intro x fun y child => (none_child y x child).elim⟩

/-- `x` bound to the symbol `a`. -/
def boundX : Subst := FreshFrameOccursCheck.bind (fun _ => none) "x" (.symbol "a")

theorem boundX_terminating : Terminating boundX :=
  terminating_of_no_child fun y x ⟨u, bound, member⟩ => by
    unfold boundX at bound
    by_cases same : x = "x"
    · subst same
      rw [FreshFrameOccursCheck.bind_self] at bound
      cases bound
      simp [vars] at member
    · rw [FreshFrameOccursCheck.bind_other _ _ same] at bound
      cases bound

theorem unbound_terminating (cells : List Var) :
    Terminating (unbindAll boundX cells) :=
  boundX_terminating.unbindAll cells

theorem resolve_boundX_x :
    resolve boundX boundX_terminating (.var "x") = .symbol "a" := by
  rw [resolve_var_of_some boundX_terminating (FreshFrameOccursCheck.bind_self _ _ _)]
  simp [resolve, shunt, subst]

/-- A frame pushed before `x` was bound: the binding is revocable. -/
def revocableRegion : Region := ⟨boundX, ["x"], [0]⟩

/-- That frame, restored. -/
def restoredRegion : Region := ⟨unbindAll boundX ["x"], [], [0]⟩

theorem revocableRegion_valid : revocableRegion.Valid :=
  ⟨boundX_terminating, by decide, by decide⟩

theorem restoredRegion_terminating : Terminating restoredRegion.cells :=
  unbound_terminating ["x"]

theorem revocable_restored : Reachable revocableRegion restoredRegion :=
  .single (Step.restore revocableRegion 0 [] rfl)

/-- Negative: treating the revocable `x` as permanent replaces it by `a`, but
once the frame is restored `x` is unbound again, and the two terms resolve
differently. -/
theorem shunting_revocable_is_unsound :
    revocableRegion.Revocable "x" ∧
      resolve restoredRegion.cells restoredRegion_terminating
          (shunt revocableRegion.cells revocableRegion_valid.terminating
            (fun _ => False) (.var "x")) ≠
        resolve restoredRegion.cells restoredRegion_terminating (.var "x") := by
  have unbound : restoredRegion.cells "x" = none := by
    simp [restoredRegion, unbindAll]
  refine ⟨by decide, ?_⟩
  change resolve restoredRegion.cells restoredRegion_terminating
      (resolve boundX boundX_terminating (.var "x")) ≠ _
  rw [resolve_boundX_x, resolve_var_of_none restoredRegion_terminating unbound]
  simp [resolve, shunt, subst]

/-- The correct revocability keeps `x`: the theorem's shunting is the identity
on it. -/
example :
    shunt revocableRegion.cells revocableRegion_valid.terminating
        revocableRegion.Revocable (.var "x") = .var "x" := by
  rw [shunt_var, shuntVar_of_mem _ (by decide)]

/-- `x` bound before the only frame was pushed. -/
def permanentRegion : Region := ⟨boundX, ["x"], [1]⟩

theorem permanentRegion_valid : permanentRegion.Valid :=
  ⟨boundX_terminating, by decide, by decide⟩

/-- Positive: the binding lies below the oldest mark, so it is shunted, and
restoring the frame keeps it: the shunted term still resolves as the term. -/
theorem binding_below_oldest_mark_survives :
    ¬ permanentRegion.Revocable "x" ∧
      shunt permanentRegion.cells permanentRegion_valid.terminating
          permanentRegion.Revocable (.var "x") = .symbol "a" ∧
      Reachable permanentRegion ⟨unbindAll boundX [], ["x"], [1]⟩ := by
  refine ⟨by decide, ?_, .single (Step.restore permanentRegion 1 [] rfl)⟩
  have bound : permanentRegion.cells "x" = some (.symbol "a") :=
    FreshFrameOccursCheck.bind_self (fun _ => none) "x" (.symbol "a")
  rw [shunt_var, shuntVar_of_not_mem _ bound (by decide)]
  simp [shunt, subst]

/-- With no live frame nothing is revocable. -/
example : ¬ (⟨boundX, ["x"], []⟩ : Region).Revocable "x" := by
  decide

/-- Revocability judged from the newest frame's mark. -/
def NewestRevocable (r : Region) (x : Var) : Prop :=
  x ∈ r.trail.drop (r.frames.headD r.trail.length)

instance (r : Region) : DecidablePred (NewestRevocable r) :=
  fun x => inferInstanceAs (Decidable (x ∈ r.trail.drop _))

/-- Two frames: the oldest pushed before `x` was bound, the newest after. -/
def twoFrameRegion : Region := ⟨boundX, ["x"], [1, 0]⟩

theorem twoFrameRegion_valid : twoFrameRegion.Valid :=
  ⟨boundX_terminating, by decide, by decide⟩

/-- Pop the newest frame, then restore the oldest. -/
theorem twoFrame_restored : Reachable twoFrameRegion restoredRegion :=
  (Relation.ReflTransGen.single (Step.pop twoFrameRegion 1 [0] rfl)).tail
    (Step.restore ⟨boundX, ["x"], [0]⟩ 0 [] rfl)

/-- Negative: judged from the newest mark `x` is not revocable and would be
shunted, yet popping the newest frame and restoring the oldest unbinds it. -/
theorem newest_mark_is_unsound :
    ¬ NewestRevocable twoFrameRegion "x" ∧ twoFrameRegion.Revocable "x" ∧
      resolve restoredRegion.cells restoredRegion_terminating
          (shunt twoFrameRegion.cells twoFrameRegion_valid.terminating
            (NewestRevocable twoFrameRegion) (.var "x")) ≠
        resolve restoredRegion.cells restoredRegion_terminating (.var "x") := by
  have unbound : restoredRegion.cells "x" = none := by
    simp [restoredRegion, unbindAll]
  refine ⟨by decide, by decide, ?_⟩
  have bound : twoFrameRegion.cells "x" = some (.symbol "a") :=
    FreshFrameOccursCheck.bind_self (fun _ => none) "x" (.symbol "a")
  rw [shunt_var, shuntVar_of_not_mem _ bound (by decide),
    resolve_var_of_none restoredRegion_terminating unbound]
  simp [resolve, shunt, subst]

/-- `x` bound to `(h x)`, which the occurs check rejects. -/
def cyclic : Subst :=
  FreshFrameOccursCheck.bind (fun _ => none) "x" (.expression [.symbol "h", .var "x"])

/-- Negative: without the occurs check the binding chain from `x` does not
terminate. -/
theorem unchecked_binding_does_not_terminate :
    Reaches (fun _ => none) (.expression [.symbol "h", .var "x"]) "x" ∧
      ¬ Terminating cyclic := by
  refine ⟨.here (by decide), fun terminating => ?_⟩
  have loop : Child cyclic "x" "x" :=
    ⟨_, FreshFrameOccursCheck.bind_self _ _ _, by decide⟩
  exact terminating.asymmetric _ _ loop loop

/-- Every cell bound to a longer cell: no cycle, but an infinite chain. -/
def primed : Subst := fun x => some (.var (x ++ "'"))

theorem primed_reaches_longer {n : Nat} {t : Atom} {y : Var} (reach : Reaches primed t y) :
    (∀ z ∈ vars t, n < z.length) → n < y.length := by
  induction reach with
  | here member => exact fun longer => longer _ member
  | @through t u z y member bound _ inductionHypothesis =>
      intro longer
      apply inductionHypothesis
      intro w occurs
      simp only [primed, Option.some.injEq] at bound
      subst bound
      have same : w = z ++ "'" := by simpa [vars] using occurs
      subst same
      have := longer z member
      simp
      omega

/-- Negative: finiteness is needed for `Terminating.of_acyclic`.  `primed` is
acyclic, since a chain only lengthens cells, yet following bindings never
terminates. -/
theorem acyclic_infinite_store_does_not_terminate :
    Acyclic primed ∧ ¬ Terminating primed := by
  refine ⟨fun x u bound reach => ?_, fun terminating => ?_⟩
  · simp only [primed, Option.some.injEq] at bound
    subst bound
    have := primed_reaches_longer (n := x.length) reach (fun z member => by
      have same : z = x ++ "'" := by simpa [vars] using member
      subst same
      simp only [String.length_append, Nat.lt_add_right_iff_pos]
      decide)
    omega
  · exact (terminating.apply "").rec fun x _ inductionHypothesis =>
      inductionHypothesis (x ++ "'") ⟨_, rfl, by simp [vars]⟩

end Canary

end Mettapedia.GSLT.LanguageDef.RegionVariableShunting
