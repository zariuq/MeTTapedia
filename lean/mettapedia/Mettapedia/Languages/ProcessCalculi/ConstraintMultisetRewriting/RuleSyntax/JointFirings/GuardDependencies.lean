import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Members
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Maximal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Guard dependencies from matching alone

A rule reads `true` at its own cell and asks whether a second cell is
`true`. The read contributes the first equation to the shared model.
An accepted bag must include every successor of an included rule.
Conversely every successor-closed set can be realized by a bag.

All rules have two read ports and one guard. The result uses the actual
bag admission relation, including freshness and its universal ask.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.GuardDependencies

open Mettapedia.Logic.LP
open Interface (Frames)
open OneFrame (Terms frames ext)
open MeTTaCalculus.OccurrenceCommits (Enabled)

variable {I : Type}

/-- Incoming variables and rule-local variables occupy separate slots. -/
abbrev Signature (I : Type) : LPSignature where
  vars := I ⊕ I
  constants := Bool
  functionSymbols := Empty
  functionArity := Empty.elim
  relationSymbols := Empty
  relationArity := Empty.elim

abbrev Value (I : Type) := I × Term (Signature I)
abbrev Assignment (I : Type) := Subst (Signature I)

abbrev action (I : Type) : SubstitutionAction (Value I) (Assignment I) :=
  LocatedSubstitution.action (FirstOrder.action (Signature I))

abbrev X (I : Type) := frames (action I)
abbrev E (I : Type) := ext (action I)

def cell (i : I) : Value I := (i, .var (.inl i))
def trueAt (i : I) : Value I := (i, .const true)
def readAt (dependency : I → I) (i : I) : Value I := (dependency i, .var (.inr i))

def rule (dependency : I → I) (i : I) : Rule (Terms (Value I)) :=
  ⟨PUnit.unit, ⟨[], [trueAt i, readAt dependency i], [],
    [.equal (readAt dependency i) (trueAt (dependency i))], []⟩, []⟩

def program (dependency : I → I) : Program (Terms (Value I)) := Set.range (rule dependency)

def world [Fintype I] : State (Terms (Value I)) I := ⟨PUnit.unit, [], Finset.univ, cell⟩

abbrev Batch (dependency : I → I) := Bag I (E I) (program dependency) PUnit.unit

private def member (dependency : I → I) (i : I) :
    Member I (E I) (program dependency) (a := PUnit.unit) PUnit.unit :=
  ⟨rule dependency i, ⟨i, rfl⟩, Subst.id (Signature I), ⟨[], [i, dependency i], []⟩, []⟩

private def bag (dependency : I → I) (indices : List I) : Batch dependency :=
  ⟨PUnit.unit, indices.map (member dependency)⟩

private theorem agrees_on_rule (dependency : I → I) (i : I) (u h : Assignment I)
    (same : u (.inr i) = h (.inr i)) :
    ∀ t ∈ (rule dependency i).terms, (action I).E ((action I).apply u t) ((action I).apply h t) := by
  intro t ht
  have terms : t = trueAt i ∨ t = readAt dependency i ∨ t = trueAt (dependency i) := by
    simpa [rule, Rule.terms, checkTerms, or_assoc] using ht
  rcases terms with rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, same⟩
  · exact ⟨rfl, rfl⟩

variable [DecidableEq I]

private theorem realized (dependency : I → I) (indices : List I) (distinct : indices.Nodup)
    (g : Assignment I) (defaults : I → Term (Signature I)) :
    Realized (X I) PUnit.unit (indices.map (member dependency)) (fun u =>
      (∀ i, u (.inl i) = g (.inl i)) ∧ ∀ i ∉ indices, u (.inr i) = defaults i) := by
  induction indices generalizing defaults with
  | nil =>
    exact ⟨Sum.elim (fun i => g (.inl i)) defaults, fun _ => rfl, fun _ _ => rfl⟩
  | cons i rest ih =>
    have split := List.nodup_cons.mp distinct
    intro requested
    have later := ih split.2 (Function.update defaults i (requested (.inr i)))
    refine Realized.mono (X I) (rest.map (member dependency)) (fun u ⟨entry, localValues⟩ => ?_) later
    refine ⟨⟨entry, ?_⟩, ?_⟩
    · intro other outside
      have apart : other ≠ i := fun same => outside (same ▸ List.mem_cons_self)
      have inRest : other ∉ rest := fun inside => outside (List.mem_cons_of_mem _ inside)
      simpa only [Function.update_of_ne apart] using localValues other inRest
    · intro value mentioned
      have agree : u (.inr i) = requested (.inr i) := by
        simpa only [Function.update_self] using localValues i split.1
      change (action I).E ((action I).apply u ((action I).apply (Subst.id (Signature I)) value))
        ((action I).apply requested value)
      change (action I).E ((action I).apply u ((action I).apply (action I).identity value))
        ((action I).apply requested value)
      rw [(action I).apply_identity]
      exact agrees_on_rule dependency i u requested agree value mentioned

variable [Fintype I]

private theorem fresh (dependency : I → I) (indices : List I) (distinct : indices.Nodup) :
    (bag dependency indices).Fresh (X I) world := by
  intro b g
  cases b
  have alone := realized dependency indices distinct g (fun i => g (.inr i))
  refine Realized.mono (X I) _ (fun u stable => ?_) alone
  intro term mentioned
  obtain ⟨i, _, rfl⟩ : ∃ i ∈ (Finset.univ : Finset I), cell i = term := by
    simpa [world, State.Mentions] using mentioned
  change (action I).E ((action I).apply u ((action I).apply (action I).identity (cell i)))
    ((action I).apply g (cell i))
  rw [(action I).apply_identity]
  exact ⟨rfl, stable.1 i⟩

private theorem fit (dependency : I → I) (indices : List I) (distinct : indices.Nodup) :
    (bag dependency indices).Fits (X I) world := by
  have noTaken : (bag dependency indices).selection.taken = [] := by
    simp [bag, Bag.selection, member, List.flatMap_map]
  have noMade : (bag dependency indices).selection.made = [] := by
    simp [bag, Bag.selection, member, List.flatMap_map]
  refine ⟨fresh dependency indices distinct, by rw [noTaken]; simp,
    by rw [noMade]; simp, ?_⟩
  intro m hm
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem enabled (dependency : I → I) (indices : List I) :
    Enabled (fun _ : I => ()) world.present ((bag dependency indices).selection.commit (T := Unit)) := by
  have commit : (bag dependency indices).selection.commit (T := Unit) =
      ⟨∅, (((indices.map fun i => [i, dependency i]).flatten).toFinset), ∅, []⟩ := by
    simp [bag, Bag.selection, member, Selection.commit, List.flatMap, Function.comp_def]
  rw [commit]
  exact ⟨by simp, Finset.subset_univ _, by simp, by simp, fun _ h => (List.not_mem_nil h).elim⟩

section ArbitraryBags

variable {dependency : I → I} (f : Batch dependency)

noncomputable def index (m : Member I (E I) (program dependency) f.ext) : I :=
  Classical.choose m.member

omit [Fintype I] [DecidableEq I] in
theorem rule_index (m : Member I (E I) (program dependency) f.ext) :
    m.rule = rule dependency (index f m) :=
  (Classical.choose_spec m.member).symm

/-- Which cell assertions the selected members contribute. -/
noncomputable def support : Finset I := (f.members.map (index f)).toFinset

omit [Fintype I] in
theorem mem_support {i : I} :
    i ∈ support f ↔ ∃ m ∈ f.members, index f m = i := by
  rw [support, List.mem_toFinset, List.mem_map]

omit [Fintype I] [DecidableEq I] in
private theorem opened_reads (m : Member I (E I) (program dependency) f.ext) :
    (m.firing.opened (X I)).read =
      [trueAt (index f m), (dependency (index f m), m.opening (.inr (index f m)))] := by
  change m.rule.body.read.map ((action I).apply m.opening) = _
  rw [rule_index f m]
  rfl

omit [Fintype I] [DecidableEq I] in
private theorem no_tells (m : Member I (E I) (program dependency) f.ext) :
    (m.firing.opened (X I)).tell = [] := by
  change m.rule.body.tell.map _ = _
  rw [rule_index f m]
  rfl

omit [Fintype I] [DecidableEq I] in
private theorem no_takes (m : Member I (E I) (program dependency) f.ext) :
    (m.firing.opened (X I)).take = [] := by
  change m.rule.body.take.map _ = _
  rw [rule_index f m]
  rfl

omit [DecidableEq I] in
/-- Matching under the rigid cell tags fixes the selected read identities. -/
private theorem reads_of_model (shapes : f.Fits (X I) world)
    {σ : Assignment I} (model : (X I).Models (b := PUnit.unit) σ (f.information (X I) world))
    {m : Member I (E I) (program dependency) f.ext} (inside : m ∈ f.members) :
    m.selection.read = [index f m, dependency (index f m)] := by
  have readLength := (shapes.2.2.2 m inside).2.1
  rw [rule_index f m] at readLength
  obtain ⟨left, right, ports⟩ := List.length_eq_two.mp readLength.symm
  have memberModel := Bag.models_member (X I) inside model
  have matchedLeft := Firing.read_solved (X := X I) (s := world) m.firing memberModel
    (p := trueAt (index f m)) (o := left) (by
      rw [opened_reads f m]
      change (trueAt (index f m), left) ∈
        [trueAt (index f m), (dependency (index f m), m.opening (.inr (index f m)))].zip m.selection.read
      rw [ports]
      exact List.mem_cons_self)
  have matchedRight := Firing.read_solved (X := X I) (s := world) m.firing memberModel
    (p := (dependency (index f m), m.opening (.inr (index f m)))) (o := right) (by
      rw [opened_reads f m]
      change ((dependency (index f m), m.opening (.inr (index f m))), right) ∈
        [trueAt (index f m), (dependency (index f m), m.opening (.inr (index f m)))].zip m.selection.read
      rw [ports]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
  have leftId : index f m = left := matchedLeft.1
  have rightId : dependency (index f m) = right := matchedRight.1
  rw [ports, ← leftId, rightId]

omit [DecidableEq I] in
private theorem matching_equations (m : Member I (E I) (program dependency) f.ext)
    (ports : m.selection.read = [index f m, dependency (index f m)]) :
    m.own (X I) world =
      [(trueAt (index f m), cell (index f m)),
        ((dependency (index f m), m.opening (.inr (index f m))), cell (dependency (index f m)))] := by
  unfold Member.own
  rw [no_takes f m, opened_reads f m, no_tells f m]
  change m.firing.matching (X I) world [] m.selection.taken ++
    m.firing.matching (X I) world _ m.selection.read ++ [] = _
  rw [ports]
  rfl

omit [DecidableEq I] in
private theorem models_iff
    (ports : ∀ m ∈ f.members, m.selection.read = [index f m, dependency (index f m)])
    (u : Assignment I) :
    (X I).Models (b := PUnit.unit) u (f.information (X I) world) ↔
      ∀ m ∈ f.members, u (.inl (index f m)) = .const true ∧
        u.applyTerm (m.opening (.inr (index f m))) = u (.inl (dependency (index f m))) := by
  change (∀ e ∈ f.members.flatMap (fun m => m.own (X I) world),
    (action I).Solves u e) ↔ _
  constructor
  · intro solved m inside
    have equation : ∀ e ∈ m.own (X I) world, (action I).Solves u e :=
      fun e he => solved e (List.mem_flatMap.mpr ⟨m, inside, he⟩)
    rw [matching_equations f m (ports m inside)] at equation
    exact ⟨(equation _ List.mem_cons_self).2.symm,
      (equation _ (List.mem_cons_of_mem _ List.mem_cons_self)).2⟩
  · intro data e member
    obtain ⟨m, inside, held⟩ := List.mem_flatMap.mp member
    rw [matching_equations f m (ports m inside)] at held
    obtain ⟨fixed, seen⟩ := data m inside
    rcases List.mem_cons.mp held with rfl | later
    · exact ⟨rfl, fixed.symm⟩
    · obtain rfl := List.mem_singleton.mp later
      exact ⟨rfl, seen⟩

omit [DecidableEq I] in
private theorem member_guard_iff (m : Member I (E I) (program dependency) f.ext)
    (u : Assignment I) :
    m.firing.Holds (X I) world (b := PUnit.unit) u ↔
      u.applyTerm (m.opening (.inr (index f m))) = .const true := by
  have check : (m.firing.opened (X I)).checks =
      [.equal (dependency (index f m), m.opening (.inr (index f m)))
        (trueAt (dependency (index f m)))] := by
    change m.rule.body.checks.map (Check.map ((action I).apply m.opening)) = _
    rw [rule_index f m]
    rfl
  have collected : m.firing.collectOpened (X I) = [] := by
    change m.rule.collect.map _ = _
    rw [rule_index f m]
    rfl
  unfold Firing.Holds
  simp [check, collected]
  show (_ ∧ u.applyTerm (m.opening (.inr (index f m))) = .const true) ↔ _
  exact ⟨And.right, fun eq => ⟨rfl, eq⟩⟩

/-- The projection of the joint models to the incoming variables is exact.
Matching fixes precisely the asserted cells, while the other cells may be
assigned arbitrarily. Joint freshness provides every such extension. -/
theorem project_models (freshness : f.Fresh (X I) world)
    (ports : ∀ m ∈ f.members, m.selection.read = [index f m, dependency (index f m)])
    (values : I → Term (Signature I)) :
    (∃ u : Assignment I, (X I).Models (b := PUnit.unit) u (f.information (X I) world) ∧
      ∀ i, u (.inl i) = values i) ↔
      ∀ i ∈ support f, values i = .const true := by
  constructor
  · rintro ⟨u, solved, projected⟩ i selected
    obtain ⟨m, hm, rfl⟩ := (mem_support f).mp selected
    exact (projected _).symm.trans ((models_iff f ports u).mp solved m hm).1
  · intro prescribed
    let incoming : Assignment I := Sum.elim values (fun i => .var (.inr i))
    let requested : Member I (E I) (program dependency) f.ext → Assignment I :=
      fun m _ => values (dependency (index f m))
    obtain ⟨u, onState, onRules⟩ := Realized.pick (X I) requested f.members (freshness PUnit.unit incoming)
    have projected (i : I) : u (.inl i) = values i := by
      have here : (world (I := I)).Mentions (cell i) := .inr (.inr ⟨i, Finset.mem_univ _, rfl⟩)
      exact (onState (cell i) here).2
    refine ⟨u, (models_iff f ports u).mpr ?_, projected⟩
    intro m hm
    have term : readAt dependency (index f m) ∈ m.rule.terms := by
      rw [rule_index f m]
      simp [rule, Rule.terms]
    have localValue : u.applyTerm (m.opening (.inr (index f m))) = values (dependency (index f m)) :=
      (onRules m hm _ term).2
    exact ⟨(projected _).trans (prescribed _ ((mem_support f).mpr ⟨m, hm, rfl⟩)),
      localValue.trans (projected _).symm⟩

/-- With two reads and one guard per rule, the admitted populations are
exactly the successor-closed sets, subject to ordinary matching shape and
joint freshness. This holds with asks before tells. -/
theorem admits_iff_closed :
    f.AdmitsBeforeTells (X I) world ↔
      f.Fits (X I) world ∧
      Enabled (fun _ : I => ()) world.present (f.selection.commit (T := Unit)) ∧
      (∀ m ∈ f.members, m.selection.read = [index f m, dependency (index f m)]) ∧
      ∀ i ∈ support f, dependency i ∈ support f := by
  have timing := Bag.beforeTells_iff_of_no_tells (X I) world f (fun m _ => no_tells f m)
  rw [timing]
  constructor
  · intro admitted
    obtain ⟨b, σ, solved⟩ := admitted.2.2.1
    cases b
    have ports (m : Member I (E I) (program dependency) f.ext) (h : m ∈ f.members) :
        m.selection.read = [index f m, dependency (index f m)] :=
      reads_of_model f admitted.1 solved h
    let values (i : I) : Term (Signature I) :=
      .const (decide (i ∈ support f))
    obtain ⟨u, model, projected⟩ := (project_models f admitted.1.1 ports values).mpr
      fun i inside => by simp [values, inside]
    refine ⟨admitted.1, admitted.2.1, ports, fun i chosen => ?_⟩
    obtain ⟨m, hm, rfl⟩ := (mem_support f).mp chosen
    have asked := (member_guard_iff f m u).mp (admitted.2.2.2 PUnit.unit u model m hm)
    have fromRead := ((models_iff f ports u).mp model m hm).2
    have cellTrue := (projected (dependency (index f m))).symm.trans (fromRead.symm.trans asked)
    have vote := Term.const.inj cellTrue
    exact of_decide_eq_true vote
  · rintro ⟨shapes, available, ports, closed⟩
    obtain ⟨u, solved, _⟩ := (project_models f shapes.1 ports (fun _ => .const true)).mpr
      (fun _ _ => rfl)
    refine ⟨shapes, available, ⟨PUnit.unit, u, solved⟩, ?_⟩
    intro b σ model m hm
    cases b
    have values := (models_iff f ports σ).mp model
    obtain ⟨other, ho, atCell⟩ := (mem_support f).mp (closed _ ((mem_support f).mpr ⟨m, hm, rfl⟩))
    have trueAtOther := (values other ho).1
    rw [atCell] at trueAtOther
    exact (member_guard_iff f m σ).mpr ((values m hm).2.trans trueAtOther)

/-- The two ask timings agree on this family because every contribution is
a matching equation. -/
theorem admitsBeforeTells_iff_admits :
    f.AdmitsBeforeTells (X I) world ↔ f.Admits (X I) world :=
  Bag.beforeTells_iff_of_no_tells (X I) world f (fun m _ => no_tells f m)

end ArbitraryBags

section Populations

variable (dependency : I → I)

omit [Fintype I] [DecidableEq I] in
private theorem rule_injective : Function.Injective (rule dependency) := by
  intro i j same
  let firstSite (r : Rule (Terms (Value I))) : Option I :=
    r.body.read.head?.map Prod.fst
  have found : some i = some j := congrArg firstSite same
  exact Option.some.inj found

omit [Fintype I] [DecidableEq I] in
private theorem index_of_member (indices : List I) (i : I) :
    index (bag dependency indices) (member dependency i) = i :=
  rule_injective dependency (rule_index (bag dependency indices) (member dependency i)).symm

omit [Fintype I] in
private theorem support_bag (indices : List I) :
    support (bag dependency indices) = indices.toFinset := by
  ext i
  rw [mem_support, List.mem_toFinset]
  constructor
  · rintro ⟨m, active, rfl⟩
    obtain ⟨source, picked, rfl⟩ := List.mem_map.mp active
    rwa [index_of_member]
  · intro chosen
    exact ⟨member dependency i, List.mem_map_of_mem chosen, index_of_member dependency indices i⟩

/-- The scope of admitted members ranges over exactly the successor-closed
populations. Every such population has a realization with one member per
asserted cell. -/
theorem populations_iff (selected : Finset I) :
    (∃ f : Batch dependency, f.AdmitsBeforeTells (X I) world ∧
      support f = selected ∧ f.members.length = selected.card) ↔
      ∀ i ∈ selected, dependency i ∈ selected := by
  constructor
  · rintro ⟨f, admitted, rfl, _⟩
    exact ((admits_iff_closed f).mp admitted).2.2.2
  · intro closed
    let f := bag dependency selected.toList
    have selectedExactly : support f = selected :=
      (support_bag dependency selected.toList).trans (Finset.toList_toFinset _)
    refine ⟨f, (admits_iff_closed f).mpr ⟨fit dependency _ (Finset.nodup_toList _),
      enabled dependency _, ?_, ?_⟩, selectedExactly, ?_⟩
    · intro m inside
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp inside
      change [i, dependency i] = [index f (member dependency i), dependency (index f (member dependency i))]
      rw [index_of_member dependency selected.toList i]
    · simpa only [selectedExactly] using closed
    · change (selected.toList.map (member dependency)).length = selected.card
      rw [List.length_map, Finset.length_toList]

end Populations

section Cycles

/-- Every vertex of a rotation is reached from each starting vertex. -/
private theorem closed_rotation_eq_univ {n : Nat} [NeZero n] {selected : Finset (Fin n)}
    (nonempty : selected.Nonempty)
    (closed : ∀ i ∈ selected, finRotate n i ∈ selected) : selected = Finset.univ := by
  obtain ⟨start, started⟩ := nonempty
  have walk (length : Nat) : ((finRotate n)^[length]) start ∈ selected := by
    induction length with
    | zero => exact started
    | succ length prior =>
      rw [Function.iterate_succ_apply']
      exact closed _ prior
  apply Finset.eq_univ_of_forall
  intro target
  have walked := walk (target - start).val
  have reach := congrFun (finCycle_eq_finRotate_iterate (k := target - start)) start
  rw [← reach] at walked
  change start + (target - start) ∈ selected at walked
  rwa [add_comm start, sub_add_cancel] at walked

/-- Every nonempty firing on a cycle needs at least its full population.
The bound covers arbitrary openings and every legal selection in the
program, including when guards are asked before tells. -/
theorem rotation_lower_bound (n : Nat) [NeZero n] (f : Batch (finRotate n))
    (admitted : f.AdmitsBeforeTells (X (Fin n)) world) (nonempty : f.members ≠ []) :
    n ≤ f.members.length := by
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ nonempty
  have supported : (support f).Nonempty := ⟨index f m, (mem_support f).mpr ⟨m, hm, rfl⟩⟩
  have full := closed_rotation_eq_univ supported ((admits_iff_closed f).mp admitted).2.2.2
  have size : (support f).card ≤ f.members.length := by
    unfold support
    exact (List.toFinset_card_le _).trans_eq (List.length_map _)
  simpa [full] using size

/-- No interleaving can start on a nontrivial rotation, even if the
individual step asks after tells. The full joint step still exists. -/
theorem rotation_no_single (n : Nat) (large : 1 < n)
    (g : Firing (Fin n) (E (Fin n)) (program (finRotate n)) PUnit.unit) :
    ¬ g.Admits (X (Fin n)) world := by
  let _ : NeZero n := ⟨by omega⟩
  intro admitted
  have bagAdmission := (Bag.single_admits_iff (X (Fin n)) world g).mpr admitted
  have ready := (admitsBeforeTells_iff_admits (Bag.single g)).mpr bagAdmission
  have lower := rotation_lower_bound n (Bag.single g) ready (List.cons_ne_nil _ _)
  rw [Bag.single_members] at lower
  omega

/-- The lower bound is sharp. For each lookahead bound there is an actual
two-read, one-guard program with a joint step and no nonempty step of
size at most that bound. -/
theorem no_uniform_bound (bound : Nat) :
    let n := bound + 2
    let rotate := finRotate n
    (∃ f : Batch rotate, (bagStep (X (Fin n)) (Fin n) (E (Fin n)) (program rotate)).Admits
        (s := world) f ∧ f.members.length = n) ∧
      ∀ f : Batch rotate, f.AdmitsBeforeTells (X (Fin n)) world →
        f.members.length ≤ bound → f.members = [] := by
  dsimp only
  let n := bound + 2
  obtain ⟨f, admitted, _, length⟩ :=
    (populations_iff (finRotate n) Finset.univ).mpr (fun i _ => Finset.mem_univ (finRotate n i))
  have full : f.members.length = n := length.trans (by simp)
  have live : f.members ≠ [] := by
    intro empty
    simp [empty, n] at full
  refine ⟨⟨f, Bag.beforeTells_step (X (Fin n)) world f ⟨live, admitted⟩ |>.1, full⟩, ?_⟩
  intro g ready small
  by_contra notEmpty
  have tooLarge := rotation_lower_bound n g ready notEmpty
  omega

end Cycles

section Maximality

private def cellKey (dependency : I → I) (i : I) : Rule (Terms (Value I)) × List I × List I :=
  (rule dependency i, [], [i, dependency i])

omit [Fintype I] [DecidableEq I] in
private theorem cellKey_injective (dependency : I → I) : Function.Injective (cellKey dependency) :=
  fun _ _ same => rule_injective dependency (congrArg Prod.fst same)

private theorem keys_iff {dependency : I → I} (f : Batch dependency)
    (admitted : f.Admits (X I) world) (key : Rule (Terms (Value I)) × List I × List I) :
    key ∈ f.members.map Member.key ↔ ∃ i ∈ support f, cellKey dependency i = key := by
  obtain ⟨b, σ, solved⟩ := admitted.2.2.1
  cases b
  have keyAt (m : Member I (E I) (program dependency) f.ext) (hm : m ∈ f.members) :
      m.key = cellKey dependency (index f m) := by
    have length := (admitted.1.2.2.2 m hm).1
    rw [rule_index f m] at length
    have empty : m.selection.taken = [] := List.length_eq_zero_iff.mp length.symm
    unfold Member.key cellKey
    rw [empty, reads_of_model f admitted.1 solved hm, rule_index f m]
  constructor
  · rintro listed
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp listed
    exact ⟨index f m, (mem_support f).mpr ⟨m, hm, rfl⟩, (keyAt m hm).symm⟩
  · rintro ⟨i, chosen, rfl⟩
    obtain ⟨m, hm, rfl⟩ := (mem_support f).mp chosen
    exact List.mem_map.mpr ⟨m, hm, keyAt m hm⟩

private theorem distinct_of_support_card {dependency : I → I} (f : Batch dependency)
    (admitted : f.Admits (X I) world) (size : (support f).card = f.members.length) :
    f.Distinct := by
  classical
  unfold Bag.Distinct
  have present := fun key => (keys_iff f admitted key)
  have keySet : (f.members.map Member.key).toFinset = (support f).image (cellKey dependency) := by
    ext key
    rw [List.mem_toFinset, Finset.mem_image]
    exact present key
  have count : (f.members.map Member.key).toFinset.card = (f.members.map Member.key).length := by
    rw [keySet, Finset.card_image_of_injective _ (cellKey_injective dependency), List.length_map, size]
  exact Multiset.coe_nodup.mp
    ((Multiset.toFinset_card_eq_card_iff_nodup (m := ⟦f.members.map Member.key⟧)).mp count)

/-- Bounded extension tests fail even on a nonempty admitted bag of
distinct matches. A separate self-dependent rule supplies the incumbent.
Any strict enlargement must include the whole rotation. -/
theorem no_bounded_maximality_test (bound : Nat) :
    let n := bound + 2
    let dependency : Option (Fin n) → Option (Fin n) := Option.map (finRotate n)
    ∃ base : Batch dependency,
      base.Admits (X (Option (Fin n))) world ∧ base.Distinct ∧ base.members.length = 1 ∧
        ¬ base.AdmitsMaximal (X (Option (Fin n))) world ∧
        ∀ extended : Batch dependency, extended.Admits (X (Option (Fin n))) world →
          extended.members.length ≤ 1 + bound →
          ∀ key ∈ extended.members.map Member.key, key ∈ base.members.map Member.key := by
  dsimp only
  let n := bound + 2
  let I := Option (Fin n)
  let dependency : I → I := Option.map (finRotate n)
  obtain ⟨base, baseBefore, baseSupport, baseLength⟩ :=
    (populations_iff dependency ({none} : Finset I)).mpr (by simp [dependency])
  obtain ⟨full, fullBefore, fullSupport, fullLength⟩ :=
    (populations_iff dependency Finset.univ).mpr (fun _ _ => Finset.mem_univ _)
  have baseAdmits := (admitsBeforeTells_iff_admits base).mp baseBefore
  have fullAdmits := (admitsBeforeTells_iff_admits full).mp fullBefore
  have baseDistinct := distinct_of_support_card base baseAdmits (baseSupport ▸ baseLength.symm)
  have fullDistinct := distinct_of_support_card full fullAdmits (fullSupport ▸ fullLength.symm)
  refine ⟨base, baseAdmits, baseDistinct, baseLength.trans (Finset.card_singleton _), ?_, ?_⟩
  · intro maximal
    have included : ∀ key ∈ base.members.map Member.key, key ∈ full.members.map Member.key := by
      intro key here
      obtain ⟨i, _, rfl⟩ := (keys_iff base baseAdmits key).mp here
      apply (keys_iff full fullAdmits _).mpr
      exact ⟨i, fullSupport ▸ Finset.mem_univ _, rfl⟩
    let site : I := some 0
    have keyPresent : cellKey dependency site ∈ full.members.map Member.key :=
      (keys_iff full fullAdmits _).mpr ⟨site, fullSupport ▸ Finset.mem_univ _, rfl⟩
    obtain ⟨i, iBase, keyEqual⟩ := (keys_iff base baseAdmits _).mp
      (maximal.2.2 full fullAdmits fullDistinct included _ keyPresent)
    have same : i = site := cellKey_injective dependency keyEqual
    subst i
    simp [site, baseSupport] at iBase
  · intro extended admitted small key found
    obtain ⟨i, chosen, rfl⟩ := (keys_iff extended admitted key).mp found
    cases i with
    | none =>
      exact (keys_iff base baseAdmits _).mpr ⟨none, baseSupport ▸ Finset.mem_singleton_self _, rfl⟩
    | some first =>
      let selected : Finset (Fin n) := Finset.univ.filter fun i => some i ∈ support extended
      have starts : first ∈ selected := by simp [selected, chosen]
      have closed := ((admits_iff_closed extended).mp ((admitsBeforeTells_iff_admits extended).mpr admitted)).2.2.2
      have closedCycle : ∀ i ∈ selected, finRotate n i ∈ selected := by
        intro i member
        have present : some i ∈ support extended := (Finset.mem_filter.mp member).2
        simpa [selected, dependency] using closed (some i) present
      have all := closed_rotation_eq_univ ⟨first, starts⟩ closedCycle
      have lower : n ≤ (support extended).card := by
        have included : (Finset.univ : Finset (Fin n)).image some ⊆ support extended := by
          rintro _ member
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
          have inCycle : j ∈ selected := by rw [all]; exact Finset.mem_univ _
          exact (Finset.mem_filter.mp inCycle).2
        simpa [Finset.card_image_of_injective _ (fun _ _ same => Option.some.inj same)]
          using Finset.card_le_card included
      have count : (support extended).card ≤ extended.members.length :=
        (List.toFinset_card_le _).trans_eq (List.length_map _)
      omega

end Maximality

#print axioms project_models
#print axioms admits_iff_closed
#print axioms populations_iff
#print axioms no_uniform_bound
#print axioms rotation_no_single
#print axioms no_bounded_maximality_test

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.GuardDependencies

