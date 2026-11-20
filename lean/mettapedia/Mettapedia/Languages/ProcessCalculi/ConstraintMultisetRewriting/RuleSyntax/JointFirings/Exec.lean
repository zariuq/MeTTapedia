import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Clashes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.MM2ExecStep

/-!
# MM2's exec as one step of `every`, and `match` as one step of `every`

`DialectsAsStrategies.MM2` reads one exec step from a space `S` as `((S \ {e}) ∪ A) \ R`
(`MM2.Behaviour.step`), with `A` and `R` the additions and removals of every solution of the exec's
patterns on `S`. There, the one-match step hosts it through a firing built from the effect, whose
admission does not check that every match was used (`MM2.Controls.incomplete_matches_admitted`).

Here the exec is one step of `every` over the foundation's rules, and admission checks completeness.

## A store that is a set

MM2's space is a set: removing an atom twice removes it once, adding it twice adds it once. The reading
of joint admission for such a store (`Bag.AdmitsAsSet`): every member is admitted on its own at the
entry state (so a member may read a row another takes: matching is on the pre-state), every member keeps
labels (its made identities already carry its made rows), the bag is jointly fresh, and the joint
information is solvable with every member's guards. Takes of two members may coincide, and so may makes,
which then carry one label. `every` in this reading (`Bag.AdmitsEveryAsSet`): admitted, within a set of
rules, and complete for it (the key of every admitted firing of one of the rules is the key of a member).
A match occurring twice changes nothing in this reading, so distinct keys are not asked.

With atoms as their own occurrences and labelled by themselves (`space`), and keeping labels, a made
row is its own atom (`Bag.result_label_of_keeping`): the store stays a set.

## The exec as rules

For an exec with behaviour `b` and row `e`:

* the **kernel** (`kernel e`): take the exec row;
* for each solution `σ`, the ground rule **`solutionRule b σ`**: take the atoms the solution removes,
  read the other atoms it matched, make the atoms it adds.

The exec's program (`program b e`) is the kernel and every solution rule. Its admitted firings at a space
select exactly the atoms of their patterns (`admitted_rows`).

## The theorem (`exec_is_every`)

When the solutions of the exec are the substitutions whose matched atoms are all present (`Presented`:
this is what matching a conjunction of patterns is), every solution removes only atoms it matched, the
exec row is present, and every solution's additions are new to the space:

* **a step of `every` exists** at the space: the kernel and one member per solution (`canonical`);
* **every step of `every` has the exec's result**: its rows are `b.step S e`, each labelled by itself.

So an exec step is exactly one step of `every`, and completeness is asked by admission: a bag that skips
a solution is not complete (`Items.skipping_not_every`), where the firing built from the effect admitted
it.

## Where the hypotheses are needed

* `Unmatched`: a solution that removes an atom it did not match (MM2 removes if present) is a take whose
  row must be present: at a space without that atom the exec still has the solution, and no firing of
  its rule is admitted.
* `Readd`: a solution that adds an atom already present (MM2 adds idempotently, and a removal of that
  atom wins) makes an identity that is present: no firing of its rule is admitted.

In a store that is a bag rather than a set, takes may not coincide (`Clashes`): the reading that refuses
applies, and two solutions removing one atom have no joint step.

## `match` (`MatchAll`)

A rule that only reads, with its answer as a made row: the complete bag of its matches is one step of
`every` in the reading that refuses (`MatchAll.both_every`); its result keeps the read rows and holds one
answer row per match (`MatchAll.both_result`). The answers are rows of the one world. Answers kept as
alternatives, each continuing on its own, are not given by a step whose result is one state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open OneFrame (Terms frames ext)

universe uO uT uH uE uOcc

/-! ## A store that is a set -/

section SetReading

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **Relabelling a list of identities by their own labels changes nothing.** -/
theorem relabel_map_self {O : Type uOcc} [DecidableEq O] {a : Obj} (old : O → Tm a) :
    ∀ (l : List O) (o : O), relabel old l (l.map old) o = old o
  | [], _ => rfl
  | o' :: rest, o => by
      simp only [List.map_cons, relabel]
      by_cases same : o = o'
      · rw [if_pos same, same]
      · rw [if_neg same]
        exact relabel_map_self old rest o

namespace Bag

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O)

/-- **Joint admission in a store that is a set**: every member is admitted on its own at the entry state
and keeps labels, the bag is jointly fresh, and the joint information is solvable with the guards of
every member at its solutions. -/
def AdmitsAsSet (f : Bag O E P s.frame) : Prop :=
  f.Fresh X s ∧ (∀ m ∈ f.members, m.firing.Admits X s ∧
      m.selection.made.map (m.firing.row X s) = (m.firing.opened X).produce) ∧
    X.Solvable (f.information X s) ∧ X.Entails (f.information X s) (fun _ σ => f.Holds X s σ)

/-- **`every` in a store that is a set**: admitted, within the rules, complete for them. -/
def AdmitsEveryAsSet (Q : Set (Rule Tm)) (f : Bag O E P s.frame) : Prop :=
  f.AdmitsAsSet X s ∧ f.Within Q ∧ f.Complete X s Q

variable {X s}

/-- **Keeping labels, the result labels every identity as before**: a made row is the label its
identity already had. -/
theorem result_label_of_keeping {f : Bag O E P s.frame}
    (keeps : ∀ m ∈ f.members, m.selection.made.map (m.firing.row X s) = (m.firing.opened X).produce)
    (o : O) : (f.result X s).label o = X.act (E.weaken f.ext) (s.label o) := by
  have produced : f.produce X = f.selection.made.map fun o' => X.act (E.weaken f.ext) (s.label o') := by
    show f.members.flatMap (fun m => (m.firing.opened X).produce) =
      (f.members.flatMap fun m => m.selection.made).map fun o' => X.act (E.weaken f.ext) (s.label o')
    rw [List.map_flatMap]
    exact List.flatMap_congr fun m inside => (keeps m inside).symm
  show relabel (fun o' => X.act (E.weaken f.ext) (s.label o')) f.selection.made (f.produce X) o = _
  rw [produced]
  exact relabel_map_self _ _ o

end Bag

end SetReading

/-! ## The exec as rules over atoms -/

namespace ExecStep

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)
open DialectsAsStrategies.MM2 (Behaviour)

/-- **A space**: atoms as their own occurrences, each labelled by itself, nothing known. -/
def space (S : Finset ℕ) : State Tm ℕ := ⟨PUnit.unit, [], S, c⟩

theorem c_injective : Function.Injective c := fun _ _ same => Term.const.inj same

/-- Constants are fixed by every substitution. -/
theorem opened_consts (τ : Subst atoms) (l : List ℕ) : (l.map c).map (action.apply τ) = l.map c := by
  rw [List.map_map]
  rfl

theorem consts_ground (l : List ℕ) : ∀ t ∈ l.map c, ∀ τ : Subst atoms, action.apply τ t = t := by
  intro t member τ
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp member
  rfl

section Rows

variable {P : Program Tm}

/-- **At a space, the rows selected for patterns of constants are their atoms.** -/
theorem matching_selected {S : Finset ℕ} (g : Firing ℕ E P PUnit.unit) {τ : Subst atoms} :
    ∀ (l sel : List ℕ), l.length = sel.length →
      (∀ e ∈ g.matching X (space S) (l.map c) sel, action.Solves τ e) → sel = l
  | [], [], _, _ => rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | a :: l, o :: sel, lengths, solves => by
      have head : (Term.const a : Term atoms) = Term.const o := solves _ List.mem_cons_self
      have rest := matching_selected g l sel (Nat.succ.inj lengths) fun e member =>
        solves e (List.mem_cons_of_mem _ member)
      rw [Term.const.inj head, rest]

/-- The equations of patterns of constants with their own atoms have identical sides. -/
theorem matching_identical {S : Finset ℕ} (g : Firing ℕ E P PUnit.unit) :
    ∀ (l : List ℕ), ∀ e ∈ g.matching X (space S) (l.map c) l, e.1 = e.2
  | [] => fun _ member => absurd member List.not_mem_nil
  | a :: l => fun e member => by
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact matching_identical g l e later

/-- **An admitted firing of a rule of constants selects the atoms of its patterns.** -/
theorem rows_of_admitted {S : Finset ℕ} {g : Firing ℕ E P PUnit.unit}
    (admitted : g.Admits X (space S)) {lt lr : List ℕ} (take : g.rule.body.take = lt.map c)
    (read : g.rule.body.read = lr.map c) : g.selection.taken = lt ∧ g.selection.read = lr := by
  obtain ⟨⟨-, -, -, takeLength, readLength, -, -⟩, -, ⟨_, τ, solved⟩, -⟩ := admitted
  have openedTake : (g.opened X).take = lt.map c := by
    show g.rule.body.take.map (action.apply g.opening) = lt.map c
    rw [take, opened_consts]
  have openedRead : (g.opened X).read = lr.map c := by
    show g.rule.body.read.map (action.apply g.opening) = lr.map c
    rw [read, opened_consts]
  rw [take, List.length_map] at takeLength
  rw [read, List.length_map] at readLength
  constructor
  · refine matching_selected (S := S) (τ := τ) g lt g.selection.taken takeLength fun e member => ?_
    rw [← openedTake] at member
    exact solved e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))
  · refine matching_selected (S := S) (τ := τ) g lr g.selection.read readLength fun e member => ?_
    rw [← openedRead] at member
    exact solved e (List.mem_append_left _ (List.mem_append_right _ member))

/-- **The information of a firing of a rule of constants with no tells, selecting its own atoms, has
identical sides.** -/
theorem information_identical {S : Finset ℕ} (g : Firing ℕ E P PUnit.unit) {lt lr : List ℕ}
    (take : g.rule.body.take = lt.map c) (read : g.rule.body.read = lr.map c)
    (tell : g.rule.body.tell = []) (taken : g.selection.taken = lt) (readSel : g.selection.read = lr) :
    ∀ e ∈ g.information X (space S), e.1 = e.2 := by
  have openedTake : (g.opened X).take = lt.map c := by
    show g.rule.body.take.map (action.apply g.opening) = lt.map c
    rw [take, opened_consts]
  have openedRead : (g.opened X).read = lr.map c := by
    show g.rule.body.read.map (action.apply g.opening) = lr.map c
    rw [read, opened_consts]
  have openedTell : (g.opened X).tell = [] := by
    show g.rule.body.tell.map _ = []
    rw [tell]
    rfl
  intro e member
  have split : e ∈ X.applyStore (E.weaken g.ext) (space S).knowledge ∨
      e ∈ g.matching X (space S) (g.opened X).take g.selection.taken ∨
      e ∈ g.matching X (space S) (g.opened X).read g.selection.read ∨ e ∈ (g.opened X).tell := by
    unfold Firing.information at member
    simp only [List.mem_append] at member
    tauto
  rcases split with known | inTake | inRead | told
  · exact absurd known List.not_mem_nil
  · rw [openedTake, taken] at inTake
    exact matching_identical g lt e inTake
  · rw [openedRead, readSel] at inRead
    exact matching_identical g lr e inRead
  · rw [openedTell] at told
    exact absurd told List.not_mem_nil

end Rows

variable {Sub : Type*} (b : Behaviour ℕ Sub)

/-- **The solutions are the substitutions whose matched atoms are all present**: what matching a
conjunction of patterns is. -/
def Presented : Prop := ∀ (S : Finset ℕ) (σ : Sub), σ ∈ b.solutions S ↔ b.matched σ ⊆ S

/-- **The rule of one solution**: take the atoms it removes, read the other atoms it matched, make the
atoms it adds. -/
noncomputable def solutionRule (σ : Sub) : Rule Tm :=
  ⟨PUnit.unit, ⟨(b.removes σ).toList.map c, (b.matched σ \ b.removes σ).toList.map c, [], [],
    (b.adds σ).toList.map c⟩, []⟩

/-- **The kernel**: take the exec row. -/
def kernel (e : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[c e], [], [], [], []⟩, []⟩

/-- **The exec's program**: the kernel and the rule of every solution. -/
def program (e : ℕ) : Program Tm := insert (kernel e) (Set.range (solutionRule b))

theorem kernel_ground (e : ℕ) : ∀ t ∈ (kernel e).terms, ∀ τ : Subst atoms, action.apply τ t = t := by
  intro t member τ
  have listed : t ∈ [c e] := by simpa [kernel, Rule.terms] using member
  rw [List.mem_singleton.mp listed]
  rfl

theorem solutionRule_ground (σ : Sub) :
    ∀ t ∈ (solutionRule b σ).terms, ∀ τ : Subst atoms, action.apply τ t = t := by
  intro t member τ
  have listed : t ∈ (b.removes σ).toList.map c ∨ t ∈ (b.matched σ \ b.removes σ).toList.map c ∨
      t ∈ (b.adds σ).toList.map c := by
    simp only [solutionRule, Rule.terms, List.map_nil, List.flatMap_nil, List.append_nil,
      List.mem_append] at member
    tauto
  rcases listed with inside | inside | inside <;> exact consts_ground _ t inside τ

/-- **The shape of an admitted firing of the exec's program**: the kernel takes the exec row; the rule of
a solution takes the atoms it removes and reads the other atoms it matched, which are present. -/
theorem admitted_rows {S : Finset ℕ} {e : ℕ} {g : Firing ℕ E (program b e) PUnit.unit}
    (admitted : g.Admits X (space S)) :
    (g.rule = kernel e ∧ g.selection.taken = [e] ∧ g.selection.read = []) ∨
      ∃ σ, g.rule = solutionRule b σ ∧ g.selection.taken = (b.removes σ).toList ∧
        g.selection.read = (b.matched σ \ b.removes σ).toList ∧ b.matched σ ⊆ S := by
  rcases g.member with isKernel | ⟨σ, isSolution⟩
  · obtain ⟨taken, read⟩ := rows_of_admitted admitted (lt := [e]) (lr := [])
      (by rw [isKernel]; rfl) (by rw [isKernel]; rfl)
    exact Or.inl ⟨isKernel, taken, read⟩
  · obtain ⟨taken, read⟩ := rows_of_admitted admitted (lt := (b.removes σ).toList)
      (lr := (b.matched σ \ b.removes σ).toList) (by rw [← isSolution]; rfl) (by rw [← isSolution]; rfl)
    have enabled := admitted.2.1
    refine Or.inr ⟨σ, isSolution.symm, taken, read, fun a inMatched => ?_⟩
    by_cases removed : a ∈ b.removes σ
    · refine enabled.taken_subset (List.mem_toFinset.mpr ?_)
      rw [taken]
      exact Finset.mem_toList.mpr removed
    · refine enabled.kept_subset (List.mem_toFinset.mpr ?_)
      rw [read]
      exact Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨inMatched, removed⟩)

/-- Keeping labels, a firing of the rule of a solution makes the atoms it adds. -/
theorem made_of_keeping {S : Finset ℕ} {e : ℕ} {g : Firing ℕ E (program b e) PUnit.unit} {σ : Sub}
    (isSolution : g.rule = solutionRule b σ)
    (keeps : g.selection.made.map (g.row X (space S)) = (g.opened X).produce) :
    g.selection.made = (b.adds σ).toList := by
  have produced : (g.opened X).produce = (b.adds σ).toList.map c := by
    show g.rule.body.produce.map (action.apply g.opening) = _
    rw [isSolution]
    exact opened_consts g.opening _
  have mapped : g.selection.made.map c = (b.adds σ).toList.map c := keeps.trans produced
  exact List.map_injective_iff.mpr c_injective mapped

/-- Keeping labels, a firing of the kernel makes nothing. -/
theorem kernel_made_of_keeping {S : Finset ℕ} {e : ℕ} {g : Firing ℕ E (program b e) PUnit.unit}
    (isKernel : g.rule = kernel e)
    (keeps : g.selection.made.map (g.row X (space S)) = (g.opened X).produce) :
    g.selection.made = [] := by
  have produced : (g.opened X).produce = [] := by
    show g.rule.body.produce.map (action.apply g.opening) = []
    rw [isKernel]
    rfl
  exact List.map_eq_nil_iff.mp (keeps.trans produced)

/-! ## The bag of every solution -/

/-- Take the exec row. -/
def kernelMember (e : ℕ) : OneMember action ℕ (program b e) :=
  ⟨kernel e, Or.inl rfl, Subst.id atoms, ⟨[e], [], []⟩, []⟩

/-- The member of one solution: its removed atoms taken, its other matched atoms read, its added atoms
made as their own identities. -/
noncomputable def solutionMember (e : ℕ) (σ : Sub) : OneMember action ℕ (program b e) :=
  ⟨solutionRule b σ, Or.inr ⟨σ, rfl⟩, Subst.id atoms,
    ⟨(b.removes σ).toList, (b.matched σ \ b.removes σ).toList, (b.adds σ).toList⟩, []⟩

/-- **The kernel and one member per solution.** -/
noncomputable def canonical (S : Finset ℕ) (e : ℕ) : Bag ℕ E (program b e) PUnit.unit :=
  bagOf action (kernelMember b e :: (b.solutions S).toList.map (solutionMember b e))

theorem kernelMember_admitted {S : Finset ℕ} {e : ℕ} (present : e ∈ S) :
    (kernelMember b e).firing.Admits X (space S) := by
  refine ⟨⟨Examples.fresh_of_ground action (space S) _ (kernel_ground e), List.nodup_singleton e,
      List.nodup_nil, rfl, rfl, rfl, rfl⟩, ⟨fun o member => ?_, fun o member => ?_,
      Finset.disjoint_left.mpr fun o _ kept => ?_, Finset.disjoint_left.mpr fun o made _ => ?_,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical
      (information_identical (kernelMember b e).firing (lt := [e]) (lr := []) rfl rfl rfl rfl rfl)⟩,
    fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · rw [List.mem_singleton.mp (List.mem_toFinset.mp member)]
    exact present
  · exact absurd (List.mem_toFinset.mp member) List.not_mem_nil
  · exact absurd (List.mem_toFinset.mp kept) List.not_mem_nil
  · exact absurd (List.mem_toFinset.mp made) List.not_mem_nil

variable {b}

theorem solutionMember_admitted (presented : Presented b)
    (consumesMatched : ∀ σ, b.removes σ ⊆ b.matched σ) {S : Finset ℕ} {e : ℕ} {σ : Sub}
    (solution : σ ∈ b.solutions S) (addsNew : Disjoint (b.adds σ) S) :
    (solutionMember b e σ).firing.Admits X (space S) := by
  have matched : b.matched σ ⊆ S := (presented S σ).mp solution
  refine ⟨⟨Examples.fresh_of_ground action (space S) _ (solutionRule_ground b σ),
      Finset.nodup_toList _, Finset.nodup_toList _, by simp [solutionRule, solutionMember],
      by simp [solutionRule, solutionMember], by simp [solutionRule, solutionMember], rfl⟩,
      ⟨fun o member => ?_, fun o member => ?_, Finset.disjoint_left.mpr fun o taken kept => ?_,
        Finset.disjoint_left.mpr fun o made present => ?_,
        fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical
      (information_identical (solutionMember b e σ).firing rfl rfl rfl rfl rfl)⟩,
    fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · exact matched (consumesMatched σ (Finset.mem_toList.mp (List.mem_toFinset.mp member)))
  · exact matched (Finset.mem_sdiff.mp (Finset.mem_toList.mp (List.mem_toFinset.mp member))).1
  · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp (List.mem_toFinset.mp kept))).2
      (Finset.mem_toList.mp (List.mem_toFinset.mp taken))
  · exact Finset.disjoint_left.mp addsNew (Finset.mem_toList.mp (List.mem_toFinset.mp made)) present

theorem canonical_members {S : Finset ℕ} {e : ℕ} {m : OneMember action ℕ (program b e)}
    (inside : m ∈ (canonical b S e).members) :
    m = kernelMember b e ∨ ∃ σ ∈ b.solutions S, m = solutionMember b e σ := by
  rcases List.mem_cons.mp inside with first | rest
  · exact Or.inl first
  · obtain ⟨σ, inSolutions, rfl⟩ := List.mem_map.mp rest
    exact Or.inr ⟨σ, Finset.mem_toList.mp inSolutions, rfl⟩

/-! ## An exec step is one step of `every` -/

/-- **An exec step is exactly one step of `every`.** When the solutions are the substitutions whose
matched atoms are present, every solution removes only atoms it matched, the exec row is present, and
every solution's additions are new: a step of `every` over the exec's program exists at the space, and
every such step has the exec's result, each row labelled by itself. -/
theorem exec_is_every (presented : Presented b) (consumesMatched : ∀ σ, b.removes σ ⊆ b.matched σ)
    {S : Finset ℕ} {e : ℕ} (present : e ∈ S) (addsNew : ∀ σ ∈ b.solutions S, Disjoint (b.adds σ) S) :
    (∃ f : Bag ℕ E (program b e) PUnit.unit, f.AdmitsEveryAsSet X (space S) (program b e)) ∧
      ∀ f : Bag ℕ E (program b e) PUnit.unit, f.AdmitsEveryAsSet X (space S) (program b e) →
        (f.result X (space S)).present = b.step S e ∧ ∀ o, (f.result X (space S)).label o = c o := by
  constructor
  · -- the bag of the kernel and every solution
    refine ⟨canonical b S e, ⟨fresh_of_ground_bag action (space S) _ fun m inside => ?_,
      fun m inside => ?_, ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun q inInfo => ?_⟩,
      fun _ _ _ m inside => ⟨fun check member => ?_, fun q member => ?_⟩⟩,
      fun m _ => m.member, fun g _ admitted => ?_⟩
    · rcases canonical_members inside with rfl | ⟨σ, -, rfl⟩
      · exact kernel_ground e
      · exact solutionRule_ground b σ
    · rcases canonical_members inside with rfl | ⟨σ, solution, rfl⟩
      · exact ⟨kernelMember_admitted b present, rfl⟩
      · refine ⟨solutionMember_admitted presented consumesMatched solution (addsNew σ solution), ?_⟩
        show (b.adds σ).toList.map c = ((b.adds σ).toList.map c).map (action.apply (Subst.id atoms))
        rw [opened_consts]
    · obtain ⟨m, inM, inOwn⟩ := List.mem_flatMap.mp (List.mem_append.mp inInfo |>.resolve_left
        (fun known => absurd known List.not_mem_nil))
      have inInformation : q ∈ m.firing.information X (space S) := by
        rw [Member.information_eq X (space S) m]
        exact List.mem_append_right _ inOwn
      rcases canonical_members inM with rfl | ⟨σ, -, rfl⟩
      · exact information_identical (kernelMember b e).firing (lt := [e]) (lr := []) rfl rfl rfl rfl rfl
          q inInformation
      · exact information_identical (solutionMember b e σ).firing rfl rfl rfl rfl rfl q inInformation
    · rcases canonical_members inside with rfl | ⟨σ, -, rfl⟩ <;> exact absurd member List.not_mem_nil
    · rcases canonical_members inside with rfl | ⟨σ, -, rfl⟩ <;> exact absurd member List.not_mem_nil
    · rcases admitted_rows b admitted with ⟨isKernel, taken, read⟩ |
        ⟨σ, isSolution, taken, read, matched⟩
      · refine List.mem_map.mpr ⟨kernelMember b e, List.mem_cons_self, ?_⟩
        show (kernel e, [e], ([] : List ℕ)) = (g.rule, g.selection.taken, g.selection.read)
        rw [isKernel, taken, read]
      · refine List.mem_map.mpr ⟨solutionMember b e σ, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨σ, Finset.mem_toList.mpr ((presented S σ).mpr matched), rfl⟩), ?_⟩
        show (solutionRule b σ, (b.removes σ).toList, (b.matched σ \ b.removes σ).toList) =
          (g.rule, g.selection.taken, g.selection.read)
        rw [isSolution, taken, read]
  · -- every step of `every` has the exec's result
    rintro f ⟨⟨-, members, -, -⟩, -, complete⟩
    refine ⟨?_, fun o => Bag.result_label_of_keeping (fun m inside => (members m inside).2) o⟩
    -- what the bag takes
    have takenIff : ∀ x, x ∈ f.selection.taken ↔ x = e ∨ x ∈ b.removed S := by
      intro x
      constructor
      · intro inside
        obtain ⟨m, inM, inTaken⟩ := List.mem_flatMap.mp inside
        rcases admitted_rows b (members m inM).1 with ⟨-, taken, -⟩ | ⟨σ, -, taken, -, matched⟩
        · have : x ∈ [e] := taken ▸ inTaken
          exact Or.inl (List.mem_singleton.mp this)
        · have inRemoves : x ∈ b.removes σ := Finset.mem_toList.mp (taken ▸ inTaken)
          exact Or.inr (Finset.mem_biUnion.mpr ⟨σ, (presented S σ).mpr matched, inRemoves⟩)
      · rintro (rfl | inRemoved)
        · obtain ⟨m, inM, sameKey⟩ := List.mem_map.mp (complete (kernelMember b x).firing (Or.inl rfl)
            (kernelMember_admitted b present))
          have taken : m.selection.taken = [x] := congrArg (fun k => k.2.1) sameKey
          exact List.mem_flatMap.mpr ⟨m, inM, by rw [taken]; exact List.mem_cons_self⟩
        · obtain ⟨σ, solution, inRemoves⟩ := Finset.mem_biUnion.mp inRemoved
          obtain ⟨m, inM, sameKey⟩ := List.mem_map.mp (complete (solutionMember b e σ).firing
            (Or.inr ⟨σ, rfl⟩)
            (solutionMember_admitted presented consumesMatched solution (addsNew σ solution)))
          have taken : m.selection.taken = (b.removes σ).toList := congrArg (fun k => k.2.1) sameKey
          exact List.mem_flatMap.mpr ⟨m, inM, by rw [taken]; exact Finset.mem_toList.mpr inRemoves⟩
    -- what the bag makes
    have madeIff : ∀ x, x ∈ f.selection.made ↔ x ∈ b.added S := by
      intro x
      constructor
      · intro inside
        obtain ⟨m, inM, inMade⟩ := List.mem_flatMap.mp inside
        rcases admitted_rows b (members m inM).1 with ⟨isKernel, -, -⟩ | ⟨σ, isSolution, -, -, matched⟩
        · rw [kernel_made_of_keeping b isKernel (members m inM).2] at inMade
          exact absurd inMade List.not_mem_nil
        · rw [made_of_keeping b isSolution (members m inM).2] at inMade
          exact Finset.mem_biUnion.mpr ⟨σ, (presented S σ).mpr matched, Finset.mem_toList.mp inMade⟩
      · intro inAdded
        obtain ⟨σ, solution, inAdds⟩ := Finset.mem_biUnion.mp inAdded
        obtain ⟨m, inM, sameKey⟩ := List.mem_map.mp (complete (solutionMember b e σ).firing
          (Or.inr ⟨σ, rfl⟩)
          (solutionMember_admitted presented consumesMatched solution (addsNew σ solution)))
        have isSolution : m.rule = solutionRule b σ := congrArg (fun k => k.1) sameKey
        refine List.mem_flatMap.mpr ⟨m, inM, ?_⟩
        rw [made_of_keeping b (g := m.firing) isSolution (members m inM).2]
        exact Finset.mem_toList.mpr inAdds
    -- removals are of present atoms; additions are new
    have removedIn : ∀ x ∈ b.removed S, x ∈ S := by
      intro x inRemoved
      obtain ⟨σ, solution, inRemoves⟩ := Finset.mem_biUnion.mp inRemoved
      exact (presented S σ).mp solution (consumesMatched σ inRemoves)
    have addedOut : ∀ x ∈ b.added S, x ∉ S := by
      intro x inAdded inS
      obtain ⟨σ, solution, inAdds⟩ := Finset.mem_biUnion.mp inAdded
      exact Finset.disjoint_left.mp (addsNew σ solution) inAdds inS
    ext x
    show x ∈ fire S (f.selection.commit (T := Unit)) ↔ x ∈ b.step S e
    rw [mem_fire]
    simp only [Selection.commit, List.mem_toFinset, Behaviour.step, Finset.mem_sdiff,
      Finset.mem_union, Finset.mem_erase]
    rw [takenIff x, madeIff x]
    constructor
    · rintro (⟨inS, notTaken⟩ | inAdded)
      · exact ⟨Or.inl ⟨fun same => notTaken (Or.inl same), inS⟩, fun inRemoved =>
          notTaken (Or.inr inRemoved)⟩
      · exact ⟨Or.inr inAdded, fun inRemoved => addedOut x inAdded (removedIn x inRemoved)⟩
    · rintro ⟨⟨notExec, inS⟩ | inAdded, notRemoved⟩
      · exact Or.inl ⟨inS, fun taken => taken.elim notExec notRemoved⟩
      · exact Or.inr inAdded

end ExecStep

/-! ## An instance, and the hypotheses with their controls -/

namespace ExecControls

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)
open DialectsAsStrategies.MM2 (Behaviour)
open ExecStep

/-- An exec over two items: the solution `true` matches item `1`, the solution `false` item `2`; each
takes its item and makes `10` more. -/
def items : Behaviour ℕ Bool where
  solutions S := Finset.univ.filter fun σ => (if σ then ({1} : Finset ℕ) else {2}) ⊆ S
  matched σ := if σ then {1} else {2}
  matched_sub _ _ solution := (Finset.mem_filter.mp solution).2
  removes σ := if σ then {1} else {2}
  adds σ := if σ then {11} else {12}
  stages _ := ∅

theorem items_presented : Presented items := fun S σ => by
  simp [items]

theorem items_consume : ∀ σ, items.removes σ ⊆ items.matched σ := fun _ => le_refl _

/-- The space of the exec `100` and the two items. -/
def start : Finset ℕ := {100, 1, 2}

theorem items_new : ∀ σ ∈ items.solutions start, Disjoint (items.adds σ) start := by
  intro σ _
  cases σ <;> decide

/-- **The exec's result**: both items taken, both made. -/
theorem items_step : items.step start 100 = {11, 12} := by decide

/-- **Every step of `every` has it**, and one exists. -/
theorem items_every :
    (∃ f : Bag ℕ E (program items 100) PUnit.unit,
      f.AdmitsEveryAsSet X (space start) (program items 100)) ∧
    ∀ f : Bag ℕ E (program items 100) PUnit.unit,
      f.AdmitsEveryAsSet X (space start) (program items 100) →
        (f.result X (space start)).present = {11, 12} := by
  obtain ⟨exists_, all⟩ := exec_is_every items_presented items_consume (S := start) (e := 100)
    (by decide) items_new
  exact ⟨exists_, fun f every => (all f every).1.trans items_step⟩

/-- **A bag that skips a solution is not a step of `every`**: the firing of the skipped solution is
admitted and its key is missing. -/
theorem skipping_not_every :
    ¬ (bagOf action [kernelMember items 100, solutionMember items 100 true] :
        Bag ℕ E (program items 100) PUnit.unit).Complete X (space start) (program items 100) := by
  intro complete
  have admitted := solutionMember_admitted (e := 100) items_presented items_consume
    (S := start) (σ := false) (by decide) (by decide)
  have listed := complete (solutionMember items 100 false).firing (Or.inr ⟨false, rfl⟩) admitted
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with same | same
  · have taken := congrArg (fun k : Rule Tm × List ℕ × List ℕ => k.2.1) same
    simp [firingKey, solutionMember, kernelMember, Member.key, items] at taken
  · have taken := congrArg (fun k : Rule Tm × List ℕ × List ℕ => k.2.1) same
    simp [firingKey, solutionMember, Member.key, items] at taken

/-- An exec whose solution `true` matches item `1` and removes item `2`, which it did not match. -/
def unmatched : Behaviour ℕ Bool where
  solutions S := Finset.univ.filter fun σ => (if σ then ({1} : Finset ℕ) else {2}) ⊆ S
  matched σ := if σ then {1} else {2}
  matched_sub _ _ solution := (Finset.mem_filter.mp solution).2
  removes _ := {2}
  adds σ := if σ then {11} else {12}
  stages _ := ∅

/-- **A removal of an atom the solution did not match**: at a space without item `2`, the exec has the
solution `true` and makes `11`; no firing of the solution's rule is admitted there, since its take of
item `2` finds no row. -/
theorem unmatched_refused :
    true ∈ unmatched.solutions {100, 1} ∧ 11 ∈ unmatched.step {100, 1} 100 ∧
      ∀ g : Firing ℕ E (program unmatched 100) PUnit.unit, g.rule = solutionRule unmatched true →
        ¬ g.Admits X (space {100, 1}) := by
  refine ⟨by decide, by decide, fun g isSolution admitted => ?_⟩
  obtain ⟨taken, -⟩ := rows_of_admitted admitted (lt := (unmatched.removes true).toList)
    (lr := (unmatched.matched true \ unmatched.removes true).toList) (by rw [isSolution]; rfl)
    (by rw [isSolution]; rfl)
  have inside : 2 ∈ g.selection.taken := by
    rw [taken]
    exact Finset.mem_toList.mpr (by decide)
  exact absurd (admitted.2.1.taken_subset (List.mem_toFinset.mpr inside)) (by decide)

/-- An exec whose one solution matches item `1`, removes it, and adds it again. -/
def readd : Behaviour ℕ Unit where
  solutions S := if 1 ∈ S then {()} else ∅
  matched _ := {1}
  matched_sub S σ solution := by
    by_cases present : 1 ∈ S
    · exact Finset.singleton_subset_iff.mpr present
    · simp [present] at solution
  removes _ := {1}
  adds _ := {1}
  stages _ := ∅

/-- **An addition of an atom that is present**: MM2 removes item `1` (its removal wins); no firing that
keeps labels and makes item `1` as its own identity is admitted, since that identity is present. -/
theorem readd_refused :
    1 ∉ readd.step {100, 1} 100 ∧
      ∀ g : Firing ℕ E (program readd 100) PUnit.unit, g.rule = solutionRule readd () →
        g.selection.made.map (g.row X (space {100, 1})) = (g.opened X).produce →
        ¬ g.Admits X (space {100, 1}) := by
  refine ⟨by decide, fun g isSolution keeps admitted => ?_⟩
  have made := made_of_keeping readd isSolution keeps
  have inside : 1 ∈ g.selection.made := by
    rw [made]
    exact Finset.mem_toList.mpr (by decide)
  exact Finset.disjoint_left.mp admitted.2.1.fresh (List.mem_toFinset.mpr inside) (by decide)

end ExecControls

/-! ## `match`: every match of a rule that only reads -/

namespace MatchAll

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open EveryControls (copy copies readAt copy_ground twoTokens tokensAt)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **Every admitted firing of `copy` reads one present token and makes one row.** -/
theorem copy_shape {W : Finset ℕ} (g : Firing ℕ E copies PUnit.unit)
    (admitted : g.Admits X (tokensAt W)) :
    ∃ o n, o ∈ W ∧ g.rule = copy ∧ g.selection = ⟨[], [o], [n]⟩ := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := g
  obtain ⟨⟨-, -, -, takeLength, readLength, produceLength, -⟩, enabled, -, -⟩ := admitted
  have isCopy : rule = copy := member
  subst isCopy
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp (show read.length = 1 from readLength.symm)
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp (show made.length = 1 from produceLength.symm)
  have noTake : taken = [] := List.length_eq_zero_iff.mp (show taken.length = 0 from takeLength.symm)
  subst noTake
  exact ⟨o, n, enabled.kept_subset (List.mem_toFinset.mpr List.mem_cons_self), rfl, rfl⟩

/-- **The bag of the two matches of `copy`.** -/
def both : Bag ℕ E copies PUnit.unit := bagOf action [readAt 0 10, readAt 1 11]

theorem both_information : Bag.information X twoTokens both = [(c 1, c 1), (c 1, c 1)] := rfl

/-- **Every match of the reading rule, at once, is a step of `every` in the reading that refuses.** -/
theorem both_every : Bag.AdmitsEvery X twoTokens copies both := by
  have members : ∀ m ∈ both.members, m = readAt 0 10 ∨ m = readAt 1 11 := by
    intro m inside
    have listed : m ∈ [readAt 0 10, readAt 1 11] := inside
    rcases List.mem_cons.mp listed with first | rest
    · exact Or.inl first
    · exact Or.inr (List.mem_singleton.mp rest)
  refine ⟨⟨⟨fresh_of_ground_bag action twoTokens _ fun m inside => ?_, by decide, by decide,
      fun m inside => ?_⟩, ⟨by decide, by decide, by decide, by decide,
        fun q member => by simp [Selection.commit] at member⟩,
      ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
      fun m inside b σ _ => ?_⟩, fun m inside => ?_, ?_, fun g _ admitted => ?_⟩
  · rcases members m inside with rfl | rfl <;> exact copy_ground
  · rcases members m inside with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [both_information] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    rw [member]
  · rcases members m inside with rfl | rfl <;>
      exact ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩
  · rcases members m inside with rfl | rfl <;> exact rfl
  · show [(readAt 0 10).key, (readAt 1 11).key].Nodup
    refine List.nodup_cons.mpr ⟨fun inside => ?_, List.nodup_singleton _⟩
    have differ : ([0] : List ℕ) ≠ [1] := by decide
    exact differ (congrArg (fun k : Rule Tm × List ℕ × List ℕ => k.2.2) (List.mem_singleton.mp inside))
  · obtain ⟨o, n, present, rule, selection⟩ := copy_shape g admitted
    have key : firingKey g = (copy, [], [o]) := by
      unfold firingKey
      rw [rule, selection]
    have cases : o = 0 ∨ o = 1 := by
      have inside : o ∈ ({0, 1} : Finset ℕ) := present
      simpa using inside
    rw [key]
    rcases cases with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **Its result keeps the read rows and holds one answer row per match.** -/
theorem both_result : (Bag.result X twoTokens both).present = {0, 1, 10, 11} ∧
    (Bag.result X twoTokens both).label 10 = c 2 ∧ (Bag.result X twoTokens both).label 11 = c 2 :=
  ⟨by decide, rfl, rfl⟩

end MatchAll

#print axioms relabel_map_self
#print axioms Bag.result_label_of_keeping
#print axioms ExecStep.matching_selected
#print axioms ExecStep.rows_of_admitted
#print axioms ExecStep.information_identical
#print axioms ExecStep.admitted_rows
#print axioms ExecStep.made_of_keeping
#print axioms ExecStep.kernelMember_admitted
#print axioms ExecStep.solutionMember_admitted
#print axioms ExecStep.exec_is_every
#print axioms ExecControls.items_step
#print axioms ExecControls.items_every
#print axioms ExecControls.skipping_not_every
#print axioms ExecControls.unmatched_refused
#print axioms ExecControls.readd_refused
#print axioms MatchAll.copy_shape
#print axioms MatchAll.both_every
#print axioms MatchAll.both_result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
