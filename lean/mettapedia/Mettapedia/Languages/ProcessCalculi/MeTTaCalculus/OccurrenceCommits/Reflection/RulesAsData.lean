import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceControls
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.HigherOrderFootprints

/-!
# Rules as data: installing, uninstalling and reading rules, with exact commutation

A persistent rule (`whenever`) is an occurrence in the store, in a **rule region**, and each of its
firings keeps that occurrence. So rules are data of the one store, and the operations on rules are
ordinary commits:

* **installing** a rule makes its occurrence (`install`);
* **uninstalling** takes it (`uninstall`);
* **firing** keeps it (`FiresRule`): concurrent firings of one rule only share a kept occurrence;
* **querying the rule base** is a predicate query of the rule region (`QueriesRuleAt`); MeTTa's
  evaluator does this when it decides that no equation applies, and an `every` over rules does it
  to be complete.

## The footprint of installing, and when it commutes

`install r` takes nothing, keeps nothing, makes `r` and has no predicate query. Exactness
(`Exactness.independent_iff_both_orders`) then gives the whole answer:

* **An install commutes with a commit exactly when the commit does not query `r`'s place in the
  rule region** and does not claim the same fresh identity (`install_independent_iff`). Every
  positive commit commutes with every install (`install_commutes_of_positive`), including firings
  of other rules.
* **An install and a reader of the rule base**: the reader must come first, or be matched again
  (`ruleBase_reader_before_install`). A wave with both has a precedence edge from the reader to the
  installer.
* **Uninstalling and firing**: an uninstall spoils every firing of the rule; the firing must come
  first (`firing_before_uninstall`).
* **Installing causes firings**: a firing of `r` is never enabled before `r` is installed
  (`firing_needs_install`). This is causality, not a conflict.

## A rule added inside an `every`: a stratum question

An `every` queries its regions (its completeness queries). If its region contains the rule
region, then:

* **its own installs falsify its snapshot** (`self_install_stales_read`): a commit that makes a rule
  inside a region it queries leaves that query false at its result. The new rule fires in a
  later round, never in the round that made it;
* **another commit's install must follow it** (`ruleBase_reader_before_install`), and a commit that
  installs a rule under a predicate query of the `every`'s outputs closes a precedence cycle with it
  (`RuleControls.reflective_cycle`): no order runs both, which is the reflective form of the absence
  race. A stratified program ranks the readers of the rule base before the installs into it.
* **MeTTa's own case**: the answer route of evaluation queries the equation region (no equation
  applies), so installing an equation withdraws an inert answer
  (`RuleControls.install_withdraws_inert_answer`), the commit form of
  `MeTTaZeroTransformEvaluation.answer_not_stable_under_new_equation`.

## MM2 reflective activation

An MM2 step takes an `exec` atom and fires every match of its pattern: a transform with a take of the
`exec` atom and an `every` over the matches, whose completeness query covers the match region. Two
activations commute exactly when their takes are apart and neither makes inside the other's match
region (`Exactness`); otherwise MM2's priority order decides the outcome
(`RuleControls.mm2_order_matters`).

## Controls (compiled through `SourceCompilation`, rows computed by `decide`)

* **A rule installed mid-wave changes an `every`'s outcome** (`RuleControls.install_changes_every`): a
  meta-interpreter that fires every installed rule on every fact makes `q(a)` from one rule; once a
  second rule is installed it makes `q(a)` and `s(a)`. The commit of the first `every` is disabled by
  the install (`RuleControls.install_disables_every`): the two do not commute.
* **MM2 activations in two orders** (`RuleControls.mm2_order_matters`).
* **An uninstall counts copies** (`RuleControls.uninstall_counts_copies`): with one copy of a rule, one
  uninstall leaves no firing; with two, a firing remains. The law "a persistent rule equals two
  copies of itself" holds only for contexts that do not take rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## Operations on rules -/

/-- Install the rule occurrence `r`: make it (`Commit.makeOne`). -/
def install (r : O) : Commit O R := Commit.makeOne r

/-- Uninstall the rule occurrence `r`: take it (`Commit.takeOne`). -/
def uninstall (r : O) : Commit O R := Commit.takeOne r

/-- A commit **fires the rule** `r` when it keeps the rule's occurrence. -/
def FiresRule (r : O) (c : Commit O R) : Prop := r ∈ c.kept

/-- A commit **queries the rule base at `r`'s place**: one of its predicate queries covers `r`'s
label. -/
def QueriesRuleAt (label : O → R) (r : O) (c : Commit O R) : Prop :=
  ∃ read ∈ c.queries, read.region (label r) = true

variable {label : O → R}

omit [DecidableEq O] in
theorem install_enabled_iff {S : Finset O} {r : O} :
    Enabled label S (install r : Commit O R) ↔ r ∉ S := by
  constructor
  · intro enabled inS
    exact Finset.disjoint_left.mp enabled.fresh (by simp [install]) inS
  · intro notIn
    exact ⟨by simp [install], by simp [install], by simp [install],
      by simpa [install] using notIn, by simp [install]⟩

/-- **When an install commutes**: exactly when the other commit claims a different fresh identity and
does not query the rule's place in the rule region. -/
theorem install_independent_iff {r : O} {c : Commit O R} :
    Independent label (install r) c ↔ r ∉ c.made ∧ ¬ QueriesRuleAt label r c := by
  constructor
  · rintro ⟨noClash, noSpoil, -⟩
    refine ⟨fun made => noClash (Or.inr (Finset.not_disjoint_iff.mpr ⟨r, by simp [install], made⟩)), ?_⟩
    rintro ⟨read, member, inRegion⟩
    exact noSpoil (Or.inr ⟨read, member, r, by simp [install], inRegion⟩)
  · rintro ⟨notMade, noRead⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro (taken | made)
      · exact taken (by simp [install])
      · exact made (Finset.disjoint_singleton_left.mpr notMade)
    · rintro (kept | ⟨read, member, o, written, inRegion⟩)
      · exact kept (by simp [install])
      · have same : o = r := by simpa [install] using written
        subst same
        exact noRead ⟨read, member, inRegion⟩
    · rintro (kept | ⟨read, member, -⟩)
      · exact kept (by simp [install])
      · simp [install] at member

/-- **Every positive commit commutes with every install**: both orders run and reach one store. -/
theorem install_commutes_of_positive {S : Finset O} {r : O} {c : Commit O R}
    (enabledC : Enabled label S c) (notIn : r ∉ S) (positive : c.Positive) (notMade : r ∉ c.made) :
    Enabled label (fire S (install r : Commit O R)) c ∧
      Enabled label (fire S c) (install r : Commit O R) ∧
      fire (fire S (install r : Commit O R)) c = fire (fire S c) (install r : Commit O R) := by
  have enabledI : Enabled label S (install r : Commit O R) := install_enabled_iff.mpr notIn
  have independent : Independent label (install r) c :=
    install_independent_iff.mpr ⟨notMade, fun ⟨read, member, _⟩ => by
      rw [show c.queries = [] from positive] at member
      cases member⟩
  obtain ⟨after, after'⟩ := (independent_iff_both_orders enabledI enabledC).mp independent
  exact ⟨after, after', fire_comm enabledI enabledC⟩

/-- **A reader of the rule base comes before an install into it**: the install spoils it, so in any
wave holding both the reader precedes the installer. -/
theorem ruleBase_reader_before_install {r : O} {e : Commit O R} (reads : QueriesRuleAt label r e)
    {W : List (Commit O R)} (inE : e ∈ W) (inI : install r ∈ W) (different : e ≠ install r) :
    Spoils label (install r) e ∧ BeforeOn label W e (install r) := by
  obtain ⟨read, member, inRegion⟩ := reads
  have spoils : Spoils label (install r) e :=
    Or.inr ⟨read, member, r, by simp [install], inRegion⟩
  exact ⟨spoils, inE, inI, different, spoils⟩

/-- **Uninstalling spoils every firing of the rule; the firing must come first.** -/
theorem firing_before_uninstall {S : Finset O} {r : O} {c : Commit O R}
    (enabledC : Enabled label S c) (fires : FiresRule r c) :
    Enabled label (fire S c) (uninstall r : Commit O R) ∧
      ¬ Enabled label (fire S (uninstall r : Commit O R)) c := by
  have inS : r ∈ S := enabledC.kept_subset fires
  have enabledU : Enabled label S (uninstall r : Commit O R) :=
    ⟨by simpa [uninstall] using inS, by simp [uninstall], by simp [uninstall], by simp [uninstall],
      by simp [uninstall]⟩
  have notTaken : r ∉ c.taken := fun taken => Finset.disjoint_left.mp enabledC.apart taken fires
  refine spoils_blocks_one_order enabledC enabledU ?_ ?_ ?_
  · rintro (taken | made)
    · exact taken (by simpa [uninstall] using notTaken)
    · exact made (by simp [uninstall])
  · exact Or.inl (Finset.not_disjoint_iff.mpr ⟨r, by simp [uninstall], fires⟩)
  · rintro (kept | ⟨read, member, -⟩)
    · exact kept (by simp [uninstall])
    · simp [uninstall] at member

omit [DecidableEq O] in
/-- **Installing causes firings**: a firing of `r` is not enabled where `r` is absent. -/
theorem firing_needs_install {S : Finset O} {r : O} {c : Commit O R} (fires : FiresRule r c)
    (absent : r ∉ S) : ¬ Enabled label S c := fun enabled => absent (enabled.kept_subset fires)

omit [DecidableEq O] in
/-- Two firings of one rule do not conflict over the rule: neither takes what both keep. -/
theorem firings_share_rule {S : Finset O} {r : O} {c d : Commit O R} (enabledC : Enabled label S c)
    (enabledD : Enabled label S d) (firesC : FiresRule r c) (firesD : FiresRule r d) :
    r ∉ c.taken ∧ r ∉ d.taken :=
  ⟨fun taken => Finset.disjoint_left.mp enabledC.apart taken firesC,
    fun taken => Finset.disjoint_left.mp enabledD.apart taken firesD⟩

/-- **Its own installs falsify an `every`'s snapshot**: a commit that makes a rule inside a region
it queries leaves that query false at its result, so the new rule is seen only by a later
round. -/
theorem self_install_stales_read {S : Finset O} {c : Commit O R} (enabled : Enabled label S c)
    {read : PredicateQuery O R} (member : read ∈ c.queries) {r : O} (made : r ∈ c.made)
    (inRegion : read.region (label r) = true) : ¬ read.Holds label (fire S c) := by
  intro holdsAfter
  have before := enabled.queries_hold read member
  unfold PredicateQuery.Holds at before holdsAfter
  have inSeen : r ∈ read.seen := by
    rw [← holdsAfter]
    exact mem_regionOf.mpr ⟨made_subset_fire made, inRegion⟩
  rw [← before] at inSeen
  exact Finset.disjoint_left.mp enabled.fresh made (mem_regionOf.mp inSeen).1

/-! ## Controls -/

namespace RuleControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls
  (Occ lbl Ls ms supply exists_of_not_forall k empty aAndB heldBoundRows heldFreeRows
    held_context_changes_source_rows)

/-- The atoms of the ground controls of `Commits`. -/
abbrev Atom := Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls.Atom

/-- Symbols of the rule controls. -/
abbrev RSig := Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls.Sig

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls.Sig

/-- A unary term. -/
def un (f : RSig) (x : Tm RSig) : Tm RSig := .node f x (.leaf .nil)

/-- The fact `seen(a)`. -/
def factA : Tm RSig := un .seen (.leaf .a)
/-- The output `out(a)`. -/
def outA : Tm RSig := un .out (.leaf .a)
/-- The output `out(b)`. -/
def outB : Tm RSig := un .out (.leaf .b)

/-- Two source texts that differ only in the variable they name. -/
def boundRead : Transform ℕ (Tm RSig) (Pat ℕ RSig) :=
  ⟨.cons (.read (.var 0)) .done, [.var 0]⟩

def freeRead : Transform ℕ (Tm RSig) (Pat ℕ RSig) :=
  ⟨.cons (.read (.var 1)) .done, [.var 1]⟩

/-- A held binding changes what the closure can keep. The free source can
    keep `a`; the source whose variable is bound to `b` cannot. -/
theorem held_context_distinguishes_closure_firings :
    (∀ c, ClosureFires Ls ms lbl aAndB boundRead
        (Function.update empty 0 (some (k .b))) c → (k .a, 0) ∉ c.kept) ∧
    (∃ c, ClosureFires Ls ms lbl aAndB freeRead
        (Function.update empty 0 (some (k .b))) c ∧ (k .a, 0) ∈ c.kept) := by
  constructor
  · intro c ⟨row, member, _, commit⟩
    change row ∈ heldBoundRows at member
    have keeps := held_context_changes_source_rows.2.2.1 row member
    rw [commit.kept, keeps]
    simp [k]
  · have has : ¬ ∀ row ∈ heldFreeRows,
        ¬ ((footprintOf row.2).Linear ∧ (footprintOf row.2).keeps = {(k .a, 0)}) := by
      decide +kernel
    obtain ⟨row, member, linear, keeps⟩ := exists_of_not_forall has
    obtain ⟨c, commit⟩ := exists_isCommitOf (S := aAndB) supply (footprintOf row.2)
    refine ⟨c, ⟨row, ?_, linear, commit⟩, ?_⟩
    · exact member
    · rw [commit.kept, keeps]
      simp

/-- A ground rule: `eqn(fact, output)`, "when `fact` holds, make `output`". -/
def rule (fact output : Tm RSig) : Tm RSig := .node .eqn fact output

/-- **The meta-interpreter**: for every installed rule and every fact it names, make the rule's
output. Its rule source reads the rule region (head `eqn`), its fact source the fact. -/
def interp : Transform ℕ (Tm RSig) (Pat ℕ RSig) :=
  ⟨.every (.cons (.read (.node .eqn (.var 0) (.var 1))) (.cons (.read (.var 0)) .done)), [.var 1]⟩

/-- One fact and one rule `seen(a) ⇒ out(a)`. -/
def before : Finset Occ := {(factA, 0), (rule factA outA, 1)}
/-- The same with a second rule `seen(a) ⇒ out(b)` installed. -/
def after : Finset Occ := {(factA, 0), (rule factA outA, 1), (rule factA outB, 2)}

/-- Install the second rule. -/
def installB : Commit Occ (Tm RSig) := install (rule factA outB, 2)

theorem installB_enabled : Enabled lbl before installB := install_enabled_iff.mpr (by decide)

theorem fire_installB : fire before installB = after := by decide

theorem interp_before_row :
    ∃ x ∈ interp.rows Ls ms lbl before, (footprintOf x.2).Linear ∧
      (footprintOf x.2).makes = {outA} ∧
      (true, ({(rule factA outA, 1)} : Finset Occ)) ∈
        (footprintOf x.2).queries.map fun read => (read.region (rule factA outB), read.seen) :=
  exists_of_not_forall (by decide)

theorem interp_after_row :
    ∃ x ∈ interp.rows Ls ms lbl after, (footprintOf x.2).Linear ∧
      (footprintOf x.2).makes = {outA, outB} :=
  exists_of_not_forall (by decide)

/-- Every row of the meta-interpreter before the install makes exactly `out(a)`. -/
theorem interp_before_only : ∀ x ∈ interp.rows Ls ms lbl before, (footprintOf x.2).makes = {outA} := by
  decide

/-- **A rule installed mid-wave changes an `every`'s outcome.** Before the install, every row of the
meta-interpreter makes `out(a)`; after it, a row makes `out(a)` and `out(b)`. -/
theorem install_changes_every :
    (∀ x ∈ interp.rows Ls ms lbl before, (footprintOf x.2).makes = {outA}) ∧
      ∃ x ∈ interp.rows Ls ms lbl (fire before installB), (footprintOf x.2).makes = {outA, outB} := by
  refine ⟨interp_before_only, ?_⟩
  rw [fire_installB]
  obtain ⟨x, member, -, makes⟩ := interp_after_row
  exact ⟨x, member, makes⟩

/-- **The install disables the snapshot `every`**: the commit the meta-interpreter fires before the
install queries the rule region, the install makes a rule there, so the commit is not enabled
after the install. The two do not commute; a stratified program runs the `every` first, or matches
it again. -/
theorem install_disables_every :
    ∃ c, Fires Ls ms lbl before interp c ∧ QueriesRuleAt lbl (rule factA outB, 2) c ∧
      ¬ Enabled lbl (fire before installB) c := by
  obtain ⟨x, member, linear, -, inMap⟩ := interp_before_row
  obtain ⟨read, inQueries, same⟩ := Multiset.mem_map.mp inMap
  have inRegion : read.region (rule factA outB) = true := (Prod.mk.inj same).1
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := before) supply (footprintOf x.2)
  have fires : Fires Ls ms lbl before interp c := ⟨x, member, linear, commit⟩
  have readsRule : QueriesRuleAt lbl (rule factA outB, 2) c :=
    ⟨read, (commit.queries read).mpr inQueries, inRegion⟩
  have spoils : Spoils lbl installB c := by
    obtain ⟨read', member', inRegion'⟩ := readsRule
    exact Or.inr ⟨read', member', (rule factA outB, 2), by simp [installB, install], inRegion'⟩
  exact ⟨c, fires, readsRule, fun after =>
    ((enabled_fire_iff fires.enabled installB_enabled).mp after).2 spoils⟩

/-! ### Installing an equation withdraws an inert answer -/

/-- The answer route of evaluation: take a redex `redex(x)` and, when no equation `eqn(x, _)` is
installed, answer `out(x)`. The absence queries the equation region. -/
def inertAnswer : Transform ℕ (Tm RSig) (Pat ℕ RSig) :=
  ⟨.cons (.take (.node .redex (.var 0) (.leaf .nil)))
    (.cons (.absent (.node .eqn (.var 0) (.var 1))) .done), [.node .out (.var 0) (.leaf .nil)]⟩

/-- A redex `redex(a)` and no equation. -/
def redexOnly : Finset Occ := {(un .redex (.leaf .a), 0)}
/-- The same after installing the equation `eqn(a, b)`. -/
def redexWithRule : Finset Occ := {(un .redex (.leaf .a), 0), (rule (.leaf .a) (.leaf .b), 1)}

/-- **Installing an equation withdraws an inert answer.** Before the install the answer route fires
and answers `out(a)`; after it, no row is linear and nothing fires. Installing a rule commutes with
every positive firing, never with an evaluation that has concluded that no rule applies. -/
theorem install_withdraws_inert_answer :
    (∃ x ∈ inertAnswer.rows Ls ms lbl redexOnly, (footprintOf x.2).Linear ∧
        (footprintOf x.2).makes = {un .out (.leaf .a)}) ∧
      (∀ x ∈ inertAnswer.rows Ls ms lbl redexWithRule, False) ∧
      ∀ c, ¬ Fires Ls ms lbl redexWithRule inertAnswer c := by
  have none : ∀ x ∈ inertAnswer.rows Ls ms lbl redexWithRule, False := by decide
  exact ⟨exists_of_not_forall (by decide), none, fun c ⟨x, member, _⟩ => none x member⟩

/-! ### A reflective precedence cycle -/

/-- Occurrence labels for the cycle: `100` is a rule, `101` an output. -/
def cycLabel : ℕ → Atom
  | 100 => .lock
  | 101 => .out
  | _ => .tok

/-- The rule region: locks stand for rules here. -/
def isRuleRegion : Atom → Bool
  | .lock => true
  | _ => false

/-- The output region. -/
def isOutRegion : Atom → Bool
  | .out => true
  | _ => false

/-- The `every` over the rule base: queries the rule region (empty), makes an output. -/
def everyOverRules : Commit ℕ Atom := ⟨∅, ∅, {101}, [⟨isRuleRegion, ∅⟩]⟩

/-- An installer guarded by the absence of outputs: installs the rule `100`. -/
def guardedInstall : Commit ℕ Atom := ⟨∅, ∅, {100}, [⟨isOutRegion, ∅⟩]⟩

/-- **A reflective precedence cycle.** The `every` over rules must precede the installer (the
install writes into the rule region it reads), and the installer must precede the `every` (the
`every` writes into the output region the installer reads). No order runs both. -/
theorem reflective_cycle :
    Enabled cycLabel ∅ everyOverRules ∧ Enabled cycLabel ∅ guardedInstall ∧
      BeforeOn cycLabel [everyOverRules, guardedInstall] everyOverRules guardedInstall ∧
      BeforeOn cycLabel [everyOverRules, guardedInstall] guardedInstall everyOverRules ∧
      ¬ ∃ l, l.Perm [everyOverRules, guardedInstall] ∧ Executable cycLabel ∅ l := by
  have enabledE : Enabled cycLabel ∅ everyOverRules :=
    ⟨by simp [everyOverRules], by simp [everyOverRules], by simp [everyOverRules],
      by simp [everyOverRules], by
        intro read member
        simp only [everyOverRules, List.mem_singleton] at member
        subst member
        decide⟩
  have enabledG : Enabled cycLabel ∅ guardedInstall :=
    ⟨by simp [guardedInstall], by simp [guardedInstall], by simp [guardedInstall],
      by simp [guardedInstall], by
        intro read member
        simp only [guardedInstall, List.mem_singleton] at member
        subst member
        decide⟩
  have different : everyOverRules ≠ guardedInstall := fun same => by
    have := congrArg Commit.made same
    simp [everyOverRules, guardedInstall] at this
  have edge1 : BeforeOn cycLabel [everyOverRules, guardedInstall] everyOverRules guardedInstall :=
    ⟨by simp, by simp, different,
      Or.inr ⟨⟨isRuleRegion, ∅⟩, by simp [everyOverRules], 100, by simp [guardedInstall], by decide⟩⟩
  have edge2 : BeforeOn cycLabel [everyOverRules, guardedInstall] guardedInstall everyOverRules :=
    ⟨by simp, by simp, fun same => different same.symm,
      Or.inr ⟨⟨isOutRegion, ∅⟩, by simp [guardedInstall], 101, by simp [everyOverRules], by decide⟩⟩
  refine ⟨enabledE, enabledG, edge1, edge2, fun ordered => ?_⟩
  have noClash : [everyOverRules, guardedInstall].Pairwise (fun e d => ¬ Clash e d) := by
    refine List.pairwise_pair.mpr ?_
    rintro (taken | made)
    · exact taken (by simp [everyOverRules])
    · exact made (by simp [everyOverRules, guardedInstall])
  have acyclic := (exists_executable_perm_iff_acyclic (fun c member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact enabledE
    · exact enabledG) noClash).mp ordered
  exact acyclic _ (Relation.TransGen.tail (.single edge1) edge2)

/-! ### MM2 activation in two orders -/

/-- An MM2 step: take `redex(pattern, output)` (the `exec` atom) and, for every occurrence of the
pattern, make the output. -/
def mm2Exec : Transform ℕ (Tm RSig) (Pat ℕ RSig) :=
  ⟨.cons (.take (.node .redex (.var 0) (.var 1))) (.every (.cons (.read (.var 0)) .done)), [.var 1]⟩

/-- `exec(seen(a), out(a))`: if `seen(a)`, make `out(a)`. -/
def execOut : Tm RSig := .node .redex factA outA
/-- `exec(tok, seen(a))`: if `tok`, make `seen(a)`. -/
def execFact : Tm RSig := .node .redex (.leaf .tok) factA

/-- Both `exec` atoms and a token. -/
def mm2Store : Finset Occ := {(execOut, 0), (execFact, 1), (.leaf .tok, 2)}

/-- Running `execOut` first: its `every` has no row, it takes its `exec` atom and makes nothing. -/
theorem mm2_out_first :
    ∃ x ∈ mm2Exec.rows Ls ms lbl mm2Store, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(execOut, 0)} ∧ (footprintOf x.2).makes = 0 :=
  exists_of_not_forall (by decide)

/-- The store after `execFact` ran first: the fact `seen(a)` is there. -/
def mm2AfterFact : Finset Occ := {(execOut, 0), (.leaf .tok, 2), (factA, 3)}

/-- Running `execOut` after `execFact`: its `every` has one row and makes `out(a)`. -/
theorem mm2_out_second :
    ∃ x ∈ mm2Exec.rows Ls ms lbl mm2AfterFact, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(execOut, 0)} ∧ (footprintOf x.2).makes = {outA} :=
  exists_of_not_forall (by decide)

/-- `execFact` fires at the start and makes `seen(a)`. -/
theorem mm2_fact_fires :
    ∃ x ∈ mm2Exec.rows Ls ms lbl mm2Store, (footprintOf x.2).Linear ∧
      (footprintOf x.2).takes = {(execFact, 1)} ∧ (footprintOf x.2).makes = {factA} :=
  exists_of_not_forall (by decide)

/-- **MM2's order decides the outcome.** At the start, the activation of `execOut` makes nothing;
after the activation of `execFact`, it makes `out(a)`. -/
theorem mm2_order_matters :
    (∀ x ∈ mm2Exec.rows Ls ms lbl mm2Store, (footprintOf x.2).takes = {(execOut, 0)} →
        (footprintOf x.2).makes = 0) ∧
      ∃ x ∈ mm2Exec.rows Ls ms lbl mm2AfterFact, (footprintOf x.2).makes = {outA} := by
  refine ⟨by decide, ?_⟩
  obtain ⟨x, member, -, -, makes⟩ := mm2_out_second
  exact ⟨x, member, makes⟩

/-! ### An uninstall counts copies -/

/-- One copy of a rule. -/
def oneCopy : Finset ℕ := {100}
/-- Two copies of a rule (one label, two occurrences). -/
def twoCopies : Finset ℕ := {100, 102}

/-- A firing of the copy `102`. -/
def fireCopy : Commit ℕ Atom := ⟨∅, {102}, {101}, []⟩

/-- A firing of the copy `100`. -/
def fireFirst : Commit ℕ Atom := ⟨∅, {100}, {101}, []⟩

/-- **An uninstall counts copies.** With two copies, after uninstalling `100` a firing of the rule
is still enabled; with one copy, no firing of any copy is. -/
theorem uninstall_counts_copies :
    Enabled cycLabel (fire twoCopies (uninstall 100 : Commit ℕ Atom)) fireCopy ∧
      fire oneCopy (uninstall 100 : Commit ℕ Atom) = ∅ ∧
      ∀ c : Commit ℕ Atom, (FiresRule 100 c ∨ FiresRule 102 c) →
        ¬ Enabled cycLabel (fire oneCopy (uninstall 100 : Commit ℕ Atom)) c := by
  refine ⟨⟨by simp [fireCopy], by decide, by simp [fireCopy], by decide, by simp [fireCopy]⟩,
    by decide, fun c fires enabled => ?_⟩
  have empty : fire oneCopy (uninstall 100 : Commit ℕ Atom) = ∅ := by decide
  rcases fires with fires | fires
  · have := enabled.kept_subset fires
    rw [empty] at this
    simp at this
  · have := enabled.kept_subset fires
    rw [empty] at this
    simp at this

end RuleControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection
