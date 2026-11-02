import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability

/-!
# Separating examples over the existing constraint multiset rewriting definitions

Uses `Check`, `Selection.Valid`, `SubstitutionAction.Entails`,
`Provenance.Infers`, `Provenance.SystemStep` and `Derivable`.

* Conjunctive absence: absence of a conjunction with a shared local variable is not the list of
  separately entailed absence checks.
* Promotion: `Provenance.Infers` keeps no trace of the world in which a guard was checked.
  A conclusion derivable from no hypotheses can still depend on an absence guard, and the
  installation that drops the guard reaches a configuration the original system never reaches.
  A closed conclusion can also depend on a local equation (a scope restriction): the
  universal schema is not derivable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedProcessCounterexamples

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)

/-- Two unary symbols `p` (`false`) and `q` (`true`) over natural-number constants. -/
abbrev sig : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Bool
  functionArity _ := 1

abbrev A := FirstOrder.action sig

def p (t : Term sig) : Term sig := .app false (fun _ => t)
def q (t : Term sig) : Term sig := .app true (fun _ => t)
def a : Term sig := .const 0
def b : Term sig := .const 1
def X : Term sig := .var 0

theorem p_inj {s t : Term sig} (same : p s = p t) : s = t :=
  congr_fun (eq_of_heq (Term.app.inj same).2) 0

theorem q_inj {s t : Term sig} (same : q s = q t) : s = t :=
  congr_fun (eq_of_heq (Term.app.inj same).2) 0

theorem p_ne_q (s t : Term sig) : p s ≠ q t := by
  intro same
  have symbols := (Term.app.inj same).1
  cases symbols

theorem a_ne_b : a ≠ b := by
  intro same
  cases same

/-! ## Conjunctive absence: absence of a conjunction with a shared local variable -/

def world : Finset Nat := {0, 1}

/-- Occurrence `0` carries `p(a)`, occurrence `1` carries `q(b)`. -/
def worldLabel : Nat → Term sig
  | 0 => p a
  | _ => q b

/-- The list encoding `[absent p(X), absent q(X)]` fails already at its first check:
the all-future ask ranges over `X := a`, where `p(a)` is present. -/
theorem list_encoding_first_check_not_entailed :
    ¬ A.Entails [] (fun σ => (Check.absent (p X)).Holds A σ worldLabel world) := by
  intro entailed
  have holds := entailed (Subst.single 0 a) (A.models_nil _)
  exact holds 0 (by simp [world]) rfl

/-- The intended guard: no single value of `X` makes both `p(X)` and `q(X)` present. -/
def JoinAbsent (σ : Subst sig) : Prop :=
  ¬ ((∃ o ∈ world, A.E (A.apply σ (p X)) (A.apply σ (worldLabel o))) ∧
     (∃ o ∈ world, A.E (A.apply σ (q X)) (A.apply σ (worldLabel o))))

/-- The joined absence holds in every solution of the empty store. -/
theorem join_absence_entailed : A.Entails [] JoinAbsent := by
  intro σ _ both
  obtain ⟨⟨o, member, same⟩, ⟨o', member', same'⟩⟩ := both
  simp only [world, Finset.mem_insert, Finset.mem_singleton] at member member'
  rcases member with rfl | rfl <;> rcases member' with rfl | rfl
  · have hq : q (σ 0) = p a := same'
    exact p_ne_q _ _ hq.symm
  · have hp : p (σ 0) = p a := same
    have hq : q (σ 0) = q b := same'
    exact a_ne_b ((p_inj hp).symm.trans (q_inj hq))
  · have hp : p (σ 0) = q b := same
    exact p_ne_q _ _ hp
  · have hp : p (σ 0) = q b := same
    exact p_ne_q _ _ hp

/-! ## Promotion: world-free inference forgets an absence guard -/

def pTok : Term sig := .const 7
def qTok : Term sig := .const 9

/-- Publish `q` when no `p` is present. -/
def guarded : RuleInstance (Term sig) := ⟨[], [], [], [.absent pTok], [qTok]⟩

/-- The same rule installed with its guard dropped. -/
def unguarded : RuleInstance (Term sig) := ⟨[], [], [], [], [qTok]⟩

/-- Identity `4` carries `p`; every other identity carries `q`. -/
def lab : Nat → Term sig := fun o => if o = 4 then pTok else qTok

def emptyWorld : Configuration (Term sig) Nat := ⟨[], ∅⟩
def pWorld : Configuration (Term sig) Nat := ⟨[], {4}⟩
def makeFive : Selection Nat := ⟨[], [], [5]⟩

theorem guarded_fires_in_the_empty_world : makeFive.Valid A lab guarded emptyWorld := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id sig, ?_⟩, ?_⟩
  · intro equation member
    simp [Selection.problem, Selection.equations, guarded, makeFive, emptyWorld] at member
  · intro check member σ _
    have same : check = .absent pTok := by simpa [guarded] using member
    subst same
    intro o present
    simp [emptyWorld] at present

/-- In the world holding `p`, no selection fires the guarded rule. -/
theorem guarded_never_fires_beside_p (before : Configuration (Term sig) Nat)
    (present : 4 ∈ before.present) (selection : Selection Nat) :
    ¬ selection.Valid A lab guarded before := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.consistent
  have holds := valid.checks (.absent pTok) (by simp [guarded]) σ solved
  exact holds 4 present rfl

def everyProtected : Nat → Prop := fun _ => True

instance : DecidablePred everyProtected := fun _ => isTrue trivial

/-- The firing in the empty world is an inference with no premises. -/
theorem guarded_infers_from_nothing :
    Provenance.Infers A lab everyProtected [guarded] 0 qTok := by
  refine ⟨guarded, List.mem_singleton_self _, emptyWorld, makeFive, Subst.id sig,
    guarded_fires_in_the_empty_world, ?_, ?_, 5, by simp [makeFive], trivial, rfl⟩
  · intro equation member
    simp [Selection.problem, Selection.equations, guarded, makeFive, emptyWorld] at member
  · simp [Provenance.premises, makeFive, labels]

/-- So `q` is derivable from no hypotheses at all, in every world. -/
theorem q_derivable_from_nothing :
    Derivable (fun _ => False) (Provenance.Infers A lab everyProtected [guarded]) qTok :=
  .infer guarded_infers_from_nothing (fun premise member => by simp at member)

/-- Invariant of the original system started beside `p`: while `p` is present, nothing else is. -/
def PAlone (state : Configuration (Term sig) Nat) : Prop :=
  4 ∈ state.present → ∀ o ∈ state.present, o = 4

theorem step_keeps_p_alone {before after : Configuration (Term sig) Nat}
    (step : Provenance.SystemStep A lab everyProtected [guarded] before after)
    (prior : PAlone before) : PAlone after := by
  obtain ⟨rule, selection, valid, admitted, rfl⟩ := step
  intro pAfter o member
  rcases admitted with installed | unpublished
  · have same : rule = guarded := List.mem_singleton.mp installed
    subst same
    have notBefore : 4 ∉ before.present := fun pBefore =>
      guarded_never_fires_beside_p before pBefore selection valid
    exfalso
    rcases mem_fire.mp pAfter with ⟨stayed, _⟩ | made
    · exact notBefore stayed
    · have made' : 4 ∈ selection.made := by simpa [Selection.commit] using made
      have labelled := valid.outputs
      have inMap : lab 4 ∈ selection.made.map lab := List.mem_map_of_mem made'
      rw [labelled] at inMap
      simp [guarded, lab, pTok, qTok] at inMap
  · have noneMade : selection.made = [] := by
      cases hm : selection.made with
      | nil => rfl
      | cons first rest =>
          exact absurd trivial (unpublished first (by simp [hm]))
    have shrink : ∀ o', o' ∈ fire before.present (selection.commit (T := Term sig)) → o' ∈ before.present := by
      intro o' inFire
      rcases mem_fire.mp inFire with ⟨stayed, _⟩ | made
      · exact stayed
      · simp [Selection.commit, noneMade] at made
    exact prior (shrink 4 pAfter) o (shrink o member)

theorem run_keeps_p_alone {before after : Configuration (Term sig) Nat}
    (run : Relation.ReflTransGen (Provenance.SystemStep A lab everyProtected [guarded]) before after)
    (prior : PAlone before) : PAlone after := by
  induction run with
  | refl => exact prior
  | tail _ step earlier => exact step_keeps_p_alone step earlier

theorem p_world_alone : PAlone pWorld := by
  intro _ o member
  simpa [pWorld] using member

/-- **The original system never holds `p` and `q` together**, from the world holding `p`. -/
theorem original_never_reaches_p_and_q {after : Configuration (Term sig) Nat}
    (run : Relation.ReflTransGen (Provenance.SystemStep A lab everyProtected [guarded]) pWorld after) :
    ¬ (4 ∈ after.present ∧ 5 ∈ after.present) := by
  rintro ⟨four, five⟩
  have alone := run_keeps_p_alone run p_world_alone four 5 five
  cases alone

theorem unguarded_fires_beside_p : makeFive.Valid A lab unguarded pWorld := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id sig, ?_⟩, ?_⟩
  · intro equation member
    simp [Selection.problem, Selection.equations, unguarded, makeFive, pWorld] at member
  · intro check member
    simp [unguarded] at member

/-- **Installing the guard-free schema reaches `p` and `q` together in one step.** -/
theorem guard_free_installation_is_not_conservative :
    ∃ after, Provenance.SystemStep A lab everyProtected [guarded, unguarded] pWorld after ∧
      4 ∈ after.present ∧ 5 ∈ after.present :=
  ⟨makeFive.result lab unguarded pWorld,
    ⟨unguarded, makeFive, unguarded_fires_beside_p, Or.inl (by simp), rfl⟩, by decide, by decide⟩

/-! ## Promotion: a closed conclusion that depends on a local equation (scope restriction) -/

/-- Tell `X = a`, publish `p(X)`. -/
def pinned : RuleInstance (Term sig) := ⟨[], [], [(X, a)], [], [p X]⟩

def pinnedLabel : Nat → Term sig := fun _ => p X

theorem pinned_fires : makeFive.Valid A pinnedLabel pinned emptyWorld := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.single 0 a, ?_⟩, ?_⟩
  · intro equation member
    have same : equation = (X, a) := by
      simpa [Selection.problem, Selection.equations, pinned, makeFive, emptyWorld] using member
    subst same
    rfl
  · intro check member
    simp [pinned] at member

/-- Every inference of the installed rule concludes `p(a)`. -/
theorem pinned_concludes_only_pa {premises : Multiset (Term sig)} {conclusion : Term sig}
    (inferred : Provenance.Infers A pinnedLabel everyProtected [pinned] premises conclusion) :
    conclusion = p a := by
  obtain ⟨rule, installed, before, selection, σ, valid, solved, _, o, made, _, rfl⟩ := inferred
  have same : rule = pinned := List.mem_singleton.mp installed
  subst same
  have told : σ.applyTerm X = σ.applyTerm a :=
    (Selection.models_problem A valid solved).2.2.2 (X, a) (by simp [pinned])
  change p (σ.applyTerm X) = p a
  rw [told]
  rfl

/-- `p(a)` is derivable from nothing, `p(b)` is not: promoting the closed conclusion to the
schema `∀X. p(X)` would be unsound. -/
theorem pa_derivable_pb_not :
    Derivable (fun _ => False) (Provenance.Infers A pinnedLabel everyProtected [pinned]) (p a) ∧
    ¬ Derivable (fun _ => False) (Provenance.Infers A pinnedLabel everyProtected [pinned]) (p b) := by
  constructor
  · refine .infer (premises := 0) ?_ (fun premise member => by simp at member)
    refine ⟨pinned, List.mem_singleton_self _, emptyWorld, makeFive, Subst.single 0 a,
      pinned_fires, ?_, ?_, 5, by simp [makeFive], trivial, rfl⟩
    · intro equation member
      have same : equation = (X, a) := by
        simpa [Selection.problem, Selection.equations, pinned, makeFive, emptyWorld] using member
      subst same
      rfl
    · simp [Provenance.premises, makeFive, labels]
  · intro derived
    cases derived with
    | initial impossible => exact impossible
    | infer inferred _ =>
        have same := pinned_concludes_only_pa inferred
        exact a_ne_b (p_inj same).symm

/-! ## an absence guard adds order between firings with no resource edge

`maker` publishes `p` as identity `4`; `checker` publishes `q` as `5` when no `p` is present.
Neither takes or reads anything, so there is no causality, no asymmetric conflict and no
identity reuse between them, yet only one order runs. The check-free hypothesis of the swap
lemma cannot be dropped. -/

def maker : ConditionalSchedule.Firing (Term sig) Nat := (⟨[], [], [], [], [pTok]⟩, ⟨[], [], [4]⟩)
def checker : ConditionalSchedule.Firing (Term sig) Nat := (guarded, makeFive)

theorem no_resource_edges :
    maker.2.taken = [] ∧ maker.2.read = [] ∧ checker.2.taken = [] ∧ checker.2.read = [] ∧
      maker.2.made = [4] ∧ checker.2.made = [5] := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem checker_then_maker_runs :
    ConditionalSchedule.Executable A lab emptyWorld [checker, maker] := by
  refine ⟨guarded_fires_in_the_empty_world, ?_, ⟨Subst.id sig, ?_⟩⟩
  · refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id sig, ?_⟩, ?_⟩
    · intro equation member
      simp [Selection.problem, Selection.result, Selection.equations, maker, checker, guarded,
        makeFive, emptyWorld] at member
    · intro check member
      simp [maker] at member
  · intro equation member
    simp [Selection.problem, Selection.result, Selection.equations, maker,
      checker, guarded, makeFive, emptyWorld] at member

theorem maker_then_checker_does_not_run :
    ¬ ConditionalSchedule.Executable A lab emptyWorld [maker, checker] := by
  rintro ⟨_, checkerValid, _⟩
  exact guarded_never_fires_beside_p _ (by decide) makeFive checkerValid

/-! ## consume-and-republish inflates proof-use dependencies

`ProofUse.advance` gives each made occurrence the union of the origins of its protected
premises. A rule reading `1`, taking `2` and making `3`: the read row keeps its own origin.
Rendered as take-and-republish, the copy `4` of row `1` inherits both premises. -/

def readsOneTakesTwo : Selection Nat := ⟨[2], [1], [3]⟩
def renderedReadsOneTakesTwo : Selection Nat := ⟨[2, 1], [], [3, 4]⟩

theorem read_row_keeps_its_own_origin :
    ProofUse.advance everyProtected ProofUse.initialOrigins readsOneTakesTwo 1 = {1} ∧
      ProofUse.advance everyProtected ProofUse.initialOrigins readsOneTakesTwo 3 = {1, 2} := by
  decide

theorem republished_copy_inherits_every_premise :
    ProofUse.advance everyProtected ProofUse.initialOrigins renderedReadsOneTakesTwo 4 = {1, 2} := by
  decide


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedProcessCounterexamples
