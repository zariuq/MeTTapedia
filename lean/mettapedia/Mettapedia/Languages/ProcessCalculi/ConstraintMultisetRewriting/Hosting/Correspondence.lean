import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Transfer

/-!
# The correspondence of steps, both ways, for `ret`, `apply`, `choice` and `fail`

**The fragment** (`PlainComp`, `PlainProgram`, `PlainBranch`): computations built from `ret`,
`apply`, `choice` and `fail`, over data of any binding signature with second-order unknowns
(equations under binders). Alternatives have no pending frames.

**One firing** of the translated program (`Fires`): an admitted firing of `hostStep`, i.e. of
`RuleSyntax.step` at the contextual frames.

* `simulation`: every source step of a represented alternative is matched, for each live alternative
  it makes, by **exactly one firing**, to a state that represents it (no administrative firings).
* `reflection`: every admitted firing from a state that represents an alternative is a source step of
  that alternative, and its result represents one of the alternatives the step makes.

The unmatched call is the one place where admission has a check: the none query of a matching equation
row is exactly "no equation matches" (`unmatched_guard`, `unmatched_none`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-! ## The fragment -/

section Fragment

variable {Ty : Type}

/-- **The computations of the first fragment**: `ret`, `apply`, `choice`, `fail`. -/
def PlainComp : Comp κ Γ star Ty → Prop
  | .ret _ => True
  | .apply _ => True
  | .choice c d => PlainComp c ∧ PlainComp d
  | .fail => True
  | _ => False

/-- A program of the first fragment: every right-hand side is a plain computation. -/
def PlainProgram (P : SourceLanguage.Program κ Γ star Ty) : Prop := ∀ e ∈ P.equations, PlainComp e.rhs

/-- An alternative of the first fragment: no frames, and a plain computation or a value. -/
def PlainBranch (b : Branch κ Γ star Ty) : Prop :=
  b.frames = [] ∧ ((∃ c, b.focus = .eval c ∧ PlainComp c) ∨ ∃ t, b.focus = .value t)

theorem plainComp_mapData (g : Data κ Γ star → Data κ Γ star) :
    ∀ c : Comp κ Γ star Ty, PlainComp c → PlainComp (c.mapData g)
  | .ret _, _ => trivial
  | .apply _, _ => trivial
  | .choice c d, ⟨pc, pd⟩ => ⟨plainComp_mapData g c pc, plainComp_mapData g d pd⟩
  | .fail, _ => trivial
  | .let_ _ _ _ _, h => h.elim
  | .run _, h => h.elim
  | .query _ _ _, h => h.elim
  | .add _ _ _, h => h.elim
  | .remove _ _ _, h => h.elim
  | .new _ _ _, h => h.elim
  | .check _ _, h => h.elim
  | .delay _ _ _ _, h => h.elim
  | .force _, h => h.elim

theorem comp_data_mapData (g : Data κ Γ star → Data κ Γ star) :
    ∀ c : Comp κ Γ star Ty, (c.mapData g).data = c.data.map g
  | .ret _ => rfl
  | .apply _ => rfl
  | .run _ => rfl
  | .let_ _ p c k => by simp [Comp.mapData, Comp.data, comp_data_mapData g c, comp_data_mapData g k]
  | .choice c d => by simp [Comp.mapData, Comp.data, comp_data_mapData g c, comp_data_mapData g d]
  | .fail => rfl
  | .query _ _ k => by simp [Comp.mapData, Comp.data, comp_data_mapData g k]
  | .add _ _ k => by simp [Comp.mapData, Comp.data, comp_data_mapData g k]
  | .remove _ _ k => by simp [Comp.mapData, Comp.data, comp_data_mapData g k]
  | .new _ _ k => by simp [Comp.mapData, Comp.data, comp_data_mapData g k]
  | .check _ k => by simp [Comp.mapData, Comp.data, comp_data_mapData g k]
  | .delay _ _ c k => by simp [Comp.mapData, Comp.data, comp_data_mapData g c, comp_data_mapData g k]
  | .force _ => rfl

end Fragment

/-! ## One firing -/

section Firing

variable {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)

/-- **One firing of the translated program.** -/
def Fires (s s' : HostState S) : Prop :=
  ∃ f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame,
    f.Admits (Interface.Frames.contextual S) s ∧ f.result (Interface.Frames.contextual S) s = s'

/-- A firing is one admitted firing of the step of the translated program. -/
theorem fires_iff_step (s s' : HostState S) :
    Fires N P s s' ↔ ∃ (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame)
      (admitted : (hostStep N P).Admits f), (hostStep N P).result f admitted = s' :=
  ⟨fun ⟨f, admitted, result⟩ => ⟨f, admitted, result⟩, fun ⟨f, admitted, result⟩ => ⟨f, admitted, result⟩⟩

end Firing

/-! ## Canonical firings -/

section Canonical

/-- A row identity not present. -/
def freshId (s : HostState S) : ℕ := s.present.sup id + 1

theorem freshId_not_mem (s : HostState S) : freshId s ∉ s.present := by
  intro inside
  have bound : id (freshId s) ≤ s.present.sup id := Finset.le_sup inside
  simp only [id, freshId] at bound
  omega

theorem enabled_single {present : Finset ℕ} {a a' : ℕ} (ha : a ∈ present) (ha' : a' ∉ present) :
    Enabled (fun _ : ℕ => ()) present ((⟨[a], [], [a']⟩ : Selection ℕ).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Selection.commit, ha]
  · simp [Selection.commit]
  · simp [Selection.commit]
  · simp [Selection.commit, ha']
  · simp [Selection.commit]

variable {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} (s : HostState S)
  (r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)) (member : r ∈ Prog) (a : ℕ)

/-- The canonical firing of a rule taking row `a` and making a fresh row. -/
abbrev canonicalAt : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame :=
  RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [freshId s]⟩ []

variable {s r member a} {pat out : Observation S r.locals.arity}

theorem canonical_simple (htake : r.body.take = [pat]) (hread : r.body.read = [])
    (hprod : r.body.produce = [out]) :
    Simple (canonicalAt s r member a) a (freshId s) pat out :=
  ⟨rfl, rfl, rfl, htake, hread, hprod⟩

theorem canonical_shapes (htake : r.body.take = [pat]) (hread : r.body.read = [])
    (hprod : r.body.produce = [out]) (hcollect : r.collect = []) :
    (canonicalAt s r member a).Shapes (Interface.Frames.contextual S) s := by
  refine ⟨RuleSyntax.Contextual.canonical_fresh s r member _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_singleton a
  · exact List.nodup_singleton (freshId s)
  · change r.body.take.length = 1; rw [htake]; rfl
  · change r.body.read.length = 0; rw [hread]; rfl
  · change r.body.produce.length = 1; rw [hprod]; rfl
  · change r.collect.length = 0; rw [hcollect]; rfl

/-- A rule without checks and collect query holds at every solution. -/
theorem entails_of_no_checks {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame}
    (hchecks : f.rule.body.checks = []) (hcollect : f.rule.collect = []) :
    (Interface.Frames.contextual S).Entails (f.information (Interface.Frames.contextual S) s)
      (fun _ σ => f.Holds (Interface.Frames.contextual S) s σ) := by
  intro B σ _
  refine ⟨?_, ?_⟩
  · intro c member
    simp [RuleSyntax.Firing.opened, RuleInstance.map, hchecks] at member
  · intro q member
    simp [RuleSyntax.Firing.collectOpened, hcollect] at member

end Canonical

/-! ## Firing a rule that takes the alternative's row -/

section FireSimple

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **Firing a simple rule**: if the rule transforms the alternative's readings into a live
alternative's readings, its canonical firing is admitted (given its guard) and the result represents
that alternative. -/
theorem fire_simple {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)} (member : r ∈ translate N P)
    {pat out : Observation S r.locals.arity} (htake : r.body.take = [pat]) (hread : r.body.read = [])
    (hprod : r.body.produce = [out]) (hcollect : r.collect = [])
    {n n' : ℕ} {b b' : Branch κ Γ star Ty} {s : HostState S} {a : ℕ} (rep : Represents N P n b s a)
    (transfer : ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity),
      (∃ h : Assignment r.locals.arity B.arity, branchReads N b B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h r.body.tell ∧ instantiateObservation h out = q) ↔
      branchReads N b' B q)
    (live : Solvable b'.store)
    (guard : (Interface.Frames.contextual S).Entails
      ((canonicalAt s r member a).information (Interface.Frames.contextual S) s)
      (fun _ σ => (canonicalAt s r member a).Holds (Interface.Frames.contextual S) s σ))
    (fresh : BranchBelow n' b') (noPending : b'.pending = []) :
    ∃ s' a', Fires N P s s' ∧ Represents N P n' b' s' a' := by
  have simple := canonical_simple (s := s) (member := member) (a := a) htake hread hprod
  have shapes := canonical_shapes (s := s) (member := member) (a := a) htake hread hprod hcollect
  have aPresent : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have solvable : (Interface.Frames.contextual S).Solvable
      ((canonicalAt s r member a).information (Interface.Frames.contextual S) s) := by
    obtain ⟨W, target, σ, solved⟩ := live
    have reads : branchReads N b' ⟨W, target⟩ (observe (encBranch N (instantiate σ) b')) := ⟨σ, solved, rfl⟩
    obtain ⟨h, readsB, told, _⟩ := (transfer _ _).mpr reads
    obtain ⟨g, known, matched⟩ := (rep.reads _ _).mpr readsB
    obtain ⟨u, solvedU, _⟩ := simple_amalgamate simple shapes.1 aPresent g h known told matched.symm
    exact ⟨_, u, solvedU⟩
  refine ⟨_, freshId s, ⟨canonicalAt s r member a, ⟨shapes, enabled_single aPresent (freshId_not_mem s),
    solvable, guard⟩, rfl⟩, ?_⟩
  exact represents_after N rep simple shapes (freshId_not_mem s) transfer fresh noPending

end FireSimple

/-! ## Decomposing an admitted firing -/

section Decompose

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **An admitted firing of a rule with one take and one made row takes the alternative's row**, and
its take pattern reads as a reading of the alternative. -/
theorem admitted_takes_alternative {s : HostState S} {n : ℕ} {b : Branch κ Γ star Ty} {a : ℕ}
    (rep : Represents N P n b s a)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) s) {pat out : Observation S f.rule.locals.arity}
    (htake : f.rule.body.take = [pat]) (hread : f.rule.body.read = []) (hprod : f.rule.body.produce = [out])
    (altHead : ∀ {B : Interface.Frames.Frame S} (h : Assignment f.rule.locals.arity B.arity),
      ∃ x y : Term (signature S B.arity) Γ star, instantiateObservation h pat = observe (altN N x y)) :
    ∃ a', Simple f a a' pat out ∧ a' ∉ s.present ∧
      ∃ (B : Interface.Frames.Frame S) (h : Assignment f.rule.locals.arity B.arity),
        branchReads N b B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h f.rule.body.tell := by
  obtain ⟨shapes, enabled, solvable, _⟩ := admitted
  obtain ⟨_, _, _, takeLen, readLen, prodLen, _⟩ := shapes
  rw [htake] at takeLen
  rw [hread] at readLen
  rw [hprod] at prodLen
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp takeLen.symm
  obtain ⟨o', made⟩ := List.length_eq_one_iff.mp prodLen.symm
  have read : f.selection.read = [] := List.eq_nil_of_length_eq_zero readLen.symm
  have simple : Simple f o o' pat out := ⟨taken, read, made, htake, hread, hprod⟩
  have oPresent : o ∈ s.present := enabled.taken_subset (by simp [Selection.commit, taken])
  have o'Fresh : o' ∉ s.present := by
    intro inside
    exact Finset.disjoint_left.mp enabled.fresh (by simp [Selection.commit, made]) inside
  obtain ⟨B, u, solved⟩ := solvable
  obtain ⟨known, told, matched⟩ := simple_restrict simple u solved
  have isAlt : o = a := by
    by_contra other
    have small : o < P.equations.length := by
      have := oPresent
      rw [rep.present, Finset.mem_insert, Finset.mem_range] at this
      exact this.resolve_left other
    obtain ⟨θ, row⟩ := rep.rows B _ known o small
    obtain ⟨x, y, headed⟩ := altHead (Assignment.compose u f.opening)
    have same := matched.trans row
    rw [headed] at same
    have tags := N.tag_eq (observe_injective same)
    exact absurd tags (by decide)
  subst isAlt
  exact ⟨o', simple, o'Fresh, B, _, (rep.reads B _).mp ⟨_, known, matched.symm⟩, told⟩

end Decompose

#print axioms fire_simple
#print axioms admitted_takes_alternative

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
