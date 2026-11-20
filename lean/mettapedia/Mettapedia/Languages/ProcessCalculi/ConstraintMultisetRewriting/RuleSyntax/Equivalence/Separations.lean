import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Strong
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Contexts that separate closed bisimilar systems, each named in its statement, at one frame

**A context separates two systems** (`SeparatedBy`) when they are closed bisimilar, the context applies
to both, and after it they are not closed bisimilar. Then they are not congruent
(`not_congruent_of_separatedBy`), for barbs that see neither a renaming of identities nor a change
modulo the knowledge. Every separation below names its context in its statement.

The one-frame instance of the examples (`RuleSyntax.Examples`): first-order terms with numerals as
constants and variables, identities `ℕ`, the may-barbs (`Separates`).

* **A row context** (`row_kind`; the seed is the tree's `none_not_monotone`). The rule "make `5`
  where no `9` is present" and the rule "make `5`" are closed bisimilar from the empty store
  (`spawn_bisimilar`): no `9` ever appears. The context that adds the row `9` at identity `0`
  (`nineRow`) stops the first and not the second.
* **A rule context** (`rule_kind`). One row `7` and two rows `7` with no rules: the may-barbs do not
  count (`sevens_barbs`), so they are closed bisimilar (`sevens_bisimilar`). The context that adds the
  rule "make `5` when exactly one `7` is present" makes the first move and not the second.
* **A tell context** (`tell_kind`). One row labelled by the unknown `x` and one labelled by the unknown
  `y`: every may-barb holds at both (`variable_barbs`), they are closed bisimilar
  (`variables_bisimilar`). After the context that tells `x = 5` only the second may be `6`. A context
  can name the system's unknowns: at one frame, renaming unknowns is not a law.
* **An extend context separates nothing at one frame** (`not_separates_extend`): there extending the
  frame is the identity on states (`extendState_eq_self`), so every context of this kind keeps closed
  bisimilarity (`extend_keeps_bisim`). Whether one separates a pair at an instance with more than one
  frame is open.

So three of the four kinds of basic context separate a pair at one frame, and the fourth cannot there.

**Running beside another system is not a kind of its own**: it is the composite of a tell, a row context
and a rule context (`applyAll_beside`). Beside a system whose rule takes a `1` and makes a `9`, the pair
of the row context is separated through a run of the other system (`beside_separates`); one row context
already separates that pair (`row_kind`), so there the composite adds no separating power over rows.

The earlier controls on closed equivalence, `Observation.CongruenceControls.closed_not_congruence` and
`Race.Triggered.nonport_not_congruence`, are stated for programs that name occurrence identities
(`Race.Triggered.offers`, over fixed selections). Rule syntax cannot name identities; rows with one
label are interchangeable (`rename_congruent`), so their pair of continuations with one label is
congruent here. The phenomenon those controls exhibit, that closed equivalence is not preserved by a
context, is what this module shows for three kinds of context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)

universe uO uT uH uE uOcc uB

section Separating

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  {B : Type uB} (obs : B → State Tm O → Prop)

/-- **A context separates two systems**: they are closed bisimilar, the context applies to both, and
after it they are not closed bisimilar. A basic context is the composite of one. -/
def SeparatedBy (C : List (Basic Tm O E)) (S T : System Tm O) : Prop :=
  Bisimilar X O E obs S T ∧ AppliesAll X C S ∧ AppliesAll X C T ∧
    ¬ Bisimilar X O E obs (applyAll X C S) (applyAll X C T)

variable {X O E obs}

theorem Bisimilar.symm {S T : System Tm O} (related : Bisimilar X O E obs S T) :
    Bisimilar X O E obs T S := by
  obtain ⟨R, bisimulation, r⟩ := related
  exact ⟨R, bisimulation, bisimulation.symm r⟩

/-- Closed bisimilar systems move together. -/
theorem Bisimilar.moves {S T : System Tm O} (related : Bisimilar X O E obs S T)
    (moving : ∃ S', Reduces X O E S S') : ∃ T', Reduces X O E T T' := by
  obtain ⟨R, bisimulation, r⟩ := related
  obtain ⟨S', moved⟩ := moving
  obtain ⟨T', moved', -⟩ := bisimulation.reduces r moved
  exact ⟨T', moved'⟩

/-- Closed bisimilar systems show the same barbs. -/
theorem Bisimilar.barbs {S T : System Tm O} (related : Bisimilar X O E obs S T) (β : B)
    (holds : obs β S.state) : obs β T.state := by
  obtain ⟨R, bisimulation, r⟩ := related
  exact bisimulation.barbs r β holds

/-- **A separated pair is not congruent**, for barbs that see neither a renaming of identities nor a
change modulo the knowledge: the congruence is closed under every context with the same identities
(`Congruent.applyAll_same`) and contained in closed bisimilarity. -/
theorem not_congruent_of_separatedBy
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (modulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {C : List (Basic Tm O E)} {S T : System Tm O} (separated : SeparatedBy X O E obs C S T) :
    ¬ Congruent X O E obs S T := fun related =>
  separated.2.2.2
    (related.applyAll_same invariantRename modulo separated.2.1 separated.2.2.1).bisimilar

end Separating

#print axioms Bisimilar.symm
#print axioms Bisimilar.moves
#print axioms Bisimilar.barbs
#print axioms not_congruent_of_separatedBy

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)

/-! ## Notation and general facts at one frame -/

/-- Systems at one frame. -/
abbrev Sys := System Tm ℕ

/-- The congruence for the may-barbs. -/
abbrev Cong (S T : Sys) : Prop := Congruent X ℕ E (MayBarb X) S T

/-- Closed bisimilarity for the may-barbs. -/
abbrev Bisim (S T : Sys) : Prop := Bisimilar X ℕ E (MayBarb X) S T

/-- A context separates two systems at one frame, for the may-barbs. -/
abbrev Separates (C : List (Basic Tm ℕ E)) (S T : Sys) : Prop := SeparatedBy X ℕ E (MayBarb X) C S T

/-- **A separated pair is not congruent.** -/
theorem not_cong_of_separates {C : List (Basic Tm ℕ E)} {S T : Sys} (separated : Separates C S T) :
    ¬ Cong S T :=
  not_congruent_of_separatedBy (fun π p s => mayBarb_renameState X π p s)
    (fun related p => mayBarb_modulo related p) separated

/-- A system that can move. -/
def Moves (S : Sys) : Prop := ∃ T, Reduces X ℕ E S T

/-- A pattern with no unknowns of its own beyond the frame's. -/
def pat (t : Term atoms) : Pattern Tm := ⟨PUnit.unit, t⟩

/-- The unknown `y`. -/
def y : Term atoms := .var 1

theorem moves_of_congruent {S T : Sys} (related : Cong S T) (moving : Moves S) : Moves T :=
  related.moves moving

/-- A system with no rules does not move. -/
theorem empty_stuck (s : State Tm ℕ) : ¬ Moves ⟨∅, s⟩ := by
  rintro ⟨T, -, f, -, -⟩
  exact Set.notMem_empty _ f.member

/-- An identity missing from a finite set. -/
theorem fresh_identity (W : Finset ℕ) : W.sup id + 1 ∉ W := by
  intro inside
  have bound : W.sup id + 1 ≤ W.sup id := Finset.le_sup (f := id) inside
  omega

/-- The information of a firing with no takes, reads or tells is the knowledge carried along. -/
theorem information_of_empty {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame)
    (take : f.rule.body.take = []) (read : f.rule.body.read = []) (tell : f.rule.body.tell = []) :
    f.information X s = X.applyStore (E.weaken f.ext) s.knowledge := by
  unfold Firing.information Firing.matching Firing.opened RuleInstance.map
  rw [take, read, tell]
  simp

/-- Two systems that never move and show the same barbs are closed bisimilar. -/
theorem bisimilar_of_stuck {S T : Sys} (stuckS : ¬ Moves S) (stuckT : ¬ Moves T)
    (barbs : ∀ β, MayBarb X β S.state ↔ MayBarb X β T.state) : Bisim S T := by
  refine ⟨fun A B => (A = S ∧ B = T) ∨ (A = T ∧ B = S), ⟨?_, ?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · rintro A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) β holds
    · exact (barbs β).mp holds
    · exact (barbs β).mpr holds
  · rintro A B (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) A' moved
    · exact absurd ⟨A', moved⟩ stuckS
    · exact absurd ⟨A', moved⟩ stuckT

/-! ## Adding a row: none queries -/

/-- No row at all. -/
def empty : State Tm ℕ := ⟨PUnit.unit, [], ∅, fun _ => c 0⟩

/-- Make `5` where no `9` is present. -/
def spawnGuarded : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.predicate .none (c 9)], [c 5]⟩, []⟩

/-- Make `5`. -/
def spawn : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [], [c 5]⟩, []⟩

/-- The states the pair reaches: no knowledge, and every present row is `5`. -/
def Fives (s : State Tm ℕ) : Prop := s.knowledge = [] ∧ ∀ o ∈ s.present, s.label o = c 5

theorem spawnGuarded_fresh {P : Program Tm} (s : State Tm ℕ) (f : Firing ℕ E P s.frame)
    (rule : f.rule = spawnGuarded ∨ f.rule = spawn) : f.Fresh X s := by
  apply fresh_of_ground action s f
  intro t member σ
  rcases rule with same | same <;> rw [same] at member <;>
    simp [spawnGuarded, spawn, Rule.terms, checkTerms] at member <;> rcases member with rfl | rfl <;> rfl

/-- A firing of the guarded rule is answered by the same firing of the unguarded one. -/
theorem spawn_answers (s : State Tm ℕ) (ext : PUnit) (ι : Subst atoms) (selection : Selection ℕ)
    (seen : List (Finset ℕ))
    (admitted : (step X ℕ E ({spawnGuarded} : Program Tm)).Admits (s := s)
      ⟨spawnGuarded, Set.mem_singleton _, ext, ι, selection, seen⟩) :
    (step X ℕ E ({spawn} : Program Tm)).Admits (s := s)
      ⟨spawn, Set.mem_singleton _, ext, ι, selection, seen⟩ := by
  obtain ⟨-, shapes, enabled, solvable, -, -⟩ := (admits_iff _).mp admitted
  refine (admits_iff _).mpr ⟨spawnGuarded_fresh s _ (Or.inr rfl), shapes, enabled, solvable,
    fun c member => absurd member List.not_mem_nil, fun q member => ?_⟩
  have lengths := shapes.2.2.2.2.2
  have empty : seen = [] := List.length_eq_zero_iff.mp lengths.symm
  subst empty
  exact absurd member (by simp [Firing.collectOpened, spawn])

/-- At a state where every row is `5`, the unguarded firing is answered by the guarded one. -/
theorem guarded_answers (s : State Tm ℕ) (fives : Fives s) (ext : PUnit) (ι : Subst atoms)
    (selection : Selection ℕ) (seen : List (Finset ℕ))
    (admitted : (step X ℕ E ({spawn} : Program Tm)).Admits (s := s)
      ⟨spawn, Set.mem_singleton _, ext, ι, selection, seen⟩) :
    (step X ℕ E ({spawnGuarded} : Program Tm)).Admits (s := s)
      ⟨spawnGuarded, Set.mem_singleton _, ext, ι, selection, seen⟩ := by
  obtain ⟨-, shapes, enabled, solvable, -, collect⟩ := (admits_iff _).mp admitted
  refine (admits_iff _).mpr ⟨spawnGuarded_fresh s _ (Or.inl rfl), shapes, enabled, solvable,
    fun check member => ?_, collect⟩
  have isNone : check = .predicate .none (c 9) := List.mem_singleton.mp member
  subst isNone
  intro b σ _ o present equated
  have five : s.label o = c 5 := fives.2 o present
  have nine : (c 9 : Term atoms) = c 5 := by
    have h : Subst.applyTerm σ (c 9) = Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (s.label o)) :=
      equated
    rw [five] at h
    exact h
  exact absurd (Term.const.inj nine) (by decide)

/-- The pair's results keep every row `5`. -/
theorem fives_result {P : Program Tm} (s : State Tm ℕ) (fives : Fives s) (f : Firing ℕ E P s.frame)
    (rule : f.rule = spawnGuarded ∨ f.rule = spawn) (admitted : f.Admits X s) : Fives (f.result X s) := by
  obtain ⟨-, ⟨-, -, -, -, produceLength, -⟩, -, -, -, -⟩ := (admits_iff f).mp admitted
  have bodies : f.rule.body.take = [] ∧ f.rule.body.read = [] ∧ f.rule.body.tell = [] ∧
      f.rule.body.produce = [c 5] := by
    rcases rule with same | same <;> rw [same] <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨?_, fun o present => ?_⟩
  · show f.information X s = []
    rw [information_of_empty f bodies.1 bodies.2.1 bodies.2.2.1, fives.1]
    rfl
  · rw [bodies.2.2.2] at produceLength
    obtain ⟨m, made⟩ := List.length_eq_one_iff.mp produceLength.symm
    have opened : (f.opened X).produce = [c 5] := by
      simp only [Firing.opened, RuleInstance.map, bodies.2.2.2, List.map_cons, List.map_nil]
      rfl
    show relabel (f.row X s) f.selection.made (f.opened X).produce o = c 5
    rw [opened, made]
    simp only [relabel]
    split_ifs with same
    · rfl
    · have old : o ∈ s.present := by
        rcases mem_fire.mp present with ⟨old, -⟩ | isMade
        · exact old
        · have isMade' : o ∈ f.selection.made := by simpa [Selection.commit] using isMade
          rw [made, List.mem_singleton] at isMade'
          exact absurd isMade' same
      show Subst.applyTerm (Subst.id atoms) (s.label o) = c 5
      rw [fives.2 o old]
      rfl

/-- **The guarded and the unguarded spawn are closed bisimilar from the empty store.** -/
theorem spawn_bisimilar : Bisim ⟨{spawnGuarded}, empty⟩ ⟨{spawn}, empty⟩ := by
  let R : Sys → Sys → Prop := fun S T => ∃ s, Fives s ∧
    ((S = ⟨{spawnGuarded}, s⟩ ∧ T = ⟨{spawn}, s⟩) ∨ (S = ⟨{spawn}, s⟩ ∧ T = ⟨{spawnGuarded}, s⟩))
  refine ⟨R, ⟨?_, ?_, ?_⟩, empty, ⟨rfl, fun o inside => absurd inside (Finset.notMem_empty o)⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  · rintro S T ⟨s, fives, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨s, fives, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨s, fives, Or.inl ⟨rfl, rfl⟩⟩
  · rintro S T ⟨s, -, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ β holds <;> exact holds
  · rintro S T ⟨s, fives, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ S' ⟨same, f, admitted, reached⟩
    · obtain ⟨rule, member, ext, ι, selection, seen⟩ := f
      have isRule : rule = spawnGuarded := member
      subst isRule
      have answered := spawn_answers s ext ι selection seen admitted
      refine ⟨⟨{spawn}, S'.state⟩, ⟨rfl, _, answered, reached⟩, S'.state, ?_, Or.inl ⟨?_, rfl⟩⟩
      · rw [← reached]
        exact fives_result s fives _ (Or.inl rfl) admitted
      · cases S'
        simp only at same
        rw [same]
    · obtain ⟨rule, member, ext, ι, selection, seen⟩ := f
      have isRule : rule = spawn := member
      subst isRule
      have answered := guarded_answers s fives ext ι selection seen admitted
      refine ⟨⟨{spawnGuarded}, S'.state⟩, ⟨rfl, _, answered, reached⟩, S'.state, ?_, Or.inr ⟨?_, rfl⟩⟩
      · rw [← reached]
        exact fives_result s fives _ (Or.inr rfl) admitted
      · cases S'
        simp only at same
        rw [same]

/-- The unguarded spawn moves at every state with solvable knowledge. -/
theorem spawn_moves {P : Program Tm} (member : spawn ∈ P) (s : State Tm ℕ)
    (solvable : X.Solvable s.knowledge) : Moves ⟨P, s⟩ := by
  let f : Firing ℕ E P s.frame :=
    ⟨spawn, member, PUnit.unit, Subst.id atoms, ⟨[], [], [s.present.sup id + 1]⟩, []⟩
  have admitted : f.Admits X s := by
    refine (admits_iff f).mpr ⟨spawnGuarded_fresh s f (Or.inr rfl),
      ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simpa [f, Selection.commit] using fresh_identity s.present
      · intro q inside
        simp [f, Selection.commit] at inside
    · rw [information_of_empty f rfl rfl rfl]
      obtain ⟨b, σ, solved⟩ := solvable
      refine ⟨b, σ, (Frames.models_applyStore _ _ _).mpr ?_⟩
      exact (Frames.models_congr (fun t => Frames.act_comp_id (X := X) σ t) s.knowledge).mp solved
    · intro check inside
      exact absurd inside List.not_mem_nil
    · intro q inside
      exact absurd inside List.not_mem_nil
  exact ⟨_, reduces_of_admits f admitted⟩

/-- **A row `9` stops the guarded spawn.** -/
theorem guarded_stuck_nine (W : Finset ℕ) (ℓ : ℕ → Term atoms) (nine : ∃ o ∈ W, ℓ o = c 9) :
    ¬ Moves ⟨{spawnGuarded}, ⟨PUnit.unit, [], W, ℓ⟩⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  have isRule : rule = spawnGuarded := member
  subst isRule
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  obtain ⟨o, present, label⟩ := nine
  have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit (Subst.id atoms)
    (fun e inside => absurd inside List.not_mem_nil)
  apply holds o present
  show Subst.applyTerm (Subst.id atoms) (c 9) =
    Subst.applyTerm (Subst.id atoms) (Subst.applyTerm (Subst.id atoms) (ℓ o))
  rw [label]
  rfl

/-- The row context: a row `9` at identity `0`. -/
def nineRow : Basic Tm ℕ E := .rows {0} fun _ _ => c 9

/-- **A row context separates the guarded and the unguarded spawn**: after the row `9` at identity `0`
the unguarded spawn moves and the guarded one does not. -/
theorem row_kind : Separates [nineRow] ⟨{spawnGuarded}, empty⟩ ⟨{spawn}, empty⟩ := by
  have applies : ∀ P : Program Tm, AppliesAll X [nineRow] (⟨P, empty⟩ : Sys) := fun P =>
    .cons (Finset.disjoint_empty_right _) (.nil _)
  refine ⟨spawn_bisimilar, applies _, applies _, fun related => ?_⟩
  have moving : Moves ⟨{spawn}, addRows empty {0} (fun _ => c 9)⟩ :=
    spawn_moves (Set.mem_singleton _) _
      ⟨PUnit.unit, Subst.id atoms, fun e inside => absurd inside List.not_mem_nil⟩
  exact guarded_stuck_nine (∅ ∪ {0}) (fun o => if o ∈ ({0} : Finset ℕ) then c 9 else c 0)
    ⟨0, by simp, by simp⟩ (related.symm.moves moving)

/-- **The guarded and the unguarded spawn are not congruent.** -/
theorem none_separates : ¬ Cong ⟨{spawnGuarded}, empty⟩ ⟨{spawn}, empty⟩ :=
  not_cong_of_separates row_kind

/-! ## Adding a rule: counting -/

/-- One row labelled `7`. -/
def oneSeven : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 7⟩

/-- Two rows labelled `7`. -/
def twoSevens : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, fun _ => c 7⟩

/-- Make `5` when exactly one row is `7`. -/
def countOne : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.count (c 7) 1], [c 5]⟩, []⟩

/-- **May-barbs do not count**: one and two rows `7` show the same barbs. -/
theorem sevens_barbs (β : Pattern Tm) : MayBarb X β oneSeven ↔ MayBarb X β twoSevens := by
  constructor
  · rintro ⟨_, _, b, σ, h, _, equated⟩
    exact ⟨0, by simp [twoSevens], b, σ, h, Frames.models_nil (X := X) σ, equated⟩
  · rintro ⟨_, _, b, σ, h, _, equated⟩
    exact ⟨0, by simp [oneSeven], b, σ, h, Frames.models_nil (X := X) σ, equated⟩

theorem sevens_bisimilar : Bisim ⟨∅, oneSeven⟩ ⟨∅, twoSevens⟩ :=
  bisimilar_of_stuck (empty_stuck _) (empty_stuck _) sevens_barbs

/-- The rows a solution equates with `7` at a store of `7`s are all of them. -/
theorem matchesAt_sevens (σ : Subst atoms) (W : Finset ℕ) :
    matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ
      (fun _ => Subst.applyTerm (Subst.id atoms) (c 7)) W (c 7) = W := by
  ext o
  rw [mem_matchesAt]
  exact ⟨fun inside => inside.1, fun inside => ⟨inside, rfl⟩⟩

theorem countOne_moves : Moves ⟨∅ ∪ {countOne}, oneSeven⟩ := by
  let f : Firing ℕ E (∅ ∪ {countOne}) oneSeven.frame :=
    ⟨countOne, Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id atoms, ⟨[], [], [1]⟩, []⟩
  have admitted : f.Admits X oneSeven := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
      ?_, ⟨PUnit.unit, Subst.id atoms, fun e inside => absurd inside List.not_mem_nil⟩, ?_, ?_⟩
    · apply fresh_of_ground action oneSeven f
      intro t member σ
      simp [f, countOne, Rule.terms, checkTerms] at member
      rcases member with rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, oneSeven]
      · intro q inside
        simp [f, Selection.commit] at inside
    · intro check inside b σ _
      have isCount : check = .count (c 7) 1 := List.mem_singleton.mp inside
      subst isCount
      show (matchesAt X σ (fun _ => Subst.applyTerm (Subst.id atoms) (c 7)) oneSeven.present (c 7)).card = 1
      rw [matchesAt_sevens]
      rfl
    · intro q inside
      exact absurd inside List.not_mem_nil
  exact ⟨_, reduces_of_admits f admitted⟩

theorem countOne_stuck : ¬ Moves ⟨∅ ∪ {countOne}, twoSevens⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = countOne := isRule
  subst same
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  have holds := checks (.count (c 7) 1) (List.mem_singleton_self _) PUnit.unit (Subst.id atoms)
    (fun e inside => absurd inside List.not_mem_nil)
  have counted : (matchesAt X (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms)
      (fun _ => Subst.applyTerm (Subst.id atoms) (c 7)) twoSevens.present (c 7)).card = 1 := holds
  rw [matchesAt_sevens] at counted
  exact absurd counted (by decide)

/-- **A rule context separates one row `7` from two**: after the rule that makes `5` when exactly one
row is `7`, the first moves and the second does not. -/
theorem rule_kind : Separates [.rules {countOne}] ⟨∅, oneSeven⟩ ⟨∅, twoSevens⟩ :=
  ⟨sevens_bisimilar, .cons (Basic.applies_of_ids_empty rfl _) (.nil _),
    .cons (Basic.applies_of_ids_empty rfl _) (.nil _),
    fun related => countOne_stuck (related.moves countOne_moves)⟩

/-- **One row `7` and two rows `7` are not congruent.** -/
theorem count_separates : ¬ Cong ⟨∅, oneSeven⟩ ⟨∅, twoSevens⟩ :=
  not_cong_of_separates rule_kind

/-! ## Telling an equation: the context names an unknown -/

/-- One row labelled by the unknown `x`. -/
def rowX : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => x⟩

/-- One row labelled by the unknown `y`. -/
def rowY : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => y⟩

/-- **A row labelled by a free unknown shows every may-barb.** -/
theorem variable_barbs (v : ℕ) (β : Pattern Tm) :
    MayBarb X β (⟨PUnit.unit, [], {0}, fun _ => .var v⟩ : State Tm ℕ) :=
  ⟨0, Finset.mem_singleton_self 0, PUnit.unit, fun _ => β.term, Subst.id atoms,
    Frames.models_nil _, (Subst.applyTerm_id β.term).symm⟩

theorem variables_bisimilar : Bisim ⟨∅, rowX⟩ ⟨∅, rowY⟩ :=
  bisimilar_of_stuck (empty_stuck _) (empty_stuck _) fun β =>
    ⟨fun _ => variable_barbs 1 β, fun _ => variable_barbs 0 β⟩

/-- **A tell context separates the row `x` from the row `y`**: after `x = 5` the row `y` may be `6`
and the row `x` may not. -/
theorem tell_kind : Separates [.tell fun _ => [(x, c 5)]] ⟨∅, rowX⟩ ⟨∅, rowY⟩ := by
  refine ⟨variables_bisimilar, .cons (Basic.applies_of_ids_empty rfl _) (.nil _),
    .cons (Basic.applies_of_ids_empty rfl _) (.nil _), fun related => ?_⟩
  have atY : MayBarb X (pat (c 6)) (tellState rowY [(x, c 5)]) := by
    refine ⟨0, Finset.mem_singleton_self 0, PUnit.unit, fun v => if v = 0 then c 5 else c 6,
      Subst.id atoms, ?_, ?_⟩
    · intro e inside
      simp only [tellState, rowY, List.nil_append, List.mem_singleton] at inside
      subst inside
      rfl
    · rfl
  obtain ⟨o, -, b, σ, h, known, equated⟩ := related.symm.barbs (pat (c 6)) atY
  have bound : σ 0 = c 5 := known (x, c 5) (List.mem_singleton_self _)
  have six : σ 0 = Subst.applyTerm h (c 6) := equated
  rw [bound] at six
  exact absurd (Term.const.inj six) (by decide)

/-- **The row `x` and the row `y` are not congruent.** -/
theorem tell_separates : ¬ Cong ⟨∅, rowX⟩ ⟨∅, rowY⟩ :=
  not_cong_of_separates tell_kind

/-! ## Extending the frame separates nothing at one frame -/

/-- **At one frame, extending the frame changes no state.** -/
theorem extendState_eq_self (s : State Tm ℕ) (e : E.Ext s.frame) : extendState X E s e = s := by
  obtain ⟨frame, knowledge, present, label⟩ := s
  show (⟨frame, X.applyStore (X.id frame) knowledge, present, fun o => X.act (X.id frame) (label o)⟩ :
    State Tm ℕ) = ⟨frame, knowledge, present, label⟩
  rw [Frames.applyStore_id]
  congr 1
  funext o
  exact X.act_id (label o)

/-- **A context of the extend kind is the identity on systems at one frame.** -/
theorem extend_apply_eq_self (extension : (a : PUnit) → E.Ext a) (S : Sys) :
    (Basic.extend (Tm := Tm) (O := ℕ) extension).apply X S = S := by
  obtain ⟨P, s⟩ := S
  show (⟨P, extendState X E s (extension s.frame)⟩ : Sys) = ⟨P, s⟩
  rw [extendState_eq_self]

/-- **A context of the extend kind keeps closed bisimilarity at one frame.** -/
theorem extend_keeps_bisim (extension : (a : PUnit) → E.Ext a) {S T : Sys} (related : Bisim S T) :
    Bisim ((Basic.extend (Tm := Tm) (O := ℕ) extension).apply X S)
      ((Basic.extend (Tm := Tm) (O := ℕ) extension).apply X T) := by
  rw [extend_apply_eq_self, extend_apply_eq_self]
  exact related

/-- **No context of the extend kind separates any pair at one frame.** -/
theorem not_separates_extend (extension : (a : PUnit) → E.Ext a) (S T : Sys) :
    ¬ Separates [.extend extension] S T :=
  fun ⟨related, _, _, separated⟩ => separated (extend_keeps_bisim extension related)

/-! ## Running beside another system: a composite, not a kind of its own -/

/-- Take a `1`, make a `9`. -/
def feeder : Rule Tm := ⟨PUnit.unit, ⟨[c 1], [], [], [], [c 9]⟩, []⟩

/-- The other system: the rule `feeder` and a row `1` at identity `0`, with no knowledge. -/
def besideFeeder : List (Basic Tm ℕ E) :=
  beside {feeder} {0} (fun _ _ => c 1) (fun _ => [])

/-- **One row `9` at identity `1` stops both rules**: the guarded spawn sees the `9`, and the feeder
finds no `1`. -/
theorem nine_stuck (s : State Tm ℕ) (present : s.present = {1})
    (nine : ∀ σ : Subst atoms, Subst.applyTerm σ (s.label 1) = c 9) :
    ¬ Moves ⟨{spawnGuarded} ∪ {feeder}, s⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  obtain ⟨-, ⟨-, -, takeLength, -, -, -⟩, enabled, ⟨b, σ, solved⟩, checks, -⟩ :=
    (admits_iff _).mp admitted
  rcases (Set.mem_union _ _ _).mp member with isGuarded | isFeeder
  · have same : rule = spawnGuarded := isGuarded
    subst same
    have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) b σ solved
    apply holds 1 (by rw [present]; exact Finset.mem_singleton_self 1)
    show Subst.applyTerm σ (c 9) = Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (s.label 1))
    rw [Subst.applyTerm_id, nine σ]
    rfl
  · have same : rule = feeder := isFeeder
    subst same
    obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp takeLength.symm
    have taken' : selection.taken = [o] := taken
    have inside : o ∈ s.present := enabled.taken_subset (by simp [Selection.commit, taken'])
    rw [present] at inside
    have one : o = 1 := Finset.mem_singleton.mp inside
    subst one
    have equated := Firing.take_solved _ solved (p := X.act ι (c 1)) (o := 1) (by
      show (X.act ι (c 1), 1) ∈ [X.act ι (c 1)].zip selection.taken
      rw [taken']
      exact List.mem_cons_self)
    have one' : Subst.applyTerm σ (Subst.applyTerm ι (c 1)) =
        Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (s.label 1)) := equated
    rw [Subst.applyTerm_id, nine σ] at one'
    exact absurd (Term.const.inj one') (by decide)

/-- **The feeder fires** beside the guarded spawn, and leaves one row `9`, at identity `1`. -/
theorem feeder_fires : ∃ X₁ : Sys,
    Reduces X ℕ E (applyAll X besideFeeder ⟨{spawnGuarded}, empty⟩) X₁ ∧
      X₁.program = {spawnGuarded} ∪ {feeder} ∧ X₁.state.present = {1} ∧
      ∀ σ : Subst atoms, Subst.applyTerm σ (X₁.state.label 1) = c 9 := by
  let s := (applyAll X besideFeeder ⟨({spawnGuarded} : Program Tm), empty⟩).state
  let f : Firing ℕ E ({spawnGuarded} ∪ {feeder}) s.frame :=
    ⟨feeder, Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩
  have admitted : f.Admits X s := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl,
      rfl⟩, ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action s f
      intro t member σ
      simp [f, feeder, Rule.terms] at member
      rcases member with rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, s, Selection.commit, besideFeeder, applyAll_beside, empty]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, s, Selection.commit, besideFeeder, applyAll_beside, empty]
      · intro q inside
        simp [f, Selection.commit] at inside
    · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++
          [(Subst.applyTerm (Subst.id atoms) (c 1),
            Subst.applyTerm (Subst.id atoms) (if (0 : ℕ) ∈ ({0} : Finset ℕ) then c 1 else c 0))] ++
          [] ++ [] := inside
      simp only [List.nil_append, List.append_nil, List.mem_singleton] at unfolded
      subst unfolded
      rfl
    · intro check inside
      exact absurd inside List.not_mem_nil
    · intro q inside
      exact absurd inside List.not_mem_nil
  refine ⟨⟨{spawnGuarded} ∪ {feeder}, f.result X s⟩, ⟨rfl, f, admitted, rfl⟩, rfl, ?_, fun σ => rfl⟩
  show fire (∅ ∪ {0}) ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Unit)) = {1}
  decide

/-- **Running beside the feeder separates the guarded and the unguarded spawn**, through a run of the
feeder: it makes a row `9`, which stops the guarded side only. Running beside is the composite of a
tell, a row context and a rule context (`applyAll_beside`); on this pair it adds no separating power
over rows, since the row context `nineRow` alone separates the same pair (`row_kind`). -/
theorem beside_separates : Separates besideFeeder ⟨{spawnGuarded}, empty⟩ ⟨{spawn}, empty⟩ := by
  have applies : ∀ P : Program Tm, AppliesAll X besideFeeder (⟨P, empty⟩ : Sys) := fun P =>
    (appliesAll_beside_iff X {feeder} {0} (fun _ _ => c 1) (fun _ => []) ⟨P, empty⟩).mpr
      (by simp [empty])
  refine ⟨spawn_bisimilar, applies _, applies _, fun related => ?_⟩
  obtain ⟨X₁, fired, program₁, present₁, nine₁⟩ := feeder_fires
  obtain ⟨R, bisimulation, r⟩ := related
  obtain ⟨T', moved, related'⟩ := bisimulation.reduces r fired
  obtain ⟨program, g, admittedG, reached⟩ := moved
  have spawnIn : spawn ∈ T'.program := by
    rw [program]
    exact Or.inl (Set.mem_singleton _)
  have solvable : X.Solvable T'.state.knowledge := by
    rw [← reached]
    exact ((admits_iff g).mp admittedG).2.2.2.1
  obtain ⟨T'', movedT⟩ : Moves ⟨T'.program, T'.state⟩ := spawn_moves spawnIn T'.state solvable
  obtain ⟨X₂, movedX, -⟩ := bisimulation.reduces (bisimulation.symm related') movedT
  obtain ⟨P₁, s₁⟩ := X₁
  simp only at program₁ present₁ nine₁
  subst program₁
  exact nine_stuck s₁ present₁ nine₁ ⟨X₂, movedX⟩

#print axioms empty_stuck
#print axioms fresh_identity
#print axioms spawn_answers
#print axioms guarded_answers
#print axioms fives_result
#print axioms spawn_bisimilar
#print axioms not_cong_of_separates
#print axioms spawn_moves
#print axioms guarded_stuck_nine
#print axioms row_kind
#print axioms none_separates
#print axioms sevens_barbs
#print axioms sevens_bisimilar
#print axioms countOne_moves
#print axioms countOne_stuck
#print axioms rule_kind
#print axioms count_separates
#print axioms variable_barbs
#print axioms variables_bisimilar
#print axioms tell_kind
#print axioms tell_separates
#print axioms extendState_eq_self
#print axioms extend_apply_eq_self
#print axioms extend_keeps_bisim
#print axioms not_separates_extend
#print axioms nine_stuck
#print axioms feeder_fires
#print axioms beside_separates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame
