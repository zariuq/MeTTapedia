import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceReadouts

/-!
# Controls for the class readout

Classes are those of the renaming transport: configurations related by a renaming that keeps every
label (`AnnotatedRuns.RenamingIso`).

## `a.0 + a.0` against `a.0` (`Twice.twice_control`)

Labels are rules, every occurrence carries `τ`, and one rule takes `τ` and makes `τ`. At `{a}` two
firings take `a`, one making `k₁` and one making `k₂`; at `{b}` one firing takes `b` and makes `k`.
The two starts are answer-respecting bisimilar. R61's `collect` reports two distinct configurations
for the first and one for the second; the class readout reports one class for both, and the class
bag counts it twice and once.

## Bisimilarity alone does not fix the answers (`Labels.answerClasses_differ`)

A program that fires nothing makes every two configurations bisimilar; `{x}` and `{y}`, with
different labels, have different answer classes. The answer system observes what plain bisimilarity
does not.

## A finite alphabet is not equivariant (`Equivariance.not_equivariant`)

The single firing that takes `a` and makes `k` is offered, and the one that takes `b` is not. `{a}`
and `{b}` are related by a label-keeping renaming and have different answer classes, so the program
is not equivariant.

## An equivariant finite alphabet (`Symmetric.symmetric_control`)

Two firings take `x` or `y` together with a gate `g` whose label differs. Every label-keeping
renaming fixes the gate and permutes `x, y`, so the program is equivariant, and the starts `{x, g}`
and `{y, g}` have equal class sets at their finished budgets (`classSet_eq_of_renamingIso`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ReadoutControls

open AnnotatedRuns (Firing RenamingIso renamingTransport renameConfiguration)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uT uS

/-! ## `a.0 + a.0` against `a.0` -/

namespace Twice

/-- Occurrence identities. -/
inductive Site
  | a | b | k₁ | k₂ | k
  deriving DecidableEq

variable {T : Type uT} {S : Type uS} (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The rule: take `τ`, make `τ`. -/
def rule : RuleInstance T := ⟨[τ], [], [], [], [τ]⟩

/-- The firing of the rule that takes `o` and makes `o'`. -/
def firing (o o' : Site) : Firing T S Site := ⟨rule τ, [], ⟨[o], [], [o']⟩⟩

def f₁ : Firing T S Site := firing τ .a .k₁
def f₂ : Firing T S Site := firing τ .a .k₂
def f₃ : Firing T S Site := firing τ .b .k

def alphabet : List (Firing T S Site) := [f₁ τ, f₂ τ, f₃ τ]

/-- **Labels are rules.** -/
def offers (r : RuleInstance T) (f : Firing T S Site) : Prop := f ∈ alphabet τ ∧ f.rule = r

/-- `a.0 + a.0`. -/
def twice : Configuration T Site := ⟨[], {.a}⟩
/-- `a.0`. -/
def once : Configuration T Site := ⟨[], {.b}⟩
def end₁ : Configuration T Site := ⟨[(τ, τ)], {.k₁}⟩
def end₂ : Configuration T Site := ⟨[(τ, τ)], {.k₂}⟩
def end₀ : Configuration T Site := ⟨[(τ, τ)], {.k}⟩

theorem config_eq {C D : Configuration T Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

theorem reflexive_one : Reflexive [(τ, τ)] := by
  intro e member
  simp only [List.mem_singleton] at member
  subst member
  rfl

theorem ground : ∀ f ∈ alphabet (S := S) τ, Ground (label τ) f := by
  intro f member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem alphabet_nodup : (alphabet (S := S) τ).Nodup := by
  simp [alphabet, f₁, f₂, f₃, firing]

theorem covers (f : Firing T S Site) : f ∈ alphabet τ ↔ ∃ r, offers τ r f :=
  ⟨fun member => ⟨f.rule, member, rfl⟩, fun ⟨_, member, _⟩ => member⟩

variable (A : SubstitutionAction T S)

theorem valid_iff {f : Firing T S Site} (member : f ∈ alphabet τ) {C : Configuration T Site}
    (refl : Reflexive C.equations) :
    f.Valid A (label τ) C ↔ Enabled (label τ) C.present (f.selection.commit (T := T)) :=
  (ground τ f member).valid_iff A refl

theorem result_f₁ : (f₁ (S := S) τ).result (label τ) twice = end₁ τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_f₂ : (f₂ (S := S) τ).result (label τ) twice = end₂ τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_f₃ : (f₃ (S := S) τ).result (label τ) once = end₀ τ := config_eq rfl (of_decide_eq_true rfl)

theorem mem_f₁ : f₁ (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_f₂ : f₂ (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_f₃ : f₃ (S := S) τ ∈ alphabet τ := by simp [alphabet]

theorem moves_twice {r : RuleInstance T} {X : Configuration T Site} :
    Moves A (label τ) (offers (S := S) τ) twice r X ↔ r = rule τ ∧ (X = end₁ τ ∨ X = end₂ τ) := by
  constructor
  · rintro ⟨f, ⟨member, rfl⟩, valid, rfl⟩
    rw [valid_iff τ A member reflexive_nil] at valid
    simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨rfl, .inl (result_f₁ τ)⟩
    · exact ⟨rfl, .inr (result_f₂ τ)⟩
    · exact absurd valid (of_decide_eq_false rfl)
  · rintro ⟨rfl, rfl | rfl⟩
    · exact ⟨f₁ τ, ⟨mem_f₁ τ, rfl⟩, (valid_iff τ A (mem_f₁ τ) reflexive_nil).mpr (of_decide_eq_true rfl),
        (result_f₁ τ).symm⟩
    · exact ⟨f₂ τ, ⟨mem_f₂ τ, rfl⟩, (valid_iff τ A (mem_f₂ τ) reflexive_nil).mpr (of_decide_eq_true rfl),
        (result_f₂ τ).symm⟩

theorem moves_once {r : RuleInstance T} {X : Configuration T Site} :
    Moves A (label τ) (offers (S := S) τ) once r X ↔ r = rule τ ∧ X = end₀ τ := by
  constructor
  · rintro ⟨f, ⟨member, rfl⟩, valid, rfl⟩
    rw [valid_iff τ A member reflexive_nil] at valid
    simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact absurd valid (of_decide_eq_false rfl)
    · exact absurd valid (of_decide_eq_false rfl)
    · exact ⟨rfl, result_f₃ τ⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨f₃ τ, ⟨mem_f₃ τ, rfl⟩, (valid_iff τ A (mem_f₃ τ) reflexive_nil).mpr (of_decide_eq_true rfl),
      (result_f₃ τ).symm⟩

/-- A configuration whose equations are `[(τ, τ)]` and where no member of the alphabet is enabled is
dead. -/
theorem dead_of {X : Configuration T Site} (equations : X.equations = [(τ, τ)])
    (none : ∀ f ∈ alphabet (S := S) τ, ¬ Enabled (label τ) X.present (f.selection.commit (T := T))) :
    Dead A (label τ) (offers (S := S) τ) X := by
  rintro r Y ⟨f, ⟨member, _⟩, valid, _⟩
  rw [valid_iff τ A member (equations ▸ reflexive_one τ)] at valid
  exact none f member valid

theorem dead_end₁ : Dead A (label τ) (offers (S := S) τ) (end₁ τ) := by
  refine dead_of τ A rfl fun f member => ?_
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact of_decide_eq_false rfl

theorem dead_end₂ : Dead A (label τ) (offers (S := S) τ) (end₂ τ) := by
  refine dead_of τ A rfl fun f member => ?_
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact of_decide_eq_false rfl

theorem dead_end₀ : Dead A (label τ) (offers (S := S) τ) (end₀ τ) := by
  refine dead_of τ A rfl fun f member => ?_
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact of_decide_eq_false rfl

/-- The class of a configuration up to label-keeping renaming. -/
abbrev cls : Configuration T Site → (renamingTransport A (label τ)).StateClass :=
  Interface.Transport.StateClass.mk (renamingTransport A (label τ))

theorem renamed (o o' : Site) (C D : Configuration T Site) (equations : C.equations = D.equations)
    (present : C.present.map (Equiv.swap o o').toEmbedding = D.present) :
    cls τ A C = cls τ A D :=
  (Interface.Transport.StateClass.mk_eq_mk_iff (renamingTransport A (label τ))).mpr
    ⟨(⟨Equiv.swap o o', fun _ => rfl, ⟨fun σ => by rw [← equations]; exact Iff.rfl, present⟩⟩ :
      RenamingIso A (label τ) C D)⟩

theorem class_end₁ : cls τ A (end₁ τ) = cls τ A (end₀ τ) :=
  renamed τ A .k₁ .k _ _ rfl (by simp [end₁, end₀])

theorem class_end₂ : cls τ A (end₂ τ) = cls τ A (end₀ τ) :=
  renamed τ A .k₂ .k _ _ rfl (by simp [end₂, end₀])

/-- **`a.0 + a.0` and `a.0` are answer-respecting bisimilar.** -/
theorem answerBisimilar : AnswerBisimilar A (label τ) (offers (S := S) τ) (cls τ A) twice once := by
  refine ⟨fun X Y => (X = twice ∧ Y = once) ∨ ((X = end₁ τ ∨ X = end₂ τ) ∧ Y = end₀ τ),
    ⟨?_, ?_, ?_⟩, .inl ⟨rfl, rfl⟩⟩
  · rintro X Y (⟨rfl, rfl⟩ | ⟨rfl | rfl, rfl⟩) r X' moved
    · obtain ⟨rfl, ends⟩ := (moves_twice τ A).mp moved
      exact ⟨end₀ τ, (moves_once τ A).mpr ⟨rfl, rfl⟩, .inr ⟨ends, rfl⟩⟩
    · exact absurd moved (dead_end₁ τ A r X')
    · exact absurd moved (dead_end₂ τ A r X')
  · rintro X Y (⟨rfl, rfl⟩ | ⟨rfl | rfl, rfl⟩) r Y' moved
    · obtain ⟨rfl, rfl⟩ := (moves_once τ A).mp moved
      exact ⟨end₁ τ, (moves_twice τ A).mpr ⟨rfl, .inl rfl⟩, .inr ⟨.inl rfl, rfl⟩⟩
    · exact absurd moved (dead_end₀ τ A r Y')
    · exact absurd moved (dead_end₀ τ A r Y')
  · rintro X Y (⟨rfl, rfl⟩ | ⟨rfl | rfl, rfl⟩) b
    · have liveTwice : ¬ Dead A (label τ) (offers (S := S) τ) twice := fun dead =>
        dead (rule τ) (end₁ τ) ((moves_twice τ A).mpr ⟨rfl, .inl rfl⟩)
      have liveOnce : ¬ Dead A (label τ) (offers (S := S) τ) once := fun dead =>
        dead (rule τ) (end₀ τ) ((moves_once τ A).mpr ⟨rfl, rfl⟩)
      exact ⟨fun observed => absurd observed.1 liveTwice, fun observed => absurd observed.1 liveOnce⟩
    · exact and_congr (iff_of_true (dead_end₁ τ A) (dead_end₀ τ A)) (by rw [class_end₁])
    · exact and_congr (iff_of_true (dead_end₂ τ A) (dead_end₀ τ A)) (by rw [class_end₂])

/-! ### The search -/

/-- The search of the program. -/
noncomputable abbrev search := (alternatives A (label τ) (alphabet τ)).space

theorem next_twice :
    ((alternatives A (label τ) (alphabet τ)).next twice).map (fun g => g.1.1) = [f₁ τ, f₂ τ] := by
  rw [next_map_of_ground (ground τ) reflexive_nil]
  rfl

theorem next_once :
    ((alternatives A (label τ) (alphabet τ)).next once).map (fun g => g.1.1) = [f₃ (S := S) τ] := by
  rw [next_map_of_ground (ground τ) reflexive_nil]
  rfl

theorem next_end₁ :
    ((alternatives A (label τ) (alphabet (S := S) τ)).next (end₁ τ)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground τ) (reflexive_one τ)]
  rfl

theorem next_end₂ :
    ((alternatives A (label τ) (alphabet (S := S) τ)).next (end₂ τ)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground τ) (reflexive_one τ)]
  rfl

theorem next_end₀ :
    ((alternatives A (label τ) (alphabet (S := S) τ)).next (end₀ τ)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground τ) (reflexive_one τ)]
  rfl

theorem approx_twice : (search τ A).approx 2 (.inr twice) = ⟨{end₁ τ, end₂ τ}, .finished⟩ := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_twice τ A)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, result_f₁, result_f₂,
    Search.Space.approx_succ, unfold_of_nil (next_end₁ τ A), unfold_of_nil (next_end₂ τ A),
    Search.Space.approx_inl]
  rfl

theorem approx_once : (search τ A).approx 2 (.inr once) = ⟨{end₀ τ}, .finished⟩ := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_once τ A)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, result_f₃,
    Search.Space.approx_succ, unfold_of_nil (next_end₀ τ A), Search.Space.approx_inl]
  rfl

/-- **`a.0 + a.0` against `a.0`.** The two starts are answer-respecting bisimilar. At budget 2 both
searches are finished; `collect` reports two distinct configurations for the first and one for the
second, while the class readout reports the same class set, and the class bag counts the one class
twice and once. -/
theorem twice_control :
    AnswerBisimilar A (label τ) (offers (S := S) τ) (cls τ A) twice once ∧
    Search.Outcome.collect ((search τ A).approx 2 (.inr twice)) =
      Search.Outcome.pure ({end₁ τ, end₂ τ} : Multiset (Configuration T Site)) ∧
    Search.Outcome.collect ((search τ A).approx 2 (.inr once)) =
      Search.Outcome.pure ({end₀ τ} : Multiset (Configuration T Site)) ∧
    end₁ τ ≠ end₂ τ ∧
    Search.Outcome.collect ((search τ A).approx 2 (.inr twice)) ≠
      Search.Outcome.collect ((search τ A).approx 2 (.inr once)) ∧
    Search.classSet (cls τ A) ((search τ A).approx 2 (.inr twice)) =
      Search.classSet (cls τ A) ((search τ A).approx 2 (.inr once)) ∧
    Search.classBag (cls τ A) ((search τ A).approx 2 (.inr twice)) = {cls τ A (end₀ τ), cls τ A (end₀ τ)} ∧
    Search.classBag (cls τ A) ((search τ A).approx 2 (.inr once)) = {cls τ A (end₀ τ)} := by
  have collectTwice : Search.Outcome.collect ((search τ A).approx 2 (.inr twice)) =
      Search.Outcome.pure ({end₁ τ, end₂ τ} : Multiset (Configuration T Site)) := by
    rw [approx_twice]
    rfl
  have collectOnce : Search.Outcome.collect ((search τ A).approx 2 (.inr once)) =
      Search.Outcome.pure ({end₀ τ} : Multiset (Configuration T Site)) := by
    rw [approx_once]
    rfl
  have finishedTwice : ((search τ A).run 2 (.inr twice)).status = .finished := by
    have status : ((search τ A).approx 2 (.inr twice)).status = .finished := by
      rw [approx_twice]
    exact status
  have finishedOnce : ((search τ A).run 2 (.inr once)).status = .finished := by
    have status : ((search τ A).approx 2 (.inr once)).status = .finished := by
      rw [approx_once]
    exact status
  refine ⟨answerBisimilar τ A, collectTwice, collectOnce, ?_, ?_, ?_, ?_, ?_⟩
  · intro same
    exact absurd (congrArg Configuration.present same) (of_decide_eq_false rfl)
  · rw [collectTwice, collectOnce]
    intro same
    have inner : ({end₁ τ, end₂ τ} : Multiset (Configuration T Site)) = {end₀ τ} := by
      have answers := congrArg Search.Outcome.answers same
      simpa using answers
    have cards := congrArg Multiset.card inner
    simp at cards
  · rw [classSet_eq_answerClasses (alphabet_nodup τ) (covers τ) finishedTwice,
      classSet_eq_answerClasses (alphabet_nodup τ) (covers τ) finishedOnce]
    exact answerClasses_eq_of_answerBisimilar (answerBisimilar τ A)
  · rw [approx_twice]
    show Multiset.map (cls τ A) {end₁ τ, end₂ τ} = _
    simp [class_end₁, class_end₂]
  · rw [approx_once]
    show Multiset.map (cls τ A) {end₀ τ} = _
    simp

end Twice

/-! ## Bisimilarity alone does not fix the answers -/

namespace Labels

/-- Occurrence identities. -/
inductive Site
  | x | y
  deriving DecidableEq

variable {T : Type uT} {S : Type uS} (τ₁ τ₂ : T)

def label : Site → T
  | .x => τ₁
  | .y => τ₂

/-- The program that offers nothing. -/
def offers (_ : Unit) (_ : Firing T S Site) : Prop := False

def X : Configuration T Site := ⟨[], {.x}⟩
def Y : Configuration T Site := ⟨[], {.y}⟩

variable (A : SubstitutionAction T S)

/-- **`{x}` and `{y}` are bisimilar**: nothing moves. -/
theorem bisimilar : Bisimilar A (label τ₁ τ₂) (offers (S := S)) X Y := by
  refine ⟨fun _ _ => True, ⟨?_, ?_, ?_⟩, trivial⟩
  · rintro _ _ _ _ _ ⟨_, offered, _⟩
    exact offered.elim
  · rintro _ _ _ _ _ ⟨_, offered, _⟩
    exact offered.elim
  · intro _ _ _ atom
    exact atom.elim

theorem reaches_self {C G : Configuration T Site}
    (reached : Relation.ReflTransGen (Moved A (label τ₁ τ₂) (offers (S := S))) C G) : G = C := by
  induction reached with
  | refl => rfl
  | tail _ step _ =>
      obtain ⟨_, _, offered, _⟩ := step
      exact offered.elim

/-- **Bisimilarity alone does not fix the answer classes**: `{x}` and `{y}` are bisimilar, and when
their labels differ they have different answer classes. -/
theorem answerClasses_differ (apart : τ₁ ≠ τ₂) :
    Bisimilar A (label τ₁ τ₂) (offers (S := S)) X Y ∧
      AnswerClasses A (label τ₁ τ₂) (offers (S := S))
          (Interface.Transport.StateClass.mk (renamingTransport A (label τ₁ τ₂))) X ≠
        AnswerClasses A (label τ₁ τ₂) (offers (S := S))
          (Interface.Transport.StateClass.mk (renamingTransport A (label τ₁ τ₂))) Y := by
  refine ⟨bisimilar τ₁ τ₂ A, fun same => ?_⟩
  have member : Interface.Transport.StateClass.mk (renamingTransport A (label τ₁ τ₂)) X ∈
      AnswerClasses A (label τ₁ τ₂) (offers (S := S))
        (Interface.Transport.StateClass.mk (renamingTransport A (label τ₁ τ₂))) X :=
    ⟨X, ⟨.refl, fun _ _ ⟨_, offered, _⟩ => offered⟩, rfl⟩
  rw [same] at member
  obtain ⟨G, ⟨reached, _⟩, classes⟩ := member
  obtain rfl := reaches_self τ₁ τ₂ A reached
  obtain ⟨i⟩ := (Interface.Transport.StateClass.mk_eq_mk_iff (renamingTransport A (label τ₁ τ₂))).mp
    classes
  have present : ({Site.y} : Finset Site).map i.rename.toEmbedding = {Site.x} := i.same.2
  rw [Finset.map_singleton, Finset.singleton_inj] at present
  have kept := i.keeps Site.y
  rw [show i.rename Site.y = Site.x from present] at kept
  exact apart kept

end Labels

/-! ## A finite alphabet is not equivariant -/

namespace Equivariance

/-- Occurrence identities. -/
inductive Site
  | a | b | k
  deriving DecidableEq

variable {T : Type uT} {S : Type uS} (τ τ' : T)

def label : Site → T
  | .a => τ
  | .b => τ
  | .k => τ'

/-- Take `a`, make `k`. -/
def make : Firing T S Site := ⟨⟨[τ], [], [], [], [τ']⟩, [], ⟨[.a], [], [.k]⟩⟩

/-- The program offers only `make`. -/
def offers (r : RuleInstance T) (f : Firing T S Site) : Prop := f = make τ τ' ∧ f.rule = r

def X : Configuration T Site := ⟨[], {.a}⟩
def Y : Configuration T Site := ⟨[], {.b}⟩
def Z : Configuration T Site := ⟨[(τ, τ)], {.k}⟩

variable (A : SubstitutionAction T S)

theorem config_eq {C D : Configuration T Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

theorem ground_make : Ground (label τ τ') (make (S := S) τ τ') :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem reflexive_Z : Reflexive (Z τ).equations := by
  intro e member
  simp only [Z, List.mem_singleton] at member
  subst member
  rfl

/-- `{a}` and `{b}` are related by a label-keeping renaming. -/
def renamed : RenamingIso A (label τ τ') X Y where
  rename := Equiv.swap .a .b
  keeps o := by cases o <;> simp [label, Equiv.swap_apply_def]
  same := ⟨fun _ => Iff.rfl, by simp [renameConfiguration, X, Y]⟩

theorem dead_Y : Dead A (label τ τ') (offers (S := S) τ τ') Y := by
  rintro r D ⟨f, ⟨rfl, _⟩, valid, _⟩
  rw [(ground_make τ τ').valid_iff A reflexive_nil] at valid
  exact of_decide_eq_false rfl valid

theorem dead_Z : Dead A (label τ τ') (offers (S := S) τ τ') (Z τ) := by
  rintro r D ⟨f, ⟨rfl, _⟩, valid, _⟩
  rw [(ground_make τ τ').valid_iff A (reflexive_Z τ)] at valid
  exact of_decide_eq_false rfl valid

theorem reaches_of_dead {C G : Configuration T Site}
    (dead : Dead A (label τ τ') (offers (S := S) τ τ') C)
    (reached : Relation.ReflTransGen (Moved A (label τ τ') (offers (S := S) τ τ')) C G) : G = C := by
  induction reached with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      obtain ⟨ℓ, moved⟩ := step
      exact absurd moved (dead ℓ _)

/-- **A finite alphabet is not equivariant.** `{a}` and `{b}` are related by a label-keeping renaming
and have different answer classes, so the program that offers only `make` is not equivariant. -/
theorem not_equivariant (apart : τ ≠ τ') :
    AnswerClasses A (label τ τ') (offers (S := S) τ τ')
        (Interface.Transport.StateClass.mk (renamingTransport A (label τ τ'))) X ≠
      AnswerClasses A (label τ τ') (offers (S := S) τ τ')
        (Interface.Transport.StateClass.mk (renamingTransport A (label τ τ'))) Y ∧
      ¬ Equivariant (label τ τ') (offers (S := S) τ τ') := by
  have differ : AnswerClasses A (label τ τ') (offers (S := S) τ τ')
        (Interface.Transport.StateClass.mk (renamingTransport A (label τ τ'))) X ≠
      AnswerClasses A (label τ τ') (offers (S := S) τ τ')
        (Interface.Transport.StateClass.mk (renamingTransport A (label τ τ'))) Y := by
    intro same
    have moved : Moved A (label τ τ') (offers (S := S) τ τ') X (Z τ) :=
      ⟨(make τ τ').rule, make τ τ', ⟨rfl, rfl⟩,
        ((ground_make τ τ').valid_iff A reflexive_nil).mpr (of_decide_eq_true rfl),
        config_eq rfl (of_decide_eq_true rfl)⟩
    have member : Interface.Transport.StateClass.mk (renamingTransport A (label τ τ')) (Z τ) ∈
        AnswerClasses A (label τ τ') (offers (S := S) τ τ')
          (Interface.Transport.StateClass.mk (renamingTransport A (label τ τ'))) X :=
      ⟨Z τ, ⟨Relation.ReflTransGen.single moved, dead_Z τ τ' A⟩, rfl⟩
    rw [same] at member
    obtain ⟨G, ⟨reached, _⟩, classes⟩ := member
    obtain rfl := reaches_of_dead τ τ' A (dead_Y τ τ' A) reached
    obtain ⟨i⟩ := (Interface.Transport.StateClass.mk_eq_mk_iff (renamingTransport A (label τ τ'))).mp
      classes
    have present : ({Site.b} : Finset Site).map i.rename.toEmbedding = {Site.k} := i.same.2
    rw [Finset.map_singleton, Finset.singleton_inj] at present
    have kept := i.keeps Site.b
    rw [show i.rename Site.b = Site.k from present] at kept
    exact apart kept.symm
  exact ⟨differ, fun equivariant =>
    differ (answerClasses_eq_of_renamingIso equivariant (renamed τ τ' A))⟩

end Equivariance

/-! ## An equivariant finite alphabet -/

namespace Symmetric

/-- Two indiscernible occurrences and a gate with its own label. -/
inductive Site
  | x | y | g
  deriving DecidableEq

variable {T : Type uT} {S : Type uS} (τ τg : T)

def label : Site → T
  | .x => τ
  | .y => τ
  | .g => τg

/-- Take `o` and the gate. -/
def take (o : Site) : Firing T S Site := ⟨⟨[τ, τg], [], [], [], []⟩, [], ⟨[o, .g], [], []⟩⟩

def alphabet : List (Firing T S Site) := [take τ τg .x, take τ τg .y]

/-- **Labels are rules.** -/
def offers (r : RuleInstance T) (f : Firing T S Site) : Prop := f ∈ alphabet τ τg ∧ f.rule = r

def X : Configuration T Site := ⟨[], {.x, .g}⟩
def Y : Configuration T Site := ⟨[], {.y, .g}⟩
def done : Configuration T Site := ⟨[(τ, τ), (τg, τg)], ∅⟩

theorem config_eq {C D : Configuration T Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

/-- A renaming that keeps the labels fixes the gate. -/
theorem fixes_gate (apart : τ ≠ τg) {π : Site ≃ Site} (keeps : ∀ o, label τ τg (π o) = label τ τg o) :
    π .g = .g := by
  have kept := keeps .g
  cases h : π .g with
  | x => rw [h] at kept; exact absurd kept apart
  | y => rw [h] at kept; exact absurd kept apart
  | g => rfl

theorem rename_take {π : Site ≃ Site} (fixed : π .g = .g) (o : Site) :
    (take (S := S) τ τg o).rename π = take τ τg (π o) := by
  show (⟨⟨[τ, τg], [], [], [], []⟩, [], ⟨[π o, π .g], [], []⟩⟩ : Firing T S Site) = _
  rw [fixed]
  rfl

theorem take_mem (o : Site) (gate : o ≠ .g) : take (S := S) τ τg o ∈ alphabet τ τg := by
  cases o with
  | x => simp [alphabet]
  | y => simp [alphabet]
  | g => exact absurd rfl gate

/-- **The program is equivariant**: a label-keeping renaming fixes the gate and permutes `x, y`. -/
theorem equivariant (apart : τ ≠ τg) : Equivariant (label τ τg) (offers (S := S) τ τg) := by
  intro π keeps r f ⟨member, rule⟩
  have fixed := fixes_gate τ τg apart keeps
  refine ⟨?_, rule⟩
  have moved : ∀ o, o ≠ .g → π o ≠ .g := fun o gate same => gate (π.injective (same.trans fixed.symm))
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [rename_take τ τg fixed]
    exact take_mem τ τg _ (moved .x (by decide))
  · rw [rename_take τ τg fixed]
    exact take_mem τ τg _ (moved .y (by decide))

theorem ground : ∀ f ∈ alphabet (S := S) τ τg, Ground (label τ τg) f := by
  intro f member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem alphabet_nodup : (alphabet (S := S) τ τg).Nodup := by
  simp [alphabet, take]

theorem covers (f : Firing T S Site) : f ∈ alphabet τ τg ↔ ∃ r, offers τ τg r f :=
  ⟨fun member => ⟨f.rule, member, rfl⟩, fun ⟨_, member, _⟩ => member⟩

theorem reflexive_done : Reflexive (done τ τg).equations := by
  intro e member
  simp only [done, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

variable (A : SubstitutionAction T S)

/-- `{x, g}` and `{y, g}` are related by the exchange of `x` and `y`. -/
def exchanged : RenamingIso A (label τ τg) X Y where
  rename := Equiv.swap .x .y
  keeps o := by cases o <;> simp [label, Equiv.swap_apply_def]
  same := ⟨fun _ => Iff.rfl, by simp [renameConfiguration, X, Y, Equiv.swap_apply_def]⟩

/-- The search of the program. -/
noncomputable abbrev search := (alternatives A (label τ τg) (alphabet τ τg)).space

theorem result_x : (take (S := S) τ τg .x).result (label τ τg) X = done τ τg :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_y : (take (S := S) τ τg .y).result (label τ τg) Y = done τ τg :=
  config_eq rfl (of_decide_eq_true rfl)

theorem next_X : ((alternatives A (label τ τg) (alphabet τ τg)).next X).map (fun g => g.1.1) =
    [take (S := S) τ τg .x] := by
  rw [next_map_of_ground (ground τ τg) reflexive_nil]
  rfl

theorem next_Y : ((alternatives A (label τ τg) (alphabet τ τg)).next Y).map (fun g => g.1.1) =
    [take (S := S) τ τg .y] := by
  rw [next_map_of_ground (ground τ τg) reflexive_nil]
  rfl

theorem next_done :
    ((alternatives A (label τ τg) (alphabet (S := S) τ τg)).next (done τ τg)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground τ τg) (reflexive_done τ τg)]
  rfl

theorem approx_X : (search τ τg A).approx 2 (.inr X) = Search.Outcome.pure (done τ τg) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_X τ τg A)]
  simp [result_x, Search.Space.approx_succ, unfold_of_nil (next_done τ τg A), Search.Space.approx_inl]

theorem approx_Y : (search τ τg A).approx 2 (.inr Y) = Search.Outcome.pure (done τ τg) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_Y τ τg A)]
  simp [result_y, Search.Space.approx_succ, unfold_of_nil (next_done τ τg A), Search.Space.approx_inl]

/-- **An equivariant finite alphabet**: when the gate has its own label, the program is equivariant,
and the renaming-equivalent starts `{x, g}` and `{y, g}` have equal class sets at their finished
budgets. -/
theorem symmetric_control (apart : τ ≠ τg) :
    Equivariant (label τ τg) (offers (S := S) τ τg) ∧
      Search.classSet (Interface.Transport.StateClass.mk (renamingTransport A (label τ τg)))
          ((search τ τg A).approx 2 (.inr X)) =
        Search.classSet (Interface.Transport.StateClass.mk (renamingTransport A (label τ τg)))
          ((search τ τg A).approx 2 (.inr Y)) := by
  have finishedX : ((search τ τg A).run 2 (.inr X)).status = .finished := by
    have status : ((search τ τg A).approx 2 (.inr X)).status = .finished := by rw [approx_X]; rfl
    exact status
  have finishedY : ((search τ τg A).run 2 (.inr Y)).status = .finished := by
    have status : ((search τ τg A).approx 2 (.inr Y)).status = .finished := by rw [approx_Y]; rfl
    exact status
  exact ⟨equivariant τ τg apart, classSet_eq_of_renamingIso (alphabet_nodup τ τg) (covers τ τg)
    (equivariant τ τg apart) finishedX finishedY (exchanged τ τg A)⟩

end Symmetric

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ReadoutControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ReadoutControls in
#print axioms Twice.answerBisimilar
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ReadoutControls in
#print axioms Twice.twice_control
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ReadoutControls in
#print axioms Labels.answerClasses_differ
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ReadoutControls in
#print axioms Equivariance.not_equivariant
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ReadoutControls in
#print axioms Symmetric.symmetric_control
