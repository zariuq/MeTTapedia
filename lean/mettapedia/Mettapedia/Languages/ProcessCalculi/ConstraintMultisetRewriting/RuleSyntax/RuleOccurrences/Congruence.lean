import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Congruence

/-!
# The congruence of systems is the contextual congruence of the candidate, in the persistent case

`RuleSyntax/Equivalence` defines a system as a program with a state, its reductions as the steps of
its program, and reduction-closed barbed congruence over contexts that add rows, tells, extensions of
the frame, and **rules** (`Equivalence.Congruent`).

Here a **configuration** (`Config`) is the candidate in the persistent case: an ambient program,
finitely many identities each holding a rule persistently (through a fixed assignment
`code : R → Rule Tm`), and a state of rows. It **presents** the system whose program is the ambient
program together with the rules held (`Config.system`), and it is a state of the candidate
(`Config.rstate`).

* **Moves** (`Moves`): the transitions of the candidate with the configuration's ambient program.
  Every transition of the candidate from the state of a configuration is a move (`moves_of_succ`),
  and the moves of a configuration are exactly the reductions of the system it presents
  (`moves_iff`, from `program_eq`).
* **Contexts** (`CBasic`): the contexts of `Equivalence` acting on the rows, the knowledge, the
  frame and the ambient program, and one more: **hold finitely many more rules** (`CBasic.hold`).
  Applying a context commutes with presenting (`system_apply`); holding more rules presents as adding
  those rules to the program.
* **The contextual congruence of configurations** (`CCongruent`): the largest symmetric relation that
  preserves the barbs and is closed under moves and under these contexts.
* **`ccongruent_iff`**: two configurations are congruent exactly when the systems they present are
  congruent in the sense of `Equivalence`.

So the quantification over contexts that add rules, in the congruence of systems, is the
quantification over contexts that make the state hold more rules or enlarge the ambient program.

**What the statement does not say.** A context of `Equivalence` may add an infinite program; for a
configuration that is an enlargement of the ambient program, never of what is held. And the system
presented forgets how often a rule is held: two identities holding one rule present the same system
as one (`system_twice`), in agreement with `program_eq`; so the two configurations are congruent
(`ccongruent_twice`). This congruence observes which rows can be read, and does not count
derivations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (System Basic Reduces)

universe uO uT uH uE uOcc uR uZ uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A configuration**: an ambient program, finitely many identities that each hold a rule
persistently, and a state of rows. -/
structure Config (Tm : Obj → Type uT) (O : Type uOcc) (R : Type uR) where
  ambient : Program Tm
  held : Finset R
  state : State Tm O

variable {O : Type uOcc} {R : Type uR} {Z : Type uZ}

namespace Config

/-- **The system a configuration presents**: its program is the ambient program together with the
rules held. -/
def system (code : R → Rule Tm) (κ : Config Tm O R) : System Tm O :=
  ⟨κ.ambient ∪ code '' ↑κ.held, κ.state⟩

/-- **A configuration as a state of the candidate.** -/
def rstate (code : R → Rule Tm) (zone : R → Z) (κ : Config Tm O R) : RState Tm O R (Rule Tm) Z :=
  holding κ.state κ.held code zone

end Config

/-- The rules held are exactly the image of the identities. -/
theorem offers_image (code : R → Rule Tm) (held : Finset R) : Offers (code '' ↑held) held code := by
  intro r
  constructor
  · rintro ⟨ρ, inside, rfl⟩
    exact ⟨ρ, Finset.mem_coe.mp inside, rfl⟩
  · rintro ⟨ρ, inside, rfl⟩
    exact ⟨ρ, Finset.mem_coe.mpr inside, rfl⟩

/-- **Holding a rule twice presents the same system**: the system does not see how often a rule is
held. -/
theorem system_twice [DecidableEq R] (code : R → Rule Tm) (ambient : Program Tm) (held : Finset R)
    (state : State Tm O) {ρ ρ' : R} (inside : ρ ∈ held) (same : code ρ' = code ρ) :
    (⟨ambient, insert ρ' held, state⟩ : Config Tm O R).system code =
      (⟨ambient, held, state⟩ : Config Tm O R).system code := by
  have images : code '' ↑(insert ρ' held) = code '' ↑held := by
    rw [Finset.coe_insert, Set.image_insert_eq, same]
    exact Set.insert_eq_of_mem ⟨ρ, Finset.mem_coe.mpr inside, rfl⟩
  unfold Config.system
  rw [images]

section Moves

variable (X : Frames Tm Hom) [DecidableEq O] [DecidableEq R] (E : Extensions.{uO, uH, uE} Hom)
  (code : R → Rule Tm) (zone : R → Z)

/-- **A move of a configuration**: a transition of the candidate with its ambient program; the
ambient program and the identities that hold rules stay. -/
def Moves (κ κ' : Config Tm O R) : Prop :=
  κ'.ambient = κ.ambient ∧ κ'.held = κ.held ∧
    Succ (rstep X O R E (ofRules Z) κ.ambient).toStep (κ.rstate code zone) (κ'.rstate code zone)

/-- **Every transition of the candidate from the state of a configuration is a move.** -/
theorem moves_of_succ (κ : Config Tm O R) {u : RState Tm O R (Rule Tm) Z}
    (reached : Succ (rstep X O R E (ofRules Z) κ.ambient).toStep (κ.rstate code zone) u) :
    ∃ κ' : Config Tm O R, u = κ'.rstate code zone ∧ Moves X E code zone κ κ' := by
  obtain ⟨t, rfl, -⟩ := holding_closed R X E (offers_image code κ.held) zone reached
  exact ⟨⟨κ.ambient, κ.held, t⟩, rfl, rfl, rfl, reached⟩

/-- **The moves of a configuration are the reductions of the system it presents.** -/
theorem moves_iff (κ κ' : Config Tm O R) :
    Moves X E code zone κ κ' ↔ κ'.ambient = κ.ambient ∧ κ'.held = κ.held ∧
      Reduces X O E (κ.system code) (κ'.system code) := by
  constructor
  · rintro ⟨ambient, held, moved⟩
    refine ⟨ambient, held, ?_, ?_⟩
    · show κ'.ambient ∪ code '' ↑κ'.held = κ.ambient ∪ code '' ↑κ.held
      rw [ambient, held]
    · unfold Config.rstate at moved
      rw [held] at moved
      exact (program_eq R X E (offers_image code κ.held) zone κ.state κ'.state).mp moved
  · rintro ⟨ambient, held, -, moved⟩
    refine ⟨ambient, held, ?_⟩
    unfold Config.rstate
    rw [held]
    exact (program_eq R X E (offers_image code κ.held) zone κ.state κ'.state).mpr moved

end Moves

/-! ## Contexts of configurations -/

/-- **A basic context of configurations**: a context of `Equivalence` (add rows, enlarge the ambient
program, tell, extend the frame), or hold finitely many more rules. -/
inductive CBasic (Tm : Obj → Type uT) (O : Type uOcc) (R : Type uR)
    (E : Extensions.{uO, uH, uE} Hom) : Type (max uO uT uOcc uE uR) where
  | system (c : Basic Tm O E)
  | hold (added : Finset R)

namespace CBasic

variable {E : Extensions.{uO, uH, uE} Hom}

/-- The context of systems that a context of configurations presents: holding more rules presents
as adding those rules to the program. -/
def toBasic (code : R → Rule Tm) : CBasic Tm O R E → Basic Tm O E
  | .system c => c
  | .hold added => .rules (code '' ↑added)

/-- The same context with its added row identities renamed. -/
def rename (π : Equiv.Perm O) : CBasic Tm O R E → CBasic Tm O R E
  | .system c => .system (c.rename π)
  | .hold added => .hold added

/-- A context applies to a configuration when the row identities it adds are absent. -/
def Applies (code : R → Rule Tm) (c : CBasic Tm O R E) (κ : Config Tm O R) : Prop :=
  (c.toBasic code).Applies (κ.system code)

theorem toBasic_rename (code : R → Rule Tm) (π : Equiv.Perm O) (c : CBasic Tm O R E) :
    (c.rename π).toBasic code = (c.toBasic code).rename π := by
  cases c <;> rfl

variable (X : Frames Tm Hom) [DecidableEq O] [DecidableEq R]

/-- **Applying a context to a configuration.** -/
def apply : CBasic Tm O R E → Config Tm O R → Config Tm O R
  | .system c, κ =>
      ⟨(c.apply X ⟨κ.ambient, κ.state⟩).program, κ.held, (c.apply X ⟨κ.ambient, κ.state⟩).state⟩
  | .hold added, κ => ⟨κ.ambient, κ.held ∪ added, κ.state⟩

/-- **Applying a context commutes with presenting.** -/
theorem system_apply (code : R → Rule Tm) (c : CBasic Tm O R E) (κ : Config Tm O R) :
    (c.apply X κ).system code = (c.toBasic code).apply X (κ.system code) := by
  cases c with
  | system c =>
      cases c with
      | rows ids label => rfl
      | rules added =>
          show (⟨(κ.ambient ∪ added) ∪ code '' ↑κ.held, κ.state⟩ : System Tm O) =
            ⟨(κ.ambient ∪ code '' ↑κ.held) ∪ added, κ.state⟩
          rw [Set.union_right_comm]
      | tell equations => rfl
      | extend extension => rfl
  | hold added =>
      show (⟨κ.ambient ∪ code '' ↑(κ.held ∪ added), κ.state⟩ : System Tm O) =
        ⟨(κ.ambient ∪ code '' ↑κ.held) ∪ code '' ↑added, κ.state⟩
      rw [Finset.coe_union, Set.image_union, Set.union_assoc]

end CBasic

/-! ## The contextual congruence of configurations -/

section Congruence

variable (X : Frames Tm Hom) [DecidableEq O] [DecidableEq R] (E : Extensions.{uO, uH, uE} Hom)
  (code : R → Rule Tm) (zone : R → Z) {B : Type uB} (obs : B → State Tm O → Prop)

/-- **A candidate relation on configurations**: symmetric, preserving the barbs, closed under moves
and under every basic context; at the right side the identities of added rows are chosen afresh. -/
structure CCandidate (Rel : Config Tm O R → Config Tm O R → Prop) : Prop where
  symm : ∀ {κ μ : Config Tm O R}, Rel κ μ → Rel μ κ
  barbs : ∀ {κ μ : Config Tm O R}, Rel κ μ → ∀ β, obs β κ.state → obs β μ.state
  moves : ∀ {κ μ : Config Tm O R}, Rel κ μ → ∀ {κ' : Config Tm O R}, Moves X E code zone κ κ' →
    ∃ μ', Moves X E code zone μ μ' ∧ Rel κ' μ'
  context : ∀ {κ μ : Config Tm O R}, Rel κ μ → ∀ c : CBasic Tm O R E, c.Applies code κ →
    ∃ π : Equiv.Perm O, (c.rename π).Applies code μ ∧ Rel (c.apply X κ) ((c.rename π).apply X μ)

/-- **The contextual congruence of configurations**: related by some candidate. -/
def CCongruent (κ μ : Config Tm O R) : Prop :=
  ∃ Rel, CCandidate X E code zone obs Rel ∧ Rel κ μ

variable {X E code zone obs}

omit [DecidableEq O] [DecidableEq R] in
/-- A system with the program of a configuration is presented by the configuration with its state. -/
theorem system_of_program {μ : Config Tm O R} {T : System Tm O}
    (same : T.program = (μ.system code).program) :
    (⟨μ.ambient, μ.held, T.state⟩ : Config Tm O R).system code = T := by
  obtain ⟨program, state⟩ := T
  have programs : program = μ.ambient ∪ code '' ↑μ.held := same
  subst programs
  rfl

/-- **The congruence of systems, read on configurations, is a candidate.** -/
theorem ccandidate_congruent :
    CCandidate X E code zone obs
      (fun κ μ : Config Tm O R => Equivalence.Congruent X O E obs (κ.system code) (μ.system code)) where
  symm := fun related => Equivalence.Congruent.symm related
  barbs := fun related β holds => Equivalence.candidate_congruent.barbs related β holds
  moves := by
    intro κ μ related κ' moved
    obtain ⟨-, -, reduces⟩ := (moves_iff X E code zone κ κ').mp moved
    obtain ⟨T', reduces', related'⟩ := Equivalence.candidate_congruent.reduces related reduces
    have presented := system_of_program (code := code) (μ := μ) reduces'.1
    refine ⟨⟨μ.ambient, μ.held, T'.state⟩, (moves_iff X E code zone μ _).mpr ⟨rfl, rfl, ?_⟩, ?_⟩
    · rw [presented]
      exact reduces'
    · show Equivalence.Congruent X O E obs (κ'.system code)
        ((⟨μ.ambient, μ.held, T'.state⟩ : Config Tm O R).system code)
      rw [presented]
      exact related'
  context := by
    intro κ μ related c applies
    obtain ⟨π, applies', related'⟩ :=
      Equivalence.candidate_congruent.context related (c.toBasic code) applies
    refine ⟨π, ?_, ?_⟩
    · show ((c.rename π).toBasic code).Applies (μ.system code)
      rw [CBasic.toBasic_rename]
      exact applies'
    · show Equivalence.Congruent X O E obs ((c.apply X κ).system code)
        (((c.rename π).apply X μ).system code)
      rw [CBasic.system_apply, CBasic.system_apply, CBasic.toBasic_rename]
      exact related'

/-- **A candidate on configurations presents a candidate on systems.** -/
theorem candidate_of_ccandidate {Rel : Config Tm O R → Config Tm O R → Prop}
    (candidate : CCandidate X E code zone obs Rel) :
    Equivalence.Candidate X O E obs
      (fun S T : System Tm O => ∃ κ μ : Config Tm O R,
        κ.system code = S ∧ μ.system code = T ∧ Rel κ μ) where
  symm := by
    rintro S T ⟨κ, μ, rfl, rfl, related⟩
    exact ⟨μ, κ, rfl, rfl, candidate.symm related⟩
  barbs := by
    rintro S T ⟨κ, μ, rfl, rfl, related⟩ β holds
    exact candidate.barbs related β holds
  reduces := by
    rintro S T ⟨κ, μ, rfl, rfl, related⟩ S' reduces
    have presented := system_of_program (code := code) (μ := κ) reduces.1
    have moved : Moves X E code zone κ ⟨κ.ambient, κ.held, S'.state⟩ := by
      refine (moves_iff X E code zone κ _).mpr ⟨rfl, rfl, ?_⟩
      rw [presented]
      exact reduces
    obtain ⟨μ', moved', related'⟩ := candidate.moves related moved
    exact ⟨μ'.system code, ((moves_iff X E code zone μ μ').mp moved').2.2,
      ⟨κ.ambient, κ.held, S'.state⟩, μ', presented, rfl, related'⟩
  context := by
    rintro S T ⟨κ, μ, rfl, rfl, related⟩ c applies
    obtain ⟨π, applies', related'⟩ := candidate.context related (.system c) applies
    exact ⟨π, applies', (CBasic.system c).apply X κ, (CBasic.system (c.rename π)).apply X μ,
      CBasic.system_apply X code (.system c) κ, CBasic.system_apply X code (.system (c.rename π)) μ,
      related'⟩

/-- **The congruence of systems is the contextual congruence of configurations**: two
configurations are congruent exactly when the systems they present are congruent. -/
theorem ccongruent_iff (κ μ : Config Tm O R) :
    CCongruent X E code zone obs κ μ ↔
      Equivalence.Congruent X O E obs (κ.system code) (μ.system code) := by
  constructor
  · rintro ⟨Rel, candidate, related⟩
    exact ⟨_, candidate_of_ccandidate candidate, κ, μ, rfl, rfl, related⟩
  · intro related
    exact ⟨_, ccandidate_congruent, related⟩

/-- Every configuration is congruent to itself: the relation is not empty. -/
theorem ccongruent_refl (κ : Config Tm O R) : CCongruent X E code zone obs κ κ :=
  (ccongruent_iff κ κ).mpr (Equivalence.Congruent.refl _)

/-- **The congruence does not count**: a configuration that holds a rule persistently at one more
identity is congruent to the configuration that does not, for every family of barbs. -/
theorem ccongruent_twice (ambient : Program Tm) (held : Finset R) (state : State Tm O) {ρ ρ' : R}
    (inside : ρ ∈ held) (same : code ρ' = code ρ) :
    CCongruent X E code zone obs ⟨ambient, insert ρ' held, state⟩ ⟨ambient, held, state⟩ := by
  rw [ccongruent_iff, system_twice code ambient held state inside same]
  exact Equivalence.Congruent.refl _

end Congruence

#print axioms offers_image
#print axioms system_twice
#print axioms moves_of_succ
#print axioms moves_iff
#print axioms CBasic.system_apply
#print axioms ccandidate_congruent
#print axioms candidate_of_ccandidate
#print axioms ccongruent_iff
#print axioms ccongruent_refl
#print axioms ccongruent_twice

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
