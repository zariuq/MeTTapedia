import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Parsing.HornCertificate

/-!
# Operational GSLT for bounded Horn-certificate derivability

An operational state is an ordered list of fuel-indexed ground obligations.
One transition selects an authored rule occurrence and a valid ground
substitution for the first obligation, then replaces it by the instantiated
premises in authored order.  Nothing is deduplicated and there is no
first-match policy.

The central theorem is two-sided: bounded Horn derivability is equivalent to
reaching the empty obligation list in this GSLT.  Certificate replay therefore
has the same exact operational reading through the existing replay theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.HornCertificateGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.Parsing.HornCertificate

abbrev Obligation := Nat × GroundAtom
abbrev State := List Obligation

def goalsAt (fuel : Nat) (goals : List GroundAtom) : State :=
  goals.map (fun goal => (fuel, goal))

/-- One source-rule application at the first outstanding obligation. -/
inductive Step (program : Program) : State → State → Prop where
  | apply (fuel : Nat) (goal : GroundAtom) (rest : State)
      (rule : Rule) (member : rule ∈ program)
      (substitution : Substitution)
      (valid : substitutionValid substitution = true)
      (goals : List GroundAtom)
      (head : instantiateAtom substitution rule.head = some goal)
      (body : instantiateAtoms substitution rule.body = some goals) :
      Step program ((fuel + 1, goal) :: rest)
        (goalsAt fuel goals ++ rest)

/-- The equality-free operational GSLT of a finite ordered Horn program. -/
def theory (program : Program) : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step program
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def appendMultiStep {program : Program} {first middle last : State} :
    (theory program).MultiStep first middle →
      (theory program).MultiStep middle last →
        (theory program).MultiStep first last
  | .refl _, suffix => suffix
  | .step step rest, suffix => .step step (appendMultiStep rest suffix)

mutual

  /-- A Horn derivation executes to discharge its first obligation. -/
  def derivesMultiStep {program : Program} {fuel : Nat} {goal : GroundAtom}
      (derivation : DerivesWithin program fuel goal) (rest : State) :
      (theory program).MultiStep ((fuel, goal) :: rest) rest :=
    match derivation with
    | .apply innerFuel goal rule member substitution valid goals head body premises =>
        .step
          (.apply innerFuel goal rest rule member substitution valid goals head body)
          (derivationsMultiStep premises rest)

  /-- Ordered sibling derivations execute left-to-right without losing their
  occurrence structure. -/
  def derivationsMultiStep {program : Program} {fuel : Nat}
      {goals : List GroundAtom}
      (derivations : DerivationsWithin program fuel goals) (rest : State) :
      (theory program).MultiStep (goalsAt fuel goals ++ rest) rest :=
    match derivations with
    | .nil _ => by
        simpa [goalsAt] using
          (@GSLT.MultiStep.refl (theory program) rest)
    | .cons head tail =>
        appendMultiStep
          (derivesMultiStep head (goalsAt fuel _ ++ rest))
          (derivationsMultiStep tail rest)

end

/-- Independent proposition that every outstanding obligation is derivable
at its recorded fuel. -/
def StateDerivable (program : Program) (state : State) : Prop :=
  ∀ obligation ∈ state,
    DerivesWithin program obligation.1 obligation.2

def derivationsOfPointwise {program : Program} {fuel : Nat}
    (goals : List GroundAtom)
    (derives : ∀ goal ∈ goals, DerivesWithin program fuel goal) :
    DerivationsWithin program fuel goals :=
  match goals with
  | [] => .nil fuel
  | goal :: rest =>
      .cons (derives goal (by simp))
        (derivationsOfPointwise rest (fun child member =>
          derives child (by simp [member])))

/-- A chosen operational rule application reflects derivability from its
target obligations back to its source obligation. -/
theorem step_reflects_derivability {program : Program} {source target : State}
    (step : Step program source target)
    (targetDerivable : StateDerivable program target) :
    StateDerivable program source := by
  cases step with
  | apply fuel goal rest rule member substitution valid goals head body =>
      intro obligation sourceMember
      simp only [List.mem_cons] at sourceMember
      rcases sourceMember with obligationIsHead | obligationInRest
      · subst obligation
        exact .apply fuel goal rule member substitution valid goals head body
          (derivationsOfPointwise goals (fun child childMember =>
            targetDerivable (fuel, child) (by
              apply List.mem_append_left
              simp [goalsAt, childMember])))
      · exact targetDerivable obligation (by
          apply List.mem_append_right
          exact obligationInRest)

/-- Any path to the empty state reflects a derivation of every source
obligation. -/
theorem multiStep_reflects_derivability {program : Program}
    {source target : State}
    (steps : (theory program).MultiStep source target)
    (targetDerivable : StateDerivable program target) :
    StateDerivable program source := by
  refine @GSLT.MultiStep.rec (theory program)
    (fun first last _ =>
      StateDerivable program last → StateDerivable program first)
    ?_ ?_ source target steps targetDerivable
  · intro state derivable
    exact derivable
  · intro first middle last firstStep _ induction lastDerivable
    exact step_reflects_derivability firstStep (induction lastDerivable)

theorem terminal_path_reflects_derivability {program : Program}
    {source : State}
    (steps : (theory program).MultiStep source []) :
    StateDerivable program source :=
  multiStep_reflects_derivability steps (by simp [StateDerivable])

/-- Exact operational characterization of bounded Horn derivability. -/
theorem derivesWithin_iff_terminal_path
    (program : Program) (fuel : Nat) (goal : GroundAtom) :
    DerivesWithin program fuel goal ↔
      (theory program).MultiStep [(fuel, goal)] [] := by
  constructor
  · intro derivation
    exact derivesMultiStep derivation []
  · intro steps
    have source := terminal_path_reflects_derivability steps
    exact source (fuel, goal) (by simp)

/-- Certificate replay, declarative derivability, and operational execution
have the same bounded success set. -/
theorem replay_iff_terminal_path
    (program : Program) (fuel : Nat) (goal : GroundAtom) :
    (∃ certificate, replay program fuel goal certificate = true) ↔
      (theory program).MultiStep [(fuel, goal)] [] := by
  rw [replay_iff_derivesWithin, derivesWithin_iff_terminal_path]

/-! ## Discriminating controls -/

theorem family_ancestor_reaches_terminal :
    (theory familyProgram).MultiStep [(2, ancestorGoal)] [] :=
  (derivesWithin_iff_terminal_path familyProgram 2 ancestorGoal).mp
    ancestorCertificate_is_sound

theorem empty_program_cannot_invent_derivation (goal : GroundAtom) :
    ¬ (theory []).MultiStep [(1, goal)] [] := by
  intro steps
  have derivation :=
    (derivesWithin_iff_terminal_path [] 1 goal).mpr steps
  cases derivation with
  | apply _ _ rule member _ _ _ _ _ _ => simp at member

#print axioms step_reflects_derivability
#print axioms terminal_path_reflects_derivability
#print axioms derivesWithin_iff_terminal_path
#print axioms replay_iff_terminal_path
#print axioms family_ancestor_reaches_terminal
#print axioms empty_program_cannot_invent_derivation

end Mettapedia.GSLT.Parsing.HornCertificateGSLT
