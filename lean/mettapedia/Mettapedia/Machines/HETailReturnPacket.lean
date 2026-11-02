import Std

/-!
# Compiling a tail publication word

The reference interpreter keeps every projection and invocation-return action.
The packet compiler keeps at most two saved fallback operators and three exact
natural projection counts. Its equality theorem permits arbitrary interleaving
and does not assume payload projection is idempotent. A plain fixed point can
consume an entire remaining projection power immediately.

The preview carrier distinguishes a bare NotReducible marker, a marker exposed
by one projection, and a preview stable under later projection. Native
correspondence must establish that classification from the actual publication
helper, including variable/variant/delayed cases. This module does not assert
that all native outcomes satisfy it, that every return observer is fusible,
or that arbitrary projection powers have constant execution cost. Exact counts
require logarithmic bits. Types, normalization, HE marking, pending choices,
options and ownership remain separate native admission obligations.

The negative examples require both fallback positions and leading projections.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HETailReturnPacket

variable {α β : Type}

/-- Preview classes for a publication run. `data` includes opaque payloads
    whose preview cannot turn into the bare marker on later publication.
    `latent` is a non-marker preview exposed as the marker by one publication.
    Native correspondence to these classes is a separate obligation. -/
inductive Return (α : Type) where
  | marker (payload : α)
  | latent (payload : α)
  | data (payload : α)
  deriving DecidableEq, Repr

/-- Projecting a payload may do arbitrary work. It is not assumed idempotent. -/
def project (p : α → α) : Return α → Return α
  | .marker a => .marker (p a)
  | .latent a => .marker (p a)
  | .data a => .data (p a)

/-- A saved-call fallback may depend on all of the incoming payload. -/
def publish (p call : α → α) : Return α → Return α
  | .marker a => .data (call a)
  | other => project p other

/-- The unfused, innermost-first return continuation. -/
def reference (p : α → α) : List (α → α) → Return α → Return α
  | [], out => out
  | call :: rest, out => reference p rest (publish p call out)

/-- Exact iteration, retaining conditional/cyclic payload work if required. -/
def power (p : α → α) : Nat → Return α → Return α
  | 0, out => out
  | n + 1, out => power p n (project p out)

def dataPower (p : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => dataPower p n (p a)

/-- The independent packet algorithm retains only two fallback operators. -/
def packet (p : α → α) : List (α → α) → Return α → Return α
  | [], out => out
  | [first], out => publish p first out
  | first :: second :: rest, out =>
      power p rest.length (publish p second (publish p first out))

theorem power_data (p : α → α) (n : Nat) (a : α) :
    power p n (.data a) = .data (dataPower p n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact ih (p a)

theorem reference_data (p : α → α) (calls : List (α → α)) (a : α) :
    reference p calls (.data a) = .data (dataPower p calls.length a) := by
  induction calls generalizing a with
  | nil => rfl
  | cons call rest ih => exact ih (p a)

/-- Two invocations consume any immediately exposed marker. All remaining
    invocations are exact projection powers, regardless of their fallbacks. -/
theorem packet_eq_reference (p : α → α)
    (calls : List (α → α)) (out : Return α) :
    packet p calls out = reference p calls out := by
  cases calls with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second more =>
          cases out with
          | marker a =>
              exact (power_data p more.length (p (first a))).trans
                (reference_data p more (p (first a))).symm
          | latent a =>
              exact (power_data p more.length (second (p a))).trans
                (reference_data p more (second (p a))).symm
          | data a =>
              exact (power_data p more.length (p (p a))).trans
                (reference_data p more (p (p a))).symm

theorem packet_preserves_observer (p : α → α)
    (calls : List (α → α)) (out : Return α) (observe : Return α → β) :
    observe (packet p calls out) = observe (reference p calls out) :=
  congrArg observe (packet_eq_reference p calls out)

/-- Multiplicity and order remain visible to an arbitrary frontier observer. -/
theorem packet_preserves_frontier (p : α → α)
    (calls : List (α → α)) (out : List (Return α)) :
    out.map (packet p calls) = out.map (reference p calls) := by
  induction out with
  | nil => rfl
  | cons value rest ih =>
      exact (congrArg (fun first => first :: rest.map (packet p calls))
        (packet_eq_reference p calls value)).trans
          (congrArg (List.cons (reference p calls value)) ih)

/-- A plain fixed point consumes the entire remaining power in one step. -/
theorem power_fixed (p : α → α) (n : Nat) (a : α) (fixed : p a = a) :
    power p n (.data a) = .data a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [power, project, fixed] using ih

/-- One fallback is insufficient when projection first exposes the marker. -/
theorem one_fallback_counterexample :
    reference (fun n : Nat => n)
      [fun _ => 7, fun _ => 9] (.latent 0) ≠
    power (fun n : Nat => n) 1
      (publish (fun n : Nat => n) (fun _ => 7) (.latent 0)) := by
  intro impossible
  cases impossible


end Mettapedia.Machines.HETailReturnPacket

namespace Mettapedia.Machines.HETailReturnPacket

variable {α β : Type}

inductive Action (α : Type) where
  | project
  | invoke (call : α → α)

def runActions (p : α → α) : List (Action α) → Return α → Return α
  | [], out => out
  | .project :: rest, out => runActions p rest (project p out)
  | .invoke call :: rest, out => runActions p rest (publish p call out)

abbrev ProjectSplit (α : Type) :=
  Nat × Option ((α → α) × List (Action α))

def splitProjects : List (Action α) → ProjectSplit α
  | [] => (0, none)
  | .project :: rest =>
      let (count, tail) := splitProjects rest
      (count + 1, tail)
  | .invoke call :: rest => (0, some (call, rest))

def runSplit (p : α → α) (split : ProjectSplit α) (out : Return α) : Return α :=
  match split with
  | (count, none) => power p count out
  | (count, some (call, rest)) =>
      runActions p rest (publish p call (power p count out))

theorem split_projects_law (p : α → α)
    (actions : List (Action α)) (out : Return α) :
    runActions p actions out = runSplit p (splitProjects actions) out := by
  induction actions generalizing out with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | invoke call => rfl
      | project =>
          cases split : splitProjects rest with
          | mk count next =>
              cases next with
              | none =>
                  simpa only [runActions, splitProjects, split, runSplit, power]
                    using ih (project p out)
              | some next =>
                  cases next with
                  | mk call tail =>
                      simpa only [runActions, splitProjects, split, runSplit, power]
                        using ih (project p out)

inductive WordPacket (α : Type) where
  | projects (count : Nat)
  | one (before : Nat) (call : α → α) (after : Nat)
  | two (before : Nat) (first : α → α)
      (between : Nat) (second : α → α) (after : Nat)

def compileActions (actions : List (Action α)) : WordPacket α :=
  match splitProjects actions with
  | (before, none) => .projects before
  | (before, some (first, rest)) =>
      match splitProjects rest with
      | (after, none) => .one before first after
      | (between, some (second, tail)) =>
          .two before first between second tail.length

def runPacket (p : α → α) : WordPacket α → Return α → Return α
  | .projects count, out => power p count out
  | .one before call after, out =>
      power p after (publish p call (power p before out))
  | .two before first between second after, out =>
      power p after
        (publish p second (power p between (publish p first (power p before out))))

theorem power_marker (p : α → α) (n : Nat) (a : α) :
    power p n (.marker a) = .marker (dataPower p n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact ih (p a)

theorem actions_data (p : α → α)
    (actions : List (Action α)) (a : α) :
    runActions p actions (.data a) =
      .data (dataPower p actions.length a) := by
  induction actions generalizing a with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | project => exact ih (p a)
      | invoke call => exact ih (p a)

theorem two_invocations_stable (p first second : α → α)
    (before between : Nat) (out : Return α) :
    ∃ a, publish p second
      (power p between (publish p first (power p before out))) = .data a := by
  cases initial : power p before out with
  | marker a =>
      exact ⟨p (dataPower p between (first a)), by
        change publish p second (power p between (.data (first a))) = _
        rw [power_data]; rfl⟩
  | latent a =>
      exact ⟨second (dataPower p between (p a)), by
        change publish p second (power p between (.marker (p a))) = _
        rw [power_marker]; rfl⟩
  | data a =>
      exact ⟨p (dataPower p between (p a)), by
        change publish p second (power p between (.data (p a))) = _
        rw [power_data]; rfl⟩

/-- Arbitrary interleaving of projections and invocations, not merely a
    repeated loop template, compiles to at most two saved fallbacks. -/
theorem word_packet_eq_reference (p : α → α)
    (actions : List (Action α)) (out : Return α) :
    runPacket p (compileActions actions) out = runActions p actions out := by
  cases firstSplit : splitProjects actions with
  | mk before next =>
      cases next with
      | none =>
          simpa only [compileActions, firstSplit, runPacket, runSplit]
            using (split_projects_law p actions out).symm
      | some next =>
          cases next with
          | mk first rest =>
              cases secondSplit : splitProjects rest with
              | mk between next =>
                  cases next with
                  | none =>
                      have outer := split_projects_law p actions out
                      simp only [firstSplit, runSplit] at outer
                      have inner := split_projects_law p rest
                        (publish p first (power p before out))
                      simp only [secondSplit, runSplit] at inner
                      simpa only [compileActions, firstSplit, secondSplit,
                        runPacket, runSplit] using (outer.trans inner).symm
                  | some next =>
                      cases next with
                      | mk second tail =>
                          have outer := split_projects_law p actions out
                          simp only [firstSplit, runSplit] at outer
                          have inner := split_projects_law p rest
                            (publish p first (power p before out))
                          simp only [secondSplit, runSplit] at inner
                          obtain ⟨a, stable⟩ :=
                            two_invocations_stable p first second before between out
                          have restLaw := (power_data p tail.length a).trans
                            (actions_data p tail a).symm
                          have result : power p tail.length
                              (publish p second
                                (power p between (publish p first (power p before out)))) =
                              runActions p actions out := by
                            rw [stable]
                            calc
                              power p tail.length (.data a) =
                                  runActions p tail (.data a) := restLaw
                              _ = runActions p actions out := by
                                simpa only [stable] using (outer.trans inner).symm
                          simpa only [compileActions, firstSplit, secondSplit, runPacket]
                            using result

theorem word_packet_preserves_observer (p : α → α)
    (actions : List (Action α)) (out : Return α) (observe : Return α → β) :
    observe (runPacket p (compileActions actions) out) =
      observe (runActions p actions out) :=
  congrArg observe (word_packet_eq_reference p actions out)

theorem leading_projection_counterexample :
    runActions (fun n : Nat => n)
      [.project, .invoke (fun _ => 7)] (.latent 0) ≠
    publish (fun n : Nat => n) (fun _ => 7) (.latent 0) := by
  intro impossible
  cases impossible


end Mettapedia.Machines.HETailReturnPacket
