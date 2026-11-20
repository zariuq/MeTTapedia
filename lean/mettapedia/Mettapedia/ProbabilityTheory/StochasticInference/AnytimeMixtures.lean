import Mettapedia.ProbabilityTheory.StochasticInference.Binary

/-!
# Bounded inference in a binary model grammar

Every unresolved prefix holds the prior mass of its continuations.
Each completed model gives the masses of the evidence and the joint
query and evidence. The unvisited prior mass bounds both the missing
query mass and the missing evidence mass.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.AnytimeMixtures

open Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout

structure Joint where
  masses : Masses
  joint_nonneg : 0 ≤ masses.joint
  included : masses.joint ≤ masses.evidence
  evidence_le_one : masses.evidence ≤ 1

namespace Joint

def zero : Joint := ⟨⟨0, 0⟩, le_rfl, le_rfl, zero_le_one⟩

def mix (p : UnitProbability) (left right : Joint) : Joint where
  masses :=
    ⟨(1 - p.val) * left.masses.joint + p.val * right.masses.joint,
      (1 - p.val) * left.masses.evidence + p.val * right.masses.evidence⟩
  joint_nonneg := add_nonneg (mul_nonneg (sub_nonneg.mpr p.le_one) left.joint_nonneg)
    (mul_nonneg p.nonneg right.joint_nonneg)
  included := add_le_add (mul_le_mul_of_nonneg_left left.included (sub_nonneg.mpr p.le_one))
    (mul_le_mul_of_nonneg_left right.included p.nonneg)
  evidence_le_one := by
    have hl := mul_le_mul_of_nonneg_left left.evidence_le_one (sub_nonneg.mpr p.le_one)
    have hr := mul_le_mul_of_nonneg_left right.evidence_le_one p.nonneg
    linarith

end Joint

structure Summary where
  known : Joint
  remaining : ℚ

structure Sound (summary : Summary) (full : Joint) : Prop where
  query : summary.known.masses.joint ≤ full.masses.joint
  complement : summary.known.masses.evidence - summary.known.masses.joint ≤
    full.masses.evidence - full.masses.joint
  evidence : full.masses.evidence ≤ summary.known.masses.evidence + summary.remaining

def Summary.interval? (summary : Summary) : Option (ℚ × ℚ) :=
  let upperSupport := summary.known.masses.evidence + summary.remaining
  if 0 < upperSupport then
    some (summary.known.masses.joint / upperSupport,
      1 - (summary.known.masses.evidence - summary.known.masses.joint) / upperSupport)
  else none

theorem Sound.interval_sound {summary : Summary} {full : Joint} (sound : Sound summary full)
    (possible : 0 < full.masses.evidence) :
    ∃ low high, summary.interval? = some (low, high) ∧
      low ≤ full.masses.joint / full.masses.evidence ∧
      full.masses.joint / full.masses.evidence ≤ high := by
  let upperSupport := summary.known.masses.evidence + summary.remaining
  have positive : 0 < upperSupport := possible.trans_le sound.evidence
  refine ⟨summary.known.masses.joint / upperSupport,
    1 - (summary.known.masses.evidence - summary.known.masses.joint) / upperSupport, ?_, ?_, ?_⟩
  · simp [Summary.interval?, upperSupport, positive]
  · exact (div_le_div_of_nonneg_left summary.known.joint_nonneg possible sound.evidence).trans
      (div_le_div_of_nonneg_right sound.query possible.le)
  · have bound :=
      (div_le_div_of_nonneg_left (sub_nonneg.mpr summary.known.included) possible sound.evidence).trans
        (div_le_div_of_nonneg_right sound.complement possible.le)
    change full.masses.joint / full.masses.evidence ≤ 1 -
      (summary.known.masses.evidence - summary.known.masses.joint) / upperSupport
    have complement : (full.masses.evidence - full.masses.joint) / full.masses.evidence =
        1 - full.masses.joint / full.masses.evidence := by
      rw [sub_div, div_self possible.ne']
    rw [complement] at bound
    linarith

theorem Sound.no_support {summary : Summary} {full : Joint} (sound : Sound summary full)
    (answer : summary.interval? = none) : full.masses.evidence = 0 := by
  by_contra h
  have positive := lt_of_le_of_ne (full.joint_nonneg.trans full.included) (Ne.symm h)
  obtain ⟨_, _, found, _, _⟩ := sound.interval_sound positive
  rw [found] at answer
  contradiction

/-- The total evidence retained from an earlier snapshot can sharpen the
upper support used by a partial search. -/
def Summary.capEvidence (summary : Summary) (upper : ℚ) : Summary :=
  { summary with remaining := min summary.remaining (upper - summary.known.masses.evidence) }

theorem Sound.capEvidence {summary : Summary} {full : Joint} (sound : Sound summary full)
    (upper : ℚ) (valid : full.masses.evidence ≤ upper) :
    Sound (summary.capEvidence upper) full := by
  refine ⟨sound.query, sound.complement, ?_⟩
  change full.masses.evidence ≤ summary.known.masses.evidence +
    min summary.remaining (upper - summary.known.masses.evidence)
  have h : full.masses.evidence - summary.known.masses.evidence ≤
      min summary.remaining (upper - summary.known.masses.evidence) :=
    le_min (by linarith [sound.evidence]) (sub_le_sub_right valid _)
  linarith

/-- A branch makes one feature choice. Only completed leaves are read. -/
inductive Trace : Nat → Type where
  | pending {depth : Nat} : Trace depth
  | evaluated : Trace 0
  | branch {depth : Nat} : Trace depth → Trace depth → Trace (depth + 1)

def fullMass (p : UnitProbability) (leaf : List Bool → Joint) : Nat → Joint
  | 0 => leaf []
  | depth + 1 => Joint.mix p (fullMass p (fun path => leaf (false :: path)) depth)
      (fullMass p (fun path => leaf (true :: path)) depth)

theorem fullMass_evidence_mono (p : UnitProbability) (left right : List Bool → Joint)
    (depth : Nat) (compare : ∀ path, (left path).masses.evidence ≤ (right path).masses.evidence) :
    (fullMass p left depth).masses.evidence ≤ (fullMass p right depth).masses.evidence := by
  induction depth generalizing left right with
  | zero => exact compare []
  | succ depth ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (ih _ _ (fun path => compare (false :: path)))
      (sub_nonneg.mpr p.le_one)) (mul_le_mul_of_nonneg_left (ih _ _ (fun path => compare (true :: path)))
      p.nonneg)

def priorMass (p : UnitProbability) : List Bool → ℚ
  | [] => 1
  | bit :: rest => p.atOutcome bit * priorMass p rest

/-- The full mixture likelihood dominates every hypothesis weighted by its
prior. With positive masses, taking negative logs gives the code-length
cost bound for this model grammar. -/
theorem dominates (p : UnitProbability) (leaf : List Bool → Joint) (path : List Bool) :
    priorMass p path * (leaf path).masses.evidence ≤
      (fullMass p leaf path.length).masses.evidence := by
  induction path generalizing leaf with
  | nil => simp [priorMass, fullMass]
  | cons bit rest ih =>
    let lo := (fullMass p (fun path => leaf (false :: path)) rest.length).masses.evidence
    let hi := (fullMass p (fun path => leaf (true :: path)) rest.length).masses.evidence
    have loNonneg : 0 ≤ lo :=
      (fullMass p _ _).joint_nonneg.trans (fullMass p _ _).included
    have hiNonneg : 0 ≤ hi :=
      (fullMass p _ _).joint_nonneg.trans (fullMass p _ _).included
    cases bit
    · change (1 - p.val) * priorMass p rest * (leaf (false :: rest)).masses.evidence ≤
        (1 - p.val) * lo + p.val * hi
      rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left (ih _) (sub_nonneg.mpr p.le_one)).trans
        (le_add_of_nonneg_right (mul_nonneg p.nonneg hiNonneg))
    · change p.val * priorMass p rest * (leaf (true :: rest)).masses.evidence ≤
        (1 - p.val) * lo + p.val * hi
      rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left (ih _) p.nonneg).trans
        (le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr p.le_one) loNonneg))

def Trace.summarize (p : UnitProbability) (leaf : List Bool → Joint) :
    {depth : Nat} → Trace depth → Summary
  | _, .pending => ⟨Joint.zero, 1⟩
  | _, .evaluated => ⟨leaf [], 0⟩
  | _, .branch left right =>
    let lo := left.summarize p (fun path => leaf (false :: path))
    let hi := right.summarize p (fun path => leaf (true :: path))
    ⟨Joint.mix p lo.known hi.known, (1 - p.val) * lo.remaining + p.val * hi.remaining⟩

theorem Trace.summarize_sound (p : UnitProbability) {depth : Nat} (trace : Trace depth)
    (leaf : List Bool → Joint) :
    Sound (trace.summarize p leaf) (fullMass p leaf depth) := by
  induction trace generalizing leaf with
  | pending =>
    constructor
    · exact (fullMass p leaf _).joint_nonneg
    · simpa [summarize, Joint.zero] using sub_nonneg.mpr (fullMass p leaf _).included
    · simpa [summarize, Joint.zero] using (fullMass p leaf _).evidence_le_one
  | evaluated => constructor <;> simp [summarize, fullMass]
  | branch left right hl hr =>
    let dl := hl (fun path => leaf (false :: path))
    let dr := hr (fun path => leaf (true :: path))
    have nonnegLeft := sub_nonneg.mpr p.le_one
    constructor
    · simpa only [summarize, fullMass, Joint.mix] using
        add_le_add (mul_le_mul_of_nonneg_left dl.query nonnegLeft)
          (mul_le_mul_of_nonneg_left dr.query p.nonneg)
    · simp only [summarize, fullMass, Joint.mix]
      have l := mul_le_mul_of_nonneg_left dl.complement nonnegLeft
      have r := mul_le_mul_of_nonneg_left dr.complement p.nonneg
      linarith only [l, r]
    · simp only [summarize, fullMass, Joint.mix]
      have l := mul_le_mul_of_nonneg_left dl.evidence nonnegLeft
      have r := mul_le_mul_of_nonneg_left dr.evidence p.nonneg
      linarith only [l, r]

def Trace.pendingPaths : {depth : Nat} → Trace depth → List (List Bool)
  | _, .pending => [[]]
  | _, .evaluated => []
  | _, .branch left right =>
    left.pendingPaths.map (false :: ·) ++ right.pendingPaths.map (true :: ·)

def Trace.visitedPaths : {depth : Nat} → Trace depth → List (List Bool)
  | _, .pending => []
  | _, .evaluated => [[]]
  | _, .branch left right =>
    left.visitedPaths.map (false :: ·) ++ right.visitedPaths.map (true :: ·)

theorem Trace.closed_summary {depth : Nat} (trace : Trace depth) (p : UnitProbability)
    (leaf : List Bool → Joint) (exhausted : trace.pendingPaths = []) :
    (trace.summarize p leaf).remaining = 0 ∧
      (trace.summarize p leaf).known.masses = (fullMass p leaf depth).masses := by
  induction trace generalizing leaf with
  | pending => simp [pendingPaths] at exhausted
  | evaluated => exact ⟨rfl, rfl⟩
  | branch left right il ir =>
    have ends : left.pendingPaths = [] ∧ right.pendingPaths = [] := by
      simpa [pendingPaths] using exhausted
    have lo := il (fun path => leaf (false :: path)) ends.1
    have hi := ir (fun path => leaf (true :: path)) ends.2
    simp [summarize, fullMass, Joint.mix, lo.1, hi.1, lo.2, hi.2]

/-- Spend one step expanding an unresolved prefix or evaluating a leaf. -/
def Trace.advance : {depth : Nat} → Trace depth → List Bool → Trace depth
  | 0, .pending, [] => .evaluated
  | _ + 1, .pending, [] => .branch .pending .pending
  | _, .branch left right, false :: tail => .branch (left.advance tail) right
  | _, .branch left right, true :: tail => .branch left (right.advance tail)
  | _, trace, _ => trace

def completeWork : Nat → Nat
  | 0 => 1
  | depth + 1 => completeWork depth + completeWork depth + 1

def Trace.workLeft : {depth : Nat} → Trace depth → Nat
  | depth, .pending => completeWork depth
  | _, .evaluated => 0
  | _, .branch left right => left.workLeft + right.workLeft

theorem Trace.work_zero_iff {depth : Nat} (trace : Trace depth) :
    trace.workLeft = 0 ↔ trace.pendingPaths = [] := by
  induction trace with
  | @pending depth => cases depth <;> simp [workLeft, pendingPaths, completeWork]
  | evaluated => simp [workLeft, pendingPaths]
  | branch left right lo hi => simp [workLeft, pendingPaths, lo, hi]

theorem Trace.advance_spends_one {depth : Nat} (trace : Trace depth) (path : List Bool)
    (pending : path ∈ trace.pendingPaths) :
    (trace.advance path).workLeft + 1 = trace.workLeft := by
  induction trace generalizing path with
  | @pending depth =>
    have root : path = [] := by simpa [pendingPaths] using pending
    subst path
    cases depth <;> simp [advance, workLeft, completeWork]
  | evaluated => simp [pendingPaths] at pending
  | branch left right lo hi =>
    cases path with
    | nil => simp [pendingPaths, List.mem_map] at pending
    | cons bit rest =>
      cases bit
      · have valid : rest ∈ left.pendingPaths := by
          simpa [pendingPaths, List.mem_map] using pending
        have smaller := lo rest valid
        simp only [advance, workLeft]
        omega
      · have valid : rest ∈ right.pendingPaths := by
          simpa [pendingPaths, List.mem_map] using pending
        have smaller := hi rest valid
        simp only [advance, workLeft]
        omega

namespace Controls

private def prior : UnitProbability := ⟨1 / 4, by decide +kernel, by decide +kernel⟩
private def first : Joint := ⟨⟨1 / 4, 1 / 2⟩, by decide +kernel, by decide +kernel, by decide +kernel⟩
private def second : Joint := ⟨⟨1 / 4, 1 / 4⟩, by decide +kernel, le_rfl, by decide +kernel⟩
private def leaf (path : List Bool) : Joint := if path == [true] then second else first

theorem exact_answer_from_completed_work :
    ((Trace.pending (depth := 1)).summarize prior leaf).interval? = some (0, 1) ∧
      ((Trace.branch .evaluated .pending).summarize prior leaf).interval? = some (3 / 10, 7 / 10) ∧
      ((Trace.branch .evaluated .evaluated).summarize prior leaf).interval? = some (4 / 7, 4 / 7) := by
  decide +kernel

theorem zero_evidence_is_exposed_after_completion :
    ((Trace.branch .evaluated .evaluated).summarize prior (fun _ => Joint.zero)).interval? = none := by
  decide +kernel

end Controls

end Mettapedia.ProbabilityTheory.StochasticInference.AnytimeMixtures
