import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# The tier-0 kernel built from steps: presentations, checking, and the step machine

A **presentation** gives the judgments `J`, rule names `R`, rule arguments `A`, and for each
rule name and arguments the rule instance: its ordered premises and its conclusion
(`Presentation.inst`). Instantiation stands for the matching that the MeTTa kernel performs when it
reads a stored rule schema with the node's ground arguments. A premise is either a judgment, proved
by a child, or a **side condition** (`Presentation.side`), decided by the kernel and consuming no
child (distinctness, non-occurrence, substitution results).

* `Derivable P hyps j`: the least set of judgments containing `hyps` and closed under the rule
  instances. This is the declarative layer: it mentions no proof object.
* A **proof** is a list of nodes `(rule, arguments, children)` in topological order; a child is a
  hypothesis `.hyp i` or an earlier node `.node n`. `run` walks it and returns the conclusions, and
  `check P hyps proof root goal` accepts when the walk succeeds and the root concludes the goal.
* `Step` is the machine of the MeTTa kernel `tier0_seq.metta`: the next node becomes an
  obligation (`open`), premises are discharged one at a time by a child's theorem or by a side
  condition, and a discharged obligation becomes a theorem (`close`).

## Results

* `run_sound`, `check_sound`: an accepted proof proves its goal.
* `check_complete`: every derivable judgment has an accepted proof (`check_iff_derivable`).
* `Step.deterministic`: the machine has at most one next state; checking is a function of the
  proof, not of a schedule.
* `reaches_accept_iff_check`: the machine reaches an accepting state exactly when `check` accepts.

## Controls

`Controls` checks a two-rule presentation: an accepted proof, a proof whose child does not meet the
premise, a proof whose root proves another judgment, and a proof citing a later node.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero

universe u

/-- A tier-0 presentation. -/
structure Presentation where
  J : Type u
  R : Type u
  A : Type u
  inst : R → A → Option (List J × J)
  side : J → Bool

variable (P : Presentation.{u})

/-- Declarative derivability from hypotheses. Side-condition premises hold by `side`; every
other premise must be derivable. -/
inductive Derivable (hyps : List P.J) : P.J → Prop
  | hyp {j : P.J} : j ∈ hyps → Derivable hyps j
  | rule {r : P.R} {a : P.A} {ps : List P.J} {c : P.J} :
      P.inst r a = some (ps, c) → (∀ p ∈ ps, P.side p = false → Derivable hyps p) →
      Derivable hyps c

/-- A child of a node: a hypothesis of the claim or an earlier node. -/
inductive Kid where
  | hyp (i : ℕ)
  | node (n : ℕ)
  deriving DecidableEq, Repr

/-- A node: a rule name, its arguments, and its children in premise order. -/
abbrev Node := P.R × P.A × List Kid

variable {P}

/-- The judgment a child names, given the hypotheses and the conclusions so far. -/
def lookup (hyps done : List P.J) : Kid → Option P.J
  | .hyp i => hyps[i]?
  | .node n => done[n]?

variable [DecidableEq P.J]

/-- Discharge premises in order: a side condition consumes no child, a judgment premise consumes the
next child, whose judgment must be exactly the premise. -/
def discharge (look : Kid → Option P.J) : List P.J → List Kid → Bool
  | [], [] => true
  | [], _ :: _ => false
  | p :: ps, kids =>
      if P.side p then discharge look ps kids
      else match kids with
        | [] => false
        | k :: ks => decide (look k = some p) && discharge look ps ks

/-- Walk a proof from the conclusions `done`. -/
def run (hyps : List P.J) : List P.J → List (Node P) → Option (List P.J)
  | done, [] => some done
  | done, (r, a, kids) :: rest =>
      match P.inst r a with
      | none => none
      | some (ps, c) => if discharge (lookup hyps done) ps kids then run hyps (done ++ [c]) rest else none

/-- The checker: the walk succeeds and the root names the goal. -/
def check (hyps : List P.J) (proof : List (Node P)) (root : Kid) (goal : P.J) : Bool :=
  match run hyps [] proof with
  | none => false
  | some done => decide (lookup hyps done root = some goal)

/-! ## Soundness -/

omit [DecidableEq P.J] in
theorem lookup_derivable {hyps done : List P.J} (doneOk : ∀ j ∈ done, Derivable P hyps j)
    {k : Kid} {j : P.J} (found : lookup hyps done k = some j) : Derivable P hyps j := by
  cases k with
  | hyp i => exact Derivable.hyp (List.mem_of_getElem? found)
  | node n => exact doneOk j (List.mem_of_getElem? found)

theorem discharge_sound {hyps done : List P.J} (doneOk : ∀ j ∈ done, Derivable P hyps j) :
    ∀ (ps : List P.J) (kids : List Kid), discharge (lookup hyps done) ps kids = true →
      ∀ p ∈ ps, P.side p = false → Derivable P hyps p
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [discharge] at h
  | p :: ps, kids, h => by
      intro q mem notSide
      by_cases sp : P.side p = true
      · have rest : discharge (lookup hyps done) ps kids = true := by
          simpa [discharge, sp] using h
        rcases List.mem_cons.mp mem with rfl | mem'
        · simp [sp] at notSide
        · exact discharge_sound doneOk ps kids rest q mem' notSide
      · have sp' : P.side p = false := by simpa using sp
        cases kids with
        | nil => simp [discharge, sp'] at h
        | cons k ks =>
            simp only [discharge, sp', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
              decide_eq_true_eq] at h
            rcases List.mem_cons.mp mem with rfl | mem'
            · exact lookup_derivable doneOk h.1
            · exact discharge_sound doneOk ps ks h.2 q mem' notSide

/-- **Soundness of the walk**: every conclusion is derivable. -/
theorem run_sound {hyps : List P.J} :
    ∀ (done : List P.J) (proof : List (Node P)) (out : List P.J),
      (∀ j ∈ done, Derivable P hyps j) → run hyps done proof = some out →
        ∀ j ∈ out, Derivable P hyps j
  | done, [], out, doneOk, h => by
      simp only [run, Option.some.injEq] at h
      subst h; exact doneOk
  | done, (r, a, kids) :: rest, out, doneOk, h => by
      simp only [run] at h
      cases hi : P.inst r a with
      | none => simp [hi] at h
      | some pc =>
          obtain ⟨ps, c⟩ := pc
          simp only [hi] at h
          by_cases hd : discharge (lookup hyps done) ps kids = true
          · simp only [hd, ↓reduceIte] at h
            refine run_sound (done ++ [c]) rest out ?_ h
            intro j mem
            rcases List.mem_append.mp mem with inDone | inC
            · exact doneOk j inDone
            · rw [List.mem_singleton.mp inC]
              exact Derivable.rule hi (discharge_sound doneOk ps kids hd)
          · simp [hd] at h

/-- **Soundness of checking**: an accepted proof proves its goal. -/
theorem check_sound {hyps : List P.J} {proof : List (Node P)} {root : Kid} {goal : P.J}
    (accepted : check hyps proof root goal = true) : Derivable P hyps goal := by
  unfold check at accepted
  cases h : run hyps [] proof with
  | none => simp [h] at accepted
  | some done =>
      simp only [h, decide_eq_true_eq] at accepted
      exact lookup_derivable (run_sound [] proof done (by simp) h) accepted

/-! ## Completeness -/

/-- Shift the node children of a proof placed after `k` earlier nodes. -/
def Kid.shift (k : ℕ) : Kid → Kid
  | .hyp i => .hyp i
  | .node n => .node (k + n)

/-- A proof placed after `k` earlier nodes. -/
def shiftProof (k : ℕ) (proof : List (Node P)) : List (Node P) :=
  proof.map fun x => (x.1, x.2.1, x.2.2.map (Kid.shift k))

omit [DecidableEq P.J] in
theorem lookup_shift (hyps pre done : List P.J) (k : Kid) :
    lookup hyps (pre ++ done) (k.shift pre.length) = lookup hyps done k := by
  cases k with
  | hyp i => rfl
  | node n => simp [lookup, Kid.shift, List.getElem?_append_right]

theorem discharge_shift (hyps pre done : List P.J) :
    ∀ (ps : List P.J) (kids : List Kid),
      discharge (lookup hyps (pre ++ done)) ps (kids.map (Kid.shift pre.length)) =
        discharge (lookup hyps done) ps kids
  | [], [] => rfl
  | [], _ :: _ => rfl
  | p :: ps, kids => by
      by_cases sp : P.side p = true
      · simp only [discharge, sp, ↓reduceIte]
        exact discharge_shift hyps pre done ps kids
      · have sp' : P.side p = false := by simpa using sp
        cases kids with
        | nil => simp [discharge, sp']
        | cons k ks =>
            simp only [discharge, sp', Bool.false_eq_true, ↓reduceIte, List.map_cons,
              lookup_shift, discharge_shift hyps pre done ps ks]

theorem run_shift (hyps pre : List P.J) :
    ∀ (done : List P.J) (proof : List (Node P)),
      run hyps (pre ++ done) (shiftProof pre.length proof) =
        (run hyps done proof).map (pre ++ ·)
  | done, [] => by simp [run, shiftProof]
  | done, (r, a, kids) :: rest => by
      simp only [shiftProof, List.map_cons, run]
      cases hi : P.inst r a with
      | none => simp
      | some pc =>
          obtain ⟨ps, c⟩ := pc
          simp only
          rw [discharge_shift hyps pre done ps kids]
          by_cases hd : discharge (lookup hyps done) ps kids = true
          · simp only [hd, ↓reduceIte]
            have := run_shift hyps pre (done ++ [c]) rest
            simpa [shiftProof, List.append_assoc] using this
          · simp [hd]

theorem run_append (hyps : List P.J) :
    ∀ (done : List P.J) (first second : List (Node P)),
      run hyps done (first ++ second) = (run hyps done first).bind fun mid => run hyps mid second
  | done, [], second => by simp [run]
  | done, (r, a, kids) :: rest, second => by
      simp only [List.cons_append, run]
      cases hi : P.inst r a with
      | none => simp
      | some pc =>
          obtain ⟨ps, c⟩ := pc
          simp only
          by_cases hd : discharge (lookup hyps done) ps kids = true
          · simp only [hd, ↓reduceIte]
            exact run_append hyps (done ++ [c]) rest second
          · simp [hd]

/-- A proof of `j` from the empty walk: its conclusions and the child naming `j`. -/
def Proves (hyps : List P.J) (j : P.J) (proof : List (Node P)) (root : Kid) : Prop :=
  ∃ out, run hyps [] proof = some out ∧ lookup hyps out root = some j

/-- Proofs of a list of premises, laid end to end, with the children naming them. -/
theorem proofs_of_list (hyps : List P.J) :
    ∀ (ps : List P.J), (∀ p ∈ ps, P.side p = false → ∃ proof root, Proves hyps p proof root) →
      ∃ (proof : List (Node P)) (kids : List Kid) (out : List P.J),
        run hyps [] proof = some out ∧ discharge (lookup hyps out) ps kids = true
  | [], _ => ⟨[], [], [], by simp [run], by simp [discharge]⟩
  | p :: ps, hp => by
      obtain ⟨proof, kids, out, hrun, hdis⟩ :=
        proofs_of_list hyps ps fun q mem => hp q (List.mem_cons_of_mem p mem)
      by_cases sp : P.side p = true
      · exact ⟨proof, kids, out, hrun, by simp [discharge, sp, hdis]⟩
      · have sp' : P.side p = false := by simpa using sp
        obtain ⟨proofP, rootP, outP, hrunP, hlookP⟩ := hp p (List.mem_cons_self) sp'
        -- the premise's proof first, then the others' proof shifted after it
        refine ⟨proofP ++ shiftProof outP.length proof, rootP :: kids.map (Kid.shift outP.length),
          outP ++ out, ?_, ?_⟩
        · rw [run_append, hrunP]
          simp only [Option.bind_some]
          have := run_shift hyps outP [] proof
          simpa [hrun] using this
        · simp only [discharge, sp', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
            decide_eq_true_eq]
          refine ⟨?_, ?_⟩
          · cases rootP with
            | hyp i => simpa [lookup] using hlookP
            | node n =>
                have hn : n < outP.length := by
                  by_contra hge
                  simp [lookup, List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hlookP
                simpa [lookup, List.getElem?_append_left hn] using hlookP
          · rw [discharge_shift hyps outP out ps kids]; exact hdis

/-- **Completeness**: every derivable judgment has an accepted proof. -/
theorem derivable_proves {hyps : List P.J} {j : P.J} (h : Derivable P hyps j) :
    ∃ proof root, Proves hyps j proof root := by
  induction h with
  | hyp mem =>
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
      exact ⟨[], .hyp i, [], by simp [run], by simp [lookup, hi]⟩
  | @rule r a ps c hi _ ih =>
      obtain ⟨proof, kids, out, hrun, hdis⟩ := proofs_of_list hyps ps ih
      refine ⟨proof ++ [(r, a, kids)], .node out.length, out ++ [c], ?_, by simp [lookup]⟩
      rw [run_append, hrun]
      simp [run, hi, hdis]

theorem check_complete {hyps : List P.J} {goal : P.J} (h : Derivable P hyps goal) :
    ∃ proof root, check hyps proof root goal = true := by
  obtain ⟨proof, root, out, hrun, hlook⟩ := derivable_proves h
  exact ⟨proof, root, by simp [check, hrun, hlook]⟩

/-- Accepted proofs exist exactly for derivable judgments (the native proof type is inhabited
exactly at the provable judgments). -/
theorem check_iff_derivable (hyps : List P.J) (goal : P.J) :
    (∃ proof root, check hyps proof root goal = true) ↔ Derivable P hyps goal :=
  ⟨fun ⟨_, _, h⟩ => check_sound h, check_complete⟩

/-! ## The step machine of `tier0_seq.metta` -/

/-- A machine state: conclusions so far, the open obligation (conclusion, remaining premises,
remaining children), and the nodes still to walk. -/
structure State (P : Presentation.{u}) where
  done : List P.J
  ob : Option (P.J × List P.J × List Kid)
  walk : List (Node P)

/-- One kernel step. -/
inductive Step (hyps : List P.J) : State P → State P → Prop
  /-- The next node's rule instance becomes the obligation. -/
  | «open» {done r a kids rest ps c} : P.inst r a = some (ps, c) →
      Step hyps ⟨done, none, (r, a, kids) :: rest⟩ ⟨done, some (c, ps, kids), rest⟩
  /-- A judgment premise is discharged by the next child's theorem. -/
  | dischargeChild {done c p ps k ks walk} : P.side p = false → lookup hyps done k = some p →
      Step hyps ⟨done, some (c, p :: ps, k :: ks), walk⟩ ⟨done, some (c, ps, ks), walk⟩
  /-- A side-condition premise is discharged by the kernel's check. -/
  | dischargeSide {done c p ps ks walk} : P.side p = true →
      Step hyps ⟨done, some (c, p :: ps, ks), walk⟩ ⟨done, some (c, ps, ks), walk⟩
  /-- A discharged obligation becomes a theorem. -/
  | close {done c walk} : Step hyps ⟨done, some (c, [], []), walk⟩ ⟨done ++ [c], none, walk⟩

omit [DecidableEq P.J] in
/-- The machine has at most one next state. -/
theorem Step.deterministic {hyps : List P.J} {s t t' : State P}
    (h : Step hyps s t) (h' : Step hyps s t') : t = t' := by
  cases h with
  | «open» hi => cases h' with | «open» hi' => rw [hi] at hi'; cases hi'; rfl
  | dischargeChild sp hl =>
      cases h' with
      | dischargeChild => rfl
      | dischargeSide sp' => rw [sp] at sp'; cases sp'
  | dischargeSide sp =>
      cases h' with
      | dischargeChild sp' => rw [sp] at sp'; cases sp'
      | dischargeSide => rfl
  | close => cases h' with | close => rfl

/-- Accepting states: nothing left to walk, no obligation, and the root names the goal. -/
def Accepting (hyps : List P.J) (root : Kid) (goal : P.J) (s : State P) : Prop :=
  s.ob = none ∧ s.walk = [] ∧ lookup hyps s.done root = some goal

/-- Discharging an obligation step by step. -/
theorem discharge_steps {hyps done : List P.J} {walk : List (Node P)} {c : P.J} :
    ∀ (ps : List P.J) (kids : List Kid), discharge (lookup hyps done) ps kids = true →
      Relation.ReflTransGen (Step hyps) ⟨done, some (c, ps, kids), walk⟩ ⟨done, some (c, [], []), walk⟩
  | [], [], _ => Relation.ReflTransGen.refl
  | [], _ :: _, h => by simp [discharge] at h
  | p :: ps, kids, h => by
      by_cases sp : P.side p = true
      · have rest : discharge (lookup hyps done) ps kids = true := by simpa [discharge, sp] using h
        exact Relation.ReflTransGen.head (Step.dischargeSide sp) (discharge_steps ps kids rest)
      · have sp' : P.side p = false := by simpa using sp
        cases kids with
        | nil => simp [discharge, sp'] at h
        | cons k ks =>
            simp only [discharge, sp', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
              decide_eq_true_eq] at h
            exact Relation.ReflTransGen.head (Step.dischargeChild sp' h.1) (discharge_steps ps ks h.2)

/-- A successful walk is a run of the machine. -/
theorem run_steps {hyps : List P.J} :
    ∀ (done : List P.J) (proof : List (Node P)) (out : List P.J), run hyps done proof = some out →
      Relation.ReflTransGen (Step hyps) ⟨done, none, proof⟩ ⟨out, none, []⟩
  | done, [], out, h => by
      simp only [run, Option.some.injEq] at h; subst h; exact Relation.ReflTransGen.refl
  | done, (r, a, kids) :: rest, out, h => by
      simp only [run] at h
      cases hi : P.inst r a with
      | none => simp [hi] at h
      | some pc =>
          obtain ⟨ps, c⟩ := pc
          simp only [hi] at h
          by_cases hd : discharge (lookup hyps done) ps kids = true
          · simp only [hd, ↓reduceIte] at h
            refine Relation.ReflTransGen.head (Step.open hi) ?_
            refine Relation.ReflTransGen.trans (discharge_steps ps kids hd) ?_
            exact Relation.ReflTransGen.head Step.close (run_steps (done ++ [c]) rest out h)
          · simp [hd] at h

/-- The result a state is heading for: the walk's result from here. Every step preserves it. -/
def outcome (hyps : List P.J) (s : State P) : Option (List P.J) :=
  match s.ob with
  | none => run hyps s.done s.walk
  | some (c, ps, kids) =>
      if discharge (lookup hyps s.done) ps kids then run hyps (s.done ++ [c]) s.walk else none

theorem Step.outcome_eq {hyps : List P.J} {s t : State P} (h : Step hyps s t) :
    outcome hyps t = outcome hyps s := by
  cases h with
  | «open» hi => simp [outcome, run, hi]
  | dischargeChild sp hl => simp [outcome, discharge, sp, hl]
  | dischargeSide sp => simp [outcome, discharge, sp]
  | close => simp [outcome, discharge]

theorem outcome_reach {hyps : List P.J} {s t : State P}
    (h : Relation.ReflTransGen (Step hyps) s t) : outcome hyps t = outcome hyps s := by
  induction h with
  | refl => rfl
  | tail _ step ih => rw [step.outcome_eq, ih]

/-- **The machine reaches acceptance exactly when the checker accepts.** -/
theorem reaches_accept_iff_check (hyps : List P.J) (proof : List (Node P)) (root : Kid)
    (goal : P.J) :
    (∃ s, Relation.ReflTransGen (Step hyps) ⟨[], none, proof⟩ s ∧ Accepting hyps root goal s) ↔
      check hyps proof root goal = true := by
  constructor
  · rintro ⟨⟨done, ob, walk⟩, reach, hob, hwalk, hlook⟩
    simp only at hob hwalk hlook
    subst hob hwalk
    have same := outcome_reach reach
    simp only [outcome, run] at same
    simp [check, ← same, hlook]
  · intro accepted
    unfold check at accepted
    cases hrun : run hyps [] proof with
    | none => simp [hrun] at accepted
    | some out =>
        simp only [hrun, decide_eq_true_eq] at accepted
        exact ⟨⟨out, none, []⟩, run_steps [] proof out hrun, rfl, rfl, accepted⟩

/-! ## Controls -/

namespace Controls

/-- Formulas of a two-rule presentation: atoms and implication. -/
inductive F where
  | atom (n : ℕ)
  | imp (a b : F)
  deriving DecidableEq, Repr

/-- `k`: `a → b → a` with no premises; `mp`: from `a → b` and `a`, `b`. -/
inductive Rl where
  | k
  | mp
  deriving DecidableEq, Repr

abbrev pres : Presentation.{0} where
  J := F
  R := Rl
  A := F × F
  inst
    | .k, (a, b) => some ([], .imp a (.imp b a))
    | .mp, (a, b) => some ([.imp a b, a], b)
  side _ := false

instance : DecidableEq pres.J := inferInstanceAs (DecidableEq F)

def p : F := .atom 0
def q : F := .atom 1

/-- From the hypothesis `p`, `q → p`: `k` then `mp`. -/
def good : List (Node pres) := [(Rl.k, (p, q)), (Rl.mp, (p, .imp q p))].zip
  [[], [Kid.node 0, Kid.hyp 0]] |>.map fun x => (x.1.1, x.1.2, x.2)

theorem good_accepted : check (P := pres) [p] good (.node 1) (.imp q p) = true := by decide

/-- The same proof claimed for another goal is refused. -/
theorem wrong_goal_refused : check (P := pres) [p] good (.node 1) (.imp p q) = false := by decide

/-- A child that does not meet the premise: `mp` cites `q` where `p` is needed. -/
def badChild : List (Node pres) := [(Rl.k, (p, q), []), (Rl.mp, (p, .imp q p), [Kid.node 0, Kid.hyp 1])]

theorem badChild_refused : check (P := pres) [p, q] badChild (.node 1) (.imp q p) = false := by decide

/-- A node citing a later node is refused: proofs are walked in order. -/
def forward : List (Node pres) := [(Rl.mp, (p, .imp q p), [Kid.node 1, Kid.hyp 0]), (Rl.k, (p, q), [])]

theorem forward_refused : check (P := pres) [p] forward (.node 0) (.imp q p) = false := by decide

/-- Without the hypothesis the goal is not derivable by this proof. -/
theorem missing_hyp_refused : check (P := pres) [] good (.node 1) (.imp q p) = false := by decide

end Controls

end Mettapedia.Logic.TierZero
