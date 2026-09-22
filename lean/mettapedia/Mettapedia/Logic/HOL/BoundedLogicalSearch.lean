import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.Logic.HOL.Syntax.DecidableEq

/-!
# Bounded proof-producing search in the implicational universal fragment

Search reconstructs the existing indexed proof syntax. It introduces
implications and universals, and chains through supplied hypotheses using
implication and universal elimination. Universal instantiations come from an
explicit finite, context-indexed term inventory; function types are allowed.
Equality here is syntactic equality, not conversion or semantic equality.

The depth bound makes cyclic hypotheses harmless. Failed branches remain in
the event history, so accounting observes the actual attempts, not just the
successful proof tree. Failure of this selected strategy is not refutation.
No completeness for unrestricted higher-order reasoning is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.BoundedLogicalSearch

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A property of the one retained proof carrier, not another proof calculus. -/
inductive Logical : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
    {φ : Formula Const Γ} → ProofSyntax Const Δ φ → Prop where
  | hyp {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (i : Fin Δ.length) :
      Logical (.hyp i)
  | impI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {p q : Formula Const Γ}
      {proof : ProofSyntax Const (p :: Δ) q} : Logical proof → Logical (.impI proof)
  | impE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {p q : Formula Const Γ}
      {major : ProofSyntax Const Δ (.imp p q)} {minor : ProofSyntax Const Δ p} :
      Logical major → Logical minor → Logical (.impE major minor)
  | allI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
      {p : Formula Const (σ :: Γ)} {proof : ProofSyntax Const (weakenHyps Δ) p} :
      Logical proof → Logical (.allI proof)
  | allE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
      {p : Formula Const (σ :: Γ)} (term : Term Const Γ σ)
      {proof : ProofSyntax Const Δ (.all p)} : Logical proof → Logical (.allE term proof)

/-- A returned tree retains both its original sequent and its exact fragment. -/
structure Found {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) where
  proof : ProofSyntax Const Δ φ
  logical : Logical proof

def Found.cast {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {p q : Formula Const Γ}
    (equal : p = q) (found : Found Δ p) : Found Δ q := equal ▸ found

inductive Event where
  | enterGoal
  | inspectHypothesis (occurrence : Nat)
  | introduceImplication
  | introduceUniversal
  | tryImplication
  | tryInstantiation (ordinal : Nat)
  | depthLimit
  deriving DecidableEq, Repr

/-- Search output retains unsuccessful attempts as well as any actual proof. -/
structure Result {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (φ : Formula Const Γ) where
  answer : Option (Found Δ φ)
  events : List Event

def Result.prependEvents {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (events : List Event) (result : Result Δ φ) : Result Δ φ :=
  { result with events := events ++ result.events }

/-- A finite inventory for each actual object context and requested type. -/
abbrev Candidates (Const : Ty Base → Type v) :=
  (Γ : Ctx Base) → (σ : Ty Base) → List (Term Const Γ σ)

variable [DecidableEq Base] [∀ σ, DecidableEq (Const σ)]

/-- Bound variables are legitimate candidates, including function variables. -/
def contextCandidates : Candidates Const
  | [], _ => []
  | σ :: Γ, τ =>
      let prior := (contextCandidates Γ τ).map (weaken (σ := σ))
      if same : τ = σ then by
        subst τ
        exact .var .vz :: prior
      else prior

/-- Choose the first success, retaining every earlier failed branch. -/
def first {Index : Type w} {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (attempt : Index → Result Δ φ) :
    List Index → Result Δ φ
  | [] => ⟨none, []⟩
  | index :: rest =>
      let tried := attempt index
      match tried.answer with
      | some _ => tried
      | none => (first attempt rest).prependEvents tried.events

def lookup {Γ : Ctx Base} (Δ : List (Formula Const Γ)) (goal : Formula Const Γ) :
    Result Δ goal :=
  first (fun occurrence =>
    if equal : Δ.get occurrence = goal then
      ⟨some ((Found.mk (.hyp occurrence) (.hyp occurrence)).cast equal),
        [.inspectHypothesis occurrence.val]⟩
    else ⟨none, [.inspectHypothesis occurrence.val]⟩) (List.finRange Δ.length)

/-- Chain from one supplied proof; every recursive elimination decreases depth.
Premise search is supplied by the enclosing, strictly smaller goal search. -/
def chain (candidates : Candidates Const) {Γ : Ctx Base}
    (Δ : List (Formula Const Γ)) (prove : (p : Formula Const Γ) → Result Δ p)
    (fuel : Nat) (hypothesis goal : Formula Const Γ) (known : Found Δ hypothesis) :
    Result Δ goal :=
      if same : hypothesis = goal then
        ⟨some (known.cast same), []⟩
      else
        match fuel with
        | 0 => ⟨none, [.depthLimit]⟩
        | fuel + 1 =>
            match hypothesis with
            | .imp premise conclusion =>
                let argument := prove premise
                match argument.answer with
                | none => ⟨none, .tryImplication :: argument.events⟩
                | some checked =>
                    (chain candidates Δ prove fuel conclusion goal
                      ⟨.impE known.proof checked.proof,
                        .impE known.logical checked.logical⟩).prependEvents
                      (.tryImplication :: argument.events)
            | @Term.all _ _ σ _ body =>
                first (fun pair =>
                  (chain candidates Δ prove fuel (instantiate pair.1 body) goal
                    ⟨.allE pair.1 known.proof, .allE pair.1 known.logical⟩).prependEvents
                    [.tryInstantiation pair.2]) (candidates Γ σ).zipIdx
            | _ => ⟨none, []⟩
termination_by fuel

/-- Bounded backward search over actual sequents. Introductions extend the
correct hypothesis or object context; no fresh-name heuristic is involved. -/
def search (candidates : Candidates Const) :
    Nat → {Γ : Ctx Base} → (Δ : List (Formula Const Γ)) →
      (goal : Formula Const Γ) → Result Δ goal
  | 0, _, Δ, goal =>
      let direct := lookup Δ goal
      match direct.answer with
      | some _ => direct.prependEvents [.enterGoal]
      | none => direct.prependEvents [.enterGoal, .depthLimit]
  | fuel + 1, _, Δ, goal =>
      let introduced : Result Δ goal :=
        match goal with
        | .imp premise conclusion =>
            let child := search candidates fuel (premise :: Δ) conclusion
            ⟨child.answer.map (fun found => ⟨.impI found.proof, .impI found.logical⟩),
              .introduceImplication :: child.events⟩
        | .all body =>
            let child := search candidates fuel (weakenHyps Δ) body
            ⟨child.answer.map (fun found => ⟨.allI found.proof, .allI found.logical⟩),
              .introduceUniversal :: child.events⟩
        | _ => ⟨none, []⟩
      match introduced.answer with
      | some _ => introduced.prependEvents [.enterGoal]
      | none =>
          (first (fun occurrence =>
            (chain candidates Δ (search candidates fuel Δ) fuel (Δ.get occurrence) goal
              ⟨.hyp occurrence, .hyp occurrence⟩).prependEvents
              [.inspectHypothesis occurrence.val]) (List.finRange Δ.length)).prependEvents
            (.enterGoal :: introduced.events)

/-- Accepted source trees establish the original extensional judgment.
This theorem makes no claim about completeness or raw-byte checking. -/
theorem sound {candidates : Candidates Const} {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {goal : Formula Const Γ} {fuel : Nat}
    {found : Found Δ goal}
    (_success : (search candidates fuel Δ goal).answer = some found) :
    ExtDerivation Const Δ goal := found.proof.erase

/-- Resource interpretation folds the actual event history in execution order. -/
def Result.cost {Grade : Type w} [AddMonoid Grade] {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {goal : Formula Const Γ}
    (charge : Event → Grade) (result : Result Δ goal) : Grade :=
  result.events.foldr (fun event rest => charge event + rest) 0

omit [DecidableEq Base] [∀ σ, DecidableEq (Const σ)] in
theorem Result.unit_cost {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {goal : Formula Const Γ} (result : Result Δ goal) :
    result.cost (fun _ => (1 : Nat)) = result.events.length := by
  have fold_length (events : List Event) :
      events.foldr (fun _ rest => 1 + rest) 0 = events.length := by
    induction events with
    | nil => rfl
    | cons event rest ih =>
        simp only [List.foldr_cons, List.length_cons]
        rw [ih]
        exact Nat.add_comm _ _
  exact fold_length result.events

omit [DecidableEq Base] [∀ σ, DecidableEq (Const σ)] in
theorem Result.cost_prependEvents {Grade : Type w} [AddMonoid Grade] {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {goal : Formula Const Γ}
    (charge : Event → Grade) (events : List Event) (result : Result Δ goal) :
    (result.prependEvents events).cost charge =
      events.foldr (fun event rest => charge event + rest) 0 + result.cost charge := by
  induction events with
  | nil => simp [cost, prependEvents]
  | cons event rest ih => simpa [cost, prependEvents, add_assoc] using congrArg (charge event + ·) ih

#print axioms sound
#print axioms Result.cost_prependEvents

end Mettapedia.Logic.HOL.BoundedLogicalSearch
