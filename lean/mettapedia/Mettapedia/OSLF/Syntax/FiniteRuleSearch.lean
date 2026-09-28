import Mettapedia.OSLF.Syntax.FiniteRulePremiseEvidence

/-!
# Evidence-producing bounded execution of finite-premise rules

Candidate selection supplies actual rule instances at the requested judgment.
The executor reads their ordered premises from the presentation, recursively
constructs their children, and returns the resulting native derivation.

Failure of a candidate list refutes the judgment only if that list covers all
root rule instances. A missing coverage proof or an exhausted recursive budget
produces `incomplete`. No failure of bounded search becomes a negative verdict.
Executable instances require executable candidates and premise computation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleSearch

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

universe u v w

inductive Verdict (D : Type u) where
  | established (evidence : D)
  | refuted (impossible : D → False)
  | incomplete

namespace Verdict

def isEstablished {D : Type u} : Verdict D → Bool
  | .established _ => true
  | _ => false

def isRefuted {D : Type u} : Verdict D → Bool
  | .refuted _ => true
  | _ => false

def isIncomplete {D : Type u} : Verdict D → Bool
  | .incomplete => true
  | _ => false

theorem established_iff {D : Type u} (result : Verdict D) :
    result.isEstablished = true ↔ ∃ evidence, result = .established evidence := by
  cases result <;> simp [isEstablished]

theorem refuted_sound {D : Type u} {result : Verdict D}
    (negative : result.isRefuted = true) : D → False := by
  cases result with
  | established _ => cases negative
  | refuted impossible => exact impossible
  | incomplete => cases negative

end Verdict

variable {J : Type u} {D : J → Type v}

/-- Traverse every ordered premise. A disproved premise rules out the rule,
including when another premise has an unfinished search. -/
def premises (solve : (j : J) → Verdict (D j)) :
    (js : List J) → Verdict (Evidence D js)
  | [] => .established (noEvidence D)
  | j :: js =>
      match solve j, premises solve js with
      | .established first, .established rest => .established (consEvidence D first rest)
      | .refuted impossible, _ => .refuted (fun children => impossible (children 0))
      | _, .refuted impossible => .refuted (fun children => impossible (fun p => children p.succ))
      | _, _ => .incomplete

abbrev Selection {A : Type u} (E : A → Type v) (choices : List A) :=
  Σ choice : {a // a ∈ choices}, E choice.val

/-- Try candidates in their declared order. An unfinished earlier candidate
does not prevent a later candidate from producing a proof. -/
def alternatives {A : Type u} {E : A → Type v}
    (solve : (a : A) → Verdict (E a)) :
    (choices : List A) → Verdict (Selection E choices)
  | [] => .refuted (fun candidate => List.not_mem_nil candidate.1.property)
  | a :: choices =>
      match solve a with
      | .established evidence => .established ⟨⟨a, List.mem_cons_self ..⟩, evidence⟩
      | .refuted firstImpossible =>
          match alternatives solve choices with
          | .established candidate =>
              .established ⟨⟨candidate.1.val, List.mem_cons_of_mem a candidate.1.property⟩, candidate.2⟩
          | .refuted restImpossible => .refuted (by
              intro candidate
              rcases List.mem_cons.mp candidate.1.property with equal | member
              · exact firstImpossible (equal ▸ candidate.2)
              · exact restImpossible ⟨⟨candidate.1.val, member⟩, candidate.2⟩)
          | .incomplete => .incomplete
      | .incomplete =>
          match alternatives solve choices with
          | .established candidate =>
              .established ⟨⟨candidate.1.val, List.mem_cons_of_mem a candidate.1.property⟩, candidate.2⟩
          | _ => .incomplete

variable (F : FinitePresentation.{0,u,v} Unit (fun _ => J))

/-- Coverage is checked per goal, independently of the finite candidate list.
Partial candidate generation remains usable for positive proof production. -/
structure Candidates (j : J) where
  rules : List (F.Shape () j)
  exhaustive : Bool
  covers : exhaustive = true → ∀ shape, shape ∈ rules

/-- Every accepted result is constructed from actual presentation nodes.
Refutation carries a proof of non-inhabitation. The budget counts recursive
rule depth; candidate breadth is exactly the supplied finite list. -/
def search (candidates : (j : J) → Candidates F j) :
    Nat → (j : J) → Verdict (F.Derivation () j)
  | 0, _ => .incomplete
  | fuel + 1, j =>
      let batch := candidates j
      match alternatives (fun shape : F.Shape () j =>
          premises (search candidates fuel) (F.premises () j shape)) batch.rules with
      | .established found => .established (.roll found.1.val found.2)
      | .refuted impossible =>
          if covered : batch.exhaustive = true then
            .refuted (fun tree => match tree with
              | .roll shape children =>
                  impossible ⟨⟨shape, batch.covers covered shape⟩, children⟩)
          else .incomplete
      | .incomplete => .incomplete

theorem search_refuted_sound (candidates : (j : J) → Candidates F j)
    (fuel : Nat) (j : J)
    (negative : (search F candidates fuel j).isRefuted = true) :
    F.Derivation () j → False := Verdict.refuted_sound negative

/-- A proof returned by execution satisfies every interpretation closed under
the actual presentation rules. No separate typing verdict is trusted. -/
theorem search_established_model (candidates : (j : J) → Candidates F j)
    (fuel : Nat) (j : J) (R : J → Prop)
    (closed : F.RuleClosed (fun _ => R))
    (positive : (search F candidates fuel j).isEstablished = true) : R j := by
  rcases (Verdict.established_iff _).mp positive with ⟨tree, _⟩
  exact F.derivation_least (fun _ => R) closed () j tree

end Mettapedia.OSLF.Binding.FiniteRuleSearch
