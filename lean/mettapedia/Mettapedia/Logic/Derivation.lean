import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

/-!
# Finitary rule closure and replayable derivations

This module contains the logic-independent syntax of finitary inference:

* `Derives rules` is the least predicate closed under `rules`;
* `RuleWitness` makes rule instances decidable without changing their meaning;
* `Derivation` is a finitely branching certificate tree;
* `Derivation.valid` replays a certificate;
* `Derives.exists_derivation` reconstructs a certificate from a derivation when
  the rule predicate has an exact witness interface.

No object logic, operational semantics, GSLT, OSLF, or NIK structure is fixed
here.  Those layers consume this generic closure.
-/

set_option autoImplicit false

namespace Mettapedia.Logic

universe u v

variable {J : Type u}

/-- The least set closed under a finitary rule predicate. -/
inductive Derives (rules : List J → J → Prop) : J → Prop where
  | node (premises : List J) (conclusion : J) (rule : rules premises conclusion)
      (subderivations : ∀ premise ∈ premises, Derives rules premise) :
      Derives rules conclusion

/-- Any predicate closed under the rules contains every derivable judgment. -/
theorem Derives.least {rules : List J → J → Prop} (P : J → Prop)
    (closed : ∀ premises conclusion, rules premises conclusion →
      (∀ premise ∈ premises, P premise) → P conclusion) :
    ∀ {judgment : J}, Derives rules judgment → P judgment := by
  intro judgment derivation
  induction derivation with
  | node premises conclusion rule _ ih =>
      exact closed premises conclusion rule ih

/-- Derivability is monotone in its rule predicate. -/
theorem Derives.mono {rules rules' : List J → J → Prop}
    (mapRule : ∀ premises conclusion, rules premises conclusion →
      rules' premises conclusion)
    {judgment : J} (derivation : Derives rules judgment) :
    Derives rules' judgment := by
  refine Derives.least (Derives rules') ?_ derivation
  intro premises conclusion rule subderivations
  exact Derives.node premises conclusion (mapRule premises conclusion rule) subderivations

/-- A decidable rule-instance test whose witnesses cover a rule predicate
exactly. -/
structure RuleWitness (rules : List J → J → Prop) : Type (max u (v + 1)) where
  W : Type v
  isInstance : W → List J → J → Bool
  sound : ∀ witness premises conclusion,
    isInstance witness premises conclusion = true → rules premises conclusion
  complete : ∀ premises conclusion, rules premises conclusion →
    ∃ witness, isInstance witness premises conclusion = true

/-- A finitely branching tree of witnessed rule applications. -/
inductive Derivation (J : Type u) (W : Type v) : Type (max u v) where
  | node (conclusion : J) (witness : W) (n : Nat)
      (children : Fin n → Derivation J W)

namespace Derivation

variable {W : Type v}

def concl : Derivation J W → J
  | .node result _ _ _ => result

/-- Replay checks the rule witness at every certificate node. -/
def valid {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules) :
    Derivation J interface.W → Bool
  | .node result witness _ children =>
      interface.isInstance witness
          (List.ofFn fun i => (children i).concl) result &&
        (List.ofFn fun i => (children i).valid interface).all id

theorem valid_sound {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) :
    ∀ certificate : Derivation J interface.W,
      certificate.valid interface = true →
      Derives rules certificate.concl := by
  intro certificate
  induction certificate with
  | node result witness _ children ih =>
    intro accepted
    simp only [valid, Bool.and_eq_true, List.all_eq_true,
      List.forall_mem_ofFn_iff, id] at accepted
    obtain ⟨ruleAccepted, childrenAccepted⟩ := accepted
    refine Derives.node _ result
      (interface.sound witness _ result ruleAccepted) ?_
    intro premise member
    rw [List.mem_ofFn] at member
    obtain ⟨i, rfl⟩ := member
    exact ih i (childrenAccepted i)

end Derivation

theorem Derives.exists_derivation {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) :
    ∀ {judgment : J}, Derives rules judgment →
      ∃ certificate : Derivation J interface.W,
        certificate.valid interface = true ∧
        certificate.concl = judgment := by
  intro judgment derivation
  induction derivation with
  | node premises conclusion rule _ ih =>
    obtain ⟨witness, witnessValid⟩ := interface.complete premises conclusion rule
    choose children childrenValid using ih
    refine ⟨.node conclusion witness premises.length
      (fun i => children premises[i] (List.getElem_mem i.isLt)), ?_, rfl⟩
    simp only [Derivation.valid, Bool.and_eq_true, List.all_eq_true,
      List.forall_mem_ofFn_iff, id]
    refine ⟨?_, fun i => (childrenValid _ _).1⟩
    have pointwise : (fun i : Fin premises.length =>
        (children premises[i] (List.getElem_mem i.isLt)).concl) =
        fun i => premises[i] := by
      funext i
      exact (childrenValid _ _).2
    have conclusions : (List.ofFn fun i : Fin premises.length =>
        (children premises[i] (List.getElem_mem i.isLt)).concl) = premises := by
      rw [pointwise]
      exact List.ofFn_getElem
    rw [conclusions]
    exact witnessValid

end Mettapedia.Logic
