import Mettapedia.OSLF.Framework.InitialModalSchema
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# What isolates Pure: internalization of the hypothetical judgment

Metamath Zero and Isabelle/Pure are both schematic frameworks — rules are
data; the engine contributes substitution and replay.  This module proves the
property that separates them, over the neutral `Derives` machinery of
`InitialModalSchema`:

* **Weakening** (`mono_context`): hypothetical derivability is monotone in
  the context.
* **Deduction** (`deduction`): `A :: Γ ⊢ B` iff `Γ ⊢ A ⟹ B`.
* **Internalization** (`internalize`): `Γ ⊢ B` iff `[] ⊢ Γ ⟹⋯⟹ B`.

Internalization is the precise sense in which Pure's meta-implication is
special: the judgment structure itself (hypotheses) is reflected into the
object language, so rules become theorems and compose by `⟹`-elimination —
which is why a library grows smoothly on top of Pure.  The MM0 shape
(`SchematicRules`) requires no structure on judgments and has no such
reflection: hypothetical reasoning stays external, in the checker's stack.
Pure's `⋀` and `≡` internalize the two remaining judgment structures
(schematic generality, definitional replacement); their composition with the
schematic layer is future work, as noted in `InitialModalSchema`.

The second half places any witnessed rule system as an object of the
authority category (`derivesTheory`, `derivesContract`); the Pure-shape and
MM0-shape canaries become authority nodes whose consistency is by model
qualification, never by replay alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PureInternalization

open Mettapedia.OSLF.Framework.InitialModalSchema
open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.OSLF.Formula

universe u v w

/-! ## Weakening, deduction, internalization for the Pure shape -/

section Pure

variable {Atom : Type u}
variable (objectRules : List (List (PureForm Atom) × PureForm Atom))

/-- Hypothetical derivability is monotone in the context. -/
theorem mono_context {Γ Δ : List (PureForm Atom)} {C : PureForm Atom}
    (subset : ∀ B, B ∈ Γ → B ∈ Δ)
    (d : Derives (HypotheticalRules objectRules) (Γ, C)) :
    Derives (HypotheticalRules objectRules) (Δ, C) := by
  have general :
      ∀ {j : Hyp Atom}, Derives (HypotheticalRules objectRules) j →
        ∀ Δ' : List (PureForm Atom), (∀ B, B ∈ j.1 → B ∈ Δ') →
          Derives (HypotheticalRules objectRules) (Δ', j.2) := by
    intro j d
    refine Derives.least
      (fun j => ∀ Δ' : List (PureForm Atom), (∀ B, B ∈ j.1 → B ∈ Δ') →
        Derives (HypotheticalRules objectRules) (Δ', j.2)) ?_ d
    rintro hyps ⟨Γ₀, C₀⟩ rule ih Δ' extended
    rcases rule with ⟨rfl, mem⟩ | ⟨r, hr, rfl, rfl⟩ | ⟨A, B, rfl, rfl⟩ | ⟨A, rfl⟩
    · exact Derives.node [] _ (Or.inl ⟨rfl, extended _ mem⟩) (by simp)
    · refine Derives.node (r.1.map (fun A => (Δ', A))) _
        (Or.inr (Or.inl ⟨r, hr, rfl, rfl⟩)) ?_
      intro h hmem
      simp only [List.mem_map] at hmem
      obtain ⟨A, hA, rfl⟩ := hmem
      exact ih (Γ₀, A) (List.mem_map_of_mem hA) Δ' extended
    · refine Derives.node [(A :: Δ', B)] _
        (Or.inr (Or.inr (Or.inl ⟨A, B, rfl, rfl⟩))) ?_
      intro h hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      refine ih (A :: Γ₀, B) (by simp) (A :: Δ') ?_
      intro X hX
      simp only [List.mem_cons] at hX ⊢
      rcases hX with rfl | hX
      · exact Or.inl rfl
      · exact Or.inr (extended X hX)
    · refine Derives.node [(Δ', .imp A C₀), (Δ', A)] _
        (Or.inr (Or.inr (Or.inr ⟨A, rfl⟩))) ?_
      intro h hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | h'
      · exact ih (Γ₀, .imp A C₀) (by simp) Δ' extended
      · exact ih (Γ₀, A) (by simp) Δ' extended
      · cases h'
  exact general d Δ subset

/-- **Deduction.**  Discharging a hypothesis is the same as proving the
internal implication. -/
theorem deduction {Γ : List (PureForm Atom)} {A B : PureForm Atom} :
    Derives (HypotheticalRules objectRules) (A :: Γ, B) ↔
      Derives (HypotheticalRules objectRules) (Γ, .imp A B) := by
  constructor
  · intro d
    exact Derives.node [(A :: Γ, B)] _
      (Or.inr (Or.inr (Or.inl ⟨A, B, rfl, rfl⟩)))
      (by intro h hm; simp only [List.mem_singleton] at hm; subst hm; exact d)
  · intro d
    have dImp : Derives (HypotheticalRules objectRules) (A :: Γ, .imp A B) :=
      mono_context objectRules (fun X hX => List.mem_cons_of_mem A hX) d
    have dA : Derives (HypotheticalRules objectRules) (A :: Γ, A) :=
      Derives.node [] _ (Or.inl ⟨rfl, List.mem_cons_self⟩) (by simp)
    exact Derives.node [(A :: Γ, .imp A B), (A :: Γ, A)] _
      (Or.inr (Or.inr (Or.inr ⟨A, rfl⟩)))
      (by
        intro h hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | rfl | h'
        · exact dImp
        · exact dA
        · cases h')

/-- Iterated internal implication, peeling the context head-first. -/
def internImp (Γ : List (PureForm Atom)) (B : PureForm Atom) : PureForm Atom :=
  Γ.foldl (fun acc A => .imp A acc) B

/-- **Internalization.**  The hypothetical judgment is fully reflected into
the object language: contexts are eliminable in favour of `⟹`.  This is the
property that makes rules first-class theorems in Pure, and it is absent by
design from the MM0 shape, whose judgments carry no required structure. -/
theorem internalize {Γ : List (PureForm Atom)} {B : PureForm Atom} :
    Derives (HypotheticalRules objectRules) (Γ, B) ↔
      Derives (HypotheticalRules objectRules) ([], internImp Γ B) := by
  induction Γ generalizing B with
  | nil => exact Iff.rfl
  | cons A Γ ih =>
    calc Derives (HypotheticalRules objectRules) (A :: Γ, B)
        ↔ Derives (HypotheticalRules objectRules) (Γ, .imp A B) :=
          deduction objectRules
      _ ↔ Derives (HypotheticalRules objectRules) ([], internImp Γ (.imp A B)) :=
          ih
      _ ↔ _ := Iff.rfl

end Pure

/-! ## Any witnessed rule system is an authority node -/

section AuthorityNode

variable {J : Type u}

/-- The theory of a rule system with an independently supplied meaning whose
rules are sound for it. -/
def derivesTheory (rules : List J → J → Prop) (Meaning : J → Prop)
    (sound : ∀ hyps concl, rules hyps concl →
      (∀ h ∈ hyps, Meaning h) → Meaning concl) :
    TheoryFamily.{0, 0, u} Unit where
  Signature := Unit
  signatureOf _ := ()
  Claim _ := J
  Scope _ := Derives rules
  Meaning _ := Meaning
  scope_sound _ _ d := Derives.least Meaning sound d

/-- Its exact replay contract, from the generic certificate machinery. -/
def derivesContract [DecidableEq J] {rules : List J → J → Prop}
    {Meaning : J → Prop}
    {sound : ∀ hyps concl, rules hyps concl →
      (∀ h ∈ hyps, Meaning h) → Meaning concl}
    (rw : RuleWitness.{u, v} rules) :
    AuthorityContract (derivesTheory rules Meaning sound) where
  Certificate _ := Derivation J rw.W
  checker _ := replayChecker rw
  scopeAuthority _ := replayChecker_authority rw

end AuthorityNode

/-! ### The Pure-shape and MM0-shape canaries as authority nodes -/

/-- The Pure-shape node over the empty object-rule list, with valuation
semantics as its meaning. -/
noncomputable def pureNode :=
  derivesTheory (HypotheticalRules (Atom := String) [])
    HypotheticalCanary.Valid HypotheticalCanary.rules_valid

/-- Consistency of the Pure node, by model qualification. -/
theorem pureNode_consistent :
    ¬ pureNode.Scope () ([], HypotheticalCanary.a) :=
  HypotheticalCanary.atom_not_derivable

/-- The schematic (MM0-shape) canary rules are sound for the
empty-reduction, all-true-atoms model. -/
theorem schematicRules_sound :
    ∀ hyps concl, SchematicCanary.rules hyps concl →
      (∀ h ∈ hyps, ∀ p, sem (fun _ _ => False) (fun _ _ => True) h p) →
      ∀ p, sem (fun _ _ => False) (fun _ _ => True) concl p := by
  rintro hyps concl ⟨ax, hax, σ, rfl, rfl⟩ hhyps p
  simp only [SchematicCanary.axioms, List.mem_cons, List.not_mem_nil,
    or_false] at hax
  rcases hax with rfl | rfl
  · have hA := hhyps (SchematicCanary.substAtoms σ (.atom "A")) (by simp) p
    have hAB := hhyps
      (SchematicCanary.substAtoms σ (.imp (.atom "A") (.atom "B"))) (by simp) p
    simp only [SchematicCanary.substAtoms, sem] at hA hAB ⊢
    exact hAB hA
  · simp only [SchematicCanary.substAtoms, sem]
    intro hA _
    exact hA

/-- The MM0-shape node (modus ponens + K over OSLF formulas), with the
empty-reduction all-true-atoms model as its meaning. -/
noncomputable def schematicNode :=
  derivesTheory SchematicCanary.rules
    (fun φ => ∀ p, sem (fun _ _ => False) (fun _ _ => True) φ p)
    schematicRules_sound

/-- Consistency of the MM0-shape node, by model qualification. -/
theorem schematicNode_consistent :
    ¬ schematicNode.Scope () OSLFFormula.bot :=
  SchematicCanary.bot_not_derivable

#print axioms mono_context
#print axioms deduction
#print axioms internalize
#print axioms pureNode_consistent
#print axioms schematicNode_consistent

end Mettapedia.OSLF.Framework.PureInternalization
