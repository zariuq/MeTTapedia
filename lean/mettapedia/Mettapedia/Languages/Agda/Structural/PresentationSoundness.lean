import Mettapedia.Languages.Agda.Structural.Presentation
import Mettapedia.Languages.Agda.Structural.RuleInterpretation
import Mettapedia.Languages.Agda.Structural.PresentationCompleteness

/-!
# Soundness of the actual structural computation rule table

Every firing tree of the 29 authored root and generated congruence declarations
produces a compatible structural step at its exact scoped endpoints. Local
valuations and the result supplied by each congruence premise are retained.
The proof interprets arbitrary occurrences, not a selected set of examples.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

/-- Compatible structural evidence at the endpoints of a polynomial judgment. -/
def StepAt (j : Judgment Authored.algebra) : Type := Step j.2.2.1 j.2.2.2

/-- A canonical singleton occurrence keeps all the local rule data. -/
private def singletonOccurrence (r : LocalRule sig) (Γ : Ctx sig)
    (values : Valuation (M := r.1) Authored.algebra Γ)
    (close : Sub sig r.2.conclusion.ctx Γ) : Instance [r] Authored.algebra where
  index := 0
  ambient := Γ
  valuation := values
  close := close

/-- An interpretation of one declaration from the interpretation of its children. -/
private def RuleSound (r : LocalRule sig) : Type :=
  (Γ : Ctx sig) → (values : Valuation (M := r.1) Authored.algebra Γ) →
  (close : Sub sig r.2.conclusion.ctx Γ) →
  ((position : Fin r.2.premises.length) →
    StepAt (childJudgment [r] Authored.algebra
      (singletonOccurrence r Γ values close) position)) →
  StepAt (conclusionJudgment [r] Authored.algebra
    (singletonOccurrence r Γ values close))

private def root_rule_sound (index : Fin Authored.roots.length) :
    RuleSound (Authored.roots.get index) := by
  intro Γ values close _children
  let event : Instance Authored.roots Authored.algebra := ⟨index, Γ, values, close⟩
  exact .root (Authored.rootOfOccurrence event)

private def congruence_rule_sound {s : sig.Srt} (op : sig.Op s)
    (position : Fin (sig.arity op).length) :
    RuleSound (IntrinsicScopedLocalCongruence.rule (S := sig) op position) := by
  intro Γ values close children
  let args := IntrinsicScopedLocalCongruence.inputs (S := sig) op position values
  let result : Term sig (((sig.arity op).get position).1 ++ Γ)
      ((sig.arity op).get position).2 := values ⟨0, Nat.zero_lt_succ _⟩
  have close_eq : close = IntrinsicScopedLocalCongruence.emptyClose Γ := by
    funext resultSort var
    nomatch var
  have occurrence_eq :
      singletonOccurrence (IntrinsicScopedLocalCongruence.rule (S := sig) op position) Γ values close =
      IntrinsicScopedLocalCongruence.occurrence (S := sig) op position args result := by
    cases close_eq
    exact congrArg (fun vals =>
      singletonOccurrence (IntrinsicScopedLocalCongruence.rule (S := sig) op position)
        Γ vals (IntrinsicScopedLocalCongruence.emptyClose Γ))
      (IntrinsicScopedLocalCongruence.valuation_recovery (S := sig) op position values).symm
  have child : StepAt (childJudgment [IntrinsicScopedLocalCongruence.rule (S := sig) op position]
      Authored.algebra (IntrinsicScopedLocalCongruence.occurrence (S := sig) op position args result)
      ⟨0, Nat.zero_lt_succ _⟩) := by
    have canonicalChildren := Eq.mp
      (congrArg (fun event : Instance
          [IntrinsicScopedLocalCongruence.rule (S := sig) op position] Authored.algebra =>
        (p : Fin ([IntrinsicScopedLocalCongruence.rule (S := sig) op position].get event.index).2.premises.length) →
          StepAt (childJudgment [IntrinsicScopedLocalCongruence.rule (S := sig) op position]
            Authored.algebra event p)) occurrence_eq) children
    exact canonicalChildren ⟨0, Nat.zero_lt_succ _⟩
  have concreteChild := Eq.mp
    (congrArg StepAt (IntrinsicScopedLocalCongruence.child_occurrence (S := sig) op position args result)) child
  have concreteStep : StepAt
      (⟨Γ, s, .op op args,
        .op op (IntrinsicScopedLocalCongruence.replaceArg args position result)⟩ :
        Judgment Authored.algebra) :=
    .congr op (IntrinsicScopedLocalCongruence.compatibleAt (S := sig) (R := Root)
      args position result concreteChild)
  rw [occurrence_eq]
  exact Eq.mpr
    (congrArg StepAt (IntrinsicScopedLocalCongruence.conclusion_occurrence (S := sig) op position args result))
    concreteStep

/-- A Type-valued table provides a constructor interpretation at every list index. -/
private def SoundTable : List (LocalRule sig) → Type
  | [] => PUnit
  | r :: rs => RuleSound r × SoundTable rs

private def SoundTable.get : {rs : List (LocalRule sig)} → SoundTable rs →
    (index : Fin rs.length) → RuleSound (rs.get index)
  | _ :: _, table, ⟨0, _⟩ => table.1
  | _ :: _, table, ⟨i + 1, h⟩ => table.2.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

private def SoundTable.ofGet : (rs : List (LocalRule sig)) →
    ((index : Fin rs.length) → RuleSound (rs.get index)) → SoundTable rs
  | [], _ => ⟨⟩
  | _ :: rs, witnesses => ⟨witnesses 0, ofGet rs (fun i => witnesses i.succ)⟩

private def SoundTable.append : {rs ss : List (LocalRule sig)} →
    SoundTable rs → SoundTable ss → SoundTable (rs ++ ss)
  | [], _, _, right => right
  | _ :: _, _, left, right => ⟨left.1, left.2.append right⟩

private def SoundTable.map {α : Type} (f : α → LocalRule sig)
    (sound : (a : α) → RuleSound (f a)) : (xs : List α) → SoundTable (xs.map f)
  | [] => ⟨⟩
  | a :: xs => ⟨sound a, map f sound xs⟩

private def SoundTable.flatMap {α : Type} (f : α → List (LocalRule sig))
    (sound : (a : α) → SoundTable (f a)) : (xs : List α) → SoundTable (xs.flatMap f)
  | [] => ⟨⟩
  | a :: xs => (sound a).append (flatMap f sound xs)

private def rootTable : SoundTable Authored.roots :=
  SoundTable.ofGet Authored.roots root_rule_sound

private def congruenceTable : SoundTable Authored.generatedCongruences :=
  SoundTable.flatMap _
    (fun ⟨_, op⟩ => SoundTable.map _ (congruence_rule_sound op)
      (List.finRange (sig.arity op).length)) Authored.operatorsWithArguments

private def computationTable : SoundTable Authored.computationRules :=
  rootTable.append congruenceTable

/-- Interpret an arbitrary constructor occurrence and all of its ordered children. -/
def interpretOccurrence (event : Instance Authored.computationRules Authored.algebra)
    (children : (position : Fin (Authored.computationRules.get event.index).2.premises.length) →
      StepAt (childJudgment Authored.computationRules Authored.algebra event position)) :
    StepAt (conclusionJudgment Authored.computationRules Authored.algebra event) :=
  computationTable.get event.index event.ambient event.valuation event.close children

/-- Every actual authored firing tree gives a structural step at the same endpoints. -/
def interpretTree {j : Judgment Authored.algebra}
    (tree : Tree Authored.computationRules Authored.algebra j) : StepAt j := by
  match tree with
  | .roll shape children =>
    exact shape.2 ▸ interpretOccurrence shape.1 (fun position => interpretTree (children position))

/-- Exact source, target, context, and sort are retained in the table soundness map. -/
def treeToStep {Γ : Ctx sig} {s : Srt} {source target : Term sig Γ s}
    (tree : Tree Authored.computationRules Authored.algebra ⟨Γ, s, source, target⟩) :
    Step source target := interpretTree tree

private def soundAtAddress {r : LocalRule sig} (address : Authored.Address r) : RuleSound r := by
  rcases address with ⟨index, same⟩
  subst r
  exact computationTable.get index

private theorem soundAtAddress_root (index : Fin Authored.roots.length) :
    soundAtAddress (Authored.rootAddress index) = root_rule_sound index := by
  rcases index with ⟨n, bound⟩
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | n + 6 =>
    exfalso
    simp only [Authored.roots, List.length_cons, List.length_nil] at bound
    omega

set_option maxHeartbeats 800000 in
private theorem soundAtAddress_congruence {s : sig.Srt} (op : sig.Op s)
    (position : Fin (sig.arity op).length) :
    soundAtAddress (Authored.congruenceAddress op position) =
      congruence_rule_sound op position := by
  cases op <;> rcases position with ⟨n, bound⟩
  all_goals simp only [sig, List.length_cons, List.length_nil] at bound
  all_goals
    match n with
    | 0 => first | rfl | (exfalso; omega)
    | 1 => first | rfl | (exfalso; omega)
    | n + 2 => exfalso; omega

private theorem interpret_fireAddress {r : LocalRule sig} (address : Authored.Address r)
    (Γ : Ctx sig) (values : Valuation (M := r.1) Authored.algebra Γ)
    (close : Sub sig r.2.conclusion.ctx Γ)
    (children : (position : Fin r.2.premises.length) →
      Tree Authored.computationRules Authored.algebra
        (childJudgment [r] Authored.algebra (Authored.localOccurrence r Γ values close) position)) :
    interpretTree (Authored.fireAddress address Γ values close children) =
      soundAtAddress address Γ values close (fun position => interpretTree (children position)) := by
  rcases address with ⟨index, same⟩
  subst r
  rfl

/-- Interpreting a transported tree transports the resulting structural evidence. -/
theorem interpretTree_transport {j k : Judgment Authored.algebra} (same : j = k)
    (tree : Tree Authored.computationRules Authored.algebra j) :
    interpretTree (same ▸ tree) = same ▸ interpretTree tree := by
  cases same
  rfl

private theorem interpretTree_mp {j k : Judgment Authored.algebra} (same : j = k)
    (tree : Tree Authored.computationRules Authored.algebra j) :
    interpretTree ((congrArg (Tree Authored.computationRules Authored.algebra) same).mp tree) =
      (congrArg StepAt same).mp (interpretTree tree) := by
  cases same
  rfl

private theorem interpretTree_mpr {j k : Judgment Authored.algebra} (same : j = k)
    (tree : Tree Authored.computationRules Authored.algebra k) :
    interpretTree ((congrArg (Tree Authored.computationRules Authored.algebra) same).mpr tree) =
      (congrArg StepAt same).mpr (interpretTree tree) := by
  cases same
  rfl

private theorem root_transport {j k : Judgment Authored.algebra} (same : j = k)
    (root : Authored.RootAt j) :
    same ▸ (CompatibleDerivations.Step.root root : StepAt j) =
      (CompatibleDerivations.Step.root (same ▸ root) : StepAt k) := by
  cases same
  rfl

private theorem mp_mpr {α β : Type} (same : α = β) (value : β) :
    same.mp (same.mpr value) = value := by
  cases same
  rfl

/-- The root encoding retains its complete structural root derivation. -/
theorem interpretTree_rootTree {Γ : Ctx sig} {s : sig.Srt}
    {source target : Term sig Γ s} (root : Root source target) :
    interpretTree (Authored.rootTree root) = CompatibleDerivations.Step.root root := by
  unfold Authored.rootTree
  dsimp only
  erw [interpretTree_transport, interpret_fireAddress, soundAtAddress_root]
  change (Authored.shapeOfRoot root).2 ▸
    CompatibleDerivations.Step.root
      (Authored.rootOfOccurrence (Authored.shapeOfRoot root).1) = _
  erw [root_transport]
  exact congrArg (fun r => CompatibleDerivations.Step.root r)
    (Authored.rootOfShape_shapeOfRoot root)

private theorem congruence_rule_sound_canonical {Γ : Ctx sig} {s : sig.Srt}
    (op : sig.Op s) (args : Args sig (sig.arity op) Γ)
    (position : Fin (sig.arity op).length)
    (result : Term sig (((sig.arity op).get position).1 ++ Γ) ((sig.arity op).get position).2)
    (children : (p : Fin 1) → StepAt
      (childJudgment [IntrinsicScopedLocalCongruence.rule (S := sig) op position]
        Authored.algebra (IntrinsicScopedLocalCongruence.occurrence op position args result) p)) :
    Eq.mp (congrArg StepAt (IntrinsicScopedLocalCongruence.conclusion_occurrence op position args result))
      (congruence_rule_sound op position Γ
        (IntrinsicScopedLocalCongruence.valuation op position args result)
        (IntrinsicScopedLocalCongruence.emptyClose Γ) children) =
      CompatibleDerivations.Step.congr op
        (IntrinsicScopedLocalCongruence.compatibleAt args position result
          (Eq.mp (congrArg StepAt (IntrinsicScopedLocalCongruence.child_occurrence op position args result))
            (children 0))) := by
  cases op
  all_goals first
    | exact Fin.elim0 position
    | (match args with
       | .cons head .nil =>
         dsimp only [congruence_rule_sound]
         exact mp_mpr _ _)
    | (match args with
       | .cons first (.cons second .nil) =>
         dsimp only [congruence_rule_sound]
         exact mp_mpr _ _)

/-- Encoding and interpreting a generated congruence retains its selected child. -/
theorem interpretTree_congruenceTree {Γ : Ctx sig} {s : sig.Srt}
    (op : sig.Op s) (args : Args sig (sig.arity op) Γ)
    (position : Fin (sig.arity op).length)
    (result : Term sig (((sig.arity op).get position).1 ++ Γ) ((sig.arity op).get position).2)
    (child : Tree Authored.computationRules Authored.algebra
      ⟨((sig.arity op).get position).1 ++ Γ, ((sig.arity op).get position).2,
        IntrinsicScopedLocalCongruence.getArg args position, result⟩) :
    interpretTree (Authored.congruenceTree op args position result child) =
      CompatibleDerivations.Step.congr op
        (IntrinsicScopedLocalCongruence.compatibleAt args position result (interpretTree child)) := by
  unfold Authored.congruenceTree
  dsimp only
  erw [interpretTree_mp (IntrinsicScopedLocalCongruence.conclusion_occurrence op position args result),
    interpret_fireAddress, soundAtAddress_congruence,
    congruence_rule_sound_canonical]
  erw [interpretTree_mpr (IntrinsicScopedLocalCongruence.child_occurrence op position args result)]
  congr 2
  exact mp_mpr _ _

/-- Positive control: the empty-spine declaration fires in the actual table. -/
def emptySpineTree {Γ : Ctx sig} (head : Tm Γ) :
    Tree Authored.computationRules Authored.algebra
      ⟨Γ, .term, eliminate head nil, head⟩ := by
  let event : Instance Authored.computationRules Authored.algebra :=
    ⟨⟨2, by decide⟩, Γ, Authored.emptyValues head,
      IntrinsicScopedLocalCongruence.emptyClose Γ⟩
  refine .roll ⟨event, ?_⟩ ?_
  · exact Authored.empty_conclusion (Authored.emptyValues head)
  · intro position
    exact Fin.elim0 position

/-- Positive control: interpreting that declaration retains its exact endpoints. -/
def emptySpineStep {Γ : Ctx sig} (head : Tm Γ) : Step (eliminate head nil) head :=
  treeToStep (emptySpineTree head)

/-- Negative control: the table cannot fabricate a firing from a scoped variable. -/
theorem variable_has_no_tree {Γ : Ctx sig} {s : Srt} (v : Var Γ s)
    (target : Term sig Γ s) :
    IsEmpty (Tree Authored.computationRules Authored.algebra
      ⟨Γ, s, .var v, target⟩) :=
  ⟨fun tree => (variable_inert v target).false (treeToStep tree)⟩

#print axioms interpretOccurrence
#print axioms interpretTree
#print axioms treeToStep
#print axioms interpretTree_transport
#print axioms interpretTree_rootTree
#print axioms interpretTree_congruenceTree
#print axioms emptySpineStep
#print axioms variable_has_no_tree

end Mettapedia.Languages.Agda.Structural
