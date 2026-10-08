import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleSignature
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-!
# Substitution on retained formation-sensitive rule trees

Renaming visits the supplied tree and retains every rule and premise position.
Substitution replaces variable leaves by supplied component trees. Under a
binder those component trees are weakened and the new variable is supplied
directly. No proof-irrelevant typing derivation is used to select a replacement
tree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveRuleSignature

open Mettapedia.TypeTheory.JudgmentDerivation

variable {Head : Type} {R : Rules Head}

namespace Tree

set_option backward.isDefEq.respectTransparency false in
/-- The local rule action receives the original children and their already
renamed versions. This isolates dependent rule elimination from recursion. -/
def renamingStep {j : Judgment Head} (rule : Rule R j)
    (premises : (position : Fin (premiseCount rule)) → Tree R (hypothesis rule position))
    (ih : (position : Fin (premiseCount rule)) →
      ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren (hypothesis rule position).arity m},
        CtxRen (hypothesis rule position).context Δ ρ →
          Tree R (judgment Δ (Presentation.rename ρ (hypothesis rule position).subject)
            (Presentation.rename ρ (hypothesis rule position).type))) :
    ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren j.arity m}, CtxRen j.context Δ ρ →
      Tree R (judgment Δ (Presentation.rename ρ j.subject) (Presentation.rename ρ j.type)) := by
  intro m Δ ρ compatible
  cases rule with
  | headType typed => exact Derivation.node (S := signature R) (.headType typed) (fun position => Fin.elim0 position)
  | var index =>
      simpa only [judgment, Presentation.rename, compatible index] using
        (Derivation.node (S := signature R) (Rule.var (R := R) (Γ := Δ) (ρ index))
          (fun position => Fin.elim0 position))
  | const known universeWitness =>
      dsimp only [judgment]
      simpa only [judgment, Presentation.rename, rename_liftClosed] using
        (Derivation.node (S := signature R) (Rule.const (Γ := Δ) known universeWitness) (fun _ => premises 0))
  | piForm universeA universeB joined =>
      exact Derivation.node (S := signature R) (.piForm universeA universeB joined)
        (Fin.cases (ih 0 compatible) (fun _ => ih 1 (compatible.snoc _)))
  | sigmaForm universeA universeB joined =>
      exact Derivation.node (S := signature R) (.sigmaForm universeA universeB joined)
        (Fin.cases (ih 0 compatible) (fun _ => ih 1 (compatible.snoc _)))
  | lamIntro universeWitness =>
      exact Derivation.node (S := signature R) (.lamIntro universeWitness)
        (Fin.cases (ih 0 compatible) (fun _ => ih 1 (compatible.snoc _)))
  | @appElim n Γ g a A B =>
      dsimp only [judgment]
      simpa only [judgment, Presentation.rename, rename_inst0] using
        (Derivation.node (S := signature R) (Rule.appElim (Γ := Δ)
          (g := Presentation.rename ρ g) (a := Presentation.rename ρ a)
          (A := Presentation.rename ρ A) (B := Presentation.rename (liftRen ρ) B))
          (Fin.cases (ih 0 compatible) (fun _ => ih 1 compatible)))
  | @pairIntro n Γ a b A B u universeWitness =>
      have second := ih 2 compatible
      change Tree R (judgment Δ (Presentation.rename ρ b)
        (Presentation.rename ρ (inst0 a B))) at second
      rw [rename_inst0] at second
      exact Derivation.node (S := signature R) (.pairIntro universeWitness)
        (Fin.cases (ih 0 compatible) (Fin.cases (ih 1 compatible) (fun _ => second)))
  | @fstElim n Γ p A B =>
      exact Derivation.node (S := signature R)
        (Rule.fstElim (B := Presentation.rename (liftRen ρ) B)) (fun _ => ih 0 compatible)
  | @sndElim n Γ p A B =>
      dsimp only [judgment]
      simpa only [judgment, Presentation.rename, rename_inst0] using
        (Derivation.node (S := signature R) (Rule.sndElim (Γ := Δ)
          (p := Presentation.rename ρ p) (A := Presentation.rename ρ A)
          (B := Presentation.rename (liftRen ρ) B)) (fun _ => ih 0 compatible))
  | idForm universeWitness =>
      exact Derivation.node (S := signature R) (.idForm universeWitness)
        (Fin.cases (ih 0 compatible)
          (Fin.cases (ih 1 compatible) (fun _ => ih 2 compatible)))
  | reflIntro => exact Derivation.node (S := signature R) .reflIntro (fun _ => ih 0 compatible)
  | cumul order => exact Derivation.node (S := signature R) (.cumul order) (fun _ => ih 0 compatible)
  | convert universeWitness conversion =>
      exact Derivation.node (S := signature R) (.convert universeWitness (conversion.renameTerms ρ))
        (Fin.cases (ih 0 compatible) (fun _ => ih 1 compatible))

/-- Scope-preserving renaming acts on the supplied rules and their children. -/
noncomputable def rename {j : Judgment Head} (tree : Tree R j)
    {m : Nat} {Δ : Ctx Head m} {ρ : Ren j.arity m}
    (compatible : CtxRen j.context Δ ρ) :
    Tree R (judgment Δ (Presentation.rename ρ j.subject) (Presentation.rename ρ j.type)) :=
  Derivation.rec (S := signature R)
    (motive := fun (j : Judgment Head) _ => ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren j.arity m}, CtxRen j.context Δ ρ →
      Tree R (judgment Δ (Presentation.rename ρ j.subject) (Presentation.rename ρ j.type)))
    (fun rule premises ih => renamingStep rule premises ih) tree compatible

@[simp] theorem rename_node {j : Judgment Head} (rule : Rule R j)
    (premises : (position : Fin (premiseCount rule)) → Tree R (hypothesis rule position))
    {m : Nat} {Δ : Ctx Head m} {ρ : Ren j.arity m}
    (compatible : CtxRen j.context Δ ρ) :
    Tree.rename (.node rule premises) compatible =
      renamingStep rule premises (fun position => @Tree.rename Head R _ (premises position)) compatible := rfl

/-- Adding one binder preserves each actual child tree. -/
noncomputable def weaken {n : Nat} {Γ : Ctx Head n} {term type extension : Tm Head n}
    (tree : Tree R (judgment Γ term type)) :
    Tree R (judgment (.snoc Γ extension)
      (Presentation.rename wk term) (Presentation.rename wk type)) :=
  tree.rename (fun _ => rfl)

/-- The identity compatibility proof is available for every raw telescope. -/
theorem identityCompatibility {n : Nat} (Γ : Ctx Head n) :
    CtxRen Γ Γ idRen := by
  intro index
  simp only [idRen, rename_id]

/-- A variable tree has no premise positions to erase or choose. -/
def variableLeaf {n : Nat} (Γ : Ctx Head n) (index : Fin n) :
    Tree R (judgment Γ (.var index) (Ctx.lookup Γ index)) :=
  .node (.var index) (fun position => Fin.elim0 position)

/-- Equal raw renamings and target telescopes give the same retained action. -/
theorem rename_congr {j : Judgment Head} (tree : Tree R j)
    {m : Nat} {Δ Θ : Ctx Head m} {ρ τ : Ren j.arity m}
    (first : CtxRen j.context Δ ρ) (second : CtxRen j.context Θ τ)
    (contexts : Δ = Θ) (renamings : ρ = τ) :
    HEq (tree.rename first) (tree.rename second) := by
  cases contexts
  cases renamings
  rfl

/-- Transporting a judgment and its retained tree commutes with renaming. -/
theorem rename_heq {j k : Judgment Head} (judgments : j = k)
    {first : Tree R j} {second : Tree R k} (trees : HEq first second)
    {m : Nat} {Δ Θ : Ctx Head m} {ρ : Ren j.arity m} {τ : Ren k.arity m}
    (firstCompatibility : CtxRen j.context Δ ρ)
    (secondCompatibility : CtxRen k.context Θ τ)
    (contexts : Δ = Θ) (renamings : HEq ρ τ) :
    HEq (first.rename firstCompatibility) (second.rename secondCompatibility) := by
  cases judgments
  cases contexts
  have maps : ρ = τ := eq_of_heq renamings
  cases maps
  have same : first = second := eq_of_heq trees
  cases same
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A renamed variable remains the corresponding target variable tree. -/
theorem rename_variableLeaf {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ) (index : Fin n) :
    HEq ((variableLeaf (R := R) Γ index).rename compatible)
      (variableLeaf (R := R) Δ (ρ index)) := by
  rw [variableLeaf, rename_node]
  simp only [renamingStep, id_eq, Eq.mp, eqRec_heq_iff]
  rfl

/-- A fiber cast earned by equality of raw types remains a fiber cast after
renaming; its proof does not alter the tree. -/
theorem rename_cast_type {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term A B : Tm Head n} (types : A = B)
    (transport : Tree R (judgment Γ term A) = Tree R (judgment Γ term B))
    (tree : Tree R (judgment Γ term B)) {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ) :
    HEq (Tree.rename (transport.mpr tree) compatible) (tree.rename compatible) := by
  cases types
  rfl

theorem rename_cast_type_heq {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term A B : Tm Head n} (types : A = B)
    (transport : Tree R (judgment Γ term A) = Tree R (judgment Γ term B))
    (tree : Tree R (judgment Γ term B)) {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ)
    {α : Sort _} (other : α) :
    HEq (Tree.rename (transport.mpr tree) compatible) other ↔
      HEq (tree.rename compatible) other := by
  constructor
  · exact fun same => (rename_cast_type types transport tree compatible).symm.trans same
  · exact fun same => (rename_cast_type types transport tree compatible).trans same

/-- The forward form of a raw-type fiber cast has the same retained action. -/
theorem rename_cast_type_mp_heq {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term A B : Tm Head n} (types : A = B)
    (transport : Tree R (judgment Γ term A) = Tree R (judgment Γ term B))
    (tree : Tree R (judgment Γ term A)) {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ)
    {α : Sort _} (other : α) :
    HEq (Tree.rename (transport.mp tree) compatible) other ↔
      HEq (tree.rename compatible) other := by
  cases types
  rfl

/-- A recursively expressed fiber cast is determined by the same raw type
equality; it does not change the renamed rule tree. -/
theorem rename_cast_type_rec_heq {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term A B : Tm Head n} (types : A = B)
    (transport : Tree R (judgment Γ term A) = Tree R (judgment Γ term B))
    (tree : Tree R (judgment Γ term A)) {ρ : Ren n m} (compatible : CtxRen Γ Δ ρ)
    {α : Sort _} (other : α) :
    HEq (Tree.rename (transport ▸ tree) compatible) other ↔
      HEq (tree.rename compatible) other := by
  cases types
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Renaming by the identity retains the exact supplied proof tree. -/
theorem rename_identity {j : Judgment Head} (tree : Tree R j) :
    HEq (tree.rename (identityCompatibility j.context)) tree := by
  refine Derivation.rec (S := signature R)
    (motive := fun j tree => HEq (Tree.rename tree (identityCompatibility j.context)) tree) ?_ tree
  intro j rule premises ih
  rw [rename_node]
  cases rule <;> simp only [renamingStep, id_eq, Eq.mp, Eq.mpr, eqRec_heq_iff]
  all_goals congr 1
  all_goals try simp only [judgment, rename_id, liftRen_id]
  all_goals try congr 1
  all_goals try simp only [rename_id, liftRen_id]
  all_goals try exact proof_irrel_heq _ _
  all_goals first
    | (funext position; exact Fin.elim0 position)
    | (funext position; have same : position = 0 := Subsingleton.elim _ _; cases same; rfl)
    | (apply Function.hfunext rfl; intro position other equal; cases equal)
  all_goals fin_cases position
  all_goals first
    | simpa [premiseCount, hypothesis, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat, judgment,
        Eq.mp, Eq.mpr, eqRec_heq_iff] using ih ⟨0, by dsimp only [premiseCount]; decide⟩
    | simpa [premiseCount, hypothesis, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat, judgment,
        Eq.mp, Eq.mpr, eqRec_heq_iff] using ih ⟨1, by dsimp only [premiseCount]; decide⟩
    | simpa [premiseCount, hypothesis, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat, judgment,
        Eq.mp, Eq.mpr, eqRec_heq_iff] using ih ⟨2, by dsimp only [premiseCount]; decide⟩
    | skip
  all_goals
    simp only [Fin.cases, Fin.induction, Fin.induction.go]
    refine HEq.trans ?_ (ih ⟨1, by dsimp only [premiseCount]; decide⟩)
    apply Tree.rename_congr
    · simp only [hypothesis, Fin.cases, Fin.induction, Fin.induction.go, judgment, rename_id]
    · exact liftRen_id

/-- Compatibility composes through the actual context lookups. -/
theorem composeCompatibility {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {ρ : Ren n m} {τ : Ren m k} (first : CtxRen Γ Δ ρ) (second : CtxRen Δ Θ τ) :
    CtxRen Γ Θ (fun index => τ (ρ index)) := by
  intro index
  rw [second (ρ index), first index, Presentation.rename_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Two successive context renamings retain the same rule tree as their composite. -/
theorem rename_composition {j : Judgment Head} (tree : Tree R j)
    {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k} {ρ : Ren j.arity m} {τ : Ren m k}
    (first : CtxRen j.context Δ ρ) (second : CtxRen Δ Θ τ) :
    HEq ((tree.rename first).rename second)
      (tree.rename (composeCompatibility first second)) := by
  refine Derivation.rec (S := signature R)
    (motive := fun j tree => ∀ {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k}
      {ρ : Ren j.arity m} {τ : Ren m k}, (first : CtxRen j.context Δ ρ) →
        (second : CtxRen Δ Θ τ) →
          HEq (Tree.rename (Tree.rename tree first) second)
            (Tree.rename tree (composeCompatibility first second))) ?_ tree first second
  intro j rule premises ih m k Δ Θ ρ τ first second
  cases rule <;> simp only [rename_node, renamingStep, id_eq]
  case var index =>
    dsimp only [judgment, Presentation.rename] at ρ first ⊢
    rw [rename_cast_type_mp_heq (first index)]
    simp only [rename_node, renamingStep, id_eq, Eq.mp, eqRec_heq_iff, heq_eqRec_iff]
    rfl
  all_goals first
    | rfl
    | (dsimp only [judgment, Presentation.rename] at ρ first ⊢
       rw [rename_cast_type_heq (by simp only [rename_inst0, rename_liftClosed, Presentation.rename])]
       simp only [rename_node, renamingStep, id_eq, Eq.mpr, eqRec_heq_iff])
    | skip
  all_goals try simp only [Eq.mp, heq_eqRec_iff]
  all_goals congr 1
  all_goals try simp only [judgment, Presentation.rename_comp]
  all_goals try congr 1
  all_goals try simp only [Presentation.rename_comp]
  all_goals try exact proof_irrel_heq _ _
  all_goals try simp only [Presentation.rename, Presentation.rename_comp, liftRen_comp_apply]
  all_goals apply Function.hfunext rfl
  all_goals intro position other equal
  all_goals cases equal
  all_goals try fin_cases position
  all_goals try simp [premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
    Eq.mpr, eqRec_heq_iff, heq_eqRec_iff]
  case pairIntro.e_4.refl.«2» =>
    rw [rename_cast_type_rec_heq (rename_inst0 _ _ _)]
    have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
    dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
      judgment] at child
    exact child first second
  all_goals first
    | (have child := @ih ⟨0, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child first second)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child first second)
    | (have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child first second)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       refine HEq.trans (child (first.snoc _) (second.snoc _)) ?_
       apply rename_congr
       · simp only [Presentation.rename_comp]
       · funext index; exact liftRen_comp_apply _ _ index)

end Tree

/-- Component trees are retained independently, including repeated terms. -/
abbrev TreeSubstitution {n m : Nat} (Γ : Ctx Head n) (Δ : Ctx Head m)
    (σ : Sub Head n m) :=
  (index : Fin n) → Tree R (judgment Δ (σ index) (subst σ (Ctx.lookup Γ index)))

namespace TreeSubstitution

/-- Identity substitution supplies the actual variable derivation at every
position, without choosing a typing witness. -/
noncomputable def identity {n : Nat} (Γ : Ctx Head n) :
    TreeSubstitution (R := R) Γ Γ ids := by
  intro index
  simpa only [subst_ids, ids] using Tree.variableLeaf (R := R) Γ index

theorem identity_component {n : Nat} (Γ : Ctx Head n) (index : Fin n) :
    HEq (identity (R := R) Γ index) (Tree.variableLeaf (R := R) Γ index) := by
  simp only [identity, Eq.mpr, eqRec_heq_iff]
  rfl

/-- The newest component is a variable; older components are the supplied
trees weakened into the extended target context. -/
noncomputable def lift {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) (A : Tm Head n) :
    TreeSubstitution (R := R) (.snoc Γ A) (.snoc Δ (subst σ A)) (liftSub σ) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · simpa only [liftSub_zero, Ctx.lookup_snoc_zero, subst_liftSub_wk] using
      (Derivation.node (S := signature R) (Rule.var (R := R) (Γ := .snoc Δ (subst σ A)) (0 : Fin (m + 1)))
        (fun position => Fin.elim0 position))
  · simpa only [liftSub_succ, Ctx.lookup_snoc_succ, subst_liftSub_wk] using
      (Tree.weaken (extension := subst σ A) (components prior))

set_option backward.isDefEq.respectTransparency false in
/-- Identity component trees lift to identity component trees under a binder. -/
theorem lift_identity {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) :
    HEq ((identity (R := R) Γ).lift A) (identity (R := R) (.snoc Γ A)) := by
  apply Function.hfunext rfl
  intro index other equal
  cases equal
  refine Fin.cases ?_ (fun prior => ?_) index
  · simp only [lift, identity, Eq.mpr, eqRec_heq_iff, Fin.cases_zero]
    simp only [judgment, Ctx.lookup, Tree.variableLeaf, heq_eqRec_iff]
    congr 1
    simp only [subst_ids]
    congr 1
    simp only [subst_ids]
  · simp only [lift, Fin.cases_succ, Eq.mpr, eqRec_heq_iff]
    refine HEq.trans ?_ (identity_component (.snoc Γ A) prior.succ).symm
    unfold Tree.weaken
    refine HEq.trans (Tree.rename_heq ?_ (identity_component Γ prior)
      (fun _ => rfl) (fun _ => rfl) rfl (HEq.refl _)) ?_
    · simp only [judgment, ids, subst_ids]
    · refine HEq.trans (Tree.rename_variableLeaf (fun _ => rfl) prior) ?_
      congr 1
      simp only [subst_ids]

end TreeSubstitution

namespace Tree

set_option backward.isDefEq.respectTransparency false in
/-- The local substitution action receives the supplied original children and
their recursively substituted versions. -/
noncomputable def substitutionStep {j : Judgment Head} (rule : Rule R j)
    (premises : (position : Fin (premiseCount rule)) → Tree R (hypothesis rule position))
    (ih : (position : Fin (premiseCount rule)) →
      ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head (hypothesis rule position).arity m},
        TreeSubstitution (R := R) (hypothesis rule position).context Δ σ →
          Tree R (judgment Δ (subst σ (hypothesis rule position).subject)
            (subst σ (hypothesis rule position).type))) :
    ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head j.arity m},
      TreeSubstitution (R := R) j.context Δ σ →
        Tree R (judgment Δ (subst σ j.subject) (subst σ j.type)) := by
  intro m Δ σ components
  cases rule with
  | headType typed => exact Derivation.node (S := signature R) (.headType typed) (fun position => Fin.elim0 position)
  | var index => exact components index
  | const known universeWitness =>
      dsimp only [judgment]
      simpa only [judgment, subst, subst_liftClosed] using
        (Derivation.node (S := signature R) (Rule.const (Γ := Δ) known universeWitness) (fun _ => premises 0))
  | piForm universeA universeB joined =>
      exact Derivation.node (S := signature R) (.piForm universeA universeB joined)
        (Fin.cases (ih 0 components) (fun _ => ih 1 (components.lift _)))
  | sigmaForm universeA universeB joined =>
      exact Derivation.node (S := signature R) (.sigmaForm universeA universeB joined)
        (Fin.cases (ih 0 components) (fun _ => ih 1 (components.lift _)))
  | lamIntro universeWitness =>
      exact Derivation.node (S := signature R) (.lamIntro universeWitness)
        (Fin.cases (ih 0 components) (fun _ => ih 1 (components.lift _)))
  | @appElim n Γ g a A B =>
      dsimp only [judgment]
      simpa only [judgment, subst, subst_inst0] using
        (Derivation.node (S := signature R) (Rule.appElim (Γ := Δ)
          (g := subst σ g) (a := subst σ a) (A := subst σ A) (B := subst (liftSub σ) B))
          (Fin.cases (ih 0 components) (fun _ => ih 1 components)))
  | @pairIntro n Γ a b A B u universeWitness =>
      have second := ih 2 components
      change Tree R (judgment Δ (subst σ b) (subst σ (inst0 a B))) at second
      rw [subst_inst0] at second
      exact Derivation.node (S := signature R) (.pairIntro universeWitness)
        (Fin.cases (ih 0 components) (Fin.cases (ih 1 components) (fun _ => second)))
  | @fstElim n Γ p A B =>
      exact Derivation.node (S := signature R)
        (Rule.fstElim (B := subst (liftSub σ) B)) (fun _ => ih 0 components)
  | @sndElim n Γ p A B =>
      dsimp only [judgment]
      simpa only [judgment, subst, subst_inst0] using
        (Derivation.node (S := signature R) (Rule.sndElim (Γ := Δ)
          (p := subst σ p) (A := subst σ A) (B := subst (liftSub σ) B))
            (fun _ => ih 0 components))
  | idForm universeWitness =>
      exact Derivation.node (S := signature R) (.idForm universeWitness)
        (Fin.cases (ih 0 components)
          (Fin.cases (ih 1 components) (fun _ => ih 2 components)))
  | reflIntro => exact Derivation.node (S := signature R) .reflIntro (fun _ => ih 0 components)
  | cumul order => exact Derivation.node (S := signature R) (.cumul order) (fun _ => ih 0 components)
  | convert universeWitness conversion =>
      exact Derivation.node (S := signature R) (.convert universeWitness (conversion.substitute σ))
        (Fin.cases (ih 0 components) (fun _ => ih 1 components))

/-- Substitution recursively uses the supplied component trees at variable
leaves and retains every non-variable rule and its premise positions. -/
noncomputable def substitute {j : Judgment Head} (tree : Tree R j)
    {m : Nat} {Δ : Ctx Head m} {σ : Sub Head j.arity m}
    (components : TreeSubstitution (R := R) j.context Δ σ) :
    Tree R (judgment Δ (subst σ j.subject) (subst σ j.type)) :=
  Derivation.rec (S := signature R)
    (motive := fun (j : Judgment Head) _ => ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head j.arity m},
      TreeSubstitution (R := R) j.context Δ σ →
        Tree R (judgment Δ (subst σ j.subject) (subst σ j.type)))
    (fun rule premises ih => substitutionStep rule premises ih) tree components

@[simp] theorem substitute_node {j : Judgment Head} (rule : Rule R j)
    (premises : (position : Fin (premiseCount rule)) → Tree R (hypothesis rule position))
    {m : Nat} {Δ : Ctx Head m} {σ : Sub Head j.arity m}
    (components : TreeSubstitution (R := R) j.context Δ σ) :
    Tree.substitute (.node rule premises) components =
      substitutionStep rule premises
        (fun position => @Tree.substitute Head R _ (premises position)) components := rfl

/-- Each variable leaf is replaced by the exact supplied component tree. -/
theorem substitute_variableLeaf {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {σ : Sub Head n m} (components : TreeSubstitution (R := R) Γ Δ σ) (index : Fin n) :
    (variableLeaf (R := R) Γ index).substitute components = components index := rfl

/-- Equal supplied component families give the same retained substitution. -/
theorem substitute_congr {j : Judgment Head} (tree : Tree R j)
    {m : Nat} {Δ Θ : Ctx Head m} {σ τ : Sub Head j.arity m}
    (first : TreeSubstitution (R := R) j.context Δ σ)
    (second : TreeSubstitution (R := R) j.context Θ τ)
    (contexts : Δ = Θ) (substitutions : σ = τ) (components : HEq first second) :
    HEq (tree.substitute first) (tree.substitute second) := by
  cases contexts
  cases substitutions
  have same : first = second := eq_of_heq components
  cases same
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Identity substitution preserves the exact supplied rule tree. -/
theorem substitute_identity {j : Judgment Head} (tree : Tree R j) :
    HEq (tree.substitute (TreeSubstitution.identity j.context)) tree := by
  refine Derivation.rec (S := signature R)
    (motive := fun j tree => HEq (Tree.substitute tree (TreeSubstitution.identity j.context)) tree) ?_ tree
  intro j rule premises ih
  rw [substitute_node]
  cases rule
  case var index =>
    simp only [substitutionStep]
    refine HEq.trans (TreeSubstitution.identity_component _ index) ?_
    simp only [variableLeaf]
    congr 1
    funext position
    exact Fin.elim0 position
  all_goals simp only [substitutionStep, id_eq, Eq.mp, Eq.mpr, eqRec_heq_iff]
  all_goals congr 1
  all_goals try simp only [judgment, subst_ids, liftSub_ids]
  all_goals try congr 1
  all_goals try simp only [subst_ids, liftSub_ids]
  all_goals try exact proof_irrel_heq _ _
  all_goals first
    | (funext position; exact Fin.elim0 position)
    | (funext position; have same : position = 0 := Subsingleton.elim _ _; cases same; rfl)
    | (apply Function.hfunext rfl; intro position other equal; cases equal)
  all_goals fin_cases position
  all_goals first
    | simpa [premiseCount, hypothesis, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat, judgment,
        Eq.mp, Eq.mpr, eqRec_heq_iff] using ih ⟨0, by dsimp only [premiseCount]; decide⟩
    | simpa [premiseCount, hypothesis, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat, judgment,
        Eq.mp, Eq.mpr, eqRec_heq_iff] using ih ⟨1, by dsimp only [premiseCount]; decide⟩
    | simpa [premiseCount, hypothesis, Fin.cases, Fin.induction, Fin.induction.go, Fin.ofNat, judgment,
        Eq.mp, Eq.mpr, eqRec_heq_iff] using ih ⟨2, by dsimp only [premiseCount]; decide⟩
    | skip
  all_goals
    simp only [Fin.cases, Fin.induction, Fin.induction.go]
    refine HEq.trans ?_ (ih ⟨1, by dsimp only [premiseCount]; decide⟩)
    apply Tree.substitute_congr
    · simp only [hypothesis, Fin.cases, Fin.induction, Fin.induction.go, judgment, subst_ids]
    · exact liftSub_ids
    · exact TreeSubstitution.lift_identity _ _

/-- Transporting a raw judgment and its supplied tree commutes with the
component-tree action. -/
theorem substitute_heq {j k : Judgment Head} (judgments : j = k)
    {firstTree : Tree R j} {secondTree : Tree R k} (trees : HEq firstTree secondTree)
    {m : Nat} {Δ Θ : Ctx Head m} {σ : Sub Head j.arity m} {τ : Sub Head k.arity m}
    (first : TreeSubstitution (R := R) j.context Δ σ)
    (second : TreeSubstitution (R := R) k.context Θ τ)
    (contexts : Δ = Θ) (substitutions : HEq σ τ) (components : HEq first second) :
    HEq (firstTree.substitute first) (secondTree.substitute second) := by
  cases judgments
  cases contexts
  have maps : σ = τ := eq_of_heq substitutions
  cases maps
  have sameTrees : firstTree = secondTree := eq_of_heq trees
  cases sameTrees
  have sameComponents : first = second := eq_of_heq components
  cases sameComponents
  rfl

theorem substitute_cast_type_heq {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term A B : Tm Head n} (types : A = B)
    (transport : Tree R (judgment Γ term A) = Tree R (judgment Γ term B))
    (tree : Tree R (judgment Γ term B)) {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) {α : Sort _} (other : α) :
    HEq (Tree.substitute (transport.mpr tree) components) other ↔
      HEq (tree.substitute components) other := by
  cases types
  rfl

theorem substitute_cast_type_mp_heq {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term A B : Tm Head n} (types : A = B)
    (transport : Tree R (judgment Γ term A) = Tree R (judgment Γ term B))
    (tree : Tree R (judgment Γ term A)) {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) {α : Sort _} (other : α) :
    HEq (Tree.substitute (transport.mp tree) components) other ↔
      HEq (tree.substitute components) other := by
  cases types
  rfl

theorem substitute_cast_type_rec_heq {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {term A B : Tm Head n} (types : A = B)
    (transport : Tree R (judgment Γ term A) = Tree R (judgment Γ term B))
    (tree : Tree R (judgment Γ term A)) {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) {α : Sort _} (other : α) :
    HEq (Tree.substitute (transport ▸ tree) components) other ↔
      HEq (tree.substitute components) other := by
  cases types
  rfl

end Tree

namespace TreeSubstitution

/-- Renaming every supplied component tree acts on the target telescope. -/
noncomputable def postcompose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ : Sub Head n m} {ρ : Ren m k} (components : TreeSubstitution (R := R) Γ Δ σ)
    (compatible : CtxRen Δ Θ ρ) :
    TreeSubstitution (R := R) Γ Θ (fun index => Presentation.rename ρ (σ index)) := by
  intro index
  simpa only [judgment, rename_subst] using (components index).rename compatible

/-- The retained target-renamed component is exactly the supplied tree action. -/
theorem postcompose_component {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ : Sub Head n m} {ρ : Ren m k} (components : TreeSubstitution (R := R) Γ Δ σ)
    (compatible : CtxRen Δ Θ ρ) (index : Fin n) :
    HEq (components.postcompose compatible index) ((components index).rename compatible) := by
  simp only [postcompose, id_eq, Eq.mp, eqRec_heq_iff]
  rfl

theorem lift_zero {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) (A : Tm Head n) :
    HEq (components.lift A 0)
      (Tree.variableLeaf (R := R) (.snoc Δ (subst σ A)) (0 : Fin (m + 1))) := by
  simp only [lift, Fin.cases_zero, Eq.mpr]
  simp only [Tree.variableLeaf, Ctx.lookup]
  exact eqRec_heq (φ := fun (X : Type) => X) _ _

theorem lift_succ {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) (A : Tm Head n) (index : Fin n) :
    HEq (components.lift A index.succ)
      (Tree.weaken (extension := subst σ A) (components index)) := by
  simp only [lift, Fin.cases_succ, Eq.mpr, eqRec_heq_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Lifting and target renaming commute on the actual component trees. -/
theorem lift_postcompose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ : Sub Head n m} {ρ : Ren m k} (components : TreeSubstitution (R := R) Γ Δ σ)
    (compatible : CtxRen Δ Θ ρ) (A : Tm Head n) :
    HEq ((components.lift A).postcompose (compatible.snoc (subst σ A)))
      ((components.postcompose compatible).lift A) := by
  apply Function.hfunext rfl
  intro index other same
  cases same
  refine Fin.cases ?_ (fun prior => ?_) index
  · refine HEq.trans (postcompose_component (components.lift A)
      (compatible.snoc (subst σ A)) 0) ?_
    refine HEq.trans (Tree.rename_heq ?_ (lift_zero components A)
      (compatible.snoc (subst σ A)) (compatible.snoc (subst σ A)) rfl (HEq.refl _)) ?_
    · simp only [judgment, liftSub_zero, Ctx.lookup_snoc_zero, subst_liftSub_wk]
    · refine HEq.trans (Tree.rename_variableLeaf (compatible.snoc (subst σ A)) 0) ?_
      refine HEq.trans ?_ (lift_zero (components.postcompose compatible) A).symm
      congr 1
      simp only [rename_subst]
  · refine HEq.trans (postcompose_component (components.lift A)
      (compatible.snoc (subst σ A)) prior.succ) ?_
    refine HEq.trans (Tree.rename_heq ?_ (lift_succ components A prior)
      (compatible.snoc (subst σ A)) (compatible.snoc (subst σ A)) rfl (HEq.refl _)) ?_
    · simp only [judgment, liftSub_succ, Ctx.lookup_snoc_succ, subst_liftSub_wk]
    · refine HEq.trans ?_ (lift_succ (components.postcompose compatible) A prior).symm
      unfold Tree.weaken
      refine HEq.trans (Tree.rename_composition (components prior)
        (fun _ => rfl) (compatible.snoc (subst σ A))) ?_
      refine HEq.trans ?_ (Tree.rename_heq ?_ (postcompose_component components compatible prior).symm
        (fun _ => rfl) (fun _ => rfl) rfl (HEq.refl _))
      · refine HEq.trans ?_ (Tree.rename_composition (components prior) compatible
          (fun _ => rfl)).symm
        apply Tree.rename_congr
        · simp only [rename_subst]
        · funext position
          rfl
      · simp only [judgment, rename_subst]

end TreeSubstitution

namespace Tree

set_option backward.isDefEq.respectTransparency false in
/-- Target renaming commutes with substitution by the supplied component
trees, including the lifted trees at binding rules. -/
theorem rename_substitute {j : Judgment Head} (tree : Tree R j)
    {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k} {σ : Sub Head j.arity m} {ρ : Ren m k}
    (components : TreeSubstitution (R := R) j.context Δ σ) (compatible : CtxRen Δ Θ ρ) :
    HEq ((tree.substitute components).rename compatible)
      (tree.substitute (components.postcompose compatible)) := by
  refine Derivation.rec (S := signature R)
    (motive := fun j tree => ∀ {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k}
      {σ : Sub Head j.arity m} {ρ : Ren m k},
        (components : TreeSubstitution (R := R) j.context Δ σ) → (compatible : CtxRen Δ Θ ρ) →
          HEq (Tree.rename (Tree.substitute tree components) compatible)
            (Tree.substitute tree (components.postcompose compatible))) ?_ tree components compatible
  intro j rule premises ih m k Δ Θ σ ρ components compatible
  cases rule <;> simp only [substitute_node, substitutionStep, rename_node, renamingStep, id_eq]
  case var index => exact (TreeSubstitution.postcompose_component components compatible index).symm
  all_goals first
    | rfl
    | (dsimp only [judgment, subst] at σ components ⊢
       rw [rename_cast_type_heq (by simp only [subst_inst0, subst_liftClosed, subst])]
       simp only [rename_node, renamingStep, id_eq, Eq.mpr, eqRec_heq_iff])
    | skip
  all_goals try simp only [Eq.mp, heq_eqRec_iff]
  all_goals congr 1
  all_goals try simp only [judgment, Presentation.rename_subst]
  all_goals try congr 1
  all_goals try simp only [Presentation.rename_subst]
  all_goals try exact proof_irrel_heq _ _
  all_goals try simp only [Presentation.rename, subst, Presentation.rename_subst, rename_liftSub]
  all_goals apply Function.hfunext rfl
  all_goals intro position other equal
  all_goals cases equal
  all_goals try fin_cases position
  all_goals try simp [premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
    Eq.mpr, eqRec_heq_iff, heq_eqRec_iff]
  case pairIntro.e_4.refl.«2» =>
    rw [rename_cast_type_rec_heq (subst_inst0 _ _ _)]
    have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
    dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
      judgment] at child
    exact child components compatible
  all_goals first
    | (have child := @ih ⟨0, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child components compatible)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child components compatible)
    | (have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child components compatible)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       refine HEq.trans (child (components.lift _) (compatible.snoc _)) ?_
       apply substitute_congr
       · simp only [Presentation.rename_subst]
       · funext index; exact rename_liftSub _ _ index
       · exact TreeSubstitution.lift_postcompose components compatible _)

end Tree

namespace TreeSubstitution

/-- Selecting components along a typed context renaming preserves the exact
supplied component tree at each selected occurrence. -/
noncomputable def precompose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {ρ : Ren n m} {σ : Sub Head m k} (components : TreeSubstitution (R := R) Δ Θ σ)
    (compatible : CtxRen Γ Δ ρ) :
    TreeSubstitution (R := R) Γ Θ (fun index => σ (ρ index)) := by
  intro index
  simpa only [judgment, compatible index, subst_rename] using components (ρ index)

theorem precompose_component {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {ρ : Ren n m} {σ : Sub Head m k} (components : TreeSubstitution (R := R) Δ Θ σ)
    (compatible : CtxRen Γ Δ ρ) (index : Fin n) :
    HEq (components.precompose compatible index) (components (ρ index)) := by
  simp only [precompose, id_eq, Eq.mp, eqRec_heq_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Selecting components along a renaming commutes with binder lifting. -/
theorem lift_precompose {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {ρ : Ren n m} {σ : Sub Head m k} (components : TreeSubstitution (R := R) Δ Θ σ)
    (compatible : CtxRen Γ Δ ρ) (A : Tm Head n) :
    HEq ((components.lift (Presentation.rename ρ A)).precompose (compatible.snoc A))
      ((components.precompose compatible).lift A) := by
  apply Function.hfunext rfl
  intro index other same
  cases same
  refine Fin.cases ?_ (fun prior => ?_) index
  · refine HEq.trans (precompose_component (components.lift (Presentation.rename ρ A))
      (compatible.snoc A) 0) ?_
    refine HEq.trans (lift_zero components (Presentation.rename ρ A)) ?_
    refine HEq.trans ?_ (lift_zero (components.precompose compatible) A).symm
    congr 1
    simp only [subst_rename]
  · refine HEq.trans (precompose_component (components.lift (Presentation.rename ρ A))
      (compatible.snoc A) prior.succ) ?_
    refine HEq.trans (lift_succ components (Presentation.rename ρ A) (ρ prior)) ?_
    refine HEq.trans ?_ (lift_succ (components.precompose compatible) A prior).symm
    unfold Tree.weaken
    refine Tree.rename_heq ?_ (precompose_component components compatible prior).symm
      (fun _ => rfl) (fun _ => rfl) ?_ (HEq.refl _)
    · simp only [judgment, compatible prior, subst_rename]
    · simp only [subst_rename]

end TreeSubstitution

namespace Tree

set_option backward.isDefEq.respectTransparency false in
/-- Renaming the input telescope selects the supplied target component trees;
substituting those trees gives the same retained derivation. -/
theorem substitute_rename {j : Judgment Head} (tree : Tree R j)
    {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k} {ρ : Ren j.arity m} {σ : Sub Head m k}
    (compatible : CtxRen j.context Δ ρ) (components : TreeSubstitution (R := R) Δ Θ σ) :
    HEq ((tree.rename compatible).substitute components)
      (tree.substitute (components.precompose compatible)) := by
  refine Derivation.rec (S := signature R)
    (motive := fun j tree => ∀ {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k}
      {ρ : Ren j.arity m} {σ : Sub Head m k},
        (compatible : CtxRen j.context Δ ρ) → (components : TreeSubstitution (R := R) Δ Θ σ) →
          HEq (Tree.substitute (Tree.rename tree compatible) components)
            (Tree.substitute tree (components.precompose compatible))) ?_ tree compatible components
  intro j rule premises ih m k Δ Θ ρ σ compatible components
  cases rule <;> simp only [rename_node, renamingStep, substitute_node, substitutionStep, id_eq]
  case var index =>
    dsimp only [judgment, Presentation.rename] at ρ compatible ⊢
    rw [substitute_cast_type_mp_heq (compatible index)]
    simp only [substitute_node, substitutionStep]
    exact (TreeSubstitution.precompose_component components compatible index).symm
  all_goals first
    | rfl
    | (dsimp only [judgment, Presentation.rename] at ρ compatible ⊢
       rw [substitute_cast_type_heq (by simp only [rename_inst0, rename_liftClosed, Presentation.rename])]
       simp only [substitute_node, substitutionStep, id_eq, Eq.mpr, eqRec_heq_iff])
    | skip
  all_goals try simp only [Eq.mp, heq_eqRec_iff]
  all_goals congr 1
  all_goals try simp only [judgment, subst_rename]
  all_goals try congr 1
  all_goals try simp only [subst_rename]
  all_goals try exact proof_irrel_heq _ _
  all_goals try simp only [Presentation.rename, subst, subst_rename, liftSub_liftRen_apply]
  all_goals apply Function.hfunext rfl
  all_goals intro position other equal
  all_goals cases equal
  all_goals try fin_cases position
  all_goals try simp [premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
    Eq.mpr, eqRec_heq_iff, heq_eqRec_iff]
  case pairIntro.e_4.refl.«2» =>
    rw [substitute_cast_type_rec_heq (rename_inst0 _ _ _)]
    have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
    dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
      judgment] at child
    exact child compatible components
  all_goals first
    | (have child := @ih ⟨0, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child compatible components)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child compatible components)
    | (have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child compatible components)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       refine HEq.trans (child (compatible.snoc _) (components.lift _)) ?_
       apply substitute_congr
       · simp only [subst_rename]
       · funext index; exact liftSub_liftRen_apply _ _ index
       · exact TreeSubstitution.lift_precompose components compatible _)

end Tree

namespace TreeSubstitution

set_option backward.isDefEq.respectTransparency false in
/-- Weakening selects precisely the weakened original component trees from
the lifted family. -/
theorem precompose_lift_wk {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) (A : Tm Head n) :
    HEq ((components.lift A).precompose (ρ := wk) (fun _ => rfl))
      (components.postcompose (ρ := wk) (Δ := Δ) (Θ := .snoc Δ (subst σ A)) (fun _ => rfl)) := by
  apply Function.hfunext rfl
  intro index other same
  cases same
  refine HEq.trans (precompose_component (components.lift A) (ρ := wk) (fun _ => rfl) index) ?_
  refine HEq.trans (lift_succ components A index) ?_
  exact (postcompose_component components (ρ := wk) (Θ := .snoc Δ (subst σ A))
    (fun _ => rfl) index).symm

end TreeSubstitution

namespace Tree

set_option backward.isDefEq.respectTransparency false in
/-- Weakening and substitution commute on the actual retained tree. -/
theorem substitute_weaken {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {term type A : Tm Head n}
    {σ : Sub Head n m} (tree : Tree R (judgment Γ term type))
    (components : TreeSubstitution (R := R) Γ Δ σ) :
    HEq ((tree.weaken (extension := A)).substitute (components.lift A))
      ((tree.substitute components).weaken (extension := subst σ A)) := by
  unfold Tree.weaken
  refine HEq.trans (substitute_rename tree (ρ := wk) (Δ := .snoc Γ A)
    (fun _ => rfl) (components.lift A)) ?_
  refine HEq.trans ?_ (rename_substitute tree components (ρ := wk)
    (Θ := .snoc Δ (subst σ A)) (fun _ => rfl)).symm
  apply substitute_congr
  · rfl
  · rfl
  · exact TreeSubstitution.precompose_lift_wk components A

end Tree

namespace TreeSubstitution

/-- Composition substitutes the supplied second component trees into each
supplied first component tree. -/
noncomputable def comp {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ : Sub Head n m} {τ : Sub Head m k} (first : TreeSubstitution (R := R) Γ Δ σ)
    (second : TreeSubstitution (R := R) Δ Θ τ) :
    TreeSubstitution (R := R) Γ Θ (fun index => subst τ (σ index)) := by
  intro index
  simpa only [judgment, subst_comp] using (first index).substitute second

theorem comp_component {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ : Sub Head n m} {τ : Sub Head m k} (first : TreeSubstitution (R := R) Γ Δ σ)
    (second : TreeSubstitution (R := R) Δ Θ τ) (index : Fin n) :
    HEq (first.comp second index) ((first index).substitute second) := by
  simp only [comp, id_eq, Eq.mp, eqRec_heq_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Lifted component composition agrees with lifting the composed actual
component trees. -/
theorem lift_comp {n m k : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {Θ : Ctx Head k}
    {σ : Sub Head n m} {τ : Sub Head m k} (first : TreeSubstitution (R := R) Γ Δ σ)
    (second : TreeSubstitution (R := R) Δ Θ τ) (A : Tm Head n) :
    HEq ((first.lift A).comp (second.lift (subst σ A))) ((first.comp second).lift A) := by
  apply Function.hfunext rfl
  intro index other same
  cases same
  refine Fin.cases ?_ (fun prior => ?_) index
  · refine HEq.trans (comp_component (first.lift A) (second.lift (subst σ A)) 0) ?_
    refine HEq.trans (Tree.substitute_heq ?_ (lift_zero first A)
      (second.lift (subst σ A)) (second.lift (subst σ A)) rfl (HEq.refl _) (HEq.refl _)) ?_
    · simp only [judgment, liftSub_zero, Ctx.lookup_snoc_zero, subst_liftSub_wk]
    · rw [Tree.substitute_variableLeaf]
      refine HEq.trans (lift_zero second (subst σ A)) ?_
      refine HEq.trans ?_ (lift_zero (first.comp second) A).symm
      congr 1
      simp only [subst_comp]
  · refine HEq.trans (comp_component (first.lift A) (second.lift (subst σ A)) prior.succ) ?_
    refine HEq.trans (Tree.substitute_heq ?_ (lift_succ first A prior)
      (second.lift (subst σ A)) (second.lift (subst σ A)) rfl (HEq.refl _) (HEq.refl _)) ?_
    · simp only [judgment, liftSub_succ, Ctx.lookup_snoc_succ, subst_liftSub_wk]
    · refine HEq.trans (Tree.substitute_weaken (first prior) second) ?_
      refine HEq.trans ?_ (lift_succ (first.comp second) A prior).symm
      unfold Tree.weaken
      refine Tree.rename_heq ?_ (comp_component first second prior).symm
        (fun _ => rfl) (fun _ => rfl) ?_ (HEq.refl _)
      · simp only [judgment, subst_comp]
      · simp only [subst_comp]

end TreeSubstitution

namespace Tree

set_option backward.isDefEq.respectTransparency false in
/-- Successive substitution by retained component families equals
substitution by their actual composed trees, including all binding rules. -/
theorem substitute_composition {j : Judgment Head} (tree : Tree R j)
    {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k} {σ : Sub Head j.arity m} {τ : Sub Head m k}
    (first : TreeSubstitution (R := R) j.context Δ σ) (second : TreeSubstitution (R := R) Δ Θ τ) :
    HEq ((tree.substitute first).substitute second)
      (tree.substitute (first.comp second)) := by
  refine Derivation.rec (S := signature R)
    (motive := fun j tree => ∀ {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k}
      {σ : Sub Head j.arity m} {τ : Sub Head m k},
        (first : TreeSubstitution (R := R) j.context Δ σ) → (second : TreeSubstitution (R := R) Δ Θ τ) →
          HEq (Tree.substitute (Tree.substitute tree first) second)
            (Tree.substitute tree (first.comp second))) ?_ tree first second
  intro j rule premises ih m k Δ Θ σ τ first second
  cases rule <;> simp only [substitute_node, substitutionStep, id_eq]
  case var index => exact (TreeSubstitution.comp_component first second index).symm
  all_goals first
    | rfl
    | (dsimp only [judgment, subst] at σ first ⊢
       rw [substitute_cast_type_heq (by simp only [subst_inst0, subst_liftClosed, subst])]
       simp only [substitute_node, substitutionStep, id_eq, Eq.mpr, eqRec_heq_iff])
    | skip
  all_goals try simp only [Eq.mp, heq_eqRec_iff]
  all_goals congr 1
  all_goals try simp only [judgment, subst_comp]
  all_goals try congr 1
  all_goals try simp only [subst_comp]
  all_goals try exact proof_irrel_heq _ _
  all_goals try simp only [subst, subst_comp, liftSub_comp_apply]
  all_goals apply Function.hfunext rfl
  all_goals intro position other equal
  all_goals cases equal
  all_goals try fin_cases position
  all_goals try simp [premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
    Eq.mpr, eqRec_heq_iff, heq_eqRec_iff]
  case pairIntro.e_4.refl.«2» =>
    rw [substitute_cast_type_rec_heq (subst_inst0 _ _ _)]
    have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
    dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
      judgment] at child
    exact child first second
  all_goals first
    | (have child := @ih ⟨0, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child first second)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child first second)
    | (have child := @ih ⟨2, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       exact child first second)
    | (have child := @ih ⟨1, by dsimp only [premiseCount]; decide⟩
       dsimp only [signature, hypothesis, premiseCount, Fin.cases, Fin.induction, Fin.induction.go,
         judgment] at child
       refine HEq.trans (child (first.lift _) (second.lift _)) ?_
       apply substitute_congr
       · simp only [subst_comp]
       · funext index; exact liftSub_comp_apply _ _ index
       · exact TreeSubstitution.lift_comp first second _)

end Tree

namespace TreeSubstitution

/-- Composing with identity component trees on the target preserves every
supplied original component tree. -/
theorem comp_identity_right {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) :
    HEq (components.comp (identity Δ)) components := by
  apply Function.hfunext rfl
  intro index other same
  cases same
  exact (comp_component components (identity Δ) index).trans
    (Tree.substitute_identity (components index))

set_option backward.isDefEq.respectTransparency false in
/-- Composing actual identity variable trees with a supplied family returns
that family, including its evidence occurrences. -/
theorem comp_identity_left {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (components : TreeSubstitution (R := R) Γ Δ σ) :
    HEq ((identity Γ).comp components) components := by
  apply Function.hfunext rfl
  intro index other same
  cases same
  refine HEq.trans (comp_component (identity Γ) components index) ?_
  refine HEq.trans (Tree.substitute_heq ?_ (identity_component Γ index)
    components components rfl (HEq.refl _) (HEq.refl _)) ?_
  · simp only [judgment, ids, subst_ids]
  · exact heq_of_eq (Tree.substitute_variableLeaf components index)

set_option backward.isDefEq.respectTransparency false in
/-- Actual component-tree composition is associative, rather than merely
associative after erasing evidence to a typing proposition. -/
theorem comp_associativity {n m k l : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {Θ : Ctx Head k} {Ξ : Ctx Head l} {σ : Sub Head n m} {τ : Sub Head m k} {υ : Sub Head k l}
    (first : TreeSubstitution (R := R) Γ Δ σ) (second : TreeSubstitution (R := R) Δ Θ τ)
    (third : TreeSubstitution (R := R) Θ Ξ υ) :
    HEq ((first.comp second).comp third) (first.comp (second.comp third)) := by
  apply Function.hfunext rfl
  intro index other same
  cases same
  refine HEq.trans (comp_component (first.comp second) third index) ?_
  refine HEq.trans (Tree.substitute_heq ?_ (comp_component first second index)
    third third rfl (HEq.refl _) (HEq.refl _)) ?_
  · simp only [judgment, subst_comp]
  · exact (Tree.substitute_composition (first index) second third).trans
      (comp_component first (second.comp third) index).symm

end TreeSubstitution

end FormationSensitiveRuleSignature
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
