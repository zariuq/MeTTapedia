import Mettapedia.Languages.MeTTa.PeTTa.LibTransformExecutable

/-!
# Made occurrences: labels resolved by knowledge

A firing that makes atoms makes occurrences whose labels, in the step, are the rule's
produce terms as written, with the firing's own variables. What the store holds is their
value under the knowledge the firing told. This module has the lemmas that connect the two:

* `BoundGround τ t`: the substitution `τ` gives every variable of `t` a ground value.
  `boundGround_of_ground_subst`: an atom whose instance is ground has all its variables
  so bound; `ground_subst_of_boundGround`: and then its instance is ground.
* `subst_eq_of_agrees`: a solution that agrees with a list of bindings substitutes as the
  bindings do, on an atom whose variables the bindings give ground values.
* `subst_rename_of_untagged`: if the untagged solution makes an atom equal to a ground
  atom, the solution makes the renamed atom equal to it (the converse of
  `subst_untagged_of_rename`).
* `Closed pats template`: every variable of the template occurs in a kernel pattern, so a
  kernel row gives every instance of the template a ground value
  (`instances_ground_of_closed`).
* `exists_made`: fresh, distinct occurrences with given labels, from a supply of fresh
  occurrences for every label.

Negative example: `Controls.open_template_instance_not_ground` (a template variable that
no kernel pattern binds stays in the instance).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.MeTTa (SubstitutionAlgebra.subst SubstitutionAlgebra.vars)
open LibTransform

variable {O : Type} [DecidableEq O]

/-! ## Variables with ground values -/

/-- The substitution gives every variable of the atom a ground value. -/
def BoundGround (τ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (t : Atom) : Prop :=
  ∀ v ∈ SubstitutionAlgebra.vars t, ∃ a, τ v = some a ∧ isGroundAtom a = true

/-- An atom whose instance is ground has every variable given a ground value. -/
theorem boundGround_of_ground_subst (τ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) :
    ∀ t : Atom, isGroundAtom (SubstitutionAlgebra.subst τ t) = true → BoundGround τ t
  | .var x, ground => by
      intro v member
      simp only [SubstitutionAlgebra.vars, List.mem_singleton] at member
      subst member
      simp only [SubstitutionAlgebra.subst] at ground
      cases bound : τ v with
      | none =>
          rw [bound] at ground
          simp [isGroundAtom] at ground
      | some a =>
          rw [bound] at ground
          exact ⟨a, rfl, by simpa using ground⟩
  | .symbol _, _ => by
      intro v member
      simp [SubstitutionAlgebra.vars] at member
  | .grounded _, _ => by
      intro v member
      simp [SubstitutionAlgebra.vars] at member
  | .expression es, ground => by
      simp only [SubstitutionAlgebra.subst, isGroundAtom] at ground
      intro v member
      simp only [SubstitutionAlgebra.vars] at member
      exact list es ground v member
where
  list : ∀ es : List Atom,
      isGroundAtom.isGroundList (SubstitutionAlgebra.subst.substList τ es) = true →
      ∀ v ∈ SubstitutionAlgebra.vars.varsList es, ∃ a, τ v = some a ∧ isGroundAtom a = true
    | [], _ => by
        intro v member
        simp [SubstitutionAlgebra.vars.varsList] at member
    | e :: es, ground => by
        simp only [SubstitutionAlgebra.subst.substList, isGroundAtom.isGroundList,
          Bool.and_eq_true] at ground
        intro v member
        simp only [SubstitutionAlgebra.vars.varsList, List.mem_append] at member
        rcases member with here | later
        · exact boundGround_of_ground_subst τ e ground.1 v here
        · exact list es ground.2 v later

/-- An atom all of whose variables have ground values has a ground instance. -/
theorem ground_subst_of_boundGround
    (τ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) :
    ∀ t : Atom, BoundGround τ t → isGroundAtom (SubstitutionAlgebra.subst τ t) = true
  | .var x, bound => by
      obtain ⟨a, isBound, ground⟩ := bound x (by simp [SubstitutionAlgebra.vars])
      simp only [SubstitutionAlgebra.subst, isBound, Option.getD_some]
      exact ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression es, bound => by
      simp only [SubstitutionAlgebra.subst, isGroundAtom]
      exact list es fun v member => bound v (by simpa [SubstitutionAlgebra.vars] using member)
where
  list : ∀ es : List Atom,
      (∀ v ∈ SubstitutionAlgebra.vars.varsList es, ∃ a, τ v = some a ∧ isGroundAtom a = true) →
      isGroundAtom.isGroundList (SubstitutionAlgebra.subst.substList τ es) = true
    | [], _ => rfl
    | e :: es, bound => by
        simp only [SubstitutionAlgebra.subst.substList, isGroundAtom.isGroundList,
          Bool.and_eq_true]
        refine ⟨ground_subst_of_boundGround τ e fun v member => bound v ?_,
          list es fun v member => bound v ?_⟩
        · simp only [SubstitutionAlgebra.vars.varsList, List.mem_append]
          exact Or.inl member
        · simp only [SubstitutionAlgebra.vars.varsList, List.mem_append]
          exact Or.inr member

/-- **A solution that agrees with the bindings substitutes as they do**, on an atom whose
variables the bindings give ground values. -/
theorem subst_eq_of_agrees {ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst}
    {σ : Subst} (agrees : Agrees ρ σ) {t : Atom} (bound : BoundGround (solution σ) t) :
    SubstitutionAlgebra.subst ρ t = SubstitutionAlgebra.subst (solution σ) t := by
  refine Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_congr_on_vars _ _ t ?_
  intro v member
  obtain ⟨a, isBound, ground⟩ := bound v member
  have value : SubstitutionAlgebra.subst ρ (.var v) = a := agrees v a isBound
  simp only [SubstitutionAlgebra.subst] at value
  cases given : ρ v with
  | none =>
      rw [given] at value
      simp only [Option.getD_none] at value
      rw [← value] at ground
      simp [isGroundAtom] at ground
  | some b =>
      rw [given] at value
      simp only [Option.getD_some] at value
      rw [value]
      exact isBound.symm

/-- **A solution of the pattern, untagged, is a solution of the renamed pattern**, when
the instance is ground. -/
theorem subst_rename_of_untagged
    (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (n : Nat) :
    ∀ (p b : Atom), SubstitutionAlgebra.subst (untagged ρ n) p = b → isGroundAtom b = true →
      SubstitutionAlgebra.subst ρ (rename n p) = b
  | .var x, b, solved, ground => by
      simp only [SubstitutionAlgebra.subst, untagged] at solved
      simp only [rename, SubstitutionAlgebra.subst]
      cases bound : ρ (tag n x) with
      | none =>
          rw [bound] at solved
          simp only [Option.getD_none] at solved
          rw [← solved] at ground
          simp [isGroundAtom] at ground
      | some value =>
          rw [bound] at solved
          simpa using solved
  | .symbol _, _, solved, _ => solved
  | .grounded _, _, solved, _ => solved
  | .expression es, b, solved, ground => by
      simp only [SubstitutionAlgebra.subst] at solved
      subst solved
      simp only [isGroundAtom] at ground
      simp only [rename, SubstitutionAlgebra.subst]
      rw [list es ground]
where
  list : ∀ es : List Atom,
      isGroundAtom.isGroundList (SubstitutionAlgebra.subst.substList (untagged ρ n) es) = true →
      SubstitutionAlgebra.subst.substList ρ (rename.renameList n es) =
        SubstitutionAlgebra.subst.substList (untagged ρ n) es
    | [], _ => rfl
    | e :: es, ground => by
        simp only [SubstitutionAlgebra.subst.substList, isGroundAtom.isGroundList,
          Bool.and_eq_true] at ground
        simp only [rename.renameList, SubstitutionAlgebra.subst.substList,
          subst_rename_of_untagged ρ n e _ rfl ground.1, list es ground.2]

/-! ## Templates closed in the kernel -/

/-- Every variable of the template occurs in a kernel pattern. -/
def Closed (pats : Footprint) (template : Atom) : Prop :=
  ∀ t ∈ split template, ∀ v ∈ SubstitutionAlgebra.vars t,
    ∃ e ∈ pats, v ∈ SubstitutionAlgebra.vars e.2

/-- Related lists: every element of the first has a related element of the second. -/
theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {u : List β}, List.Forall₂ R l u → ∀ a ∈ l, ∃ b ∈ u, R a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .cons head tail, a, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨b, inTail, related⟩ := forall₂_exists_right tail a member
        exact ⟨b, List.mem_cons_of_mem _ inTail, related⟩

/-- Bindings under which the kernel's patterns are ground atoms give every part of a
closed template ground values for its variables. -/
theorem boundGround_of_closed {pats fp : Footprint} {template : Atom} {σ : Subst}
    (closed : Closed pats template)
    (solved : List.Forall₂
      (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution σ) (e.2, f.2)) pats fp)
    (ground : ∀ f ∈ fp, isGroundAtom f.2 = true) :
    ∀ t ∈ split template, BoundGround (solution σ) t := by
  have each : ∀ e ∈ pats, BoundGround (solution σ) e.2 := by
    intro e member
    obtain ⟨f, inFp, _, solves⟩ := forall₂_exists_right solved e member
    have instanceGround : isGroundAtom (SubstitutionAlgebra.subst (solution σ) e.2) = true := by
      have same : SubstitutionAlgebra.subst (solution σ) e.2 =
          SubstitutionAlgebra.subst (solution σ) f.2 := solves
      rw [same, Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
        (vars_of_ground _ (ground f inFp))]
      exact ground f inFp
    exact boundGround_of_ground_subst _ _ instanceGround
  intro t inTemplate v member
  obtain ⟨e, inPats, inPattern⟩ := closed t inTemplate v member
  exact each e inPats v inPattern

/-- The instances of a closed template under such bindings are ground. -/
theorem instances_ground_of_closed {pats fp : Footprint} {template : Atom} {σ : Subst}
    (closed : Closed pats template)
    (solved : List.Forall₂
      (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution σ) (e.2, f.2)) pats fp)
    (ground : ∀ f ∈ fp, isGroundAtom f.2 = true) :
    ∀ a ∈ instances template σ, isGroundAtom a = true := by
  intro a member
  obtain ⟨t, inTemplate, rfl⟩ := List.mem_map.mp member
  rw [applySubst_eq_subst]
  exact ground_subst_of_boundGround _ _ (boundGround_of_closed closed solved ground t inTemplate)

/-! ## Fresh occurrences -/

/-- Fresh, distinct occurrences with given labels, outside a given finite set. -/
theorem exists_made {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t) :
    ∀ (labels : List Atom) (X : Finset O),
      ∃ made : List O, made.Nodup ∧ (∀ o ∈ made, o ∉ X) ∧ made.map label = labels
  | [], _ => ⟨[], List.nodup_nil, by simp, rfl⟩
  | t :: labels, X => by
      obtain ⟨made, nodup, outside, same⟩ := exists_made supply labels X
      obtain ⟨o, fresh, isLabel⟩ := supply (X ∪ made.toFinset) t
      have notInX : o ∉ X := fun inside => fresh (Finset.mem_union_left _ inside)
      have notMade : o ∉ made := fun inside =>
        fresh (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))
      refine ⟨o :: made, List.nodup_cons.mpr ⟨notMade, nodup⟩, ?_, by simp [isLabel, same]⟩
      intro x member
      rcases List.mem_cons.mp member with rfl | member
      · exact notInX
      · exact outside x member

namespace Controls

/-- A template variable that no kernel pattern binds stays in the instance: the instance
is not ground. -/
theorem open_template_instance_not_ground :
    isGroundAtom (applySubst [("x", a)] (.expression [.var "x", .var "y"])) = false := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
