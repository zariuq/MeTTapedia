import Mettapedia.Logic.HOL.OrderedPositionActivityReadback

/-!
# Child-index transport and selection for uniformly labelled position plans

The position and the original plan stay fixed while a proved child-index
equality changes the query target. A plan with one declared label recovers
that label from any successful lookup, without arithmetic assumptions or an
index-selection oracle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))

def targetQuery (plan : Plan Const Γ number index) (images : Subst Const Γ Ξ) (slot : Term Const Ξ number) :
    Term Const Ξ (index ⇒ .prop) :=
  .lam (compileAt zero successor plan (fun entry => weaken (images entry)) (weaken slot) (.var .vz))

def targetQuery_beta {Δ : List (Formula Const Ξ)} (plan : Plan Const Γ number index) (images : Subst Const Γ Ξ)
    (slot : Term Const Ξ number) (target : Term Const Ξ index) :
    ProofSyntax Const Δ (.eq (.app (targetQuery zero successor plan images slot) target)
      (compileAt zero successor plan images slot target)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta target
    (compileAt zero successor plan (fun entry => weaken (images entry)) (weaken slot) (.var .vz)))
  apply congrArg₂ Term.eq
  · rfl
  · simp only [instantiate,compileAt_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem targetQuery_beta_free {Δ : List (Formula Const Ξ)} (plan : Plan Const Γ number index) (images : Subst Const Γ Ξ)
    (slot : Term Const Ξ number) (target : Term Const Ξ index) :
    (targetQuery_beta (Δ := Δ) zero successor plan images slot target).FunctionExtensionalityFree := by
  unfold targetQuery_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def targetEquality {Δ : List (Formula Const Ξ)} (plan : Plan Const Γ number index) (images : Subst Const Γ Ξ)
    (slot : Term Const Ξ number) (first second : Term Const Ξ index) (same : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (compileAt zero successor plan images slot first) (compileAt zero successor plan images slot second)) :=
  .eqTrans (.eqSymm (targetQuery_beta zero successor plan images slot first))
    (.eqTrans (.eqAppArg (targetQuery zero successor plan images slot) same)
      (targetQuery_beta zero successor plan images slot second))

theorem targetEquality_free {Δ : List (Formula Const Ξ)} (plan : Plan Const Γ number index) (images : Subst Const Γ Ξ)
    (slot : Term Const Ξ number) (first second : Term Const Ξ index) (same : ProofSyntax Const Δ (.eq first second))
    (free : same.FunctionExtensionalityFree) :
    (targetEquality zero successor plan images slot first second same).FunctionExtensionalityFree :=
  ⟨targetQuery_beta_free _ _ _ _ _ _,free,targetQuery_beta_free _ _ _ _ _ _⟩

def withLabel (counts : List (Term Const Γ number)) (label : Term Const Γ index) : Plan Const Γ number index :=
  counts.map (fun count => (count,label))

def labelFromLookup (label : Term Const Γ index) :
    (counts : List (Term Const Γ number)) → {Ξ : Ctx Base} → (images : Subst Const Γ Ξ) →
    (slot : Term Const Ξ number) → (target : Term Const Ξ index) → {Δ : List (Formula Const Ξ)} →
    ProofSyntax Const Δ (compileAt zero successor (withLabel counts label) images slot target) →
    ProofSyntax Const Δ (.eq target (HOL.subst images label))
  | [], _, _, _, _, _, present => .botE present
  | _ :: rest, _, images, _, target, _, present => by
      apply ProofSyntax.orE present
      · exact .andER (.hyp 0)
      · apply ProofSyntax.exE (.hyp 0)
        apply ProofSyntax.castIndices rfl ?_
          (labelFromLookup label rest (fun entry => weaken (images entry)) (.var .vz) (weaken target) (.andER (.hyp 0)))
        apply congrArg (Term.eq (weaken target))
        exact (HOL.rename_subst Rename.weaken images label).symm

theorem labelFromLookup_free (label : Term Const Γ index) (counts : List (Term Const Γ number))
    {Ξ : Ctx Base} (images : Subst Const Γ Ξ) (slot : Term Const Ξ number) (target : Term Const Ξ index)
    {Δ : List (Formula Const Ξ)}
    (present : ProofSyntax Const Δ (compileAt zero successor (withLabel counts label) images slot target))
    (free : present.FunctionExtensionalityFree) :
    (labelFromLookup zero successor label counts images slot target present).FunctionExtensionalityFree := by
  induction counts generalizing Ξ with
  | nil => exact free
  | cons count rest previous =>
      unfold labelFromLookup
      refine ⟨free,True.intro,True.intro,?_⟩
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact previous _ _ _ _ trivial

def knownIndex {Δ : List (Formula Const Γ)} (counts : List (Term Const Γ number)) (label : Term Const Γ index)
    (slot : Term Const Γ number) (active : ProofSyntax Const Δ (activeAt zero successor (withLabel counts label) slot)) :
    ProofSyntax Const Δ (compileAt zero successor (withLabel counts label) Subst.id slot label) := by
  apply ProofSyntax.exE active
  let images : Subst Const Γ (index :: Γ) := Subst.ofRename Rename.weaken
  let body := compileAt zero successor (withLabel counts label) images (weaken slot) (.var .vz)
  let assumptions := body :: weakenHyps Δ
  have same := labelFromLookup zero successor label counts images (weaken slot) (.var .vz) (ProofSyntax.hyp (Δ := assumptions) 0)
  have labelEq : ProofSyntax Const assumptions (.eq (.var .vz) (weaken label)) :=
    ProofSyntax.castIndices rfl (congrArg (Term.eq (.var .vz)) (subst_ofRename Rename.weaken label)) same
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropEL (targetEquality zero successor (withLabel counts label) images (weaken slot) (.var .vz) (weaken label) labelEq))
      (.hyp (Δ := assumptions) 0))
  simp only [weaken,compileAt_rename]
  rfl

theorem knownIndex_free {Δ : List (Formula Const Γ)} (counts : List (Term Const Γ number)) (label : Term Const Γ index)
    (slot : Term Const Γ number) (active : ProofSyntax Const Δ (activeAt zero successor (withLabel counts label) slot))
    (free : active.FunctionExtensionalityFree) :
    (knownIndex zero successor counts label slot active).FunctionExtensionalityFree := by
  unfold knownIndex
  refine ⟨free,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨?_,True.intro⟩
  apply targetEquality_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact labelFromLookup_free _ _ _ _ _ _ _ _ trivial

#print axioms knownIndex_free
end Mettapedia.Logic.HOL.OrderedPositionPrograms
