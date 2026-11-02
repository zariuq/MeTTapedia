import Mettapedia.Logic.HOL.PredicateContexts
import Mettapedia.Logic.HOL.Syntax.SubstitutionExtension

/-!
# Instantiating predicate contexts in arbitrary proof environments

The target hypotheses need not themselves be a telescope. Each new source
binder is assigned an actual target term together with its instantiated
predicate proof. Target renaming and fresh guarded binders retain these
proofs, including duplicate source occurrences and aliased variable images.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateContexts.Telescope.Realizes

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ Ω : Ctx Base}
    {context : Telescope Const Γ} {images : Subst Const Γ Ξ}
    {assumptions : List (Formula Const Ξ)}

def mono (realizer : context.Realizes images assumptions)
    {target : List (Formula Const Ξ)} (placement : ProofSyntax.OccurrenceMap assumptions target) :
    context.Realizes images target := fun index => (realizer index).mono placement

theorem mono_free (realizer : context.Realizes images assumptions)
    {target : List (Formula Const Ξ)} (placement : ProofSyntax.OccurrenceMap assumptions target)
    (free : ∀ {type} (index : Var Γ type), (realizer index).FunctionExtensionalityFree) :
    ∀ {type} (index : Var Γ type), (realizer.mono placement index).FunctionExtensionalityFree := by
  intro type index
  exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (free index)

private theorem subst_cons_weaken {domain result : Ty Base}
    (argument : Term Const Ξ domain) (images : Subst Const Γ Ξ) (term : Term Const Γ result) :
    subst (Subst.cons argument images) (weaken term) = subst images term := by
  rw [weaken, subst_rename]
  rfl

def cons (realizer : context.Realizes images assumptions) {domain : Ty Base}
    (predicate : Term Const Γ (domain ⇒ .prop)) (argument : Term Const Ξ domain)
    (member : ProofSyntax Const assumptions (.app (subst images predicate) argument)) :
    (context.snoc predicate).Realizes (Subst.cons argument images) assumptions := fun index =>
  match index with
  | .vz => by
      apply ProofSyntax.castIndices rfl ?_ member
      simp only [Telescope.guard, Telescope.domain, subst, Subst.cons, subst_cons_weaken]
  | .vs prior => by
      apply ProofSyntax.castIndices rfl ?_ (realizer prior)
      simp only [Telescope.guard, Telescope.domain, subst, Subst.cons, subst_cons_weaken]

theorem cons_free (realizer : context.Realizes images assumptions) {domain : Ty Base}
    (predicate : Term Const Γ (domain ⇒ .prop)) (argument : Term Const Ξ domain)
    (member : ProofSyntax Const assumptions (.app (subst images predicate) argument))
    (free : ∀ {type} (index : Var Γ type), (realizer index).FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    ∀ {type} (index : Var (domain :: Γ) type),
      (realizer.cons predicate argument member index).FunctionExtensionalityFree := by
  intro type index
  cases index with
  | vz => simpa only [cons, ProofSyntax.functionExtensionalityFree_castIndices] using memberFree
  | vs prior => simpa only [cons, ProofSyntax.functionExtensionalityFree_castIndices] using free prior

def renameTarget (realizer : context.Realizes images assumptions) (rho : Rename Base Ξ Ω) :
    context.Realizes (fun index => rename rho (images index)) (assumptions.map (rename rho)) :=
  fun index => ProofSyntax.castIndices rfl (rename_subst rho images _)
    (ProofSyntax.renameShared rho (realizer index))

theorem renameTarget_free (realizer : context.Realizes images assumptions) (rho : Rename Base Ξ Ω)
    (free : ∀ {type} (index : Var Γ type), (realizer index).FunctionExtensionalityFree) :
    ∀ {type} (index : Var Γ type), (realizer.renameTarget rho index).FunctionExtensionalityFree := by
  intro type index
  simpa only [renameTarget, ProofSyntax.renameShared_eq, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free index

def liftUnderGuard (realizer : context.Realizes images assumptions) {domain : Ty Base}
    (predicate : Term Const Γ (domain ⇒ .prop)) :
    (context.snoc predicate).Realizes (Subst.lift images)
      (.app (weaken (subst images predicate)) (.var .vz) :: weakenHyps assumptions) :=
  let guard := Term.app (weaken (subst images predicate)) (.var .vz)
  let raised : context.Realizes (fun index => weaken (images index)) (guard :: weakenHyps assumptions) :=
    mono (renameTarget realizer Rename.weaken) (ProofSyntax.OccurrenceMap.prepend guard)
  cons raised predicate (.var .vz) (ProofSyntax.castIndices rfl (by
    exact congrArg (fun code => Term.app code (.var .vz)) (rename_subst Rename.weaken images predicate)) (.hyp 0))

theorem liftUnderGuard_free (realizer : context.Realizes images assumptions) {domain : Ty Base}
    (predicate : Term Const Γ (domain ⇒ .prop))
    (free : ∀ {type} (index : Var Γ type), (realizer index).FunctionExtensionalityFree) :
    ∀ {type} (index : Var (domain :: Γ) type),
      (realizer.liftUnderGuard predicate index).FunctionExtensionalityFree := by
  unfold liftUnderGuard
  apply cons_free
  · apply mono_free
    exact renameTarget_free realizer Rename.weaken free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

theorem transport_free (realizer : context.Realizes images assumptions)
    {formula : Formula Const Γ} (proof : ProofSyntax Const context.hypotheses formula)
    (guardsFree : ∀ {type} (index : Var Γ type), (realizer index).FunctionExtensionalityFree)
    (proofFree : proof.FunctionExtensionalityFree) :
    (realizer.transport proof).FunctionExtensionalityFree := by
  apply ProofSyntax.substituteHypotheses_free
  · exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr proofFree
  · exact hypotheses_free realizer guardsFree

#print axioms cons_free
#print axioms liftUnderGuard_free
#print axioms transport_free

end Mettapedia.Logic.HOL.PredicateContexts.Telescope.Realizes

namespace Mettapedia.Logic.HOL.ProofSyntax.HypothesisSubstitution

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {target : List (Formula Const Γ)} {formula : Formula Const Γ}

def single (proof : ProofSyntax Const target formula) : HypothesisSubstitution [formula] target :=
  Fin.cases proof (fun impossible => nomatch impossible)

theorem single_free (proof : ProofSyntax Const target formula) (free : proof.FunctionExtensionalityFree) :
    ∀ occurrence, (single proof occurrence).FunctionExtensionalityFree := by
  intro occurrence
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
  exact free

end Mettapedia.Logic.HOL.ProofSyntax.HypothesisSubstitution
