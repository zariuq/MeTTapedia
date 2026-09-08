import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionParallel

/-!
# Binding laws for conversion-coherent native parallel development

Renaming and simultaneous parallel substitution preserve the native completed
parallel relation. The metadata guards remain derivations of authored
conversion: substitution transports them using the source substitution, while
the recursively developed arguments use the target substitution. No confluence
or conversion-checking assumption is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionParallel

open Presentation NativeIndexedFamilies NativeRelatorConversionCompletion

/-- Renaming retains each metadata coherence derivation and all five
native contraction shapes. -/
theorem par_rename {n m : Nat} (rho : Ren n m) {source target : Tower.Tm n} :
    Par source target → Par (rename rho source) (rename rho target)
  | .var _ => .var _
  | .const _ => .const _
  | .head _ => .head _
  | .headRel equality => .headRel equality
  | .pi domain codomain => .pi (par_rename rho domain) (par_rename (liftRen rho) codomain)
  | .sigma domain codomain =>
      .sigma (par_rename rho domain) (par_rename (liftRen rho) codomain)
  | .id carrier left right => .id (par_rename rho carrier) (par_rename rho left) (par_rename rho right)
  | .lam body => .lam (par_rename (liftRen rho) body)
  | .app function argument => .app (par_rename rho function) (par_rename rho argument)
  | .pair first second => .pair (par_rename rho first) (par_rename rho second)
  | .fst pair => .fst (par_rename rho pair)
  | .snd pair => .snd (par_rename rho pair)
  | .refl term => .refl (par_rename rho term)
  | .betaPi body argument => by
      simpa only [rename, rename_inst0] using
        (Par.betaPi (par_rename (liftRen rho) body) (par_rename rho argument))
  | .betaSigmaFst first second => .betaSigmaFst (par_rename rho first) (par_rename rho second)
  | .betaSigmaSnd first second => .betaSigmaSnd (par_rename rho first) (par_rename rho second)
  | .listNil ca a p z s =>
      .listNil (ca.renameTerms rho)
        (par_rename rho a) (par_rename rho p) (par_rename rho z) (par_rename rho s)
  | .listCons ca a p z s h t =>
      .listCons (ca.renameTerms rho)
        (par_rename rho a) (par_rename rho p) (par_rename rho z) (par_rename rho s)
        (par_rename rho h) (par_rename rho t)
  | .identity cy cw a x p d y witness =>
      .identity (cy.renameTerms rho) (cw.renameTerms rho)
        (par_rename rho a) (par_rename rho x) (par_rename rho p)
        (par_rename rho d) (par_rename rho y) (par_rename rho witness)
  | .relNil ca cb cr cx cy a b r p z s xs ys =>
      .relNil (ca.renameTerms rho) (cb.renameTerms rho) (cr.renameTerms rho)
        (cx.renameTerms rho) (cy.renameTerms rho)
        (par_rename rho a) (par_rename rho b) (par_rename rho r) (par_rename rho p)
        (par_rename rho z) (par_rename rho s) (par_rename rho xs) (par_rename rho ys)
  | .relCons ca cb cr cx cy a b r p z s xs ys h k t u he te =>
      .relCons (ca.renameTerms rho) (cb.renameTerms rho) (cr.renameTerms rho)
        (cx.renameTerms rho) (cy.renameTerms rho)
        (par_rename rho a) (par_rename rho b) (par_rename rho r) (par_rename rho p)
        (par_rename rho z) (par_rename rho s) (par_rename rho xs) (par_rename rho ys)
        (par_rename rho h) (par_rename rho k) (par_rename rho t) (par_rename rho u)
        (par_rename rho he) (par_rename rho te)

/-- The new binder remains variable zero, and every older replacement is
weakened before its parallel development is reused. -/
theorem parallel_liftSub {n m : Nat} {source target : Sub Tower.Head n m}
    (arguments : ∀ i, Par (source i) (target i)) :
    ∀ i, Par (liftSub source i) (liftSub target i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact .var 0
  · intro prior
    exact par_rename wk (arguments prior)

/-- Simultaneous parallel substitution preserves all five native branches. The
authored coherence guards are transported, not recomputed or erased. -/
theorem par_substitute {n m : Nat} {sourceSub targetSub : Sub Tower.Head n m}
    (arguments : ∀ i, Par (sourceSub i) (targetSub i))
    {source target : Tower.Tm n} :
    Par source target → Par (subst sourceSub source) (subst targetSub target)
  | .var index => arguments index
  | .const _ => .const _
  | .head _ => .head _
  | .headRel equality => .headRel equality
  | .pi domain codomain =>
      .pi (par_substitute arguments domain) (par_substitute (parallel_liftSub arguments) codomain)
  | .sigma domain codomain =>
      .sigma (par_substitute arguments domain)
        (par_substitute (parallel_liftSub arguments) codomain)
  | .id carrier left right =>
      .id (par_substitute arguments carrier) (par_substitute arguments left)
        (par_substitute arguments right)
  | .lam body => .lam (par_substitute (parallel_liftSub arguments) body)
  | .app function argument => .app (par_substitute arguments function) (par_substitute arguments argument)
  | .pair first second => .pair (par_substitute arguments first) (par_substitute arguments second)
  | .fst pair => .fst (par_substitute arguments pair)
  | .snd pair => .snd (par_substitute arguments pair)
  | .refl term => .refl (par_substitute arguments term)
  | .betaPi body argument => by
      simpa only [subst, subst_inst0] using
        (Par.betaPi (par_substitute (parallel_liftSub arguments) body)
          (par_substitute arguments argument))
  | .betaSigmaFst first second =>
      .betaSigmaFst (par_substitute arguments first) (par_substitute arguments second)
  | .betaSigmaSnd first second =>
      .betaSigmaSnd (par_substitute arguments first) (par_substitute arguments second)
  | .listNil ca a p z s =>
      .listNil (ca.substitute sourceSub)
        (par_substitute arguments a) (par_substitute arguments p)
        (par_substitute arguments z) (par_substitute arguments s)
  | .listCons ca a p z s h t =>
      .listCons (ca.substitute sourceSub)
        (par_substitute arguments a) (par_substitute arguments p)
        (par_substitute arguments z) (par_substitute arguments s)
        (par_substitute arguments h) (par_substitute arguments t)
  | .identity cy cw a x p d y witness =>
      .identity (cy.substitute sourceSub) (cw.substitute sourceSub)
        (par_substitute arguments a) (par_substitute arguments x)
        (par_substitute arguments p) (par_substitute arguments d)
        (par_substitute arguments y) (par_substitute arguments witness)
  | .relNil ca cb cr cx cy a b r p z s xs ys =>
      .relNil (ca.substitute sourceSub) (cb.substitute sourceSub) (cr.substitute sourceSub)
        (cx.substitute sourceSub) (cy.substitute sourceSub)
        (par_substitute arguments a) (par_substitute arguments b)
        (par_substitute arguments r) (par_substitute arguments p)
        (par_substitute arguments z) (par_substitute arguments s)
        (par_substitute arguments xs) (par_substitute arguments ys)
  | .relCons ca cb cr cx cy a b r p z s xs ys h k t u he te =>
      .relCons (ca.substitute sourceSub) (cb.substitute sourceSub) (cr.substitute sourceSub)
        (cx.substitute sourceSub) (cy.substitute sourceSub)
        (par_substitute arguments a) (par_substitute arguments b)
        (par_substitute arguments r) (par_substitute arguments p)
        (par_substitute arguments z) (par_substitute arguments s)
        (par_substitute arguments xs) (par_substitute arguments ys)
        (par_substitute arguments h) (par_substitute arguments k)
        (par_substitute arguments t) (par_substitute arguments u)
        (par_substitute arguments he) (par_substitute arguments te)

/-- Binder instantiation develops the substituted argument and the body
together, including any completed native root beneath that binder. -/
theorem par_inst0 {n : Nat} {argument argument' : Tower.Tm n}
    {body body' : Tower.Tm (n + 1)} (argumentStep : Par argument argument')
    (bodyStep : Par body body') :
    Par (inst0 argument body) (inst0 argument' body') := by
  apply par_substitute (sourceSub := subst0 argument) (targetSub := subst0 argument') _ bodyStep
  intro i
  refine Fin.cases ?_ ?_ i
  · exact argumentStep
  · intro prior
    exact .var prior

namespace BindingExamples

def ground {n : Nat} : Tower.Tm n := .head .legacyGround
def betaGround {n : Nat} : Tower.Tm n := .app (.lam (.var 0)) ground

/-- The free parameter occurs as the outer element type, its nil index,
the selected branch and a convertible copy in the retained relation witness. -/
def openRelNil : Tower.Tm 1 :=
  IntrinsicRelator.eliminateApp (.var 0) ground ground ground (.var 0) ground
    (Intrinsic.nilApp (.var 0)) (Intrinsic.nilApp ground)
    (IntrinsicRelator.nilRelApp (.app (.lam (.var 0)) (.var 0)) ground ground)

theorem openRelNil_parallel : Par openRelNil (.var 0) :=
  .relNil (.rel _ _ (.betaPi _ _)) (.refl _) (.refl _) (.refl _) (.refl _)
    (par_refl _) (par_refl _) (par_refl _) (par_refl _)
    (par_refl _) (par_refl _) (par_refl _) (par_refl _)

/-- The raw relational contraction survives simultaneous development of the
replacement while retaining converted metadata under the source substitution. -/
theorem substitutedRelNil_parallel :
    Par (inst0 (betaGround : Tower.Tm 0) openRelNil) ground :=
  par_inst0 (.betaPi (par_refl _) (par_refl _)) openRelNil_parallel

theorem substitution_under_binder :
    Par (.lam (betaGround : Tower.Tm 1) : Tower.Tm 0) (.lam ground) := by
  have arguments : ∀ i : Fin 1,
      Par ((subst0 (betaGround : Tower.Tm 0)) i) ((subst0 (ground : Tower.Tm 0)) i) := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact .betaPi (par_refl _) (par_refl _)
  exact par_substitute arguments (par_refl (.lam (.var 1) : Tower.Tm 1))

theorem captured_variable_not_parallel :
    ¬ Par (.lam (ground : Tower.Tm 1) : Tower.Tm 0) (.lam (.var 0)) := by
  intro parallel
  cases parallel with
  | lam body => cases body

end BindingExamples

#print axioms par_rename
#print axioms parallel_liftSub
#print axioms par_substitute
#print axioms par_inst0
#print axioms BindingExamples.openRelNil_parallel
#print axioms BindingExamples.substitutedRelNil_parallel
#print axioms BindingExamples.substitution_under_binder
#print axioms BindingExamples.captured_variable_not_parallel

end NativeRelatorConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
