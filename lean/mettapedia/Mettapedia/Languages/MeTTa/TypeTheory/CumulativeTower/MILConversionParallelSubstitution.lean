import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionParallel

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
namespace MILConversionParallel

open Presentation IntrinsicMILHypothesis MILConversionCompletion

/-- Renaming retains all four metadata coherence derivations and every
primitive or chain development. -/
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
  | .primitive cs cp cx cy sorts primitives motive pc cc source target symbol =>
      .primitive (cs.renameTerms rho) (cp.renameTerms rho) (cx.renameTerms rho) (cy.renameTerms rho)
        (par_rename rho sorts) (par_rename rho primitives) (par_rename rho motive)
        (par_rename rho pc) (par_rename rho cc) (par_rename rho source)
        (par_rename rho target) (par_rename rho symbol)
  | .chain cs cp cx cy sorts primitives motive pc cc source middle target earlier later =>
      .chain (cs.renameTerms rho) (cp.renameTerms rho) (cx.renameTerms rho) (cy.renameTerms rho)
        (par_rename rho sorts) (par_rename rho primitives) (par_rename rho motive)
        (par_rename rho pc) (par_rename rho cc) (par_rename rho source)
        (par_rename rho middle) (par_rename rho target) (par_rename rho earlier) (par_rename rho later)

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

/-- Simultaneous parallel substitution preserves both native branches. The
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
  | .primitive cs cp cx cy sorts primitives motive pc cc source target symbol =>
      .primitive (cs.substitute sourceSub) (cp.substitute sourceSub)
        (cx.substitute sourceSub) (cy.substitute sourceSub)
        (par_substitute arguments sorts) (par_substitute arguments primitives)
        (par_substitute arguments motive) (par_substitute arguments pc)
        (par_substitute arguments cc) (par_substitute arguments source)
        (par_substitute arguments target) (par_substitute arguments symbol)
  | .chain cs cp cx cy sorts primitives motive pc cc source middle target earlier later =>
      .chain (cs.substitute sourceSub) (cp.substitute sourceSub)
        (cx.substitute sourceSub) (cy.substitute sourceSub)
        (par_substitute arguments sorts) (par_substitute arguments primitives)
        (par_substitute arguments motive) (par_substitute arguments pc)
        (par_substitute arguments cc) (par_substitute arguments source)
        (par_substitute arguments middle) (par_substitute arguments target)
        (par_substitute arguments earlier) (par_substitute arguments later)

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

/-- A free parameter occurs in the metadata twice with distinct convertible
syntax, and also as the primitive symbol retained by the result. -/
def openPrimitive : Tower.Tm 1 :=
  eliminateApp (.var 0) Examples.ground Examples.ground (.const hypothesisName)
    Examples.ground Examples.ground Examples.ground
    (primitiveApp (.app (.lam (.var 0)) (.var 0)) Examples.ground
      Examples.ground Examples.ground (.var 0))

def openResult : Tower.Tm 1 :=
  .app (.app (.app (.const hypothesisName) Examples.ground) Examples.ground) (.var 0)

theorem openPrimitive_parallel : Par openPrimitive openResult :=
  .primitive (.rel _ _ (.betaPi _ _)) (.refl _) (.refl _) (.refl _)
    (par_refl _) (par_refl _) (par_refl _) (par_refl _) (par_refl _)
    (par_refl _) (par_refl _) (par_refl _)

/-- The actual primitive contraction survives replacement of its free
parameter by a simultaneously developed beta redex. -/
theorem substitutedPrimitive_parallel :
    Par (inst0 (Examples.betaGround : Tower.Tm 0) openPrimitive)
      (inst0 Examples.ground openResult) :=
  par_inst0 (.betaPi (par_refl _) (par_refl _)) openPrimitive_parallel

/-- A free replacement remains free from the new binder and develops under
that binder. -/
theorem substitution_under_binder :
    Par (.lam (Examples.betaGround : Tower.Tm 1) : Tower.Tm 0)
      (.lam Examples.ground) := by
  have arguments : ∀ i : Fin 1,
      Par ((subst0 (Examples.betaGround : Tower.Tm 0)) i)
        ((subst0 (Examples.ground : Tower.Tm 0)) i) := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact .betaPi (par_refl _) (par_refl _)
  exact par_substitute arguments (par_refl (.lam (.var 1) : Tower.Tm 1))

/-- Capturing that replacement as the freshly bound variable is impossible
in the actual completed parallel relation. -/
theorem captured_variable_not_parallel :
    ¬ Par (.lam (Examples.ground : Tower.Tm 1) : Tower.Tm 0) (.lam (.var 0)) := by
  intro parallel
  cases parallel with
  | lam body => cases body

end BindingExamples

#print axioms par_rename
#print axioms parallel_liftSub
#print axioms par_substitute
#print axioms par_inst0
#print axioms BindingExamples.openPrimitive_parallel
#print axioms BindingExamples.substitutedPrimitive_parallel
#print axioms BindingExamples.substitution_under_binder
#print axioms BindingExamples.captured_variable_not_parallel

end MILConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
