import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextualPreservation

/-!
# A typed term keeps its set value along every reduction

A set model gives every term a set. This file relates that set to what the term does when
its package's steps are applied to it, at any position and in any order.

In a package whose type formers are injective and distinct, whose root steps of typed terms
are equalities and whose head equality preserves typing (the hypotheses of
`Annotated.ContextualPreservation`), and which has a set model:

* **the value does not change** (`reduction_value_eq`): a term typed in a formed context has
  the same set as every term it reduces to, at every environment that satisfies the context;
* the set of every reduct is a member of the set of the type (`reduction_value_mem`);
* **two reducts have one value** (`reducts_value_eq`);
* **results are determined** (`result_unique`): on a class of closed terms that the model
  reads injectively, a typed closed term reduces to at most one term of the class.

No statement here uses termination or confluence, and none gives them. A term whose
reduction never stops has one value at every stage of it. The last statement is what a
reading of data terms that is injective buys the running side: two runs of one typed term
that both end in data terms end in the same data term.

The hypothesis on the type formers is needed. A set model alone does not make the β-step
keep the value: the model reads functions as traces, the trace of a function does not
record its domain, so two function types with different domains can have one set, and a
package may declare them equal (`Instances.MegalodonHOTG.ReductionValueControls`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (LevelModel)
open Mettapedia.TypeTheory.UniverseLevel (LevelOrder)

universe u

variable {Head L : Type} [LevelOrder L] {R : Rules Head} {P : ChurchRules R}
  {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}

section Values

variable (model : SetModel heads consts P) (facts : CFormerFacts P) (levels : LevelModel R L)
  (admitted : CRootAdmitted P) (preserving : CHeadPreserving P)

include model facts levels admitted preserving

/-- **A typed term keeps its set value along every reduction**, at every environment that
satisfies its context. -/
theorem reduction_value_eq {n : Nat} {Γ : CCtx Head n} {t s T : CTm Head n}
    (formed : CCtxFormed P Γ) (typing : CTyped P Γ t T) (reduces : CReduces P t s)
    (ρ : Env.{u} n) (sat : Sat heads consts Γ ρ) :
    ev heads consts t ρ = ev heads consts s ρ :=
  CDerivable.sound_equality model
    (CReduces.equal facts levels admitted preserving formed reduces typing) ρ sat

/-- The set of a reduct of a typed term is a member of the set of the term's type. -/
theorem reduction_value_mem {n : Nat} {Γ : CCtx Head n} {t s T : CTm Head n}
    (formed : CCtxFormed P Γ) (typing : CTyped P Γ t T) (reduces : CReduces P t s)
    (ρ : Env.{u} n) (sat : Sat heads consts Γ ρ) :
    ev heads consts s ρ ∈ ev heads consts T ρ :=
  CDerivable.sound model
    (CReduces.typed facts levels admitted preserving formed reduces typing) ρ sat

/-- **Two reducts of one typed term have one value.** -/
theorem reducts_value_eq {n : Nat} {Γ : CCtx Head n} {t s s' T : CTm Head n}
    (formed : CCtxFormed P Γ) (typing : CTyped P Γ t T) (first : CReduces P t s)
    (second : CReduces P t s') (ρ : Env.{u} n) (sat : Sat heads consts Γ ρ) :
    ev heads consts s ρ = ev heads consts s' ρ :=
  (reduction_value_eq model facts levels admitted preserving formed typing first ρ sat).symm.trans
    (reduction_value_eq model facts levels admitted preserving formed typing second ρ sat)

/-- **Results are determined.** On a class of closed terms that the model reads injectively,
a typed closed term reduces to at most one term of the class. -/
theorem result_unique {t s s' T : CTm Head 0} (typing : CTyped P .nil t T)
    (first : CReduces P t s) (second : CReduces P t s') {Result : CTm Head 0 → Prop}
    (injective : ∀ {a b : CTm Head 0}, Result a → Result b →
      ev heads consts a Fin.elim0 = ev heads consts b Fin.elim0 → a = b)
    (isResult : Result s) (isResult' : Result s') : s = s' :=
  injective isResult isResult'
    (reducts_value_eq model facts levels admitted preserving .nil typing first second Fin.elim0
      (sat_nil heads consts Fin.elim0))

end Values

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
