import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationComputation
import Mettapedia.TypeTheory.JudgmentalEquality

/-!
# Proof-relevant structural computation for declaration-aware Prime

`Presentation.StepCore` is the established proposition-valued support
relation used by conversion.  It is intentionally proof irrelevant.  Native
execution, replay, cost, and higher-dimensional semantics additionally need
to retain which structural rule fired and the complete congruence path.

`StructuralStepReceipt` is the type-valued layer above that support.  It
mirrors every structural constructor and accepts a
`ProofRelevantRootComputation` for declaration-specific steps.  The two
layers are connected by an exact theorem:

```
StepCore computation.support headEq source target
  <-> Nonempty (StructuralStepReceipt computation headEq source target)
```

Thus ordinary conversion consumes support, while native execution may keep
the receipt.  Renaming and substitution act directly on receipts, including
the declaration-provided root witness.  This is the computational enrichment
needed by a judgmental/comprehension model; it does not quotient receipts or
turn their endpoints into Lean equality.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace ProofRelevantStructuralComputation

open Declaration
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.JudgmentalEquality

universe uEvidence

/-- Type-valued evidence for one structural computation step.  Primitive
head equality is lifted only as data; declaration-specific computation keeps
the authored evidence supplied by `computation`. -/
inductive StructuralStepReceipt
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) :
    Tm Head n → Tm Head n → Type (max uEvidence 0) where
  | betaPi (body : Tm Head (n + 1)) (argument : Tm Head n) :
      StructuralStepReceipt computation headEq
        (.app (.lam body) argument) (inst0 argument body)
  | betaSigmaFst (first second : Tm Head n) :
      StructuralStepReceipt computation headEq (.fst (.pair first second)) first
  | betaSigmaSnd (first second : Tm Head n) :
      StructuralStepReceipt computation headEq (.snd (.pair first second)) second
  | head {left right : Head} :
      PLift (headEq left right) →
      StructuralStepReceipt computation headEq (.head left) (.head right)
  | root {left right : Tm Head n} :
      computation.Evidence left right →
      StructuralStepReceipt computation headEq left right
  | congPiDom {domain domain' : Tm Head n} {codomain : Tm Head (n + 1)} :
      StructuralStepReceipt computation headEq domain domain' →
      StructuralStepReceipt computation headEq
        (.pi domain codomain) (.pi domain' codomain)
  | congPiCod {domain : Tm Head n} {codomain codomain' : Tm Head (n + 1)} :
      StructuralStepReceipt computation headEq codomain codomain' →
      StructuralStepReceipt computation headEq
        (.pi domain codomain) (.pi domain codomain')
  | congSigmaDom {domain domain' : Tm Head n}
      {codomain : Tm Head (n + 1)} :
      StructuralStepReceipt computation headEq domain domain' →
      StructuralStepReceipt computation headEq
        (.sigma domain codomain) (.sigma domain' codomain)
  | congSigmaCod {domain : Tm Head n}
      {codomain codomain' : Tm Head (n + 1)} :
      StructuralStepReceipt computation headEq codomain codomain' →
      StructuralStepReceipt computation headEq
        (.sigma domain codomain) (.sigma domain codomain')
  | congIdTy {type type' left right : Tm Head n} :
      StructuralStepReceipt computation headEq type type' →
      StructuralStepReceipt computation headEq
        (.id type left right) (.id type' left right)
  | congIdLeft {type left left' right : Tm Head n} :
      StructuralStepReceipt computation headEq left left' →
      StructuralStepReceipt computation headEq
        (.id type left right) (.id type left' right)
  | congIdRight {type left right right' : Tm Head n} :
      StructuralStepReceipt computation headEq right right' →
      StructuralStepReceipt computation headEq
        (.id type left right) (.id type left right')
  | congLam {body body' : Tm Head (n + 1)} :
      StructuralStepReceipt computation headEq body body' →
      StructuralStepReceipt computation headEq (.lam body) (.lam body')
  | congAppFun {function function' argument : Tm Head n} :
      StructuralStepReceipt computation headEq function function' →
      StructuralStepReceipt computation headEq
        (.app function argument) (.app function' argument)
  | congAppArg {function argument argument' : Tm Head n} :
      StructuralStepReceipt computation headEq argument argument' →
      StructuralStepReceipt computation headEq
        (.app function argument) (.app function argument')
  | congPairFst {first first' second : Tm Head n} :
      StructuralStepReceipt computation headEq first first' →
      StructuralStepReceipt computation headEq
        (.pair first second) (.pair first' second)
  | congPairSnd {first second second' : Tm Head n} :
      StructuralStepReceipt computation headEq second second' →
      StructuralStepReceipt computation headEq
        (.pair first second) (.pair first second')
  | congFst {pair pair' : Tm Head n} :
      StructuralStepReceipt computation headEq pair pair' →
      StructuralStepReceipt computation headEq (.fst pair) (.fst pair')
  | congSnd {pair pair' : Tm Head n} :
      StructuralStepReceipt computation headEq pair pair' →
      StructuralStepReceipt computation headEq (.snd pair) (.snd pair')
  | congRefl {term term' : Tm Head n} :
      StructuralStepReceipt computation headEq term term' →
      StructuralStepReceipt computation headEq (.refl term) (.refl term')

namespace StructuralStepReceipt

/-- Forget the retained structural receipt to the established support step. -/
def toSupport
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n} :
    StructuralStepReceipt computation headEq left right →
      StepCore computation.support headEq left right
  | .betaPi body argument => .betaPi body argument
  | .betaSigmaFst first second => .betaSigmaFst first second
  | .betaSigmaSnd first second => .betaSigmaSnd first second
  | .head equality => .head equality.down
  | .root evidence => .root ⟨evidence⟩
  | .congPiDom receipt => .congPiDom receipt.toSupport
  | .congPiCod receipt => .congPiCod receipt.toSupport
  | .congSigmaDom receipt => .congSigmaDom receipt.toSupport
  | .congSigmaCod receipt => .congSigmaCod receipt.toSupport
  | .congIdTy receipt => .congIdTy receipt.toSupport
  | .congIdLeft receipt => .congIdLeft receipt.toSupport
  | .congIdRight receipt => .congIdRight receipt.toSupport
  | .congLam receipt => .congLam receipt.toSupport
  | .congAppFun receipt => .congAppFun receipt.toSupport
  | .congAppArg receipt => .congAppArg receipt.toSupport
  | .congPairFst receipt => .congPairFst receipt.toSupport
  | .congPairSnd receipt => .congPairSnd receipt.toSupport
  | .congFst receipt => .congFst receipt.toSupport
  | .congSnd receipt => .congSnd receipt.toSupport
  | .congRefl receipt => .congRefl receipt.toSupport

/-- Every supported structural step has at least one retained receipt, and
every retained receipt erases to that support. -/
theorem support_iff_nonempty
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) {left right : Tm Head n} :
    StepCore computation.support headEq left right ↔
      Nonempty (StructuralStepReceipt computation headEq left right) := by
  constructor
  · intro support
    induction support with
    | betaPi body argument => exact ⟨.betaPi body argument⟩
    | betaSigmaFst first second => exact ⟨.betaSigmaFst first second⟩
    | betaSigmaSnd first second => exact ⟨.betaSigmaSnd first second⟩
    | head equality => exact ⟨.head ⟨equality⟩⟩
    | root evidence =>
        rcases evidence with ⟨receipt⟩
        exact ⟨.root receipt⟩
    | congPiDom _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPiDom receipt⟩
    | congPiCod _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPiCod receipt⟩
    | congSigmaDom _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congSigmaDom receipt⟩
    | congSigmaCod _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congSigmaCod receipt⟩
    | congIdTy _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congIdTy receipt⟩
    | congIdLeft _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congIdLeft receipt⟩
    | congIdRight _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congIdRight receipt⟩
    | congLam _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congLam receipt⟩
    | congAppFun _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congAppFun receipt⟩
    | congAppArg _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congAppArg receipt⟩
    | congPairFst _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPairFst receipt⟩
    | congPairSnd _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congPairSnd receipt⟩
    | congFst _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congFst receipt⟩
    | congSnd _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congSnd receipt⟩
    | congRefl _ ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.congRefl receipt⟩
  · rintro ⟨receipt⟩
    exact receipt.toSupport

/-- Renaming transports the complete structural receipt. -/
def rename
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n}
    (receipt : StructuralStepReceipt computation headEq left right)
    (rho : Ren n m) :
    StructuralStepReceipt computation headEq
      (Presentation.rename rho left) (Presentation.rename rho right) :=
  match receipt with
  | .betaPi body argument => by
      simpa only [Presentation.rename, rename_inst0] using
        (StructuralStepReceipt.betaPi
          (computation := computation) (headEq := headEq)
          (Presentation.rename (liftRen rho) body)
          (Presentation.rename rho argument))
  | .betaSigmaFst first second => .betaSigmaFst _ _
  | .betaSigmaSnd first second => .betaSigmaSnd _ _
  | .head equality => .head equality
  | .root evidence => .root (computation.rename rho evidence)
  | .congPiDom nested => .congPiDom (rename nested rho)
  | .congPiCod nested => .congPiCod (rename nested (liftRen rho))
  | .congSigmaDom nested => .congSigmaDom (rename nested rho)
  | .congSigmaCod nested => .congSigmaCod (rename nested (liftRen rho))
  | .congIdTy nested => .congIdTy (rename nested rho)
  | .congIdLeft nested => .congIdLeft (rename nested rho)
  | .congIdRight nested => .congIdRight (rename nested rho)
  | .congLam nested => .congLam (rename nested (liftRen rho))
  | .congAppFun nested => .congAppFun (rename nested rho)
  | .congAppArg nested => .congAppArg (rename nested rho)
  | .congPairFst nested => .congPairFst (rename nested rho)
  | .congPairSnd nested => .congPairSnd (rename nested rho)
  | .congFst nested => .congFst (rename nested rho)
  | .congSnd nested => .congSnd (rename nested rho)
  | .congRefl nested => .congRefl (rename nested rho)

/-- Simultaneous substitution transports the complete structural receipt. -/
def substitute
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n}
    (receipt : StructuralStepReceipt computation headEq left right)
    (substitution : Sub Head n m) :
    StructuralStepReceipt computation headEq
      (subst substitution left) (subst substitution right) :=
  match receipt with
  | .betaPi body argument => by
      simpa only [Presentation.subst, subst_inst0] using
        (StructuralStepReceipt.betaPi
          (computation := computation) (headEq := headEq)
          (subst (liftSub substitution) body)
          (subst substitution argument))
  | .betaSigmaFst first second => .betaSigmaFst _ _
  | .betaSigmaSnd first second => .betaSigmaSnd _ _
  | .head equality => .head equality
  | .root evidence => .root (computation.substitute substitution evidence)
  | .congPiDom nested => .congPiDom (substitute nested substitution)
  | .congPiCod nested =>
      .congPiCod (substitute nested (liftSub substitution))
  | .congSigmaDom nested => .congSigmaDom (substitute nested substitution)
  | .congSigmaCod nested =>
      .congSigmaCod (substitute nested (liftSub substitution))
  | .congIdTy nested => .congIdTy (substitute nested substitution)
  | .congIdLeft nested => .congIdLeft (substitute nested substitution)
  | .congIdRight nested => .congIdRight (substitute nested substitution)
  | .congLam nested => .congLam (substitute nested (liftSub substitution))
  | .congAppFun nested => .congAppFun (substitute nested substitution)
  | .congAppArg nested => .congAppArg (substitute nested substitution)
  | .congPairFst nested => .congPairFst (substitute nested substitution)
  | .congPairSnd nested => .congPairSnd (substitute nested substitution)
  | .congFst nested => .congFst (substitute nested substitution)
  | .congSnd nested => .congSnd (substitute nested substitution)
  | .congRefl nested => .congRefl (substitute nested substitution)

end StructuralStepReceipt

/-! ## Proof-relevant structural conversion -/

/-- The raw structural computation used only to retain conversion paths.
Typing authority is supplied later by formed endpoints; this object does not
infer or reconstruct a type from an untyped rewrite. -/
def rawStructuralComputation
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) (n : Nat) :
    JudgmentalComputation Unit where
  State := fun _ => Tm Head n
  Step := fun source target =>
    StructuralStepReceipt computation headEq source target

/-- A retained reflexive, symmetric, transitive structural conversion path.
Unlike `Presentation.Conv`, this type preserves every step receipt and every
intermediate raw term. -/
abbrev StructuralConversionReceipt
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) {n : Nat}
    (left right : Tm Head n) : Type (max uEvidence 0) :=
  ConversionEvidence (rawStructuralComputation computation headEq n)
    (index := ()) left right

namespace StructuralConversionReceipt

/-- Erase a retained conversion path to the established proposition-valued
conversion relation. -/
def toSupport
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n} :
    StructuralConversionReceipt computation headEq left right →
      Conv headEq left right computation.support
  | .step receipt => .rel _ _ receipt.toSupport
  | .refl state => .refl state
  | .symm conversion =>
      .symm _ _ (StructuralConversionReceipt.toSupport conversion)
  | .trans first second =>
      .trans _ _ _ (StructuralConversionReceipt.toSupport first)
        (StructuralConversionReceipt.toSupport second)

/-- Proposition-valued conversion is exactly the support quotient of retained
structural conversion.  The reverse direction yields only `Nonempty`, since
support does not select a particular declaration receipt or conversion path. -/
theorem support_iff_nonempty
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) {left right : Tm Head n} :
    Conv headEq left right computation.support ↔
      Nonempty (StructuralConversionReceipt computation headEq left right) := by
  constructor
  · intro support
    induction support with
    | rel source target step =>
        rcases
            (StructuralStepReceipt.support_iff_nonempty computation headEq).mp
              step with
          ⟨receipt⟩
        exact ⟨.step receipt⟩
    | refl state =>
        exact ⟨ConversionEvidence.refl
          (computation := rawStructuralComputation computation headEq n)
          state⟩
    | symm source target relation ih =>
        rcases ih with ⟨receipt⟩
        exact ⟨.symm receipt⟩
    | trans source middle target first second ihFirst ihSecond =>
        rcases ihFirst with ⟨firstReceipt⟩
        rcases ihSecond with ⟨secondReceipt⟩
        exact ⟨.trans firstReceipt secondReceipt⟩
  · rintro ⟨receipt⟩
    exact receipt.toSupport

/-- Lift a retained conversion through any syntax constructor that maps one
structural step to one structural step. -/
def mapCompatible
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n}
    (map : Tm Head n → Tm Head m)
    (mapStep : ∀ {source target : Tm Head n},
      StructuralStepReceipt computation headEq source target →
        StructuralStepReceipt computation headEq (map source) (map target)) :
    StructuralConversionReceipt computation headEq left right →
      StructuralConversionReceipt computation headEq (map left) (map right)
  | .step receipt => .step (mapStep receipt)
  | .refl state =>
      ConversionEvidence.refl
        (computation := rawStructuralComputation computation headEq m)
        (map state)
  | .symm conversion => .symm (mapCompatible map mapStep conversion)
  | .trans first second =>
      .trans (mapCompatible map mapStep first)
        (mapCompatible map mapStep second)

/-- Renaming transports a complete conversion path. -/
def rename
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n}
    (conversion : StructuralConversionReceipt computation headEq left right)
    (rho : Ren n m) :
    StructuralConversionReceipt computation headEq
      (Presentation.rename rho left) (Presentation.rename rho right) :=
  mapCompatible (Presentation.rename rho)
    (fun receipt => receipt.rename rho) conversion

/-- Applying one simultaneous substitution transports a complete conversion
path. -/
def substitute
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n}
    (conversion : StructuralConversionReceipt computation headEq left right)
    (substitution : Sub Head n m) :
    StructuralConversionReceipt computation headEq
      (subst substitution left) (subst substitution right) :=
  mapCompatible (subst substitution)
    (fun receipt => receipt.substitute substitution) conversion

/-- Congruence for dependent products retains both component paths in their
evaluation order. -/
def congPi
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {domain domain' : Tm Head n} {codomain codomain' : Tm Head (n + 1)}
    (domainConversion :
      StructuralConversionReceipt computation headEq domain domain')
    (codomainConversion :
      StructuralConversionReceipt computation headEq codomain codomain') :
    StructuralConversionReceipt computation headEq
      (.pi domain codomain) (.pi domain' codomain') :=
  .trans
    (mapCompatible (fun next => .pi next codomain)
      (fun receipt => .congPiDom receipt) domainConversion)
    (mapCompatible (fun next => .pi domain' next)
      (fun receipt => .congPiCod receipt) codomainConversion)

/-- Congruence for dependent sums retains both component paths. -/
def congSigma
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {domain domain' : Tm Head n} {codomain codomain' : Tm Head (n + 1)}
    (domainConversion :
      StructuralConversionReceipt computation headEq domain domain')
    (codomainConversion :
      StructuralConversionReceipt computation headEq codomain codomain') :
    StructuralConversionReceipt computation headEq
      (.sigma domain codomain) (.sigma domain' codomain') :=
  .trans
    (mapCompatible (fun next => .sigma next codomain)
      (fun receipt => .congSigmaDom receipt) domainConversion)
    (mapCompatible (fun next => .sigma domain' next)
      (fun receipt => .congSigmaCod receipt) codomainConversion)

/-- Congruence for identity types retains the carrier and both endpoint
paths separately. -/
def congId
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {type type' left left' right right' : Tm Head n}
    (typeConversion :
      StructuralConversionReceipt computation headEq type type')
    (leftConversion :
      StructuralConversionReceipt computation headEq left left')
    (rightConversion :
      StructuralConversionReceipt computation headEq right right') :
    StructuralConversionReceipt computation headEq
      (.id type left right) (.id type' left' right') :=
  .trans
    (mapCompatible (fun next => .id next left right)
      (fun receipt => .congIdTy receipt) typeConversion)
    (.trans
      (mapCompatible (fun next => .id type' next right)
        (fun receipt => .congIdLeft receipt) leftConversion)
      (mapCompatible (fun next => .id type' left' next)
        (fun receipt => .congIdRight receipt) rightConversion))

/-- Congruence for application retains function and argument paths. -/
def congApp
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {function function' argument argument' : Tm Head n}
    (functionConversion :
      StructuralConversionReceipt computation headEq function function')
    (argumentConversion :
      StructuralConversionReceipt computation headEq argument argument') :
    StructuralConversionReceipt computation headEq
      (.app function argument) (.app function' argument') :=
  .trans
    (mapCompatible (fun next => .app next argument)
      (fun receipt => .congAppFun receipt) functionConversion)
    (mapCompatible (fun next => .app function' next)
      (fun receipt => .congAppArg receipt) argumentConversion)

/-- Congruence for pairs retains both component paths. -/
def congPair
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {first first' second second' : Tm Head n}
    (firstConversion :
      StructuralConversionReceipt computation headEq first first')
    (secondConversion :
      StructuralConversionReceipt computation headEq second second') :
    StructuralConversionReceipt computation headEq
      (.pair first second) (.pair first' second') :=
  .trans
    (mapCompatible (fun next => .pair next second)
      (fun receipt => .congPairFst receipt) firstConversion)
    (mapCompatible (fun next => .pair first' next)
      (fun receipt => .congPairSnd receipt) secondConversion)

private def liftSubPointwise
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {source target : Sub Head n m}
    (pointwise : ∀ index,
      StructuralConversionReceipt computation headEq
        (source index) (target index)) :
    ∀ index,
      StructuralConversionReceipt computation headEq
        (liftSub source index) (liftSub target index) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact ConversionEvidence.refl
      (computation := rawStructuralComputation computation headEq (m + 1))
      (Tm.var 0)
  · intro prior
    exact (pointwise prior).rename wk

/-- Pointwise retained conversion of substitutions lifts through every open
term.  Each occurrence contributes its own receipt; duplicates are not
collapsed into set-level support. -/
def substitutePointwise
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop}
    {source target : Sub Head n m}
    (pointwise : ∀ index,
      StructuralConversionReceipt computation headEq
        (source index) (target index)) :
    (term : Tm Head n) →
      StructuralConversionReceipt computation headEq
        (subst source term) (subst target term)
  | .var index => pointwise index
  | .const _ => .refl _
  | .head _ => .refl _
  | .pi domain codomain =>
      congPi (substitutePointwise pointwise domain)
        (substitutePointwise (liftSubPointwise pointwise) codomain)
  | .sigma domain codomain =>
      congSigma (substitutePointwise pointwise domain)
        (substitutePointwise (liftSubPointwise pointwise) codomain)
  | .id type left right =>
      congId (substitutePointwise pointwise type)
        (substitutePointwise pointwise left)
        (substitutePointwise pointwise right)
  | .lam body =>
      mapCompatible Tm.lam (fun receipt => .congLam receipt)
        (substitutePointwise (liftSubPointwise pointwise) body)
  | .app function argument =>
      congApp (substitutePointwise pointwise function)
        (substitutePointwise pointwise argument)
  | .pair first second =>
      congPair (substitutePointwise pointwise first)
        (substitutePointwise pointwise second)
  | .fst pair =>
      mapCompatible Tm.fst (fun receipt => .congFst receipt)
        (substitutePointwise pointwise pair)
  | .snd pair =>
      mapCompatible Tm.snd (fun receipt => .congSnd receipt)
        (substitutePointwise pointwise pair)
  | .refl term =>
      mapCompatible Tm.refl (fun receipt => .congRefl receipt)
        (substitutePointwise pointwise term)

/-- When propositional conversion support is absent, no retained conversion
receipt can be fabricated. -/
@[reducible] def isEmpty_of_not_support
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {left right : Tm Head n}
    (unsupported : ¬ Conv headEq left right computation.support) :
    IsEmpty (StructuralConversionReceipt computation headEq left right) :=
  ⟨fun receipt => unsupported
    (StructuralConversionReceipt.toSupport receipt)⟩

end StructuralConversionReceipt

/-! ## Controls -/

namespace Canary

/-- A declaration root with no authored computation witnesses. -/
def emptyComputation (Head : Type) :
    ProofRelevantRootComputation Head where
  Evidence := fun _ _ => Empty
  rename := by
    intro n m rho left right evidence
    exact Empty.elim evidence
  substitute := by
    intro n m substitution left right evidence
    exact Empty.elim evidence

/-- Structural beta remains available even when the declaration-specific
root relation is empty. -/
def betaReceipt (argument : Tm Unit n) :
    StructuralStepReceipt (emptyComputation Unit) (fun _ _ => False)
      (.app (.lam (.var 0)) argument) argument := by
  simpa [inst0, subst0, Presentation.subst] using
    (StructuralStepReceipt.betaPi
      (computation := emptyComputation Unit)
      (headEq := fun _ _ => False) (.var 0) argument)

/-- A root receipt cannot be fabricated when the hosted declaration calculus
supplies no root evidence. -/
theorem no_empty_root_receipt {left right : Tm Unit n} :
    IsEmpty ((emptyComputation Unit).Evidence left right) :=
  ⟨fun evidence => Empty.elim evidence⟩

end Canary

/-! ## Axiom audit -/

#print axioms StructuralStepReceipt.support_iff_nonempty
#print axioms StructuralStepReceipt.rename
#print axioms StructuralStepReceipt.substitute
#print axioms StructuralConversionReceipt.support_iff_nonempty
#print axioms StructuralConversionReceipt.rename
#print axioms StructuralConversionReceipt.substitute
#print axioms StructuralConversionReceipt.substitutePointwise
#print axioms StructuralConversionReceipt.isEmpty_of_not_support
#print axioms Canary.betaReceipt
#print axioms Canary.no_empty_root_receipt

end ProofRelevantStructuralComputation
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
