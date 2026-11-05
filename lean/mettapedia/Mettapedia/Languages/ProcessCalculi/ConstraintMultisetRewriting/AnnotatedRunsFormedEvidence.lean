import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCertificate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLogicEvidence

/-!
# Formed evidence: source judgments and checked conversions as an evidence family over runs

A piece of **formed evidence** at a formed context relates a formed source program to a target
term. It retains

* the source judgment: a formed type and a term typed at it (`TotalTerm`);
* the target judgment: a formed type and a term typed at it, with the target's code;
* two finite conversion certificates accepted by the Flower's structural checker: one between the
  two displayed types, one between the two terms.

Formation of both endpoints is retained; the rules package and the root decoder, the theory
assumptions, are indices of the type. The certificates are data: two pieces of evidence for one
pair of endpoints may differ, for instance in their number of selected steps (`stepCount`).

## What follows from it

* The source is retyped at the target's formed type by the Flower's own checked conversion,
  `Judgment.convertChecked` (`FormedEvidence.retyped`).
* The source and the target lie in one class of the Flower's quotient of total terms, `QTerm`
  (`FormedEvidence.class_eq`): formation and the semantic value descend through the quotient.

## Two axes

* **Context substitution** acts on formed evidence (`FormedEvidence.reindex`). The finite
  certificates are transformed by the checker's own code substitution, and they stay accepted at
  the substituted endpoints (`Code.check_substitute`). The action is strictly functorial on the
  evidence's data (`reindex_id_data`, `reindex_comp_data`), and it keeps the number of selected
  steps (`stepCount_reindex`).
* **Execution** extends histories. Over any category of runs with a readout of histories, the
  formed evidence of the readout is a family of R28's evidence fibration (`formedFiber`).
  Substitution acts on that family fibrewise (`formedFiberReindex`).

The square relating the two axes is about runs, not about this family: substituting in the
context and then running agrees, at the checked observation, with running and then substituting
(`AnnotatedRunsFormedSquare`).

Formed contexts are the outer index; runs and their evidence live inside them.

## Truncation

The propositional truncation of the formed family at a history holds exactly when the history's
readout is a formed term in the source's `QTerm` class (`trunc_formedFiber`). The certificates,
and their costs, are what the truncation forgets: composition of evidence adds step counts
(`stepCount_trans`), so equal classes do not imply equal costs.

The root-code substitution is an input of the calculus (`RootAction`): an actual substitution of
a decoder's root codes. Its naturality and functor laws are fields of the structure; every
instance in the consumers proves them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.FormationSensitiveContextual
open StructuralConversionCode
open AnnotatedRuns (EvFiber trunc Separates)

variable {Head : Type} [DecidableEq Head] {R : Rules Head} [DecidableRel R.headEq]

/-! ## Formed evidence -/

section Evidence

variable (decoder : RootDecoder R.computation)

/-- **Formed evidence** that a formed source program converts to a target term: the target's
formed type and typing, and checked certificates for both conversions. -/
structure FormedEvidence (context : Context R) (source : TotalTerm context)
    (target : Tm Head context.arity) where
  targetType : TypeOver context
  targetTerm : Term context targetType
  target_code : targetTerm.code = target
  typeCertificate : Certificate R.headEq decoder.decode source.1.code targetType.code
  termCertificate : Certificate R.headEq decoder.decode source.2.code targetTerm.code

/-- The data of formed evidence: the target's type code and level, and the two finite codes.
The judgments are propositions. -/
abbrev EvidenceData (n : Nat) :=
  (Tm Head n × Head) × Code Head decoder.Code n × Code Head decoder.Code n

variable {decoder}

namespace FormedEvidence

variable {context : Context R} {source : TotalTerm context} {target : Tm Head context.arity}

/-- The source term converts to the target term. -/
theorem termConversion (e : FormedEvidence decoder context source target) :
    Conv R.headEq source.2.code target R.computation := by
  rw [← e.target_code]
  exact Code.check_sound decoder e.termCertificate.checked

/-- The source's displayed type converts to the target's formed type. -/
theorem typeConversion (e : FormedEvidence decoder context source target) :
    Conv R.headEq source.1.code e.targetType.code R.computation :=
  Code.check_sound decoder e.typeCertificate.checked

/-- **The source program retyped** at the target's formed type, by the Flower's checked
conversion: source admission and target formation are both used. -/
theorem retyped (e : FormedEvidence decoder context source target) :
    FormationSensitive.Judgment R context.raw source.2.code e.targetType.code :=
  FormationSensitive.Judgment.convertChecked decoder source.2.judgment e.targetType.formed
    e.targetType.universeWitness e.typeCertificate.checked

/-- The target's own judgment at its formed type. -/
theorem targetJudgment (e : FormedEvidence decoder context source target) :
    FormationSensitive.Judgment R context.raw target e.targetType.code := by
  have judgment := e.targetTerm.judgment
  rw [e.target_code] at judgment
  exact judgment

/-- **The semantic value descends**: source and target are one class of `QTerm`. -/
theorem class_eq (e : FormedEvidence decoder context source target) :
    QTerm.mk source.2 = QTerm.mk e.targetTerm :=
  (QTerm.mk_eq_iff source.2 e.targetTerm).mpr
    ⟨e.typeConversion, Code.check_sound decoder e.termCertificate.checked⟩

/-- The data of a piece of formed evidence. -/
def data (e : FormedEvidence decoder context source target) : EvidenceData decoder context.arity :=
  ((e.targetType.code, e.targetType.level), e.typeCertificate.code, e.termCertificate.code)

/-- Formed evidence is determined by its data. -/
theorem ext {e e' : FormedEvidence decoder context source target} (same : e.data = e'.data) :
    e = e' := by
  obtain ⟨type, term, code, typeCertificate, termCertificate⟩ := e
  obtain ⟨type', term', code', typeCertificate', termCertificate'⟩ := e'
  simp only [data, Prod.mk.injEq] at same
  obtain ⟨⟨sameType, sameLevel⟩, sameTypeCode, sameTermCode⟩ := same
  obtain rfl : type = type' := TypeOver.ext sameType sameLevel
  obtain rfl : term = term' := Term.ext (code.trans code'.symm)
  obtain ⟨typeCode, typeChecked⟩ := typeCertificate
  obtain ⟨typeCode', typeChecked'⟩ := typeCertificate'
  obtain ⟨termCode, termChecked⟩ := termCertificate
  obtain ⟨termCode', termChecked'⟩ := termCertificate'
  simp only at sameTypeCode sameTermCode
  subst sameTypeCode
  subst sameTermCode
  rfl

/-- **A cost of evidence**: the number of selected steps of its two certificates. -/
def stepCount (e : FormedEvidence decoder context source target) : Nat :=
  e.typeCertificate.code.stepCount + e.termCertificate.code.stepCount

/-! ### Identity and composition of evidence -/

/-- The identity evidence of a source program. -/
def refl (source : TotalTerm context) : FormedEvidence decoder context source source.2.code where
  targetType := source.1
  targetTerm := source.2
  target_code := rfl
  typeCertificate := Certificate.refl _
  termCertificate := Certificate.refl _

/-- Composition of evidence: the target of the first is the source of the second. -/
def trans (e : FormedEvidence decoder context source target) {next : Tm Head context.arity}
    (e' : FormedEvidence decoder context ⟨e.targetType, e.targetTerm⟩ next) :
    FormedEvidence decoder context source next where
  targetType := e'.targetType
  targetTerm := e'.targetTerm
  target_code := e'.target_code
  typeCertificate := e.typeCertificate.trans e'.typeCertificate
  termCertificate := e.termCertificate.trans e'.termCertificate

theorem stepCount_refl (source : TotalTerm context) :
    (refl (decoder := decoder) source).stepCount = 0 := rfl

/-- **Costs add along composition**, while the class does not change. -/
theorem stepCount_trans (e : FormedEvidence decoder context source target)
    {next : Tm Head context.arity}
    (e' : FormedEvidence decoder context ⟨e.targetType, e.targetTerm⟩ next) :
    (e.trans e').stepCount = e.stepCount + e'.stepCount := by
  simp only [stepCount, trans, Certificate.trans, Code.stepCount]
  omega

theorem class_trans (e : FormedEvidence decoder context source target)
    {next : Tm Head context.arity}
    (e' : FormedEvidence decoder context ⟨e.targetType, e.targetTerm⟩ next) :
    QTerm.mk source.2 = QTerm.mk (e.trans e').targetTerm :=
  (e.class_eq).trans e'.class_eq

end FormedEvidence

end Evidence

/-! ## Context substitution -/

section Substitution

/-- **An actual substitution action on a decoder's root codes**, with its naturality and functor
laws. This is an input of the calculus: each consumer supplies one with proofs. -/
structure RootAction (decoder : RootDecoder R.computation) where
  substitute : {n m : Nat} → Sub Head n m → decoder.Code n → decoder.Code m
  natural : ∀ {n m : Nat} (σ : Sub Head n m) (code : decoder.Code n),
    decoder.decode (substitute σ code) = mapEndpoints (subst σ) (decoder.decode code)
  substitute_ids : ∀ {n : Nat} (code : decoder.Code n), substitute ids code = code
  substitute_comp : ∀ {n m k : Nat} (σ : Sub Head n m) (τ : Sub Head m k) (code : decoder.Code n),
    substitute τ (substitute σ code) = substitute (subComp τ σ) code

variable {decoder : RootDecoder R.computation} (action : RootAction decoder)

/-- A certificate transformed by the checker's code substitution; it stays accepted at the
substituted endpoints. -/
def reindexCertificate {n m : Nat} {left right : Tm Head n}
    (certificate : Certificate R.headEq decoder.decode left right) (σ : Sub Head n m) :
    Certificate R.headEq decoder.decode (subst σ left) (subst σ right) :=
  ⟨certificate.code.substitute action.substitute σ,
    Code.check_substitute action.substitute R.headEq decoder.decode action.natural σ
      certificate.code certificate.checked⟩

namespace FormedEvidence

variable {context : Context R} {source : TotalTerm context} {target : Tm Head context.arity}

/-- **Context substitution of formed evidence**: types and terms by the formed substitution,
certificates by the code substitution. -/
def reindex (e : FormedEvidence decoder context source target) {other : Context R}
    (morphism : other ⟶ context) :
    FormedEvidence decoder other (TotalTerm.reindex source morphism)
      (subst morphism.substitution target) where
  targetType := e.targetType.reindex morphism
  targetTerm := e.targetTerm.reindex morphism
  target_code := congrArg (subst morphism.substitution) e.target_code
  typeCertificate := reindexCertificate action e.typeCertificate morphism.substitution
  termCertificate := reindexCertificate action e.termCertificate morphism.substitution

/-- **Identity**: substitution along the identity leaves the evidence's data unchanged. -/
theorem reindex_id_data (e : FormedEvidence decoder context source target) :
    (e.reindex action (𝟙 context)).data = e.data := by
  simp only [data, reindex, reindexCertificate, TypeOver.reindex]
  change ((subst ids e.targetType.code, e.targetType.level),
      e.typeCertificate.code.substitute action.substitute ids,
      e.termCertificate.code.substitute action.substitute ids) = _
  rw [subst_ids, Code.substitute_ids action.substitute action.substitute_ids,
    Code.substitute_ids action.substitute action.substitute_ids]

/-- **Composition**: substitution along a composite is the composite of substitutions. -/
theorem reindex_comp_data (e : FormedEvidence decoder context source target)
    {first middle : Context R} (earlier : first ⟶ middle) (later : middle ⟶ context) :
    (e.reindex action (earlier ≫ later)).data =
      ((e.reindex action later).reindex action earlier).data := by
  simp only [data, reindex, reindexCertificate, TypeOver.reindex]
  change ((subst (subComp earlier.substitution later.substitution) e.targetType.code,
      e.targetType.level),
      e.typeCertificate.code.substitute action.substitute
        (subComp earlier.substitution later.substitution),
      e.termCertificate.code.substitute action.substitute
        (subComp earlier.substitution later.substitution)) =
    ((subst earlier.substitution (subst later.substitution e.targetType.code),
      e.targetType.level),
      (e.typeCertificate.code.substitute action.substitute later.substitution).substitute
        action.substitute earlier.substitution,
      (e.termCertificate.code.substitute action.substitute later.substitution).substitute
        action.substitute earlier.substitution)
  rw [subst_subComp, Code.substitute_comp action.substitute action.substitute_comp,
    Code.substitute_comp action.substitute action.substitute_comp]

/-- Substitution keeps the number of selected steps, whatever the substituted payloads. -/
theorem stepCount_reindex (e : FormedEvidence decoder context source target) {other : Context R}
    (morphism : other ⟶ context) :
    (e.reindex action morphism).stepCount = e.stepCount := by
  simp only [stepCount, reindex, reindexCertificate, Code.substitute_stepCount]

end FormedEvidence

end Substitution

/-! ## The formed family over histories -/

section Fibre

variable {B : Type} [Category.{0} B] (root : B)
variable (decoder : RootDecoder R.computation) (context : Context R) (source : TotalTerm context)

/-- **The formed-evidence family over histories**: at a history, its readout and formed evidence
for it. A history without a readout, such as an unfinished computation, has no evidence. -/
def formedFiber (read : ∀ {x : B}, (root ⟶ x) → Option (Tm Head context.arity)) (x : B) :
    EvFiber.{0} root x :=
  fun h => Σ target : {target // read h = some target}, FormedEvidence decoder context source target.1

variable {root decoder context source}

/-- **The truncation of formed evidence is the semantic class**: a history has formed evidence
exactly when its readout is a formed term in the source's `QTerm` class. -/
theorem trunc_formedFiber (read : ∀ {x : B}, (root ⟶ x) → Option (Tm Head context.arity))
    {x : B} (h : root ⟶ x) :
    h ∈ trunc (formedFiber root decoder context source read x) ↔
      ∃ target, read h = some target ∧ ∃ (type : TypeOver context) (term : Term context type),
        term.code = target ∧ QTerm.mk source.2 = QTerm.mk term := by
  constructor
  · rintro ⟨⟨⟨target, readout⟩, e⟩⟩
    exact ⟨target, readout, e.targetType, e.targetTerm, e.target_code, e.class_eq⟩
  · rintro ⟨target, readout, type, term, code, same⟩
    obtain ⟨typeConverted, termConverted⟩ := (QTerm.mk_eq_iff source.2 term).mp same
    obtain ⟨typeCode, typeChecked⟩ := (Code.conversion_iff_checked decoder).mp typeConverted
    obtain ⟨termCode, termChecked⟩ := (Code.conversion_iff_checked decoder).mp termConverted
    exact ⟨⟨⟨target, readout⟩, ⟨type, term, code, ⟨typeCode, typeChecked⟩, ⟨termCode, termChecked⟩⟩⟩⟩

/-- **Two pieces of formed evidence for one history with different costs** separate the family:
the cost is a reading of evidence, not of the history. -/
theorem formedFiber_separates (read : ∀ {x : B}, (root ⟶ x) → Option (Tm Head context.arity))
    {x : B} {h : root ⟶ x} (e e' : formedFiber root decoder context source read x h)
    (differ : e.2.stepCount ≠ e'.2.stepCount) :
    Separates (E := formedFiber root decoder context source read x)
      (fun _ evidence => evidence.2.stepCount) :=
  ⟨h, e, e', differ⟩

variable (action : RootAction decoder)

/-- **Context substitution as a fibrewise map** of formed families over histories. -/
def formedFiberReindex (read : ∀ {x : B}, (root ⟶ x) → Option (Tm Head context.arity))
    {other : Context R} (morphism : other ⟶ context) (x : B) :
    formedFiber root decoder context source read x ⟶
      formedFiber root decoder other (TotalTerm.reindex source morphism)
        (fun h => (read h).map (subst morphism.substitution)) x :=
  fun _ => TypeCat.ofHom fun evidence =>
    ⟨⟨subst morphism.substitution evidence.1.1,
      congrArg (Option.map (subst morphism.substitution)) evidence.1.2⟩,
      evidence.2.reindex action morphism⟩

end Fibre

#print axioms FormedEvidence.termConversion
#print axioms FormedEvidence.retyped
#print axioms FormedEvidence.targetJudgment
#print axioms FormedEvidence.class_eq
#print axioms FormedEvidence.ext
#print axioms FormedEvidence.stepCount_trans
#print axioms FormedEvidence.class_trans
#print axioms FormedEvidence.reindex_id_data
#print axioms FormedEvidence.reindex_comp_data
#print axioms FormedEvidence.stepCount_reindex
#print axioms trunc_formedFiber
#print axioms formedFiber_separates
#print axioms formedFiberReindex

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
