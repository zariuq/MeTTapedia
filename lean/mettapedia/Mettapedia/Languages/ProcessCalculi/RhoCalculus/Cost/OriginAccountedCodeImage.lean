import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginSignatureRefinement

/-!
# Scoped account fold of origin-refined generated code

The graphs refine the existing decoder image at its exact authored Pattern and
runtime value. A signed node retains its literal signature and closed origin
word. The fold acts on process values at that occurrence. Input continuations
stay in their extended context, and quotation inserts the complete closed
accounted value. Literal authority is retained by the graph rather than
reconstructed from its source observation.

The target is the existing full rho binding-account model. This is a supported
source readout, not a mixed-sort model of arbitrary generated Cost contexts or
a resource transition interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginAccountedCodeImage

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open ActivationGenerated
open RuntimeSourceReification
open AccountedGeneratedReadout
open ClosedOriginAccountInterpretation

mutual
  inductive NameRefinement : Nat → Pattern → CostName LiteralAuthority → Type where
    | bvar {depth index : Nat} (bound : index < depth) :
        NameRefinement depth (.bvar index) (.bvar index)
    | baseZeroQuote {depth : Nat} : NameRefinement depth
        (.apply (costBaseConstructorName "NQuote") [.apply (costBaseConstructorName "PZero") []])
        (.quote .nil)
    | quote {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
        (code : CodeRefinement 0 source term) :
        NameRefinement depth (.apply (costWrappedConstructorName "NQuote") [source]) (.quote term)

  inductive CodeRefinement : Nat → Pattern → CostTerm LiteralAuthority → Type where
    | zero {depth : Nat} :
        CodeRefinement depth (.apply (costWrappedConstructorName "PZero") []) .nil
    | drop {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
        (parsed : NameRefinement depth source name) :
        CodeRefinement depth (.apply (costWrappedConstructorName "PDrop") [source]) (.drop name)
    | signed {depth : Nat} {core literal : Pattern} {process : CostProc LiteralAuthority}
        (signature : OriginSignatureRefinement.Image literal)
        (parsed : ProcessRefinement depth core process) :
        CodeRefinement depth (.apply costSignedConstructorName [core, literal])
          (.signed process signature.authority.val)
    | collection {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority}
        (parsed : CodeListRefinement depth sources term) :
        CodeRefinement depth (.collection .hashBag sources none) term

  inductive ProcessRefinement : Nat → Pattern → CostProc LiteralAuthority → Type where
    | zero {depth : Nat} :
        ProcessRefinement depth (.apply (costBaseConstructorName "PZero") []) .nil
    | send {depth : Nat} {channel payload : Pattern}
        {name : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
        (channelImage : NameRefinement depth channel name)
        (payloadImage : CodeRefinement depth payload term) :
        ProcessRefinement depth (.apply (costBaseConstructorName "POutput") [channel, payload])
          (.send name term)
    | recv {depth : Nat} {channel body : Pattern}
        {name : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
        (channelImage : NameRefinement depth channel name)
        (bodyImage : CodeRefinement (depth + 1) body term) :
        ProcessRefinement depth (.apply (costBaseConstructorName "PInput")
          [channel, .lambda none body]) (.recv name term)
    | pair {depth : Nat} {left right : Pattern} {first second : CostProc LiteralAuthority}
        (leftImage : ProcessRefinement depth left first)
        (rightImage : ProcessRefinement depth right second) :
        ProcessRefinement depth (.collection .hashBag [left, right] none) (.par first second)

  inductive CodeListRefinement : Nat → List Pattern → CostTerm LiteralAuthority → Type where
    | nil {depth : Nat} : CodeListRefinement depth [] .nil
    | cons {depth : Nat} {source : Pattern} {sources : List Pattern}
        {head tail : CostTerm LiteralAuthority}
        (headImage : CodeRefinement depth source head)
        (tailImage : CodeListRefinement depth sources tail) :
        CodeListRefinement depth (source :: sources) (.par head tail)
end

mutual
  theorem NameRefinement.structural_image {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameRefinement depth source name) :
      NameImage depth source name := by
    cases image with
    | bvar bound => exact .bvar bound
    | baseZeroQuote => exact .baseZeroQuote
    | quote code => exact .quote code.structural_image

  theorem CodeRefinement.structural_image {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) :
      CodeImage depth source term := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop name.structural_image
    | signed signature process =>
        exact .signed signature.authority signature.accepted process.structural_image
    | collection codes => exact .collection codes.structural_image

  theorem ProcessRefinement.structural_image {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcessRefinement depth source process) :
      ProcImage depth source process := by
    cases image with
    | zero => exact .zero
    | send name code => exact .send name.structural_image code.structural_image
    | recv name code => exact .recv name.structural_image code.structural_image
    | pair first second => exact .pair first.structural_image second.structural_image

  theorem CodeListRefinement.structural_image {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListRefinement depth sources term) :
      CodeListImage depth sources term := by
    cases image with
    | nil => exact .nil
    | cons head tail => exact .cons head.structural_image tail.structural_image
end

mutual
  def NameRefinement.erased {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority} :
      NameRefinement depth source name → Term sig (nameContext depth) Srt.nm
    | .bvar bound => .var (namePosition depth _ bound)
    | .baseZeroQuote => .op Op.quo (.cons (insertClosed depth (.op Op.nil .nil)) .nil)
    | .quote code => .op Op.quo (.cons (insertClosed depth code.erased) .nil)

  def CodeRefinement.erased {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority} :
      CodeRefinement depth source term → Term sig (nameContext depth) Srt.pr
    | .zero => .op Op.nil .nil
    | .drop name => .op Op.drp (.cons name.erased .nil)
    | .signed _ process => process.erased
    | .collection codes => codes.erased

  def ProcessRefinement.erased {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority} :
      ProcessRefinement depth source process → Term sig (nameContext depth) Srt.pr
    | .zero => .op Op.nil .nil
    | .send name code => .op Op.out (.cons name.erased (.cons code.erased .nil))
    | .recv name code => .op Op.inp (.cons name.erased (.cons (by
        simpa only [nameContext, List.replicate_succ, List.cons_append,
          List.nil_append] using code.erased) .nil))
    | .pair first second => .op Op.par (.cons first.erased (.cons second.erased .nil))

  def CodeListRefinement.erased {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority} :
      CodeListRefinement depth sources term → Term sig (nameContext depth) Srt.pr
    | .nil => .op Op.nil .nil
    | .cons head tail => .op Op.par (.cons head.erased (.cons tail.erased .nil))
end

/-- Insert the whole closed semantic value, including all occurrence-local accounts. -/
noncomputable def insertAccounted {sort : Srt} (Γ : Ctx sig)
    (value : accounted.observed.left.substitution.Carrier [] sort) :
    accounted.observed.left.substitution.Carrier Γ sort :=
  accounted.observed.left.substitution.substitute
    (fun sort (position : Var ([] : Ctx sig) sort) => nomatch position) value

noncomputable def insertAccountedClosed {sort : Srt} (depth : Nat)
    (value : accounted.observed.left.substitution.Carrier [] sort) :=
  insertAccounted (nameContext depth) value

theorem insertAccounted_substitute {Γ Δ : Ctx sig} {sort : Srt}
    (env : Environment sig accounted.observed.left.substitution.Carrier Γ Δ)
    (value : accounted.observed.left.substitution.Carrier [] sort) :
    accounted.observed.left.substitution.substitute env (insertAccounted Γ value) =
      insertAccounted Δ value := by
  unfold insertAccounted
  rw [accounted.observed.left.substitution.substitute_comp]
  congr 1
  funext sort position
  nomatch position

theorem program_insertClosed {sort : Srt} (depth : Nat) (term : Term sig [] sort) :
    program (insertClosed depth term) = insertAccountedClosed depth (program term) := by
  unfold insertClosed insertAccountedClosed insertAccounted
  rw [← bind_var_eq_rename]
  rw [program_substitute]
  congr 1
  funext sort position
  nomatch position

mutual
  noncomputable def NameRefinement.fold {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority} :
      NameRefinement depth source name → accounted.observed.left.substitution.Carrier (nameContext depth) Srt.nm
    | .bvar bound => program (.var (namePosition depth _ bound))
    | .baseZeroQuote => program (.op Op.quo (.cons (insertClosed depth (.op Op.nil .nil)) .nil))
    | .quote code => accounted.observed.left.operation Op.quo
        (.cons (insertAccountedClosed depth code.fold) .nil)

  noncomputable def CodeRefinement.fold {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority} :
      CodeRefinement depth source term → accounted.observed.left.substitution.Carrier (nameContext depth) Srt.pr
    | .zero => program (.op Op.nil .nil)
    | .drop name => accounted.observed.left.operation Op.drp (.cons name.fold .nil)
    | .signed signature process => annotate signature.word process.fold
    | .collection codes => codes.fold

  noncomputable def ProcessRefinement.fold {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority} :
      ProcessRefinement depth source process → accounted.observed.left.substitution.Carrier (nameContext depth) Srt.pr
    | .zero => program (.op Op.nil .nil)
    | .send name code => accounted.observed.left.operation Op.out (.cons name.fold (.cons code.fold .nil))
    | .recv name code => accounted.observed.left.operation Op.inp (.cons name.fold (.cons (by
        simpa only [nameContext, List.replicate_succ, List.cons_append,
          List.nil_append] using code.fold) .nil))
    | .pair first second => accounted.observed.left.operation Op.par
        (.cons first.fold (.cons second.fold .nil))

  noncomputable def CodeListRefinement.fold {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority} :
      CodeListRefinement depth sources term → accounted.observed.left.substitution.Carrier (nameContext depth) Srt.pr
    | .nil => program (.op Op.nil .nil)
    | .cons head tail => accounted.observed.left.operation Op.par (.cons head.fold (.cons tail.fold .nil))
end

mutual
  theorem NameRefinement.reification {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameRefinement depth source name) :
      RuntimeSourceReification.name? depth name = some image.erased := by
    cases image with
    | bvar bound => simp [RuntimeSourceReification.name?, bound, NameRefinement.erased]
    | baseZeroQuote => rfl
    | quote code => simp [RuntimeSourceReification.name?, code.reification, NameRefinement.erased]

  theorem CodeRefinement.reification {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) :
      RuntimeSourceReification.code? depth term = some image.erased := by
    cases image with
    | zero => rfl
    | drop name => simp [RuntimeSourceReification.code?, name.reification, CodeRefinement.erased]
    | signed signature process => exact process.reification
    | collection codes => exact codes.reification

  theorem ProcessRefinement.reification {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcessRefinement depth source process) :
      RuntimeSourceReification.process? depth process = some image.erased := by
    cases image with
    | zero => rfl
    | send name code =>
        simp [RuntimeSourceReification.process?, name.reification, code.reification, ProcessRefinement.erased]
    | recv name code =>
        simp [RuntimeSourceReification.process?, name.reification, code.reification, ProcessRefinement.erased]
    | pair first second =>
        simp [RuntimeSourceReification.process?, first.reification, second.reification, ProcessRefinement.erased]

  theorem CodeListRefinement.reification {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListRefinement depth sources term) :
      RuntimeSourceReification.code? depth term = some image.erased := by
    cases image with
    | nil => rfl
    | cons head tail =>
        simp [RuntimeSourceReification.code?, head.reification, tail.reification, CodeListRefinement.erased]
end

/-- The existing certifying readout supplies the source safety proof. -/
theorem CodeRefinement.quoteSafe {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) :
    RhoSchema.IntrinsicEncoding.intrinsicQuoteSafe depth image.erased = true :=
  code_readout_quoteSafe image.structural_image image.reification

private theorem program_operation {Γ : Ctx sig} {sort : Srt} (operation : Op sort)
    (args : Args sig (sig.arity operation) Γ) :
    program (Term.op operation args) = accounted.observed.left.operation operation
      (FamilyArgs.map program (syntaxToFamily args)) := by
  have mapped := sourceFold.raw.map_operation operation (syntaxToFamily args)
  change program (Term.op operation ((FreeBindingTerms.terms.familyToSyntax sig)
    (syntaxToFamily args))) = _ at mapped
  rw [familyToSyntax_syntaxToFamily] at mapped
  exact mapped

private theorem observe_operation {Γ : Ctx sig} {sort : Srt} (operation : Op sort)
    (args : FamilyArgs sig accounted.observed.left.substitution.Carrier (sig.arity operation) Γ) :
    accounted.observed.hom.raw.map (accounted.observed.left.operation operation args) =
      source.operation operation (FamilyArgs.map accounted.observed.hom.raw.map args) :=
  accounted.observed.hom.raw.map_operation operation args

private theorem insert_observation {sort : Srt} (depth : Nat)
    (value : accounted.observed.left.substitution.Carrier [] sort) (term : Term sig [] sort)
    (agree : accounted.observed.hom.raw.map value =
      accounted.observed.hom.raw.map (program term)) :
    accounted.observed.hom.raw.map (insertAccountedClosed depth value) =
      accounted.observed.hom.raw.map (program (insertClosed depth term)) := by
  rw [program_insertClosed]
  unfold insertAccountedClosed insertAccounted
  rw [accounted.observed.hom.map_substitute, accounted.observed.hom.map_substitute, agree]

mutual
  theorem NameRefinement.observation {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameRefinement depth source name) :
      accounted.observed.hom.raw.map image.fold =
        accounted.observed.hom.raw.map (program image.erased) := by
    cases image with
    | bvar bound => rfl
    | baseZeroQuote => rfl
    | quote code =>
        have child := insert_observation depth code.fold code.erased code.observation
        simp only [NameRefinement.fold, NameRefinement.erased, program_operation,
          observe_operation, FamilyArgs.map, syntaxToFamily, child]
        rfl

  theorem CodeRefinement.observation {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) :
      accounted.observed.hom.raw.map image.fold =
        accounted.observed.hom.raw.map (program image.erased) := by
    cases image with
    | zero => rfl
    | drop name =>
        simp only [CodeRefinement.fold, CodeRefinement.erased, program_operation,
          observe_operation, FamilyArgs.map, syntaxToFamily, name.observation]
        rfl
    | signed signature process =>
        exact (annotate_observation signature.word process.fold).trans process.observation
    | collection codes => exact codes.observation

  theorem ProcessRefinement.observation {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcessRefinement depth source process) :
      accounted.observed.hom.raw.map image.fold =
        accounted.observed.hom.raw.map (program image.erased) := by
    cases image with
    | zero => rfl
    | send name code =>
        simp only [ProcessRefinement.fold, ProcessRefinement.erased, program_operation,
          observe_operation, FamilyArgs.map, syntaxToFamily, name.observation, code.observation]
        rfl
    | recv name code =>
        simp only [ProcessRefinement.fold, ProcessRefinement.erased, program_operation,
          observe_operation, FamilyArgs.map, syntaxToFamily, id_eq, name.observation, code.observation]
        rfl
    | pair first second =>
        simp only [ProcessRefinement.fold, ProcessRefinement.erased, program_operation,
          observe_operation, FamilyArgs.map, syntaxToFamily, first.observation, second.observation]
        rfl

  theorem CodeListRefinement.observation {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListRefinement depth sources term) :
      accounted.observed.hom.raw.map image.fold =
        accounted.observed.hom.raw.map (program image.erased) := by
    cases image with
    | nil => rfl
    | cons head tail =>
        simp only [CodeListRefinement.fold, CodeListRefinement.erased, program_operation,
          observe_operation, FamilyArgs.map, syntaxToFamily, head.observation, tail.observation]
        rfl
end

theorem CodeRefinement.canonical_observation {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) :
    RhoSchema.IntrinsicEncoding.encodeEquationClass (accounted.observed.hom.raw.map image.fold) =
      Canonical.canonicalize (eraseGenerated source) := by
  rw [image.observation, program_observation,
    RhoSchema.IntrinsicEncoding.encodeEquationClass_mk]
  exact code_readout_canonical image.structural_image image.reification

/-- The input binder lifts the complete marked environment by the clone's own operation. -/
noncomputable def inputEnvironment {depth : Nat} {Γ : Ctx sig}
    (env : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ) :
    Environment sig accounted.observed.left.substitution.Carrier (nameContext (depth + 1))
      (Srt.nm :: Γ) := by
  simpa only [nameContext, List.replicate_succ, List.cons_append, List.nil_append] using
    accounted.observed.left.substitution.liftEnvironment env [Srt.nm]

mutual
  noncomputable def NameRefinement.interpret {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} {Γ : Ctx sig} :
      NameRefinement depth source name →
      Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ →
      accounted.observed.left.substitution.Carrier Γ Srt.nm
    | .bvar bound, env => env Srt.nm (namePosition depth _ bound)
    | .baseZeroQuote, _env => accounted.observed.left.operation Op.quo
        (.cons (insertAccounted Γ (program (.op Op.nil .nil))) .nil)
    | .quote code, _env => accounted.observed.left.operation Op.quo
        (.cons (insertAccounted Γ code.fold) .nil)

  noncomputable def CodeRefinement.interpret {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} {Γ : Ctx sig} :
      CodeRefinement depth source term →
      Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ →
      accounted.observed.left.substitution.Carrier Γ Srt.pr
    | .zero, _env => program (.op Op.nil .nil)
    | .drop name, env => accounted.observed.left.operation Op.drp (.cons (name.interpret env) .nil)
    | .signed signature process, env => annotate signature.word (process.interpret env)
    | .collection codes, env => codes.interpret env

  noncomputable def ProcessRefinement.interpret {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} {Γ : Ctx sig} :
      ProcessRefinement depth source process →
      Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ →
      accounted.observed.left.substitution.Carrier Γ Srt.pr
    | .zero, _env => program (.op Op.nil .nil)
    | .send name code, env => accounted.observed.left.operation Op.out
        (.cons (name.interpret env) (.cons (code.interpret env) .nil))
    | .recv name code, env => accounted.observed.left.operation Op.inp
        (.cons (name.interpret env) (.cons (code.interpret (inputEnvironment env)) .nil))
    | .pair first second, env => accounted.observed.left.operation Op.par
        (.cons (first.interpret env) (.cons (second.interpret env) .nil))

  noncomputable def CodeListRefinement.interpret {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} {Γ : Ctx sig} :
      CodeListRefinement depth sources term →
      Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ →
      accounted.observed.left.substitution.Carrier Γ Srt.pr
    | .nil, _env => program (.op Op.nil .nil)
    | .cons head tail, env => accounted.observed.left.operation Op.par
        (.cons (head.interpret env) (.cons (tail.interpret env) .nil))
end

private theorem program_variable {Γ : Ctx sig} {sort : Srt} (position : Var Γ sort) :
    program (.var position) = accounted.observed.left.substitution.injectVar position :=
  sourceFold.raw.map_variable position

mutual
  theorem NameRefinement.interpret_substitute :
      ∀ {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
        (image : NameRefinement depth source name) {Γ : Ctx sig}
        (env : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ),
        accounted.observed.left.substitution.substitute env image.fold = image.interpret env
    | depth, _, _, .bvar bound, Γ, env => by
        simp only [NameRefinement.fold, NameRefinement.interpret, program_variable,
          accounted.observed.left.substitution.substitute_var]
    | depth, _, _, .baseZeroQuote, Γ, env => by
        simp only [NameRefinement.fold, NameRefinement.interpret, program_operation,
          syntaxToFamily, FamilyArgs.map, program_insertClosed,
          accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs,
          BindingSubstitutionAlgebra.Algebra.liftEnvironment, insertAccountedClosed]
        congr 2
        exact insertAccounted_substitute env (accounted.observed.left.operation Op.nil .nil)
    | depth, _, _, .quote code, Γ, env => by
        simp only [NameRefinement.fold, NameRefinement.interpret,
          accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs,
          BindingSubstitutionAlgebra.Algebra.liftEnvironment, insertAccountedClosed]
        congr 2
        exact insertAccounted_substitute env code.fold

  theorem CodeRefinement.interpret_substitute :
      ∀ {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
        (image : CodeRefinement depth source term) {Γ : Ctx sig}
        (env : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ),
        accounted.observed.left.substitution.substitute env image.fold = image.interpret env
    | depth, _, _, .zero, Γ, env => by
        simp only [CodeRefinement.fold, CodeRefinement.interpret, program_operation,
          syntaxToFamily, FamilyArgs.map, accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs]
    | depth, _, _, .drop name, Γ, env => by
        simp only [CodeRefinement.fold, CodeRefinement.interpret,
          accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs,
          BindingSubstitutionAlgebra.Algebra.liftEnvironment, name.interpret_substitute]
    | depth, _, _, .signed signature process, Γ, env => by
        rw [CodeRefinement.fold, annotate_substitute, process.interpret_substitute]
        rfl
    | depth, _, _, .collection codes, Γ, env => by
        exact codes.interpret_substitute env

  theorem ProcessRefinement.interpret_substitute :
      ∀ {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority}
        (image : ProcessRefinement depth source process) {Γ : Ctx sig}
        (env : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ),
        accounted.observed.left.substitution.substitute env image.fold = image.interpret env
    | depth, _, _, .zero, Γ, env => by
        simp only [ProcessRefinement.fold, ProcessRefinement.interpret, program_operation,
          syntaxToFamily, FamilyArgs.map, accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs]
    | depth, _, _, .send name code, Γ, env => by
        simp only [ProcessRefinement.fold, ProcessRefinement.interpret,
          accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs,
          BindingSubstitutionAlgebra.Algebra.liftEnvironment,
          name.interpret_substitute, code.interpret_substitute]
    | depth, _, _, .recv name code, Γ, env => by
        have body := code.interpret_substitute (inputEnvironment env)
        simp only [ProcessRefinement.fold, ProcessRefinement.interpret,
          accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs,
          name.interpret_substitute, id_eq]
        simp only [BindingSubstitutionAlgebra.Algebra.liftEnvironment] at body ⊢
        congr 3
    | depth, _, _, .pair first second, Γ, env => by
        simp only [ProcessRefinement.fold, ProcessRefinement.interpret,
          accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs,
          BindingSubstitutionAlgebra.Algebra.liftEnvironment,
          first.interpret_substitute, second.interpret_substitute]

  theorem CodeListRefinement.interpret_substitute :
      ∀ {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority}
        (image : CodeListRefinement depth sources term) {Γ : Ctx sig}
        (env : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ),
        accounted.observed.left.substitution.substitute env image.fold = image.interpret env
    | depth, _, _, .nil, Γ, env => by
        simp only [CodeListRefinement.fold, CodeListRefinement.interpret, program_operation,
          syntaxToFamily, FamilyArgs.map, accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs]
    | depth, _, _, .cons head tail, Γ, env => by
        simp only [CodeListRefinement.fold, CodeListRefinement.interpret,
          accounted.observed.left.operation_substitute,
          BindingSubstitutionAlgebra.Algebra.substituteArgs,
          BindingSubstitutionAlgebra.Algebra.liftEnvironment,
          head.interpret_substitute, tail.interpret_substitute]

end

theorem CodeRefinement.interpret_identity {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) :
    image.interpret (fun _ position => accounted.observed.left.substitution.injectVar position) =
      image.fold := by
  rw [← image.interpret_substitute]
  exact accounted.observed.left.substitution.substitute_identity _

/-- Composition substitutes complete target values, including their inner accounts. -/
theorem CodeRefinement.interpret_comp {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term)
    {Γ Δ : Ctx sig}
    (first : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ)
    (second : Environment sig accounted.observed.left.substitution.Carrier Γ Δ) :
    accounted.observed.left.substitution.substitute second (image.interpret first) =
      image.interpret (fun sort position =>
        accounted.observed.left.substitution.substitute second (first sort position)) := by
  rw [← image.interpret_substitute, accounted.observed.left.substitution.substitute_comp,
    image.interpret_substitute]

theorem ProcessRefinement.interpret_comp {depth : Nat} {source : Pattern}
    {process : CostProc LiteralAuthority} (image : ProcessRefinement depth source process)
    {Γ Δ : Ctx sig}
    (first : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ)
    (second : Environment sig accounted.observed.left.substitution.Carrier Γ Δ) :
    accounted.observed.left.substitution.substitute second (image.interpret first) =
      image.interpret (fun sort position =>
        accounted.observed.left.substitution.substitute second (first sort position)) := by
  rw [← image.interpret_substitute, accounted.observed.left.substitution.substitute_comp,
    image.interpret_substitute]

theorem CodeRefinement.interpret_observation {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) {Γ : Ctx sig}
    (env : Environment sig accounted.observed.left.substitution.Carrier (nameContext depth) Γ) :
    accounted.observed.hom.raw.map (image.interpret env) =
      AccountedGeneratedReadout.source.substitution.substitute
        (fun sort position => accounted.observed.hom.raw.map (env sort position))
        (Quotient.mk _ image.erased) := by
  rw [← image.interpret_substitute, accounted.observed.hom.map_substitute,
    image.observation, program_observation]

/-- Parser success is supplied by the existing certifying decoder image. -/
theorem CodeRefinement.decoded {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeRefinement depth source term) :
    ∃ fuel, (ActivationGenerated.code? fuel depth source).map Subtype.val = some term :=
  code_parser_iff_image.mpr image.structural_image

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.OriginAccountedCodeImage
