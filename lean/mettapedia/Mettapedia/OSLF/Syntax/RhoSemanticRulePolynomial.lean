import Mettapedia.OSLF.Syntax.RhoSourceEquationModel
import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Rho operational constructors over semantic binding clones

The intrinsic binary presentation of the Chapter 7 reflective calculus has
COMM, Drop, and recursive parallel congruence. Their endpoints are meaningful
in any model of the binding signature: communication substitutes a quoted
payload into a process in the name-extended context. Rule shapes retain that
context and the recursive premise address. The canonical hash-bag language
still needs a separate comparison to this intrinsic presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.TypeTheory

universe u v

variable {A : BindingCloneAlgebra.Algebra.{u} sig}
variable {B : BindingCloneAlgebra.Algebra.{v} sig}

abbrev Name (A : BindingCloneAlgebra.Algebra.{u} sig)
    (Γ : Ctx sig) := A.substitution.Carrier Γ .nm

abbrev Proc (A : BindingCloneAlgebra.Algebra.{u} sig)
    (Γ : Ctx sig) := A.substitution.Carrier Γ .pr

def zero (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} : Proc A Γ :=
  A.operation .nil .nil

def par (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (left right : Proc A Γ) : Proc A Γ :=
  A.operation .par (.cons left (.cons right .nil))

def output (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (channel : Name A Γ) (payload : Proc A Γ) : Proc A Γ :=
  A.operation .out (.cons channel (.cons payload .nil))

def input (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (channel : Name A Γ)
    (continuation : Proc A (.nm :: Γ)) : Proc A Γ :=
  A.operation .inp (.cons channel (.cons continuation .nil))

def quote (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (process : Proc A Γ) : Name A Γ :=
  A.operation .quo (.cons process .nil)

def drop (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (name : Name A Γ) : Proc A Γ :=
  A.operation .drp (.cons name .nil)

/-- Replace the newest name variable while leaving every older variable
projected from the ambient context. -/
def newestNameEnvironment (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (name : Name A Γ) :
    Environment sig A.substitution.Carrier (.nm :: Γ) Γ
  | _, .zero => name
  | _, .succ old => A.substitution.injectVar old

/-- Semantic application of the continuation metavariable to one name.
Its domain is the name-extended context, not an unscoped function type. -/
def instantiateName (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (continuation : Proc A (.nm :: Γ))
    (name : Name A Γ) : Proc A Γ :=
  A.substitution.substitute (newestNameEnvironment A name) continuation

def commSource (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (channel : Name A Γ) (payload : Proc A Γ)
    (continuation : Proc A (.nm :: Γ)) : Proc A Γ :=
  par A (output A channel payload) (input A channel continuation)

def commTarget (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (payload : Proc A Γ)
    (continuation : Proc A (.nm :: Γ)) : Proc A Γ :=
  instantiateName A continuation (quote A payload)

/-- The open communication source in the free clone is exactly the
quote-safe intrinsic source, with one ambient name. -/
theorem terms_openCommSource :
    commSource (BindingCloneAlgebra.terms sig)
      IntrinsicEncoding.openCommAmbientName
      IntrinsicEncoding.openCommPayload
      IntrinsicEncoding.openCommContinuation =
        IntrinsicEncoding.openCommSource := by
  rfl

/-- The corresponding general rule target is the intrinsically well-scoped
term that cannot be read as a literal sealed quote in the authored syntax. -/
theorem terms_openCommTarget :
    commTarget (BindingCloneAlgebra.terms sig)
      IntrinsicEncoding.openCommPayload
      IntrinsicEncoding.openCommContinuation =
        IntrinsicEncoding.openCommTarget := by
  rfl

/-- Admission of a general COMM source in an intrinsic context is exactly
admission of its channel, payload, and binder-extended continuation. The
payload need not be closed to the ambient context at this stage. -/
theorem terms_commSource_quoteSafe {Γ : Ctx sig}
    (channel : Term sig Γ .nm) (payload : Term sig Γ .pr)
    (continuation : Term sig (.nm :: Γ) .pr) :
    IntrinsicEncoding.intrinsicQuoteSafe Γ.length
      (commSource (BindingCloneAlgebra.terms sig)
        channel payload continuation) = true ↔
      IntrinsicEncoding.intrinsicQuoteSafe Γ.length channel = true ∧
      IntrinsicEncoding.intrinsicQuoteSafe Γ.length payload = true ∧
      IntrinsicEncoding.intrinsicQuoteSafe (Γ.length + 1) continuation =
        true := by
  change IntrinsicEncoding.intrinsicQuoteSafe Γ.length
      (.op Op.par
        (.cons (.op Op.out (.cons channel (.cons payload .nil)))
          (.cons (.op Op.inp
            (.cons channel (.cons continuation .nil))) .nil))) = true ↔ _
  simp [IntrinsicEncoding.intrinsicQuoteSafe,
    IntrinsicEncoding.intrinsicQuoteSafeArgs,
    and_assoc, and_left_comm]

/-- Thus the actual free operational rule, not merely an unrelated raw term,
exhibits the source-admission boundary at open contexts. -/
theorem terms_comm_not_closed_on_literal_source :
    IntrinsicEncoding.intrinsicQuoteSafe 1
      (commSource (BindingCloneAlgebra.terms sig)
        IntrinsicEncoding.openCommAmbientName
        IntrinsicEncoding.openCommPayload
        IntrinsicEncoding.openCommContinuation) = true ∧
    IntrinsicEncoding.intrinsicQuoteSafe 1
      (commTarget (BindingCloneAlgebra.terms sig)
        IntrinsicEncoding.openCommPayload
        IntrinsicEncoding.openCommContinuation) = false := by
  rw [terms_openCommSource, terms_openCommTarget]
  exact IntrinsicEncoding.openComm_not_closed_on_literal_source

variable (h : FreeBindingClone.Hom A B)

theorem map_par {Γ : Ctx sig} (left right : Proc A Γ) :
    h.raw.map (par A left right) =
      par B (h.raw.map left) (h.raw.map right) :=
  h.raw.map_operation .par (.cons left (.cons right .nil))

theorem map_output {Γ : Ctx sig} (channel : Name A Γ)
    (payload : Proc A Γ) :
    h.raw.map (output A channel payload) =
      output B (h.raw.map channel) (h.raw.map payload) :=
  h.raw.map_operation .out (.cons channel (.cons payload .nil))

theorem map_input {Γ : Ctx sig} (channel : Name A Γ)
    (continuation : Proc A (.nm :: Γ)) :
    h.raw.map (input A channel continuation) =
      input B (h.raw.map channel) (h.raw.map continuation) :=
  h.raw.map_operation .inp (.cons channel (.cons continuation .nil))

theorem map_quote {Γ : Ctx sig} (process : Proc A Γ) :
    h.raw.map (quote A process) = quote B (h.raw.map process) :=
  h.raw.map_operation .quo (.cons process .nil)

theorem map_drop {Γ : Ctx sig} (name : Name A Γ) :
    h.raw.map (drop A name) = drop B (h.raw.map name) :=
  h.raw.map_operation .drp (.cons name .nil)

theorem map_instantiateName {Γ : Ctx sig}
    (continuation : Proc A (.nm :: Γ)) (name : Name A Γ) :
    h.raw.map (instantiateName A continuation name) =
      instantiateName B (h.raw.map continuation) (h.raw.map name) := by
  have environmentEq :
      (fun sort index =>
        h.raw.map (newestNameEnvironment A name sort index)) =
      newestNameEnvironment B (h.raw.map name) := by
    funext sort index
    cases index with
    | zero => rfl
    | succ older => exact h.raw.map_variable older
  change h.raw.map
      (A.substitution.substitute (newestNameEnvironment A name)
        continuation) =
    B.substitution.substitute
      (newestNameEnvironment B (h.raw.map name))
      (h.raw.map continuation)
  exact (h.map_substitute (newestNameEnvironment A name)
    continuation).trans
      (congrArg
        (fun environment =>
          B.substitution.substitute environment (h.raw.map continuation))
        environmentEq)

theorem map_commSource {Γ : Ctx sig} (channel : Name A Γ)
    (payload : Proc A Γ) (continuation : Proc A (.nm :: Γ)) :
    h.raw.map (commSource A channel payload continuation) =
      commSource B (h.raw.map channel) (h.raw.map payload)
        (h.raw.map continuation) := by
  simp only [commSource, map_par, map_output, map_input]
  rfl

theorem map_commTarget {Γ : Ctx sig} (payload : Proc A Γ)
    (continuation : Proc A (.nm :: Γ)) :
    h.raw.map (commTarget A payload continuation) =
      commTarget B (h.raw.map payload) (h.raw.map continuation) := by
  simp only [commTarget, map_instantiateName, map_quote]
  rfl

/-- A process reduction judgment keeps its full sorted context and both
semantic endpoints. Names are used as parameters but are not reduced here. -/
abbrev Judgment (A : BindingCloneAlgebra.Algebra.{u} sig) :=
  Σ Γ : Ctx sig, Proc A Γ × Proc A Γ

def judgment (A : BindingCloneAlgebra.Algebra.{u} sig)
    {Γ : Ctx sig} (source target : Proc A Γ) : Judgment A :=
  ⟨Γ, source, target⟩

/-- The intrinsic binary operational profile corresponding to the source's
COMM and Drop rules, with recursive parallel congruence. The COMM
continuation lives in the name-extended context. -/
inductive RuleShape (A : BindingCloneAlgebra.Algebra.{u} sig) :
    Judgment A → Type (max u 1) where
  | comm {Γ : Ctx sig} (channel : Name A Γ) (payload : Proc A Γ)
      (continuation : Proc A (.nm :: Γ)) :
      RuleShape A (judgment A
        (commSource A channel payload continuation)
        (commTarget A payload continuation))
  | drop {Γ : Ctx sig} (process : Proc A Γ) :
      RuleShape A (judgment A
        (RhoSemanticRulePolynomial.drop A (quote A process)) process)
  | parCong {Γ : Ctx sig} (source target rest : Proc A Γ) :
      RuleShape A (judgment A
        (par A source rest) (par A target rest))

/-- COMM and Drop are nullary; parallel congruence requests one recursive
reduction premise. -/
def premisePosition : {j : Judgment A} → RuleShape A j → Type
  | _, .comm _ _ _ => Empty
  | _, .drop _ => Empty
  | _, .parCong _ _ _ => Unit

/-- The recursive congruence premise remains in its original sorted context.
The binder-local continuation of COMM is an authored parameter, not a
recursive premise. -/
def premiseJudgment : {j : Judgment A} →
    (shape : RuleShape A j) → premisePosition shape → Judgment A
  | _, .comm _ _ _, impossible => impossible.elim
  | _, .drop _, impossible => impossible.elim
  | _, .parCong source target _, _ => judgment A source target

def rules (A : BindingCloneAlgebra.Algebra.{u} sig) :
    IndexedPolynomial Unit (fun _ => Judgment A) where
  Shape _ j := RuleShape A j
  Position shape := premisePosition shape
  next shape position := premiseJudgment shape position

/-- A genuine nullary COMM firing at the open-context boundary. Its source is
literal-quote safe; its target uses a constructed name from the ambient
payload. Both are intrinsically scoped process terms. -/
def terms_openCommTree :
    (rules (BindingCloneAlgebra.terms sig)).Fix ()
      (judgment (BindingCloneAlgebra.terms sig)
        IntrinsicEncoding.openCommSource
        IntrinsicEncoding.openCommTarget) := by
  rw [← terms_openCommSource, ← terms_openCommTarget]
  exact .roll (RuleShape.comm (A := BindingCloneAlgebra.terms sig)
    IntrinsicEncoding.openCommAmbientName
    IntrinsicEncoding.openCommPayload
    IntrinsicEncoding.openCommContinuation)
    (fun impossible => impossible.elim)

/-- Clone maps preserve contexts and map each endpoint by the corresponding
semantic operation and substitution map. -/
def mapJudgment (h : FreeBindingClone.Hom A B) : Judgment A → Judgment B
  | ⟨Γ, source, target⟩ =>
      ⟨Γ, h.raw.map source, h.raw.map target⟩

theorem mapJudgment_id (A : BindingCloneAlgebra.Algebra.{u} sig)
    (j : Judgment A) :
    mapJudgment (FreeBindingClone.Hom.id A) j = j := by
  cases j
  rfl

theorem mapJudgment_comp
    {D : BindingCloneAlgebra.Algebra.{u} sig}
    (first : FreeBindingClone.Hom A B)
    (later : FreeBindingClone.Hom B D) (j : Judgment A) :
    mapJudgment (FreeBindingClone.Hom.comp first later) j =
      mapJudgment later (mapJudgment first j) := by
  cases j
  rfl

/-- The image of each rule shape has exactly the mapped semantic endpoints.
In particular the communication target uses substitution preservation under
the input binder, rather than a textual variable-name argument. -/
noncomputable def mapShape (h : FreeBindingClone.Hom A B) :
    {j : Judgment A} → RuleShape A j →
      RuleShape B (mapJudgment h j)
  | _, .comm channel payload continuation => by
      change RuleShape B (judgment B
        (h.raw.map (commSource A channel payload continuation))
        (h.raw.map (commTarget A payload continuation)))
      rw [map_commSource h, map_commTarget h]
      exact .comm (h.raw.map channel) (h.raw.map payload)
        (h.raw.map continuation)
  | _, .drop process => by
      change RuleShape B (judgment B
        (h.raw.map (drop A (quote A process))) (h.raw.map process))
      rw [map_drop h, map_quote h]
      exact .drop (h.raw.map process)
  | _, .parCong source target rest => by
      change RuleShape B (judgment B
        (h.raw.map (par A source rest))
        (h.raw.map (par A target rest)))
      rw [map_par h, map_par h]
      exact .parCong (h.raw.map source) (h.raw.map target)
        (h.raw.map rest)

/-- The sole recursive premise of parallel congruence transports to the
same sorted judgment under a binding-clone interpretation. -/
theorem map_parCong_premise (h : FreeBindingClone.Hom A B)
    {Γ : Ctx sig} (source target rest : Proc A Γ) :
    mapJudgment h
        (premiseJudgment (RuleShape.parCong source target rest) ()) =
      premiseJudgment
        (RuleShape.parCong (h.raw.map source) (h.raw.map target)
          (h.raw.map rest)) () := by
  rfl

/-! ## The authored communication schema in the raw term model -/

private abbrev raw := BindingCloneAlgebra.terms sig

/-- Place a source metavariable body under the input's ambient context while
retaining its one dependency on the newly bound name. -/
private def boundNameRen : Ren sig [Srt.nm] (.nm :: G) :=
  fun (sort : Srt) (index : Var [Srt.nm] sort) =>
    match index with
    | .zero => (Var.zero : Var (Srt.nm :: G) Srt.nm)

def openContinuation (body : Term sig [Srt.nm] Srt.pr) :
    Proc raw (.nm :: G) :=
  rename boundNameRen body

private theorem boundNameSub_eq :
    (argsToSub (.cons (Term.var (Var.zero : Var (.nm :: G) .nm)) .nil) :
      Sub sig [Srt.nm] (.nm :: G)) =
    (fun sort index => Term.var (boundNameRen sort index)) := by
  funext sort index
  cases index with
  | zero => rfl
  | succ old => nomatch old

private theorem openContinuation_eq_bind
    (body : Term sig [Srt.nm] Srt.pr) :
    openContinuation body =
      bind (argsToSub (.cons
        (Term.var (Var.zero : Var (.nm :: G) .nm)) .nil)) body := by
  rw [boundNameSub_eq, bind_var_eq_rename]
  rfl

def singleBody (body : Term sig [Srt.nm] Srt.pr) :
    (i : Fin metas.length) → Term sig (metas.get i).1 (metas.get i).2
  | ⟨0, _⟩ => body

/-- Every possible authored continuation body, not just a chosen example,
has the same communication source when read as a semantic clone operation. -/
theorem raw_comm_source_body (body : Term sig [Srt.nm] Srt.pr) :
    commSource raw (Term.var Var.zero) (Term.var (Var.succ Var.zero))
        (openContinuation body) =
      instantiate (singleBody body) commLhs := by
  rw [openContinuation_eq_bind]
  rfl

/-- The corresponding target comparison holds for every continuation body:
semantic binder substitution is the same operation as schema instantiation. -/
theorem raw_comm_target_body (body : Term sig [Srt.nm] Srt.pr) :
    commTarget raw (Term.var (Var.succ Var.zero))
        (openContinuation body) =
      instantiate (singleBody body) commRhs := by
  let quoted : Term sig G Srt.nm :=
    quote raw (Term.var (Var.succ Var.zero))
  change bind
      (newestNameEnvironment raw quoted)
      (rename boundNameRen body) =
    bind (argsToSub (.cons
      quoted .nil))
      body
  calc
    bind (newestNameEnvironment raw quoted) (rename boundNameRen body) =
        bind (fun sort index =>
          newestNameEnvironment raw quoted sort (boundNameRen sort index))
          body := bind_rename boundNameRen (newestNameEnvironment raw quoted)
            body
    _ = bind (argsToSub (.cons quoted .nil)) body := by
      congr 1
      funext sort index
      cases index with
      | zero => rfl
      | succ old => nomatch old

/-- All intrinsic COMM schema instances, including ones that use the bound
name, are constructors of the semantic rule polynomial on raw syntax. -/
theorem authored_comm_shape_body (body : Term sig [Srt.nm] Srt.pr) :
    Nonempty (RuleShape raw
      (judgment raw (instantiate (singleBody body) commLhs)
        (instantiate (singleBody body) commRhs))) := by
  rw [← raw_comm_source_body, ← raw_comm_target_body]
  exact ⟨.comm (Term.var Var.zero) (Term.var (Var.succ Var.zero))
    (openContinuation body)⟩

/-- The complete source equation quotient interprets every authored COMM
continuation, with source and target mapped by one substitution-preserving
binding-clone morphism. -/
theorem source_equation_model_comm_shape_body
    (body : Term sig [Srt.nm] Srt.pr) :
    Nonempty (RuleShape
      (FreeBindingEquationModel.presented rhoSourceE).algebra
      (mapJudgment
        (FreeBindingClone.interpretHom
          (FreeBindingEquationModel.presented rhoSourceE).algebra)
        (judgment raw (instantiate (singleBody body) commLhs)
          (instantiate (singleBody body) commRhs)))) := by
  obtain ⟨shape⟩ := authored_comm_shape_body body
  exact ⟨mapShape
    (FreeBindingClone.interpretHom
      (FreeBindingEquationModel.presented rhoSourceE).algebra) shape⟩

/-- The independently authored source Drop schema is the semantic Drop
constructor in the raw term model. -/
theorem authored_drop_shape :
    Nonempty (RuleShape raw
      (judgment raw (instantiate contDiscard dropLhs)
        (instantiate contDiscard dropRhs))) := by
  change Nonempty (RuleShape raw
    (judgment raw
      (drop raw (quote raw (Term.var Var.zero)))
      (Term.var Var.zero)))
  exact ⟨RuleShape.drop (A := raw) (Γ := [Srt.pr])
    (Term.var Var.zero)⟩

/-- That same Drop constructor survives the complete source equations. -/
theorem source_equation_model_drop_shape :
    Nonempty (RuleShape
      (FreeBindingEquationModel.presented rhoSourceE).algebra
      (mapJudgment
        (FreeBindingClone.interpretHom
          (FreeBindingEquationModel.presented rhoSourceE).algebra)
        (judgment raw (instantiate contDiscard dropLhs)
          (instantiate contDiscard dropRhs)))) := by
  obtain ⟨shape⟩ := authored_drop_shape
  exact ⟨mapShape
    (FreeBindingClone.interpretHom
      (FreeBindingEquationModel.presented rhoSourceE).algebra) shape⟩

private def openUnquote : Proc raw (.nm :: G) :=
  Term.op Op.drp (.cons (.var .zero) .nil)

/-- The schema instantiated with the continuation that uses its bound name
has exactly the semantic COMM source, including the binder body. -/
theorem raw_comm_source_unquote :
    commSource raw (Term.var Var.zero) (Term.var (Var.succ Var.zero))
        openUnquote =
      instantiate contUnquote commLhs := by
  rfl

/-- Communication substitutes the quoted payload into that same authored
continuation; the semantic target agrees with the schema's instantiated RHS. -/
theorem raw_comm_target_unquote :
    commTarget raw (Term.var (Var.succ Var.zero)) openUnquote =
      instantiate contUnquote commRhs := by
  rfl

/-- A concrete constructor inhabits the judgment specified by the actual
authored schema instance, rather than an unrelated synthetic operation. -/
theorem authored_comm_shape_unquote :
    Nonempty (RuleShape raw
      (judgment raw (instantiate contUnquote commLhs)
        (instantiate contUnquote commRhs))) := by
  rw [← raw_comm_source_unquote, ← raw_comm_target_unquote]
  exact ⟨.comm (Term.var Var.zero) (Term.var (Var.succ Var.zero))
    openUnquote⟩

/-- The source's complete equation quotient still interprets the concrete
open-continuation COMM constructor. The general clone-map law transports
its endpoints and its binder-dependent substitution together. -/
theorem source_equation_model_comm_shape_unquote :
    Nonempty (RuleShape
      (FreeBindingEquationModel.presented rhoSourceE).algebra
      (mapJudgment
        (FreeBindingClone.interpretHom
          (FreeBindingEquationModel.presented rhoSourceE).algebra)
        (judgment raw (instantiate contUnquote commLhs)
          (instantiate contUnquote commRhs)))) := by
  obtain ⟨shape⟩ := authored_comm_shape_unquote
  exact ⟨mapShape
    (FreeBindingClone.interpretHom
      (FreeBindingEquationModel.presented rhoSourceE).algebra) shape⟩

end Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
