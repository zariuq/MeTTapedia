import Mettapedia.Logic.HOL.Embedding.ContextualSimpleSlice
import Mettapedia.TypeTheory.BubbleBetaTyping
import Mettapedia.Languages.HOLLight.ProofDataEncoding
import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.OpenTheory.ReverseTranslation
import Mettapedia.Languages.HOLLight.FirstOrder.Encoding
import Mettapedia.GSLT.LanguageDef.GSLTILSyntax

/-! A forward GSLT-IL route from a registered HOL Light signature to the simple
slice of the dependent core. The source kernel checks the entire proof graph
in the selected theory. The target contains the translated sequent and the
original claim and receipt. Only the former is interpreted as target syntax. -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightPrimeRoute

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.GSLT.LanguageDef GSLTIL

abbrev CoreExpr := Expr AtomicTy Symbol

/-- Lower raw OpenTheory syntax compositionally. The source typing check
below decides admission. Unsaturated primitive equality is a first-class
function in HOL, including when it is passed to another function. -/
def lower : DBTerm → CoreExpr
  | .bound n => .bvar n
  | .free v => .const v.ty.toHOL (.variable v rfl)
  | .const c ty =>
    match equalityOperand? c ty with
    | some a => termToExpr (equalityLambda (Γ := []) a.toHOL)
    | none => .const ty.toHOL (.constant c ty rfl)
  | .app f x => .app (lower f) (lower x)
  | .abs a t => .lam (tyToExpr a.toHOL) (lower t)

private theorem index_eq {Γ : HOL.Ctx AtomicTy} {τ} (i : HOL.Var Γ τ) :
    deBruijnIndex i = varIdx i := by induction i <;> simp [deBruijnIndex, varIdx, *]

theorem lower_translation {Γ : HOL.Ctx AtomicTy} {τ t} {v : HOL.Term Symbol Γ τ}
    (h : TranslatesCompositionally Γ t τ v) : lower t = termToExpr v := by
  induction h with
  | equality recognized typed => cases typed; simp [lower, recognized, equalityLambda, termToExpr, varIdx]
  | constant unrecognized typed => cases typed; simp [lower, unrecognized, termToExpr]
  | free typed => cases typed; rfl
  | bound i => simp [lower, termToExpr, index_eq]
  | app _ _ ih₁ ih₂ => simp [lower, termToExpr, ih₁, ih₂]
  | abs typed _ ih => cases typed; simp [lower, termToExpr, ih]

section Equality

open Mettapedia.TypeTheory.BubbleBetaTyping (Beta)
open Mettapedia.TypeTheory.BubbleConversion (Rewrite Convertible)
open Mettapedia.TypeTheory.BubbleSubjectReduction (convertible_congr convertible_congr₂)

/-- The first-class equality function applied twice contracts to primitive
equality even when both arguments have loose variables. -/
private theorem applied_equality (a : HOL.Ty AtomicTy) (l r : CoreExpr) :
    Convertible Beta (.app (.app (termToExpr (equalityLambda (Γ := []) a)) l) r) (.eq l r) := by
  let A : CoreExpr := tyToExpr a
  let b : CoreExpr := .eq (.bvar 1) (.bvar 0)
  have first := @Beta.contract _ Symbol A (.lam A b) l
  have second := @Beta.contract _ Symbol A (.eq (Expr.shiftAt 0 l) (.bvar 0)) r
  have inner : Expr.substAt 0 l (.lam A b) = .lam A (.eq (Expr.shiftAt 0 l) (.bvar 0)) := by
    simp [A, b, Expr.substAt, Expr.shiftN, substAt_tyToExpr]
  rw [inner] at first
  have outer : Expr.substAt 0 r (.eq (Expr.shiftAt 0 l) (.bvar 0)) = .eq l r := by
    change Expr.eq (Expr.substAt 0 r (Expr.shiftAt 0 l)) r = .eq l r
    rw [Mettapedia.TypeTheory.KnowledgeSubstitution.substAt_shiftAt_cancel]
  rw [outer] at second
  exact Relation.EqvGen.trans _ _ _ (.rel _ _ (.appFunction (.root first))) (.rel _ _ (.root second))

/-- Agreement with the direct equality readback used by the first binder
publication. Only contextual β-conversion is needed. -/
theorem lower_direct {Γ : HOL.Ctx AtomicTy} {τ t} {v : HOL.Term Symbol Γ τ}
    (h : Translates Γ t τ v) : Convertible Beta (lower t) (termToExpr v) := by
  induction h with
  | equality recognized typed =>
    cases typed
    simp only [lower, recognized]
    exact .refl _
  | constant unrecognized typed =>
    cases typed
    simp only [lower, unrecognized]
    exact .refl _
  | free typed => cases typed; exact .refl _
  | bound i => rw [lower, termToExpr, index_eq]; exact .refl _
  | equalityApp recognized typed _ _ hl hr =>
    cases typed
    simp only [lower, recognized, termToExpr]
    exact .trans _ _ _ (applied_equality _ _ _)
      (convertible_congr₂ Expr.eq (fun _ _ _ h => .eqLeft h) (fun _ _ _ h => .eqRight h) hl hr)
  | app _ _ _ hf hx =>
    exact convertible_congr₂ Expr.app (fun _ _ _ h => .appFunction h) (fun _ _ _ h => .appArgument h) hf hx
  | abs typed _ hb =>
    cases typed
    exact convertible_congr (Expr.lam _) (fun _ _ h => .lamBody h) hb

end Equality

theorem lower_typed {Γ : List Ty} {t : DBTerm} {a : Ty} (admitted : t.inferType Γ = some a) :
    HasType (ctxToExpr (Γ.map Ty.toHOL)) (lower t) (tyToExpr a.toHOL) := by
  obtain ⟨v, h⟩ := TranslatesCompositionally.exists_of_inferType admitted
  rw [lower_translation h]
  exact termToExpr_typed v

/-- Type instantiation and replacement of named HOL variables use the
OpenTheory simultaneous substitution, including its change of the symbol
signature. Bound context substitution uses the same embedded terms. -/
theorem lower_instantiation {Γ : HOL.Ctx AtomicTy} {τ t} {v : HOL.Term Symbol Γ τ}
    (h : TranslatesCompositionally Γ t τ v) (s : TypeCorrectTermSubstitution) :
    lower (s.raw.applyDB t) = termToExpr (s.targetMap v) :=
  lower_translation (h.applyDB s)

theorem lower_substitution {Γ Δ : HOL.Ctx AtomicTy} {τ t} {v : HOL.Term Symbol Γ τ}
    (h : TranslatesCompositionally Γ t τ v) (σ : HOL.Subst Symbol Γ Δ) :
    termToExpr (HOL.subst σ v) = Expr.substitute (imagesOf σ) (lower t) := by
  rw [lower_translation h, substitution_natural]

/-- Substitution for loose de Bruijn indices at the source boundary. HOL's
named free symbols are unaffected; those are handled by `lower_instantiation`. -/
def liftBound (σ : Nat → DBTerm) : Nat → DBTerm
  | 0 => .bound 0
  | n + 1 => ReverseTranslation.shiftLoose 0 (σ n)

def substituteBound (σ : Nat → DBTerm) : DBTerm → DBTerm
  | .bound n => σ n
  | .const c a => .const c a
  | .free v => .free v
  | .app f x => .app (substituteBound σ f) (substituteBound σ x)
  | .abs a b => .abs a (substituteBound (liftBound σ) b)

private theorem lower_shift (t : DBTerm) (k : Nat) :
    lower (ReverseTranslation.shiftLoose k t) = Expr.shiftAt k (lower t) := by
  induction t generalizing k with
  | const c a =>
    simp only [ReverseTranslation.shiftLoose, lower]
    split <;> simp [equalityLambda, termToExpr, varIdx, Expr.shiftAt, shiftAt_tyToExpr]
  | free => rfl
  | bound i => by_cases h : i < k <;> simp [ReverseTranslation.shiftLoose, lower, Expr.shiftAt, h]
  | app f x hf hx => simp [ReverseTranslation.shiftLoose, lower, Expr.shiftAt, hf, hx]
  | abs a b ih => simp [ReverseTranslation.shiftLoose, lower, Expr.shiftAt, shiftAt_tyToExpr, ih]

private theorem lift_lower (σ : Nat → DBTerm) :
    (fun i => lower (liftBound σ i)) = Expr.liftImages (fun i => lower (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact lower_shift (σ i) 0

/-- The square on raw syntax commutes before any comparisons or printing.
It therefore also applies to every open term admitted by the route. -/
theorem lower_substituteBound (σ : Nat → DBTerm) (t : DBTerm) :
    lower (substituteBound σ t) = Expr.substitute (fun i => lower (σ i)) (lower t) := by
  induction t generalizing σ with
  | const c a =>
    simp only [substituteBound, lower]
    split <;> simp [equalityLambda, termToExpr, varIdx, Expr.substitute, Expr.liftImages,
      Expr.shiftAt, substitute_type]
  | bound => rfl
  | free => rfl
  | app f x hf hx => simp [substituteBound, lower, Expr.substitute, hf, hx]
  | abs a b ih => simp [substituteBound, lower, Expr.substitute, substitute_type, ih, lift_lower]

/-- A closed, self-delimiting payload in a MeTTaIL command. The codec retains
typed free names, primitive declarations, proof parents, root and origins. -/
private def atom {α} (codec : Codec α) (v : α) : Pattern :=
  .apply (Binary.Text.render (Binary.encodeWith codec v)) []

private def readAtom {α} (codec : Codec α) : Pattern → Option α
  | .apply text [] => (Binary.Text.parse text).bind (Binary.canonicalDecodeWith codec)
  | _ => none

private theorem read_atom {α} (codec : Codec α) (v : α) :
    readAtom codec (atom codec v) = some v := by
  simp [readAtom, atom, Binary.Text.parse_render, Binary.canonicalDecodeWith_encodeWith]

/-- Constructor view of the dependent core, with indices carried as closed
data and symbol payloads retaining their OpenTheory provenance. -/
def expression : CoreExpr → Pattern
  | .bvar n => .apply "var" [atom Codec.nat n]
  | .const _ (.variable v _) => .apply "free" [atom sourceVarCodec v]
  | .const _ (.constant c a _) => .apply "constant" [atom constantCodec c, atom tyCodec a]
  | .prop => .apply "Prop" []
  | .base b => .apply "base" [atom tyCodec b.1]
  | .pi a b => .apply "Pi" [expression a, expression b]
  | .lam a b => .apply "lambda" [expression a, expression b]
  | .app f a => .apply "app" [expression f, expression a]
  | .eq l r => .apply "eq" [expression l, expression r]
  | .all a b => .apply "forall" [expression a, expression b]
  | .ex a b => .apply "exists" [expression a, expression b]
  | .univ => .apply "universe" []
  | .tyFam b => .apply "family" [atom tyCodec b.1]
  | .top => .apply "true" []
  | .bot => .apply "false" []
  | .and a b => .apply "and" [expression a, expression b]
  | .or a b => .apply "or" [expression a, expression b]
  | .imp a b => .apply "implies" [expression a, expression b]
  | .not a => .apply "not" [expression a]

def image (s : Sequent) : Pattern :=
  .apply "sequent" [.apply "hypotheses" ((FirstOrder.sortedHypotheses s.hyp).map
    (fun h => expression (lower h.term))), expression (lower s.concl.term)]

open DefinitionAdapters ProofExecution

/-- Signature and axiom policy come from the receiving service. The sender
can propose a graph and a conclusion, but cannot install a declaration. -/
private def commands (ctx : TheoryContext) (cert : ProofSystem.Certificate) : List Registered.Command :=
  cert.1.map fun n => .proof n (ExportReplay.instanceCertificates ctx.signature)

def root? (ctx : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (cert : ProofSystem.Certificate) : Option Theorem := do
  let state ← Registered.replayFrom policy (Registered.empty ctx) (commands ctx cert)
  state.cache[cert.2]?

private theorem proof_context (policy : AxiomPolicy) [DecidablePred policy]
    {before after : Registered.State} {n : Receipt} {w : SignatureFormation.InstanceWitnesses}
    (ok : Registered.apply policy before (.proof n w) = some after) : after.context = before.context := by
  obtain ⟨out, checked, ctx, _, _⟩ := Registered.apply_result _ ok
  simp only [Registered.Command.check, Option.bind_eq_bind] at checked
  cases hn : n.replay (ruleWitness policy) before.cache with
  | none => simp [hn] at checked
  | some cache =>
    simp [hn] at checked
    exact ctx.trans (congrArg Registered.Output.context checked.2.symm)

private theorem same_context (policy : AxiomPolicy) [DecidablePred policy] (ctx : TheoryContext)
    (nodes : List Receipt) (before after : Registered.State)
    (ok : Registered.replayFrom policy before (commands ctx (nodes, 0)) = some after) :
    after.context = before.context := by
  induction nodes generalizing before with
  | nil => exact congrArg Registered.State.context (Option.some.inj ok).symm
  | cons n rest ih =>
    change (Registered.apply policy before (.proof n _) >>= fun middle =>
      Registered.replayFrom policy middle (commands ctx (rest, 0))) = some after at ok
    obtain ⟨middle, step, more⟩ := Option.bind_eq_some_iff.mp ok
    exact (ih middle more).trans (proof_context policy step)

theorem root_authority (ctx : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    {cert : ProofSystem.Certificate} {out : Theorem} (ok : root? ctx policy cert = some out) :
    TheoryDerives policy ctx out := by
  obtain ⟨state, replayed, found⟩ := Option.bind_eq_some_iff.mp ok
  have valid := Registered.replayFrom_preserves_derivations _ _ _ _ (Registered.empty_valid policy ctx) replayed
  have derives := valid out (Array.mem_of_getElem? found)
  rwa [same_context policy ctx cert.1 _ _ replayed] at derives

def termRequest (Γ : List Ty) (t : DBTerm) : Pattern :=
  .apply "HOLLight.term" [atom (Codec.list tyCodec) Γ, atom dbTermCodec t]

def termImage (Γ : List Ty) (t : DBTerm) (a : Ty) : Pattern :=
  .apply "Prime.term" [.apply "context" (Γ.map (fun ty => expression (tyToExpr ty.toHOL))),
    expression (tyToExpr a.toHOL), expression (lower t)]

private abbrev formed (ctx : TheoryContext) :=
  SignatureFormation.annotationsFormedB ctx.signature (ExportReplay.instanceCertificates ctx.signature)

def termType? (ctx : TheoryContext) (Γ : List Ty) (t : DBTerm) : Option Ty := do
  guard (Γ.all (SignatureFormation.typeFormedB ctx.signature) && formed ctx t)
  let a ← t.inferType Γ
  guard (SignatureFormation.typeFormedB ctx.signature a)
  return a

theorem termType_exact (ctx : TheoryContext) (Γ : List Ty) (t : DBTerm) (a : Ty) :
    termType? ctx Γ t = some a ↔ Γ.all (SignatureFormation.typeFormedB ctx.signature) = true ∧
      formed ctx t = true ∧ t.inferType Γ = some a ∧ SignatureFormation.TypeFormed ctx.signature a := by
  simp [termType?, guard, Option.bind_eq_some_iff, SignatureFormation.typeFormedB_eq_true_iff, and_assoc]

theorem admitted_term_typed {ctx : TheoryContext} {Γ : List Ty} {t : DBTerm} {a : Ty}
    (checked : termType? ctx Γ t = some a) :
    HasType (ctxToExpr (Γ.map Ty.toHOL)) (lower t) (tyToExpr a.toHOL) :=
  lower_typed ((termType_exact _ _ _ _).mp checked).2.2.1

private theorem formed_shift (ctx : TheoryContext) (i : Nat) (t : DBTerm) :
    formed ctx (ReverseTranslation.shiftLoose i t) = formed ctx t := by
  induction t generalizing i with
  | bound n => by_cases h : n < i <;> simp [formed, ReverseTranslation.shiftLoose, h, SignatureFormation.annotationsFormedB]
  | const | free => rfl
  | app f x hf hx =>
    simp only [formed, ReverseTranslation.shiftLoose, SignatureFormation.annotationsFormedB] at *
    rw [hf, hx]
  | abs a b ih =>
    simp only [formed, ReverseTranslation.shiftLoose, SignatureFormation.annotationsFormedB] at *
    rw [ih]

/-- Only declared positions are constrained. An image can mention any
variable of the destination context, including one used by another image. -/
def AdmittedImages (ctx : TheoryContext) (Γ Δ : List Ty) (σ : Nat → DBTerm) : Prop :=
  ∀ i a, Γ[i]? = some a → (σ i).inferType Δ = some a ∧ formed ctx (σ i) = true

private theorem lift_admitted {ctx : TheoryContext} {Γ Δ : List Ty} {σ : Nat → DBTerm}
    (h : AdmittedImages ctx Γ Δ σ) (a : Ty) :
    AdmittedImages ctx (a :: Γ) (a :: Δ) (liftBound σ) := by
  intro i τ hit
  cases i with
  | zero => exact ⟨by simpa [liftBound, DBTerm.inferType] using hit, by simp [formed, liftBound, SignatureFormation.annotationsFormedB]⟩
  | succ i =>
    obtain ⟨ty, ok⟩ := h i τ hit
    exact ⟨(ReverseTranslation.inferType_shiftLoose_zero _ _ _).trans ty,
      (formed_shift _ _ _).trans ok⟩

private theorem subst_checked {ctx : TheoryContext} {Γ Δ : List Ty} {σ : Nat → DBTerm}
    {a : Ty} (t : DBTerm) (images : AdmittedImages ctx Γ Δ σ)
    (ty : t.inferType Γ = some a) (ok : formed ctx t = true) :
    (substituteBound σ t).inferType Δ = some a ∧ formed ctx (substituteBound σ t) = true := by
  induction t generalizing Γ Δ σ a with
  | bound n => exact images n _ (by simpa only [DBTerm.inferType.eq_3] using ty)
  | const | free => exact ⟨by simpa [substituteBound, DBTerm.inferType] using ty, ok⟩
  | app f x hf hx =>
    obtain ⟨dom, ft, xt⟩ := DBTerm.inferType_app_eq_some_iff.mp ty
    simp only [formed, SignatureFormation.annotationsFormedB, Bool.and_eq_true] at ok
    obtain ⟨ff, xf⟩ := ok
    obtain ⟨ft', ff'⟩ := hf images ft ff
    obtain ⟨xt', xf'⟩ := hx images xt xf
    exact ⟨DBTerm.inferType_app_eq_some_iff.mpr ⟨dom, ft', xt'⟩, by simpa only [substituteBound, formed, SignatureFormation.annotationsFormedB, Bool.and_eq_true] using And.intro ff' xf'⟩
  | abs dom b ih =>
    obtain ⟨cod, body, rfl⟩ := DBTerm.inferType_abs_eq_some_iff.mp ty
    simp only [formed, SignatureFormation.annotationsFormedB, Bool.and_eq_true] at ok
    obtain ⟨domainOk, bodyOk⟩ := ok
    obtain ⟨body', ok'⟩ := ih (lift_admitted images dom) body bodyOk
    exact ⟨DBTerm.inferType_abs_eq_some_iff.mpr ⟨cod, body', rfl⟩,
      by simpa only [substituteBound, formed, SignatureFormation.annotationsFormedB, Bool.and_eq_true] using And.intro domainOk ok'⟩

/-- Admission survives a typed substitution into a declared destination
context. Together with `lower_substituteBound` this is a commuting square
between two executable term requests, with no successful lookup assumed. -/
theorem termType_substitution {ctx : TheoryContext} {Γ Δ : List Ty} {σ : Nat → DBTerm}
    {a : Ty} {t : DBTerm} (admitted : termType? ctx Γ t = some a)
    (destination : Δ.all (SignatureFormation.typeFormedB ctx.signature) = true)
    (images : AdmittedImages ctx Γ Δ σ) : termType? ctx Δ (substituteBound σ t) = some a := by
  obtain ⟨_, formedInput, inputType, resultFormed⟩ := (termType_exact _ _ _ _).mp admitted
  obtain ⟨ty, ok⟩ := subst_checked t images inputType formedInput
  exact (termType_exact _ _ _ _).mpr ⟨destination, ok, ty, resultFormed⟩

def request (claim : Theorem) (cert : ProofSystem.Certificate) : Pattern :=
  .apply "HOLLight.request" [atom theoremCodec claim, atom ProofDataEncoding.certificateCodec cert]

def issued (source : Pattern) (claim : Theorem) (cert : ProofSystem.Certificate) : Pattern :=
  .apply "Prime.import" [image claim.sequent, .apply "HOLLight.receipt" [source, request claim cert]]

def routeDecl (source : Pattern) : GSLTIL.Syntax.RouteDecl :=
  ⟨.apply "HOLLight.toSimpleSlice" [], "HOLLight.toSimpleSlice", source, .apply "Prime.simpleSlice" []⟩

def cross (ctx : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (source : Pattern) : Pattern → Option Pattern
  | .apply "HOLLight.term" [contextWire, termWire] => do
    let Γ ← readAtom (Codec.list tyCodec) contextWire
    let t ← readAtom dbTermCodec termWire
    let a ← termType? ctx Γ t
    return termImage Γ t a
  | .apply "HOLLight.request" [claimWire, certWire] => do
    let claim ← readAtom theoremCodec claimWire
    let cert ← readAtom ProofDataEncoding.certificateCodec certWire
    let root ← root? ctx policy cert
    guard (root == claim)
    return issued source claim cert
  | _ => none

def targets (ctx : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (source kind route fromStage toStage state : Pattern) : List Pattern :=
  let d := routeDecl source
  if kind = GSLTIL.Syntax.forwardKind ∧ route = GSLTIL.Syntax.routeIdentity d ∧
      fromStage = source ∧ toStage = d.targetSpace then
    (cross ctx policy source state).toList
  else []

theorem cross_term (ctx : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (source : Pattern) (Γ : List Ty) (t : DBTerm) :
    cross ctx policy source (termRequest Γ t) = (termType? ctx Γ t).map (termImage Γ t) := by
  simp [cross, termRequest, read_atom]
  cases termType? ctx Γ t <;> rfl

/-- A second call after a scoped substitution both passes admission and
returns the term obtained by substituting in the destination syntax. -/
theorem cross_substituted_term {ctx : TheoryContext} (policy : AxiomPolicy) [DecidablePred policy]
    (source : Pattern) {Γ Δ : List Ty} {σ : Nat → DBTerm} {t : DBTerm} {a : Ty}
    (admitted : termType? ctx Γ t = some a)
    (destination : Δ.all (SignatureFormation.typeFormedB ctx.signature) = true)
    (images : AdmittedImages ctx Γ Δ σ) :
    cross ctx policy source (termRequest Δ (substituteBound σ t)) =
      some (.apply "Prime.term" [.apply "context" (Δ.map (fun ty => expression (tyToExpr ty.toHOL))),
        expression (tyToExpr a.toHOL), expression (Expr.substitute (fun i => lower (σ i)) (lower t))]) := by
  rw [cross_term, termType_substitution admitted destination images]
  simp [termImage, lower_substituteBound]

theorem cross_request (ctx : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (source : Pattern) (claim : Theorem) (cert : ProofSystem.Certificate) :
    cross ctx policy source (request claim cert) =
      if root? ctx policy cert = some claim then some (issued source claim cert) else none := by
  simp only [cross, request, read_atom]
  cases h : root? ctx policy cert with
  | none => simp [h]
  | some t => by_cases same : t = claim <;> simp [h, same, guard]

/-- The receiver resolves a stage key to one signature and policy. A table
can hold many source revisions; documents never supply their own policy. -/
structure Authority where
  context : TheoryContext
  policy : AxiomPolicy
  deciding : DecidablePred policy

abbrev Registry := Pattern → Option Authority

def registeredTargets (registry : Registry)
    (kind route source target state : Pattern) : List Pattern :=
  match registry source with
  | none => []
  | some a => @targets a.context a.policy a.deciding source kind route source target state

/-- Submit a packet through the authored GSLT-IL evaluator. Source computation
under a pending crossing is selected by the caller's local step service. -/
def dispatch (registry : Registry) (localSteps : Pattern → Pattern → List Pattern)
    (source state : Pattern) : List Pattern :=
  let d := routeDecl source
  OSLF.MeTTaIL.Engine.rewriteStepWithPremisesUsing (queryEnv localSteps (registeredTargets registry))
    language (viaPattern GSLTIL.Syntax.forwardKind (GSLTIL.Syntax.routeIdentity d) source d.targetSpace state)

theorem execute_registered (registry : Registry) {source : Pattern} {a : Authority}
    (found : registry source = some a) (localSteps : Pattern → Pattern → List Pattern)
    (state : Pattern) :
    let d := routeDecl source
    let via := viaPattern GSLTIL.Syntax.forwardKind (GSLTIL.Syntax.routeIdentity d) source d.targetSpace
    dispatch registry localSteps source state =
      (localSteps source state).map via ++
      ((@cross a.context a.policy a.deciding source state).toList.map (atPattern d.targetSpace)) := by
  dsimp only
  unfold dispatch
  rw [execute_via_using]
  simp [registeredTargets, found, targets]

/-- A returned proof has only one possible origin in this command.
Independent computational alternatives still have a pending `via` tag. -/
theorem returned_iff (registry : Registry) {source : Pattern} {a : Authority}
    (found : registry source = some a) (localSteps : Pattern → Pattern → List Pattern)
    (claim : Theorem) (cert : ProofSystem.Certificate) (packet : Pattern) :
    atPattern (routeDecl source).targetSpace packet ∈
        dispatch registry localSteps source (request claim cert) ↔
      @root? a.context a.policy a.deciding cert = some claim ∧ packet = issued source claim cert := by
  rw [execute_registered registry found, cross_request]
  split <;> simp_all [atPattern, viaPattern]

private def inspectReceipt : Pattern → Option (Pattern × Theorem × ProofSystem.Certificate)
  | .apply "Prime.import" [_, .apply "HOLLight.receipt" [source, .apply "HOLLight.request" [f, g]]] =>
    return (source, ← readAtom theoremCodec f, ← readAtom ProofDataEncoding.certificateCodec g)
  | _ => none

/-- An independent receiver reconstructs the target and checks the source
graph anew. Parsing the issuer tag alone grants no authority. -/
def recheck (registry : Registry) (alleged : Pattern) : Bool := (do
  let (source, claim, cert) ← inspectReceipt alleged
  let a ← registry source
  let expected ← @cross a.context a.policy a.deciding source (request claim cert)
  pure (expected == alleged)).getD false

theorem recheck_iff (registry : Registry) (alleged : Pattern) :
    recheck registry alleged = true ↔ ∃ source claim cert, ∃ a : Authority,
      registry source = some a ∧ @root? a.context a.policy a.deciding cert = some claim ∧
      alleged = issued source claim cert := by
  constructor
  · intro ok
    unfold recheck at ok
    cases seen : inspectReceipt alleged with
    | none => simp [seen] at ok
    | some p =>
      obtain ⟨s, c, g⟩ := p
      cases found : registry s with
      | none => simp [seen, found] at ok
      | some a =>
        by_cases accepted : @root? a.context a.policy a.deciding g = some c
        · exact ⟨s, c, g, a, found, accepted, (by simpa [seen, found, cross_request, accepted] using ok : issued s c g = alleged).symm⟩
        · simp [seen, found, cross_request, accepted] at ok
  · rintro ⟨s, c, g, a, found, accepted, rfl⟩
    have parsed : inspectReceipt (issued s c g) = some (s, c, g) := by
      simp [issued, inspectReceipt, request, read_atom]
    simp [recheck, parsed, found, cross_request, accepted]

/-- Every returned theorem packet passes independent replay at its registered
source, for any choice of source-fibre computation under `via`. -/
theorem returned_rechecks (registry : Registry) {source : Pattern} {a : Authority}
    (found : registry source = some a) (localSteps : Pattern → Pattern → List Pattern)
    {claim : Theorem} {cert : ProofSystem.Certificate} {packet : Pattern}
    (returned : atPattern (routeDecl source).targetSpace packet ∈
      dispatch registry localSteps source (request claim cert)) : recheck registry packet = true := by
  obtain ⟨root, same⟩ := (returned_iff registry found localSteps claim cert packet).mp returned
  exact (recheck_iff _ _).2 ⟨source, claim, cert, a, found, root, same⟩

theorem rechecked_authority {registry : Registry} {packet : Pattern}
    (ok : recheck registry packet = true) :
    ∃ s c g, ∃ a : Authority, registry s = some a ∧ TheoryDerives a.policy a.context c ∧
      packet = issued s c g := by
  obtain ⟨s, c, g, a, found, checked, exactPacket⟩ := (recheck_iff _ _).1 ok
  exact ⟨s, c, g, a, found, @root_authority a.context a.policy a.deciding g c checked, exactPacket⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightPrimeRoute
