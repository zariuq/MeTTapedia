import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadMorphism
import Mettapedia.Logic.HOL.PredicateContexts

/-!
# Reading source telescopes into guarded HOL contexts

Every source binder is read in its preceding context at the predicate type
of its selected simple carrier. The executable reader retains the resulting
guard telescope and is complete and coherent for this relation. Source
formation is checked separately by the existing context certificate receiver.

Compatible source/context renamings construct actual guard proofs. General
substitution transports type readings; transporting their truth additionally
requires proofs of the substituted variable guards. No general interpretation
of universes, or of all source typing rules, is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Mettapedia.Logic
open Presentation TypedEquality.Annotated
open HOL.PredicateContexts
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Preserve successful lexical entries along a source-head map. The target
may additionally interpret other declarations; reflection is not asserted. -/
structure LexicalMap {Head' : Type} (source : LexicalReading Head Base Const)
    (target : LexicalReading Head' Base Const) (headMap : Head → Head') : Prop where
  constants : ∀ name type (code : HOL.ClosedTerm Const type),
    source.constCode? name = some ⟨type, code⟩ → target.constCode? name = some ⟨type, code⟩
  heads : ∀ head type (code : HOL.ClosedTerm Const type),
    source.headCode? head = some ⟨type, code⟩ → target.headCode? (headMap head) = some ⟨type, code⟩
  structural : ∀ operator result (code : HOL.ClosedTerm Const (operator.codeType result)),
    source.structuralCode? operator = some ⟨result, code⟩ →
      target.structuralCode? operator = some ⟨result, code⟩

theorem Reads.mapLexical {Head' : Type} {source : LexicalReading Head Base Const}
    {target : LexicalReading Head' Base Const} {headMap : Head → Head'}
    (mapping : LexicalMap source target headMap)
    {Γ : HOL.Ctx Base} {type : HOL.Ty Base} {term : CTm Head Γ.length}
    {code : HOL.Term Const Γ type} (reading : Reads source term code) :
    Reads target (term.mapHead headMap) code := by
  induction reading with
  | var index => exact .var index
  | constant found => exact .constant (mapping.constants _ _ _ found)
  | head found => exact .head (mapping.heads _ _ _ found)
  | application _ _ first second => exact .application first second
  | abstraction _ _ first second => exact .abstraction first second
  | product _ _ first second => exact .product first second
  | dependentSum lookup _ _ domain family =>
      exact .dependentSum (mapping.structural _ _ _ lookup) domain family
  | identity lookup _ _ _ domain left right =>
      exact .identity (mapping.structural _ _ _ lookup) domain left right
  | pair lookup _ _ left right => exact .pair (mapping.structural _ _ _ lookup) left right
  | first lookup _ argument => exact .first (mapping.structural _ _ _ lookup) argument
  | second lookup _ argument => exact .second (mapping.structural _ _ _ lookup) argument
  | reflexivity lookup _ argument => exact .reflexivity (mapping.structural _ _ _ lookup) argument

theorem LexicalMap.carrier_eq_of_collision {Head' : Type}
    {source : LexicalReading Head Base Const} {target : LexicalReading Head' Base Const}
    {headMap : Head → Head'} (mapping : LexicalMap source target headMap)
    {first second : Head} (collision : headMap first = headMap second)
    {firstType secondType : HOL.Ty Base} {firstCode : HOL.ClosedTerm Const firstType}
    {secondCode : HOL.ClosedTerm Const secondType}
    (firstRead : source.headCode? first = some ⟨firstType, firstCode⟩)
    (secondRead : source.headCode? second = some ⟨secondType, secondCode⟩) : firstType = secondType := by
  have firstMapped := mapping.heads _ _ _ firstRead
  have secondMapped := mapping.heads _ _ _ secondRead
  rw [collision] at firstMapped
  exact congrArg Sigma.fst (Option.some.inj (firstMapped.symm.trans secondMapped))

inductive ContextReads (lex : LexicalReading Head Base Const) :
    {Γ : HOL.Ctx Base} → CCtx Head Γ.length → Telescope Const Γ → Prop where
  | nil : ContextReads lex .nil .nil
  | snoc {Γ : HOL.Ctx Base} {type : HOL.Ty Base}
      {context : CCtx Head Γ.length} {code : Telescope Const Γ}
      {domain : CTm Head Γ.length} {predicate : HOL.Term Const Γ (type ⇒ .prop)} :
      ContextReads lex context code → Reads lex domain predicate →
      ContextReads lex (Γ := type :: Γ) (.snoc context domain) (.snoc code predicate)

namespace ContextReads
variable {lex : LexicalReading Head Base Const} {Γ Ξ : HOL.Ctx Base}
  {context : CCtx Head Γ.length} {code : Telescope Const Γ}

theorem mapLexical {Head' : Type} {target : LexicalReading Head' Base Const}
    {headMap : Head → Head'} (mapping : LexicalMap lex target headMap)
    (reading : ContextReads lex context code) : ContextReads target (context.mapHead headMap) code := by
  induction reading with
  | nil => exact .nil
  | snoc _ domain ih => exact .snoc ih (domain.mapLexical mapping)

theorem lookup (reading : ContextReads lex context code) {type : HOL.Ty Base} (index : HOL.Var Γ type) :
    Reads lex (context.lookup index.toFin) (code.domain index) := by
  induction reading with
  | nil => cases index
  | snoc prior predicate ih =>
      cases index with
      | vz =>
          simpa [CCtx.lookup, HOL.Var.toFin, Telescope.domain, HOL.weaken] using
            predicate.rename HOL.Rename.weaken wk (fun _ => rfl)
      | vs previous =>
          simpa [CCtx.lookup, HOL.Var.toFin, Telescope.domain, HOL.weaken] using
            (ih previous).rename HOL.Rename.weaken wk (fun _ => rfl)

theorem lookup_substitute (reading : ContextReads lex context code)
    (substitution : HOL.Subst Const Γ Ξ) (raw : CSub Head Γ.length Ξ.length)
    (components : ∀ {type} (index : HOL.Var Γ type), Reads lex (raw index.toFin) (substitution index))
    {type : HOL.Ty Base} (index : HOL.Var Γ type) :
    Reads lex ((context.lookup index.toFin).subst raw) (HOL.subst substitution (code.domain index)) :=
  (reading.lookup index).substitute substitution raw components

end ContextReads

namespace Reader
variable [DecidableEq Base]

abbrev ContextResult (lex : LexicalReading Head Base Const) (Γ : HOL.Ctx Base)
    (context : CCtx Head Γ.length) := {code : Telescope Const Γ // ContextReads lex context code}

def readContext? (lex : LexicalReading Head Base Const) : (Γ : HOL.Ctx Base) →
    (context : CCtx Head Γ.length) → Option (ContextResult lex Γ context)
  | [], .nil => some ⟨.nil, .nil⟩
  | type :: Γ, .snoc context domain => do
      let prior ← readContext? lex Γ context
      let ⟨⟨carrier, predicate⟩, reading⟩ ← read? lex Γ domain
      if sameCarrier : carrier = (type ⇒ .prop) then
        some ⟨.snoc prior.val (sameCarrier ▸ predicate), by
          cases sameCarrier
          exact .snoc prior.property reading⟩
      else none

theorem readContext_complete {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}
    {context : CCtx Head Γ.length} {code : Telescope Const Γ} (reading : ContextReads lex context code) :
    readContext? lex Γ context = some ⟨code, reading⟩ := by
  induction reading with
  | nil => rfl
  | snoc prior predicate ih =>
      simp [readContext?, ih, read?_complete predicate]

theorem context_unique {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}
    {context : CCtx Head Γ.length} {first second : Telescope Const Γ}
    (firstRead : ContextReads lex context first) (secondRead : ContextReads lex context second) : first = second :=
  congrArg Subtype.val (Option.some.inj ((readContext_complete firstRead).symm.trans (readContext_complete secondRead)))

end Reader

namespace ContextReads
variable [DecidableEq Base]
variable {lex : LexicalReading Head Base Const} {Γ Ξ : HOL.Ctx Base}
  {context : CCtx Head Γ.length} {code : Telescope Const Γ}
  {target : CCtx Head Ξ.length} {targetCode : Telescope Const Ξ}

theorem rename_domain (reading : ContextReads lex context code) (targetRead : ContextReads lex target targetCode)
    (rho : HOL.Rename Base Γ Ξ) (raw : Ren Γ.length Ξ.length)
    (compatible : ∀ {type} (index : HOL.Var Γ type), (rho index).toFin = raw index.toFin)
    (placement : CCtxRen context target raw) {type : HOL.Ty Base} (index : HOL.Var Γ type) :
    targetCode.domain (rho index) = HOL.rename rho (code.domain index) := by
  have received := targetRead.lookup (rho index)
  rw [compatible index, placement index.toFin] at received
  exact Reader.term_unique received ((reading.lookup index).rename rho raw compatible)

def renamingRealizer (reading : ContextReads lex context code) (targetRead : ContextReads lex target targetCode)
    (rho : HOL.Rename Base Γ Ξ) (raw : Ren Γ.length Ξ.length)
    (compatible : ∀ {type} (index : HOL.Var Γ type), (rho index).toFin = raw index.toFin)
    (placement : CCtxRen context target raw) :
    code.Realizes (HOL.Subst.ofRename rho) targetCode.hypotheses :=
  fun index => HOL.ProofSyntax.castIndices rfl (by
    simp only [Telescope.guard, HOL.subst_ofRename, HOL.rename,
      reading.rename_domain targetRead rho raw compatible placement index])
    (targetCode.variableProof (rho index))

end ContextReads

namespace Reader
variable [DecidableEq Base] [DecidableEq Head]
variable {R : Rules Head} (P : ChurchRules R)
  [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
  [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]

structure AdmittedContext (lex : LexicalReading Head Base Const) (Γ : HOL.Ctx Base)
    (context : CCtx Head Γ.length) where
  code : Telescope Const Γ
  reading : ContextReads lex context code
  formed : CCtxFormed P context

def admitContext? (lex : LexicalReading Head Base Const) (decoder : Checking.RootDecoder P.computation)
    (Γ : HOL.Ctx Base) (context : CCtx Head Γ.length)
    (certificate : Checking.ContextCode Head (Checking.interface P decoder).W Γ.length) :
    Option (AdmittedContext P lex Γ context) :=
  if checked : Checking.checkContext P decoder context certificate = true then
    (readContext? lex Γ context).map fun result =>
      ⟨result.val, result.property, Checking.checkContext_sound P decoder certificate checked⟩
  else none

theorem admitContext_complete {lex : LexicalReading Head Base Const} (decoder : Checking.RootDecoder P.computation)
    {Γ : HOL.Ctx Base} {context : CCtx Head Γ.length} (admitted : AdmittedContext P lex Γ context) :
    ∃ certificate, admitContext? P lex decoder Γ context certificate = some admitted := by
  obtain ⟨certificate, checked⟩ := Checking.checkContext_complete P decoder admitted.formed
  refine ⟨certificate, ?_⟩
  simp only [admitContext?, checked, dite_true, readContext_complete admitted.reading, Option.map_some]

end Reader

#print axioms ContextReads.lookup
#print axioms ContextReads.mapLexical
#print axioms LexicalMap.carrier_eq_of_collision
#print axioms Reader.readContext_complete
#print axioms Reader.context_unique
#print axioms ContextReads.rename_domain
#print axioms ContextReads.renamingRealizer
#print axioms Reader.admitContext_complete
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
