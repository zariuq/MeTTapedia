import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRealizability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateInterpreter

/-!
# Guarded endpoint transport from checked source equality

The source context and equality certificate are checked independently of their
HOL interpretation. A successful interpretation then transports an existing
guarded realizer. Carrier agreement follows from the shared annotated reader;
the consumer does not accept a carrier agreement or a proof-soundness premise.
The result retains source typing, exact readings and the target membership
proof. This interface does not assert total interpretation of source proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

open Mettapedia.Logic
open Presentation TypedEquality.Annotated

universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
  {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
  {roots : List (HOL.ClosedFormula Const)} {Γ Ξ : HOL.Ctx Base}

namespace EqualityAt

def castCarrier {source target : CTm Head Γ.length} {first second : HOL.Ty Base}
    (equality : EqualityAt lex roots Γ source target first) (same : first = second) :
    EqualityAt lex roots Γ source target second := same ▸ equality

theorem castCarrier_free {source target : CTm Head Γ.length} {first second : HOL.Ty Base}
    (equality : EqualityAt lex roots Γ source target first) (same : first = second)
    (free : equality.proof.FunctionExtensionalityFree) :
    (equality.castCarrier same).proof.FunctionExtensionalityFree := by
  cases same
  exact free

end EqualityAt

namespace Interpreter.CheckedEquality

variable [DecidableEq Base] {ops : Interpreter.EvidenceOps lex roots} {context : CCtx Head Γ.length}
  {source target type : CTm Head Γ.length} {carrier : HOL.Ty Base}

def readingAt (checked : Interpreter.CheckedEquality P ops Γ context source target type)
    {code : HOL.Term Const Γ carrier} (reading : Reads lex source code) :
    EqualityAt lex roots Γ source target carrier :=
  (ops.view checked.evidence).castCarrier
    (congrArg Sigma.fst (Reader.coherent (ops.view checked.evidence).leftRead reading))

theorem readingAt_left (checked : Interpreter.CheckedEquality P ops Γ context source target type)
    {code : HOL.Term Const Γ carrier} (reading : Reads lex source code) :
    (checked.readingAt reading).left = code :=
  Reader.term_unique (checked.readingAt reading).leftRead reading

theorem readingAt_free (checked : Interpreter.CheckedEquality P ops Γ context source target type)
    {code : HOL.Term Const Γ carrier} (reading : Reads lex source code)
    (free : (ops.view checked.evidence).proof.FunctionExtensionalityFree) :
    (checked.readingAt reading).proof.FunctionExtensionalityFree :=
  EqualityAt.castCarrier_free _ _ free

end Interpreter.CheckedEquality

namespace GuardedRealizer

variable [DecidableEq Base] {context : GuardedContext P lex Γ}
  {source target type : CTm Head Γ.length} {carrier : HOL.Ty Base}
  {ops : Interpreter.EvidenceOps lex roots}

def rewriteChecked {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L)
    (realizer : GuardedRealizer roots context source type carrier)
    (checked : Interpreter.CheckedEquality P ops Γ context.source source target type) :
    GuardedRealizer roots context target type carrier :=
  realizer.rewrite levels checked.sourceEqual (checked.readingAt realizer.termRead)

theorem rewriteChecked_free {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L)
    (realizer : GuardedRealizer roots context source type carrier)
    (checked : Interpreter.CheckedEquality P ops Γ context.source source target type)
    (realizerFree : realizer.Free)
    (equalityFree : (ops.view checked.evidence).proof.FunctionExtensionalityFree) :
    (realizer.rewriteChecked levels checked).Free :=
  realizer.rewrite_free levels checked.sourceEqual (checked.readingAt realizer.termRead)
    realizerFree (checked.readingAt_free realizer.termRead equalityFree)

@[simp] theorem rewriteChecked_predicate {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L)
    (realizer : GuardedRealizer roots context source type carrier)
    (checked : Interpreter.CheckedEquality P ops Γ context.source source target type) :
    (realizer.rewriteChecked levels checked).predicate = realizer.predicate := rfl

theorem rewriteChecked_term {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L)
    (realizer : GuardedRealizer roots context source type carrier)
    (checked : Interpreter.CheckedEquality P ops Γ context.source source target type) :
    (realizer.rewriteChecked levels checked).term = (checked.readingAt realizer.termRead).right := rfl

/-- Independently checked substituted equality and transport before substitution
have the same endpoint code and predicate. Their retained proof histories need
not be equal, and this statement does not manufacture a substituted certificate. -/
theorem rewriteChecked_substitute {L : Type} [UniverseLevel.LevelOrder L]
    (levels : TypedEquality.Normalization.LevelModel R L)
    {destination : GuardedContext P lex Ξ} {raw : CSub Head Γ.length Ξ.length}
    {code : HOL.Subst Const Γ Ξ}
    (realizer : GuardedRealizer roots context source type carrier)
    (substitution : GuardedSubstitution roots context destination raw code)
    (checked : Interpreter.CheckedEquality P ops Γ context.source source target type)
    (substituted : Interpreter.CheckedEquality P ops Ξ destination.source
      (source.subst raw) (target.subst raw) (type.subst raw)) :
    ((realizer.rewriteChecked levels checked).substitute substitution).term =
        ((realizer.substitute substitution).rewriteChecked levels substituted).term ∧
      ((realizer.rewriteChecked levels checked).substitute substitution).predicate =
        ((realizer.substitute substitution).rewriteChecked levels substituted).predicate :=
  ⟨Reader.term_unique ((realizer.rewriteChecked levels checked).substitute substitution).termRead
      ((realizer.substitute substitution).rewriteChecked levels substituted).termRead,
    Reader.term_unique ((realizer.rewriteChecked levels checked).substitute substitution).typeRead
      ((realizer.substitute substitution).rewriteChecked levels substituted).typeRead⟩

end GuardedRealizer

namespace Interpreter

variable [DecidableEq Base] [DecidableEq Head]
  [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
  [∀ a b c, Decidable (R.join a b c)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
  {L : Type} [UniverseLevel.LevelOrder L]
  (levels : TypedEquality.Normalization.LevelModel R L)
  (decoder : Checking.RootDecoder P.computation)
  (ops : EvidenceOps lex roots)
  (rootReader : (Γ : HOL.Ctx Base) → (source target : CTm Head Γ.length) → decoder.Code Γ.length →
    Option ((carrier : HOL.Ty Base) × ops.Evidence Γ source target carrier))
  {context : GuardedContext P lex Γ} {source target type : CTm Head Γ.length} {carrier : HOL.Ty Base}

def checkRealizer? (realizer : GuardedRealizer roots context source type carrier)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code) :
    Option (GuardedRealizer roots context target type carrier) :=
  (check? P decoder ops rootReader Γ context.source source target type contextCertificate certificate).map
    (fun checked => realizer.rewriteChecked levels checked)

theorem checkRealizer?_success (realizer : GuardedRealizer roots context source type carrier)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code)
    (checked : CheckedEquality P ops Γ context.source source target type)
    (accepted : check? P decoder ops rootReader Γ context.source source target type
      contextCertificate certificate = some checked) :
    checkRealizer? levels decoder ops rootReader (target := target) realizer contextCertificate certificate =
      some (realizer.rewriteChecked levels checked) := by
  simp only [checkRealizer?, accepted, Option.map_some]

theorem checkRealizer?_eq_some_iff (realizer : GuardedRealizer roots context source type carrier)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code)
    (result : GuardedRealizer roots context target type carrier) :
    checkRealizer? levels decoder ops rootReader realizer contextCertificate certificate = some result ↔
      ∃ checked : CheckedEquality P ops Γ context.source source target type,
        check? P decoder ops rootReader Γ context.source source target type contextCertificate certificate = some checked ∧
        realizer.rewriteChecked levels checked = result := by
  simp only [checkRealizer?, Option.map_eq_some_iff]

theorem checkRealizer?_refuses_source (realizer : GuardedRealizer roots context source type carrier)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code)
    (refused : checkJudgment P decoder certificate (.equality context.source source target type) = false) :
    checkRealizer? levels decoder ops rootReader (target := target) realizer contextCertificate certificate = none := by
  rw [checkRealizer?, check?_refuses_source P decoder ops rootReader Γ context.source source target type
    contextCertificate certificate refused]
  rfl

theorem checkRealizer?_refuses_context (realizer : GuardedRealizer roots context source type carrier)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code)
    (refused : Checking.checkContext P decoder context.source contextCertificate = false) :
    checkRealizer? levels decoder ops rootReader (target := target) realizer contextCertificate certificate = none := by
  rw [checkRealizer?, check?_refuses_context P decoder ops rootReader Γ context.source source target type
    contextCertificate certificate refused]
  rfl

theorem checkRealizer?_isSome_iff (realizer : GuardedRealizer roots context source type carrier)
    (contextCertificate : Checking.ContextCode Head (Witness Head decoder.Code) Γ.length)
    (certificate : Certificate (Head := Head) decoder.Code) :
    (checkRealizer? levels decoder ops rootReader (target := target) realizer contextCertificate certificate).isSome = true ↔
      (check? P decoder ops rootReader Γ context.source source target type contextCertificate certificate).isSome = true := by
  simp only [checkRealizer?, Option.isSome_map]

end Interpreter

#print axioms Interpreter.CheckedEquality.readingAt
#print axioms GuardedRealizer.rewriteChecked
#print axioms GuardedRealizer.rewriteChecked_free
#print axioms GuardedRealizer.rewriteChecked_substitute
#print axioms Interpreter.checkRealizer?
#print axioms Interpreter.checkRealizer?_success
#print axioms Interpreter.checkRealizer?_eq_some_iff
#print axioms Interpreter.checkRealizer?_isSome_iff

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
