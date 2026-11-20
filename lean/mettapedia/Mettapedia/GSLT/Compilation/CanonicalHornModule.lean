import Mettapedia.GSLT.Compilation.ModedArguments
import Mettapedia.GSLT.Compilation.ModedRuleModule
import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration
import Mettapedia.GSLT.Parsing.HornUnification
import Mettapedia.Data.List.OptionMapM

/-!
# Lower exact authored Horn rows to demand modules

The source reader and the first-order term encoding are the existing
canonical GSLT/Horn interfaces. Calls and output tuples have their own
target symbols, distinct from every authored constructor. The mode
split preserves each column and its original position.

An external premise is a fixed fact query in the reference module.
It must have all its variables already bound. Presenting that fixed
interpretation as a native ground guard is a separate realization of
the same test.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.CanonicalHornModule

open Mettapedia.Logic.LP (LPSignature Term Atom)
open Mettapedia.GSLT.Parsing
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
open Mettapedia.Data.List (option_mapM_forall₂ option_mapM_getElem? option_mapM_origin)
open ModuleReading (Premise RangeRestricted QueriesBound)
open ModedRuleModule

/-- Compiler symbols that cannot accidentally share an authored head. -/
inductive Symbol where
  | authored (original : HornUnification.FunctionSymbol)
  | call (relation : HornUnification.RelationSymbol) (inputs : Nat)
  | outputs (count : Nat)
  deriving DecidableEq

def Symbol.arity : Symbol → Nat
  | .authored original => original.arity
  | .call _ inputs => inputs
  | .outputs count => count

abbrev signature : LPSignature.{0,0,0,0} :=
  ⟨HornUnification.Constant, Nat, HornUnification.RelationSymbol,
    HornUnification.RelationSymbol.arity, Symbol, Symbol.arity⟩

abbrev Signature (Labels : Type) := ModuleReading.readingSignature signature Labels

abbrev Datum (Labels : Type) := Term (Signature Labels)

def wrapTerm {Labels : Type} : Term HornUnification.signature → Datum Labels
  | .var identifier => .var identifier
  | .const value => .const value
  | .app symbol fields =>
      .app (.con (.authored symbol)) fun index => wrapTerm (fields index)

def pack {Labels : Type} (symbol : Symbol) (columns : Fin symbol.arity → Datum Labels) :
    Datum Labels :=
  .app (.con symbol) columns

inductive Mode where
  | derived (inputMask : List Bool)
  | external

abbrev Modes := HornUnification.RelationSymbol → Option Mode

def externalAtom {Labels : Type} (atom : HornUnification.RelationSymbol)
    (args : Fin atom.arity → Datum Labels) : Atom (Signature Labels) :=
  ⟨atom, args⟩

def wrapAtom {Labels : Type} (atom : Atom HornUnification.signature) : Atom (Signature Labels) :=
  externalAtom atom.symbol (fun i => wrapTerm (atom.args i))

def splitCall? {Labels : Type} (symbol : HornUnification.RelationSymbol)
    (mask : List Bool) (arguments : List (Datum Labels)) :
    Option (CallRow (Signature Labels)) := do
  let (inputs, outputs) ← ModedArguments.split mask arguments
  pure ⟨pack (.call symbol inputs.length) inputs.get, pack (.outputs outputs.length) outputs.get⟩

def lowerAtom? {Labels : Type} (modes : Modes) (atom : Atom HornUnification.signature) :
    Option (BodyLiteral (Signature Labels)) := do
  let mode ← modes atom.symbol
  match mode with
  | .external => pure (.extensional (wrapAtom atom))
  | .derived mask =>
      .intensional <$> splitCall? atom.symbol mask
        (List.ofFn fun i => wrapTerm (atom.args i))

def lowerCall? {Labels : Type} (modes : Modes) (atom : HornCertificate.Atom) :
    Option (BodyLiteral (Signature Labels)) :=
  lowerAtom? modes (HornUnification.encodeAtom atom)

/-- Check the mode through the actual ordered reads. An extensional test
may check variables in the prefix; it does not enlarge the bound set. -/
def loadBody {Labels : Type} (output : Datum Labels) :
    Finset Nat → List (BodyLiteral (Signature Labels)) → Bool
  | bound, [] => decide (output.freeVars ⊆ bound)
  | bound, .intensional call :: rest =>
      decide (call.input.freeVars ⊆ bound) && loadBody output (bound ∪ call.output.freeVars) rest
  | bound, .extensional atom :: rest =>
      decide (atom.freeVars ⊆ bound) && loadBody output bound rest

theorem loadBody_sound {Labels : Type} (output : Datum Labels) :
    ∀ (body : List (BodyLiteral (Signature Labels))) (bound : Finset Nat),
      loadBody output bound body = true →
      ModuleReading.BoundOk bound (body.map lowerLiteral) output
  | [], bound, ok => by
      change output.freeVars ⊆ bound
      exact of_decide_eq_true ok
  | .intensional call :: rest, bound, ok => by
      rw [loadBody, Bool.and_eq_true_iff] at ok
      obtain ⟨inputBound, next⟩ := ok
      exact ⟨of_decide_eq_true inputBound, loadBody_sound output rest _ next⟩
  | .extensional atom :: rest, bound, ok => by
      rw [loadBody, Bool.and_eq_true_iff] at ok
      obtain ⟨checked, next⟩ := ok
      have already : atom.freeVars ⊆ bound := of_decide_eq_true checked
      change ModuleReading.BoundOk (bound ∪ atom.freeVars) (rest.map lowerLiteral) output
      rw [Finset.union_eq_left.mpr already]
      exact loadBody_sound output rest _ next

private theorem query_bound_in_checked_body {Labels : Type} (output : Datum Labels) :
    ∀ (body : List (BodyLiteral (Signature Labels))) (bound : Finset Nat),
      loadBody output bound body = true →
      ∀ (pre : List (Premise (Signature Labels))) atom post,
        body.map lowerLiteral = pre ++ .query atom :: post →
        atom.freeVars ⊆ bound ∪ ModuleReading.bindsAll pre
  | [], _, _, [], _, _, split => by cases split
  | [], _, _, _ :: _, _, _, split => by cases split
  | .intensional _ :: _, _, _, [], _, _, split => by cases split
  | .extensional atom :: rest, bound, ok, [], queried, _, split => by
      have same : atom = queried := Premise.query.inj (List.cons.inj split).1
      subst queried
      rw [loadBody, Bool.and_eq_true_iff] at ok
      simpa [ModuleReading.bindsAll] using
        (of_decide_eq_true ok.1 : atom.freeVars ⊆ bound)
  | .intensional call :: rest, bound, ok, before :: pre, atom, post, split => by
      obtain ⟨same, parts⟩ : Premise.call call.input call.output = before ∧
          rest.map lowerLiteral = pre ++ .query atom :: post := List.cons.inj split
      subst before
      rw [loadBody, Bool.and_eq_true_iff] at ok
      simpa [ModuleReading.bindsAll, ModuleReading.Premise.binds, Finset.union_assoc] using
        query_bound_in_checked_body output rest (bound ∪ call.output.freeVars) ok.2
          pre atom post parts
  | .extensional check :: rest, bound, ok, before :: pre, atom, post, split => by
      obtain ⟨same, parts⟩ : Premise.query check = before ∧
          rest.map lowerLiteral = pre ++ .query atom :: post := List.cons.inj split
      subst before
      rw [loadBody, Bool.and_eq_true_iff] at ok
      have already : check.freeVars ⊆ bound := of_decide_eq_true ok.1
      simpa [ModuleReading.bindsAll, ModuleReading.Premise.binds, ← Finset.union_assoc,
        Finset.union_eq_left.mpr already] using
        query_bound_in_checked_body output rest bound ok.2 pre atom post parts

def compileRule? {Labels : Type} (modes : Modes) (rule : HornCertificate.Rule) :
    Option (Clause (Signature Labels)) := do
  let .intensional head ← lowerCall? modes rule.head | none
  let body ← rule.body.mapM (lowerCall? modes)
  if loadBody head.output head.input.freeVars body then pure ⟨head, body⟩ else none

theorem compileRule?_components {Labels : Type} {modes : Modes}
    {source : HornCertificate.Rule} {result : Clause (Signature Labels)}
    (compiled : compileRule? modes source = some result) :
    lowerCall? modes source.head = some (.intensional result.head) ∧
      source.body.mapM (lowerCall? modes) = some result.body ∧
      loadBody result.head.output result.head.input.freeVars result.body = true := by
  cases headEq : lowerCall? (Labels := Labels) modes source.head with
  | none => simp [compileRule?, headEq] at compiled
  | some literal =>
      cases literal with
      | extensional atom => simp [compileRule?, headEq] at compiled
      | intensional head =>
          cases bodyEq : source.body.mapM (lowerCall? (Labels := Labels) modes) with
          | none => simp [compileRule?, headEq, bodyEq] at compiled
          | some body =>
              by_cases accepted : loadBody head.output head.input.freeVars body = true
              · have same : ⟨head, body⟩ = result := by simpa [compileRule?, headEq, bodyEq, accepted] using compiled
                subst result
                exact ⟨rfl, rfl, accepted⟩
              · simp [compileRule?, headEq, bodyEq, accepted] at compiled

theorem compileRule?_rangeRestricted {Labels : Type} {modes : Modes}
    {source : HornCertificate.Rule} {result : Clause (Signature Labels)}
    (compiled : compileRule? modes source = some result) :
    RangeRestricted (lower (fun _ : Unit => result) ()) :=
  (ModuleReading.rangeRestricted_iff_boundOk (lower (fun _ : Unit => result) ())).mpr
    (loadBody_sound result.head.output result.body result.head.input.freeVars
      (compileRule?_components compiled).2.2)

/-- A compiled external guard never supplies a new variable: even the
reference fact query can only check readings already made. -/
theorem compileRule?_queriesBound {Labels : Type} {modes : Modes}
    {source : HornCertificate.Rule} {result : Clause (Signature Labels)}
    (compiled : compileRule? modes source = some result) :
    QueriesBound (lower (fun _ : Unit => result) ()) :=
  query_bound_in_checked_body result.head.output result.body result.head.input.freeVars
    (compileRule?_components compiled).2.2

def compileProgram? {Labels : Type} (modes : Modes) (program : HornCertificate.Program) :
    Option (List (Clause (Signature Labels))) :=
  program.mapM (compileRule? modes)

def compileSource? {Labels : Type} (modes : Modes)
    (sources : List Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.Source) :
    Option (List (Clause (Signature Labels))) :=
  (CanonicalSourceHornElaboration.elaborateProgram? sources).bind (compileProgram? modes)

theorem compileProgram?_at {Labels : Type} {modes : Modes}
    {source : HornCertificate.Program} {target : List (Clause (Signature Labels))}
    (compiled : compileProgram? modes source = some target) {i : Nat} :
    source[i]?.bind (compileRule? modes) = target[i]? :=
  option_mapM_getElem? (compileRule? modes) compiled i

theorem compileProgram?_length_and_scope {Labels : Type} (modes : Modes)
    (source : HornCertificate.Program) {target : List (Clause (Signature Labels))}
    (compiled : compileProgram? modes source = some target) :
    target.length = source.length ∧
      ∀ clause ∈ target, RangeRestricted (lower (fun _ : Unit => clause) ()) := by
  have paired := option_mapM_forall₂ (compileRule? modes) source target compiled
  refine ⟨paired.length_eq.symm, ?_⟩
  intro clause member
  obtain ⟨_, _, one⟩ := option_mapM_origin (compileRule? modes) source target compiled clause member
  exact compileRule?_rangeRestricted one

/-- From the closed authored composition, a successful result covers one
module rule for every source rule. No malformed rule is silently skipped. -/
theorem compileSource?_length_and_scope {Labels : Type} {modes : Modes}
    {sources : List Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.Source}
    {target : List (Clause (Signature Labels))}
    (compiled : compileSource? modes sources = some target) :
    target.length = (CanonicalSourceHornElaboration.compositionRewrites sources).length ∧
      ∀ clause ∈ target, RangeRestricted (lower (fun _ : Unit => clause) ()) := by
  cases parsed : CanonicalSourceHornElaboration.elaborateProgram? sources with
  | none => simp [compileSource?, parsed] at compiled
  | some source =>
      have emitted : compileProgram? modes source = some target := by
        simpa [compileSource?, parsed] using compiled
      obtain ⟨length, rangeSafe⟩ := compileProgram?_length_and_scope modes source emitted
      exact ⟨length.trans (CanonicalSourceHornElaboration.elaborateProgram?_preserves_length parsed),
        rangeSafe⟩

#print axioms loadBody_sound
#print axioms compileRule?_components
#print axioms compileRule?_rangeRestricted
#print axioms compileRule?_queriesBound
#print axioms compileProgram?_at
#print axioms compileProgram?_length_and_scope
#print axioms compileSource?_length_and_scope

end Mettapedia.GSLT.Compilation.CanonicalHornModule
