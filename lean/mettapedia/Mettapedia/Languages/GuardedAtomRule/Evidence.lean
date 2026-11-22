import Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel
import Mettapedia.OSLF.Syntax.BindingWireBinary
import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Emission
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding

/-!
# Explicit guarded atom-rule evidence

This checker admits literal Atom articles for the independently specified
conditional Atom profile: original rule and query occurrences, sequential
freshness and recursive child guards, matching and the original assignment substitution,
and the three declared Atom primitive services. It also checks callable
readiness while keeping the original body separate from its bindings.

Every row names a local checking rule and retains its intermediate values.
References select earlier rows, including repeated premise uses; they do not
identify source occurrences or impose a language result order. The declaration
authority is exactly the supplied source rows and fixed primitive registration.
This is a guarded atom-rule firing calculus. It does not specify HE or PeTTa
evaluation: root firing does not supply nested argument evaluation, and its
`rule!`, `relation!` and `builtin!` declarations are this profile's source forms.
The source judgments are studied as their own calculus; no upstream dialect adequacy is assumed.

The explicit structural work account applies after local rule/word admission
and materialization. It charges literal comparison, lookup and copying,
including unused rows and repeated premise occurrences. Source expansion,
text reading, rule and address encoding, and host execution time are separate.
-/

set_option autoImplicit false

open Mettapedia.Languages.MeTTa

open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation
open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.NativeTypes.Certificates

namespace Physical
open Mettapedia.OSLF.Binding.WireCodec
def name (value : String) : List Bool := Binary.Triples.encode (Binary.encodeWith Codec.string value)
theorem name_injective : Function.Injective name := Binary.Triples.original_injective Codec.string
end Physical

/-- Explicit intermediate values belong to judgments, so references must
recheck the whole incoming/outgoing assignment and every emitted Atom. -/
inductive Judgment where
  | wordNe (first second : List Bool)
  | nameNe (first second : String)
  | lookup (bindings : Subst) (name : String) (result : Option Atom)
  | substitute (bindings : Subst) (input output : Atom)
  | substituteList (bindings : Subst) (input output : List Atom)
  | fresh (name : String) (value : Atom)
  | freshList (name : String) (values : List Atom)
  | ordinary (patterns : List Atom)
  | unquoted (pattern : Atom)
  | structural (initial : Subst) (pattern value : Atom) (final : Subst)
  | value (initial : Subst) (pattern value : Atom) (final : Subst)
  | values (initial : Subst) (patterns values : List Atom) (final : Subst)
  | binding (initial : Subst) (pattern value : Atom) (final : Subst)
  | guard (initial : Subst) (name : String) (subject : Atom)
  deriving DecidableEq

/-- All code fields are literal data. No field is a semantic proof, matcher
result, substitution equality, or whole-service authority certificate. -/
inductive Rule where
  | neNilCons (bit : Bool) (rest : List Bool)
  | neConsNil (bit : Bool) (rest : List Bool)
  | neFalseTrue (first second : List Bool)
  | neTrueFalse (first second : List Bool)
  | nePrefix (bit : Bool) (first second : List Bool)
  | neName (first second : String)
  | lookupNil (name : String)
  | lookupHead (name : String) (value : Atom) (rest : Subst)
  | lookupSkip (name other : String) (value : Atom) (rest : Subst) (result : Option Atom)
  | substUnbound (bindings : Subst) (name : String)
  | substBound (bindings : Subst) (name : String) (value : Atom)
  | substSymbol (bindings : Subst) (name : String)
  | substGrounded (bindings : Subst) (value : GroundedValue)
  | substExpression (bindings : Subst) (inputs outputs : List Atom)
  | substNil (bindings : Subst)
  | substCons (bindings : Subst) (input output : Atom) (inputs outputs : List Atom)
  | freshVar (name other : String)
  | freshSymbol (name symbol : String)
  | freshGrounded (name : String) (value : GroundedValue)
  | freshExpression (name : String) (values : List Atom)
  | freshNil (name : String)
  | freshCons (name : String) (value : Atom) (values : List Atom)
  | ordinaryNil
  | ordinaryOne (a : Atom)
  | ordinaryTwo (a b : Atom)
  | ordinaryLong (a b c d : Atom) (rest : List Atom)
  | ordinaryVar (name : String) (a b : Atom)
  | ordinaryGrounded (value : GroundedValue) (a b : Atom)
  | ordinaryExpression (fields : List Atom) (a b : Atom)
  | ordinarySymbol (name : String) (a b : Atom)
  | unquotedVar (name : String)
  | unquotedSymbol (name : String)
  | unquotedGrounded (value : GroundedValue)
  | unquotedNil
  | unquotedOne (a : Atom)
  | unquotedLong (a b c : Atom) (rest : List Atom)
  | unquotedHeadVar (name : String) (a : Atom)
  | unquotedHeadGrounded (value : GroundedValue) (a : Atom)
  | unquotedHeadExpression (fields : List Atom) (a : Atom)
  | unquotedHeadSymbol (name : String) (a : Atom)
  | matchFresh (initial : Subst) (name : String) (value : Atom)
  | matchBound (initial : Subst) (name : String) (value : Atom)
  | matchSymbol (initial : Subst) (name : String)
  | matchGrounded (initial : Subst) (value : GroundedValue)
  | matchNil (initial : Subst)
  | matchCons (initial middle final : Subst) (pattern value : Atom) (patterns values : List Atom)
  | valueCons (initial middle final : Subst) (first rest head : Atom) (tail : List Atom)
  | valueExpression (initial final : Subst) (patterns values : List Atom)
  | valueVar (initial final : Subst) (name : String) (value : Atom)
  | valueSymbol (initial final : Subst) (name : String) (value : Atom)
  | valueGrounded (initial final : Subst) (ground : GroundedValue) (value : Atom)
  | valuesNil (initial : Subst)
  | valuesCons (initial middle final : Subst) (pattern value : Atom) (patterns values : List Atom)
  | bindingQuoted (initial final : Subst) (literal value : Atom)
  | bindingOrdinary (initial final : Subst) (pattern value : Atom)
  | guardUnbound (initial : Subst) (name : String) (subject instantiated : Atom)
  | guardCaptured (initial : Subst) (name resolved : String) (subject instantiated : Atom)
  deriving DecidableEq

def conclusion : Rule → Judgment
  | .neNilCons b bs => .wordNe [] (b :: bs)
  | .neConsNil b bs => .wordNe (b :: bs) []
  | .neFalseTrue xs ys => .wordNe (false :: xs) (true :: ys)
  | .neTrueFalse xs ys => .wordNe (true :: xs) (false :: ys)
  | .nePrefix b xs ys => .wordNe (b :: xs) (b :: ys)
  | .neName a b => .nameNe a b
  | .lookupNil name => .lookup [] name none
  | .lookupHead name value rest => .lookup ((name, value) :: rest) name (some value)
  | .lookupSkip name other value rest result => .lookup ((other, value) :: rest) name result
  | .substUnbound bindings name => .substitute bindings (.var name) (.var name)
  | .substBound bindings name value => .substitute bindings (.var name) value
  | .substSymbol bindings name => .substitute bindings (.symbol name) (.symbol name)
  | .substGrounded bindings value => .substitute bindings (.grounded value) (.grounded value)
  | .substExpression bindings inputs outputs => .substitute bindings (.expression inputs) (.expression outputs)
  | .substNil bindings => .substituteList bindings [] []
  | .substCons bindings input output inputs outputs => .substituteList bindings (input :: inputs) (output :: outputs)
  | .freshVar name other => .fresh name (.var other)
  | .freshSymbol name symbol => .fresh name (.symbol symbol)
  | .freshGrounded name value => .fresh name (.grounded value)
  | .freshExpression name values => .fresh name (.expression values)
  | .freshNil name => .freshList name []
  | .freshCons name value values => .freshList name (value :: values)
  | .ordinaryNil => .ordinary []
  | .ordinaryOne a => .ordinary [a]
  | .ordinaryTwo a b => .ordinary [a, b]
  | .ordinaryLong a b c d rest => .ordinary (a :: b :: c :: d :: rest)
  | .ordinaryVar name a b => .ordinary [.var name, a, b]
  | .ordinaryGrounded value a b => .ordinary [.grounded value, a, b]
  | .ordinaryExpression fields a b => .ordinary [.expression fields, a, b]
  | .ordinarySymbol name a b => .ordinary [.symbol name, a, b]
  | .unquotedVar name => .unquoted (.var name)
  | .unquotedSymbol name => .unquoted (.symbol name)
  | .unquotedGrounded value => .unquoted (.grounded value)
  | .unquotedNil => .unquoted (.expression [])
  | .unquotedOne a => .unquoted (.expression [a])
  | .unquotedLong a b c rest => .unquoted (.expression (a :: b :: c :: rest))
  | .unquotedHeadVar name a => .unquoted (.expression [.var name, a])
  | .unquotedHeadGrounded value a => .unquoted (.expression [.grounded value, a])
  | .unquotedHeadExpression fields a => .unquoted (.expression [.expression fields, a])
  | .unquotedHeadSymbol name a => .unquoted (.expression [.symbol name, a])
  | .matchFresh initial name value => .structural initial (.var name) value ((name, value) :: initial)
  | .matchBound initial name value => .structural initial (.var name) value initial
  | .matchSymbol initial name => .structural initial (.symbol name) (.symbol name) initial
  | .matchGrounded initial value => .structural initial (.grounded value) (.grounded value) initial
  | .matchNil initial => .structural initial (.expression []) (.expression []) initial
  | .matchCons initial _middle final pattern value patterns values =>
      .structural initial (.expression (pattern :: patterns)) (.expression (value :: values)) final
  | .valueCons initial _middle final first rest head tail =>
      .value initial (.expression [.symbol "cons", first, rest]) (.expression (head :: tail)) final
  | .valueExpression initial final patterns values => .value initial (.expression patterns) (.expression values) final
  | .valueVar initial final name value => .value initial (.var name) value final
  | .valueSymbol initial final name value => .value initial (.symbol name) value final
  | .valueGrounded initial final ground value => .value initial (.grounded ground) value final
  | .valuesNil initial => .values initial [] [] initial
  | .valuesCons initial _middle final pattern value patterns values =>
      .values initial (pattern :: patterns) (value :: values) final
  | .bindingQuoted initial final literal value => .binding initial (.expression [.symbol "quote", literal]) value final
  | .bindingOrdinary initial final pattern value => .binding initial pattern value final
  | .guardUnbound initial name subject _ => .guard initial name subject
  | .guardCaptured initial name _ subject _ => .guard initial name subject

def premises : Rule → List Judgment
  | .nePrefix _ xs ys => [.wordNe xs ys]
  | .neName a b => [.wordNe (Physical.name a) (Physical.name b)]
  | .lookupSkip name other _ rest result => [.nameNe other name, .lookup rest name result]
  | .substUnbound bindings name => [.lookup bindings name none]
  | .substBound bindings name value => [.lookup bindings name (some value)]
  | .substExpression bindings inputs outputs => [.substituteList bindings inputs outputs]
  | .substCons bindings input output inputs outputs =>
      [.substitute bindings input output, .substituteList bindings inputs outputs]
  | .freshVar name other => [.nameNe name other]
  | .freshExpression name values => [.freshList name values]
  | .freshCons name value values => [.fresh name value, .freshList name values]
  | .ordinarySymbol name _ _ => [.nameNe name "cons"]
  | .unquotedHeadSymbol name _ => [.nameNe name "quote"]
  | .matchFresh initial name _ => [.lookup initial name none]
  | .matchBound initial name value => [.lookup initial name (some value)]
  | .matchCons initial middle final pattern value patterns values =>
      [.structural initial pattern value middle,
       .structural middle (.expression patterns) (.expression values) final]
  | .valueCons initial middle final first rest head tail =>
      [.value initial first head middle, .value middle rest (.expression tail) final]
  | .valueExpression initial final patterns values => [.ordinary patterns, .values initial patterns values final]
  | .valueVar initial final name value => [.structural initial (.var name) value final]
  | .valueSymbol initial final name value => [.structural initial (.symbol name) value final]
  | .valueGrounded initial final ground value => [.structural initial (.grounded ground) value final]
  | .valuesCons initial middle final pattern value patterns values =>
      [.value initial pattern value middle, .values middle patterns values final]
  | .bindingQuoted initial final literal value => [.structural initial literal value final]
  | .bindingOrdinary initial final pattern value => [.unquoted pattern, .value initial pattern value final]
  | .guardUnbound initial name subject instantiated =>
      [.lookup initial name none, .substitute initial subject instantiated, .fresh name instantiated]
  | .guardCaptured initial name resolved subject instantiated =>
      [.lookup initial name (some (.var resolved)), .substitute initial subject instantiated,
       .fresh resolved instantiated]
  | _ => []

def presentation : Presentation := ⟨Judgment, Rule, conclusion, premises⟩

instance : DecidableEq presentation.Judgment := inferInstanceAs (DecidableEq Judgment)

/-- Meaning is fixed by the original source relations and operators. -/
def Meaning : Judgment → Prop
  | .wordNe a b => a ≠ b
  | .nameNe a b => a ≠ b
  | .lookup bindings name result => Subst.lookup bindings name = result
  | .substitute bindings input output => applySubst bindings input = output
  | .substituteList bindings input output => applySubst.applySubstList bindings input = output
  | .fresh name value => name ∉ atomFreeVars value
  | .freshList name values => name ∉ atomFreeVars.atomFreeVarsList values
  | .ordinary patterns => ∀ first rest, patterns ≠ [.symbol "cons", first, rest]
  | .unquoted pattern => ∀ literal, pattern ≠ .expression [.symbol "quote", literal]
  | .structural initial pattern value final => MatchAtomRel initial pattern value final
  | .value initial pattern value final => SpaceSemantics.ValueMatch initial pattern value final
  | .values initial patterns values final => SpaceSemantics.ValueMatches initial patterns values final
  | .binding initial pattern value final => SpaceSemantics.BindingMatch initial pattern value final
  | .guard initial name subject => SourceGuardHolds initial (.freshness name subject)

theorem rule_sound (rule : Rule) (proved : ∀ judgment ∈ premises rule, Meaning judgment) :
    Meaning (conclusion rule) := by
  cases rule <;> simp only [premises, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Meaning, conclusion] at proved ⊢
  case neNilCons | neConsNil | neFalseTrue | neTrueFalse => simp
  case nePrefix => exact fun same => proved (List.cons.inj same).2
  case neName first second => exact fun same => proved (congrArg Physical.name same)
  case lookupNil => rfl
  case lookupHead => simp [Subst.lookup]
  case lookupSkip name other value rest result =>
    have different : (other == name) = false := by exact beq_eq_false_iff_ne.mpr proved.1
    simpa only [Subst.lookup, List.find?, different] using proved.2
  case substUnbound => simp [applySubst, proved]
  case substBound => simp [applySubst, proved]
  case substSymbol | substGrounded | substNil => rfl
  case substExpression => exact congrArg Atom.expression proved
  case substCons => simp only [applySubst.applySubstList, proved.1, proved.2]
  case freshVar => simpa only [atomFreeVars, List.mem_singleton] using proved
  case freshSymbol | freshGrounded | freshNil => simp [atomFreeVars, atomFreeVars.atomFreeVarsList]
  case freshExpression => exact proved
  case freshCons => simpa only [atomFreeVars.atomFreeVarsList, List.mem_append, not_or] using proved
  case ordinaryNil | ordinaryOne | ordinaryTwo | ordinaryLong | ordinaryVar |
      ordinaryGrounded | ordinaryExpression => simp
  case ordinarySymbol =>
    intro first rest same
    exact proved (Atom.symbol.inj (List.cons.inj same).1)
  case unquotedVar | unquotedSymbol | unquotedGrounded | unquotedNil | unquotedOne |
      unquotedLong | unquotedHeadVar | unquotedHeadGrounded | unquotedHeadExpression => simp
  case unquotedHeadSymbol =>
    intro literal same
    exact proved (Atom.expression.inj same |> List.cons.inj |>.1 |> Atom.symbol.inj)
  case matchFresh => exact .var_fresh proved
  case matchBound => exact .var_bound proved
  case matchSymbol => exact .symbol
  case matchGrounded => exact .grounded
  case matchNil => exact .expr_nil
  case matchCons => exact .expr_cons proved.1 proved.2
  case valueCons => exact .cons proved.1 proved.2
  case valueExpression => exact .expression proved.1 proved.2
  case valueVar | valueSymbol | valueGrounded => exact .atomic (by intro _ impossible; cases impossible) proved
  case valuesNil => exact .nil _
  case valuesCons => exact .cons proved.1 proved.2
  case bindingQuoted => exact .quoted proved
  case bindingOrdinary => exact .ordinary proved.1 proved.2
  case guardUnbound => exact .unbound proved.1 (by rw [proved.2.1]; exact proved.2.2)
  case guardCaptured => exact .captured proved.1 (proved.2.1.symm ▸ proved.2.2)

theorem derivation_sound {judgment : Judgment} (proof : presentation.Derivation judgment) : Meaning judgment := by
  apply Mettapedia.TypeTheory.JudgmentDerivation.Derivation.rec
    (motive := fun judgment _ => Meaning judgment) (t := proof)
  intro judgment rule children ih
  rcases rule with ⟨rule, same⟩
  cases same
  apply rule_sound rule
  intro premise member
  obtain ⟨position, atPosition⟩ := List.mem_iff_get.mp member
  simpa only [presentation, Presentation.signature, atPosition] using ih ⟨position⟩

abbrev Derivation := presentation.Derivation

private def node0 (rule : Rule) (shape : premises rule = []) : Derivation (conclusion rule) :=
  .node ⟨rule, rfl⟩ fun position => by
    have impossible := position.down.isLt
    change position.down.val < (premises rule).length at impossible
    rw [shape] at impossible
    exact (Nat.not_lt_zero _ impossible).elim

private def node1 (rule : Rule) {first : Judgment} (shape : premises rule = [first])
    (child : Derivation first) : Derivation (conclusion rule) :=
  .node ⟨rule, rfl⟩ fun position => by
    have bound := position.down.isLt
    change position.down.val < (premises rule).length at bound
    rw [shape] at bound
    have zero : position.down.val = 0 := by simpa using bound
    change Derivation ((premises rule).get position.down)
    have selected : (premises rule).get position.down = first := by
      change (premises rule)[position.down.val] = first
      simp only [shape, zero, List.getElem_cons_zero]
    exact selected.symm ▸ child

private def node2 (rule : Rule) {first second : Judgment} (shape : premises rule = [first, second])
    (left : Derivation first) (right : Derivation second) : Derivation (conclusion rule) :=
  .node ⟨rule, rfl⟩ fun position => by
    have bound := position.down.isLt
    change position.down.val < (premises rule).length at bound
    rw [shape] at bound
    change Derivation ((premises rule).get position.down)
    by_cases zero : position.down.val = 0
    · have selected : (premises rule).get position.down = first := by
        change (premises rule)[position.down.val] = first
        simp only [shape, zero, List.getElem_cons_zero]
      exact selected.symm ▸ left
    · have one : position.down.val = 1 := by simp only [List.length_cons, List.length_nil] at bound; omega
      have selected : (premises rule).get position.down = second := by
        change (premises rule)[position.down.val] = second
        simp only [shape, one, List.getElem_cons_succ, List.getElem_cons_zero]
      exact selected.symm ▸ right

private def node3 (rule : Rule) {first second third : Judgment}
    (shape : premises rule = [first, second, third])
    (a : Derivation first) (b : Derivation second) (c : Derivation third) : Derivation (conclusion rule) :=
  .node ⟨rule, rfl⟩ fun position => by
    have bound := position.down.isLt
    change position.down.val < (premises rule).length at bound
    rw [shape] at bound
    change Derivation ((premises rule).get position.down)
    by_cases zero : position.down.val = 0
    · have selected : (premises rule).get position.down = first := by
        change (premises rule)[position.down.val] = first
        simp only [shape, zero, List.getElem_cons_zero]
      exact selected.symm ▸ a
    · by_cases one : position.down.val = 1
      · have selected : (premises rule).get position.down = second := by
          change (premises rule)[position.down.val] = second
          simp only [shape, one, List.getElem_cons_succ, List.getElem_cons_zero]
        exact selected.symm ▸ b
      · have two : position.down.val = 2 := by simp only [List.length_cons, List.length_nil] at bound; omega
        have selected : (premises rule).get position.down = third := by
          change (premises rule)[position.down.val] = third
          simp only [shape, two, List.getElem_cons_succ, List.getElem_cons_zero]
        exact selected.symm ▸ c

def deriveWordNe : (first second : List Bool) → first ≠ second → Derivation (.wordNe first second)
  | [], [], different => (different rfl).elim
  | [], bit :: rest, _ => node0 (.neNilCons bit rest) rfl
  | bit :: rest, [], _ => node0 (.neConsNil bit rest) rfl
  | false :: first, true :: second, _ => node0 (.neFalseTrue first second) rfl
  | true :: first, false :: second, _ => node0 (.neTrueFalse first second) rfl
  | false :: first, false :: second, different =>
      node1 (.nePrefix false first second) rfl
        (deriveWordNe first second (fun same => different (congrArg (false :: ·) same)))
  | true :: first, true :: second, different =>
      node1 (.nePrefix true first second) rfl
        (deriveWordNe first second (fun same => different (congrArg (true :: ·) same)))

def deriveNameNe (first second : String) (different : first ≠ second) : Derivation (.nameNe first second) :=
  node1 (.neName first second) rfl
    (deriveWordNe (Physical.name first) (Physical.name second)
      (fun same => different (Physical.name_injective same)))

/-- The construction traverses the original first-match binding list and
emits each skipped unequal name. The proof precondition is not in rule data. -/
def deriveLookup : (bindings : Subst) → (name : String) →
    Derivation (.lookup bindings name (Subst.lookup bindings name))
  | [], name => node0 (.lookupNil name) rfl
  | (other, value) :: rest, name => by
      by_cases same : other = name
      · subst other
        simpa only [conclusion, Subst.lookup, List.find?, beq_self_eq_true, Option.map_some] using
          node0 (.lookupHead name value rest) rfl
      · have different : (other == name) = false := beq_eq_false_iff_ne.mpr same
        simpa only [conclusion, Subst.lookup, List.find?, different] using
          node2 (.lookupSkip name other value rest (Subst.lookup rest name)) rfl
            (deriveNameNe other name same) (deriveLookup rest name)

mutual
  def deriveSubstitution (bindings : Subst) : (input : Atom) →
      Derivation (.substitute bindings input (applySubst bindings input))
    | .var name => by
        cases selected : Subst.lookup bindings name with
        | none =>
            have lookup := deriveLookup bindings name
            rw [selected] at lookup
            simpa only [conclusion, applySubst, selected, Option.getD_none] using
              node1 (.substUnbound bindings name) rfl lookup
        | some value =>
            have lookup := deriveLookup bindings name
            rw [selected] at lookup
            simpa only [conclusion, applySubst, selected, Option.getD_some] using
              node1 (.substBound bindings name value) rfl lookup
    | .symbol name => node0 (.substSymbol bindings name) rfl
    | .grounded value => node0 (.substGrounded bindings value) rfl
    | .expression inputs => node1 (.substExpression bindings inputs (applySubst.applySubstList bindings inputs))
        rfl (deriveSubstitutions bindings inputs)

  def deriveSubstitutions (bindings : Subst) : (inputs : List Atom) →
      Derivation (.substituteList bindings inputs (applySubst.applySubstList bindings inputs))
    | [] => node0 (.substNil bindings) rfl
    | input :: inputs => node2 (.substCons bindings input (applySubst bindings input)
        inputs (applySubst.applySubstList bindings inputs)) rfl
        (deriveSubstitution bindings input) (deriveSubstitutions bindings inputs)
end

mutual
  def deriveFresh (name : String) : (value : Atom) → name ∉ atomFreeVars value → Derivation (.fresh name value)
    | .var other, fresh => node1 (.freshVar name other) rfl
        (deriveNameNe name other (by simpa only [atomFreeVars, List.mem_singleton] using fresh))
    | .symbol symbol, _ => node0 (.freshSymbol name symbol) rfl
    | .grounded value, _ => node0 (.freshGrounded name value) rfl
    | .expression values, fresh => node1 (.freshExpression name values) rfl (deriveFreshList name values fresh)

  def deriveFreshList (name : String) : (values : List Atom) →
      name ∉ atomFreeVars.atomFreeVarsList values → Derivation (.freshList name values)
    | [], _ => node0 (.freshNil name) rfl
    | value :: values, fresh =>
        let both := (not_or.mp (show ¬ (name ∈ atomFreeVars value ∨
          name ∈ atomFreeVars.atomFreeVarsList values) by
            simpa only [atomFreeVars.atomFreeVarsList, List.mem_append] using fresh))
        node2 (.freshCons name value values) rfl
          (deriveFresh name value both.1) (deriveFreshList name values both.2)
end

/-- Elaboration may execute the original matcher to find intermediate values;
the resulting article checks only the local constructors above. -/
def deriveStructural {initial final : Subst} {pattern value : Atom}
    (computed : matchAtom initial pattern value = some final) :
    Derivation (.structural initial pattern value final) := by
  match pattern, value with
  | .var name, value =>
      cases selected : Subst.lookup initial name with
      | none =>
          have same : (name, value) :: initial = final := by simpa only [matchAtom, selected, Option.some.injEq] using computed
          subst final
          have lookup := deriveLookup initial name
          rw [selected] at lookup
          exact node1 (.matchFresh initial name value) rfl lookup
      | some actual =>
          by_cases same : value == actual
          · have equal := Atom.eq_of_beq_eq_true same
            subst actual
            have assignments : initial = final := by simp only [matchAtom, selected, same, ↓reduceIte, Option.some.injEq] at computed; exact computed
            subst final
            have lookup := deriveLookup initial name
            rw [selected] at lookup
            exact node1 (.matchBound initial name value) rfl lookup
          · simp only [matchAtom, selected, same] at computed
            contradiction
  | .symbol name, .symbol other =>
      by_cases same : name = other
      · subst other
        have assignments : initial = final := by simpa only [matchAtom, beq_self_eq_true, ↓reduceIte, Option.some.injEq] using computed
        subst final
        exact node0 (.matchSymbol initial name) rfl
      · have different : (name == other) = false := beq_eq_false_iff_ne.mpr same
        simp only [matchAtom, different, Bool.false_eq_true, ↓reduceIte] at computed
        contradiction
  | .grounded first, .grounded second =>
      by_cases same : first = second
      · subst second
        have assignments : initial = final := by simpa only [matchAtom, beq_self_eq_true, ↓reduceIte, Option.some.injEq] using computed
        subst final
        exact node0 (.matchGrounded initial first) rfl
      · have different : (first == second) = false := beq_eq_false_iff_ne.mpr same
        simp only [matchAtom, different, Bool.false_eq_true, ↓reduceIte] at computed
        contradiction
  | .expression patterns, .expression values =>
      exact deriveStructuralList computed
  | .symbol _, .var _ | .symbol _, .grounded _ | .symbol _, .expression _ |
    .grounded _, .var _ | .grounded _, .symbol _ | .grounded _, .expression _ |
    .expression _, .var _ | .expression _, .symbol _ | .expression _, .grounded _ =>
      simp only [matchAtom] at computed
      contradiction
where
  deriveStructuralList {initial final : Subst} {patterns values : List Atom}
      (computed : matchAtom.matchAtomList initial patterns values = some final) :
      Derivation (.structural initial (.expression patterns) (.expression values) final) := by
    match patterns, values with
    | [], [] =>
        have same : initial = final := by simpa only [matchAtom.matchAtomList, Option.some.injEq] using computed
        subst final
        exact node0 (.matchNil initial) rfl
    | pattern :: patterns, value :: values =>
        cases head : matchAtom initial pattern value with
        | none => simp only [matchAtom.matchAtomList, head] at computed; contradiction
        | some middle =>
            have tail : matchAtom.matchAtomList middle patterns values = some final := by
              simpa only [matchAtom.matchAtomList, head] using computed
            exact node2 (.matchCons initial middle final pattern value patterns values) rfl
              (deriveStructural head) (deriveStructuralList tail)
    | [], _ :: _ | _ :: _, [] => simp only [matchAtom.matchAtomList] at computed; contradiction

def deriveOrdinary : (patterns : List Atom) → Meaning (.ordinary patterns) → Derivation (.ordinary patterns)
  | [], _ => node0 .ordinaryNil rfl
  | [a], _ => node0 (.ordinaryOne a) rfl
  | [a, b], _ => node0 (.ordinaryTwo a b) rfl
  | a :: b :: c :: d :: rest, _ => node0 (.ordinaryLong a b c d rest) rfl
  | [.var name, a, b], _ => node0 (.ordinaryVar name a b) rfl
  | [.grounded value, a, b], _ => node0 (.ordinaryGrounded value a b) rfl
  | [.expression fields, a, b], _ => node0 (.ordinaryExpression fields a b) rfl
  | [.symbol name, a, b], ordinary => node1 (.ordinarySymbol name a b) rfl
      (deriveNameNe name "cons" (fun same => ordinary a b (by rw [same])))

def deriveUnquoted : (pattern : Atom) → Meaning (.unquoted pattern) → Derivation (.unquoted pattern)
  | .var name, _ => node0 (.unquotedVar name) rfl
  | .symbol name, _ => node0 (.unquotedSymbol name) rfl
  | .grounded value, _ => node0 (.unquotedGrounded value) rfl
  | .expression [], _ => node0 .unquotedNil rfl
  | .expression [a], _ => node0 (.unquotedOne a) rfl
  | .expression (a :: b :: c :: rest), _ => node0 (.unquotedLong a b c rest) rfl
  | .expression [.var name, a], _ => node0 (.unquotedHeadVar name a) rfl
  | .expression [.grounded value, a], _ => node0 (.unquotedHeadGrounded value a) rfl
  | .expression [.expression fields, a], _ => node0 (.unquotedHeadExpression fields a) rfl
  | .expression [.symbol name, a], unquoted => node1 (.unquotedHeadSymbol name a) rfl
      (deriveNameNe name "quote" (fun same => unquoted a (by rw [same])))

private def consView? : Atom → Option (Atom × Atom)
  | .expression [.symbol "cons", first, rest] => some (first, rest)
  | _ => none

private theorem consView?_exact (pattern first rest : Atom) :
    consView? pattern = some (first, rest) ↔ pattern = .expression [.symbol "cons", first, rest] := by
  unfold consView?
  split
  · simp_all
  · constructor
    · intro impossible; cases impossible
    · intro same; subst pattern; simp_all

private def quoteView? : Atom → Option Atom
  | .expression [.symbol "quote", literal] => some literal
  | _ => none

private theorem quoteView?_exact (pattern literal : Atom) :
    quoteView? pattern = some literal ↔ pattern = .expression [.symbol "quote", literal] := by
  unfold quoteView?
  split
  · simp_all
  · constructor
    · intro impossible; cases impossible
    · intro same; subst pattern; simp_all

mutual
  def deriveValue {initial final : Subst} {pattern value : Atom}
      (computed : SpaceSemantics.matchValue initial pattern value = some final) :
      Derivation (.value initial pattern value final) := by
    cases consView : consView? pattern with
    | some fields =>
      rcases fields with ⟨first, rest⟩
      have shape := (consView?_exact pattern first rest).mp consView
      subst pattern
      cases value with
      | expression values =>
          cases values with
          | nil => simp only [SpaceSemantics.matchValue] at computed; contradiction
          | cons head tail =>
              cases headMatch : SpaceSemantics.matchValue initial first head with
              | none => simp only [SpaceSemantics.matchValue, headMatch, bind, Option.bind] at computed; contradiction
              | some middle =>
                  have restMatch : SpaceSemantics.matchValue middle rest (.expression tail) = some final := by
                    simpa only [SpaceSemantics.matchValue, headMatch, bind, Option.bind] using computed
                  exact node2 (.valueCons initial middle final first rest head tail) rfl
                    (deriveValue headMatch) (deriveValue restMatch)
      | var _ | symbol _ | grounded _ => simp only [SpaceSemantics.matchValue] at computed; contradiction
    | none =>
      cases pattern with
      | var name =>
        exact node1 (.valueVar initial final name value) rfl
          (deriveStructural (by simpa only [SpaceSemantics.matchValue] using computed))
      | symbol name =>
        exact node1 (.valueSymbol initial final name value) rfl
          (deriveStructural (by simpa only [SpaceSemantics.matchValue] using computed))
      | grounded ground =>
        exact node1 (.valueGrounded initial final ground value) rfl
          (deriveStructural (by simpa only [SpaceSemantics.matchValue] using computed))
      | expression patterns =>
          have ordinary : Meaning (.ordinary patterns) := by
            intro first rest same
            have found := (consView?_exact (.expression patterns) first rest).mpr (congrArg Atom.expression same)
            rw [consView] at found
            cases found
          cases value with
          | expression values =>
              have matched : SpaceSemantics.matchValue.matchValues initial patterns values = some final := by
                rw [SpaceSemantics.matchValue] at computed
                · exact computed
                · intro first rest _ _ same _; exact ordinary first rest same
                · exact ordinary
              exact node2 (.valueExpression initial final patterns values) rfl
                (deriveOrdinary patterns ordinary) (deriveValues matched)
          | var _ | symbol _ | grounded _ =>
              have impossible : False := by
                have source := SpaceSemantics.matchValue_sound computed
                cases source
                rename_i notExpression _
                exact notExpression _ rfl
              exact impossible.elim
    termination_by sizeOf pattern

  def deriveValues {initial final : Subst} {patterns values : List Atom}
      (computed : SpaceSemantics.matchValue.matchValues initial patterns values = some final) :
      Derivation (.values initial patterns values final) := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            have same : initial = final := by simpa only [SpaceSemantics.matchValue.matchValues, Option.some.injEq] using computed
            subst final
            exact node0 (.valuesNil initial) rfl
        | cons _ _ => simp only [SpaceSemantics.matchValue.matchValues] at computed; contradiction
    | cons pattern patterns =>
        cases values with
        | nil => simp only [SpaceSemantics.matchValue.matchValues] at computed; contradiction
        | cons value values =>
            cases headMatch : SpaceSemantics.matchValue initial pattern value with
            | none => simp only [SpaceSemantics.matchValue.matchValues, headMatch, bind, Option.bind] at computed; contradiction
            | some middle =>
                have tail : SpaceSemantics.matchValue.matchValues middle patterns values = some final := by
                  simpa only [SpaceSemantics.matchValue.matchValues, headMatch, bind, Option.bind] using computed
                exact node2 (.valuesCons initial middle final pattern value patterns values) rfl
                  (deriveValue headMatch) (deriveValues tail)
    termination_by sizeOf patterns
end

def deriveBinding {initial final : Subst} {pattern value : Atom}
    (computed : SpaceSemantics.matchBinding initial pattern value = some final) :
    Derivation (.binding initial pattern value final) := by
  cases quoted : quoteView? pattern with
  | some literal =>
    have shape := (quoteView?_exact pattern literal).mp quoted
    subst pattern
    exact node1 (.bindingQuoted initial final literal value) rfl (deriveStructural computed)
  | none =>
    have ordinary : Meaning (.unquoted pattern) := by
      intro literal same
      have found := (quoteView?_exact pattern literal).mpr same
      rw [quoted] at found
      cases found
    have matched : SpaceSemantics.matchValue initial pattern value = some final := by
      rw [SpaceSemantics.matchBinding_ordinary _ _ _ ordinary] at computed
      exact computed
    exact node2 (.bindingOrdinary initial final pattern value) rfl
      (deriveUnquoted pattern ordinary) (deriveValue matched)

def deriveGuard (initial : Subst) (name : String) (subject : Atom)
    (checked : matchSourceGuard initial (.freshness name subject) = true) :
    Derivation (.guard initial name subject) := by
  cases selected : Subst.lookup initial name with
  | none =>
      have fresh : name ∉ atomFreeVars (applySubst initial subject) := by
        simpa [matchSourceGuard, selected, isAtomFresh] using checked
      have lookup := deriveLookup initial name
      rw [selected] at lookup
      exact node3 (.guardUnbound initial name subject (applySubst initial subject)) rfl
        lookup (deriveSubstitution initial subject) (deriveFresh name _ fresh)
  | some value =>
      cases value with
      | var resolved =>
          have fresh : resolved ∉ atomFreeVars (applySubst initial subject) := by
            simpa [matchSourceGuard, selected, isAtomFresh] using checked
          have lookup := deriveLookup initial name
          rw [selected] at lookup
          exact node3 (.guardCaptured initial name resolved subject (applySubst initial subject)) rfl
            lookup (deriveSubstitution initial subject) (deriveFresh resolved _ fresh)
      | symbol _ | grounded _ | expression _ =>
          simp only [matchSourceGuard, selected] at checked
          contradiction

/-- Every source primitive has a finite explicit article. The construction
retains substitutions and targets that a compressed source proof may omit. -/
theorem meaning_complete (judgment : Judgment) (source : Meaning judgment) :
    Nonempty (Derivation judgment) := by
  cases judgment with
  | wordNe a b => exact ⟨deriveWordNe a b source⟩
  | nameNe a b => exact ⟨deriveNameNe a b source⟩
  | lookup bindings name result =>
      have constructed := deriveLookup bindings name
      rw [show Subst.lookup bindings name = result from source] at constructed
      exact ⟨constructed⟩
  | substitute bindings input output =>
      have constructed := deriveSubstitution bindings input
      rw [show applySubst bindings input = output from source] at constructed
      exact ⟨constructed⟩
  | substituteList bindings input output =>
      have constructed := deriveSubstitutions bindings input
      rw [show applySubst.applySubstList bindings input = output from source] at constructed
      exact ⟨constructed⟩
  | fresh name value => exact ⟨deriveFresh name value source⟩
  | freshList name values => exact ⟨deriveFreshList name values source⟩
  | ordinary patterns => exact ⟨deriveOrdinary patterns source⟩
  | unquoted pattern => exact ⟨deriveUnquoted pattern source⟩
  | structural initial pattern value final => exact ⟨deriveStructural (matchAtom_complete source)⟩
  | value initial pattern value final => exact ⟨deriveValue (SpaceSemantics.matchValue_complete source)⟩
  | values initial patterns values final => exact ⟨deriveValues (SpaceSemantics.matchValues_complete source)⟩
  | binding initial pattern value final => exact ⟨deriveBinding (SpaceSemantics.matchBinding_complete source)⟩
  | guard initial name subject => exact ⟨deriveGuard initial name subject (matchSourceGuard_exact _ _ |>.mpr source)⟩

theorem shared_sound (article : Shared.Certificate presentation) (judgment : Judgment)
    (accepted : Shared.check article judgment = true) : Meaning judgment := by
  obtain ⟨proof, _, _⟩ := Shared.accepted_original article judgment accepted
  exact derivation_sound proof

theorem shared_complete (judgment : Judgment) :
    Meaning judgment ↔ ∃ article : Shared.Certificate presentation, Shared.check article judgment = true := by
  constructor
  · intro source
    obtain ⟨proof⟩ := meaning_complete judgment source
    exact ⟨Shared.emit proof, Shared.emit_checked proof⟩
  · rintro ⟨article, accepted⟩
    exact shared_sound article judgment accepted

def expandValue? (initial : Subst) (pattern value : Atom) : Option (Subst × Shared.Certificate presentation) :=
  match computed : SpaceSemantics.matchValue initial pattern value with
  | none => none
  | some final => some (final, Shared.emit (deriveValue computed))

def expandBinding? (initial : Subst) (pattern value : Atom) : Option (Subst × Shared.Certificate presentation) :=
  match computed : SpaceSemantics.matchBinding initial pattern value with
  | none => none
  | some final => some (final, Shared.emit (deriveBinding computed))

theorem expandValue?_exact (initial : Subst) (pattern value : Atom) (final : Subst) :
    (∃ article, expandValue? initial pattern value = some (final, article) ∧
      Shared.check article (.value initial pattern value final) = true) ↔
      SpaceSemantics.ValueMatch initial pattern value final := by
  constructor
  · rintro ⟨article, _, accepted⟩
    exact shared_sound article _ accepted
  · intro source
    have matched := SpaceSemantics.matchValue_complete source
    refine ⟨Shared.emit (deriveValue matched), ?_, Shared.emit_checked _⟩
    unfold expandValue?
    split
    · rename_i refused
      rw [matched] at refused
      cases refused
    · rename_i actual computed
      have same : actual = final := Option.some.inj (computed.symm.trans matched)
      cases same
      rfl

theorem expandBinding?_exact (initial : Subst) (pattern value : Atom) (final : Subst) :
    (∃ article, expandBinding? initial pattern value = some (final, article) ∧
      Shared.check article (.binding initial pattern value final) = true) ↔
      SpaceSemantics.BindingMatch initial pattern value final := by
  constructor
  · rintro ⟨article, _, accepted⟩
    exact shared_sound article _ accepted
  · intro source
    have matched := SpaceSemantics.matchBinding_complete source
    refine ⟨Shared.emit (deriveBinding matched), ?_, Shared.emit_checked _⟩
    unfold expandBinding?
    split
    · rename_i refused
      rw [matched] at refused
      cases refused
    · rename_i actual computed
      have same : actual = final := Option.some.inj (computed.symm.trans matched)
      cases same
      rfl

namespace Wire
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge

private def boolCodec : Codec Bool := Codec.nat.mapped (fun bit => if bit then 1 else 0)
  (fun value => match value with | 0 => some false | 1 => some true | _ => none)
  (by intro value; cases value <;> rfl)
private def wordCodec := Codec.list boolCodec

def atomCodec : Codec Atom :=
  Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec.mapped
    GroundData.encode GroundData.decode GroundData.decode_encode

def atomsCodec := Codec.list atomCodec
def bindingsCodec := Codec.list (Codec.prod Codec.string atomCodec)
private def optionAtomCodec : Codec (Option Atom) := atomsCodec.mapped Option.toList
  (fun values => match values with | [] => some none | [value] => some (some value) | _ => none)
  (by intro value; cases value <;> rfl)
private def lookupCodec := Codec.prod bindingsCodec (Codec.prod Codec.string optionAtomCodec)
private def substitutionCodec := Codec.prod bindingsCodec (Codec.prod atomCodec atomCodec)
private def substitutionsCodec := Codec.prod bindingsCodec (Codec.prod atomsCodec atomsCodec)
private def matchingCodec := Codec.prod bindingsCodec
  (Codec.prod atomCodec (Codec.prod atomCodec bindingsCodec))
private def matchingsCodec := Codec.prod bindingsCodec
  (Codec.prod atomsCodec (Codec.prod atomsCodec bindingsCodec))
private def guardCodec := Codec.prod bindingsCodec (Codec.prod Codec.string atomCodec)

def putJudgment : Judgment → Data
  | .wordNe a b => .pair (.atom 0) ((Codec.prod wordCodec wordCodec).put (a, b))
  | .nameNe a b => .pair (.atom 1) ((Codec.prod Codec.string Codec.string).put (a, b))
  | .lookup bindings name result => .pair (.atom 2) (lookupCodec.put (bindings, name, result))
  | .substitute bindings input output => .pair (.atom 3) (substitutionCodec.put (bindings, input, output))
  | .substituteList bindings inputs outputs => .pair (.atom 4) (substitutionsCodec.put (bindings, inputs, outputs))
  | .fresh name value => .pair (.atom 5) ((Codec.prod Codec.string atomCodec).put (name, value))
  | .freshList name values => .pair (.atom 6) ((Codec.prod Codec.string atomsCodec).put (name, values))
  | .ordinary patterns => .pair (.atom 7) (atomsCodec.put patterns)
  | .unquoted pattern => .pair (.atom 8) (atomCodec.put pattern)
  | .structural initial pattern value final => .pair (.atom 9) (matchingCodec.put (initial, pattern, value, final))
  | .value initial pattern value final => .pair (.atom 10) (matchingCodec.put (initial, pattern, value, final))
  | .values initial patterns values final => .pair (.atom 11) (matchingsCodec.put (initial, patterns, values, final))
  | .binding initial pattern value final => .pair (.atom 12) (matchingCodec.put (initial, pattern, value, final))
  | .guard initial name subject => .pair (.atom 13) (guardCodec.put (initial, name, subject))

def getJudgment : Data → Option Judgment
  | .pair (.atom 0) fields => (Codec.prod wordCodec wordCodec).get fields |>.map fun (a, b) => .wordNe a b
  | .pair (.atom 1) fields => (Codec.prod Codec.string Codec.string).get fields |>.map fun (a, b) => .nameNe a b
  | .pair (.atom 2) fields => lookupCodec.get fields |>.map fun (bindings, name, result) => .lookup bindings name result
  | .pair (.atom 3) fields => substitutionCodec.get fields |>.map fun (bindings, input, output) => .substitute bindings input output
  | .pair (.atom 4) fields => substitutionsCodec.get fields |>.map fun (bindings, inputs, outputs) => .substituteList bindings inputs outputs
  | .pair (.atom 5) fields => (Codec.prod Codec.string atomCodec).get fields |>.map fun (name, value) => .fresh name value
  | .pair (.atom 6) fields => (Codec.prod Codec.string atomsCodec).get fields |>.map fun (name, values) => .freshList name values
  | .pair (.atom 7) fields => atomsCodec.get fields |>.map .ordinary
  | .pair (.atom 8) fields => atomCodec.get fields |>.map .unquoted
  | .pair (.atom 9) fields => matchingCodec.get fields |>.map fun (initial, pattern, value, final) => .structural initial pattern value final
  | .pair (.atom 10) fields => matchingCodec.get fields |>.map fun (initial, pattern, value, final) => .value initial pattern value final
  | .pair (.atom 11) fields => matchingsCodec.get fields |>.map fun (initial, patterns, values, final) => .values initial patterns values final
  | .pair (.atom 12) fields => matchingCodec.get fields |>.map fun (initial, pattern, value, final) => .binding initial pattern value final
  | .pair (.atom 13) fields => guardCodec.get fields |>.map fun (initial, name, subject) => .guard initial name subject
  | _ => none

theorem getJudgment_putJudgment (judgment : Judgment) : getJudgment (putJudgment judgment) = some judgment := by
  cases judgment <;> simp only [putJudgment, getJudgment, Codec.get_put, Option.map_some]

def judgmentCodec : Codec Judgment := ⟨putJudgment, getJudgment, getJudgment_putJudgment⟩

def coding : Shared.LiteralChecking.Coding presentation.Judgment where
  word judgment := Binary.Triples.encode (Binary.encodeWith judgmentCodec judgment)
  injective := Binary.Triples.original_injective judgmentCodec

end Wire

/-- The paid checker compares the lossless physical words for all explicit
intermediates. Its result is the original generic certificate result. -/
theorem paid_exact (article : Shared.Certificate presentation) (judgment : Judgment) :
    (Shared.LiteralChecking.check Wire.coding article judgment).accepted = Shared.check article judgment :=
  Shared.LiteralChecking.check_exact Wire.coding article judgment

theorem paid_sound (article : Shared.Certificate presentation) (judgment : Judgment)
    (accepted : (Shared.LiteralChecking.check Wire.coding article judgment).accepted = true) :
    Meaning judgment := shared_sound article judgment ((paid_exact article judgment).symm.trans accepted)

theorem paid_complete (judgment : Judgment) : Meaning judgment ↔
    ∃ article : Shared.Certificate presentation,
      (Shared.LiteralChecking.check Wire.coding article judgment).accepted = true := by
  simpa only [paid_exact] using shared_complete judgment

theorem paid_structural_work (article : Shared.Certificate presentation) (judgment : Judgment) :
    (Shared.LiteralChecking.check Wire.coding article judgment).work ≤
      (Shared.LiteralChecking.inputVolume Wire.coding article judgment + 2) *
        (5 * Shared.LiteralChecking.inputVolume Wire.coding article judgment + 10) :=
  Shared.LiteralChecking.check_work_le Wire.coding article judgment

end Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source

open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (signature?)
open ConfigurationEncoding (bindingsData)

open Mettapedia.Languages.MeTTa

def environment (rows : List Atom) : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Environment :=
  ⟨rows, AtomServices.registration, AtomServices.provider⟩

inductive Judgment where
  | primitive (judgment : Evidence.Primitive.Judgment)
  | at (rows : List Atom) (index : Nat) (row : Atom)
  | clause (index : Nat) (left right : Atom) (guards : List Atom)
  | callable (index : Nat) (head : String) (arguments : List Atom) (body : Atom) (guards : List Atom)
  | root (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (subject target : Atom)
  | premise (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (guard : Atom) (initial final : Subst)
  | premises (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (guards : List Atom) (initial final : Subst)
  | query (relation : String) (arguments : List Atom) (initial : Subst) (origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin) (final : Subst)
  | call (head : String) (values : List Atom) (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (index : Nat)
      (bindings : Subst) (body : Atom)
  deriving DecidableEq

inductive Rule where
  | primitive (rule : Evidence.Primitive.Rule)
  | atHead (row : Atom) (rest : List Atom)
  | atTail (head row : Atom) (rest : List Atom) (index : Nat)
  | clauseEquation (index : Nat) (left right : Atom)
  | clauseGuarded (index : Nat) (left right : Atom) (guards : List Atom)
  | callableEquation (index : Nat) (head : String) (arguments : List Atom) (body : Atom)
  | callableGuarded (index : Nat) (head : String) (arguments : List Atom) (body : Atom) (guards : List Atom)
  | root (index : Nat) (proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (left right subject target : Atom)
      (guards : List Atom) (initial final : Subst)
  | fresh (initial : Subst) (name : String) (subject : Atom)
  | child (proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (initial final : Subst) (source instantiated target result : Atom)
  | query (relation : String) (arguments : List Atom) (initial final : Subst) (origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin)
  | premisesNil (initial : Subst)
  | premisesCons (head tail : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (guard : Atom) (guards : List Atom) (initial middle final : Subst)
  | queryRelation (index : Nat) (relation : String) (arguments values : List Atom) (initial final : Subst)
  | queryBuiltin (index : Nat) (relation : String) (arguments values : List Atom) (initial final : Subst)
  | nativeFresh (initial : Subst) (nameSchema subjectSchema : Atom) (name : String) (subject : Atom)
  | nativeValue (initial final innerInitial innerFinal : Subst)
      (bindingsSchema patternSchema valueSchema outputSchema pattern value : Atom)
  | nativeBinding (initial final innerInitial innerFinal : Subst)
      (bindingsSchema patternSchema valueSchema outputSchema pattern value : Atom)
  | call (index : Nat) (head : String) (arguments values : List Atom) (body : Atom)
      (guards : List Atom) (proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (initial final : Subst)
  deriving DecidableEq

def conclusion : Rule → Judgment
  | .primitive rule => .primitive (Evidence.Primitive.conclusion rule)
  | .atHead row rest => .at (row :: rest) 0 row
  | .atTail head row rest index => .at (head :: rest) (index + 1) row
  | .clauseEquation index left right => .clause index left right []
  | .clauseGuarded index left right guards => .clause index left right guards
  | .callableEquation index head arguments body => .callable index head arguments body []
  | .callableGuarded index head arguments body guards => .callable index head arguments body guards
  | .root index proof _ _ subject target _ _ _ => .root (.firing index proof) subject target
  | .fresh initial name subject => .premise .fresh (.expression [.symbol "fresh", .var name, subject]) initial initial
  | .child proof initial final source _ target _ => .premise (.child proof)
      (.expression [.symbol "==", source, target]) initial final
  | .query relation arguments initial final origin =>
      .premise (.query origin) (.expression (.symbol relation :: arguments)) initial final
  | .premisesNil initial => .premises .empty [] initial initial
  | .premisesCons head tail guard guards initial _ final =>
      .premises (.cons head tail) (guard :: guards) initial final
  | .queryRelation index relation arguments _ initial final => .query relation arguments initial (.relation index) final
  | .queryBuiltin index relation arguments _ initial final => .query relation arguments initial (.builtin index) final
  | .nativeFresh initial nameSchema subjectSchema _ _ =>
      .query "metta-atom-fresh-v1" [nameSchema, subjectSchema] initial (.native 0) initial
  | .nativeValue initial final _ _ bindingsSchema patternSchema valueSchema outputSchema _ _ =>
      .query "petta-match-value-v1" [bindingsSchema, patternSchema, valueSchema, outputSchema] initial (.native 0) final
  | .nativeBinding initial final _ _ bindingsSchema patternSchema valueSchema outputSchema _ _ =>
      .query "petta-match-binding-v1" [bindingsSchema, patternSchema, valueSchema, outputSchema] initial (.native 0) final
  | .call index head _ values body _ proof _ final =>
      .call head values (.firing index proof) index final body

def premises (rows : List Atom) : Rule → List Judgment
  | .primitive rule => (Evidence.Primitive.premises rule).map .primitive
  | .atHead _ _ => []
  | .atTail _ row rest index => [.at rest index row]
  | .clauseEquation index left right => [.at rows index (.expression [.symbol "=", left, right])]
  | .clauseGuarded index left right guards => [.at rows index (.expression (.symbol "rule!" :: left :: right :: guards))]
  | .callableEquation index head arguments body =>
      [.at rows index (.expression [.symbol "=", .expression (.symbol head :: arguments), body])]
  | .callableGuarded index head arguments body guards =>
      [.at rows index (.expression (.symbol "rule!" :: .expression (.symbol head :: arguments) :: body :: guards))]
  | .root index proof left right subject target guards initial final =>
      [.clause index left right guards, .primitive (.value [] left subject initial),
       .premises proof guards initial final, .primitive (.substitute final right target)]
  | .fresh initial name subject => [.primitive (.guard initial name subject)]
  | .child proof initial final source instantiated target result =>
      [.primitive (.substitute initial source instantiated), .root proof instantiated result,
       .primitive (.value initial target result final)]
  | .query relation arguments initial final origin =>
      [.primitive (.nameNe relation "fresh"), .primitive (.nameNe relation "=="),
       .query relation arguments initial origin final]
  | .premisesNil _ => []
  | .premisesCons head tail guard guards initial middle final =>
      [.premise head guard initial middle, .premises tail guards middle final]
  | .queryRelation index relation arguments values initial final =>
      [.at rows index (.expression (.symbol "relation!" :: .symbol relation :: values)),
       .primitive (.value initial (.expression arguments) (.expression values) final)]
  | .queryBuiltin index relation arguments values initial final =>
      [.at rows index (.expression (.symbol "builtin!" :: .symbol relation :: values)),
       .primitive (.value initial (.expression arguments) (.expression values) final)]
  | .nativeFresh initial nameSchema subjectSchema name subject =>
      [.primitive (.substitute initial nameSchema (.var name)),
       .primitive (.substitute initial subjectSchema subject), .primitive (.fresh name subject)]
  | .nativeValue initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value =>
      [.primitive (.substitute initial bindingsSchema (bindingsData innerInitial)),
       .primitive (.substitute initial patternSchema pattern), .primitive (.substitute initial valueSchema value),
       .primitive (.value innerInitial pattern value innerFinal),
       .primitive (.value initial outputSchema (bindingsData innerFinal) final)]
  | .nativeBinding initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value =>
      [.primitive (.substitute initial bindingsSchema (bindingsData innerInitial)),
       .primitive (.substitute initial patternSchema pattern), .primitive (.substitute initial valueSchema value),
       .primitive (.binding innerInitial pattern value innerFinal),
       .primitive (.value initial outputSchema (bindingsData innerFinal) final)]
  | .call index head arguments values body guards proof initial final =>
      [.callable index head arguments body guards,
       .primitive (.value [] (.expression arguments) (.expression values) initial),
       .premises proof guards initial final]

abbrev presentation (rows : List Atom) : Presentation := ⟨Judgment, Rule, conclusion, premises rows⟩
instance (rows : List Atom) : DecidableEq (presentation rows).Judgment := inferInstanceAs (DecidableEq Judgment)

def Meaning (rows : List Atom) : Judgment → Prop
  | .primitive judgment => Evidence.Primitive.Meaning judgment
  | .at source index row => source[index]? = some row
  | .clause index left right guards => MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.ClauseAt rows index left right guards
  | .callable index head arguments body guards => RuleAt rows index ⟨head, arguments, body⟩ guards
  | .root proof subject target => MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring (environment rows) proof subject target
  | .premise proof guard initial final => MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremiseHolds (environment rows) proof guard initial final
  | .premises proof guards initial final => MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremisesHold (environment rows) proof guards initial final
  | .query relation arguments initial origin final => MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.QueryHolds (environment rows) relation arguments initial origin final
  | .call head values proof index bindings body =>
      MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.CallReady (environment rows) head values proof index (.evaluate bindings body)

def primitiveEmbedding (rows : List Atom) : Presentation.Morphism Evidence.Primitive.presentation (presentation rows) where
  judgment := .primitive
  rule := .primitive
  conclusion _ := rfl
  premises _ := rfl

theorem nativeFresh_sound (rows : List Atom) (initial : Subst) (nameSchema subjectSchema : Atom)
    (name : String) (subject : Atom)
    (nameValue : applySubst initial nameSchema = .var name)
    (subjectValue : applySubst initial subjectSchema = subject)
    (fresh : name ∉ atomFreeVars subject) :
    MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.QueryHolds (environment rows) "metta-atom-fresh-v1" [nameSchema, subjectSchema]
      initial (.native 0) initial := by
  refine .native (signature := AtomServices.signatures[0])
    (resolved := [GroundData.encode (.var name), GroundData.encode subject])
    (rows := [[GroundData.encode (.var name), GroundData.encode subject]])
    (values := [.var name, subject]) (by simp [environment, AtomServices.registration]) (by rfl) ?_ ?_
    (by simp only [List.getElem?_cons_zero, GroundData.encodeList]) ?_
  · rw [← nameValue, ← subjectValue]
    exact .input (.input .nil)
  · exact AtomServices.Source.freshness (.held rfl (.variableName name subject fresh))
  · exact .cons (.input nameValue) (.cons (.input subjectValue) .nil)

def relationName : AtomMatchMode → String
  | .value => "petta-match-value-v1"
  | .binding => "petta-match-binding-v1"

theorem nativeMatch_sound (rows : List Atom) (mode : AtomMatchMode) (initial final innerInitial innerFinal : Subst)
    (bindingsSchema patternSchema valueSchema outputSchema pattern value : Atom)
    (bindingsValue : applySubst initial bindingsSchema = bindingsData innerInitial)
    (patternValue : applySubst initial patternSchema = pattern)
    (valueValue : applySubst initial valueSchema = value)
    (matched : AtomMatched mode innerInitial pattern value innerFinal)
    (output : SpaceSemantics.ValueMatch initial outputSchema (bindingsData innerFinal) final) :
    MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.QueryHolds (environment rows)
      (relationName mode)
      [bindingsSchema, patternSchema, valueSchema, outputSchema] initial (.native 0) final := by
  let arguments := [GroundData.encode (bindingsData innerInitial), GroundData.encode pattern,
    GroundData.encode value, GroundData.schema outputSchema]
  let produced := [[GroundData.encode (bindingsData innerInitial), GroundData.encode pattern,
    GroundData.encode value, GroundData.encode (bindingsData innerFinal)]]
  have source : AtomMatching.RowsMeaning mode arguments produced :=
    ⟨innerInitial, pattern, value, GroundData.schema outputSchema, some innerFinal, rfl, .matched matched, rfl⟩
  cases mode with
  | value =>
      refine .native (signature := AtomServices.signatures[1]) (resolved := arguments) (rows := produced)
        (values := [bindingsData innerInitial, pattern, value, bindingsData innerFinal])
        (by simp [relationName, environment, AtomServices.registration]) (by rfl) ?_
        (AtomServices.Source.matchValue source)
        (by simp only [produced, List.getElem?_cons_zero, GroundData.encodeList]) ?_
      · dsimp only [arguments]
        rw [← bindingsValue, ← patternValue, ← valueValue]
        exact .input (.input (.input (.output .nil)))
      · exact .cons (.input bindingsValue) (.cons (.input patternValue) (.cons (.input valueValue) (.cons (.output output) .nil)))
  | binding =>
      refine .native (signature := AtomServices.signatures[2]) (resolved := arguments) (rows := produced)
        (values := [bindingsData innerInitial, pattern, value, bindingsData innerFinal])
        (by simp [relationName, environment, AtomServices.registration]) (by rfl) ?_
        (AtomServices.Source.matchBinding source)
        (by simp only [produced, List.getElem?_cons_zero, GroundData.encodeList]) ?_
      · dsimp only [arguments]
        rw [← bindingsValue, ← patternValue, ← valueValue]
        exact .input (.input (.input (.output .nil)))
      · exact .cons (.input bindingsValue) (.cons (.input patternValue) (.cons (.input valueValue) (.cons (.output output) .nil)))

theorem rule_sound (rows : List Atom) (rule : Rule)
    (proved : ∀ judgment ∈ premises rows rule, Meaning rows judgment) : Meaning rows (conclusion rule) := by
  cases rule <;> simp only [premises, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Meaning, conclusion] at proved ⊢
  case primitive rule =>
    apply Evidence.Primitive.rule_sound rule
    intro judgment member
    exact proved (.primitive judgment) (List.mem_map.mpr ⟨judgment, member, rfl⟩)
  case atHead => rfl
  case atTail => exact proved
  case clauseEquation => exact ⟨_, proved, .equation _ _⟩
  case clauseGuarded => exact ⟨_, proved, .guarded _ _ _⟩
  case callableEquation => exact ⟨_, proved, .equation _ _ _⟩
  case callableGuarded => exact ⟨_, proved, .guarded _ _ _ _⟩
  case root => exact .rule proved.1 proved.2.1 proved.2.2.1 proved.2.2.2.symm
  case fresh => exact .fresh proved
  case child => exact .child (proved.1 ▸ proved.2.1) proved.2.2
  case query => exact .query proved.1 proved.2.1 proved.2.2
  case premisesNil => exact .nil
  case premisesCons => exact .cons proved.1 proved.2
  case queryRelation => exact .relation proved.1 proved.2
  case queryBuiltin => exact .builtin proved.1 proved.2
  case nativeFresh => exact nativeFresh_sound rows _ _ _ _ _ proved.1 proved.2.1 proved.2.2
  case nativeValue =>
    exact nativeMatch_sound rows .value _ _ _ _ _ _ _ _ _ _
      proved.1 proved.2.1 proved.2.2.1 proved.2.2.2.1 proved.2.2.2.2
  case nativeBinding =>
    exact nativeMatch_sound rows .binding _ _ _ _ _ _ _ _ _ _
      proved.1 proved.2.1 proved.2.2.1 proved.2.2.2.1 proved.2.2.2.2
  case call index head arguments values body guards proof initial final =>
    exact .guarded (prepared := ⟨index, ⟨head, arguments, body⟩, guards, initial⟩)
      (.matched proved.1 rfl proved.2.1) proved.2.2

theorem derivation_sound (rows : List Atom) {judgment : Judgment}
    (proof : (presentation rows).Derivation judgment) : Meaning rows judgment := by
  apply Mettapedia.TypeTheory.JudgmentDerivation.Derivation.rec
    (motive := fun judgment _ => Meaning rows judgment) (t := proof)
  intro judgment rule children ih
  rcases rule with ⟨rule, same⟩
  cases same
  apply rule_sound rows rule
  intro premise member
  obtain ⟨position, atPosition⟩ := List.mem_iff_get.mp member
  simpa only [presentation, Presentation.signature, atPosition] using ih ⟨position⟩

theorem inputs_two {initial : Subst} {arguments : List Atom}
    {resolved : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Inputs initial
      arguments [.input, .input] resolved) :
    ∃ first second, arguments = [first, second] ∧
      resolved = [GroundData.encode (applySubst initial first), GroundData.encode (applySubst initial second)] := by
  cases source with
  | input rest =>
      cases rest with
      | input rest => cases rest; exact ⟨_, _, rfl, rfl⟩

theorem inputs_four {initial : Subst} {arguments : List Atom}
    {resolved : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Inputs initial
      arguments [.input, .input, .input, .output] resolved) :
    ∃ first second third fourth, arguments = [first, second, third, fourth] ∧
      resolved = [GroundData.encode (applySubst initial first), GroundData.encode (applySubst initial second),
        GroundData.encode (applySubst initial third), GroundData.schema fourth] := by
  cases source with
  | input rest =>
      cases rest with
      | input rest =>
          cases rest with
          | input rest =>
              cases rest with
              | output rest => cases rest; exact ⟨_, _, _, _, rfl, rfl⟩

theorem signature_fresh {rows : List Atom} {arity : Nat}
    {signature : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Signature}
    (declared : signature? (environment rows).registration "metta-atom-fresh-v1" arity = some signature) :
    signature = AtomServices.signatures[0] := by
  obtain ⟨member, named, _, _⟩ := Mettapedia.OSLF.MeTTaIL.GeneralPremise.signature?_readout _ _ _ _ declared
  change signature ∈ AtomServices.signatures at member
  simp only [AtomServices.signatures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same
  · exact same
  · subst signature; contradiction
  · subst signature; contradiction

def matchSignature : AtomMatchMode → Mettapedia.OSLF.MeTTaIL.GeneralPremise.Signature
  | .value => AtomServices.signatures[1]
  | .binding => AtomServices.signatures[2]

theorem signature_match {rows : List Atom} {arity : Nat}
    {signature : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Signature} (mode : AtomMatchMode)
    (declared : signature? (environment rows).registration (relationName mode) arity = some signature) :
    signature = matchSignature mode := by
  obtain ⟨member, named, _, _⟩ := Mettapedia.OSLF.MeTTaIL.GeneralPremise.signature?_readout _ _ _ _ declared
  change signature ∈ AtomServices.signatures at member
  simp only [AtomServices.signatures, List.mem_cons, List.not_mem_nil, or_false] at member
  cases mode <;> rcases member with same | same | same
  all_goals first
    | exact same
    | subst signature; contradiction

theorem nativeFresh_expansion {rows : List Atom} {initial final : Subst} {arguments : List Atom}
    {resolved : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {provided : List (List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)} {values : List Atom} {index : Nat}
    (inputs : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Inputs initial arguments
      [.input, .input] resolved)
    (source : AtomFreshness.RowsMeaning resolved provided)
    (selected : provided[index]? = some (GroundData.encodeList values))
    (matched : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.ArgumentsHold initial
      arguments values [.input, .input] final) :
    ∃ rule : Rule, conclusion rule = .query "metta-atom-fresh-v1" arguments initial (.native index) final ∧
      ∀ judgment ∈ premises rows rule, Meaning rows judgment := by
  obtain ⟨nameSchema, subjectSchema, rfl, inputImage⟩ := inputs_two inputs
  cases source with
  | failed _ _ => simp at selected
  | @held nameValue subject image resolvedFresh =>
      have freshName : ∃ name, nameValue = .var name ∧ name ∉ atomFreeVars subject := by
        cases resolvedFresh with
        | variableName name _ held => exact ⟨name, rfl, held⟩
      obtain ⟨name, rfl, nameAbsent⟩ := freshName
      have images := inputImage.symm.trans image
      have nameValue := GroundData.encode_injective (List.cons.inj images).1
      have subjectValue := GroundData.encode_injective (List.cons.inj (List.cons.inj images).2).1
      cases index with
      | succ _ => simp at selected
      | zero =>
          have valuesImage : GroundData.encodeList [.var name, subject] = GroundData.encodeList values := by
            simpa only [List.getElem?_cons_zero, image, GroundData.encodeList] using Option.some.inj selected
          have same := GroundData.encodeList_injective valuesImage
          subst values
          cases matched with
          | cons first rest =>
              cases first with
              | input _ =>
                  cases rest with
                  | cons second rest =>
                      cases second with
                      | input _ =>
                          cases rest
                          refine ⟨.nativeFresh initial nameSchema subjectSchema name subject, rfl, ?_⟩
                          simpa only [premises, List.mem_cons, List.not_mem_nil, or_false,
                            forall_eq_or_imp, forall_eq, Meaning, Evidence.Primitive.Meaning] using
                            And.intro nameValue (And.intro subjectValue nameAbsent)

theorem nativeMatch_expansion {rows : List Atom} {initial final : Subst} {arguments : List Atom}
    {resolved : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {provided : List (List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)} {values : List Atom} {index : Nat}
    (mode : AtomMatchMode)
    (inputs : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Inputs initial arguments
      [.input, .input, .input, .output] resolved)
    (source : AtomMatching.RowsMeaning mode resolved provided)
    (selected : provided[index]? = some (GroundData.encodeList values))
    (matched : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.ArgumentsHold initial
      arguments values [.input, .input, .input, .output] final) :
    ∃ rule : Rule, conclusion rule = .query (relationName mode) arguments initial (.native index) final ∧
      ∀ judgment ∈ premises rows rule, Meaning rows judgment := by
  obtain ⟨bindingsSchema, patternSchema, valueSchema, outputSchema, rfl, inputImage⟩ := inputs_four inputs
  obtain ⟨innerInitial, pattern, value, hole, outcome, image, outcomeSource, rfl⟩ := source
  have images := inputImage.symm.trans image
  have bindingsValue := GroundData.encode_injective (List.cons.inj images).1
  have patternValue := GroundData.encode_injective (List.cons.inj (List.cons.inj images).2).1
  have valueValue := GroundData.encode_injective (List.cons.inj (List.cons.inj (List.cons.inj images).2).2).1
  cases outcome with
  | none => simp at selected
  | some innerFinal =>
      cases outcomeSource with
      | matched innerMatch =>
          cases index with
          | succ _ => simp at selected
          | zero =>
              have valuesImage : GroundData.encodeList [bindingsData innerInitial, pattern, value, bindingsData innerFinal] =
                  GroundData.encodeList values := by
                simpa only [Option.toList_some, List.map_cons, List.map_nil, List.getElem?_cons_zero,
                  GroundData.encodeList] using Option.some.inj selected
              have same := GroundData.encodeList_injective valuesImage
              subst values
              cases matched with
              | cons first rest =>
                  cases first with
                  | input _ =>
                    cases rest with
                    | cons second rest =>
                      cases second with
                      | input _ =>
                        cases rest with
                        | cons third rest =>
                          cases third with
                          | input _ =>
                            cases rest with
                            | cons output rest =>
                              cases output with
                              | output outputMatch =>
                                cases rest
                                cases mode with
                                | value =>
                                    refine ⟨.nativeValue initial final innerInitial innerFinal
                                      bindingsSchema patternSchema valueSchema outputSchema pattern value, rfl, ?_⟩
                                    simpa only [premises, List.mem_cons, List.not_mem_nil, or_false,
                                      forall_eq_or_imp, forall_eq, Meaning, Evidence.Primitive.Meaning, AtomMatched] using
                                      And.intro bindingsValue (And.intro patternValue
                                        (And.intro valueValue (And.intro innerMatch outputMatch)))
                                | binding =>
                                    refine ⟨.nativeBinding initial final innerInitial innerFinal
                                      bindingsSchema patternSchema valueSchema outputSchema pattern value, rfl, ?_⟩
                                    simpa only [premises, List.mem_cons, List.not_mem_nil, or_false,
                                      forall_eq_or_imp, forall_eq, Meaning, Evidence.Primitive.Meaning, AtomMatched] using
                                      And.intro bindingsValue (And.intro patternValue
                                        (And.intro valueValue (And.intro innerMatch outputMatch)))

theorem query_expansion {rows : List Atom} {relation : String} {arguments : List Atom}
    {initial final : Subst} {origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.QueryHolds
      (environment rows) relation arguments initial origin final) :
    ∃ rule : Rule, conclusion rule = .query relation arguments initial origin final ∧
      ∀ judgment ∈ premises rows rule, Meaning rows judgment := by
  cases source with
  | @relation index values _ stored matched =>
      refine ⟨.queryRelation index relation arguments values initial final, rfl, ?_⟩
      simpa only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Meaning, Evidence.Primitive.Meaning, environment] using And.intro stored matched
  | @builtin index values _ stored matched =>
      refine ⟨.queryBuiltin index relation arguments values initial final, rfl, ?_⟩
      simpa only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Meaning, Evidence.Primitive.Meaning, environment] using And.intro stored matched
  | native registered declared inputs provided selected matched =>
      change AtomServices.Source _ _ _ at provided
      cases provided with
      | freshness source =>
          have signature := signature_fresh declared
          subst signature
          exact nativeFresh_expansion inputs source selected matched
      | matchValue source =>
          have signature := signature_match .value declared
          subst signature
          exact nativeMatch_expansion .value inputs source selected matched
      | matchBinding source =>
          have signature := signature_match .binding declared
          subst signature
          exact nativeMatch_expansion .binding inputs source selected matched

theorem node_complete (rows : List Atom) (rule : Rule)
    (children : ∀ judgment ∈ premises rows rule, Nonempty ((presentation rows).Derivation judgment)) :
    Nonempty ((presentation rows).Derivation (conclusion rule)) := by
  classical
  exact ⟨.node ⟨rule, rfl⟩ (fun position => Classical.choice
    (children _ (List.get_mem _ position.down)))⟩

theorem primitive_complete (rows : List Atom) (judgment : Evidence.Primitive.Judgment)
    (source : Evidence.Primitive.Meaning judgment) :
    Nonempty ((presentation rows).Derivation (.primitive judgment)) := by
  obtain ⟨proof⟩ := Evidence.Primitive.meaning_complete judgment source
  exact ⟨(primitiveEmbedding rows).mapDerivation proof⟩

theorem at_complete (rows : List Atom) (source : List Atom) (index : Nat) (row : Atom)
    (stored : source[index]? = some row) : Nonempty ((presentation rows).Derivation (.at source index row)) := by
  induction source generalizing index with
  | nil => simp at stored
  | cons head rest ih =>
      cases index with
      | zero =>
          have same : head = row := Option.some.inj stored
          subst row
          exact node_complete rows (.atHead head rest) (by simp [premises])
      | succ index =>
          have later := ih index stored
          apply node_complete rows (.atTail head row rest index)
          simpa only [premises, List.mem_singleton, forall_eq] using later

theorem clause_complete (rows : List Atom) (index : Nat) (left right : Atom) (guards : List Atom)
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.ClauseAt rows index left right guards) :
    Nonempty ((presentation rows).Derivation (.clause index left right guards)) := by
  obtain ⟨row, stored, declared⟩ := source
  cases declared with
  | equation left right =>
      apply node_complete rows (.clauseEquation index left right)
      simpa only [premises, List.mem_singleton, forall_eq] using at_complete rows _ _ _ stored
  | guarded left right guards =>
      apply node_complete rows (.clauseGuarded index left right guards)
      simpa only [premises, List.mem_singleton, forall_eq] using at_complete rows _ _ _ stored

theorem callable_complete (rows : List Atom) (index : Nat) (head : String) (arguments : List Atom)
    (body : Atom) (guards : List Atom) (source : RuleAt rows index ⟨head, arguments, body⟩ guards) :
    Nonempty ((presentation rows).Derivation (.callable index head arguments body guards)) := by
  obtain ⟨row, stored, declared⟩ := source
  cases declared with
  | equation head arguments body =>
      apply node_complete rows (.callableEquation index head arguments body)
      simpa only [premises, List.mem_singleton, forall_eq] using at_complete rows _ _ _ stored
  | guarded head arguments body guards =>
      apply node_complete rows (.callableGuarded index head arguments body guards)
      simpa only [premises, List.mem_singleton, forall_eq] using at_complete rows _ _ _ stored

def leaf : Judgment → Bool
  | .primitive _ | .at _ _ _ => true
  | _ => false

theorem leaf_complete (rows : List Atom) (judgment : Judgment) (source : Meaning rows judgment)
    (basic : leaf judgment = true) : Nonempty ((presentation rows).Derivation judgment) := by
  cases judgment <;> simp only [leaf, Bool.false_eq_true] at basic
  case primitive judgment => exact primitive_complete rows judgment source
  case «at» sourceRows index row => exact at_complete rows sourceRows index row source

theorem query_leaves (rows : List Atom) (rule : Rule) (relation : String) (arguments : List Atom)
    (initial final : Subst) (origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin)
    (same : conclusion rule = .query relation arguments initial origin final) :
    ∀ judgment ∈ premises rows rule, leaf judgment = true := by
  cases rule <;> simp only [conclusion, reduceCtorEq] at same
  all_goals simp [premises, leaf]

theorem query_complete (rows : List Atom) (relation : String) (arguments : List Atom)
    (initial final : Subst) (origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin)
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.QueryHolds
      (environment rows) relation arguments initial origin final) :
    Nonempty ((presentation rows).Derivation (.query relation arguments initial origin final)) := by
  obtain ⟨rule, same, held⟩ := query_expansion source
  rw [← same]
  apply node_complete rows rule
  intro judgment member
  exact leaf_complete rows judgment (held judgment member)
    (query_leaves rows rule relation arguments initial final origin same judgment member)

mutual
  theorem root_complete {rows : List Atom} {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
      {subject target : Atom}
      (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring
        (environment rows) evidence subject target) :
      Nonempty ((presentation rows).Derivation (.root evidence subject target)) := by
    cases source with
    | @rule index proof left right subject target guards initial final stored matched held emitted =>
        apply node_complete rows (.root index proof left right subject target guards initial final)
        simpa only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro (clause_complete rows index left right guards stored)
            (And.intro (primitive_complete rows (.value [] left subject initial) matched)
              (And.intro (premises_complete held)
                (primitive_complete rows (.substitute final right target) emitted.symm)))
    termination_by sizeOf evidence

  theorem premise_complete {rows : List Atom} {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
      {guard : Atom} {initial final : Subst}
      (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremiseHolds
        (environment rows) evidence guard initial final) :
      Nonempty ((presentation rows).Derivation (.premise evidence guard initial final)) := by
    cases source with
    | @fresh name subject initial held =>
        apply node_complete rows (.fresh initial name subject)
        simpa only [premises, List.mem_singleton, forall_eq] using primitive_complete rows (.guard initial name subject) held
    | @child proof source target result initial final fired matched =>
        apply node_complete rows (.child proof initial final source (applySubst initial source) target result)
        simpa only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro (primitive_complete rows (.substitute initial source (applySubst initial source)) rfl)
            (And.intro (root_complete fired) (primitive_complete rows (.value initial target result final) matched))
    | @query relation arguments initial final origin ordinary directed queried =>
        apply node_complete rows (.query relation arguments initial final origin)
        simpa only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro (primitive_complete rows (.nameNe relation "fresh") ordinary)
            (And.intro (primitive_complete rows (.nameNe relation "==") directed)
              (query_complete rows relation arguments initial final origin queried))
    termination_by sizeOf evidence

  theorem premises_complete {rows : List Atom} {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
      {guards : List Atom} {initial final : Subst}
      (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremisesHold
        (environment rows) evidence guards initial final) :
      Nonempty ((presentation rows).Derivation (.premises evidence guards initial final)) := by
    cases source with
    | nil => exact node_complete rows (.premisesNil initial) (by simp [premises])
    | @cons head tail guard guards initial middle final held rest =>
        apply node_complete rows (.premisesCons head tail guard guards initial middle final)
        simpa only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro (premise_complete held) (premises_complete rest)
    termination_by sizeOf evidence
end

theorem call_complete {rows : List Atom} {head : String} {values : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence} {index : Nat}
    {bindings : Subst} {body : Atom}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.CallReady
      (environment rows) head values evidence index (.evaluate bindings body)) :
    Nonempty ((presentation rows).Derivation (.call head values evidence index bindings body)) := by
  cases source with
  | @guarded prepared final proof selected held =>
      cases selected with
      | @matched index equation guards initial stored named matched =>
          subst head
          apply node_complete rows (.call index equation.head equation.arguments values equation.body guards proof initial bindings)
          simpa only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
            And.intro (callable_complete rows index equation.head equation.arguments equation.body guards stored)
              (And.intro (primitive_complete rows (.value [] (.expression equation.arguments) (.expression values) initial) matched)
                (premises_complete held))

theorem meaning_complete (rows : List Atom) (judgment : Judgment) (source : Meaning rows judgment) :
    Nonempty ((presentation rows).Derivation judgment) := by
  cases judgment with
  | primitive judgment => exact primitive_complete rows judgment source
  | «at» sourceRows index row => exact at_complete rows sourceRows index row source
  | clause index left right guards => exact clause_complete rows index left right guards source
  | callable index head arguments body guards => exact callable_complete rows index head arguments body guards source
  | root evidence subject target => exact root_complete source
  | premise evidence guard initial final => exact premise_complete source
  | premises evidence guards initial final => exact premises_complete source
  | query relation arguments initial origin final => exact query_complete rows relation arguments initial final origin source
  | call head values evidence index bindings body => exact call_complete source

theorem shared_sound (rows : List Atom) (article : Shared.Certificate (presentation rows)) (judgment : Judgment)
    (accepted : Shared.check article judgment = true) : Meaning rows judgment := by
  obtain ⟨proof, _, _⟩ := Shared.accepted_original article judgment accepted
  exact derivation_sound rows proof

theorem shared_complete (rows : List Atom) (judgment : Judgment) : Meaning rows judgment ↔
    ∃ article : Shared.Certificate (presentation rows), Shared.check article judgment = true := by
  constructor
  · intro source
    obtain ⟨proof⟩ := meaning_complete rows judgment source
    exact ⟨Shared.emit proof, Shared.emit_checked proof⟩
  · rintro ⟨article, accepted⟩
    exact shared_sound rows article judgment accepted

namespace Wire
open Mettapedia.OSLF.Binding.WireCodec

private def atomCodec := Evidence.Primitive.Wire.atomCodec
private def atomsCodec := Evidence.Primitive.Wire.atomsCodec
private def bindingsCodec := Evidence.Primitive.Wire.bindingsCodec
private def evidenceCodec := atomCodec.mapped Conditional.Wire.evidenceData Conditional.Wire.readEvidence
  Conditional.Wire.readEvidence_evidenceData
private def originCodec := atomCodec.mapped Conditional.Wire.originData Conditional.Wire.readOrigin
  Conditional.Wire.readOrigin_originData
private def atCodec := Codec.prod atomsCodec (Codec.prod Codec.nat atomCodec)
private def clauseCodec := Codec.prod Codec.nat (Codec.prod atomCodec (Codec.prod atomCodec atomsCodec))
private def callableCodec := Codec.prod Codec.nat (Codec.prod Codec.string
  (Codec.prod atomsCodec (Codec.prod atomCodec atomsCodec)))
private def rootCodec := Codec.prod evidenceCodec (Codec.prod atomCodec atomCodec)
private def premiseCodec := Codec.prod evidenceCodec (Codec.prod atomCodec (Codec.prod bindingsCodec bindingsCodec))
private def premisesCodec := Codec.prod evidenceCodec (Codec.prod atomsCodec (Codec.prod bindingsCodec bindingsCodec))
private def queryCodec := Codec.prod Codec.string (Codec.prod atomsCodec
  (Codec.prod bindingsCodec (Codec.prod originCodec bindingsCodec)))
private def callCodec := Codec.prod Codec.string (Codec.prod atomsCodec (Codec.prod evidenceCodec
  (Codec.prod Codec.nat (Codec.prod bindingsCodec atomCodec))))

def putJudgment : Judgment → Data
  | .primitive judgment => .pair (.atom 0) (Evidence.Primitive.Wire.judgmentCodec.put judgment)
  | .at rows index row => .pair (.atom 1) (atCodec.put (rows, index, row))
  | .clause index left right guards => .pair (.atom 2) (clauseCodec.put (index, left, right, guards))
  | .callable index head arguments body guards => .pair (.atom 3) (callableCodec.put (index, head, arguments, body, guards))
  | .root evidence subject target => .pair (.atom 4) (rootCodec.put (evidence, subject, target))
  | .premise evidence guard initial final => .pair (.atom 5) (premiseCodec.put (evidence, guard, initial, final))
  | .premises evidence guards initial final => .pair (.atom 6) (premisesCodec.put (evidence, guards, initial, final))
  | .query relation arguments initial origin final => .pair (.atom 7) (queryCodec.put (relation, arguments, initial, origin, final))
  | .call head values evidence index bindings body => .pair (.atom 8) (callCodec.put (head, values, evidence, index, bindings, body))

def getJudgment : Data → Option Judgment
  | .pair (.atom 0) fields => Evidence.Primitive.Wire.judgmentCodec.get fields |>.map .primitive
  | .pair (.atom 1) fields => atCodec.get fields |>.map fun (rows, index, row) => .at rows index row
  | .pair (.atom 2) fields => clauseCodec.get fields |>.map fun (index, left, right, guards) => .clause index left right guards
  | .pair (.atom 3) fields => callableCodec.get fields |>.map fun (index, head, arguments, body, guards) => .callable index head arguments body guards
  | .pair (.atom 4) fields => rootCodec.get fields |>.map fun (evidence, subject, target) => .root evidence subject target
  | .pair (.atom 5) fields => premiseCodec.get fields |>.map fun (evidence, guard, initial, final) => .premise evidence guard initial final
  | .pair (.atom 6) fields => premisesCodec.get fields |>.map fun (evidence, guards, initial, final) => .premises evidence guards initial final
  | .pair (.atom 7) fields => queryCodec.get fields |>.map fun (relation, arguments, initial, origin, final) => .query relation arguments initial origin final
  | .pair (.atom 8) fields => callCodec.get fields |>.map fun (head, values, evidence, index, bindings, body) => .call head values evidence index bindings body
  | _ => none

theorem getJudgment_putJudgment (judgment : Judgment) : getJudgment (putJudgment judgment) = some judgment := by
  cases judgment <;> simp only [putJudgment, getJudgment, Codec.get_put, Option.map_some]

def judgmentCodec : Codec Judgment := ⟨putJudgment, getJudgment, getJudgment_putJudgment⟩

def coding (rows : List Atom) : Shared.LiteralChecking.Coding (presentation rows).Judgment where
  word judgment := Binary.Triples.encode (Binary.encodeWith judgmentCodec judgment)
  injective := Binary.Triples.original_injective judgmentCodec

end Wire

theorem paid_exact (rows : List Atom) (article : Shared.Certificate (presentation rows)) (judgment : Judgment) :
    (Shared.LiteralChecking.check (Wire.coding rows) article judgment).accepted = Shared.check article judgment :=
  Shared.LiteralChecking.check_exact (Wire.coding rows) article judgment

theorem paid_complete (rows : List Atom) (judgment : Judgment) : Meaning rows judgment ↔
    ∃ article : Shared.Certificate (presentation rows),
      (Shared.LiteralChecking.check (Wire.coding rows) article judgment).accepted = true := by
  simpa only [paid_exact] using shared_complete rows judgment

theorem paid_structural_work (rows : List Atom) (article : Shared.Certificate (presentation rows)) (judgment : Judgment) :
    (Shared.LiteralChecking.check (Wire.coding rows) article judgment).work ≤
      (Shared.LiteralChecking.inputVolume (Wire.coding rows) article judgment + 2) *
        (5 * Shared.LiteralChecking.inputVolume (Wire.coding rows) article judgment + 10) :=
  Shared.LiteralChecking.check_work_le (Wire.coding rows) article judgment

theorem root_baseline (rows : List Atom)
    (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence)
    (subject target : Atom) :
    MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring
      (environment rows) evidence subject target ↔
    ∃ article : Shared.Certificate (presentation rows),
      (Shared.LiteralChecking.check (Wire.coding rows) article (.root evidence subject target)).accepted = true :=
  paid_complete rows (.root evidence subject target)

theorem call_baseline (rows : List Atom) (head : String) (values : List Atom)
    (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence)
    (index : Nat) (bindings : Subst) (body : Atom) :
    MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.CallReady
      (environment rows) head values evidence index (.evaluate bindings body) ↔
    ∃ article : Shared.Certificate (presentation rows),
      (Shared.LiteralChecking.check (Wire.coding rows) article (.call head values evidence index bindings body)).accepted = true :=
  paid_complete rows (.call head values evidence index bindings body)

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source

open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open MeTTaRevisionedQueryBindEval.AuthoredActivation
open MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open ConfigurationEncoding (bindingsData readBindings)

abbrev Derivation (rows : List Atom) := (presentation rows).Derivation

private def node (rows : List Atom) (rule : Rule)
    (children : Mettapedia.OSLF.Binding.FiniteRulePremiseLists.Evidence (Derivation rows) (premises rows rule)) :
    Derivation rows (conclusion rule) := .node ⟨rule, rfl⟩ (fun position => children position.down)

private def primitive (rows : List Atom) {judgment : Evidence.Primitive.Judgment}
    (proof : Evidence.Primitive.Derivation judgment) : Derivation rows (.primitive judgment) :=
  (primitiveEmbedding rows).mapDerivation proof

def deriveAt (rows : List Atom) : (source : List Atom) → (index : Nat) → (row : Atom) →
    source[index]? = some row → Derivation rows (.at source index row)
  | [], _, _, impossible => by simp at impossible
  | head :: rest, 0, row, found => by
      have same : head = row := Option.some.inj found
      subst row
      exact node rows (.atHead head rest) (noEvidence _)
  | head :: rest, index + 1, row, found =>
      node rows (.atTail head row rest index)
        (consEvidence _ (deriveAt rows rest index row found) (noEvidence _))

def deriveClause (rows : List Atom) (index : Nat) (left right : Atom) (guards : List Atom)
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.ClauseAt rows index left right guards) :
    Derivation rows (.clause index left right guards) := by
  cases found : rows[index]? with
  | none =>
      have impossible : False := by obtain ⟨_, stored, _⟩ := source; rw [found] at stored; cases stored
      exact impossible.elim
  | some row =>
      have declared : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Clause row left right guards := by
        obtain ⟨other, stored, declared⟩ := source
        have same : other = row := Option.some.inj (stored.symm.trans found)
        exact same ▸ declared
      by_cases ordinary : row = .expression [.symbol "=", left, right]
      · have noGuards : guards = [] := by
          cases declared
          · rfl
          · simp at ordinary
        subst guards
        exact node rows (.clauseEquation index left right)
          (consEvidence _ (deriveAt rows rows index _ (found.trans (congrArg some ordinary))) (noEvidence _))
      · have guarded : row = .expression (.symbol "rule!" :: left :: right :: guards) := by
          cases declared
          · exact (ordinary rfl).elim
          · rfl
        exact node rows (.clauseGuarded index left right guards)
          (consEvidence _ (deriveAt rows rows index _ (found.trans (congrArg some guarded))) (noEvidence _))

def deriveCallable (rows : List Atom) (index : Nat) (head : String) (arguments : List Atom)
    (body : Atom) (guards : List Atom) (source : RuleAt rows index ⟨head, arguments, body⟩ guards) :
    Derivation rows (.callable index head arguments body guards) := by
  cases found : rows[index]? with
  | none =>
      have impossible : False := by obtain ⟨_, stored, _⟩ := source; rw [found] at stored; cases stored
      exact impossible.elim
  | some row =>
      have declared : RuleDeclaration row ⟨head, arguments, body⟩ guards := by
        obtain ⟨other, stored, declared⟩ := source
        have same : other = row := Option.some.inj (stored.symm.trans found)
        exact same ▸ declared
      by_cases ordinary : row = .expression [.symbol "=", .expression (.symbol head :: arguments), body]
      · have noGuards : guards = [] := by cases declared <;> first | rfl | simp at ordinary
        subst guards
        exact node rows (.callableEquation index head arguments body)
          (consEvidence _ (deriveAt rows rows index _ (found.trans (congrArg some ordinary))) (noEvidence _))
      · have guarded : row = .expression (.symbol "rule!" :: .expression (.symbol head :: arguments) :: body :: guards) := by
          cases declared
          · exact (ordinary rfl).elim
          · rfl
        exact node rows (.callableGuarded index head arguments body guards)
          (consEvidence _ (deriveAt rows rows index _ (found.trans (congrArg some guarded))) (noEvidence _))

def expandNativeFresh? (rows : List Atom) (initial : Subst) : (arguments : List Atom) →
    Option (Σ final, Derivation rows (.query "metta-atom-fresh-v1" arguments initial (.native 0) final))
  | [nameSchema, subjectSchema] =>
      match nameValue : applySubst initial nameSchema with
      | .var name =>
          let subject := applySubst initial subjectSchema
          if fresh : name ∉ atomFreeVars subject then
            let nameProof := Evidence.Primitive.deriveSubstitution initial nameSchema
            let represented : Evidence.Primitive.Derivation (.substitute initial nameSchema (.var name)) :=
              nameValue ▸ nameProof
            some ⟨initial, node rows (.nativeFresh initial nameSchema subjectSchema name subject)
              (consEvidence _ (primitive rows represented)
                (consEvidence _ (primitive rows (Evidence.Primitive.deriveSubstitution initial subjectSchema))
                  (consEvidence _ (primitive rows (Evidence.Primitive.deriveFresh name subject fresh)) (noEvidence _))))⟩
          else none
      | _ => none
  | _ => none

def expandNativeMatch? (rows : List Atom) (mode : AtomMatchMode) (initial : Subst) : (arguments : List Atom) →
    Option (Σ final, Derivation rows (.query (relationName mode) arguments initial (.native 0) final))
  | [bindingsSchema, patternSchema, valueSchema, outputSchema] =>
      match decoded : readBindings (applySubst initial bindingsSchema) with
      | none => none
      | some innerInitial =>
          let pattern := applySubst initial patternSchema
          let value := applySubst initial valueSchema
          let bindingImage := (ConfigurationEncoding.bindingsData_of_readBindings decoded).symm
          let bindingProof := Evidence.Primitive.deriveSubstitution initial bindingsSchema
          let represented : Evidence.Primitive.Derivation (.substitute initial bindingsSchema (bindingsData innerInitial)) :=
            bindingImage ▸ bindingProof
          match mode with
          | .value =>
              match inner : SpaceSemantics.matchValue innerInitial pattern value with
              | none => none
              | some innerFinal =>
                  match outer : SpaceSemantics.matchValue initial outputSchema (bindingsData innerFinal) with
                  | none => none
                  | some final =>
                      some ⟨final, node rows (.nativeValue initial final innerInitial innerFinal
                        bindingsSchema patternSchema valueSchema outputSchema pattern value)
                        (consEvidence _ (primitive rows represented)
                          (consEvidence _ (primitive rows (Evidence.Primitive.deriveSubstitution initial patternSchema))
                            (consEvidence _ (primitive rows (Evidence.Primitive.deriveSubstitution initial valueSchema))
                              (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue inner))
                                (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue outer)) (noEvidence _))))))⟩
          | .binding =>
              match inner : SpaceSemantics.matchBinding innerInitial pattern value with
              | none => none
              | some innerFinal =>
                  match outer : SpaceSemantics.matchValue initial outputSchema (bindingsData innerFinal) with
                  | none => none
                  | some final =>
                      some ⟨final, node rows (.nativeBinding initial final innerInitial innerFinal
                        bindingsSchema patternSchema valueSchema outputSchema pattern value)
                        (consEvidence _ (primitive rows represented)
                          (consEvidence _ (primitive rows (Evidence.Primitive.deriveSubstitution initial patternSchema))
                            (consEvidence _ (primitive rows (Evidence.Primitive.deriveSubstitution initial valueSchema))
                              (consEvidence _ (primitive rows (Evidence.Primitive.deriveBinding inner))
                                (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue outer)) (noEvidence _))))))⟩
  | _ => none

def expandQuery? (rows : List Atom) (relation : String) (arguments : List Atom)
    (initial : Subst) : (origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin) →
    Option (Σ final, Derivation rows (.query relation arguments initial origin final))
  | .relation index =>
      match tuple : Conditional.tuple? rows "relation!" relation index with
      | none => none
      | some values =>
          match matched : SpaceSemantics.matchValue initial (.expression arguments) (.expression values) with
          | none => none
          | some final =>
              some ⟨final, node rows (.queryRelation index relation arguments values initial final)
                (consEvidence _ (deriveAt rows rows index _ ((Conditional.tuple?_exact _ _ _ _ _).mp tuple))
                  (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue matched)) (noEvidence _)))⟩
  | .builtin index =>
      match tuple : Conditional.tuple? rows "builtin!" relation index with
      | none => none
      | some values =>
          match matched : SpaceSemantics.matchValue initial (.expression arguments) (.expression values) with
          | none => none
          | some final =>
              some ⟨final, node rows (.queryBuiltin index relation arguments values initial final)
                (consEvidence _ (deriveAt rows rows index _ ((Conditional.tuple?_exact _ _ _ _ _).mp tuple))
                  (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue matched)) (noEvidence _)))⟩
  | .native (_index + 1) => none
  | .native 0 =>
      if fresh : relation = "metta-atom-fresh-v1" then
        fresh.symm ▸ expandNativeFresh? rows initial arguments
      else if value : relation = "petta-match-value-v1" then
        value.symm ▸ expandNativeMatch? rows .value initial arguments
      else if binding : relation = "petta-match-binding-v1" then
        binding.symm ▸ expandNativeMatch? rows .binding initial arguments
      else none

mutual
  def expandRoot? (rows : List Atom) : (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) →
      (subject : Atom) → Option (Σ target, Derivation rows (.root evidence subject target))
    | .firing index proof, subject =>
        match found : rows[index]? with
        | none => none
        | some row =>
          match parsed : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.readClause? row with
          | none => none
          | some (left, right, guards) =>
            match matched : SpaceSemantics.matchValue [] left subject with
            | none => none
            | some initial =>
              match expandPremises? rows proof guards initial with
              | none => none
              | some ⟨final, premisesProof⟩ =>
                let target := applySubst final right
                some ⟨target, node rows (.root index proof left right subject target guards initial final)
                  (consEvidence _ (deriveClause rows index left right guards
                    ⟨row, found, (MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.readClause?_exact _ _ _ _).mp parsed⟩)
                    (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue matched))
                      (consEvidence _ premisesProof
                        (consEvidence _ (primitive rows (Evidence.Primitive.deriveSubstitution final right)) (noEvidence _)))))⟩
    | _, _ => none

  def expandPremise? (rows : List Atom) : (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) →
      (guard : Atom) → (initial : Subst) → Option (Σ final, Derivation rows (.premise evidence guard initial final))
    | .fresh, .expression [.symbol "fresh", .var name, subject], initial =>
        if held : matchSourceGuard initial (.freshness name subject) then
          some ⟨initial, node rows (.fresh initial name subject)
            (consEvidence _ (primitive rows (Evidence.Primitive.deriveGuard initial name subject held)) (noEvidence _))⟩
        else none
    | .child proof, .expression [.symbol "==", source, target], initial =>
        match expandRoot? rows proof (applySubst initial source) with
        | none => none
        | some ⟨result, rootProof⟩ =>
          match matched : SpaceSemantics.matchValue initial target result with
          | none => none
          | some final =>
            some ⟨final, node rows (.child proof initial final source (applySubst initial source) target result)
              (consEvidence _ (primitive rows (Evidence.Primitive.deriveSubstitution initial source))
                (consEvidence _ rootProof (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue matched)) (noEvidence _))))⟩
    | .query origin, .expression (.symbol relation :: arguments), initial =>
        if ordinary : relation ≠ "fresh" ∧ relation ≠ "==" then
          match expandQuery? rows relation arguments initial origin with
          | none => none
          | some ⟨final, queryProof⟩ =>
            some ⟨final, node rows (.query relation arguments initial final origin)
              (consEvidence _ (primitive rows (Evidence.Primitive.deriveNameNe relation "fresh" ordinary.1))
                (consEvidence _ (primitive rows (Evidence.Primitive.deriveNameNe relation "==" ordinary.2))
                  (consEvidence _ queryProof (noEvidence _))))⟩
        else none
    | _, _, _ => none

  def expandPremises? (rows : List Atom) : (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) →
      (guards : List Atom) → (initial : Subst) → Option (Σ final, Derivation rows (.premises evidence guards initial final))
    | .empty, [], initial => some ⟨initial, node rows (.premisesNil initial) (noEvidence _)⟩
    | .cons head tail, guard :: guards, initial =>
        match expandPremise? rows head guard initial with
        | none => none
        | some ⟨middle, first⟩ =>
          match expandPremises? rows tail guards middle with
          | none => none
          | some ⟨final, rest⟩ =>
            some ⟨final, node rows (.premisesCons head tail guard guards initial middle final)
              (consEvidence _ first (consEvidence _ rest (noEvidence _)))⟩
    | _, _, _ => none
end

def expandCall? (rows : List Atom) :
    (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) →
    (head : String) → (values : List Atom) →
    Option (Σ packet : Nat × Subst × Atom,
      Derivation rows (.call head values evidence packet.1 packet.2.1 packet.2.2))
  | .firing index proof, head, values =>
      match found : rows[index]? with
      | none => none
      | some row =>
          match parsed : readRule? row with
          | none => none
          | some (equation, guards) =>
              if named : equation.head = head then
                match matched : SpaceSemantics.matchValue [] (.expression equation.arguments) (.expression values) with
                | none => none
                | some initial =>
                    match expandPremises? rows proof guards initial with
                    | none => none
                    | some ⟨final, proofPremises⟩ =>
                        let typed := node rows (.call index equation.head equation.arguments values equation.body guards proof initial final)
                          (consEvidence _ (deriveCallable rows index equation.head equation.arguments equation.body guards
                            ⟨row, found, (readRule?_exact _ _ _).mp parsed⟩)
                            (consEvidence _ (primitive rows (Evidence.Primitive.deriveValue matched))
                              (consEvidence _ proofPremises (noEvidence _))))
                        some ⟨(index, final, equation.body), named ▸ typed⟩
              else none
  | _, _, _ => none

def rootArticle? (rows : List Atom)
    (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (subject : Atom) :
    Option (Atom × Shared.Certificate (presentation rows)) :=
  (expandRoot? rows evidence subject).map fun packet => (packet.1, Shared.emit packet.2)

def callArticle? (rows : List Atom)
    (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence)
    (head : String) (values : List Atom) :
    Option ((Nat × Subst × Atom) × Shared.Certificate (presentation rows)) :=
  (expandCall? rows evidence head values).map fun packet => (packet.1, Shared.emit packet.2)

theorem rootArticle?_sound {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence} {subject target : Atom}
    {article : Shared.Certificate (presentation rows)} (compiled : rootArticle? rows evidence subject = some (target, article)) :
    Shared.check article (.root evidence subject target) = true ∧
      MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring
        (environment rows) evidence subject target := by
  obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp compiled
  cases same
  exact ⟨Shared.emit_checked packet.2, derivation_sound rows packet.2⟩

theorem callArticle?_sound {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence} {head : String}
    {values : List Atom} {packet : Nat × Subst × Atom}
    {article : Shared.Certificate (presentation rows)} (compiled : callArticle? rows evidence head values = some (packet, article)) :
    Shared.check article (.call head values evidence packet.1 packet.2.1 packet.2.2) = true ∧
      MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.CallReady
        (environment rows) head values evidence packet.1 (.evaluate packet.2.1 packet.2.2) := by
  obtain ⟨packet, _, same⟩ := Option.map_eq_some_iff.mp compiled
  cases same
  exact ⟨Shared.emit_checked packet.2, derivation_sound rows packet.2⟩

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source

open Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa
open MeTTaRevisionedQueryBindEval.AuthoredActivation
open MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open ConfigurationEncoding (bindingsData)

 theorem expandQuery_complete {rows : List Atom} {relation : String} {arguments : List Atom}
    {initial final : Subst} {origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.QueryHolds
      (environment rows) relation arguments initial origin final) :
    (expandQuery? rows relation arguments initial origin).map Sigma.fst = some final := by
  with_unfolding_all
    obtain ⟨rule, same, held⟩ := query_expansion source
    cases rule with
    | queryRelation index relation arguments values initial final =>
        cases same
        simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Meaning, Evidence.Primitive.Meaning] at held
        obtain ⟨stored, matched⟩ := held
        have tuple := (Conditional.tuple?_exact rows "relation!" relation index values).mpr stored
        dsimp only [expandQuery?]
        split
        next missing => rw [tuple] at missing; cases missing
        next actual selected =>
          have equal : actual = values := Option.some.inj (selected.symm.trans tuple)
          subst actual
          split
          next missing => rw [SpaceSemantics.matchValue_complete matched] at missing; cases missing
          next actual selected =>
            have equal : actual = final := Option.some.inj (selected.symm.trans (SpaceSemantics.matchValue_complete matched))
            subst actual
            rfl
    | queryBuiltin index relation arguments values initial final =>
        cases same
        simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Meaning, Evidence.Primitive.Meaning] at held
        obtain ⟨stored, matched⟩ := held
        have tuple := (Conditional.tuple?_exact rows "builtin!" relation index values).mpr stored
        dsimp only [expandQuery?]
        split
        next missing => rw [tuple] at missing; cases missing
        next actual selected =>
          have equal : actual = values := Option.some.inj (selected.symm.trans tuple)
          subst actual
          split
          next missing => rw [SpaceSemantics.matchValue_complete matched] at missing; cases missing
          next actual selected =>
            have equal : actual = final := Option.some.inj (selected.symm.trans (SpaceSemantics.matchValue_complete matched))
            subst actual
            rfl
    | nativeFresh initial nameSchema subjectSchema name subject =>
        cases same
        simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Meaning, Evidence.Primitive.Meaning] at held
        obtain ⟨nameValue, subjectValue, fresh⟩ := held
        dsimp only [expandQuery?]
        rw [dif_pos rfl]
        dsimp only [expandNativeFresh?]
        split
        next actual selected =>
          have equal : actual = name := Atom.var.inj (selected.symm.trans nameValue)
          subst actual
          have clear : name ∉ atomFreeVars (applySubst initial subjectSchema) := by
            simpa only [subjectValue] using fresh
          split
          next _ => rfl
          next forbidden => exact (forbidden clear).elim
        next excluded => exact (excluded name nameValue).elim
    | nativeValue initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value =>
        cases same
        simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Meaning, Evidence.Primitive.Meaning] at held
        obtain ⟨bindingsValue, patternValue, valueValue, inner, outer⟩ := held
        have decoded : ConfigurationEncoding.readBindings (applySubst initial bindingsSchema) = some innerInitial := by
          rw [bindingsValue, ConfigurationEncoding.readBindings_bindingsData]
        have innerChecked : SpaceSemantics.matchValue innerInitial (applySubst initial patternSchema)
            (applySubst initial valueSchema) = some innerFinal := by
          rw [patternValue, valueValue]
          exact SpaceSemantics.matchValue_complete inner
        change (expandNativeMatch? rows .value initial [bindingsSchema, patternSchema, valueSchema, outputSchema]).map Sigma.fst = some final
        rw [expandNativeMatch?.eq_1]
        split
        next missing => rw [decoded] at missing; cases missing
        next actual selected =>
          have equal : actual = innerInitial := Option.some.inj (selected.symm.trans decoded)
          subst actual
          dsimp only
          split
          next missing => rw [innerChecked] at missing; cases missing
          next actual selected =>
            have equal : actual = innerFinal := Option.some.inj (selected.symm.trans innerChecked)
            subst actual
            split
            next missing => rw [SpaceSemantics.matchValue_complete outer] at missing; cases missing
            next actual selected =>
              have equal : actual = final := Option.some.inj (selected.symm.trans (SpaceSemantics.matchValue_complete outer))
              subst actual
              rfl
    | nativeBinding initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value =>
        cases same
        simp only [premises, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Meaning, Evidence.Primitive.Meaning] at held
        obtain ⟨bindingsValue, patternValue, valueValue, inner, outer⟩ := held
        have decoded : ConfigurationEncoding.readBindings (applySubst initial bindingsSchema) = some innerInitial := by
          rw [bindingsValue, ConfigurationEncoding.readBindings_bindingsData]
        have innerChecked : SpaceSemantics.matchBinding innerInitial (applySubst initial patternSchema)
            (applySubst initial valueSchema) = some innerFinal := by
          rw [patternValue, valueValue]
          exact SpaceSemantics.matchBinding_complete inner
        change (expandNativeMatch? rows .binding initial [bindingsSchema, patternSchema, valueSchema, outputSchema]).map Sigma.fst = some final
        rw [expandNativeMatch?.eq_1]
        split
        next missing => rw [decoded] at missing; cases missing
        next actual selected =>
          have equal : actual = innerInitial := Option.some.inj (selected.symm.trans decoded)
          subst actual
          dsimp only
          split
          next missing => rw [innerChecked] at missing; cases missing
          next actual selected =>
            have equal : actual = innerFinal := Option.some.inj (selected.symm.trans innerChecked)
            subst actual
            split
            next missing => rw [SpaceSemantics.matchValue_complete outer] at missing; cases missing
            next actual selected =>
              have equal : actual = final := Option.some.inj (selected.symm.trans (SpaceSemantics.matchValue_complete outer))
              subst actual
              rfl
    | primitive _ => cases same
    | atHead _ _ => cases same
    | atTail _ _ _ _ => cases same
    | clauseEquation _ _ _ => cases same
    | clauseGuarded _ _ _ _ => cases same
    | callableEquation _ _ _ _ => cases same
    | callableGuarded _ _ _ _ _ => cases same
    | root _ _ _ _ _ _ _ _ _ => cases same
    | fresh _ _ _ => cases same
    | child _ _ _ _ _ _ _ => cases same
    | query _ _ _ _ _ => cases same
    | premisesNil _ => cases same
    | premisesCons _ _ _ _ _ _ _ => cases same
    | call _ _ _ _ _ _ _ _ _ => cases same

private theorem completeRoot {rows : List Atom} {index : Nat}
    {proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {left right subject target : Atom} {guards : List Atom} {initial final : Subst}
    (stored : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.ClauseAt rows index left right guards)
    (matched : SpaceSemantics.ValueMatch [] left subject initial)
    (later : (expandPremises? rows proof guards initial).map Sigma.fst = some final)
    (emitted : target = applySubst final right) :
    (expandRoot? rows (.firing index proof) subject).map Sigma.fst = some target := by
  with_unfolding_all
    obtain ⟨row, positioned, declared⟩ := stored
    have parsed := (MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.readClause?_exact row left right guards).mpr declared
    subst target
    dsimp only [expandRoot?]
    split
    next missing => rw [positioned] at missing; cases missing
    next actual selected =>
      have equal : actual = row := Option.some.inj (selected.symm.trans positioned)
      subst actual
      split
      next missing => rw [parsed] at missing; cases missing
      next actualLeft actualRight actualGuards selected =>
        have equal : (actualLeft, actualRight, actualGuards) = (left, right, guards) := Option.some.inj (selected.symm.trans parsed)
        have first := (Prod.mk.inj equal).1
        have second := (Prod.mk.inj (Prod.mk.inj equal).2).1
        have third := (Prod.mk.inj (Prod.mk.inj equal).2).2
        subst actualLeft
        subst actualRight
        subst actualGuards
        split
        next missing => rw [SpaceSemantics.matchValue_complete matched] at missing; cases missing
        next actual selected =>
          have equal : actual = initial := Option.some.inj (selected.symm.trans (SpaceSemantics.matchValue_complete matched))
          subst actual
          cases found : expandPremises? rows proof guards initial with
          | none => simp only [found, Option.map_none, reduceCtorEq] at later
          | some packet =>
              have equal : packet.1 = final := Option.some.inj (by simpa only [found, Option.map_some] using later)
              simp only [Option.map_some, equal]

private theorem completeFresh {rows : List Atom} {initial : Subst} {name : String} {subject : Atom}
    (held : SourceGuardHolds initial (.freshness name subject)) :
    (expandPremise? rows .fresh (.expression [.symbol "fresh", .var name, subject]) initial).map Sigma.fst = some initial := by
  with_unfolding_all
    rw [expandPremise?.eq_1]
    split
    next _ => rfl
    next refused => exact (refused ((matchSourceGuard_exact _ _).mpr held)).elim

private theorem completeChild {rows : List Atom}
    {proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {source target result : Atom} {initial final : Subst}
    (matched : SpaceSemantics.ValueMatch initial target result final)
    (child : (expandRoot? rows proof (applySubst initial source)).map Sigma.fst = some result) :
    (expandPremise? rows (.child proof) (.expression [.symbol "==", source, target]) initial).map Sigma.fst = some final := by
  with_unfolding_all
    rw [expandPremise?.eq_2]
    cases found : expandRoot? rows proof (applySubst initial source) with
    | none => simp only [found, Option.map_none, reduceCtorEq] at child
    | some packet =>
        have equal : packet.1 = result := Option.some.inj (by simpa only [found, Option.map_some] using child)
        rcases packet with ⟨actual, proof⟩
        dsimp only at equal
        subst actual
        dsimp only
        split
        next missing => rw [SpaceSemantics.matchValue_complete matched] at missing; cases missing
        next actual selected =>
          have equal : actual = final := Option.some.inj (selected.symm.trans (SpaceSemantics.matchValue_complete matched))
          subst actual
          rfl

private theorem completeQuery {rows : List Atom} {relation : String} {arguments : List Atom}
    {initial final : Subst} {origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin}
    (ordinary : relation ≠ "fresh") (directed : relation ≠ "==")
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.QueryHolds
      (environment rows) relation arguments initial origin final) :
    (expandPremise? rows (.query origin) (.expression (.symbol relation :: arguments)) initial).map Sigma.fst = some final := by
  with_unfolding_all
    have completed := expandQuery_complete source
    rw [expandPremise?.eq_3]
    split
    next _ =>
      cases found : expandQuery? rows relation arguments initial origin with
      | none => simp only [found, Option.map_none, reduceCtorEq] at completed
      | some packet =>
          have equal : packet.1 = final := Option.some.inj (by simpa only [found, Option.map_some] using completed)
          simp only [Option.map_some, equal]
    next refused => exact (refused ⟨ordinary, directed⟩).elim

private theorem completeCons {rows : List Atom}
    {head tail : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {guard : Atom} {guards : List Atom} {initial middle final : Subst}
    (first : (expandPremise? rows head guard initial).map Sigma.fst = some middle)
    (rest : (expandPremises? rows tail guards middle).map Sigma.fst = some final) :
    (expandPremises? rows (.cons head tail) (guard :: guards) initial).map Sigma.fst = some final := by
  with_unfolding_all
    dsimp only [expandPremises?]
    cases found : expandPremise? rows head guard initial with
    | none => simp only [found, Option.map_none, reduceCtorEq] at first
    | some packet =>
        have equal : packet.1 = middle := Option.some.inj (by simpa only [found, Option.map_some] using first)
        rcases packet with ⟨actual, proof⟩
        dsimp only at equal
        subst actual
        dsimp only
        cases ended : expandPremises? rows tail guards middle with
        | none => simp only [ended, Option.map_none, reduceCtorEq] at rest
        | some packet =>
            have equal : packet.1 = final := Option.some.inj (by simpa only [ended, Option.map_some] using rest)
            simp only [Option.map_some, equal]

theorem expandRoot_complete {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {subject target : Atom}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring
      (environment rows) evidence subject target) :
    (expandRoot? rows evidence subject).map Sigma.fst = some target :=
  MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring.rec
    (motive_1 := fun evidence subject target _ =>
      (expandRoot? rows evidence subject).map Sigma.fst = some target)
    (motive_2 := fun evidence guard initial final _ =>
      (expandPremise? rows evidence guard initial).map Sigma.fst = some final)
    (motive_3 := fun evidence guards initial final _ =>
      (expandPremises? rows evidence guards initial).map Sigma.fst = some final)
    (fun stored matched _ emitted ih => completeRoot stored matched ih emitted)
    completeFresh (fun _ matched ih => completeChild matched ih) completeQuery
    rfl (fun _ _ ihHead ihTail => completeCons ihHead ihTail) source

theorem expandPremise_complete {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {guard : Atom} {initial final : Subst}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremiseHolds
      (environment rows) evidence guard initial final) :
    (expandPremise? rows evidence guard initial).map Sigma.fst = some final :=
  MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremiseHolds.rec
    (motive_1 := fun evidence subject target _ =>
      (expandRoot? rows evidence subject).map Sigma.fst = some target)
    (motive_2 := fun evidence guard initial final _ =>
      (expandPremise? rows evidence guard initial).map Sigma.fst = some final)
    (motive_3 := fun evidence guards initial final _ =>
      (expandPremises? rows evidence guards initial).map Sigma.fst = some final)
    (fun stored matched _ emitted ih => completeRoot stored matched ih emitted)
    completeFresh (fun _ matched ih => completeChild matched ih) completeQuery
    rfl (fun _ _ ihHead ihTail => completeCons ihHead ihTail) source

theorem expandPremises_complete {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {guards : List Atom} {initial final : Subst}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremisesHold
      (environment rows) evidence guards initial final) :
    (expandPremises? rows evidence guards initial).map Sigma.fst = some final :=
  MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.PremisesHold.rec
    (motive_1 := fun evidence subject target _ =>
      (expandRoot? rows evidence subject).map Sigma.fst = some target)
    (motive_2 := fun evidence guard initial final _ =>
      (expandPremise? rows evidence guard initial).map Sigma.fst = some final)
    (motive_3 := fun evidence guards initial final _ =>
      (expandPremises? rows evidence guards initial).map Sigma.fst = some final)
    (fun stored matched _ emitted ih => completeRoot stored matched ih emitted)
    completeFresh (fun _ matched ih => completeChild matched ih) completeQuery
    rfl (fun _ _ ihHead ihTail => completeCons ihHead ihTail) source

theorem expandCall_complete {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {head : String} {values : List Atom} {index : Nat} {control : Eval.Control}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.CallReady
      (environment rows) head values evidence index control) :
    (expandCall? rows evidence head values).map
      (fun packet => (packet.1.1, Eval.Control.evaluate packet.1.2.1 packet.1.2.2)) = some (index, control) := by
  with_unfolding_all
    cases source with
    | guarded selected premises =>
      cases selected with
      | matched stored named matched =>
        obtain ⟨row, positioned, declared⟩ := stored
        dsimp only [environment] at positioned
        have parsed := (readRule?_exact _ _ _).mpr declared
        have later := expandPremises_complete premises
        dsimp only at later ⊢
        rw [expandCall?.eq_1]
        split
        next missing => rw [positioned] at missing; cases missing
        next actual selected =>
          have equal : actual = row := Option.some.inj (selected.symm.trans positioned)
          subst actual
          split
          next missing => rw [parsed] at missing; cases missing
          next actualEquation actualGuards selected =>
            have equal := Option.some.inj (selected.symm.trans parsed)
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
            split
            next _ =>
              split
              next missing => rw [SpaceSemantics.matchValue_complete matched] at missing; cases missing
              next actual selected =>
                have equal := Option.some.inj (selected.symm.trans (SpaceSemantics.matchValue_complete matched))
                subst actual
                split
                next missing => simp only [missing, Option.map_none, reduceCtorEq] at later
                next actual proof selected =>
                  have equal := Option.some.inj (by simpa only [selected, Option.map_some] using later)
                  subst actual
                  rfl
            next refused => exact (refused named).elim

theorem rootArticle?_complete {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {subject target : Atom}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring
      (environment rows) evidence subject target) :
    ∃ article, rootArticle? rows evidence subject = some (target, article) := by
  obtain ⟨packet, found, equal⟩ := Option.map_eq_some_iff.mp (expandRoot_complete source)
  rcases packet with ⟨actual, proof⟩
  dsimp only at equal
  subst actual
  exact ⟨Mettapedia.OSLF.NativeTypes.Certificates.Shared.emit proof, by
    simp only [rootArticle?, found, Option.map_some]⟩

theorem root_compilation_exact (rows : List Atom)
    (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence)
    (subject target : Atom) :
    (∃ article, rootArticle? rows evidence subject = some (target, article)) ↔
      MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.RootFiring
        (environment rows) evidence subject target :=
  ⟨fun ⟨_, compiled⟩ => (rootArticle?_sound compiled).2, rootArticle?_complete⟩

theorem callArticle?_complete {rows : List Atom}
    {evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence}
    {head : String} {values : List Atom} {index : Nat} {bindings : Subst} {body : Atom}
    (source : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.CallReady
      (environment rows) head values evidence index (.evaluate bindings body)) :
    ∃ article, callArticle? rows evidence head values = some ((index, bindings, body), article) := by
  obtain ⟨packet, found, equal⟩ := Option.map_eq_some_iff.mp (expandCall_complete source)
  rcases packet with ⟨⟨actualIndex, actualBindings, actualBody⟩, proof⟩
  simp only [Prod.mk.injEq, Eval.Control.evaluate.injEq] at equal
  obtain ⟨rfl, rfl, rfl⟩ := equal
  exact ⟨Mettapedia.OSLF.NativeTypes.Certificates.Shared.emit proof, by
    simp only [callArticle?, found, Option.map_some]⟩

theorem call_compilation_exact (rows : List Atom)
    (evidence : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence)
    (head : String) (values : List Atom) (index : Nat) (bindings : Subst) (body : Atom) :
    (∃ article, callArticle? rows evidence head values = some ((index, bindings, body), article)) ↔
      MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.CallReady
        (environment rows) head values evidence index (.evaluate bindings body) :=
  ⟨fun ⟨_, compiled⟩ => (callArticle?_sound compiled).2, callArticle?_complete⟩

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive.AtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open ConfigurationEncoding (bindingsData readBindings index readIndex)
open Mettapedia.OSLF.Binding.WireCodec

def text (value : String) : Atom := .grounded (.string value)
def readText : Atom → Option String
  | .grounded (.string value) => some value
  | _ => none

def readGround : Atom → Option GroundedValue
  | .grounded value => some value
  | _ => none

def readBoolean : Atom → Option Bool
  | .grounded (.bool value) => some value
  | _ => none

def atoms (values : List Atom) : Atom := .expression values
def readAtoms : Atom → Option (List Atom)
  | .expression values => some values
  | _ => none

def bitList (values : List Bool) : Atom := .expression (values.map Effects.boolean)
def readBits : List Atom → Option (List Bool)
  | [] => some []
  | head :: tail => do return (← readBoolean head) :: (← readBits tail)
def readBitList : Atom → Option (List Bool)
  | .expression values => readBits values
  | _ => none

theorem readBits_map (values : List Bool) : readBits (values.map Effects.boolean) = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, readBits, Effects.boolean, readBoolean, ih]; rfl

@[simp] theorem readBitList_bitList (values : List Bool) : readBitList (bitList values) = some values :=
  readBits_map values

def optional (value : Option Atom) : Atom := .expression value.toList
def readOptional : Atom → Option (Option Atom)
  | .expression [] => some none
  | .expression [value] => some (some value)
  | _ => none

@[simp] theorem readOptional_optional (value : Option Atom) : readOptional (optional value) = some value := by
  cases value <;> rfl

def putRule : Rule → Atom
  | .neNilCons bit rest => .expression [.symbol "difference", .expression [.symbol "nilCons", Effects.boolean bit, bitList rest]]
  | .neConsNil bit rest => .expression [.symbol "difference", .expression [.symbol "consNil", Effects.boolean bit, bitList rest]]
  | .neFalseTrue first second => .expression [.symbol "difference", .expression [.symbol "falseTrue", bitList first, bitList second]]
  | .neTrueFalse first second => .expression [.symbol "difference", .expression [.symbol "trueFalse", bitList first, bitList second]]
  | .nePrefix bit first second => .expression [.symbol "difference", .expression [.symbol "prefix", Effects.boolean bit, bitList first, bitList second]]
  | .neName first second => .expression [.symbol "difference", .expression [.symbol "name", text first, text second]]
  | .lookupNil name => .expression [.symbol "lookup", .expression [.symbol "nil", text name]]
  | .lookupHead name value rest => .expression [.symbol "lookup", .expression [.symbol "head", text name, value, bindingsData rest]]
  | .lookupSkip name other value rest result => .expression [.symbol "lookup", .expression [.symbol "skip", text name, text other, value, bindingsData rest, optional result]]
  | .substUnbound bindings name => .expression [.symbol "substitution", .expression [.symbol "unbound", bindingsData bindings, text name]]
  | .substBound bindings name value => .expression [.symbol "substitution", .expression [.symbol "bound", bindingsData bindings, text name, value]]
  | .substSymbol bindings name => .expression [.symbol "substitution", .expression [.symbol "symbol", bindingsData bindings, text name]]
  | .substGrounded bindings value => .expression [.symbol "substitution", .expression [.symbol "grounded", bindingsData bindings, Atom.grounded value]]
  | .substExpression bindings inputs outputs => .expression [.symbol "substitution", .expression [.symbol "expression", bindingsData bindings, atoms inputs, atoms outputs]]
  | .substNil bindings => .expression [.symbol "substitution", .expression [.symbol "nil", bindingsData bindings]]
  | .substCons bindings input output inputs outputs => .expression [.symbol "substitution", .expression [.symbol "cons", bindingsData bindings, input, output, atoms inputs, atoms outputs]]
  | .freshVar name other => .expression [.symbol "freshness", .expression [.symbol "var", text name, text other]]
  | .freshSymbol name symbol => .expression [.symbol "freshness", .expression [.symbol "symbol", text name, text symbol]]
  | .freshGrounded name value => .expression [.symbol "freshness", .expression [.symbol "grounded", text name, Atom.grounded value]]
  | .freshExpression name values => .expression [.symbol "freshness", .expression [.symbol "expression", text name, atoms values]]
  | .freshNil name => .expression [.symbol "freshness", .expression [.symbol "nil", text name]]
  | .freshCons name value values => .expression [.symbol "freshness", .expression [.symbol "cons", text name, value, atoms values]]
  | .ordinaryNil => .expression [.symbol "ordinary", .expression [.symbol "nil"]]
  | .ordinaryOne a => .expression [.symbol "ordinary", .expression [.symbol "one", a]]
  | .ordinaryTwo a b => .expression [.symbol "ordinary", .expression [.symbol "two", a, b]]
  | .ordinaryLong a b c d rest => .expression [.symbol "ordinary", .expression [.symbol "long", a, b, c, d, atoms rest]]
  | .ordinaryVar name a b => .expression [.symbol "ordinary", .expression [.symbol "var", text name, a, b]]
  | .ordinaryGrounded value a b => .expression [.symbol "ordinary", .expression [.symbol "grounded", Atom.grounded value, a, b]]
  | .ordinaryExpression fields a b => .expression [.symbol "ordinary", .expression [.symbol "expression", atoms fields, a, b]]
  | .ordinarySymbol name a b => .expression [.symbol "ordinary", .expression [.symbol "symbol", text name, a, b]]
  | .unquotedVar name => .expression [.symbol "unquoted", .expression [.symbol "var", text name]]
  | .unquotedSymbol name => .expression [.symbol "unquoted", .expression [.symbol "symbol", text name]]
  | .unquotedGrounded value => .expression [.symbol "unquoted", .expression [.symbol "grounded", Atom.grounded value]]
  | .unquotedNil => .expression [.symbol "unquoted", .expression [.symbol "nil"]]
  | .unquotedOne a => .expression [.symbol "unquoted", .expression [.symbol "one", a]]
  | .unquotedLong a b c rest => .expression [.symbol "unquoted", .expression [.symbol "long", a, b, c, atoms rest]]
  | .unquotedHeadVar name a => .expression [.symbol "unquoted", .expression [.symbol "headVar", text name, a]]
  | .unquotedHeadGrounded value a => .expression [.symbol "unquoted", .expression [.symbol "headGrounded", Atom.grounded value, a]]
  | .unquotedHeadExpression fields a => .expression [.symbol "unquoted", .expression [.symbol "headExpression", atoms fields, a]]
  | .unquotedHeadSymbol name a => .expression [.symbol "unquoted", .expression [.symbol "headSymbol", text name, a]]
  | .matchFresh initial name value => .expression [.symbol "match", .expression [.symbol "fresh", bindingsData initial, text name, value]]
  | .matchBound initial name value => .expression [.symbol "match", .expression [.symbol "bound", bindingsData initial, text name, value]]
  | .matchSymbol initial name => .expression [.symbol "match", .expression [.symbol "symbol", bindingsData initial, text name]]
  | .matchGrounded initial value => .expression [.symbol "match", .expression [.symbol "grounded", bindingsData initial, Atom.grounded value]]
  | .matchNil initial => .expression [.symbol "match", .expression [.symbol "nil", bindingsData initial]]
  | .matchCons initial middle final pattern value patterns values => .expression [.symbol "match", .expression [.symbol "cons", bindingsData initial, bindingsData middle, bindingsData final, pattern, value, atoms patterns, atoms values]]
  | .valueCons initial middle final first rest head tail => .expression [.symbol "value", .expression [.symbol "cons", bindingsData initial, bindingsData middle, bindingsData final, first, rest, head, atoms tail]]
  | .valueExpression initial final patterns values => .expression [.symbol "value", .expression [.symbol "expression", bindingsData initial, bindingsData final, atoms patterns, atoms values]]
  | .valueVar initial final name value => .expression [.symbol "value", .expression [.symbol "var", bindingsData initial, bindingsData final, text name, value]]
  | .valueSymbol initial final name value => .expression [.symbol "value", .expression [.symbol "symbol", bindingsData initial, bindingsData final, text name, value]]
  | .valueGrounded initial final ground value => .expression [.symbol "value", .expression [.symbol "grounded", bindingsData initial, bindingsData final, Atom.grounded ground, value]]
  | .valuesNil initial => .expression [.symbol "values", .expression [.symbol "nil", bindingsData initial]]
  | .valuesCons initial middle final pattern value patterns values => .expression [.symbol "values", .expression [.symbol "cons", bindingsData initial, bindingsData middle, bindingsData final, pattern, value, atoms patterns, atoms values]]
  | .bindingQuoted initial final literal value => .expression [.symbol "binding", .expression [.symbol "quoted", bindingsData initial, bindingsData final, literal, value]]
  | .bindingOrdinary initial final pattern value => .expression [.symbol "binding", .expression [.symbol "ordinary", bindingsData initial, bindingsData final, pattern, value]]
  | .guardUnbound initial name subject instantiated => .expression [.symbol "guard", .expression [.symbol "unbound", bindingsData initial, text name, subject, instantiated]]
  | .guardCaptured initial name resolved subject instantiated => .expression [.symbol "guard", .expression [.symbol "captured", bindingsData initial, text name, text resolved, subject, instantiated]]

def read_ne : List Atom → Option Rule
  | [.symbol "nilCons", bit, rest] => do return .neNilCons (← readBoolean bit) (← readBitList rest)
  | [.symbol "consNil", bit, rest] => do return .neConsNil (← readBoolean bit) (← readBitList rest)
  | [.symbol "falseTrue", first, second] => do return .neFalseTrue (← readBitList first) (← readBitList second)
  | [.symbol "trueFalse", first, second] => do return .neTrueFalse (← readBitList first) (← readBitList second)
  | [.symbol "prefix", bit, first, second] => do return .nePrefix (← readBoolean bit) (← readBitList first) (← readBitList second)
  | [.symbol "name", first, second] => do return .neName (← readText first) (← readText second)
  | _ => none

def read_lookup : List Atom → Option Rule
  | [.symbol "nil", name] => do return .lookupNil (← readText name)
  | [.symbol "head", name, value, rest] => do return .lookupHead (← readText name) (← some value) (← readBindings rest)
  | [.symbol "skip", name, other, value, rest, result] => do return .lookupSkip (← readText name) (← readText other) (← some value) (← readBindings rest) (← readOptional result)
  | _ => none

def read_subst : List Atom → Option Rule
  | [.symbol "unbound", bindings, name] => do return .substUnbound (← readBindings bindings) (← readText name)
  | [.symbol "bound", bindings, name, value] => do return .substBound (← readBindings bindings) (← readText name) (← some value)
  | [.symbol "symbol", bindings, name] => do return .substSymbol (← readBindings bindings) (← readText name)
  | [.symbol "grounded", bindings, value] => do return .substGrounded (← readBindings bindings) (← readGround value)
  | [.symbol "expression", bindings, inputs, outputs] => do return .substExpression (← readBindings bindings) (← readAtoms inputs) (← readAtoms outputs)
  | [.symbol "nil", bindings] => do return .substNil (← readBindings bindings)
  | [.symbol "cons", bindings, input, output, inputs, outputs] => do return .substCons (← readBindings bindings) (← some input) (← some output) (← readAtoms inputs) (← readAtoms outputs)
  | _ => none

def read_fresh : List Atom → Option Rule
  | [.symbol "var", name, other] => do return .freshVar (← readText name) (← readText other)
  | [.symbol "symbol", name, symbol] => do return .freshSymbol (← readText name) (← readText symbol)
  | [.symbol "grounded", name, value] => do return .freshGrounded (← readText name) (← readGround value)
  | [.symbol "expression", name, values] => do return .freshExpression (← readText name) (← readAtoms values)
  | [.symbol "nil", name] => do return .freshNil (← readText name)
  | [.symbol "cons", name, value, values] => do return .freshCons (← readText name) (← some value) (← readAtoms values)
  | _ => none

def read_ordinary : List Atom → Option Rule
  | [.symbol "nil"] => some .ordinaryNil
  | [.symbol "one", a] => do return .ordinaryOne (← some a)
  | [.symbol "two", a, b] => do return .ordinaryTwo (← some a) (← some b)
  | [.symbol "long", a, b, c, d, rest] => do return .ordinaryLong (← some a) (← some b) (← some c) (← some d) (← readAtoms rest)
  | [.symbol "var", name, a, b] => do return .ordinaryVar (← readText name) (← some a) (← some b)
  | [.symbol "grounded", value, a, b] => do return .ordinaryGrounded (← readGround value) (← some a) (← some b)
  | [.symbol "expression", fields, a, b] => do return .ordinaryExpression (← readAtoms fields) (← some a) (← some b)
  | [.symbol "symbol", name, a, b] => do return .ordinarySymbol (← readText name) (← some a) (← some b)
  | _ => none

def read_unquoted : List Atom → Option Rule
  | [.symbol "var", name] => do return .unquotedVar (← readText name)
  | [.symbol "symbol", name] => do return .unquotedSymbol (← readText name)
  | [.symbol "grounded", value] => do return .unquotedGrounded (← readGround value)
  | [.symbol "nil"] => some .unquotedNil
  | [.symbol "one", a] => do return .unquotedOne (← some a)
  | [.symbol "long", a, b, c, rest] => do return .unquotedLong (← some a) (← some b) (← some c) (← readAtoms rest)
  | [.symbol "headVar", name, a] => do return .unquotedHeadVar (← readText name) (← some a)
  | [.symbol "headGrounded", value, a] => do return .unquotedHeadGrounded (← readGround value) (← some a)
  | [.symbol "headExpression", fields, a] => do return .unquotedHeadExpression (← readAtoms fields) (← some a)
  | [.symbol "headSymbol", name, a] => do return .unquotedHeadSymbol (← readText name) (← some a)
  | _ => none

def read_match : List Atom → Option Rule
  | [.symbol "fresh", initial, name, value] => do return .matchFresh (← readBindings initial) (← readText name) (← some value)
  | [.symbol "bound", initial, name, value] => do return .matchBound (← readBindings initial) (← readText name) (← some value)
  | [.symbol "symbol", initial, name] => do return .matchSymbol (← readBindings initial) (← readText name)
  | [.symbol "grounded", initial, value] => do return .matchGrounded (← readBindings initial) (← readGround value)
  | [.symbol "nil", initial] => do return .matchNil (← readBindings initial)
  | [.symbol "cons", initial, middle, final, pattern, value, patterns, values] => do return .matchCons (← readBindings initial) (← readBindings middle) (← readBindings final) (← some pattern) (← some value) (← readAtoms patterns) (← readAtoms values)
  | _ => none

def read_value : List Atom → Option Rule
  | [.symbol "cons", initial, middle, final, first, rest, head, tail] => do return .valueCons (← readBindings initial) (← readBindings middle) (← readBindings final) (← some first) (← some rest) (← some head) (← readAtoms tail)
  | [.symbol "expression", initial, final, patterns, values] => do return .valueExpression (← readBindings initial) (← readBindings final) (← readAtoms patterns) (← readAtoms values)
  | [.symbol "var", initial, final, name, value] => do return .valueVar (← readBindings initial) (← readBindings final) (← readText name) (← some value)
  | [.symbol "symbol", initial, final, name, value] => do return .valueSymbol (← readBindings initial) (← readBindings final) (← readText name) (← some value)
  | [.symbol "grounded", initial, final, ground, value] => do return .valueGrounded (← readBindings initial) (← readBindings final) (← readGround ground) (← some value)
  | _ => none

def read_values : List Atom → Option Rule
  | [.symbol "nil", initial] => do return .valuesNil (← readBindings initial)
  | [.symbol "cons", initial, middle, final, pattern, value, patterns, values] => do return .valuesCons (← readBindings initial) (← readBindings middle) (← readBindings final) (← some pattern) (← some value) (← readAtoms patterns) (← readAtoms values)
  | _ => none

def read_binding : List Atom → Option Rule
  | [.symbol "quoted", initial, final, literal, value] => do return .bindingQuoted (← readBindings initial) (← readBindings final) (← some literal) (← some value)
  | [.symbol "ordinary", initial, final, pattern, value] => do return .bindingOrdinary (← readBindings initial) (← readBindings final) (← some pattern) (← some value)
  | _ => none

def read_guard : List Atom → Option Rule
  | [.symbol "unbound", initial, name, subject, instantiated] => do return .guardUnbound (← readBindings initial) (← readText name) (← some subject) (← some instantiated)
  | [.symbol "captured", initial, name, resolved, subject, instantiated] => do return .guardCaptured (← readBindings initial) (← readText name) (← readText resolved) (← some subject) (← some instantiated)
  | _ => none

def readRule : Atom → Option Rule
  | .expression [.symbol "difference", .expression fields] => read_ne fields
  | .expression [.symbol "lookup", .expression fields] => read_lookup fields
  | .expression [.symbol "substitution", .expression fields] => read_subst fields
  | .expression [.symbol "freshness", .expression fields] => read_fresh fields
  | .expression [.symbol "ordinary", .expression fields] => read_ordinary fields
  | .expression [.symbol "unquoted", .expression fields] => read_unquoted fields
  | .expression [.symbol "match", .expression fields] => read_match fields
  | .expression [.symbol "value", .expression fields] => read_value fields
  | .expression [.symbol "values", .expression fields] => read_values fields
  | .expression [.symbol "binding", .expression fields] => read_binding fields
  | .expression [.symbol "guard", .expression fields] => read_guard fields
  | _ => none

private theorem roundtrip_neNilCons (bit : Bool) (rest : List Bool) :
    readRule (putRule (.neNilCons bit rest)) = some (.neNilCons bit rest) := by
  rw [putRule.eq_1, readRule.eq_1, read_ne.eq_1]
  simp only [Effects.boolean, readBoolean, readBitList_bitList]; rfl

private theorem roundtrip_neConsNil (bit : Bool) (rest : List Bool) :
    readRule (putRule (.neConsNil bit rest)) = some (.neConsNil bit rest) := by
  rw [putRule.eq_2, readRule.eq_1, read_ne.eq_2]
  simp only [Effects.boolean, readBoolean, readBitList_bitList]; rfl

private theorem roundtrip_neFalseTrue (first : List Bool) (second : List Bool) :
    readRule (putRule (.neFalseTrue first second)) = some (.neFalseTrue first second) := by
  rw [putRule.eq_3, readRule.eq_1, read_ne.eq_3]
  simp only [readBitList_bitList]; rfl

private theorem roundtrip_neTrueFalse (first : List Bool) (second : List Bool) :
    readRule (putRule (.neTrueFalse first second)) = some (.neTrueFalse first second) := by
  rw [putRule.eq_4, readRule.eq_1, read_ne.eq_4]
  simp only [readBitList_bitList]; rfl

private theorem roundtrip_nePrefix (bit : Bool) (first : List Bool) (second : List Bool) :
    readRule (putRule (.nePrefix bit first second)) = some (.nePrefix bit first second) := by
  rw [putRule.eq_5, readRule.eq_1, read_ne.eq_5]
  simp only [Effects.boolean, readBoolean, readBitList_bitList]; rfl

private theorem roundtrip_neName (first : String) (second : String) :
    readRule (putRule (.neName first second)) = some (.neName first second) := by
  rw [putRule.eq_6, readRule.eq_1, read_ne.eq_6]
  simp only [readText, text]; rfl

private theorem roundtrip_lookupNil (name : String) :
    readRule (putRule (.lookupNil name)) = some (.lookupNil name) := by
  rw [putRule.eq_7, readRule.eq_2, read_lookup.eq_1]
  simp only [readText, text]; rfl

private theorem roundtrip_lookupHead (name : String) (value : Atom) (rest : Subst) :
    readRule (putRule (.lookupHead name value rest)) = some (.lookupHead name value rest) := by
  rw [putRule.eq_8, readRule.eq_2, read_lookup.eq_2]
  simp only [readText, text, ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_lookupSkip (name : String) (other : String) (value : Atom) (rest : Subst) (result : Option Atom) :
    readRule (putRule (.lookupSkip name other value rest result)) = some (.lookupSkip name other value rest result) := by
  rw [putRule.eq_9, readRule.eq_2, read_lookup.eq_3]
  simp only [readText, text, ConfigurationEncoding.readBindings_bindingsData, readOptional_optional]; rfl

private theorem roundtrip_substUnbound (bindings : Subst) (name : String) :
    readRule (putRule (.substUnbound bindings name)) = some (.substUnbound bindings name) := by
  rw [putRule.eq_10, readRule.eq_3, read_subst.eq_1]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_substBound (bindings : Subst) (name : String) (value : Atom) :
    readRule (putRule (.substBound bindings name value)) = some (.substBound bindings name value) := by
  rw [putRule.eq_11, readRule.eq_3, read_subst.eq_2]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_substSymbol (bindings : Subst) (name : String) :
    readRule (putRule (.substSymbol bindings name)) = some (.substSymbol bindings name) := by
  rw [putRule.eq_12, readRule.eq_3, read_subst.eq_3]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_substGrounded (bindings : Subst) (value : GroundedValue) :
    readRule (putRule (.substGrounded bindings value)) = some (.substGrounded bindings value) := by
  rw [putRule.eq_13, readRule.eq_3, read_subst.eq_4]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readGround]; rfl

private theorem roundtrip_substExpression (bindings : Subst) (inputs : List Atom) (outputs : List Atom) :
    readRule (putRule (.substExpression bindings inputs outputs)) = some (.substExpression bindings inputs outputs) := by
  rw [putRule.eq_14, readRule.eq_3, read_subst.eq_5]
  simp only [ConfigurationEncoding.readBindings_bindingsData, atoms, readAtoms]; rfl

private theorem roundtrip_substNil (bindings : Subst) :
    readRule (putRule (.substNil bindings)) = some (.substNil bindings) := by
  rw [putRule.eq_15, readRule.eq_3, read_subst.eq_6]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_substCons (bindings : Subst) (input : Atom) (output : Atom) (inputs : List Atom) (outputs : List Atom) :
    readRule (putRule (.substCons bindings input output inputs outputs)) = some (.substCons bindings input output inputs outputs) := by
  rw [putRule.eq_16, readRule.eq_3, read_subst.eq_7]
  simp only [ConfigurationEncoding.readBindings_bindingsData, atoms, readAtoms]; rfl

private theorem roundtrip_freshVar (name : String) (other : String) :
    readRule (putRule (.freshVar name other)) = some (.freshVar name other) := by
  rw [putRule.eq_17, readRule.eq_4, read_fresh.eq_1]
  simp only [readText, text]; rfl

private theorem roundtrip_freshSymbol (name : String) (symbol : String) :
    readRule (putRule (.freshSymbol name symbol)) = some (.freshSymbol name symbol) := by
  rw [putRule.eq_18, readRule.eq_4, read_fresh.eq_2]
  simp only [readText, text]; rfl

private theorem roundtrip_freshGrounded (name : String) (value : GroundedValue) :
    readRule (putRule (.freshGrounded name value)) = some (.freshGrounded name value) := by
  rw [putRule.eq_19, readRule.eq_4, read_fresh.eq_3]
  simp only [readText, text, readGround]; rfl

private theorem roundtrip_freshExpression (name : String) (values : List Atom) :
    readRule (putRule (.freshExpression name values)) = some (.freshExpression name values) := by
  rw [putRule.eq_20, readRule.eq_4, read_fresh.eq_4]
  simp only [readText, text, atoms, readAtoms]; rfl

private theorem roundtrip_freshNil (name : String) :
    readRule (putRule (.freshNil name)) = some (.freshNil name) := by
  rw [putRule.eq_21, readRule.eq_4, read_fresh.eq_5]
  simp only [readText, text]; rfl

private theorem roundtrip_freshCons (name : String) (value : Atom) (values : List Atom) :
    readRule (putRule (.freshCons name value values)) = some (.freshCons name value values) := by
  rw [putRule.eq_22, readRule.eq_4, read_fresh.eq_6]
  simp only [readText, text, atoms, readAtoms]; rfl

private theorem roundtrip_ordinaryNil :
    readRule (putRule (.ordinaryNil)) = some (.ordinaryNil) := by
  rw [putRule.eq_23, readRule.eq_5, read_ordinary.eq_1]

private theorem roundtrip_ordinaryOne (a : Atom) :
    readRule (putRule (.ordinaryOne a)) = some (.ordinaryOne a) := by
  rw [putRule.eq_24, readRule.eq_5, read_ordinary.eq_2]
  rfl

private theorem roundtrip_ordinaryTwo (a : Atom) (b : Atom) :
    readRule (putRule (.ordinaryTwo a b)) = some (.ordinaryTwo a b) := by
  rw [putRule.eq_25, readRule.eq_5, read_ordinary.eq_3]
  rfl

private theorem roundtrip_ordinaryLong (a : Atom) (b : Atom) (c : Atom) (d : Atom) (rest : List Atom) :
    readRule (putRule (.ordinaryLong a b c d rest)) = some (.ordinaryLong a b c d rest) := by
  rw [putRule.eq_26, readRule.eq_5, read_ordinary.eq_4]
  simp only [atoms, readAtoms]; rfl

private theorem roundtrip_ordinaryVar (name : String) (a : Atom) (b : Atom) :
    readRule (putRule (.ordinaryVar name a b)) = some (.ordinaryVar name a b) := by
  rw [putRule.eq_27, readRule.eq_5, read_ordinary.eq_5]
  simp only [readText, text]; rfl

private theorem roundtrip_ordinaryGrounded (value : GroundedValue) (a : Atom) (b : Atom) :
    readRule (putRule (.ordinaryGrounded value a b)) = some (.ordinaryGrounded value a b) := by
  rw [putRule.eq_28, readRule.eq_5, read_ordinary.eq_6]
  simp only [readGround]; rfl

private theorem roundtrip_ordinaryExpression (fields : List Atom) (a : Atom) (b : Atom) :
    readRule (putRule (.ordinaryExpression fields a b)) = some (.ordinaryExpression fields a b) := by
  rw [putRule.eq_29, readRule.eq_5, read_ordinary.eq_7]
  simp only [atoms, readAtoms]; rfl

private theorem roundtrip_ordinarySymbol (name : String) (a : Atom) (b : Atom) :
    readRule (putRule (.ordinarySymbol name a b)) = some (.ordinarySymbol name a b) := by
  rw [putRule.eq_30, readRule.eq_5, read_ordinary.eq_8]
  simp only [readText, text]; rfl

private theorem roundtrip_unquotedVar (name : String) :
    readRule (putRule (.unquotedVar name)) = some (.unquotedVar name) := by
  rw [putRule.eq_31, readRule.eq_6, read_unquoted.eq_1]
  simp only [readText, text]; rfl

private theorem roundtrip_unquotedSymbol (name : String) :
    readRule (putRule (.unquotedSymbol name)) = some (.unquotedSymbol name) := by
  rw [putRule.eq_32, readRule.eq_6, read_unquoted.eq_2]
  simp only [readText, text]; rfl

private theorem roundtrip_unquotedGrounded (value : GroundedValue) :
    readRule (putRule (.unquotedGrounded value)) = some (.unquotedGrounded value) := by
  rw [putRule.eq_33, readRule.eq_6, read_unquoted.eq_3]
  simp only [readGround]; rfl

private theorem roundtrip_unquotedNil :
    readRule (putRule (.unquotedNil)) = some (.unquotedNil) := by
  rw [putRule.eq_34, readRule.eq_6, read_unquoted.eq_4]

private theorem roundtrip_unquotedOne (a : Atom) :
    readRule (putRule (.unquotedOne a)) = some (.unquotedOne a) := by
  rw [putRule.eq_35, readRule.eq_6, read_unquoted.eq_5]
  rfl

private theorem roundtrip_unquotedLong (a : Atom) (b : Atom) (c : Atom) (rest : List Atom) :
    readRule (putRule (.unquotedLong a b c rest)) = some (.unquotedLong a b c rest) := by
  rw [putRule.eq_36, readRule.eq_6, read_unquoted.eq_6]
  simp only [atoms, readAtoms]; rfl

private theorem roundtrip_unquotedHeadVar (name : String) (a : Atom) :
    readRule (putRule (.unquotedHeadVar name a)) = some (.unquotedHeadVar name a) := by
  rw [putRule.eq_37, readRule.eq_6, read_unquoted.eq_7]
  simp only [readText, text]; rfl

private theorem roundtrip_unquotedHeadGrounded (value : GroundedValue) (a : Atom) :
    readRule (putRule (.unquotedHeadGrounded value a)) = some (.unquotedHeadGrounded value a) := by
  rw [putRule.eq_38, readRule.eq_6, read_unquoted.eq_8]
  simp only [readGround]; rfl

private theorem roundtrip_unquotedHeadExpression (fields : List Atom) (a : Atom) :
    readRule (putRule (.unquotedHeadExpression fields a)) = some (.unquotedHeadExpression fields a) := by
  rw [putRule.eq_39, readRule.eq_6, read_unquoted.eq_9]
  simp only [atoms, readAtoms]; rfl

private theorem roundtrip_unquotedHeadSymbol (name : String) (a : Atom) :
    readRule (putRule (.unquotedHeadSymbol name a)) = some (.unquotedHeadSymbol name a) := by
  rw [putRule.eq_40, readRule.eq_6, read_unquoted.eq_10]
  simp only [readText, text]; rfl

private theorem roundtrip_matchFresh (initial : Subst) (name : String) (value : Atom) :
    readRule (putRule (.matchFresh initial name value)) = some (.matchFresh initial name value) := by
  rw [putRule.eq_41, readRule.eq_7, read_match.eq_1]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_matchBound (initial : Subst) (name : String) (value : Atom) :
    readRule (putRule (.matchBound initial name value)) = some (.matchBound initial name value) := by
  rw [putRule.eq_42, readRule.eq_7, read_match.eq_2]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_matchSymbol (initial : Subst) (name : String) :
    readRule (putRule (.matchSymbol initial name)) = some (.matchSymbol initial name) := by
  rw [putRule.eq_43, readRule.eq_7, read_match.eq_3]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_matchGrounded (initial : Subst) (value : GroundedValue) :
    readRule (putRule (.matchGrounded initial value)) = some (.matchGrounded initial value) := by
  rw [putRule.eq_44, readRule.eq_7, read_match.eq_4]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readGround]; rfl

private theorem roundtrip_matchNil (initial : Subst) :
    readRule (putRule (.matchNil initial)) = some (.matchNil initial) := by
  rw [putRule.eq_45, readRule.eq_7, read_match.eq_5]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_matchCons (initial : Subst) (middle : Subst) (final : Subst) (pattern : Atom) (value : Atom) (patterns : List Atom) (values : List Atom) :
    readRule (putRule (.matchCons initial middle final pattern value patterns values)) = some (.matchCons initial middle final pattern value patterns values) := by
  rw [putRule.eq_46, readRule.eq_7, read_match.eq_6]
  simp only [ConfigurationEncoding.readBindings_bindingsData, atoms, readAtoms]; rfl

private theorem roundtrip_valueCons (initial : Subst) (middle : Subst) (final : Subst) (first : Atom) (rest : Atom) (head : Atom) (tail : List Atom) :
    readRule (putRule (.valueCons initial middle final first rest head tail)) = some (.valueCons initial middle final first rest head tail) := by
  rw [putRule.eq_47, readRule.eq_8, read_value.eq_1]
  simp only [ConfigurationEncoding.readBindings_bindingsData, atoms, readAtoms]; rfl

private theorem roundtrip_valueExpression (initial : Subst) (final : Subst) (patterns : List Atom) (values : List Atom) :
    readRule (putRule (.valueExpression initial final patterns values)) = some (.valueExpression initial final patterns values) := by
  rw [putRule.eq_48, readRule.eq_8, read_value.eq_2]
  simp only [ConfigurationEncoding.readBindings_bindingsData, atoms, readAtoms]; rfl

private theorem roundtrip_valueVar (initial : Subst) (final : Subst) (name : String) (value : Atom) :
    readRule (putRule (.valueVar initial final name value)) = some (.valueVar initial final name value) := by
  rw [putRule.eq_49, readRule.eq_8, read_value.eq_3]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_valueSymbol (initial : Subst) (final : Subst) (name : String) (value : Atom) :
    readRule (putRule (.valueSymbol initial final name value)) = some (.valueSymbol initial final name value) := by
  rw [putRule.eq_50, readRule.eq_8, read_value.eq_4]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_valueGrounded (initial : Subst) (final : Subst) (ground : GroundedValue) (value : Atom) :
    readRule (putRule (.valueGrounded initial final ground value)) = some (.valueGrounded initial final ground value) := by
  rw [putRule.eq_51, readRule.eq_8, read_value.eq_5]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readGround]; rfl

private theorem roundtrip_valuesNil (initial : Subst) :
    readRule (putRule (.valuesNil initial)) = some (.valuesNil initial) := by
  rw [putRule.eq_52, readRule.eq_9, read_values.eq_1]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_valuesCons (initial : Subst) (middle : Subst) (final : Subst) (pattern : Atom) (value : Atom) (patterns : List Atom) (values : List Atom) :
    readRule (putRule (.valuesCons initial middle final pattern value patterns values)) = some (.valuesCons initial middle final pattern value patterns values) := by
  rw [putRule.eq_53, readRule.eq_9, read_values.eq_2]
  simp only [ConfigurationEncoding.readBindings_bindingsData, atoms, readAtoms]; rfl

private theorem roundtrip_bindingQuoted (initial : Subst) (final : Subst) (literal : Atom) (value : Atom) :
    readRule (putRule (.bindingQuoted initial final literal value)) = some (.bindingQuoted initial final literal value) := by
  rw [putRule.eq_54, readRule.eq_10, read_binding.eq_1]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_bindingOrdinary (initial : Subst) (final : Subst) (pattern : Atom) (value : Atom) :
    readRule (putRule (.bindingOrdinary initial final pattern value)) = some (.bindingOrdinary initial final pattern value) := by
  rw [putRule.eq_55, readRule.eq_10, read_binding.eq_2]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_guardUnbound (initial : Subst) (name : String) (subject : Atom) (instantiated : Atom) :
    readRule (putRule (.guardUnbound initial name subject instantiated)) = some (.guardUnbound initial name subject instantiated) := by
  rw [putRule.eq_56, readRule.eq_11, read_guard.eq_1]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_guardCaptured (initial : Subst) (name : String) (resolved : String) (subject : Atom) (instantiated : Atom) :
    readRule (putRule (.guardCaptured initial name resolved subject instantiated)) = some (.guardCaptured initial name resolved subject instantiated) := by
  rw [putRule.eq_57, readRule.eq_11, read_guard.eq_2]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

theorem readRule_putRule (rule : Rule) : readRule (putRule rule) = some rule := by
  cases rule with
  | neNilCons bit rest => exact roundtrip_neNilCons bit rest
  | neConsNil bit rest => exact roundtrip_neConsNil bit rest
  | neFalseTrue first second => exact roundtrip_neFalseTrue first second
  | neTrueFalse first second => exact roundtrip_neTrueFalse first second
  | nePrefix bit first second => exact roundtrip_nePrefix bit first second
  | neName first second => exact roundtrip_neName first second
  | lookupNil name => exact roundtrip_lookupNil name
  | lookupHead name value rest => exact roundtrip_lookupHead name value rest
  | lookupSkip name other value rest result => exact roundtrip_lookupSkip name other value rest result
  | substUnbound bindings name => exact roundtrip_substUnbound bindings name
  | substBound bindings name value => exact roundtrip_substBound bindings name value
  | substSymbol bindings name => exact roundtrip_substSymbol bindings name
  | substGrounded bindings value => exact roundtrip_substGrounded bindings value
  | substExpression bindings inputs outputs => exact roundtrip_substExpression bindings inputs outputs
  | substNil bindings => exact roundtrip_substNil bindings
  | substCons bindings input output inputs outputs => exact roundtrip_substCons bindings input output inputs outputs
  | freshVar name other => exact roundtrip_freshVar name other
  | freshSymbol name symbol => exact roundtrip_freshSymbol name symbol
  | freshGrounded name value => exact roundtrip_freshGrounded name value
  | freshExpression name values => exact roundtrip_freshExpression name values
  | freshNil name => exact roundtrip_freshNil name
  | freshCons name value values => exact roundtrip_freshCons name value values
  | ordinaryNil => exact roundtrip_ordinaryNil
  | ordinaryOne a => exact roundtrip_ordinaryOne a
  | ordinaryTwo a b => exact roundtrip_ordinaryTwo a b
  | ordinaryLong a b c d rest => exact roundtrip_ordinaryLong a b c d rest
  | ordinaryVar name a b => exact roundtrip_ordinaryVar name a b
  | ordinaryGrounded value a b => exact roundtrip_ordinaryGrounded value a b
  | ordinaryExpression fields a b => exact roundtrip_ordinaryExpression fields a b
  | ordinarySymbol name a b => exact roundtrip_ordinarySymbol name a b
  | unquotedVar name => exact roundtrip_unquotedVar name
  | unquotedSymbol name => exact roundtrip_unquotedSymbol name
  | unquotedGrounded value => exact roundtrip_unquotedGrounded value
  | unquotedNil => exact roundtrip_unquotedNil
  | unquotedOne a => exact roundtrip_unquotedOne a
  | unquotedLong a b c rest => exact roundtrip_unquotedLong a b c rest
  | unquotedHeadVar name a => exact roundtrip_unquotedHeadVar name a
  | unquotedHeadGrounded value a => exact roundtrip_unquotedHeadGrounded value a
  | unquotedHeadExpression fields a => exact roundtrip_unquotedHeadExpression fields a
  | unquotedHeadSymbol name a => exact roundtrip_unquotedHeadSymbol name a
  | matchFresh initial name value => exact roundtrip_matchFresh initial name value
  | matchBound initial name value => exact roundtrip_matchBound initial name value
  | matchSymbol initial name => exact roundtrip_matchSymbol initial name
  | matchGrounded initial value => exact roundtrip_matchGrounded initial value
  | matchNil initial => exact roundtrip_matchNil initial
  | matchCons initial middle final pattern value patterns values => exact roundtrip_matchCons initial middle final pattern value patterns values
  | valueCons initial middle final first rest head tail => exact roundtrip_valueCons initial middle final first rest head tail
  | valueExpression initial final patterns values => exact roundtrip_valueExpression initial final patterns values
  | valueVar initial final name value => exact roundtrip_valueVar initial final name value
  | valueSymbol initial final name value => exact roundtrip_valueSymbol initial final name value
  | valueGrounded initial final ground value => exact roundtrip_valueGrounded initial final ground value
  | valuesNil initial => exact roundtrip_valuesNil initial
  | valuesCons initial middle final pattern value patterns values => exact roundtrip_valuesCons initial middle final pattern value patterns values
  | bindingQuoted initial final literal value => exact roundtrip_bindingQuoted initial final literal value
  | bindingOrdinary initial final pattern value => exact roundtrip_bindingOrdinary initial final pattern value
  | guardUnbound initial name subject instantiated => exact roundtrip_guardUnbound initial name subject instantiated
  | guardCaptured initial name resolved subject instantiated => exact roundtrip_guardCaptured initial name resolved subject instantiated

def ruleCodec : Codec Rule :=
  Evidence.Primitive.Wire.atomCodec.mapped putRule readRule readRule_putRule

end Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive.AtomWire

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source.AtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding (bindingsData readBindings index readIndex)
open Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive.AtomWire

def putRule : Rule → Atom
  | .primitive rule => .expression [.symbol "primitive", Evidence.Primitive.AtomWire.putRule rule]
  | .atHead row rest => .expression [.symbol "atHead", row, atoms rest]
  | .atTail head row rest index => .expression [.symbol "atTail", head, row, atoms rest, ConfigurationEncoding.index index]
  | .clauseEquation index left right => .expression [.symbol "clauseEquation", ConfigurationEncoding.index index, left, right]
  | .clauseGuarded index left right guards => .expression [.symbol "clauseGuarded", ConfigurationEncoding.index index, left, right, atoms guards]
  | .callableEquation index head arguments body => .expression [.symbol "callableEquation", ConfigurationEncoding.index index, text head, atoms arguments, body]
  | .callableGuarded index head arguments body guards => .expression [.symbol "callableGuarded", ConfigurationEncoding.index index, text head, atoms arguments, body, atoms guards]
  | .root index proof left right subject target guards initial final => .expression [.symbol "root", ConfigurationEncoding.index index, Conditional.Wire.evidenceData proof, left, right, subject, target, atoms guards, bindingsData initial, bindingsData final]
  | .fresh initial name subject => .expression [.symbol "fresh", bindingsData initial, text name, subject]
  | .child proof initial final source instantiated target result => .expression [.symbol "child", Conditional.Wire.evidenceData proof, bindingsData initial, bindingsData final, source, instantiated, target, result]
  | .query relation arguments initial final origin => .expression [.symbol "query", text relation, atoms arguments, bindingsData initial, bindingsData final, Conditional.Wire.originData origin]
  | .premisesNil initial => .expression [.symbol "premisesNil", bindingsData initial]
  | .premisesCons head tail guard guards initial middle final => .expression [.symbol "premisesCons", Conditional.Wire.evidenceData head, Conditional.Wire.evidenceData tail, guard, atoms guards, bindingsData initial, bindingsData middle, bindingsData final]
  | .queryRelation index relation arguments values initial final => .expression [.symbol "queryRelation", ConfigurationEncoding.index index, text relation, atoms arguments, atoms values, bindingsData initial, bindingsData final]
  | .queryBuiltin index relation arguments values initial final => .expression [.symbol "queryBuiltin", ConfigurationEncoding.index index, text relation, atoms arguments, atoms values, bindingsData initial, bindingsData final]
  | .nativeFresh initial nameSchema subjectSchema name subject => .expression [.symbol "nativeFresh", bindingsData initial, nameSchema, subjectSchema, text name, subject]
  | .nativeValue initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value => .expression [.symbol "nativeValue", bindingsData initial, bindingsData final, bindingsData innerInitial, bindingsData innerFinal, bindingsSchema, patternSchema, valueSchema, outputSchema, pattern, value]
  | .nativeBinding initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value => .expression [.symbol "nativeBinding", bindingsData initial, bindingsData final, bindingsData innerInitial, bindingsData innerFinal, bindingsSchema, patternSchema, valueSchema, outputSchema, pattern, value]
  | .call index head arguments values body guards proof initial final => .expression [.symbol "call", ConfigurationEncoding.index index, text head, atoms arguments, atoms values, body, atoms guards, Conditional.Wire.evidenceData proof, bindingsData initial, bindingsData final]

def readTag : String → Option Nat
  | "primitive" => some 0
  | "atHead" => some 1
  | "atTail" => some 2
  | "clauseEquation" => some 3
  | "clauseGuarded" => some 4
  | "callableEquation" => some 5
  | "callableGuarded" => some 6
  | "root" => some 7
  | "fresh" => some 8
  | "child" => some 9
  | "query" => some 10
  | "premisesNil" => some 11
  | "premisesCons" => some 12
  | "queryRelation" => some 13
  | "queryBuiltin" => some 14
  | "nativeFresh" => some 15
  | "nativeValue" => some 16
  | "nativeBinding" => some 17
  | "call" => some 18
  | _ => none

def readFields : Nat → List Atom → Option Rule
  | 0, [rule] => do return .primitive (← Evidence.Primitive.AtomWire.readRule rule)
  | 1, [row, rest] => do return .atHead (← some row) (← readAtoms rest)
  | 2, [head, row, rest, index] => do return .atTail (← some head) (← some row) (← readAtoms rest) (← ConfigurationEncoding.readIndex index)
  | 3, [index, left, right] => do return .clauseEquation (← ConfigurationEncoding.readIndex index) (← some left) (← some right)
  | 4, [index, left, right, guards] => do return .clauseGuarded (← ConfigurationEncoding.readIndex index) (← some left) (← some right) (← readAtoms guards)
  | 5, [index, head, arguments, body] => do return .callableEquation (← ConfigurationEncoding.readIndex index) (← readText head) (← readAtoms arguments) (← some body)
  | 6, [index, head, arguments, body, guards] => do return .callableGuarded (← ConfigurationEncoding.readIndex index) (← readText head) (← readAtoms arguments) (← some body) (← readAtoms guards)
  | 7, [index, proof, left, right, subject, target, guards, initial, final] => do return .root (← ConfigurationEncoding.readIndex index) (← Conditional.Wire.readEvidence proof) (← some left) (← some right) (← some subject) (← some target) (← readAtoms guards) (← readBindings initial) (← readBindings final)
  | 8, [initial, name, subject] => do return .fresh (← readBindings initial) (← readText name) (← some subject)
  | 9, [proof, initial, final, source, instantiated, target, result] => do return .child (← Conditional.Wire.readEvidence proof) (← readBindings initial) (← readBindings final) (← some source) (← some instantiated) (← some target) (← some result)
  | 10, [relation, arguments, initial, final, origin] => do return .query (← readText relation) (← readAtoms arguments) (← readBindings initial) (← readBindings final) (← Conditional.Wire.readOrigin origin)
  | 11, [initial] => do return .premisesNil (← readBindings initial)
  | 12, [head, tail, guard, guards, initial, middle, final] => do return .premisesCons (← Conditional.Wire.readEvidence head) (← Conditional.Wire.readEvidence tail) (← some guard) (← readAtoms guards) (← readBindings initial) (← readBindings middle) (← readBindings final)
  | 13, [index, relation, arguments, values, initial, final] => do return .queryRelation (← ConfigurationEncoding.readIndex index) (← readText relation) (← readAtoms arguments) (← readAtoms values) (← readBindings initial) (← readBindings final)
  | 14, [index, relation, arguments, values, initial, final] => do return .queryBuiltin (← ConfigurationEncoding.readIndex index) (← readText relation) (← readAtoms arguments) (← readAtoms values) (← readBindings initial) (← readBindings final)
  | 15, [initial, nameSchema, subjectSchema, name, subject] => do return .nativeFresh (← readBindings initial) (← some nameSchema) (← some subjectSchema) (← readText name) (← some subject)
  | 16, [initial, final, innerInitial, innerFinal, bindingsSchema, patternSchema, valueSchema, outputSchema, pattern, value] => do return .nativeValue (← readBindings initial) (← readBindings final) (← readBindings innerInitial) (← readBindings innerFinal) (← some bindingsSchema) (← some patternSchema) (← some valueSchema) (← some outputSchema) (← some pattern) (← some value)
  | 17, [initial, final, innerInitial, innerFinal, bindingsSchema, patternSchema, valueSchema, outputSchema, pattern, value] => do return .nativeBinding (← readBindings initial) (← readBindings final) (← readBindings innerInitial) (← readBindings innerFinal) (← some bindingsSchema) (← some patternSchema) (← some valueSchema) (← some outputSchema) (← some pattern) (← some value)
  | 18, [index, head, arguments, values, body, guards, proof, initial, final] => do return .call (← ConfigurationEncoding.readIndex index) (← readText head) (← readAtoms arguments) (← readAtoms values) (← some body) (← readAtoms guards) (← Conditional.Wire.readEvidence proof) (← readBindings initial) (← readBindings final)
  | _, _ => none

def readRule : Atom → Option Rule
  | .expression (.symbol tag :: fields) => (readTag tag).bind fun selected => readFields selected fields
  | _ => none

private theorem roundtrip_primitive (rule : Evidence.Primitive.Rule) :
    readRule (putRule (.primitive rule)) = some (.primitive rule) := by
  rw [putRule.eq_1, readRule.eq_1, readTag.eq_1]
  simp only [Bind.bind, Option.bind, readFields.eq_1]
  simp only [Evidence.Primitive.AtomWire.readRule_putRule]; rfl

private theorem roundtrip_atHead (row : Atom) (rest : List Atom) :
    readRule (putRule (.atHead row rest)) = some (.atHead row rest) := by
  rw [putRule.eq_2, readRule.eq_1, readTag.eq_2]
  simp only [Bind.bind, Option.bind, readFields.eq_2]
  simp only [atoms, readAtoms]; rfl

private theorem roundtrip_atTail (head : Atom) (row : Atom) (rest : List Atom) (index : Nat) :
    readRule (putRule (.atTail head row rest index)) = some (.atTail head row rest index) := by
  rw [putRule.eq_3, readRule.eq_1, readTag.eq_3]
  simp only [Bind.bind, Option.bind, readFields.eq_3]
  simp only [atoms, readAtoms, ConfigurationEncoding.readIndex_index]; rfl

private theorem roundtrip_clauseEquation (index : Nat) (left : Atom) (right : Atom) :
    readRule (putRule (.clauseEquation index left right)) = some (.clauseEquation index left right) := by
  rw [putRule.eq_4, readRule.eq_1, readTag.eq_4]
  simp only [Bind.bind, Option.bind, readFields.eq_4]
  simp only [ConfigurationEncoding.readIndex_index]; rfl

private theorem roundtrip_clauseGuarded (index : Nat) (left : Atom) (right : Atom) (guards : List Atom) :
    readRule (putRule (.clauseGuarded index left right guards)) = some (.clauseGuarded index left right guards) := by
  rw [putRule.eq_5, readRule.eq_1, readTag.eq_5]
  simp only [Bind.bind, Option.bind, readFields.eq_5]
  simp only [ConfigurationEncoding.readIndex_index, atoms, readAtoms]; rfl

private theorem roundtrip_callableEquation (index : Nat) (head : String) (arguments : List Atom) (body : Atom) :
    readRule (putRule (.callableEquation index head arguments body)) = some (.callableEquation index head arguments body) := by
  rw [putRule.eq_6, readRule.eq_1, readTag.eq_6]
  simp only [Bind.bind, Option.bind, readFields.eq_6]
  simp only [ConfigurationEncoding.readIndex_index, readText, text, atoms, readAtoms]; rfl

private theorem roundtrip_callableGuarded (index : Nat) (head : String) (arguments : List Atom) (body : Atom) (guards : List Atom) :
    readRule (putRule (.callableGuarded index head arguments body guards)) = some (.callableGuarded index head arguments body guards) := by
  rw [putRule.eq_7, readRule.eq_1, readTag.eq_7]
  simp only [Bind.bind, Option.bind, readFields.eq_7]
  simp only [ConfigurationEncoding.readIndex_index, readText, text, atoms, readAtoms]; rfl

private theorem roundtrip_root (index : Nat) (proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (left : Atom) (right : Atom) (subject : Atom) (target : Atom) (guards : List Atom) (initial : Subst) (final : Subst) :
    readRule (putRule (.root index proof left right subject target guards initial final)) = some (.root index proof left right subject target guards initial final) := by
  rw [putRule.eq_8, readRule.eq_1, readTag.eq_8]
  simp only [Bind.bind, Option.bind, readFields.eq_8]
  simp only [ConfigurationEncoding.readIndex_index, Conditional.Wire.readEvidence_evidenceData, atoms, readAtoms, ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_fresh (initial : Subst) (name : String) (subject : Atom) :
    readRule (putRule (.fresh initial name subject)) = some (.fresh initial name subject) := by
  rw [putRule.eq_9, readRule.eq_1, readTag.eq_9]
  simp only [Bind.bind, Option.bind, readFields.eq_9]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_child (proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (initial : Subst) (final : Subst) (source : Atom) (instantiated : Atom) (target : Atom) (result : Atom) :
    readRule (putRule (.child proof initial final source instantiated target result)) = some (.child proof initial final source instantiated target result) := by
  rw [putRule.eq_10, readRule.eq_1, readTag.eq_10]
  simp only [Bind.bind, Option.bind, readFields.eq_10]
  simp only [Conditional.Wire.readEvidence_evidenceData, ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_query (relation : String) (arguments : List Atom) (initial : Subst) (final : Subst) (origin : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Origin) :
    readRule (putRule (.query relation arguments initial final origin)) = some (.query relation arguments initial final origin) := by
  rw [putRule.eq_11, readRule.eq_1, readTag.eq_11]
  simp only [Bind.bind, Option.bind, readFields.eq_11]
  simp only [readText, text, atoms, readAtoms, ConfigurationEncoding.readBindings_bindingsData, Conditional.Wire.readOrigin_originData]; rfl

private theorem roundtrip_premisesNil (initial : Subst) :
    readRule (putRule (.premisesNil initial)) = some (.premisesNil initial) := by
  rw [putRule.eq_12, readRule.eq_1, readTag.eq_12]
  simp only [Bind.bind, Option.bind, readFields.eq_12]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_premisesCons (head : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (tail : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (guard : Atom) (guards : List Atom) (initial : Subst) (middle : Subst) (final : Subst) :
    readRule (putRule (.premisesCons head tail guard guards initial middle final)) = some (.premisesCons head tail guard guards initial middle final) := by
  rw [putRule.eq_13, readRule.eq_1, readTag.eq_13]
  simp only [Bind.bind, Option.bind, readFields.eq_13]
  simp only [Conditional.Wire.readEvidence_evidenceData, atoms, readAtoms, ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_queryRelation (index : Nat) (relation : String) (arguments : List Atom) (values : List Atom) (initial : Subst) (final : Subst) :
    readRule (putRule (.queryRelation index relation arguments values initial final)) = some (.queryRelation index relation arguments values initial final) := by
  rw [putRule.eq_14, readRule.eq_1, readTag.eq_14]
  simp only [Bind.bind, Option.bind, readFields.eq_14]
  simp only [ConfigurationEncoding.readIndex_index, readText, text, atoms, readAtoms, ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_queryBuiltin (index : Nat) (relation : String) (arguments : List Atom) (values : List Atom) (initial : Subst) (final : Subst) :
    readRule (putRule (.queryBuiltin index relation arguments values initial final)) = some (.queryBuiltin index relation arguments values initial final) := by
  rw [putRule.eq_15, readRule.eq_1, readTag.eq_15]
  simp only [Bind.bind, Option.bind, readFields.eq_15]
  simp only [ConfigurationEncoding.readIndex_index, readText, text, atoms, readAtoms, ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_nativeFresh (initial : Subst) (nameSchema : Atom) (subjectSchema : Atom) (name : String) (subject : Atom) :
    readRule (putRule (.nativeFresh initial nameSchema subjectSchema name subject)) = some (.nativeFresh initial nameSchema subjectSchema name subject) := by
  rw [putRule.eq_16, readRule.eq_1, readTag.eq_16]
  simp only [Bind.bind, Option.bind, readFields.eq_16]
  simp only [ConfigurationEncoding.readBindings_bindingsData, readText, text]; rfl

private theorem roundtrip_nativeValue (initial : Subst) (final : Subst) (innerInitial : Subst) (innerFinal : Subst) (bindingsSchema : Atom) (patternSchema : Atom) (valueSchema : Atom) (outputSchema : Atom) (pattern : Atom) (value : Atom) :
    readRule (putRule (.nativeValue initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value)) = some (.nativeValue initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value) := by
  rw [putRule.eq_17, readRule.eq_1, readTag.eq_17]
  simp only [Bind.bind, Option.bind, readFields.eq_17]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_nativeBinding (initial : Subst) (final : Subst) (innerInitial : Subst) (innerFinal : Subst) (bindingsSchema : Atom) (patternSchema : Atom) (valueSchema : Atom) (outputSchema : Atom) (pattern : Atom) (value : Atom) :
    readRule (putRule (.nativeBinding initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value)) = some (.nativeBinding initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value) := by
  rw [putRule.eq_18, readRule.eq_1, readTag.eq_18]
  simp only [Bind.bind, Option.bind, readFields.eq_18]
  simp only [ConfigurationEncoding.readBindings_bindingsData]; rfl

private theorem roundtrip_call (index : Nat) (head : String) (arguments : List Atom) (values : List Atom) (body : Atom) (guards : List Atom) (proof : MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.Conditional.Evidence) (initial : Subst) (final : Subst) :
    readRule (putRule (.call index head arguments values body guards proof initial final)) = some (.call index head arguments values body guards proof initial final) := by
  rw [putRule.eq_19, readRule.eq_1, readTag.eq_19]
  simp only [Bind.bind, Option.bind, readFields.eq_19]
  simp only [ConfigurationEncoding.readIndex_index, readText, text, atoms, readAtoms, Conditional.Wire.readEvidence_evidenceData, ConfigurationEncoding.readBindings_bindingsData]; rfl

theorem readRule_putRule (rule : Rule) : readRule (putRule rule) = some rule := by
  cases rule with
  | primitive rule => exact roundtrip_primitive rule
  | atHead row rest => exact roundtrip_atHead row rest
  | atTail head row rest index => exact roundtrip_atTail head row rest index
  | clauseEquation index left right => exact roundtrip_clauseEquation index left right
  | clauseGuarded index left right guards => exact roundtrip_clauseGuarded index left right guards
  | callableEquation index head arguments body => exact roundtrip_callableEquation index head arguments body
  | callableGuarded index head arguments body guards => exact roundtrip_callableGuarded index head arguments body guards
  | root index proof left right subject target guards initial final => exact roundtrip_root index proof left right subject target guards initial final
  | fresh initial name subject => exact roundtrip_fresh initial name subject
  | child proof initial final source instantiated target result => exact roundtrip_child proof initial final source instantiated target result
  | query relation arguments initial final origin => exact roundtrip_query relation arguments initial final origin
  | premisesNil initial => exact roundtrip_premisesNil initial
  | premisesCons head tail guard guards initial middle final => exact roundtrip_premisesCons head tail guard guards initial middle final
  | queryRelation index relation arguments values initial final => exact roundtrip_queryRelation index relation arguments values initial final
  | queryBuiltin index relation arguments values initial final => exact roundtrip_queryBuiltin index relation arguments values initial final
  | nativeFresh initial nameSchema subjectSchema name subject => exact roundtrip_nativeFresh initial nameSchema subjectSchema name subject
  | nativeValue initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value => exact roundtrip_nativeValue initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value
  | nativeBinding initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value => exact roundtrip_nativeBinding initial final innerInitial innerFinal bindingsSchema patternSchema valueSchema outputSchema pattern value
  | call index head arguments values body guards proof initial final => exact roundtrip_call index head arguments values body guards proof initial final

def ruleCodec : Codec Rule :=
  Evidence.Primitive.Wire.atomCodec.mapped putRule readRule readRule_putRule

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source.AtomWire

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source.AtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive.AtomWire

abbrev Article (rows : List Atom) := Shared.Certificate (presentation rows)

def referenceData (references : List Nat) : Atom :=
  .expression (references.map ConfigurationEncoding.index)

def readReferences : List Atom → Option (List Nat)
  | [] => some []
  | first :: rest => do return (← ConfigurationEncoding.readIndex first) :: (← readReferences rest)

@[simp] theorem readReferences_map (references : List Nat) :
    readReferences (references.map ConfigurationEncoding.index) = some references := by
  induction references with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, readReferences, ConfigurationEncoding.readIndex_index, ih]
      rfl

def rowData {rows : List Atom} (row : Shared.Row (presentation rows)) : Atom :=
  .expression [.symbol "row", putRule row.rule, referenceData (List.ofFn row.references)]

def readRow (rows : List Atom) : Atom → Option (Shared.Row (presentation rows))
  | .expression [.symbol "row", ruleData, .expression referenceData] => do
      let rule ← readRule ruleData
      let references ← readReferences referenceData
      if length : references.length = (premises rows rule).length then
        pure ⟨rule, fun position => references[position.val]'(by rw [length]; exact position.isLt)⟩
      else none
  | _ => none

@[simp] theorem readRow_rowData (rows : List Atom) (row : Shared.Row (presentation rows)) :
    readRow rows (rowData row) = some row := by
  simp only [rowData, referenceData, readRow, readRule_putRule, readReferences_map,
    List.length_ofFn, ↓reduceDIte, Bind.bind, Option.bind]
  congr 2
  funext position
  exact List.getElem_ofFn _

def readRows (rows : List Atom) : List Atom → Option (List (Shared.Row (presentation rows)))
  | [] => some []
  | first :: rest => do return (← readRow rows first) :: (← readRows rows rest)

@[simp] theorem readRows_map (rows : List Atom) (entries : List (Shared.Row (presentation rows))) :
    readRows rows (entries.map rowData) = some entries := by
  induction entries with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, readRows, readRow_rowData, ih]; rfl

/-- The references are positions in this article. Repeated references remain
separate premise occurrences, and every supplied row is checked. -/
def articleData {rows : List Atom} (article : Article rows) : Atom :=
  .expression [.symbol "article", .expression (article.rows.map rowData), ConfigurationEncoding.index article.root]

def readArticle (rows : List Atom) : Atom → Option (Article rows)
  | .expression [.symbol "article", .expression entries, root] => do
      return ⟨← readRows rows entries, ← ConfigurationEncoding.readIndex root⟩
  | _ => none

@[simp] theorem readArticle_articleData (rows : List Atom) (article : Article rows) :
    readArticle rows (articleData article) = some article := by
  simp only [articleData, readArticle, readRows_map, ConfigurationEncoding.readIndex_index]
  rfl

/-- Admission requires a literal canonical article, including every primitive
field and numeric reference. It does not establish any source judgment. -/
def read (rows : List Atom) (data : Atom) : Option (Article rows) := do
  let article ← readArticle rows data
  if articleData article = data then some article else none

@[simp] theorem read_articleData (rows : List Atom) (article : Article rows) :
    read rows (articleData article) = some article := by
  simp only [read, readArticle_articleData, Bind.bind, Option.bind, ↓reduceIte]

theorem articleData_of_read {rows : List Atom} {data : Atom} {article : Article rows}
    (admitted : read rows data = some article) : articleData article = data := by
  unfold read at admitted
  cases parsed : readArticle rows data with
  | none => simp only [parsed, Bind.bind, Option.bind] at admitted; cases admitted
  | some parsed =>
      simp only [parsed, Bind.bind, Option.bind] at admitted
      split at admitted
      · cases Option.some.inj admitted
        assumption
      · cases admitted

def check (rows : List Atom) (data : Atom) (judgment : Judgment) : Bool :=
  match read rows data with
  | none => false
  | some article => Shared.check article judgment

theorem check_exact (rows : List Atom) (data : Atom) (judgment : Judgment) :
    check rows data judgment = true ↔
      ∃ article : Article rows, articleData article = data ∧ Shared.check article judgment = true := by
  unfold check
  cases admitted : read rows data with
  | none =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨article, same, _⟩
        rw [← same, read_articleData] at admitted
        cases admitted
  | some article =>
      constructor
      · intro accepted
        exact ⟨article, articleData_of_read admitted, accepted⟩
      · rintro ⟨other, same, accepted⟩
        have reread := read_articleData rows other
        rw [same, admitted] at reread
        cases Option.some.inj reread
        exact accepted

theorem check_sound {rows : List Atom} {data : Atom} {judgment : Judgment}
    (accepted : check rows data judgment = true) : Meaning rows judgment := by
  obtain ⟨article, _, checked⟩ := (check_exact rows data judgment).mp accepted
  exact shared_sound rows article judgment checked

theorem source_coverage (rows : List Atom) (judgment : Judgment) :
    Meaning rows judgment ↔ ∃ data, check rows data judgment = true := by
  rw [shared_complete]
  constructor
  · rintro ⟨article, accepted⟩
    exact ⟨articleData article, (check_exact _ _ _).mpr ⟨article, rfl, accepted⟩⟩
  · rintro ⟨data, accepted⟩
    obtain ⟨article, _, checked⟩ := (check_exact _ _ _).mp accepted
    exact ⟨article, checked⟩

def paid (rows : List Atom) (data : Atom) (judgment : Judgment) : Option Shared.LiteralChecking.Decision :=
  (read rows data).map fun article => Shared.LiteralChecking.check (Wire.coding rows) article judgment

@[simp] theorem paid_articleData (rows : List Atom) (article : Article rows) (judgment : Judgment) :
    paid rows (articleData article) judgment =
      some (Shared.LiteralChecking.check (Wire.coding rows) article judgment) := by
  simp only [paid, read_articleData, Option.map_some]

theorem paid_acceptance (rows : List Atom) (data : Atom) (judgment : Judgment) :
    (paid rows data judgment).map (·.accepted) = some true ↔ check rows data judgment = true := by
  unfold paid check
  cases admitted : read rows data with
  | none => simp
  | some article => simp only [Option.map_some, paid_exact, Option.some.injEq]

theorem paid_work {rows : List Atom} {data : Atom} {judgment : Judgment}
    {result : Shared.LiteralChecking.Decision} (calculated : paid rows data judgment = some result) :
    ∃ article : Article rows, articleData article = data ∧
      result.accepted = Shared.check article judgment ∧
      result.work ≤ (Shared.LiteralChecking.inputVolume (Wire.coding rows) article judgment + 2) *
        (5 * Shared.LiteralChecking.inputVolume (Wire.coding rows) article judgment + 10) := by
  obtain ⟨article, admitted, same⟩ := Option.map_eq_some_iff.mp calculated
  cases same
  exact ⟨article, articleData_of_read admitted, paid_exact rows article judgment,
    paid_structural_work rows article judgment⟩

theorem root_source_coverage (rows : List Atom) (evidence : Conditional.Evidence) (subject target : Atom) :
    Conditional.RootFiring (environment rows) evidence subject target ↔
      ∃ data, check rows data (.root evidence subject target) = true :=
  source_coverage rows (.root evidence subject target)

theorem call_source_coverage (rows : List Atom) (head : String) (values : List Atom)
    (evidence : Conditional.Evidence) (index : Nat) (bindings : Subst) (body : Atom) :
    Conditional.CallReady (environment rows) head values evidence index (.evaluate bindings body) ↔
      ∃ data, check rows data (.call head values evidence index bindings body) = true :=
  source_coverage rows (.call head values evidence index bindings body)

def expandRoot (rows : List Atom) (evidence : Conditional.Evidence) (subject : Atom) : Option (Atom × Atom) :=
  (rootArticle? rows evidence subject).map fun (target, article) => (target, articleData article)

def expandCall (rows : List Atom) (evidence : Conditional.Evidence) (head : String) (values : List Atom) :
    Option ((Nat × Subst × Atom) × Atom) :=
  (callArticle? rows evidence head values).map fun (packet, article) => (packet, articleData article)

theorem expandRoot_sound {rows : List Atom} {evidence : Conditional.Evidence} {subject target data : Atom}
    (expanded : expandRoot rows evidence subject = some (target, data)) :
    check rows data (.root evidence subject target) = true ∧
      Conditional.RootFiring (environment rows) evidence subject target := by
  obtain ⟨⟨target, article⟩, compiled, same⟩ := Option.map_eq_some_iff.mp expanded
  cases same
  obtain ⟨accepted, source⟩ := rootArticle?_sound compiled
  exact ⟨(check_exact _ _ _).mpr ⟨article, rfl, accepted⟩, source⟩

theorem expandRoot_exact (rows : List Atom) (evidence : Conditional.Evidence) (subject target : Atom) :
    Conditional.RootFiring (environment rows) evidence subject target ↔
      ∃ data, expandRoot rows evidence subject = some (target, data) := by
  constructor
  · intro source
    obtain ⟨article, compiled⟩ := rootArticle?_complete source
    exact ⟨articleData article, by simp only [expandRoot, compiled, Option.map_some]⟩
  · rintro ⟨data, expanded⟩
    exact (expandRoot_sound expanded).2

theorem expandCall_sound {rows : List Atom} {evidence : Conditional.Evidence} {head : String}
    {values : List Atom} {packet : Nat × Subst × Atom} {data : Atom}
    (expanded : expandCall rows evidence head values = some (packet, data)) :
    check rows data (.call head values evidence packet.1 packet.2.1 packet.2.2) = true ∧
      Conditional.CallReady (environment rows) head values evidence packet.1 (.evaluate packet.2.1 packet.2.2) := by
  obtain ⟨⟨packet, article⟩, compiled, same⟩ := Option.map_eq_some_iff.mp expanded
  cases same
  obtain ⟨accepted, source⟩ := callArticle?_sound compiled
  exact ⟨(check_exact _ _ _).mpr ⟨article, rfl, accepted⟩, source⟩

theorem expandCall_exact (rows : List Atom) (evidence : Conditional.Evidence) (head : String) (values : List Atom)
    (index : Nat) (bindings : Subst) (body : Atom) :
    Conditional.CallReady (environment rows) head values evidence index (.evaluate bindings body) ↔
      ∃ data, expandCall rows evidence head values = some ((index, bindings, body), data) := by
  constructor
  · intro source
    obtain ⟨article, compiled⟩ := callArticle?_complete source
    exact ⟨articleData article, by simp only [expandCall, compiled, Option.map_some]⟩
  · rintro ⟨data, expanded⟩
    exact (expandCall_sound expanded).2

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source.AtomWire



namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source.Native

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands
open ConfigurationEncoding (index readIndex bindingsData readBindings)
open AtomWire

/-- Counts describe the admitted materialized-word observer, not host time.
The volume includes all conclusion and premise words and the wanted root. -/
structure Report where
  decision : Shared.LiteralChecking.Decision
  volume : Nat

def inspect (rows : List Atom) (article : Atom) (judgment : Judgment) : Option Report :=
  (AtomWire.read rows article).map fun parsed =>
    ⟨Shared.LiteralChecking.check (Wire.coding rows) parsed judgment,
      Shared.LiteralChecking.inputVolume (Wire.coding rows) parsed judgment⟩

theorem inspect_acceptance (rows : List Atom) (article : Atom) (judgment : Judgment) :
    (inspect rows article judgment).map (·.decision.accepted) = some true ↔
      AtomWire.check rows article judgment = true := by
  simpa only [inspect, AtomWire.paid, Option.map_map, Function.comp_def] using
    AtomWire.paid_acceptance rows article judgment

theorem inspect_sound {rows : List Atom} {article : Atom} {judgment : Judgment} {report : Report}
    (calculated : inspect rows article judgment = some report) (accepted : report.decision.accepted = true) :
    Meaning rows judgment := by
  apply AtomWire.check_sound
  apply (inspect_acceptance rows article judgment).mp
  rw [calculated, Option.map_some, accepted]

theorem inspect_work {rows : List Atom} {article : Atom} {judgment : Judgment} {report : Report}
    (calculated : inspect rows article judgment = some report) :
    report.decision.work ≤ (report.volume + 2) * (5 * report.volume + 10) := by
  obtain ⟨parsed, _, same⟩ := Option.map_eq_some_iff.mp calculated
  cases same
  exact paid_structural_work rows parsed judgment

def reportData (report : Report) : Atom :=
  .expression [.symbol "checked", Effects.boolean report.decision.accepted,
    index report.decision.rows, index report.decision.checks, index report.decision.work, index report.volume]

def rootRequest (rows : List Atom) (evidence : Conditional.Evidence) (subject target article : Atom) : Atom :=
  .expression [.symbol "check-root", .expression rows, Conditional.Wire.evidenceData evidence, subject, target, article]

def callRequest (rows : List Atom) (evidence : Conditional.Evidence) (head : String) (values : List Atom)
    (ordinal : Nat) (bindings : Subst) (body article : Atom) : Atom :=
  .expression [.symbol "check-call", .expression rows, Conditional.Wire.evidenceData evidence,
    .grounded (.string head), .expression values, index ordinal, bindingsData bindings, body, article]

/-- Unknown operations remain literal. Malformed evidence/article statuses
concern the supplied request; they never establish absence of other proofs. -/
def invoke (request : Atom) : Atom :=
  match request with
  | .expression [.symbol "check-root", .expression rows, evidence, subject, target, article] =>
      match Conditional.Wire.readEvidence evidence with
      | none => .expression [.symbol "malformed-request", request]
      | some evidence =>
          match inspect rows article (.root evidence subject target) with
          | none => .expression [.symbol "malformed-article", request]
          | some report => reportData report
  | .expression [.symbol "check-call", .expression rows, evidence, .grounded (.string head),
      .expression values, ordinal, bindings, body, article] =>
      match Conditional.Wire.readEvidence evidence, readIndex ordinal, readBindings bindings with
      | some evidence, some ordinal, some bindings =>
          match inspect rows article (.call head values evidence ordinal bindings body) with
          | none => .expression [.symbol "malformed-article", request]
          | some report => reportData report
      | _, _, _ => .expression [.symbol "malformed-request", request]
  | .expression [.symbol "expand-root", .expression rows, evidence, subject] =>
      match Conditional.Wire.readEvidence evidence with
      | none => .expression [.symbol "malformed-request", request]
      | some evidence =>
          match AtomWire.expandRoot rows evidence subject with
          | none => .expression [.symbol "no-expansion", request]
          | some (target, article) => .expression [.symbol "expanded-root", target, article]
  | .expression [.symbol "expand-call", .expression rows, evidence, .grounded (.string head), .expression values] =>
      match Conditional.Wire.readEvidence evidence with
      | none => .expression [.symbol "malformed-request", request]
      | some evidence =>
          match AtomWire.expandCall rows evidence head values with
          | none => .expression [.symbol "no-expansion", request]
          | some ((ordinal, bindings, body), article) =>
              .expression [.symbol "expanded-call", index ordinal, bindingsData bindings, body, article]
  | _ => request

theorem invoke_rootRequest (rows : List Atom) (evidence : Conditional.Evidence) (subject target article : Atom) :
    invoke (rootRequest rows evidence subject target article) =
      match inspect rows article (.root evidence subject target) with
      | none => .expression [.symbol "malformed-article", rootRequest rows evidence subject target article]
      | some report => reportData report := by
  simp only [rootRequest, invoke.eq_1, Conditional.Wire.readEvidence_evidenceData]

theorem invoke_callRequest (rows : List Atom) (evidence : Conditional.Evidence) (head : String)
    (values : List Atom) (ordinal : Nat) (bindings : Subst) (body article : Atom) :
    invoke (callRequest rows evidence head values ordinal bindings body article) =
      match inspect rows article (.call head values evidence ordinal bindings body) with
      | none => .expression [.symbol "malformed-article", callRequest rows evidence head values ordinal bindings body article]
      | some report => reportData report := by
  simp only [callRequest, invoke.eq_2, Conditional.Wire.readEvidence_evidenceData,
    ConfigurationEncoding.readIndex_index, ConfigurationEncoding.readBindings_bindingsData]

/-- The text seam executes the existing source reader; its accepted syntax and
ambiguity policy remain that reader's, independently of article checking. -/
def onText (text : String) : Except String (List Atom) :=
  (SpaceSemantics.readSource text).map (List.map invoke)

/-- Optional lossless transport for all original Atom fields, including
custom grounded data and names outside the source reader's printable subset.
The request and response themselves remain the same native Atom objects. -/
def encode (request : Atom) : List Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet :=
  Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith
    Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive.Wire.atomCodec request

def onWord (word : List Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet) : Option Atom :=
  (Mettapedia.OSLF.Binding.WireCodec.Binary.canonicalDecodeWith
    Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive.Wire.atomCodec word).map invoke

@[simp] theorem onWord_encode (request : Atom) : onWord (encode request) = some (invoke request) := by
  simp only [onWord, encode, Mettapedia.OSLF.Binding.WireCodec.Binary.canonicalDecodeWith_encodeWith,
    Option.map_some]

theorem onWord_exact (word : List Mettapedia.OSLF.Binding.WireCodec.Binary.Alphabet) (response : Atom) :
    onWord word = some response ↔ ∃ request, encode request = word ∧ invoke request = response := by
  constructor
  · intro processed
    obtain ⟨request, admitted, same⟩ := Option.map_eq_some_iff.mp processed
    exact ⟨request, (Mettapedia.OSLF.Binding.WireCodec.Binary.canonicalDecodeWith_exact _ _ _).mp admitted, same⟩
  · rintro ⟨request, same, response⟩
    rw [← same, onWord_encode, response]

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source.Native



namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source.AtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.NativeTypes.Certificates

/-- Validity of every submitted local inference against exactly its earlier
prefix. This judgment does not call the checker or discard unused rows. -/
inductive RowsValid (source : List Atom) : List Judgment → List (Shared.Row (presentation source)) → Prop where
  | nil (table : List Judgment) : RowsValid source table []
  | cons {table : List Judgment} {row : Shared.Row (presentation source)} {rest}
      (localInference : Shared.ValidRow table row)
      (later : RowsValid source (table ++ [conclusion row.rule]) rest) :
      RowsValid source table (row :: rest)

/-- The source article has all its local inferences justified and names its
literal conclusion by the original row ordinal. -/
structure ArticleValid {source : List Atom} (article : Article source) (wanted : Judgment) : Prop where
  rows : RowsValid source [] article.rows
  root : (article.rows.map (fun row => conclusion row.rule))[article.root]? = some wanted

theorem rowsValid_iff (source : List Atom) (table : List Judgment)
    (entries : List (Shared.Row (presentation source))) :
    RowsValid source table entries ↔ ∃ result, (Shared.inspectRows table entries).table = some result := by
  induction entries generalizing table with
  | nil =>
      constructor
      · intro _; exact ⟨table, rfl⟩
      · intro _; exact .nil table
  | cons row rest ih =>
      constructor
      · intro sourceValid
        cases sourceValid with
        | cons localInference later =>
            have checked := (Shared.inspectRow_exact table row).mpr localInference
            obtain ⟨result, processed⟩ := (ih _).mp later
            exact ⟨result, by simp only [Shared.inspectRows, checked, ↓reduceIte, processed]⟩
      · rintro ⟨result, processed⟩
        simp only [Shared.inspectRows] at processed
        split at processed
        next checked => exact .cons ((Shared.inspectRow_exact table row).mp checked) ((ih _).mpr ⟨result, processed⟩)
        next => cases processed

theorem shared_article_exact (source : List Atom) (article : Article source) (wanted : Judgment) :
    Shared.check article wanted = true ↔ ArticleValid article wanted := by
  rw [← Shared.checkJudgments_eq_check]
  simp only [Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows]
  cases processed : (Shared.inspectRows [] article.rows).table with
  | none =>
      constructor
      · intro impossible; cases impossible
      · intro sourceValid
        obtain ⟨result, present⟩ := (rowsValid_iff source [] article.rows).mp sourceValid.rows
        rw [processed] at present
        cases present
  | some result =>
      have validRows : RowsValid source [] article.rows :=
        (rowsValid_iff source [] article.rows).mpr ⟨result, processed⟩
      have same := Shared.inspectRows_table [] article.rows result processed
      simp only [List.nil_append] at same
      change decide (result[article.root]? = some wanted) = true ↔ _
      rw [decide_eq_true_eq]
      constructor
      · intro root
        exact ⟨validRows, by simpa only [same] using root⟩
      · intro sourceValid
        simpa only [same] using sourceValid.root

theorem raw_article_exact (source : List Atom) (data : Atom) (wanted : Judgment) :
    check source data wanted = true ↔
      ∃ article : Article source, articleData article = data ∧ ArticleValid article wanted := by
  simp only [check_exact, shared_article_exact]

theorem article_valid_sound {source : List Atom} {article : Article source} {wanted : Judgment}
    (valid : ArticleValid article wanted) : Meaning source wanted :=
  shared_sound source article wanted ((shared_article_exact source article wanted).mpr valid)

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source.AtomWire
namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive

/-- A local rule has at most three explicitly checked premise occurrences.
This is an arity bound, not a payload-size or execution-time bound. -/
theorem local_premise_bound (rule : Rule) : (premises rule).length ≤ 3 := by
  cases rule <;> simp [premises]

end Mettapedia.Languages.GuardedAtomRule.Evidence.Primitive

namespace Mettapedia.Languages.GuardedAtomRule.Evidence.Source

/-- Source composition adds at most five local premises; each intermediate
Atom, assignment, source occurrence and native service result remains explicit. -/
theorem local_premise_bound (rows : List OSLFCore.Atom) (rule : Rule) : (premises rows rule).length ≤ 5 := by
  cases rule <;> simp only [premises, List.length_map, List.length_cons, List.length_nil]
  case primitive rule => exact (Primitive.local_premise_bound rule).trans (by decide)
  all_goals omega

end Mettapedia.Languages.GuardedAtomRule.Evidence.Source
