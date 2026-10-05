import Mettapedia.GSLT.LanguageDef.AuthoredComputation
import Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalLookupProgram
import Mettapedia.Languages.MM0.Presentation.ProofInstantiation
import Mettapedia.Languages.MM0.Presentation.ConversionCorrespondence
import Mettapedia.Languages.MM0.Presentation.TypingTheory
import Mettapedia.Languages.MM0.Presentation.UnfoldingTheory
import Mettapedia.Languages.MM0.Presentation.AdmissionData
import Mettapedia.GSLT.LanguageDef.FirstOrderRules

/-!
# MM0 proof checking as a calculus

The calculus is fixed, and a theory enters only as data. Its judgments are
derivability of an expression from local hypotheses, derivability of a list of
expressions, a hypothesis in a list, and three operations of the kernel: the
theorem declared at an index, the instance of a declaration at arguments, and
the conversion a witness establishes.

Rules present the steps of a kernel derivation: a local hypothesis, the
application of a theorem to its derived instance hypotheses, and conversion.
The three kernel operations are authored judgments, decided by the MM0
equation programs with the theory as data. The instance judgment is decided by
the admissible-substitution program, so bound variables keep MM0's own
dependency discipline.

A derivation from these rules and the facts of a theory is exactly a kernel
derivation in that theory, and the shared checker accepts a certificate for a
derivability judgment exactly when the kernel derives it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.Calculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.Languages.MM0.Kernel
open ComputationalContext ComputationalArguments ComputationalProof ComputationalConversion
open ComputationalTyping ComputationalDefinitions

/-! ## Data and judgments -/

def contextPattern (context : Context) : Pattern := termPattern (encodeContext context)
def expressionPattern (expression : Preterm) : Pattern := termPattern (encode expression)
def expressionsPattern (expressions : List Preterm) : Pattern :=
  termPattern (encodeExpressions expressions)
def indexPattern (index : Nat) : Pattern := termPattern (natural index)
def theoremPattern (declaration : TheoremDecl) : Pattern := termPattern (encodeTheorem declaration)

def jDerives (context hypotheses expression : Pattern) : Pattern :=
  .apply "mm0:derives" [context, hypotheses, expression]
def jAll (context hypotheses expressions : Pattern) : Pattern :=
  .apply "mm0:derives-all" [context, hypotheses, expressions]
def jHypothesis (expression hypotheses : Pattern) : Pattern :=
  .apply "mm0:hypothesis" [expression, hypotheses]
def jTheorem (index declaration : Pattern) : Pattern :=
  .apply "mm0:theorem" [index, declaration]
def jInstance (context declaration arguments hypotheses conclusion : Pattern) : Pattern :=
  .apply "mm0:instance" [context, declaration, arguments, hypotheses, conclusion]
def jConverts (context left right sort : Pattern) : Pattern :=
  .apply "mm0:converts" [context, left, right, sort]

/-- `context ⊢ expression` from the local hypotheses. -/
def derivesJ (context : Context) (hypotheses : List Preterm) (expression : Preterm) : Pattern :=
  jDerives (contextPattern context) (expressionsPattern hypotheses) (expressionPattern expression)

def allJ (context : Context) (hypotheses expressions : List Preterm) : Pattern :=
  jAll (contextPattern context) (expressionsPattern hypotheses) (expressionsPattern expressions)

def hypothesisJ (expression : Preterm) (hypotheses : List Preterm) : Pattern :=
  jHypothesis (expressionPattern expression) (expressionsPattern hypotheses)

def theoremJ (index : Nat) (declaration : TheoremDecl) : Pattern :=
  jTheorem (indexPattern index) (theoremPattern declaration)

def instanceJ (context : Context) (declaration : TheoremDecl) (arguments : List Preterm)
    (result : TheoremInstance) : Pattern :=
  jInstance (contextPattern context) (theoremPattern declaration) (expressionsPattern arguments)
    (expressionsPattern result.hypotheses) (expressionPattern result.conclusion)

def convertsJ (context : Context) (result : ConversionResult) : Pattern :=
  jConverts (contextPattern context) (expressionPattern result.left)
    (expressionPattern result.right) (indexPattern result.sort)

/-! ## Rules -/

def mv (name : String) : Pattern := .fvar name
def listOf (items : Pattern) : Pattern := .apply "list" [items]
def consOf (first rest : Pattern) : Pattern := .apply "cons" [first, rest]
def nilOf : Pattern := .apply "nil" []

def rHypothesisHere : FORule :=
  ⟨"mm0-hypothesis-here", ["e", "rest"], [],
    jHypothesis (mv "e") (listOf (consOf (mv "e") (mv "rest")))⟩

def rHypothesisThere : FORule :=
  ⟨"mm0-hypothesis-there", ["e", "f", "rest"], [jHypothesis (mv "e") (listOf (mv "rest"))],
    jHypothesis (mv "e") (listOf (consOf (mv "f") (mv "rest")))⟩

def rHypothesis : FORule :=
  ⟨"mm0-hypothesis", ["c", "h", "e"], [jHypothesis (mv "e") (mv "h")],
    jDerives (mv "c") (mv "h") (mv "e")⟩

def rTheorem : FORule :=
  ⟨"mm0-theorem", ["c", "h", "i", "d", "a", "hs", "e"],
    [jTheorem (mv "i") (mv "d"), jInstance (mv "c") (mv "d") (mv "a") (mv "hs") (mv "e"),
      jAll (mv "c") (mv "h") (mv "hs")],
    jDerives (mv "c") (mv "h") (mv "e")⟩

def rConversion : FORule :=
  ⟨"mm0-conversion", ["c", "h", "l", "r", "s"],
    [jConverts (mv "c") (mv "l") (mv "r") (mv "s"), jDerives (mv "c") (mv "h") (mv "l")],
    jDerives (mv "c") (mv "h") (mv "r")⟩

def rAllNil : FORule :=
  ⟨"mm0-all-nil", ["c", "h"], [], jAll (mv "c") (mv "h") (listOf nilOf)⟩

def rAllCons : FORule :=
  ⟨"mm0-all-cons", ["c", "h", "e", "rest"],
    [jDerives (mv "c") (mv "h") (mv "e"), jAll (mv "c") (mv "h") (listOf (mv "rest"))],
    jAll (mv "c") (mv "h") (listOf (consOf (mv "e") (mv "rest")))⟩

def rules : List FORule :=
  [rHypothesisHere, rHypothesisThere, rHypothesis, rTheorem, rConversion, rAllNil, rAllCons]

def profile : CacheProfile := { dataSort := "MM0Data", cacheName := "mm0-kernel-v1" }

def constructorArities : ArityTable := [("list", 1), ("cons", 2), ("nil", 0)]

def judgments : List JudgmentDecl :=
  [⟨"mm0:derives", 3⟩, ⟨"mm0:derives-all", 3⟩, ⟨"mm0:hypothesis", 2⟩, ⟨"mm0:theorem", 2⟩,
    ⟨"mm0:instance", 5⟩, ⟨"mm0:converts", 4⟩]

def definition : CalculusLanguageDef :=
  cacheDefinition profile constructorArities judgments (rules.map FORule.toSchema)

theorem definition_valid : definition.isValid = true := by
  decide +kernel

/-- **The MM0 calculus.** -/
def formMM0 : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

theorem rules_foPackage : FOPackage rules := by
  have hn : rules.all (fun r => decide r.vars.Nodup) = true := by decide +kernel
  have hp : rules.all
      (fun r => checkBindingSchemasFragment r.formals r.premises) = true := by decide +kernel
  have hc : rules.all
      (fun r => checkBindingSchemaFragment r.formals r.conclusion) = true := by decide +kernel
  exact ⟨fun r hr => of_decide_eq_true ((List.all_eq_true.mp hn) r hr),
    fun r hr => bindingSchemasFragment_of_check ((List.all_eq_true.mp hp) r hr),
    fun r hr => bindingSchemaFragment_of_check ((List.all_eq_true.mp hc) r hr)⟩

theorem presents : Presents formMM0 rules := ⟨rules_foPackage, rfl⟩

/-! ## The kernel operations of a theory -/

section Operations

variable (T : Theory)

/-- The theorem declared at an index, by the table-lookup program. -/
def lookupComputation : AuthoredComputation Nat TheoremDecl where
  relation index declaration := T.theoremSignature index = some declaration
  program := naturalLookupProgram
  host := computationalHost
  head := "nik:nat-table-get"
  encodeQuery index := [encodeNaturalTable encodeTheorem T.theorems, natural index]
  encodeAnswer result := encodeLookupResult (result.map encodeTheorem)
  accepts index declaration := by
    rw [natural_lookup_result_exact]
    constructor
    · intro same
      have mapped := encodeLookupResult_injective same
      cases found : T.theorems.lookup index with
      | none => rw [found] at mapped; cases mapped
      | some stored =>
          rw [found] at mapped
          simp only [Option.map_some, Option.some.injEq] at mapped
          simp [Theory.theoremSignature, found, ComputationalAdmission.encodeTheorem_injective mapped]
    · intro found
      simp only [Theory.theoremSignature] at found
      simp [found]
  refuses index := by
    rw [natural_lookup_result_exact]
    constructor
    · intro same ⟨declaration, found⟩
      simp only [Theory.theoremSignature] at found
      rw [found] at same
      cases encodeLookupResult_injective same
    · intro absent
      cases found : T.theorems.lookup index with
      | none => simp
      | some stored => exact absurd ⟨stored, found⟩ absent

/-- The instance of a declaration at arguments, by the admissible
instantiation program. -/
def instanceComputation :
    AuthoredComputation (Context × TheoremDecl × List Preterm) TheoremInstance where
  relation query result :=
    TheoremDecl.Instantiates T.termSignature query.1 query.2.1 query.2.2 result
  program := proofProgram
  host := dataEqualityHost
  head := "mm0:instantiate-theorem"
  encodeQuery query :=
    [encodeTable T.terms, encodeContext query.1, encodeTheorem query.2.1, encodeExpressions query.2.2]
  encodeAnswer := encodeInstance
  accepts query result := by
    rw [theorem_instantiation_accepts_iff, theory_signature]
  refuses query := by
    rw [theorem_instantiation_result_exact, theory_signature]
    constructor
    · intro same
      exact (TheoremDecl.instantiate_none_iff _ _ _ _).mp (encodeInstance_injective same).symm
    · intro refused
      rw [(TheoremDecl.instantiate_none_iff _ _ _ _).mpr refused]

/-- The conversion a witness establishes, by the conversion program. -/
def conversionComputation : AuthoredComputation (Context × ConvWitness) ConversionResult where
  relation query result :=
    ConvWitness.Checks T.termSignature T.definitionSignature query.1 query.2
      result.left result.right result.sort
  program := conversionProgram
  host := dataEqualityHost
  head := "mm0:conversion"
  encodeQuery query :=
    [encodeTable T.terms, encodeDefinitions T.definitions, encodeContext query.1, encodeWitness query.2]
  encodeAnswer := encodeConversion
  accepts query result := theory_conversion_accepts_iff T query.1 query.2 result.left result.right result.sort
  refuses query := by
    have computed := theory_conversion_computes T query.1 query.2
    constructor
    · intro returned ⟨result, checks⟩
      have same := encodeConversion_injective (returned.deterministic computed)
      rw [(ConvWitness.conversion_eq_some_iff _ _ _ _ _ _ _).mpr checks] at same
      cases same
    · intro refused
      have absent : ConvWitness.conversion? T.termSignature T.definitionSignature query.1 query.2 = none := by
        cases result : ConvWitness.conversion? T.termSignature T.definitionSignature query.1 query.2 with
        | none => rfl
        | some found =>
            exact absurd ⟨found, (ConvWitness.conversion_eq_some_iff _ _ _ _ _ _ _).mp result⟩ refused
      rwa [absent] at computed

/-- The kernel operations. -/
inductive Operation where
  | lookup
  | instantiate
  | convert

def Operation.Query : Operation → Type
  | .lookup => Nat
  | .instantiate => Context × TheoremDecl × List Preterm
  | .convert => Context × ConvWitness

def Operation.Answer : Operation → Type
  | .lookup => TheoremDecl
  | .instantiate => TheoremInstance
  | .convert => ConversionResult

/-- **The authored judgments of a theory.** -/
def family : AuthoredFamily where
  Index := Operation
  Query := Operation.Query
  Answer := Operation.Answer
  computation
    | .lookup => lookupComputation T
    | .instantiate => instanceComputation T
    | .convert => conversionComputation T
  judgment
    | .lookup => fun index declaration => theoremJ index declaration
    | .instantiate => fun query result => instanceJ query.1 query.2.1 query.2.2 result
    | .convert => fun query result => convertsJ query.1 result

theorem family_fact_iff (goal : Pattern) :
    (family T).Fact goal ↔
      (∃ index declaration, T.theoremSignature index = some declaration ∧
        goal = theoremJ index declaration) ∨
      (∃ context declaration arguments result,
        TheoremDecl.Instantiates T.termSignature context declaration arguments result ∧
          goal = instanceJ context declaration arguments result) ∨
      (∃ context witness result,
        ConvWitness.Checks T.termSignature T.definitionSignature context witness
          result.left result.right result.sort ∧ goal = convertsJ context result) := by
  constructor
  · rintro ⟨index, query, answer, related, rfl⟩
    cases index with
    | lookup => exact .inl ⟨query, answer, related, rfl⟩
    | instantiate =>
        obtain ⟨context, declaration, arguments⟩ := query
        exact .inr (.inl ⟨context, declaration, arguments, answer, related, rfl⟩)
    | convert =>
        obtain ⟨context, witness⟩ := query
        exact .inr (.inr ⟨context, witness, answer, related, rfl⟩)
  · rintro (⟨index, declaration, found, rfl⟩ |
      ⟨context, declaration, arguments, result, instantiated, rfl⟩ |
      ⟨context, witness, result, checks, rfl⟩)
    · exact ⟨.lookup, index, declaration, found, rfl⟩
    · exact ⟨.instantiate, (context, declaration, arguments), result, instantiated, rfl⟩
    · exact ⟨.convert, (context, witness), result, checks, rfl⟩

end Operations

/-! ## Decoding judgment patterns -/

theorem contextPattern_injective : Function.Injective contextPattern :=
  fun _ _ same => encodeContext_injective (termPattern_injective same)

theorem expressionPattern_injective : Function.Injective expressionPattern :=
  fun _ _ same => encode_injective (termPattern_injective same)

theorem expressionsPattern_injective : Function.Injective expressionsPattern :=
  fun _ _ same => encodeExpressions_injective (termPattern_injective same)

theorem indexPattern_injective : Function.Injective indexPattern :=
  fun _ _ same => natural_injective (termPattern_injective same)

theorem theoremPattern_injective : Function.Injective theoremPattern :=
  fun _ _ same => ComputationalAdmission.encodeTheorem_injective (termPattern_injective same)

theorem expressionsPattern_eq (expressions : List Preterm) :
    expressionsPattern expressions = listOf (itemsPattern (expressions.map encode)) := rfl

theorem expressionsPattern_cons (first : Preterm) (rest : List Preterm) :
    expressionsPattern (first :: rest) =
      listOf (consOf (expressionPattern first) (itemsPattern (rest.map encode))) := rfl

theorem expressionsPattern_nil : expressionsPattern [] = listOf nilOf := rfl

/-- A nonempty list pattern decodes to a nonempty list. -/
theorem expressionsPattern_eq_cons {first rest : Pattern} {expressions : List Preterm}
    (same : listOf (consOf first rest) = expressionsPattern expressions) :
    ∃ head tail, expressions = head :: tail ∧ first = expressionPattern head ∧
      rest = itemsPattern (tail.map encode) := by
  cases expressions with
  | nil => simp [expressionsPattern_eq, listOf, consOf, itemsPattern] at same
  | cons head tail =>
      rw [expressionsPattern_cons] at same
      simp only [listOf, consOf, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      exact ⟨head, tail, rfl, same.1, same.2⟩

theorem expressionsPattern_eq_nil {expressions : List Preterm}
    (same : listOf nilOf = expressionsPattern expressions) : expressions = [] :=
  expressionsPattern_injective (same.symm.trans expressionsPattern_nil)

theorem itemsPattern_argumentValid (items : List DeterministicEquations.Term) :
    argumentValidAt 0 (itemsPattern items) = true := by
  obtain ⟨ground, canonical⟩ := itemsPattern_valid 0 items
  simp [argumentValidAt, ground, canonical]

/-! ## Rule instances -/

section Instances

variable (a b c d e f g : Pattern)

theorem inst_rHypothesisHere :
    rHypothesisHere.instPremises [a, b] = [] ∧
      rHypothesisHere.instConclusion [a, b] = jHypothesis a (listOf (consOf a b)) := by
  constructor <;> simp [rHypothesisHere, FORule.instPremises, FORule.instConclusion,
    FORule.bindings, applyBindings, jHypothesis, listOf, consOf, mv]

theorem inst_rHypothesisThere :
    rHypothesisThere.instPremises [a, b, c] = [jHypothesis a (listOf c)] ∧
      rHypothesisThere.instConclusion [a, b, c] = jHypothesis a (listOf (consOf b c)) := by
  constructor <;> simp [rHypothesisThere, FORule.instPremises, FORule.instConclusion,
    FORule.bindings, applyBindings, jHypothesis, listOf, consOf, mv]

theorem inst_rHypothesis :
    rHypothesis.instPremises [a, b, c] = [jHypothesis c b] ∧
      rHypothesis.instConclusion [a, b, c] = jDerives a b c := by
  constructor <;> simp [rHypothesis, FORule.instPremises, FORule.instConclusion,
    FORule.bindings, applyBindings, jHypothesis, jDerives, mv]

theorem inst_rTheorem :
    rTheorem.instPremises [a, b, c, d, e, f, g] =
        [jTheorem c d, jInstance a d e f g, jAll a b f] ∧
      rTheorem.instConclusion [a, b, c, d, e, f, g] = jDerives a b g := by
  constructor <;> simp [rTheorem, FORule.instPremises, FORule.instConclusion,
    FORule.bindings, applyBindings, jTheorem, jInstance, jAll, jDerives, mv]

theorem inst_rConversion :
    rConversion.instPremises [a, b, c, d, e] = [jConverts a c d e, jDerives a b c] ∧
      rConversion.instConclusion [a, b, c, d, e] = jDerives a b d := by
  constructor <;> simp [rConversion, FORule.instPremises, FORule.instConclusion,
    FORule.bindings, applyBindings, jConverts, jDerives, mv]

theorem inst_rAllNil :
    rAllNil.instPremises [a, b] = [] ∧ rAllNil.instConclusion [a, b] = jAll a b (listOf nilOf) := by
  constructor <;> simp [rAllNil, FORule.instPremises, FORule.instConclusion,
    FORule.bindings, applyBindings, jAll, listOf, nilOf, mv]

theorem inst_rAllCons :
    rAllCons.instPremises [a, b, c, d] = [jDerives a b c, jAll a b (listOf d)] ∧
      rAllCons.instConclusion [a, b, c, d] = jAll a b (listOf (consOf c d)) := by
  constructor <;> simp [rAllCons, FORule.instPremises, FORule.instConclusion,
    FORule.bindings, applyBindings, jDerives, jAll, listOf, consOf, mv]

end Instances

/-! ## Soundness -/

section Adequacy

variable {T : Theory}

/-- What a judgment pattern says about the kernel, for every encoding it
decodes to. The kernel operations are facts, so their patterns always decode. -/
def Meaning (T : Theory) (p : Pattern) : Prop :=
  (∀ context hypotheses expression, p = derivesJ context hypotheses expression →
    Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
      expression) ∧
  (∀ context hypotheses expressions, p = allJ context hypotheses expressions →
    DerivesList T.termSignature T.definitionSignature T.theoremSignature context hypotheses
      expressions) ∧
  (∀ expression hypotheses, p = hypothesisJ expression hypotheses → expression ∈ hypotheses) ∧
  (∀ first second, p = jTheorem first second →
    ∃ (index : Nat) (declaration : TheoremDecl), first = indexPattern index ∧
      second = theoremPattern declaration ∧ T.theoremSignature index = some declaration) ∧
  (∀ c d a hs e, p = jInstance c d a hs e →
    ∃ (context : Context) (declaration : TheoremDecl) (arguments : List Preterm)
      (result : TheoremInstance), c = contextPattern context ∧
      d = theoremPattern declaration ∧ a = expressionsPattern arguments ∧
      hs = expressionsPattern result.hypotheses ∧ e = expressionPattern result.conclusion ∧
      TheoremDecl.Instantiates T.termSignature context declaration arguments result) ∧
  (∀ c l r s, p = jConverts c l r s →
    ∃ (context : Context) (result : ConversionResult), c = contextPattern context ∧
      l = expressionPattern result.left ∧
      r = expressionPattern result.right ∧ s = indexPattern result.sort ∧
      Converts T.termSignature T.definitionSignature context result.left result.right result.sort)

theorem fact_meaning {p : Pattern} (holds : (family T).Fact p) : Meaning T p := by
  rcases (family_fact_iff T p).mp holds with
    ⟨index, declaration, found, rfl⟩ |
    ⟨context, declaration, arguments, result, instantiated, rfl⟩ |
    ⟨context, witness, result, checks, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ same; simp [theoremJ, jTheorem, derivesJ, jDerives] at same
    · intro _ _ _ same; simp [theoremJ, jTheorem, allJ, jAll] at same
    · intro _ _ same; simp [theoremJ, jTheorem, hypothesisJ, jHypothesis] at same
    · intro first second same
      simp only [theoremJ, jTheorem, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      exact ⟨index, declaration, same.1.symm, same.2.symm, found⟩
    · intro _ _ _ _ _ same; simp [theoremJ, jTheorem, jInstance] at same
    · intro _ _ _ _ same; simp [theoremJ, jTheorem, jConverts] at same
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ same; simp [instanceJ, jInstance, derivesJ, jDerives] at same
    · intro _ _ _ same; simp [instanceJ, jInstance, allJ, jAll] at same
    · intro _ _ same; simp [instanceJ, jInstance, hypothesisJ, jHypothesis] at same
    · intro _ _ same; simp [instanceJ, jInstance, jTheorem] at same
    · intro c d a hs e same
      simp only [instanceJ, jInstance, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨hc, hd, ha, hhs, he⟩ := same
      exact ⟨context, declaration, arguments, result, hc.symm, hd.symm, ha.symm, hhs.symm,
        he.symm, instantiated⟩
    · intro _ _ _ _ same; simp [instanceJ, jInstance, jConverts] at same
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ same; simp [convertsJ, jConverts, derivesJ, jDerives] at same
    · intro _ _ _ same; simp [convertsJ, jConverts, allJ, jAll] at same
    · intro _ _ same; simp [convertsJ, jConverts, hypothesisJ, jHypothesis] at same
    · intro _ _ same; simp [convertsJ, jConverts, jTheorem] at same
    · intro _ _ _ _ _ same; simp [convertsJ, jConverts, jInstance] at same
    · intro c l r s same
      simp only [convertsJ, jConverts, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨hc, hl, hr, hs⟩ := same
      exact ⟨context, result, hc.symm, hl.symm, hr.symm, hs.symm,
        ConvWitness.Checks.derives checks⟩

/-- A derivability pattern means only its first clause. -/
theorem meaning_jDerives {c h e : Pattern}
    (derives : ∀ context hypotheses expression, jDerives c h e = derivesJ context hypotheses expression →
      Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses expression) :
    Meaning T (jDerives c h e) := by
  refine ⟨derives, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ same; simp [jDerives, allJ, jAll] at same
  · intro _ _ same; simp [jDerives, hypothesisJ, jHypothesis] at same
  · intro _ _ same; simp [jDerives, jTheorem] at same
  · intro _ _ _ _ _ same; simp [jDerives, jInstance] at same
  · intro _ _ _ _ same; simp [jDerives, jConverts] at same

theorem meaning_jAll {c h es : Pattern}
    (all : ∀ context hypotheses expressions, jAll c h es = allJ context hypotheses expressions →
      DerivesList T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expressions) :
    Meaning T (jAll c h es) := by
  refine ⟨?_, all, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ same; simp [jAll, derivesJ, jDerives] at same
  · intro _ _ same; simp [jAll, hypothesisJ, jHypothesis] at same
  · intro _ _ same; simp [jAll, jTheorem] at same
  · intro _ _ _ _ _ same; simp [jAll, jInstance] at same
  · intro _ _ _ _ same; simp [jAll, jConverts] at same

theorem meaning_jHypothesis {e hs : Pattern}
    (member : ∀ expression hypotheses, jHypothesis e hs = hypothesisJ expression hypotheses →
      expression ∈ hypotheses) :
    Meaning T (jHypothesis e hs) := by
  refine ⟨?_, ?_, member, ?_, ?_, ?_⟩
  · intro _ _ _ same; simp [jHypothesis, derivesJ, jDerives] at same
  · intro _ _ _ same; simp [jHypothesis, allJ, jAll] at same
  · intro _ _ same; simp [jHypothesis, jTheorem] at same
  · intro _ _ _ _ _ same; simp [jHypothesis, jInstance] at same
  · intro _ _ _ _ same; simp [jHypothesis, jConverts] at same

/-- **Every rule preserves the meaning.** -/
theorem rules_meaningSound {r : FORule} (member : r ∈ rules) (args : List Pattern)
    (length : args.length = r.vars.length) (premises : ∀ p ∈ r.instPremises args, Meaning T p) :
    Meaning T (r.instConclusion args) := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · match args, length with
    | [e, rest], _ =>
      rw [(inst_rHypothesisHere e rest).2]
      refine meaning_jHypothesis fun expression hypotheses same => ?_
      simp only [hypothesisJ, jHypothesis, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨he, hlist⟩ := same
      obtain ⟨head, tail, rfl, hhead, -⟩ := expressionsPattern_eq_cons hlist
      rw [expressionPattern_injective (he.symm.trans hhead)]
      exact List.mem_cons_self
  · match args, length with
    | [e, f, rest], _ =>
      have premise := premises (jHypothesis e (listOf rest))
        (by rw [(inst_rHypothesisThere e f rest).1]; exact List.mem_singleton_self _)
      rw [(inst_rHypothesisThere e f rest).2]
      refine meaning_jHypothesis fun expression hypotheses same => ?_
      simp only [hypothesisJ, jHypothesis, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨he, hlist⟩ := same
      obtain ⟨head, tail, rfl, -, hrest⟩ := expressionsPattern_eq_cons hlist
      exact List.mem_cons_of_mem _ (premise.2.2.1 expression tail (by rw [he, hrest]; rfl))
  · match args, length with
    | [c, h, e], _ =>
      have premise := premises (jHypothesis e h)
        (by rw [(inst_rHypothesis c h e).1]; exact List.mem_singleton_self _)
      rw [(inst_rHypothesis c h e).2]
      refine meaning_jDerives fun context hypotheses expression same => ?_
      simp only [derivesJ, jDerives, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨-, hh, he⟩ := same
      exact .hypothesis (premise.2.2.1 expression hypotheses (by rw [he, hh]; rfl))
  · match args, length with
    | [c, h, i, d, a, hs, e], _ =>
      have premiseOf := fun p (inPremises : p ∈ [jTheorem i d, jInstance c d a hs e, jAll c h hs]) =>
        premises p (by rw [(inst_rTheorem c h i d a hs e).1]; exact inPremises)
      rw [(inst_rTheorem c h i d a hs e).2]
      refine meaning_jDerives fun context hypotheses expression same => ?_
      simp only [derivesJ, jDerives, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨hc, hh, he⟩ := same
      obtain ⟨index, declaration, -, hd, found⟩ :=
        (premiseOf (jTheorem i d) (by simp)).2.2.2.1 i d rfl
      obtain ⟨context', declaration', arguments, result, hc', hd', -, hhs, he', instantiated⟩ :=
        (premiseOf (jInstance c d a hs e) (by simp)).2.2.2.2.1 c d a hs e rfl
      cases contextPattern_injective (hc'.symm.trans hc)
      cases theoremPattern_injective (hd'.symm.trans hd)
      cases expressionPattern_injective (he.symm.trans he')
      have list := (premiseOf (jAll c h hs) (by simp)).2.1 context hypotheses result.hypotheses
        (by rw [hc, hh, hhs]; rfl)
      exact .theoremApp found instantiated list
  · match args, length with
    | [c, h, l, r, s], _ =>
      have premiseOf := fun p (inPremises : p ∈ [jConverts c l r s, jDerives c h l]) =>
        premises p (by rw [(inst_rConversion c h l r s).1]; exact inPremises)
      rw [(inst_rConversion c h l r s).2]
      refine meaning_jDerives fun context hypotheses expression same => ?_
      simp only [derivesJ, jDerives, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at same
      obtain ⟨hc, hh, hr⟩ := same
      obtain ⟨context', result, hc', hl, hr', -, converted⟩ :=
        (premiseOf (jConverts c l r s) (by simp)).2.2.2.2.2 c l r s rfl
      cases contextPattern_injective (hc'.symm.trans hc)
      cases expressionPattern_injective (hr.symm.trans hr')
      have derived := (premiseOf (jDerives c h l) (by simp)).1 context hypotheses result.left
        (by rw [hc, hh, hl]; rfl)
      exact .conversion converted derived
  · match args, length with
    | [c, h], _ =>
      rw [(inst_rAllNil c h).2]
      refine meaning_jAll fun context hypotheses expressions same => ?_
      simp only [allJ, jAll, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      rw [expressionsPattern_eq_nil same.2.2]
      exact .nil
  · match args, length with
    | [c, h, e, rest], _ =>
      have premiseOf := fun p (inPremises : p ∈ [jDerives c h e, jAll c h (listOf rest)]) =>
        premises p (by rw [(inst_rAllCons c h e rest).1]; exact inPremises)
      rw [(inst_rAllCons c h e rest).2]
      refine meaning_jAll fun context hypotheses expressions same => ?_
      simp only [allJ, jAll, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      obtain ⟨hc, hh, hlist⟩ := same
      obtain ⟨head, tail, rfl, he, hrest⟩ := expressionsPattern_eq_cons hlist
      exact .cons ((premiseOf (jDerives c h e) (by simp)).1 context hypotheses head
          (by rw [hc, hh, he]; rfl))
        ((premiseOf (jAll c h (listOf rest)) (by simp)).2.1 context hypotheses tail
          (by rw [hc, hh, hrest]; rfl))

/-- **Soundness**: everything derivable from the rules and the facts of a
theory has its kernel meaning. -/
theorem meaning_of_factDerivation {p : Pattern}
    (derived : FactDerivation formMM0 (family T).Fact p) : Meaning T p := by
  induction derived with
  | fact holds => exact fact_meaning holds
  | byRule ruleInstance application _ ih =>
      have application' := application
      obtain ⟨rule, lookup, _, _, _, _⟩ := application'
      obtain ⟨r, member, rfl, sameId⟩ := presents.rule_of_lookup lookup
      rcases ruleInstance with ⟨id, args⟩
      simp only at sameId
      subst sameId
      obtain ⟨length, -, hpremises, hconclusion⟩ :=
        (ruleApplication_iff formMM0 rules presents.package r member (presents.lookup member)
          args _ _).mp application
      subst hpremises hconclusion
      exact rules_meaningSound member args length ih

/-! ## Completeness -/

theorem applyRule {Fact : Pattern → Prop} {r : FORule} (member : r ∈ rules) (args : List Pattern)
    (length : args.length = r.vars.length) (valid : ∀ a ∈ args, argumentValidAt 0 a = true)
    (children : ∀ p ∈ r.instPremises args, FactDerivation formMM0 Fact p) :
    FactDerivation formMM0 Fact (r.instConclusion args) :=
  .byRule ⟨⟨r.id⟩, args⟩
    ((ruleApplication_iff formMM0 rules presents.package r member (presents.lookup member) args _ _).mpr
      ⟨length, valid, rfl, rfl⟩)
    children

theorem hypothesis_derived {expression : Preterm} : ∀ {hypotheses : List Preterm},
    expression ∈ hypotheses → FactDerivation formMM0 (family T).Fact (hypothesisJ expression hypotheses)
  | _ :: rest, .head _ => by
      have derived := applyRule (Fact := (family T).Fact) (r := rHypothesisHere) (by simp [rules])
        [expressionPattern expression, itemsPattern (rest.map encode)] rfl
        (by simp [expressionPattern, termPattern_argumentValid, itemsPattern_argumentValid])
        (by rw [(inst_rHypothesisHere _ _).1]; simp)
      rw [(inst_rHypothesisHere _ _).2] at derived
      exact derived
  | first :: rest, .tail _ member => by
      have child := hypothesis_derived member
      have derived := applyRule (Fact := (family T).Fact) (r := rHypothesisThere) (by simp [rules])
        [expressionPattern expression, expressionPattern first, itemsPattern (rest.map encode)] rfl
        (by simp [expressionPattern, termPattern_argumentValid, itemsPattern_argumentValid])
        (by
          rw [(inst_rHypothesisThere _ _ _).1]
          intro p inPremises
          rw [List.mem_singleton] at inPremises
          subst inPremises
          exact child)
      rw [(inst_rHypothesisThere _ _ _).2] at derived
      exact derived

mutual

/-- **Completeness**: every kernel derivation is a derivation from the rules
and the facts of the theory. -/
theorem derived_of_derives {context : Context} {hypotheses : List Preterm} : ∀ {expression : Preterm},
    Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses expression →
      FactDerivation formMM0 (family T).Fact (derivesJ context hypotheses expression)
  | expression, .hypothesis member => by
      have child := hypothesis_derived (T := T) member
      have derived := applyRule (Fact := (family T).Fact) (r := rHypothesis) (by simp [rules])
        [contextPattern context, expressionsPattern hypotheses, expressionPattern expression] rfl
        (by simp [contextPattern, expressionsPattern, expressionPattern, termPattern_argumentValid])
        (by
          rw [(inst_rHypothesis _ _ _).1]
          intro p inPremises
          rw [List.mem_singleton] at inPremises
          subst inPremises
          exact child)
      rw [(inst_rHypothesis _ _ _).2] at derived
      exact derived
  | _,
      .theoremApp (index := index) (declaration := declaration) (arguments := arguments)
        (instantiation := result) found instantiated premises => by
      have lookupFact : FactDerivation formMM0 (family T).Fact (theoremJ index declaration) :=
        .fact ((family_fact_iff T _).mpr (.inl ⟨index, declaration, found, rfl⟩))
      have instanceFact :
          FactDerivation formMM0 (family T).Fact (instanceJ context declaration arguments result) :=
        .fact ((family_fact_iff T _).mpr
          (.inr (.inl ⟨context, declaration, arguments, result, instantiated, rfl⟩)))
      have children := derived_of_derivesList premises
      have derived := applyRule (Fact := (family T).Fact) (r := rTheorem) (by simp [rules])
        [contextPattern context, expressionsPattern hypotheses, indexPattern index,
          theoremPattern declaration, expressionsPattern arguments,
          expressionsPattern result.hypotheses, expressionPattern result.conclusion] rfl
        (by simp [contextPattern, expressionsPattern, expressionPattern, indexPattern,
          theoremPattern, termPattern_argumentValid])
        (by
          rw [(inst_rTheorem _ _ _ _ _ _ _).1]
          intro p inPremises
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inPremises
          rcases inPremises with rfl | rfl | rfl
          · exact lookupFact
          · exact instanceFact
          · exact children)
      rw [(inst_rTheorem _ _ _ _ _ _ _).2] at derived
      exact derived
  | _, .conversion (left := left) (right := right) (sort := sort)
      converted derivedLeft => by
      obtain ⟨witness, checks⟩ := converted.certificate_exists
      have conversionFact :
          FactDerivation formMM0 (family T).Fact (convertsJ context ⟨left, right, sort⟩) :=
        .fact ((family_fact_iff T _).mpr (.inr (.inr ⟨context, witness, ⟨left, right, sort⟩, checks, rfl⟩)))
      have child := derived_of_derives derivedLeft
      have derived := applyRule (Fact := (family T).Fact) (r := rConversion) (by simp [rules])
        [contextPattern context, expressionsPattern hypotheses, expressionPattern left,
          expressionPattern right, indexPattern sort] rfl
        (by simp [contextPattern, expressionsPattern, expressionPattern, indexPattern,
          termPattern_argumentValid])
        (by
          rw [(inst_rConversion _ _ _ _ _).1]
          intro p inPremises
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inPremises
          rcases inPremises with rfl | rfl
          · exact conversionFact
          · exact child)
      rw [(inst_rConversion _ _ _ _ _).2] at derived
      exact derived

theorem derived_of_derivesList {context : Context} {hypotheses : List Preterm} :
    ∀ {expressions : List Preterm},
    DerivesList T.termSignature T.definitionSignature T.theoremSignature context hypotheses expressions →
      FactDerivation formMM0 (family T).Fact (allJ context hypotheses expressions)
  | _, .nil => by
      have derived := applyRule (Fact := (family T).Fact) (r := rAllNil) (by simp [rules])
        [contextPattern context, expressionsPattern hypotheses] rfl
        (by simp [contextPattern, expressionsPattern, termPattern_argumentValid])
        (by rw [(inst_rAllNil _ _).1]; simp)
      rw [(inst_rAllNil _ _).2] at derived
      exact derived
  | _, .cons (expression := expression) (expressions := rest) head tail => by
      have headDerived := derived_of_derives head
      have tailDerived := derived_of_derivesList tail
      have derived := applyRule (Fact := (family T).Fact) (r := rAllCons) (by simp [rules])
        [contextPattern context, expressionsPattern hypotheses, expressionPattern expression,
          itemsPattern (rest.map encode)] rfl
        (by simp [contextPattern, expressionsPattern, expressionPattern, termPattern_argumentValid,
          itemsPattern_argumentValid])
        (by
          rw [(inst_rAllCons _ _ _ _).1]
          intro p inPremises
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inPremises
          rcases inPremises with rfl | rfl
          · exact headDerived
          · exact tailDerived)
      rw [(inst_rAllCons _ _ _ _).2] at derived
      exact derived

end

/-- **Adequacy**: a derivability judgment follows from the rules and the facts
of a theory exactly when the MM0 kernel derives it in that theory. -/
theorem factDerivation_iff (context : Context) (hypotheses : List Preterm) (expression : Preterm) :
    FactDerivation formMM0 (family T).Fact (derivesJ context hypotheses expression) ↔
      Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses expression :=
  ⟨fun derived => (meaning_of_factDerivation derived).1 _ _ _ rfl, derived_of_derives⟩

variable (T) in
/-- **The MM0 tier of a theory**: the fixed calculus with the theory's kernel
operations. -/
def mm0 : AuthoredCalculus := ⟨formMM0, family T⟩

/-- **The shared checker accepts a certificate for `context ⊢ expression`
exactly when the MM0 kernel derives it.** Computed leaves run the MM0 lookup,
instantiation and conversion programs on the theory. -/
theorem accepts_iff_derives (context : Context) (hypotheses : List Preterm) (expression : Preterm) :
    (mm0 T).Accepts (derivesJ context hypotheses expression) ↔
      Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses expression :=
  ((mm0 T).accepts_iff _).trans (factDerivation_iff context hypotheses expression)

/-- **Soundness of an implementation, with its trust explicit**: if every
judgment an implementation of the kernel operations returns is a fact of the
theory, every certificate it accepts is a kernel derivation. Nothing else
about the implementation is assumed. -/
theorem implementation_derives {Query : Type} {implementation : Query → Option Pattern}
    (trusted : (mm0 T).ReturnsFacts implementation) {context : Context}
    {hypotheses : List Preterm} {expression : Preterm} {proof : CompactProof Query}
    (accepted : check formMM0 implementation (derivesJ context hypotheses expression) proof = true) :
    Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses expression :=
  (factDerivation_iff context hypotheses expression).mp
    (AuthoredCalculus.implementation_sound trusted accepted)

end Adequacy

end Mettapedia.Languages.MM0.Presentation.Calculus
