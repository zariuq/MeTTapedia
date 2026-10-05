import Mettapedia.Languages.MM0.Presentation.Calculus
import Mettapedia.Languages.MM0.Presentation.ProofExecution
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ComputationLists

/-!
# The checker of the MM0 calculus as an equation program

The shared checker of the MM0 calculus is authored as one equation program with
the theory as data. It reads a goal and a certificate as data:

* A pattern becomes data constructor by constructor, except that the pattern of
  an engine datum is that datum and the pattern of a list of data is that list.
  The encoding is injective (`code_injective`), and the encoded application of
  a constructor depends only on the encoded arguments (`applyCode`).
* A certificate becomes data node by node. A computed leaf keeps its query and
  its claimed answer; the fuel it names is not part of the data.

The program checks that the arguments of a node are valid, instantiates the
rule of that name and arity, compares the conclusion with the goal and checks
the children against the premises in order. The equations that instantiate
rules are generated from the rules of the presentation. A computed leaf runs
the lookup, instantiation or conversion program on the theory and compares the
result with the claimed answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.Languages.MM0.Kernel
open Calculus
open ComputationalContext ComputationalArguments ComputationalProof ComputationalConversion
open ComputationalTyping ComputationalDefinitions

/-! ## Patterns as data -/

def dataCode (datum : Term) : Term := .expr [.sym "Pattern:Data", datum]
def itemsCode (items : List Term) : Term := .expr [.sym "Pattern:Items", .list items]
def applyGeneric (head : String) (arguments : List Term) : Term :=
  .expr [.sym "Pattern:Apply", .lit head, .list arguments]

/-- The name of a nullary application, read from its data. -/
def atomName? : List Term → Option String
  | [.expr [.sym "Pattern:Apply", .lit name, .list []]] => some name
  | [.expr [.sym "Pattern:Items", .list []]] => some "nil"
  | _ => none

def itemsOf? : List Term → Option (List Term)
  | [.expr [.sym "Pattern:Items", .list items]] => some items
  | _ => none

def consOf? : List Term → Option (Term × List Term)
  | [.expr [.sym "Pattern:Data", item], .expr [.sym "Pattern:Items", .list items]] =>
      some (item, items)
  | _ => none

/-- **The data of a constructor application**, from the data of its arguments:
the pattern of an engine datum or of a list of data becomes that datum or list. -/
def applyCode (head : String) (arguments : List Term) : Term :=
  if head = "sym" then
    match atomName? arguments with
    | some name => dataCode (.sym name)
    | none => applyGeneric head arguments
  else if head = "lit" then
    match atomName? arguments with
    | some name => dataCode (.lit name)
    | none => applyGeneric head arguments
  else if head = "var" then
    match atomName? arguments with
    | some name => dataCode (.var name)
    | none => applyGeneric head arguments
  else if head = "expr" then
    match itemsOf? arguments with
    | some items => dataCode (.expr items)
    | none => applyGeneric head arguments
  else if head = "list" then
    match itemsOf? arguments with
    | some items => dataCode (.list items)
    | none => applyGeneric head arguments
  else if head = "cons" then
    match consOf? arguments with
    | some (item, items) => itemsCode (item :: items)
    | none => applyGeneric head arguments
  else if head = "nil" then
    match arguments with
    | [] => itemsCode []
    | _ => applyGeneric head arguments
  else applyGeneric head arguments

def binderCode : Option String → Term
  | none => .sym "None"
  | some name => .expr [.sym "Some", .lit name]

def kindCode : CollType → Term
  | .vec => .sym "Collection:Vec"
  | .hashBag => .sym "Collection:HashBag"
  | .hashSet => .sym "Collection:HashSet"

mutual

/-- **A pattern as data.** -/
def code : Pattern → Term
  | .bvar index => .expr [.sym "Pattern:Bound", natural index]
  | .fvar name => .expr [.sym "Pattern:Free", .lit name]
  | .apply head arguments => applyCode head (codes arguments)
  | .lambda binder body => .expr [.sym "Pattern:Lambda", binderCode binder, code body]
  | .multiLambda arity binders body =>
      .expr [.sym "Pattern:MultiLambda", natural arity, .list (binders.map .lit), code body]
  | .subst body replacement => .expr [.sym "Pattern:Subst", code body, code replacement]
  | .collection kind elements rest =>
      .expr [.sym "Pattern:Collection", kindCode kind, .list (codes elements), binderCode rest]

def codes : List Pattern → List Term
  | [] => []
  | pattern :: patterns => code pattern :: codes patterns

end

theorem codes_eq_map : ∀ patterns : List Pattern, codes patterns = patterns.map code
  | [] => rfl
  | pattern :: patterns => by simp [codes, codes_eq_map patterns]

theorem codes_length (patterns : List Pattern) : (codes patterns).length = patterns.length := by
  simp [codes_eq_map]

/-! ## Decoding -/

def binderOf? : Term → Option (Option String)
  | .sym "None" => some none
  | .expr [.sym "Some", .lit name] => some (some name)
  | _ => none

def kindOf? : Term → Option CollType
  | .sym "Collection:Vec" => some .vec
  | .sym "Collection:HashBag" => some .hashBag
  | .sym "Collection:HashSet" => some .hashSet
  | _ => none

def namesOf? : List Term → Option (List String)
  | [] => some []
  | .lit name :: rest => (namesOf? rest).map (name :: ·)
  | _ => none

mutual

def decode : Term → Option Pattern
  | .expr [.sym "Pattern:Data", datum] => some (termPattern datum)
  | .expr [.sym "Pattern:Items", .list items] => some (itemsPattern items)
  | .expr [.sym "Pattern:Apply", .lit head, .list arguments] => (decodes arguments).map (.apply head)
  | .expr [.sym "Pattern:Bound", index] => (natural? index).map .bvar
  | .expr [.sym "Pattern:Free", .lit name] => some (.fvar name)
  | .expr [.sym "Pattern:Lambda", binder, body] => do
      pure (.lambda (← binderOf? binder) (← decode body))
  | .expr [.sym "Pattern:MultiLambda", arity, .list binders, body] => do
      pure (.multiLambda (← natural? arity) (← namesOf? binders) (← decode body))
  | .expr [.sym "Pattern:Subst", body, replacement] => do
      pure (.subst (← decode body) (← decode replacement))
  | .expr [.sym "Pattern:Collection", kind, .list elements, rest] => do
      pure (.collection (← kindOf? kind) (← decodes elements) (← binderOf? rest))
  | _ => none

def decodes : List Term → Option (List Pattern)
  | [] => some []
  | term :: terms => do pure ((← decode term) :: (← decodes terms))

end

theorem namesOf?_map : ∀ names : List String, namesOf? (names.map .lit) = some names
  | [] => rfl
  | name :: names => by simp [namesOf?, namesOf?_map names]

theorem atomName?_eq_some {arguments : List Term} {name : String}
    (found : atomName? arguments = some name) :
    arguments = [applyGeneric name []] ∨ (arguments = [itemsCode []] ∧ name = "nil") := by
  unfold atomName? at found
  split at found <;> simp_all [applyGeneric, itemsCode]

theorem itemsOf?_eq_some {arguments items : List Term} (found : itemsOf? arguments = some items) :
    arguments = [itemsCode items] := by
  unfold itemsOf? at found
  split at found <;> simp_all [itemsCode]

theorem consOf?_eq_some {arguments : List Term} {item : Term} {items : List Term}
    (found : consOf? arguments = some (item, items)) :
    arguments = [dataCode item, itemsCode items] := by
  unfold consOf? at found
  split at found <;> simp_all [dataCode, itemsCode]

theorem decode_dataCode (datum : Term) : decode (dataCode datum) = some (termPattern datum) := by
  simp [dataCode, decode]

theorem decode_itemsCode (items : List Term) : decode (itemsCode items) = some (itemsPattern items) := by
  simp [itemsCode, decode]

theorem decode_applyGeneric (head : String) (arguments : List Term) :
    decode (applyGeneric head arguments) = (decodes arguments).map (.apply head) := by
  simp [applyGeneric, decode]

/-- Decoding inverts the data of an application. -/
theorem decode_applyCode (head : String) {arguments : List Term} {patterns : List Pattern}
    (decoded : decodes arguments = some patterns) :
    decode (applyCode head arguments) = some (.apply head patterns) := by
  have generic : decode (applyGeneric head arguments) = some (.apply head patterns) := by
    simp [decode_applyGeneric, decoded]
  have atom : ∀ {name : String}, atomName? arguments = some name →
      patterns = [.apply name []] := by
    intro name found
    rcases atomName?_eq_some found with rfl | ⟨rfl, rfl⟩
    · simp [decodes, decode_applyGeneric] at decoded
      exact decoded.symm
    · simp [decodes, decode_itemsCode, itemsPattern] at decoded
      exact decoded.symm
  have items : ∀ {list : List Term}, itemsOf? arguments = some list →
      patterns = [itemsPattern list] := by
    intro list found
    rw [itemsOf?_eq_some found] at decoded
    simp [decodes, decode_itemsCode] at decoded
    exact decoded.symm
  unfold applyCode
  split_ifs with hsym hlit hvar hexpr hlist hcons hnil
  · subst hsym
    cases found : atomName? arguments with
    | none => exact generic
    | some name => simp [decode_dataCode, termPattern, atom found]
  · subst hlit
    cases found : atomName? arguments with
    | none => exact generic
    | some name => simp [decode_dataCode, termPattern, atom found]
  · subst hvar
    cases found : atomName? arguments with
    | none => exact generic
    | some name => simp [decode_dataCode, termPattern, atom found]
  · subst hexpr
    cases found : itemsOf? arguments with
    | none => exact generic
    | some list => simp [decode_dataCode, termPattern, items found]
  · subst hlist
    cases found : itemsOf? arguments with
    | none => exact generic
    | some list => simp [decode_dataCode, termPattern, items found]
  · subst hcons
    cases found : consOf? arguments with
    | none => exact generic
    | some pair =>
        obtain ⟨item, list⟩ := pair
        rw [consOf?_eq_some found] at decoded
        simp [decodes, decode_dataCode, decode_itemsCode] at decoded
        simp [decode_itemsCode, itemsPattern, ← decoded]
  · subst hnil
    cases arguments with
    | nil =>
        simp [decodes] at decoded
        simp [decode_itemsCode, itemsPattern, ← decoded]
    | cons _ _ => exact generic
  · exact generic

mutual

theorem decode_code : ∀ pattern : Pattern, decode (code pattern) = some pattern
  | .bvar index => by simp [code, decode]
  | .fvar name => by simp [code, decode]
  | .apply head arguments => decode_applyCode head (decodes_codes arguments)
  | .lambda binder body => by
      cases binder <;> simp [code, decode, binderCode, binderOf?, decode_code body]
  | .multiLambda arity binders body => by
      simp [code, decode, namesOf?_map binders, decode_code body]
  | .subst body replacement => by
      simp [code, decode, decode_code body, decode_code replacement]
  | .collection kind elements rest => by
      cases kind <;> cases rest <;>
        simp [code, decode, kindCode, kindOf?, binderCode, binderOf?, decodes_codes elements]

theorem decodes_codes : ∀ patterns : List Pattern, decodes (codes patterns) = some patterns
  | [] => rfl
  | pattern :: patterns => by simp [codes, decodes, decode_code pattern, decodes_codes patterns]

end

/-- **The encoding of patterns is injective.** -/
theorem code_injective : Function.Injective code := by
  intro first second same
  have decoded := congrArg decode same
  rw [decode_code, decode_code] at decoded
  exact Option.some.inj decoded

theorem code_eq_dataCode {pattern : Pattern} {datum : Term} (same : code pattern = dataCode datum) :
    pattern = termPattern datum := by
  have decoded := congrArg decode same
  rw [decode_code, decode_dataCode] at decoded
  exact Option.some.inj decoded

theorem code_eq_itemsCode {pattern : Pattern} {items : List Term}
    (same : code pattern = itemsCode items) : pattern = itemsPattern items := by
  have decoded := congrArg decode same
  rw [decode_code, decode_itemsCode] at decoded
  exact Option.some.inj decoded

/-! ## The data of engine data and of applications -/

theorem applyCode_nullary (name : String) :
    applyCode name [] = if name = "nil" then itemsCode [] else applyGeneric name [] := by
  unfold applyCode
  by_cases hnil : name = "nil"
  · subst hnil; simp
  · simp only [hnil, if_false]
    split_ifs <;> rfl

theorem atomName?_nullary (name : String) : atomName? [applyCode name []] = some name := by
  rw [applyCode_nullary]
  split_ifs with hnil
  · subst hnil; rfl
  · rfl

mutual

/-- The pattern of an engine datum is encoded as that datum. -/
theorem code_termPattern : ∀ datum : Term, code (termPattern datum) = dataCode datum
  | .sym name => by
      simp only [termPattern, code, codes]
      have named := atomName?_nullary name
      generalize applyCode name [] = argument at named ⊢
      simp [applyCode, named]
  | .lit name => by
      simp only [termPattern, code, codes]
      have named := atomName?_nullary name
      generalize applyCode name [] = argument at named ⊢
      simp [applyCode, named]
  | .var name => by
      simp only [termPattern, code, codes]
      have named := atomName?_nullary name
      generalize applyCode name [] = argument at named ⊢
      simp [applyCode, named]
  | .expr items => by
      simp only [termPattern, code, codes, code_itemsPattern items]
      simp [applyCode, itemsOf?, itemsCode]
  | .list items => by
      simp only [termPattern, code, codes, code_itemsPattern items]
      simp [applyCode, itemsOf?, itemsCode]

/-- A cons chain of data is encoded as the list of those data. -/
theorem code_itemsPattern : ∀ items : List Term, code (itemsPattern items) = itemsCode items
  | [] => by simp [itemsPattern, code, codes, applyCode]
  | item :: items => by
      simp only [itemsPattern, code, codes, code_termPattern item, code_itemsPattern items]
      simp [applyCode, consOf?, dataCode, itemsCode]

end

theorem applyCode_cases (head : String) (arguments : List Term) :
    (∃ datum, applyCode head arguments = dataCode datum) ∨
      (∃ items, applyCode head arguments = itemsCode items) ∨
        applyCode head arguments = applyGeneric head arguments := by
  unfold applyCode
  split_ifs
  all_goals first
    | (split <;> simp)
    | simp

/-- Outside the constructors of engine data, an application is encoded as it
is written. -/
theorem applyCode_generic {head : String} {arguments : List Term}
    (notData : head ∉ ["sym", "lit", "var", "expr"])
    (notList : ¬ (head = "list" ∧ arguments.length = 1))
    (notCons : ¬ (head = "cons" ∧ arguments.length = 2))
    (notNil : ¬ (head = "nil" ∧ arguments = [])) :
    applyCode head arguments = applyGeneric head arguments := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notData
  obtain ⟨hsym, hlit, hvar, hexpr⟩ := notData
  unfold applyCode
  simp only [hsym, hlit, hvar, hexpr, if_false]
  by_cases hlist : head = "list"
  · subst hlist
    have : itemsOf? arguments = none := by
      cases found : itemsOf? arguments with
      | none => rfl
      | some items => exact absurd ⟨rfl, by simp [itemsOf?_eq_some found]⟩ notList
    simp [this]
  · by_cases hcons : head = "cons"
    · subst hcons
      have : consOf? arguments = none := by
        cases found : consOf? arguments with
        | none => rfl
        | some pair => exact absurd ⟨rfl, by simp [consOf?_eq_some found]⟩ notCons
      simp [this]
    · by_cases hnil : head = "nil"
      · subst hnil
        cases arguments with
        | nil => exact absurd ⟨rfl, rfl⟩ notNil
        | cons _ _ => simp
      · simp [hlist, hcons, hnil]

/-- The data of a pattern is an encoded datum, an encoded list of data, or
carries another tag. -/
theorem code_shape (pattern : Pattern) :
    (∃ datum, code pattern = dataCode datum) ∨ (∃ items, code pattern = itemsCode items) ∨
      ((∀ value, code pattern ≠ .expr [.sym "Pattern:Data", value]) ∧
        (∀ value, code pattern ≠ .expr [.sym "Pattern:Items", value])) := by
  cases pattern with
  | apply head arguments =>
      rcases applyCode_cases head (codes arguments) with found | found | generic
      · exact .inl found
      · exact .inr (.inl found)
      · refine .inr (.inr ⟨?_, ?_⟩) <;> intro value <;> simp [code, generic, applyGeneric]
  | _ => refine .inr (.inr ⟨?_, ?_⟩) <;> intro value <;> simp [code]

theorem code_argumentValid {pattern : Pattern} (depth : Nat) :
    (∃ datum, code pattern = dataCode datum) ∨ (∃ items, code pattern = itemsCode items) →
      argumentValidAt depth pattern = true := by
  rintro (⟨datum, same⟩ | ⟨items, same⟩)
  · rw [code_eq_dataCode same]
    exact termPattern_argumentValid depth datum
  · rw [code_eq_itemsCode same]
    obtain ⟨ground, canonical⟩ := itemsPattern_valid depth items
    simp [argumentValidAt, ground, canonical]

/-! ## Certificates and theories as data -/

variable (T : Theory)

/-- A computed leaf as data: the operation, its query and the claimed answer. -/
def leafCode : (family T).Leaf → Term
  | ⟨.lookup, ⟨index, declaration, _⟩⟩ =>
      .expr [.sym "Certificate:Lookup", natural index, encodeTheorem declaration]
  | ⟨.instantiate, ⟨(context, declaration, arguments), result, _⟩⟩ =>
      .expr [.sym "Certificate:Instance", encodeContext context, encodeTheorem declaration,
        encodeExpressions arguments, encodeExpressions result.hypotheses, encode result.conclusion]
  | ⟨.convert, ⟨(context, witness), result, _⟩⟩ =>
      .expr [.sym "Certificate:Conversion", encodeContext context, encodeWitness witness,
        encode result.left, encode result.right, natural result.sort]

def nodeCode (rule : String) (arguments : List Pattern) (children : List Term) : Term :=
  .expr [.sym "Certificate:Node", .lit rule, .list (codes arguments), .list children]

mutual

def rawCode : RawProof → Term
  | .node ⟨⟨rule⟩, arguments⟩ children => nodeCode rule arguments (rawCodes children)

def rawCodes : List RawProof → List Term
  | [] => []
  | proof :: proofs => rawCode proof :: rawCodes proofs

end

mutual

/-- **A certificate as data.** A replayed derivation is encoded as its nodes. -/
def certificateCode : CompactProof (family T).Leaf → Term
  | .replay proof => rawCode proof
  | .computed leaf => leafCode T leaf
  | .node ⟨⟨rule⟩, arguments⟩ children => nodeCode rule arguments (certificateCodes children)

def certificateCodes : List (CompactProof (family T).Leaf) → List Term
  | [] => []
  | proof :: proofs => certificateCode proof :: certificateCodes proofs

end

/-- The theory as data: its term signature, definitions and theorems. -/
def theoryArguments : List Term :=
  [encodeTable T.terms, encodeDefinitions T.definitions, encodeTheorems T.theorems]

/-- The arguments of a checking request. -/
def request (goal : Pattern) (proof : CompactProof (family T).Leaf) : List Term :=
  theoryArguments T ++ [code goal, certificateCode T proof]

/-! ## Rule instantiation, generated from the rules -/

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

/-- The right side building the data of an application in a rule. -/
def applyTemplate (head : String) (arguments : List Term) : Term :=
  if head = "list" ∧ arguments.length = 1 then call "mm0:pattern-list" arguments
  else if head = "cons" ∧ arguments.length = 2 then call "mm0:pattern-cons" arguments
  else if head = "nil" ∧ arguments = [] then call "Pattern:Items" [.list []]
  else call "Pattern:Apply" [.lit head, .list arguments]

mutual

/-- The right side building the data of a rule pattern from the data of its
metavariables. -/
def templateTerm : Pattern → Term
  | .fvar name => .var name
  | .apply head arguments => applyTemplate head (templateTerms arguments)
  | _ => .sym "Pattern:Unsupported"

def templateTerms : List Pattern → List Term
  | [] => []
  | pattern :: patterns => templateTerm pattern :: templateTerms patterns

end

mutual

/-- Rule patterns the generated equations build: metavariables among the
rule's and applications of constructors other than those of engine data. -/
def templateFragment (names : List String) : Pattern → Bool
  | .fvar name => decide (name ∈ names)
  | .apply head arguments =>
      !(["sym", "lit", "var", "expr"].contains head) && templatesFragment names arguments
  | _ => false

def templatesFragment (names : List String) : List Pattern → Bool
  | [] => true
  | pattern :: patterns => templateFragment names pattern && templatesFragment names patterns

end

/-- The equation instantiating one rule: its name and an argument vector of its
arity give the data of its conclusion and of its premises. -/
def ruleEquation (r : FORule) : DeterministicEquations.Equation :=
  ⟨r.id, "mm0:rule-instance", [.lit r.id, .list (r.vars.map .var)],
    call "Rule:Instance" [templateTerm r.conclusion, .list (templateTerms r.premises)]⟩

def unknownRule : DeterministicEquations.Equation :=
  ⟨"rule-unknown", "mm0:rule-instance", [v "rule", v "arguments"], .sym "None"⟩

def ruleEquations : Program := rules.map ruleEquation ++ [unknownRule]

/-! ## Pattern data -/

def consEquations : Program := [
  ⟨"pattern-cons-items", "mm0:pattern-cons", [call "Pattern:Data" [v "item"], call "Pattern:Items" [v "items"]],
    call "Pattern:Items" [call "nik:list-cons" [v "item", v "items"]]⟩,
  ⟨"pattern-cons", "mm0:pattern-cons", [v "item", v "items"],
    call "Pattern:Apply" [.lit "cons", .list [v "item", v "items"]]⟩]

def listEquations : Program := [
  ⟨"pattern-list-items", "mm0:pattern-list", [call "Pattern:Items" [v "items"]], call "Pattern:Data" [v "items"]⟩,
  ⟨"pattern-list", "mm0:pattern-list", [v "items"], call "Pattern:Apply" [.lit "list", .list [v "items"]]⟩]

/-- Validity of an argument at a binder depth: closed at that depth, without
binder display names. -/
def validEquations : Program := [
  ⟨"valid-data", "mm0:pattern-valid", [v "depth", call "Pattern:Data" [v "datum"]], .sym "True"⟩,
  ⟨"valid-items", "mm0:pattern-valid", [v "depth", call "Pattern:Items" [v "items"]], .sym "True"⟩,
  ⟨"valid-bound", "mm0:pattern-valid", [v "depth", call "Pattern:Bound" [v "index"]],
    call "nik:nat-lt" [v "index", v "depth"]⟩,
  ⟨"valid-free", "mm0:pattern-valid", [v "depth", call "Pattern:Free" [v "name"]], .sym "False"⟩,
  ⟨"valid-apply", "mm0:pattern-valid", [v "depth", call "Pattern:Apply" [v "head", v "arguments"]],
    call "mm0:pattern-valid-all" [v "depth", v "arguments"]⟩,
  ⟨"valid-lambda", "mm0:pattern-valid", [v "depth", call "Pattern:Lambda" [.sym "None", v "body"]],
    call "mm0:pattern-valid" [call "nik:nat-add" [v "depth", natural 1], v "body"]⟩,
  ⟨"valid-lambda-named", "mm0:pattern-valid", [v "depth", call "Pattern:Lambda" [v "binder", v "body"]],
    .sym "False"⟩,
  ⟨"valid-multi-lambda", "mm0:pattern-valid",
    [v "depth", call "Pattern:MultiLambda" [v "arity", .list [], v "body"]],
    call "mm0:pattern-valid" [call "nik:nat-add" [v "depth", v "arity"], v "body"]⟩,
  ⟨"valid-multi-lambda-named", "mm0:pattern-valid",
    [v "depth", call "Pattern:MultiLambda" [v "arity", v "binders", v "body"]], .sym "False"⟩,
  ⟨"valid-subst", "mm0:pattern-valid", [v "depth", call "Pattern:Subst" [v "body", v "replacement"]],
    call "mm0:pattern-both" [call "mm0:pattern-valid" [call "nik:nat-add" [v "depth", natural 1], v "body"],
      call "mm0:pattern-valid" [v "depth", v "replacement"]]⟩,
  ⟨"valid-collection", "mm0:pattern-valid",
    [v "depth", call "Pattern:Collection" [v "kind", v "elements", .sym "None"]],
    call "mm0:pattern-valid-all" [v "depth", v "elements"]⟩,
  ⟨"valid-collection-rest", "mm0:pattern-valid",
    [v "depth", call "Pattern:Collection" [v "kind", v "elements", v "rest"]], .sym "False"⟩,
  ⟨"valid-all", "mm0:pattern-valid-all", [v "depth", v "patterns"],
    call "mm0:pattern-valid-view" [v "depth", call "nik:list-view" [v "patterns"]]⟩,
  ⟨"valid-all-nil", "mm0:pattern-valid-view", [v "depth", .sym "List:Nil"], .sym "True"⟩,
  ⟨"valid-all-cons", "mm0:pattern-valid-view", [v "depth", call "List:Cons" [v "first", v "rest"]],
    call "mm0:pattern-both" [call "mm0:pattern-valid" [v "depth", v "first"],
      call "mm0:pattern-valid-all" [v "depth", v "rest"]]⟩,
  ⟨"both-true", "mm0:pattern-both", [.sym "True", v "other"], v "other"⟩,
  ⟨"both-false", "mm0:pattern-both", [.sym "False", v "other"], .sym "False"⟩]

/-! ## Certificates -/

private def theory : List Term := [v "table", v "definitions", v "theorems"]

def certificateEquations : Program := [
  ⟨"certificate-node", "mm0:certificate",
    theory ++ [v "goal", call "Certificate:Node" [v "rule", v "arguments", v "children"]],
    call "mm0:certificate-valid" ([call "mm0:pattern-valid-all" [natural 0, v "arguments"]] ++ theory ++
      [v "goal", v "rule", v "arguments", v "children"])⟩,
  ⟨"certificate-lookup", "mm0:certificate",
    theory ++ [v "goal", call "Certificate:Lookup" [v "index", v "declaration"]],
    call "mm0:certificate-leaf" [
      call "nik:data-eq" [call "nik:nat-table-get" [v "theorems", v "index"], call "Some" [v "declaration"]],
      call "Pattern:Apply" [.lit "mm0:theorem",
        .list [call "Pattern:Data" [v "index"], call "Pattern:Data" [v "declaration"]]],
      v "goal"]⟩,
  ⟨"certificate-instance", "mm0:certificate",
    theory ++ [v "goal", call "Certificate:Instance"
      [v "context", v "declaration", v "arguments", v "hypotheses", v "conclusion"]],
    call "mm0:certificate-leaf" [
      call "nik:data-eq" [call "mm0:instantiate-theorem" [v "table", v "context", v "declaration", v "arguments"],
        call "MM0:Instance" [v "hypotheses", v "conclusion"]],
      call "Pattern:Apply" [.lit "mm0:instance",
        .list [call "Pattern:Data" [v "context"], call "Pattern:Data" [v "declaration"],
          call "Pattern:Data" [v "arguments"], call "Pattern:Data" [v "hypotheses"],
          call "Pattern:Data" [v "conclusion"]]],
      v "goal"]⟩,
  ⟨"certificate-conversion", "mm0:certificate",
    theory ++ [v "goal", call "Certificate:Conversion" [v "context", v "witness", v "left", v "right", v "sort"]],
    call "mm0:certificate-leaf" [
      call "nik:data-eq" [call "mm0:conversion" [v "table", v "definitions", v "context", v "witness"],
        call "MM0:Converted" [v "left", v "right", v "sort"]],
      call "Pattern:Apply" [.lit "mm0:converts",
        .list [call "Pattern:Data" [v "context"], call "Pattern:Data" [v "left"],
          call "Pattern:Data" [v "right"], call "Pattern:Data" [v "sort"]]],
      v "goal"]⟩,
  ⟨"leaf-returned", "mm0:certificate-leaf", [.sym "True", v "judgment", v "goal"],
    call "nik:data-eq" [v "judgment", v "goal"]⟩,
  ⟨"leaf-refused", "mm0:certificate-leaf", [.sym "False", v "judgment", v "goal"], .sym "False"⟩,
  ⟨"node-valid", "mm0:certificate-valid",
    [.sym "True"] ++ theory ++ [v "goal", v "rule", v "arguments", v "children"],
    call "mm0:certificate-rule" ([call "mm0:rule-instance" [v "rule", v "arguments"]] ++ theory ++
      [v "goal", v "children"])⟩,
  ⟨"node-invalid", "mm0:certificate-valid",
    [.sym "False"] ++ theory ++ [v "goal", v "rule", v "arguments", v "children"], .sym "False"⟩,
  ⟨"rule-unknown", "mm0:certificate-rule", [.sym "None"] ++ theory ++ [v "goal", v "children"],
    .sym "False"⟩,
  ⟨"rule-known", "mm0:certificate-rule",
    [call "Rule:Instance" [v "conclusion", v "premises"]] ++ theory ++ [v "goal", v "children"],
    call "mm0:certificate-conclusion" ([call "nik:data-eq" [v "conclusion", v "goal"]] ++ theory ++
      [v "premises", v "children"])⟩,
  ⟨"conclusion-differs", "mm0:certificate-conclusion",
    [.sym "False"] ++ theory ++ [v "premises", v "children"], .sym "False"⟩,
  ⟨"conclusion-agrees", "mm0:certificate-conclusion",
    [.sym "True"] ++ theory ++ [v "premises", v "children"],
    call "mm0:certificate-children" (theory ++ [v "premises", v "children"])⟩,
  ⟨"children", "mm0:certificate-children", theory ++ [v "premises", v "children"],
    call "mm0:certificate-children-view" (theory ++
      [call "nik:list-view" [v "premises"], call "nik:list-view" [v "children"]])⟩,
  ⟨"children-done", "mm0:certificate-children-view", theory ++ [.sym "List:Nil", .sym "List:Nil"],
    .sym "True"⟩,
  ⟨"children-next", "mm0:certificate-children-view",
    theory ++ [call "List:Cons" [v "premise", v "premises"], call "List:Cons" [v "child", v "children"]],
    call "mm0:certificate-rest" ([call "mm0:certificate" (theory ++ [v "premise", v "child"])] ++ theory ++
      [v "premises", v "children"])⟩,
  ⟨"children-mismatch", "mm0:certificate-children-view", theory ++ [v "premises", v "children"],
    .sym "False"⟩,
  ⟨"rest-refused", "mm0:certificate-rest", [.sym "False"] ++ theory ++ [v "premises", v "children"],
    .sym "False"⟩,
  ⟨"rest", "mm0:certificate-rest", [.sym "True"] ++ theory ++ [v "premises", v "children"],
    call "mm0:certificate-children" (theory ++ [v "premises", v "children"])⟩]

/-- The equations of the calculus checker. -/
def calculusEquations : Program :=
  ruleEquations ++ consEquations ++ listEquations ++ validEquations ++ certificateEquations

/-- **The checker of the MM0 calculus**: the proof program, whose lookup,
instantiation and conversion the leaves call, followed by the calculus
equations. -/
def calculusProgram : Program := proofProgram ++ calculusEquations

/-! ## Selection among the equations of one head -/

theorem consEquations_select_other {item items : Term}
    (unmatched : matchTerms [.expr [.sym "Pattern:Data", .var "item"],
      .expr [.sym "Pattern:Items", .var "items"]] [item, items] = none) :
    consEquations.select "mm0:pattern-cons" [item, items] =
      some (consEquations[1], [("item", item), ("items", items)]) := by
  simp only [Program.select, consEquations, call, v, List.findSome?_cons, List.findSome?_nil, unmatched]
  simp [matchTerms, matchTerm]

theorem listEquations_select_other {items : Term}
    (unmatched : matchTerm (.expr [.sym "Pattern:Items", .var "items"]) items = none) :
    listEquations.select "mm0:pattern-list" [items] =
      some (listEquations[1], [("items", items)]) := by
  simp only [Program.select, listEquations, call, v, List.findSome?_cons, List.findSome?_nil,
    matchTerms, unmatched]
  simp [matchTerm]

theorem matchTerms_names : ∀ (names : List String) (values : List Term),
    matchTerms (names.map .var) values =
      if names.length = values.length then some (names.zip values) else none
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | name :: names, value :: values => by
      rw [List.map_cons, matchTerms, matchTerms_names names values]
      by_cases same : names.length = values.length <;> simp [matchTerm, same]

/-- The generated rule equations select the rule of the requested name and
arity, and only an unknown name or arity falls to the refusal. -/
theorem select_rules (rs : List FORule) (rule : String) (values : List Term) :
    Program.select (rs.map ruleEquation ++ [unknownRule]) "mm0:rule-instance" [.lit rule, .list values] =
      match rs.find? (fun r => r.id == rule && values.length == r.vars.length) with
      | some r => some (ruleEquation r, r.vars.zip values)
      | none => some (unknownRule, [("rule", .lit rule), ("arguments", .list values)]) := by
  induction rs with
  | nil => simp [Program.select, unknownRule, v, matchTerms, matchTerm]
  | cons r rs ih =>
      have matched : matchTerms [.lit r.id, .list (r.vars.map .var)] [.lit rule, .list values] =
          if r.id = rule ∧ r.vars.length = values.length then some (r.vars.zip values) else none := by
        simp only [matchTerms, matchTerm, matchTerms_names]
        by_cases sameId : r.id = rule <;> by_cases sameLength : r.vars.length = values.length <;>
          simp [sameId, sameLength]
      simp only [Program.select] at ih ⊢
      rw [List.map_cons, List.cons_append, List.findSome?_cons, ih]
      have params : (ruleEquation r).params = [.lit r.id, .list (r.vars.map .var)] := rfl
      have head : (ruleEquation r).head = "mm0:rule-instance" := rfl
      simp only [head, params, matched, List.find?_cons]
      by_cases sameId : r.id = rule
      · by_cases sameLength : values.length = r.vars.length
        · simp [sameId, sameLength]
        · have other : ¬ r.vars.length = values.length := fun same => sameLength same.symm
          have differs : (values.length == r.vars.length) = false := by simpa using sameLength
          simp [sameId, other, differs]
      · have differs : (r.id == rule) = false := by simpa using sameId
        simp [sameId, differs]

/-- The generated rule equations cover every rule of the presentation. -/
theorem rules_templates : ∀ r ∈ rules,
    templateFragment r.vars r.conclusion = true ∧ templatesFragment r.vars r.premises = true := by
  decide

set_option maxRecDepth 8192 in
theorem calculusEquations_disjoint :
    ∀ equation ∈ calculusEquations, equation.head ∉ proofProgram.calledHeads := by
  simp only [proofProgram, conversionProgram, unfoldingProgram, ComputationalFreshDummies.freshEquations,
    encodeBinder, encodeDependencies, encodeNaturals, Finset.sort_empty]
  decide

end Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
