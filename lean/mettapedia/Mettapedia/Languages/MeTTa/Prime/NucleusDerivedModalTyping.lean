import Mettapedia.Languages.MeTTa.Prime.LanguageDef
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# OSLF-derived modal typing of the current Prime LanguageDef

This module runs the existing OSLF derivation — `unaryCrossings`,
`classifyArrow`, and the `langDiamondUsing` / `langBoxUsing` modalities — over
the exploratory Prime presentation `metta-prime-spec-probe` and records, as
decidable theorems, exactly what that derivation yields today.

Nothing here is authored typing.  Every statement is a readout of the
LanguageDef, so changing the LanguageDef changes or breaks these theorems.

What the readout establishes:

* the reduction sort is `Process`: every authored rewrite has a
  `Process`-category head;
* there are exactly five unary sort crossings;
* the two answer constructors are the only reflecting (`□`) arrows;
* no arrow has domain `Process`, so the derivation yields no quoting (`◇`)
  arrow at all — Prime's `prime-quote` / `prime-drop` cross
  `Atom ↔ PrimeName` and are classified neutral, unlike rho's
  `NQuote` / `PDrop`, which cross `Proc ↔ Name`;
* the sort `Alternatives` is declared but no constructor produces it, so the
  presentation names nondeterminism without generating it;
* the diamond/box Galois connection holds for any relation environment.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.Prime.LanguageDef

/-- The designated reduction sort of the nucleus. -/
def processSort : String := "Process"

/-! ## Inventory -/

theorem nucleus_name : language.name = "metta-prime-spec-probe" := by
  decide

theorem nucleus_constructor_count : language.terms.length = 17 := by
  decide

theorem nucleus_rewrite_count : language.rewrites.length = 6 := by
  decide

theorem nucleus_equation_count : language.equations.length = 1 := by
  decide

/-- The head symbol of every authored rewrite, in authored order. -/
def rewriteHeads : List String :=
  language.rewrites.map fun rule =>
    match rule.left with
    | .apply head _ => head
    | _ => "?"

theorem rewrite_heads_exact :
    rewriteHeads =
      ["zero-query", "zero-evaluate", "zero-evaluate", "prime-need",
        "prime-need-answer", "prime-evaluate-name"] := by
  decide

/-- Every rewrite head is a constructor of the `Process` sort, which is what
makes `Process` the reduction sort for the OSLF classification. -/
theorem rewrite_heads_are_process :
    (language.terms.filter fun term => term.label ∈ rewriteHeads).all
      (fun term => term.category == processSort) = true := by
  decide

/-! ## Sort crossings -/

theorem nucleus_crossings_exact :
    unaryCrossings language =
      [("zero-query-answer", "Atom", "Process"),
        ("zero-evaluate-answer", "Atom", "Process"),
        ("prime-quote", "Atom", "PrimeName"),
        ("prime-drop", "PrimeName", "Atom"),
        ("prime-receipt", "Atom", "PrimeReceipt")] := by
  decide

theorem quote_crossing :
    ("prime-quote", "Atom", "PrimeName") ∈ unaryCrossings language := by
  decide

theorem drop_crossing :
    ("prime-drop", "PrimeName", "Atom") ∈ unaryCrossings language := by
  decide

theorem evaluate_answer_crossing :
    ("zero-evaluate-answer", "Atom", "Process") ∈ unaryCrossings language := by
  decide

/-! ## Sorts as objects and constructors as arrows -/

def atomSort : LangSort language := ⟨"Atom", by decide⟩
def processSortObj : LangSort language := ⟨"Process", by decide⟩
def nameSort : LangSort language := ⟨"PrimeName", by decide⟩

def quoteArrow : SortArrow language atomSort nameSort :=
  ⟨"prime-quote", quote_crossing⟩

def dropArrow : SortArrow language nameSort atomSort :=
  ⟨"prime-drop", drop_crossing⟩

def evaluateAnswerArrow : SortArrow language atomSort processSortObj :=
  ⟨"zero-evaluate-answer", evaluate_answer_crossing⟩

/-! ## The derived classification

Positive readout: the answer constructors reflect into the reduction sort
and therefore carry `□`.  Negative readout: quotation in this presentation
does not touch the reduction sort at all, so the derivation assigns it no
modality.  This is the exact point at which the nucleus differs from rho. -/

theorem evaluate_answer_is_reflecting :
    classifyArrow language processSort evaluateAnswerArrow = .reflecting := by
  decide

theorem quote_is_neutral :
    classifyArrow language processSort quoteArrow = .neutral := by
  decide

theorem drop_is_neutral :
    classifyArrow language processSort dropArrow = .neutral := by
  decide

/-- No unary crossing has the reduction sort as its domain, so the OSLF
derivation produces no quoting (`◇`) arrow for this presentation. -/
theorem no_quoting_crossing :
    (unaryCrossings language).all
      (fun crossing => !(crossing.2.1 == processSort)) = true := by
  decide

/-- Exactly two crossings reflect into the reduction sort. -/
theorem reflecting_crossings_exact :
    (unaryCrossings language).filter
      (fun crossing => crossing.2.2 == processSort) =
      [("zero-query-answer", "Atom", "Process"),
        ("zero-evaluate-answer", "Atom", "Process")] := by
  decide

/-! ## Under the settled principle: atoms reduce, data does not

Prime's settled principle is that evaluable atoms are the processes and inert
data are the names; ordinary MeTTa rewrites atoms to atoms.  The probe
presentation instead wraps evaluation in a separate `Process` sort.  Read
under the settled principle — `Atom` as the reduction sort — quotation and
dropping are classified exactly as in rho, and the probe's own rewrites are
then all off the reduction sort.  The theorems below make the probe's
divergence from the principle explicit and checkable; they are the reason the
probe, not the principle, is the thing to revise. -/

def atomReductionSort : String := "Atom"

theorem quote_is_quoting_if_atoms_reduce :
    classifyArrow language atomReductionSort quoteArrow = .quoting := by
  decide

theorem drop_is_reflecting_if_atoms_reduce :
    classifyArrow language atomReductionSort dropArrow = .reflecting := by
  decide

/-- Under the atom-reduction reading the presentation would have rho-shaped
modalities and no reduction at all: every authored rewrite head is a
`Process` constructor, none is an `Atom`. -/
theorem no_rewrite_has_atom_head :
    (language.terms.filter fun term => term.label ∈ rewriteHeads).all
      (fun term => !(term.category == atomReductionSort)) = true := by
  decide

#print axioms quote_is_quoting_if_atoms_reduce
#print axioms no_rewrite_has_atom_head

/-! ## Backward pressure: what "quotation is a modality" forces on the presentation

Nothing here decides the reduction sort.  The theorem states the constraint
that a *derived* requirement transports back onto the LanguageDef: if
quotation is to carry `◇` at all, the reduction sort must be the domain of
`prime-quote`, i.e. atoms.  Any presentation in which something other than
atoms reduces cannot have quotation as a derived modality. -/

theorem quote_quoting_iff_atoms_reduce (reductionSort : String) :
    classifyArrow language reductionSort quoteArrow = .quoting ↔
      reductionSort = "Atom" := by
  rw [classifyArrow_eq_quoting_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem drop_reflecting_iff_atoms_reduce (reductionSort : String) :
    classifyArrow language reductionSort dropArrow = .reflecting ↔
      reductionSort = "Atom" := by
  rw [classifyArrow_eq_reflecting_iff]
  constructor
  · rintro ⟨_, h⟩; exact h.symm
  · intro h; subst h; exact ⟨by decide, rfl⟩

#print axioms quote_quoting_iff_atoms_reduce
#print axioms drop_reflecting_iff_atoms_reduce

/-! ## The phantom nondeterminism sort -/

theorem alternatives_is_declared : "Alternatives" ∈ language.typeNames := by
  decide

/-- The sort is declared, but no constructor has it as category: the
presentation names nondeterminism without any way to build it. -/
theorem alternatives_has_no_constructor :
    language.terms.all (fun term => !(term.category == "Alternatives")) = true := by
  decide

/-! ## The derived modalities form a Galois connection, for any environment -/

theorem nucleus_galois (env : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) :
    GaloisConnection
      (langDiamondUsing env language)
      (langBoxUsing env language) :=
  langGaloisUsing env language

/-! ## Populating `Alternatives` without touching the probe's dependents

The probe leaves `Alternatives` empty.  The extension below adds the two
constructors and two rewrites that nondeterminism needs, as a *separate*
LanguageDef, so that the derivation can be read off without perturbing the
modules that pin the probe today.  Promotion into the probe itself is a
design decision (`Q-TT-001`/`Q-TT-002` of the research-spec draft).

* `prime-choose : Process × Process → Process` with rewrites to either branch:
  under the derived modalities this makes `◇φ (choose a b) ⇔ φ a ∨ φ b` the
  *may* modality and `□φ (choose a b) ⇔ φ a ∧ φ b` the *must* modality — the
  Hennessy–Milner pair falls out of choice-as-reduction with no new role;
* `prime-collect : Process → Alternatives`, the reification of a process into
  its bag of alternatives; its domain is the reduction sort, so the existing
  classifier reads it as **quoting** (`◇`): collecting is the monadic unit
  seen through OSLF, and no `classifyArrow` extension is required for it. -/

private def constructor (label category : String)
    (parameters : List (String × TypeExpr)) : GrammarRule :=
  { label
    category
    params := parameters.map fun parameter => .simple parameter.1 parameter.2
    syntaxPattern := [] }

def chooseConstructor : GrammarRule :=
  constructor "prime-choose" "Process"
    [("left", .base "Process"), ("right", .base "Process")]

def collectConstructor : GrammarRule :=
  constructor "prime-collect" "Alternatives" [("process", .base "Process")]

def chooseLeftRewrite : RewriteRule :=
  { name := "prime-choose-left"
    typeContext := [("left", .base "Process"), ("right", .base "Process")]
    premises := []
    left := .apply "prime-choose" [.fvar "left", .fvar "right"]
    right := .fvar "left" }

def chooseRightRewrite : RewriteRule :=
  { name := "prime-choose-right"
    typeContext := [("left", .base "Process"), ("right", .base "Process")]
    premises := []
    left := .apply "prime-choose" [.fvar "left", .fvar "right"]
    right := .fvar "right" }

/-- The probe extended with nondeterministic choice and collection. -/
def probeWithChoice : LanguageDef :=
  { language with
    name := "metta-prime-spec-probe-with-choice"
    terms := language.terms ++ [chooseConstructor, collectConstructor]
    rewrites := language.rewrites ++ [chooseLeftRewrite, chooseRightRewrite] }

/-! Validation of the extension evaluates to `[]` (checked by the `#eval`
below); the kernel-checked proof uses the same per-field lemma as the probe's
`language_validate` and is deferred until the extension is promoted into the
probe.  The readout theorems below do not depend on validity. -/
#eval probeWithChoice.validate

theorem alternatives_has_constructor_in_extension :
    (probeWithChoice.terms.filter
      (fun term => term.category == "Alternatives")).map (·.label) =
      ["prime-collect"] := by
  decide

theorem collect_crossing :
    ("prime-collect", "Process", "Alternatives") ∈
      unaryCrossings probeWithChoice := by
  decide

def collectDomain : LangSort probeWithChoice := ⟨"Process", by decide⟩
def collectCodomain : LangSort probeWithChoice := ⟨"Alternatives", by decide⟩

def collectArrow : SortArrow probeWithChoice collectDomain collectCodomain :=
  ⟨"prime-collect", collect_crossing⟩

/-- Reifying a process into its alternatives is classified as quoting: the
first `◇`-carrying arrow the derivation produces for Prime. -/
theorem collect_is_quoting :
    classifyArrow probeWithChoice processSort collectArrow = .quoting := by
  decide

/-- A relation environment with no facts: the choice rewrites need none. -/
def noFacts : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv where
  tuples := fun _ _ => []

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-- Choice reduces to either branch in one step, and to nothing else. -/
theorem choose_step_exact :
    rewriteAt (engineBasePremises noFacts) probeWithChoice 1
      (a "prime-choose" [a "prime-left-demo", a "prime-right-demo"]) =
      [a "prime-left-demo", a "prime-right-demo"] := by
  decide +kernel

theorem probeWithChoice_galois (env : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) :
    GaloisConnection
      (langDiamondUsing env probeWithChoice)
      (langBoxUsing env probeWithChoice) :=
  langGaloisUsing env probeWithChoice

#print axioms collect_is_quoting
#print axioms choose_step_exact

#print axioms nucleus_crossings_exact
#print axioms rewrite_heads_are_process
#print axioms evaluate_answer_is_reflecting
#print axioms quote_is_neutral
#print axioms no_quoting_crossing
#print axioms alternatives_has_no_constructor
#print axioms nucleus_galois

end Mettapedia.Languages.MeTTa.Prime.NucleusDerivedModalTyping
