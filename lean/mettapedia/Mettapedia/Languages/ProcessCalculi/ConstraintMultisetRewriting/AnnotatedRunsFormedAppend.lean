import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormedCompiler
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.AppendDefinitionCompletion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionPrograms

/-!
# Second consumer: dependent vector append, compiled and executed

The source is the Flower's checked dependent append program (`Programs.append_typed`, at
`Π (A : U) (m n : Nat), Vec A m → Vec A n → Vec A (m + n)`) applied, in the formed context
`a b : Nat`, to the element type `Nat`, the lengths `1` and `1`, and the vectors `[a]` and `[b]`.
The elements stay symbolic: they are the context's variables, shared with the transform.

## The theory's values and substitution

* **Value discipline** (`vectorDiscipline`): the canonical constants are the type formers and
  constructors `Nat`, `zero`, `succ`, `Vec`, `nil`, `cons`. Every root rule is a natural or vector
  iota row, headed by an eliminator outside the table.
* **Root action** (`vectorRootAction`): inherited codes are empty, delta codes are closed,
  declared codes substitute their arguments.

## The compiled program (`appendProgram`)

* **Operations**: the compiled append denotes the program's body at its arguments; the compiled
  addition denotes `Programs.add`.
* **The callable** (`appendCallable`): the checked append program with its telescope. The compiler
  reads the source (`compile_source`): a call of the program's closed body through its telescope,
  with values as arguments.
* **Four compiled rules, each with the Flower's checked certificate**:
  * `appendConsRule` and `appendNilRule` carry the very codes behind the Flower's symbolic append
    equations (`Programs.Computation.append_cons`, `append_nil`): the search results
    `consComparison` and `nilComparison`. Their schemas denote exactly those equations' endpoints
    (`append_rule_schemas`);
  * `addZeroRule` and `addSuccRule` carry codes for the natural iota rows of addition, found once
    by the Flower's search on each rule's schema: the zero row in one root step, the successor row
    in a root step and two beta steps (`add_rule_steps`).
  Each is checked on its schema (`appendConsRule_sound`, `appendNilRule_sound`,
  `addZeroRule_sound`, `addSuccRule_sound`).
* **The compiled run** (`append_executes`): three compiled steps (cons, add-zero, nil), each
  admitted at its cut; the run is the firing of the compiled steps (`steps_firing`).

## The source side

* **Source judgment** (`appendSource`): the closed program applied through its telescope, with the
  arguments typed by kernel replay of the Flower's elaborator; the displayed type is
  `Vec Nat (add 1 1)`.
* **The value's formation** (`valueTypeOver`, `valueTerm`) at `Vec Nat 2`, the index conversion
  `add 1 1 ≡ 2` (`typeCertificate`), and the value in `Vec Nat (add 1 1)` (`value_in_sum_length`).
* **The Flower's own conversion** (`appendEvidence`), found by its search: an independent second
  witness, kept for comparison with the certificate the run produces.

## Context substitution

Substituting `a ↦ 0, b ↦ 1` (`closing`) transports the formed evidence to the closed instance, its
certificates transformed and still accepted (`closedEvidence`, `closed_class`,
`closed_stepCount`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
namespace Append

open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
open Presentation (Tm Ctx Sub subst ids subComp liftClosed)
open Presentation.FormationSensitiveContextual (Context TypeOver Term TotalTerm QTerm empty)
open Presentation.StructuralConversionCode (RootDecoder Certificate Code mapEndpoints)
open AnnotatedRuns

abbrev rules : Presentation.Rules Presentation.Tower.Head := Programs.rules

instance appendHeadTyping : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Presentation.Tower.rules.headTyping h u))
instance appendIsUniverse : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Presentation.Tower.rules.isUniverse h))
instance appendJoin : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Presentation.Tower.rules.join u v w))
instance appendCumulative : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Presentation.Tower.rules.cumulative u v))
instance appendHeadEq : DecidableRel rules.headEq :=
  fun h u => Presentation.LevelTower.instDecidableHeadEq h u

/-! ## The root-code substitution of the vector decoder -/

/-- Substitution of the vector decoder's root codes: inherited codes are empty, a delta code is
closed, a declared code substitutes its arguments. -/
def vectorRootSubstitute {n m : Nat} (σ : Sub Presentation.Tower.Head n m) :
    Programs.decoder.Code n → Programs.decoder.Code m
  | .inherited code => nomatch code
  | .delta name => .delta name
  | .declared code => .declared (Presentation.SchemaTableConversionCode.Code.substitute σ code)

/-- A delta code decodes to a closed pair, which every substitution fixes. -/
theorem delta_natural {n m : Nat} (σ : Sub Presentation.Tower.Head n m) (name : Presentation.DeclName) :
    (Programs.signature.valueOf? name).map (fun value => (Tm.const name, liftClosed (n := m) value)) =
      mapEndpoints (subst σ)
        ((Programs.signature.valueOf? name).map (fun value => (Tm.const name, liftClosed (n := n) value))) := by
  cases Programs.signature.valueOf? name with
  | none => rfl
  | some value => simp [mapEndpoints, subst]

theorem schema_substitute_ids {n : Nat} (code : Presentation.SchemaTableConversionCode.Code
    Presentation.Tower.Head n) : code.substitute ids = code := by
  obtain ⟨row, arguments⟩ := code
  simp only [Presentation.SchemaTableConversionCode.Code.substitute,
    Presentation.SchemaTableConversionCode.Code.mapArguments,
    Presentation.SchemaTableConversionCode.Code.mk.injEq, true_and]
  induction arguments with
  | nil => rfl
  | cons term rest ih => rw [List.map_cons, Presentation.subst_ids, ih]

theorem schema_substitute_comp {n m k : Nat} (σ : Sub Presentation.Tower.Head n m)
    (τ : Sub Presentation.Tower.Head m k)
    (code : Presentation.SchemaTableConversionCode.Code Presentation.Tower.Head n) :
    (code.substitute σ).substitute τ = code.substitute (subComp τ σ) := by
  obtain ⟨row, arguments⟩ := code
  simp only [Presentation.SchemaTableConversionCode.Code.substitute,
    Presentation.SchemaTableConversionCode.Code.mapArguments, List.map_map,
    Presentation.SchemaTableConversionCode.Code.mk.injEq, true_and]
  apply List.map_congr_left
  intro term _
  exact Presentation.subst_subComp τ σ term

/-- **The actual root action of the vector decoder**, with its laws proved. -/
def vectorRootAction : RootAction Programs.decoder where
  substitute := vectorRootSubstitute
  natural := by
    intro n m σ code
    cases code with
    | inherited code => exact nomatch code
    | delta name => exact delta_natural σ name
    | declared code =>
        exact Presentation.SchemaTableConversionCode.decode_substitute Checking.table Checking.enabled σ code
  substitute_ids := by
    intro n code
    cases code with
    | inherited code => exact nomatch code
    | delta name => rfl
    | declared code =>
        exact congrArg Presentation.DeclarationConversionCode.RootCode.declared (schema_substitute_ids code)
  substitute_comp := by
    intro n m k σ τ code
    cases code with
    | inherited code => exact nomatch code
    | delta name => rfl
    | declared code =>
        exact congrArg Presentation.DeclarationConversionCode.RootCode.declared
          (schema_substitute_comp σ τ code)

/-! ## Values of the vector theory -/

/-- The type formers and constructors of the vector theory. -/
def vectorConstructors : List Presentation.DeclName :=
  [natName, zeroName, succName, vecName, vnilName, vconsName]

/-- **The canonical constants**: the type formers and constructors. -/
def vectorCanonical (name : Presentation.DeclName) : Bool :=
  vectorConstructors.any fun constructor => decide (name = constructor)

/-- The vector theory's declarations are opaque: no name has a value. -/
theorem signature_valueOf_none (name : Presentation.DeclName) :
    Programs.signature.valueOf? name = none := by
  change (rawSignature.instantiateLevels Programs.levels Programs.levelInstance.computation).valueOf?
    name = none
  rw [Presentation.Declaration.Signature.valueOf_instantiateLevels, rawSignature_valueOf_none]
  rfl

/-- **The value discipline of the vector theory**: every root rule is a natural or vector iota
row, headed by an eliminator, which is not canonical. -/
def vectorDiscipline : ValueDiscipline rules where
  canonical := vectorCanonical
  root_head := by
    intro n left right step
    cases step with
    | inherited impossible => exact impossible.elim
    | delta lookup =>
        rw [signature_valueOf_none] at lookup
        cases lookup
    | declared evidence =>
        obtain ⟨evidence⟩ := evidence
        cases evidence <;> exact ⟨_, rfl, by decide +kernel⟩

/-! ## Kernel replay of the Flower's elaborator -/

/-- A judgment from an accepted elaboration: the Flower's own replay checker certifies it. -/
theorem judgment_of_elaborated {n : Nat} {ambient : Presentation.Tower.Ctx n}
    {term type : Presentation.Tower.Tm n} {fuel : Nat}
    (elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder Programs.choices fuel
      ambient term type).isSome = true) :
    Presentation.FormationSensitive.Judgment rules ambient term type := by
  cases accepted : Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder Programs.choices fuel
      ambient term type with
  | none =>
      rw [accepted] at elaborated
      cases elaborated
  | some submission =>
      exact Presentation.FormationSensitiveElaboration.elaborate_sound rules Programs.decoder Programs.choices fuel
        ambient term type submission accepted

/-- The formed context `a b : Nat`. -/
def ctx : Presentation.Tower.Ctx 2 := .snoc (.snoc .nil natTm) natTm

def one : Presentation.Tower.Tm 2 := succApp zeroTm
def two : Presentation.Tower.Tm 2 := succApp one
def elementSort : Presentation.Tower.Tm 2 := .head (.sort (.param 0))
/-- `[a]`. -/
def xs : Presentation.Tower.Tm 2 := vconsApp natTm zeroTm (.var 1) (vnilApp natTm)
/-- `[b]`. -/
def ys : Presentation.Tower.Tm 2 := vconsApp natTm zeroTm (.var 0) (vnilApp natTm)
/-- `[a, b]`. -/
def value : Presentation.Tower.Tm 2 := vconsApp natTm one (.var 1) ys
/-- `Vec Nat (add 1 1)`, the instance of `Vec A (m + n)`. -/
def sourceType : Presentation.Tower.Tm 2 := vecApp natTm (Programs.add one one)
/-- `Vec Nat 2`. -/
def valueType : Presentation.Tower.Tm 2 := vecApp natTm two

theorem element_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 ctx natTm elementSort).isSome = true := by decide +kernel
theorem one_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 ctx one natTm).isSome = true := by decide +kernel
theorem xs_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 ctx xs (vecApp natTm one)).isSome = true := by decide +kernel
theorem ys_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 ctx ys (vecApp natTm one)).isSome = true := by decide +kernel
theorem value_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 ctx value valueType).isSome = true := by decide +kernel
theorem sourceType_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 ctx sourceType elementSort).isSome = true := by decide +kernel
theorem valueType_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 ctx valueType elementSort).isSome = true := by decide +kernel

theorem ctx_formed : Presentation.FormationSensitive.ContextFormation rules ctx :=
  (judgment_of_elaborated xs_elaborated).context

/-- The formed context, as an object of the Flower's contextual category. -/
def context : Context rules := ⟨2, ctx, ctx_formed⟩

/-! ## The source program and its execution -/

/-- The arguments `Nat, 1, 1, [a], [b]`, in de Bruijn order. -/
def arguments : Sub Presentation.Tower.Head 5 2 := AppendDefinitionCompletion.arguments natTm one one xs ys

/-- **The source program**: the checked append program applied through its telescope. -/
def sourceCode : Presentation.Tower.Tm 2 :=
  Presentation.TelescopeAbstraction.applyClosed Programs.appendContext arguments (liftClosed Programs.appendTerm)

/-- Application of a closed function through its telescope, for the formation-sensitive
judgment (the raw version is `Presentation.TelescopeAbstraction.applyClosed_typed`). -/
theorem applyClosed_typing {R : Presentation.Rules Presentation.Tower.Head} {k m : Nat}
    {telescope : Presentation.Tower.Ctx k} {target : Presentation.Tower.Ctx m}
    {σ : Sub Presentation.Tower.Head k m} {type : Presentation.Tower.Tm k}
    {function : Presentation.Tower.Tm m}
    (typed : Presentation.FormationSensitive.CtxMor R telescope target σ)
    (functionTyping : Presentation.FormationSensitive.Typing R target function
      (liftClosed (Presentation.TelescopeAbstraction.closeType telescope type))) :
    Presentation.FormationSensitive.Typing R target
      (Presentation.TelescopeAbstraction.applyClosed telescope σ function) (subst σ type) := by
  induction telescope with
  | nil => simpa only [Presentation.TelescopeAbstraction.applyClosed, Presentation.TelescopeAbstraction.closeType,
      Presentation.TelescopeAbstraction.subst_empty] using functionTyping
  | snoc prior domain ih =>
      have priorTyped : Presentation.FormationSensitive.CtxMor R prior target
          (fun index => σ index.succ) := by
        intro index
        simpa only [Presentation.Ctx.lookup_snoc_succ, Presentation.TelescopeAbstraction.subst_prior] using
          typed index.succ
      have functionTyped := ih priorTyped functionTyping
      have argumentTyped := typed 0
      simp only [Presentation.Ctx.lookup_snoc_zero, Presentation.TelescopeAbstraction.subst_prior] at argumentTyped
      have application := Presentation.FormationSensitive.Typing.appElim functionTyped argumentTyped
      simpa only [Presentation.TelescopeAbstraction.applyClosed, subst, Presentation.TelescopeAbstraction.subst_open] using
        application

theorem arguments_typed : Presentation.FormationSensitive.CtxMor rules Programs.appendContext ctx
    arguments := by
  intro index
  match index with
  | ⟨0, _⟩ =>
      change Presentation.FormationSensitive.Typing rules ctx ys (vecApp natTm one)
      exact (judgment_of_elaborated ys_elaborated).typing
  | ⟨1, _⟩ =>
      change Presentation.FormationSensitive.Typing rules ctx xs (vecApp natTm one)
      exact (judgment_of_elaborated xs_elaborated).typing
  | ⟨2, _⟩ =>
      change Presentation.FormationSensitive.Typing rules ctx one natTm
      exact (judgment_of_elaborated one_elaborated).typing
  | ⟨3, _⟩ =>
      change Presentation.FormationSensitive.Typing rules ctx one natTm
      exact (judgment_of_elaborated one_elaborated).typing
  | ⟨4, _⟩ =>
      change Presentation.FormationSensitive.Typing rules ctx natTm elementSort
      exact (judgment_of_elaborated element_elaborated).typing

/-- **The source judgment**: the program at `Vec Nat (add 1 1)`. -/
theorem source_typed : Presentation.FormationSensitive.Typing rules ctx sourceCode sourceType := by
  have lifted : Presentation.FormationSensitive.Typing rules ctx (liftClosed Programs.appendTerm)
      (liftClosed Programs.appendType) :=
    Programs.append_typed.typing.renameTyping (fun index => index.elim0)
  have applied := applyClosed_typing arguments_typed lifted
  have resultType : subst arguments Programs.appendResult = sourceType := by decide
  rw [resultType] at applied
  exact applied

def sourceTypeOver : TypeOver context :=
  ⟨sourceType, .sort (.param 0), .sort _, (judgment_of_elaborated sourceType_elaborated).typing⟩

def valueTypeOver : TypeOver context :=
  ⟨valueType, .sort (.param 0), .sort _, (judgment_of_elaborated valueType_elaborated).typing⟩

def appendSource : TotalTerm context := ⟨sourceTypeOver, ⟨sourceCode, source_typed⟩⟩

def valueTerm : Term context valueTypeOver := ⟨value, (judgment_of_elaborated value_elaborated).typing⟩

/-- The Flower's conversion search, from the source to the value and between the indices. -/
def termComparison := Presentation.StructuralConversionSearch.compare Programs.decoder Programs.searchRoot
  (headEq := rules.headEq) 96 sourceCode value
def typeComparison := Presentation.StructuralConversionSearch.compare Programs.decoder Programs.searchRoot
  (headEq := rules.headEq) 48 sourceType valueType

theorem term_compared : termComparison.isSome = true := by decide +kernel
theorem type_compared : typeComparison.isSome = true := by decide +kernel

def termCertificate : Certificate rules.headEq Programs.decoder.decode sourceCode value :=
  ⟨termComparison.get term_compared,
    Presentation.StructuralConversionPrograms.compare_checked Programs.decoder Programs.searchRoot 96 _ _ _
      (Option.some_get term_compared).symm⟩

def typeCertificate : Certificate rules.headEq Programs.decoder.decode sourceType valueType :=
  ⟨typeComparison.get type_compared,
    Presentation.StructuralConversionPrograms.compare_checked Programs.decoder Programs.searchRoot 48 _ _ _
      (Option.some_get type_compared).symm⟩

/-- **The source execution as formed evidence**: the value `[a, b]` at its formed type, with the
Flower's checked codes. -/
def appendEvidence : FormedEvidence Programs.decoder context appendSource value where
  targetType := valueTypeOver
  targetTerm := valueTerm
  target_code := rfl
  typeCertificate := typeCertificate
  termCertificate := termCertificate

/-- **The value is in `Vec A (m + n)`**: the value's judgment, retyped at the source's displayed
type `Vec Nat (add 1 1)` by the symmetric checked index conversion. -/
theorem value_in_sum_length :
    Presentation.FormationSensitive.Judgment rules ctx value sourceType :=
  Presentation.FormationSensitive.Judgment.convertChecked Programs.decoder
    (judgment_of_elaborated value_elaborated) (judgment_of_elaborated sourceType_elaborated).typing
    (.sort _) typeCertificate.symm.checked

/-! ## Context substitution -/

/-- The closing substitution `a ↦ 0, b ↦ 1`, a formed morphism from the empty context. -/
def closingSubstitution : Sub Presentation.Tower.Head 2 0 := fun index => ![succApp zeroTm, zeroTm] index

theorem zero_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 .nil zeroTm natTm).isSome = true := by decide +kernel
theorem succZero_elaborated : (Presentation.FormationSensitiveElaboration.elaborate rules Programs.decoder
    Programs.choices 32 .nil (succApp zeroTm) natTm).isSome = true := by decide +kernel

def closing : empty rules ⟶ context where
  substitution := closingSubstitution
  typed := by
    intro index
    match index with
    | ⟨0, _⟩ =>
        change Presentation.FormationSensitive.Typing rules .nil (succApp zeroTm) natTm
        exact (judgment_of_elaborated succZero_elaborated).typing
    | ⟨1, _⟩ =>
        change Presentation.FormationSensitive.Typing rules .nil zeroTm natTm
        exact (judgment_of_elaborated zero_elaborated).typing

/-- **The closed instance of the formed evidence**, by the actual code substitution. -/
def closedEvidence := appendEvidence.reindex vectorRootAction closing

/-- The closed source and the closed value are one `QTerm` class: the substituted certificates
are accepted at the closed endpoints. -/
theorem closed_class :
    QTerm.mk (TotalTerm.reindex appendSource closing).2 = QTerm.mk closedEvidence.targetTerm :=
  closedEvidence.class_eq

theorem closed_stepCount : closedEvidence.stepCount = appendEvidence.stepCount :=
  appendEvidence.stepCount_reindex vectorRootAction closing

/-- The closed instance is the program applied to `[0]` and `[1]`, retyped at `Vec Nat 2`. -/
theorem closed_retyped :
    Presentation.FormationSensitive.Judgment rules .nil (subst closingSubstitution sourceCode)
      (subst closingSubstitution valueType) :=
  closedEvidence.retyped

/-! ## The compilation -/

/-- The compiled operations: the declared append program and the natural addition. -/
def appendName : Presentation.DeclName := AppendDefinitionCompletion.name
def addName : Presentation.DeclName := `Programs.add

def natP : Pattern := .const natName
def zeroP : Pattern := .const zeroName
def succP (m : Pattern) : Pattern := ap (.const succName) m
def vnilP (a : Pattern) : Pattern := ap (.const vnilName) a
def vconsP (a m h t : Pattern) : Pattern := ap (ap (ap (ap (.const vconsName) a) m) h) t
def appendP (a m n l r : Pattern) : Pattern := operation appendName [a, m, n, l, r]
def addP (m n : Pattern) : Pattern := operation addName [m, n]

/-- The body of the compiled addition over its two arguments. -/
def addBody : Presentation.Tower.Tm 2 := Programs.add (.var 1) (.var 0)

/-- **The operation table**: the compiled append denotes the append program's body at its
arguments, the compiled addition the natural addition. -/
def vectorOperations : Operations Presentation.Tower.Head := fun name arity =>
  if name = appendName then
    match arity with
    | 5 => some Programs.appendBody
    | _ => none
  else if name = addName then
    match arity with
    | 2 => some addBody
    | _ => none
  else none

/-- **The callable append program**: the checked program's telescope and body. -/
def appendCallable : Callable Presentation.Tower.Head :=
  ⟨appendName, 5, Programs.appendContext, Programs.appendBody⟩

/-- **The compiled cons equation.** Schema variables: element `5`, first length `3`, second length
`4`, head `2`, tail `1`, right `0`; outputs `6` (the length) and `7` (the tail); result `8`. Its
certificate is the Flower's checked code for the symbolic cons equation, the code behind
`Programs.Computation.append_cons`. -/
def appendConsRule : CompiledRule Presentation.Tower.Head Programs.decoder.Code where
  arity := 6
  left := appendP (.var 5) (succP (.var 3)) (.var 4) (vconsP (.var 5) (.var 3) (.var 2) (.var 1))
    (.var 0)
  result := 8
  value := vconsP (.var 5) (.var 6) (.var 2) (.var 7)
  produce := [(addP (.var 3) (.var 4), 6), (appendP (.var 5) (.var 3) (.var 4) (.var 1) (.var 0), 7)]
  certificate := Programs.Computation.consComparison.get Programs.Computation.cons_checked

/-- **The compiled nil equation.** Schema variables: element `2`, second length `1`, right `0`;
result `3`. Its certificate is the Flower's checked code behind
`Programs.Computation.append_nil`. -/
def appendNilRule : CompiledRule Presentation.Tower.Head Programs.decoder.Code where
  arity := 3
  left := appendP (.var 2) zeroP (.var 1) (vnilP (.var 2)) (.var 0)
  result := 3
  value := .var 0
  produce := []
  certificate := Programs.Computation.nilComparison.get Programs.Computation.nil_checked

/-- The zero row of the natural eliminator at addition, found once by the Flower's search. -/
def addZeroComparison := Presentation.StructuralConversionSearch.compare Programs.decoder
  Programs.searchRoot (headEq := rules.headEq) 8 (Programs.add zeroTm (.var 0) : Presentation.Tower.Tm 1)
  (.var 0)

theorem addZero_compared : addZeroComparison.isSome = true := by decide +kernel

/-- The successor row of the natural eliminator at addition, found once by the Flower's search. -/
def addSuccComparison := Presentation.StructuralConversionSearch.compare Programs.decoder
  Programs.searchRoot (headEq := rules.headEq) 8
  (Programs.add (succApp (.var 0)) (.var 1) : Presentation.Tower.Tm 2)
  (succApp (Programs.add (.var 0) (.var 1)))

theorem addSucc_compared : addSuccComparison.isSome = true := by decide +kernel

/-- **The compiled zero row of addition.** Schema variable: second argument `0`; result `1`. -/
def addZeroRule : CompiledRule Presentation.Tower.Head Programs.decoder.Code where
  arity := 1
  left := addP zeroP (.var 0)
  result := 1
  value := .var 0
  produce := []
  certificate := addZeroComparison.get addZero_compared

/-- **The compiled successor row of addition.** Schema variables: `0`, `1`; output `2`; result
`3`. -/
def addSuccRule : CompiledRule Presentation.Tower.Head Programs.decoder.Code where
  arity := 2
  left := addP (succP (.var 0)) (.var 1)
  result := 3
  value := succP (.var 2)
  produce := [(addP (.var 0) (.var 1), 2)]
  certificate := addSuccComparison.get addSucc_compared

/-- **Per-rule soundness of the cons rule against the Flower's checked cons equation.** -/
theorem appendConsRule_sound :
    appendConsRule.Sound rules.headEq Programs.decoder.decode vectorOperations := by
  unfold CompiledRule.Sound
  decide +kernel

/-- **Per-rule soundness of the nil rule against the Flower's checked nil equation.** -/
theorem appendNilRule_sound :
    appendNilRule.Sound rules.headEq Programs.decoder.decode vectorOperations := by
  unfold CompiledRule.Sound
  decide +kernel

/-- **Per-rule soundness of the zero row**: one root step of the natural eliminator. -/
theorem addZeroRule_sound :
    addZeroRule.Sound rules.headEq Programs.decoder.decode vectorOperations := by
  unfold CompiledRule.Sound
  decide +kernel

/-- **Per-rule soundness of the successor row**: a root step of the natural eliminator and two
beta steps. -/
theorem addSuccRule_sound :
    addSuccRule.Sound rules.headEq Programs.decoder.decode vectorOperations := by
  unfold CompiledRule.Sound
  decide +kernel

/-- **The cons and nil rules are the Flower's symbolic append equations**: on their schema
variables, the taken computation and the reduct denote exactly the endpoints of the checked
equations behind `Programs.Computation.append_cons` and `append_nil`. -/
theorem append_rule_schemas :
    (denote vectorOperations appendConsRule.left : Option (Presentation.Tower.Tm 6)) =
        some Programs.Computation.consSource ∧
      (denote vectorOperations appendConsRule.reduct : Option (Presentation.Tower.Tm 6)) =
        some Programs.Computation.consTarget ∧
      (denote vectorOperations appendNilRule.left : Option (Presentation.Tower.Tm 3)) =
        some Programs.Computation.nilSource ∧
      (denote vectorOperations appendNilRule.reduct : Option (Presentation.Tower.Tm 3)) =
        some (.var 0) := by
  decide +kernel

/-- The add certificates are the natural iota rows: the zero row is one root step, the successor
row a root step and two beta steps. -/
theorem add_rule_steps :
    addZeroRule.certificate.stepCount = 1 ∧ addSuccRule.certificate.stepCount = 3 := by
  decide +kernel

/-- **The compiled append program.** -/
def appendProgram : CompiledProgram rules Programs.decoder where
  operations := vectorOperations
  callables := [appendCallable]
  rules := [appendConsRule, appendNilRule, addZeroRule, addSuccRule]
  callables_denoted := by
    intro c member
    rw [List.mem_singleton] at member
    subst member
    decide +kernel
  rules_sound := by
    intro rule member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact appendConsRule_sound
    · exact appendNilRule_sound
    · exact addZeroRule_sound
    · exact addSuccRule_sound

/-- The caller's result variable. -/
def resultVar : Nat := 2

/-- **The compiled term of the source**: the compiled append on the quoted arguments. -/
def compiledTerm : Pattern :=
  appendP natP (succP zeroP) (succP zeroP) (vconsP natP zeroP (.var 1) (vnilP natP))
    (vconsP natP zeroP (.var 0) (vnilP natP))

/-- **The compiler reads the source**: the call of the checked append program through its
telescope, with values as arguments. -/
theorem compile_source : compile vectorCanonical appendProgram.callables sourceCode =
    some compiledTerm := by
  decide +kernel

/-- **The compiled program**: one pending computation of the compiled term. -/
def program : Pattern := evaluate compiledTerm (.var resultVar)

/-- The cons rule's instance for the run. -/
def appendConsInstance (A M N H T Ys R K R' : Nat) : RuleInstance Pattern where
  take := [evaluate (appendP (.var A) (succP (.var M)) (.var N) (vconsP (.var A) (.var M) (.var H) (.var T))
    (.var Ys)) (.var R)]
  read := []
  tell := [(.var R, vconsP (.var A) (.var K) (.var H) (.var R'))]
  checks := []
  produce := [evaluate (addP (.var M) (.var N)) (.var K),
    evaluate (appendP (.var A) (.var M) (.var N) (.var T) (.var Ys)) (.var R')]

/-- The nil rule's instance for the run. -/
def appendNilInstance (A N Ys R : Nat) : RuleInstance Pattern where
  take := [evaluate (appendP (.var A) zeroP (.var N) (vnilP (.var A)) (.var Ys)) (.var R)]
  read := []
  tell := [(.var R, .var Ys)]
  checks := []
  produce := []

/-- The zero row's instance for the run. -/
def addZeroInstance (N R : Nat) : RuleInstance Pattern where
  take := [evaluate (addP zeroP (.var N)) (.var R)]
  read := []
  tell := [(.var R, .var N)]
  checks := []
  produce := []

/-- Occurrence labels: the program, then what the cons firing makes. -/
def label : Nat → Pattern
  | 0 => program
  | 1 => evaluate (addP (.var 4) (.var 5)) (.var 10)
  | 2 => evaluate (appendP (.var 3) (.var 4) (.var 5) (.var 7) (.var 8)) (.var 11)
  | _ => .const .anonymous

def consFiring : Firing Pattern (Subst signature) Nat :=
  ⟨appendConsInstance 3 4 5 6 7 8 9 10 11, [], ⟨[0], [], [1, 2]⟩⟩
def addFiring : Firing Pattern (Subst signature) Nat := ⟨addZeroInstance 12 13, [], ⟨[1], [], []⟩⟩
def nilFiring : Firing Pattern (Subst signature) Nat :=
  ⟨appendNilInstance 14 15 16 17, [], ⟨[2], [], []⟩⟩

/-- **The transform run**: the cons step, the addition of the lengths, the nil step. -/
def run : List (Firing Pattern (Subst signature) Nat) := [consFiring, addFiring, nilFiring]

def start : Configuration Pattern Nat := compiledStart 0

/-! ## The run as compiled steps -/

def consRename : Nat → Nat
  | 0 => 8 | 1 => 7 | 2 => 6 | 3 => 4 | 4 => 5 | 5 => 3 | 6 => 10 | 7 => 11 | _ => 9

def addRename : Nat → Nat
  | 0 => 12 | _ => 13

def nilRename : Nat → Nat
  | 0 => 16 | 1 => 15 | 2 => 14 | _ => 17

/-- The cons step: occurrence `0` taken, `1` and `2` made. -/
def consStep : CompiledStep appendProgram :=
  ⟨appendConsRule, List.mem_cons_self, consRename, 0, [1, 2]⟩

/-- The zero row of addition on occurrence `1`. -/
def addStep : CompiledStep appendProgram :=
  ⟨addZeroRule, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), addRename, 1, []⟩

/-- The nil step on occurrence `2`. -/
def nilStep : CompiledStep appendProgram :=
  ⟨appendNilRule, List.mem_cons_of_mem _ List.mem_cons_self, nilRename, 2, []⟩

/-- **The compiled run as data.** -/
def steps : List (CompiledStep appendProgram) := [consStep, addStep, nilStep]

theorem consInstance_compiled :
    appendConsRule.instantiate consRename = appendConsInstance 3 4 5 6 7 8 9 10 11 := by
  unfold CompiledRule.instantiate appendConsInstance
  congr 1 <;> decide +kernel

theorem addInstance_compiled : addZeroRule.instantiate addRename = addZeroInstance 12 13 := by
  unfold CompiledRule.instantiate addZeroInstance
  congr 1
  decide +kernel

theorem nilInstance_compiled : appendNilRule.instantiate nilRename = appendNilInstance 14 15 16 17 := by
  unfold CompiledRule.instantiate appendNilInstance
  congr 1
  decide +kernel

/-- **The run is the firing of the compiled steps.** -/
theorem steps_firing : steps.map CompiledStep.firing = run := by
  change [(⟨appendConsRule.instantiate consRename, [], ⟨[0], [], [1, 2]⟩⟩ :
      Firing Pattern (Subst signature) Nat),
    ⟨addZeroRule.instantiate addRename, [], ⟨[1], [], []⟩⟩,
    ⟨appendNilRule.instantiate nilRename, [], ⟨[2], [], []⟩⟩] = run
  rw [consInstance_compiled, addInstance_compiled, nilInstance_compiled]
  rfl

/-! ## The transform execution and its certificate -/

theorem cons_valid : consFiring.Valid action label start :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_unified (fuel := 64) (by decide +kernel), by simp [consFiring, appendConsInstance]⟩,
    by simp [consFiring]⟩

theorem add_valid : addFiring.Valid action label (consFiring.result label start) :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_unified (fuel := 64) (by decide +kernel), by simp [addFiring, addZeroInstance]⟩,
    by simp [addFiring]⟩

theorem nil_valid : nilFiring.Valid action label (addFiring.result label (consFiring.result label start)) :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_unified (fuel := 64) (by decide +kernel), by simp [nilFiring, appendNilInstance]⟩,
    by simp [nilFiring]⟩

/-- **The compiled run is a run of the candidate step.** -/
theorem append_executes : Executable action label start run :=
  ⟨cons_valid, add_valid, nil_valid, consistent_of_unified (fuel := 64) (by decide +kernel)⟩

/-- **The result certificate**, checked by computation: the unifier solves the final store, and
the readback of the result variable is the value `[a, b]`. -/
theorem append_certified :
    checkResult vectorCanonical 64 (follow label start run).equations resultVar value = true := by
  decide +kernel

theorem append_run_length : run.length = 3 := rfl

theorem append_source_steps : (termComparison.get term_compared).stepCount ≠ run.length := by
  decide +kernel

/-- **The compiled run and the source side of append.** The compiled run executes; its final store is
consistent and observes an answer that reads back as `[a, b]`; the value is in `Vec Nat (add 1 1)`;
the source is retyped at `Vec Nat 2`; and source and value are one `QTerm` class. -/
theorem append_square :
    Executable action label start run ∧
      action.Consistent (follow label start run).equations ∧
      (∃ answer, readback vectorCanonical answer = some value ∧
        Observes action (follow label start run).equations (.var resultVar) answer) ∧
      Presentation.FormationSensitive.Judgment rules ctx value sourceType ∧
      Presentation.FormationSensitive.Judgment rules ctx sourceCode valueType ∧
      QTerm.mk appendSource.2 = QTerm.mk valueTerm :=
  ⟨append_executes, (checkResult_sound append_certified).1, (checkResult_sound append_certified).2,
    value_in_sum_length, appendEvidence.retyped, appendEvidence.class_eq⟩

#print axioms vectorRootAction
#print axioms judgment_of_elaborated
#print axioms applyClosed_typing
#print axioms source_typed
#print axioms appendEvidence
#print axioms value_in_sum_length
#print axioms closedEvidence
#print axioms closed_class
#print axioms closed_stepCount
#print axioms closed_retyped
#print axioms append_executes
#print axioms append_certified
#print axioms append_source_steps
#print axioms append_square
#print axioms vectorDiscipline
#print axioms appendConsRule_sound
#print axioms appendNilRule_sound
#print axioms addZeroRule_sound
#print axioms addSuccRule_sound
#print axioms append_rule_schemas
#print axioms add_rule_steps
#print axioms appendProgram
#print axioms compile_source
#print axioms steps_firing

end Append
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
