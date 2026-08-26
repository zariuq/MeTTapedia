import Mettapedia.GSLT.LanguageDef.Extension

/-!
# Authored exact-integer arithmetic as a coGSLT layer

Arithmetic operations and a language's overloaded surface spellings are
different objects.  This module factors them into two dependent authoring
layers:

* `ExactInteger.theoryLayer` authors a finite collection of explicitly typed
  exact-integer operations and rejects malformed signatures or duplicates;
* `ExactInteger.surfaceLayer` is indexed by an admitted theory and authors
  unambiguous surface bindings into operations already present in that theory.

The executable arithmetic semantics belongs to the shared operation family,
not to any HE, PeTTa, or Prime surface.  Undefined exact division has no value
in the core and is represented by `Outcome.declined`; a hosted language may
subsequently observe that outcome as inertness, abstention, or a diagnostic.

This is an authoring layer, not a C implementation.  C-like machines and live
CeTTa code are separate realizations and must establish their own two-sided
adequacy at a declared observation.
-/

namespace Mettapedia.GSLT.LanguageDef.ArithmeticExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension

namespace ExactInteger

/-! ## The shared typed operation family -/

/-- The one numeric sort covered by this first arithmetic family.  Rational,
word, and IEEE families extend beside it rather than changing its laws. -/
inductive NumSort where
  | integer
  deriving DecidableEq, Repr

/-- Exact-integer binary operations.  Quotient and remainder conventions are
separate operations; an overloaded surface token does not choose their
meaning. -/
inductive CoreOp where
  | add | sub | mul
  | tquot
  | fquot
  | trem
  | frem
  deriving DecidableEq, Repr

def CoreOp.inputs (_ : CoreOp) : List NumSort := [.integer, .integer]

def CoreOp.output (_ : CoreOp) : NumSort := .integer

/-- Canonical semantic identifier, independent of a dialect spelling. -/
def CoreOp.name : CoreOp → String
  | .add => "exact-int:add"
  | .sub => "exact-int:sub"
  | .mul => "exact-int:mul"
  | .tquot => "exact-int:tquot"
  | .fquot => "exact-int:fquot"
  | .trem => "exact-int:trem"
  | .frem => "exact-int:frem"

/-- Whether the operation is undefined when its second argument is zero. -/
def CoreOp.isPartial : CoreOp → Bool
  | .add | .sub | .mul => false
  | .tquot | .fquot | .trem | .frem => true

/-- Mathematical content on the operation's domain.  Lean assigns a total
function value at zero divisors, but `coreSem` below never observes it there. -/
def CoreOp.fn : CoreOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .tquot, a, b => Int.tdiv a b
  | .fquot, a, b => Int.fdiv a b
  | .trem, a, b => Int.tmod a b
  | .frem, a, b => Int.fmod a b

def undefinedAt (op : CoreOp) (second : Int) : Prop :=
  op.isPartial = true ∧ second = 0

instance (op : CoreOp) (second : Int) : Decidable (undefinedAt op second) := by
  unfold undefinedAt
  infer_instance

inductive Outcome where
  | val (value : Int)
  | declined
  deriving DecidableEq, Repr

/-- The shared exact-integer semantics.  Dialect policy is a later
post-composition and cannot redefine this function. -/
def coreSem (op : CoreOp) (first second : Int) : Outcome :=
  if undefinedAt op second then .declined else .val (op.fn first second)

theorem coreSem_pos {op : CoreOp} {second : Int}
    (undefined : undefinedAt op second) (first : Int) :
    coreSem op first second = .declined := by
  simp [coreSem, undefined]

theorem coreSem_neg {op : CoreOp} {second : Int}
    (defined : ¬ undefinedAt op second) (first : Int) :
    coreSem op first second = .val (op.fn first second) := by
  simp [coreSem, defined]

def allOps : List CoreOp :=
  [.add, .sub, .mul, .tquot, .fquot, .trem, .frem]

theorem allOps_nodup : allOps.Nodup := by decide

theorem mem_allOps (op : CoreOp) : op ∈ allOps := by
  cases op <;> simp [allOps]

/-! ## Authored operation-theory documents -/

/-- Canonical payload retained after operation authoring succeeds.  Its
signature is derived from `op`, so an ill-typed declaration has no payload
constructor. -/
structure OperationDecl where
  op : CoreOp
  deriving DecidableEq, Repr

/-- Raw authored operation syntax retains the redundant signature so the
elaborator can reject malformed declarations rather than silently repairing
them. -/
inductive OperationSyntax where
  | operation (name : String) (inputs : List NumSort) (output : NumSort)
      (partialFlag : Bool) (op : CoreOp)
  deriving DecidableEq, Repr

def encodeOperation (declaration : OperationDecl) : OperationSyntax :=
  .operation declaration.op.name declaration.op.inputs declaration.op.output
    declaration.op.isPartial declaration.op

def decodeOperation? : OperationSyntax → Option OperationDecl
  | .operation name inputs output partialFlag op =>
      if name = op.name ∧ inputs = op.inputs ∧ output = op.output ∧
          partialFlag = op.isPartial then
        some ⟨op⟩
      else
        none

@[simp] theorem decodeOperation?_encodeOperation (declaration : OperationDecl) :
    decodeOperation? (encodeOperation declaration) = some declaration := by
  cases declaration
  simp [encodeOperation, decodeOperation?]

def TheoryAdmissible (declarations : List OperationDecl) : Bool :=
  decide (declarations.map (fun declaration => declaration.op)).Nodup

abbrev AdmittedTheory :=
  { declarations : List OperationDecl // TheoryAdmissible declarations = true }

def theoryDocumentGSLT : GSLT :=
  ExactDeclarationCodec.documentGSLT OperationSyntax

private def decodeOperations? (source : DeclarationDocument OperationSyntax) :
    Option (List OperationDecl) :=
  source.values.mapM decodeOperation?

private def elaborateTheory? (source : DeclarationDocument OperationSyntax) :
    Option AdmittedTheory := do
  let declarations ← decodeOperations? source
  if admitted : TheoryAdmissible declarations = true then
    some ⟨declarations, admitted⟩
  else
    none

private def quoteTheory (theory : AdmittedTheory) :
    DeclarationDocument OperationSyntax :=
  .bundle ((theory.1.map encodeOperation).map
    DeclarationDocument.declaration)

@[simp] private theorem decodeOperations?_map_encode
    (declarations : List OperationDecl) :
    List.mapM decodeOperation? (declarations.map encodeOperation) =
      some declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations inductionHypothesis =>
      simp [inductionHypothesis]

@[simp] private theorem decodeOperations?_quoteTheory (theory : AdmittedTheory) :
    decodeOperations? (quoteTheory theory) = some theory.1 := by
  rcases theory with ⟨declarations, admitted⟩
  unfold decodeOperations? quoteTheory
  rw [DeclarationDocument.values_bundle_map]
  exact decodeOperations?_map_encode declarations

@[simp] private theorem elaborateTheory?_quoteTheory (theory : AdmittedTheory) :
    elaborateTheory? (quoteTheory theory) = some theory := by
  rcases theory with ⟨declarations, admitted⟩
  simp [elaborateTheory?, decodeOperations?_quoteTheory, admitted]

/-- The shared exact-integer operation theory as an authored coGSLT layer.
The `Unit` base records that these mathematical operations are not owned by a
particular MeTTa dialect. -/
def theoryLayer : CoGSLTLayer Unit where
  Fiber := fun _ => AdmittedTheory
  sourceGSLT := fun _ => theoryDocumentGSLT
  elaborate := fun _ => elaborateTheory?
  quote := fun _ => quoteTheory
  elaborate_quote := fun _ => elaborateTheory?_quoteTheory
  elaborate_equation := by
    intro _ source target equivalent
    change source.values = target.values at equivalent
    unfold elaborateTheory? decodeOperations?
    rw [equivalent]
  elaborate_rewrite := by
    intro _ _ _ impossible
    exact False.elim impossible

def standardTheory : AdmittedTheory :=
  ⟨allOps.map (fun op => ⟨op⟩), by decide⟩

theorem standardTheory_contains (op : CoreOp) :
    OperationDecl.mk op ∈ standardTheory.1 := by
  cases op <;> simp [standardTheory, allOps]

/-! ## Authored dialect/profile sections -/

/-- A surface key is typed.  The same spelling may be overloaded at another
operand sort without becoming ambiguous. -/
structure SurfaceKey where
  spelling : String
  inputs : List NumSort
  deriving DecidableEq, Repr

/-- A successful binding carries only a semantic operation.  Its input and
output sorts are derived from that operation. -/
structure SurfaceBinding where
  spelling : String
  op : CoreOp
  deriving DecidableEq, Repr

def SurfaceBinding.key (binding : SurfaceBinding) : SurfaceKey :=
  ⟨binding.spelling, binding.op.inputs⟩

/-- Raw surface syntax again retains a redundant result sort so malformed
overload declarations can be rejected. -/
inductive SurfaceSyntax where
  | binding (spelling : String) (inputs : List NumSort) (output : NumSort)
      (op : CoreOp)
  deriving DecidableEq, Repr

def encodeSurface (binding : SurfaceBinding) : SurfaceSyntax :=
  .binding binding.spelling binding.op.inputs binding.op.output binding.op

def decodeSurface? : SurfaceSyntax → Option SurfaceBinding
  | .binding spelling inputs output op =>
      if spelling.isEmpty then
        none
      else if inputs = op.inputs ∧ output = op.output then
        some ⟨spelling, op⟩
      else
        none

@[simp] theorem decodeSurface?_encodeSurface
    (binding : SurfaceBinding) (nonempty : binding.spelling.isEmpty = false) :
    decodeSurface? (encodeSurface binding) = some binding := by
  cases binding
  simp [encodeSurface, decodeSurface?, nonempty]

def SectionAdmissible (theory : AdmittedTheory)
    (bindings : List SurfaceBinding) : Bool :=
  decide (bindings.map SurfaceBinding.key).Nodup &&
    bindings.all fun binding =>
      !binding.spelling.isEmpty &&
        decide (binding.op ∈ theory.1.map (fun declaration => declaration.op))

abbrev AdmittedSection (theory : AdmittedTheory) :=
  { bindings : List SurfaceBinding // SectionAdmissible theory bindings = true }

def surfaceDocumentGSLT : GSLT :=
  ExactDeclarationCodec.documentGSLT SurfaceSyntax

private def decodeSurfaces? (source : DeclarationDocument SurfaceSyntax) :
    Option (List SurfaceBinding) :=
  source.values.mapM decodeSurface?

private def elaborateSection? (theory : AdmittedTheory)
    (source : DeclarationDocument SurfaceSyntax) :
    Option (AdmittedSection theory) := do
  let bindings ← decodeSurfaces? source
  if admitted : SectionAdmissible theory bindings = true then
    some ⟨bindings, admitted⟩
  else
    none

private def quoteSection (theory : AdmittedTheory)
    (profileSection : AdmittedSection theory) : DeclarationDocument SurfaceSyntax :=
  .bundle ((profileSection.1.map encodeSurface).map
    DeclarationDocument.declaration)

private theorem section_binding_nonempty (theory : AdmittedTheory)
    (profileSection : AdmittedSection theory) (binding : SurfaceBinding)
    (member : binding ∈ profileSection.1) :
    binding.spelling.isEmpty = false := by
  have admitted := profileSection.2
  simp only [SectionAdmissible, Bool.and_eq_true] at admitted
  have supported := List.all_eq_true.mp admitted.2 binding member
  cases value : binding.spelling.isEmpty <;> simp_all

private theorem decodeSurfaces?_map_encode
    (bindings : List SurfaceBinding)
    (nonempty : ∀ binding ∈ bindings,
      binding.spelling.isEmpty = false) :
    List.mapM decodeSurface? (bindings.map encodeSurface) = some bindings := by
  induction bindings with
  | nil => rfl
  | cons binding bindings inductionHypothesis =>
      have headNonempty : binding.spelling.isEmpty = false :=
        nonempty binding (by simp)
      have tailNonempty : ∀ next ∈ bindings,
          next.spelling.isEmpty = false := by
        intro next member
        exact nonempty next (by simp [member])
      simp [decodeSurface?_encodeSurface binding headNonempty,
        inductionHypothesis tailNonempty]

@[simp] private theorem decodeSurfaces?_quoteSection (theory : AdmittedTheory)
    (profileSection : AdmittedSection theory) :
    decodeSurfaces? (quoteSection theory profileSection) =
      some profileSection.1 := by
  rcases profileSection with ⟨bindings, admitted⟩
  unfold decodeSurfaces? quoteSection
  rw [DeclarationDocument.values_bundle_map]
  have nonempty : ∀ binding ∈ bindings,
      binding.spelling.isEmpty = false := by
    intro binding member
    exact section_binding_nonempty theory ⟨bindings, admitted⟩ binding member
  exact decodeSurfaces?_map_encode bindings nonempty

@[simp] private theorem elaborateSection?_quoteSection
    (theory : AdmittedTheory) (profileSection : AdmittedSection theory) :
    elaborateSection? theory (quoteSection theory profileSection) =
      some profileSection := by
  rcases profileSection with ⟨bindings, admitted⟩
  simp [elaborateSection?, decodeSurfaces?_quoteSection, admitted]

/-- Surface elaboration is a dependent coGSLT layer over an already admitted
operation theory.  A section cannot name an unavailable operation. -/
def surfaceLayer : CoGSLTLayer AdmittedTheory where
  Fiber := AdmittedSection
  sourceGSLT := fun _ => surfaceDocumentGSLT
  elaborate := elaborateSection?
  quote := quoteSection
  elaborate_quote := elaborateSection?_quoteSection
  elaborate_equation := by
    intro theory source target equivalent
    change source.values = target.values at equivalent
    unfold elaborateSection? decodeSurfaces?
    rw [equivalent]
  elaborate_rewrite := by
    intro _ _ _ impossible
    exact False.elim impossible

def lookup (theory : AdmittedTheory) (profileSection : AdmittedSection theory)
    (spelling : String) (inputs : List NumSort) : Option CoreOp :=
  (profileSection.1.find? fun binding =>
    binding.key = ⟨spelling, inputs⟩).map
    (fun binding => binding.op)

/-! ## Positive and negative controls -/

private def commonBindings : List SurfaceBinding :=
  [{ spelling := "+", op := .add },
   { spelling := "-", op := .sub },
   { spelling := "*", op := .mul }]

/-- Exact-integer sections measured from the four current dialect profiles.
These are semantic extension declarations, not claims about their text parsers
or their non-integer numeric towers. -/
def heSection : AdmittedSection standardTheory :=
  ⟨commonBindings ++
    [{ spelling := "//", op := .fquot }, { spelling := "%", op := .trem }],
    by decide⟩

def heCompatSection : AdmittedSection standardTheory :=
  ⟨commonBindings ++
    [{ spelling := "/", op := .tquot }, { spelling := "%", op := .trem }],
    by decide⟩

def pettaSection : AdmittedSection standardTheory :=
  ⟨commonBindings ++
    [{ spelling := "//", op := .fquot }, { spelling := "%", op := .frem }],
    by decide⟩

def primeSection : AdmittedSection standardTheory :=
  ⟨commonBindings ++
    [{ spelling := "//", op := .fquot }, { spelling := "%", op := .trem }],
    by decide⟩

example : lookup standardTheory pettaSection "%" [.integer, .integer] =
    some .frem := by decide

example : lookup standardTheory heSection "%" [.integer, .integer] =
    some .trem := by decide

/-- Surface differences remain observable while evaluation still factors
through the one exact-integer semantics. -/
example :
    (lookup standardTheory pettaSection "%" [.integer, .integer]).map
        (fun op => coreSem op (-7) 2) ≠
      (lookup standardTheory heSection "%" [.integer, .integer]).map
        (fun op => coreSem op (-7) 2) := by
  decide

/-- A malformed result sort is rejected by elaboration. -/
example :
    decodeOperation?
      (.operation "exact-int:add" [.integer, .integer] .integer true .add) =
        none := by
  decide

/-- Duplicate semantic operations are rejected from one theory. -/
example :
    TheoryAdmissible [⟨.add⟩, ⟨.add⟩] = false := by
  decide

/-- Ambiguous duplicate surface keys are rejected even when they name
different semantic operations. -/
example :
    SectionAdmissible standardTheory
      [{ spelling := "%", op := .trem }, { spelling := "%", op := .frem }] =
        false := by
  decide

/-- A section cannot bind an operation omitted from its admitted theory. -/
private def additiveTheory : AdmittedTheory :=
  ⟨[{ op := .add }], by decide⟩

example :
    SectionAdmissible additiveTheory [{ spelling := "%", op := .trem }] = false := by
  decide

end ExactInteger

end Mettapedia.GSLT.LanguageDef.ArithmeticExtension
