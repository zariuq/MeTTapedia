import Mettapedia.GSLT.LanguageDef.ContinuedCategory

/-!
# Typed generated namespaces for Cost

The Cost signature is generated from one authored `LanguageDef`.  Its
mathematical namespace is therefore an inductive sum of source names and
fixed apparatus names.  Rendering into the existing string-based
`LanguageDef` is a proved-faithful serialization boundary, not the semantic
definition of a generated name.
-/

namespace Mettapedia.GSLT.LanguageDef

open StructuralMorphism

/-! ## Reserved wire namespaces -/

def costApparatusSortName (name : String) : String :=
  "$cost:apparatus-sort:" ++ name

def costApparatusConstructorName (name : String) : String :=
  "$cost:apparatus-constructor:" ++ name

def costSignatureSortName : String := costApparatusSortName "signature"
def costKeySortName : String := costApparatusSortName "key"
def costTokenStackSortName : String := costApparatusSortName "token-stack"

def costKeyLeafConstructorName : String :=
  costApparatusConstructorName "key-leaf"

def costKeyBranchConstructorName : String :=
  costApparatusConstructorName "key-branch"

def costSignatureCommitConstructorName : String :=
  costApparatusConstructorName "signature-commit"

def costSignatureUnitConstructorName : String :=
  costApparatusConstructorName "signature-unit"

def costSignatureProductConstructorName : String :=
  costApparatusConstructorName "signature-product"

def costSignedConstructorName : String :=
  costApparatusConstructorName "signed"

def costTokenStackEmptyConstructorName : String :=
  costApparatusConstructorName "token-stack-empty"

def costTokenStackConsConstructorName : String :=
  costApparatusConstructorName "token-stack-cons"

def costFundingConstructorName : String :=
  costApparatusConstructorName "funding"

def costContactConstructorName : String :=
  costApparatusConstructorName "contact"

theorem costApparatusSortName_injective :
    Function.Injective costApparatusSortName := by
  intro left right equality
  exact (String.append_right_inj "$cost:apparatus-sort:").mp equality

theorem costApparatusConstructorName_injective :
    Function.Injective costApparatusConstructorName := by
  intro left right equality
  exact (String.append_right_inj "$cost:apparatus-constructor:").mp equality

theorem costBaseSortName_ne_apparatus (base apparatus : String) :
    costBaseSortName base ≠ costApparatusSortName apparatus := by
  intro equality
  change ("$cost:" ++ "base-sort:") ++ base =
    ("$cost:" ++ "apparatus-sort:") ++ apparatus at equality
  rw [String.append_assoc, String.append_assoc] at equality
  have stripped : "base-sort:" ++ base =
      "apparatus-sort:" ++ apparatus :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

theorem costWrappedSortName_ne_apparatus (apparatus : String) :
    costWrappedSortName ≠ costApparatusSortName apparatus := by
  intro equality
  change "$cost:" ++ "wrapped-term" =
    ("$cost:" ++ "apparatus-sort:") ++ apparatus at equality
  rw [String.append_assoc] at equality
  have stripped : "wrapped-term" = "apparatus-sort:" ++ apparatus :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

theorem costBaseConstructorName_ne_apparatus (base apparatus : String) :
    costBaseConstructorName base ≠ costApparatusConstructorName apparatus := by
  intro equality
  change ("$cost:" ++ "base-constructor:") ++ base =
    ("$cost:" ++ "apparatus-constructor:") ++ apparatus at equality
  rw [String.append_assoc, String.append_assoc] at equality
  have stripped : "base-constructor:" ++ base =
      "apparatus-constructor:" ++ apparatus :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

theorem costWrappedConstructorName_ne_apparatus (wrapped apparatus : String) :
    costWrappedConstructorName wrapped ≠
      costApparatusConstructorName apparatus := by
  intro equality
  change ("$cost:" ++ "wrapped-constructor:") ++ wrapped =
    ("$cost:" ++ "apparatus-constructor:") ++ apparatus at equality
  rw [String.append_assoc, String.append_assoc] at equality
  have stripped : "wrapped-constructor:" ++ wrapped =
      "apparatus-constructor:" ++ apparatus :=
    (String.append_right_inj "$cost:").mp equality
  have characters := congrArg String.toList stripped
  simp at characters

/-! ## Intrinsic generated names -/

/-- Exact commitment keys, monoid signatures, and ordered token stacks. -/
inductive CostApparatusSort where
  | signature
  | key
  | tokenStack
deriving DecidableEq, Repr

/-- The fixed apparatus constructors adjoined by Cost. -/
inductive CostApparatusConstructor where
  | signatureUnit
  | signatureProduct
  | keyLeaf
  | keyBranch
  | signatureCommit
  | signed
  | tokenStackEmpty
  | tokenStackCons
  | funding
  | contact
deriving DecidableEq, Repr

/-- A generated Cost sort over an arbitrary source namespace.  Both
`base source` and the fresh `wrapped` carrier are present: selected
continuation positions use the latter while ordinary source occurrences use
the former. -/
inductive CostSort (SourceSort : Type u) where
  | base (source : SourceSort)
  | wrapped
  | apparatus (kind : CostApparatusSort)
deriving DecidableEq, Repr

/-- A generated Cost constructor over an arbitrary source namespace. -/
inductive CostConstructor (SourceConstructor : Type u) where
  | base (source : SourceConstructor)
  | wrapped (source : SourceConstructor)
  | apparatus (kind : CostApparatusConstructor)
deriving DecidableEq, Repr

namespace CostApparatusSort

def suffix : CostApparatusSort → String
  | .signature => "signature"
  | .key => "key"
  | .tokenStack => "token-stack"

def render (kind : CostApparatusSort) : String :=
  costApparatusSortName kind.suffix

theorem suffix_injective : Function.Injective suffix := by
  intro left right equality
  cases left <;> cases right <;> simp_all [suffix]

theorem render_injective : Function.Injective render := by
  intro left right equality
  apply suffix_injective
  exact costApparatusSortName_injective equality

@[simp] theorem render_signature : render .signature = costSignatureSortName :=
  rfl

@[simp] theorem render_key : render .key = costKeySortName := rfl

@[simp] theorem render_tokenStack :
    render .tokenStack = costTokenStackSortName := rfl

end CostApparatusSort

namespace CostApparatusConstructor

def suffix : CostApparatusConstructor → String
  | .signatureUnit => "signature-unit"
  | .signatureProduct => "signature-product"
  | .keyLeaf => "key-leaf"
  | .keyBranch => "key-branch"
  | .signatureCommit => "signature-commit"
  | .signed => "signed"
  | .tokenStackEmpty => "token-stack-empty"
  | .tokenStackCons => "token-stack-cons"
  | .funding => "funding"
  | .contact => "contact"

def render (kind : CostApparatusConstructor) : String :=
  costApparatusConstructorName kind.suffix

theorem suffix_injective : Function.Injective suffix := by
  intro left right equality
  cases left <;> cases right <;> simp_all [suffix]

theorem render_injective : Function.Injective render := by
  intro left right equality
  apply suffix_injective
  exact costApparatusConstructorName_injective equality

@[simp] theorem render_signatureUnit :
    render .signatureUnit = costSignatureUnitConstructorName := rfl

@[simp] theorem render_signatureProduct :
    render .signatureProduct = costSignatureProductConstructorName := rfl

@[simp] theorem render_keyLeaf : render .keyLeaf = costKeyLeafConstructorName := rfl

@[simp] theorem render_keyBranch : render .keyBranch = costKeyBranchConstructorName := rfl

@[simp] theorem render_signatureCommit :
    render .signatureCommit = costSignatureCommitConstructorName := rfl

@[simp] theorem render_signed : render .signed = costSignedConstructorName :=
  rfl

@[simp] theorem render_tokenStackEmpty :
    render .tokenStackEmpty = costTokenStackEmptyConstructorName := rfl

@[simp] theorem render_tokenStackCons :
    render .tokenStackCons = costTokenStackConsConstructorName := rfl

@[simp] theorem render_funding : render .funding = costFundingConstructorName :=
  rfl

@[simp] theorem render_contact : render .contact = costContactConstructorName :=
  rfl

end CostApparatusConstructor

namespace CostSort

/-- Functorial action of Cost-generated sorts on a source namespace map. -/
def map (mapping : SourceSort → TargetSort) :
    CostSort SourceSort → CostSort TargetSort
  | .base source => .base (mapping source)
  | .wrapped => .wrapped
  | .apparatus kind => .apparatus kind

@[simp]
theorem map_id (sort : CostSort SourceSort) : map id sort = sort := by
  cases sort <;> rfl

@[simp]
theorem map_comp (first : SourceSort → MiddleSort)
    (second : MiddleSort → TargetSort) (sort : CostSort SourceSort) :
    map second (map first sort) = map (second ∘ first) sort := by
  cases sort <;> rfl

/-- Faithful rendering of the intrinsic generated sort namespace into the
current `LanguageDef` wire names. -/
def render (renderSource : SourceSort → String) : CostSort SourceSort → String
  | .base source => costBaseSortName (renderSource source)
  | .wrapped => costWrappedSortName
  | .apparatus kind => kind.render

@[simp]
theorem render_map (renderTarget : TargetSort → String)
    (mapping : SourceSort → TargetSort) (sort : CostSort SourceSort) :
    render renderTarget (map mapping sort) =
      render (renderTarget ∘ mapping) sort := by
  cases sort <;> rfl

theorem render_injective (renderSource : SourceSort → String)
    (sourceInjective : Function.Injective renderSource) :
    Function.Injective (render renderSource) := by
  intro left right equality
  cases left with
  | base leftSource =>
      cases right with
      | base rightSource =>
          have renderedSource : renderSource leftSource =
              renderSource rightSource :=
            costBaseSortName_injective equality
          cases sourceInjective renderedSource
          rfl
      | wrapped => exact False.elim (costBaseSortName_ne_wrapped _ equality)
      | apparatus rightKind =>
          exact False.elim
            (costBaseSortName_ne_apparatus _ rightKind.suffix equality)
  | wrapped =>
      cases right with
      | base rightSource =>
          exact False.elim
            (costBaseSortName_ne_wrapped _ equality.symm)
      | wrapped => rfl
      | apparatus rightKind =>
          exact False.elim
            (costWrappedSortName_ne_apparatus rightKind.suffix equality)
  | apparatus leftKind =>
      cases right with
      | base rightSource =>
          exact False.elim
            (costBaseSortName_ne_apparatus _ leftKind.suffix equality.symm)
      | wrapped =>
          exact False.elim
            (costWrappedSortName_ne_apparatus leftKind.suffix equality.symm)
      | apparatus rightKind =>
          have kindEquality : leftKind = rightKind :=
            CostApparatusSort.render_injective equality
          cases kindEquality
          rfl

end CostSort

namespace CostConstructor

/-- Functorial action of Cost-generated constructors on a source namespace
map. -/
def map (mapping : SourceConstructor → TargetConstructor) :
    CostConstructor SourceConstructor → CostConstructor TargetConstructor
  | .base source => .base (mapping source)
  | .wrapped source => .wrapped (mapping source)
  | .apparatus kind => .apparatus kind

@[simp]
theorem map_id (constructor : CostConstructor SourceConstructor) :
    map id constructor = constructor := by
  cases constructor <;> rfl

@[simp]
theorem map_comp (first : SourceConstructor → MiddleConstructor)
    (second : MiddleConstructor → TargetConstructor)
    (constructor : CostConstructor SourceConstructor) :
    map second (map first constructor) =
      map (second ∘ first) constructor := by
  cases constructor <;> rfl

/-- Faithful rendering of the intrinsic generated constructor namespace into
the current `LanguageDef` wire names. -/
def render (renderSource : SourceConstructor → String) :
    CostConstructor SourceConstructor → String
  | .base source => costBaseConstructorName (renderSource source)
  | .wrapped source => costWrappedConstructorName (renderSource source)
  | .apparatus kind => kind.render

@[simp]
theorem render_map (renderTarget : TargetConstructor → String)
    (mapping : SourceConstructor → TargetConstructor)
    (constructor : CostConstructor SourceConstructor) :
    render renderTarget (map mapping constructor) =
      render (renderTarget ∘ mapping) constructor := by
  cases constructor <;> rfl

theorem render_injective (renderSource : SourceConstructor → String)
    (sourceInjective : Function.Injective renderSource) :
    Function.Injective (render renderSource) := by
  intro left right equality
  cases left with
  | base leftSource =>
      cases right with
      | base rightSource =>
          have renderedSource : renderSource leftSource =
              renderSource rightSource :=
            costBaseConstructorName_injective equality
          cases sourceInjective renderedSource
          rfl
      | wrapped rightSource =>
          exact False.elim
            (costBaseConstructorName_ne_wrapped _ _ equality)
      | apparatus rightKind =>
          exact False.elim
            (costBaseConstructorName_ne_apparatus _ rightKind.suffix equality)
  | wrapped leftSource =>
      cases right with
      | base rightSource =>
          exact False.elim
            (costBaseConstructorName_ne_wrapped _ _ equality.symm)
      | wrapped rightSource =>
          have renderedSource : renderSource leftSource =
              renderSource rightSource :=
            costWrappedConstructorName_injective equality
          cases sourceInjective renderedSource
          rfl
      | apparatus rightKind =>
          exact False.elim
            (costWrappedConstructorName_ne_apparatus _ rightKind.suffix equality)
  | apparatus leftKind =>
      cases right with
      | base rightSource =>
          exact False.elim
            (costBaseConstructorName_ne_apparatus _ leftKind.suffix
              equality.symm)
      | wrapped rightSource =>
          exact False.elim
            (costWrappedConstructorName_ne_apparatus _ leftKind.suffix
              equality.symm)
      | apparatus rightKind =>
          have kindEquality : leftKind = rightKind :=
            CostApparatusConstructor.render_injective equality
          cases kindEquality
          rfl

end CostConstructor

namespace CIGSLT

/-- Intrinsic generated sort names for one exact continued presentation. -/
abbrev GeneratedCostSort (source : CIGSLT) :=
  CostSort (StructuralMorphism.DeclaredSort
    source.theory.presentation.presentation)

/-- Intrinsic generated constructor names before restricting the wrapped
summand to the declaration-derived hereditary closure. -/
abbrev GeneratedCostConstructor (source : CIGSLT) :=
  CostConstructor (StructuralMorphism.DeclaredConstructor
    source.theory.presentation.presentation)

/-- Faithful wire rendering of one exact generated Cost sort namespace. -/
def renderGeneratedCostSort (source : CIGSLT) :
    source.GeneratedCostSort → String :=
  CostSort.render (fun sort => sort.1.name)

/-- Faithful wire rendering of one exact generated Cost constructor
namespace. -/
def renderGeneratedCostConstructor (source : CIGSLT) :
    source.GeneratedCostConstructor → String :=
  CostConstructor.render (fun constructor => constructor.1.label)

theorem renderGeneratedCostSort_injective (source : CIGSLT) :
    Function.Injective source.renderGeneratedCostSort :=
  CostSort.render_injective _
    (StructuralMorphism.declaredSortName_injective
      source.theory.presentation.presentation)

theorem renderGeneratedCostConstructor_injective (source : CIGSLT) :
    Function.Injective source.renderGeneratedCostConstructor :=
  CostConstructor.render_injective _
    (ContinuationRetypingPlan.authoredConstructorLabel_injective
      source.theory.presentation.presentation)

/-- Semantic role of one exact generated constructor.  Interaction
principals are kept distinct from static base constructors even though both
live in the base wire namespace.  This is what prevents a region
canonicalizer from treating a reduction principal as static equation
structure. -/
inductive GeneratedCostConstructorRole where
  | static (color : CostStaticColor)
  | interactionPrincipal
  | apparatus (kind : CostApparatusConstructor)
deriving DecidableEq, Repr

end CIGSLT

namespace ContinuationDecorationProfile

variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- Select the actually present wrapped summand of the existing intrinsic
Cost namespace. Base and apparatus declarations are retained in full. -/
def IsDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :
    CostConstructor (DeclaredConstructor theory.presentation.presentation) → Prop
  | .base _ => True
  | .wrapped constructor => constructor ∈ profile.constructorClosure
  | .apparatus _ => True

abbrev DeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :=
  { constructor : CostConstructor (DeclaredConstructor theory.presentation.presentation) //
      profile.IsDeclaredCostConstructor constructor }

def renderDeclaredCostConstructor (profile : ContinuationDecorationProfile cut) :
    profile.DeclaredCostConstructor → String :=
  fun constructor => CostConstructor.render (fun authored => authored.1.label) constructor.1

theorem renderDeclaredCostConstructor_injective (profile : ContinuationDecorationProfile cut) :
    Function.Injective profile.renderDeclaredCostConstructor := by
  intro left right same
  apply Subtype.ext
  exact CostConstructor.render_injective _
    (ContinuationRetypingPlan.authoredConstructorLabel_injective theory.presentation.presentation) same

/-- Role classification is by the exact authored principal declarations,
using the existing role type rather than a second role hierarchy. -/
def declaredCostConstructorRole (profile : ContinuationDecorationProfile cut)
    (constructor : profile.DeclaredCostConstructor) : CIGSLT.GeneratedCostConstructorRole :=
  match constructor.1 with
  | .base authored =>
      if authored = cut.program.constructor ∨ authored = cut.environment.constructor then
        .interactionPrincipal
      else .static .base
  | .wrapped _ => .static .wrapped
  | .apparatus kind => .apparatus kind

end ContinuationDecorationProfile

namespace CIGSLT

open ContinuationDecorationProfile (ofRetypingPlan)

/-- Predicate selecting exactly the intrinsic constructors that are present
in the declaration-derived Cost signature.  Every source declaration has a
base copy; only the hereditary non-principal fragment has a wrapped copy;
and every fixed apparatus constructor is present. -/
abbrev IsDeclaredCostConstructor (source : CIGSLT) :
    source.GeneratedCostConstructor → Prop :=
  (ofRetypingPlan source.continuationRetyping).IsDeclaredCostConstructor

/-- An exact intrinsic constructor of the generated Cost signature.  The
subtype removes the spurious wrapped copies of the two interaction
principals from the unrestricted generated namespace. -/
abbrev DeclaredCostConstructor (source : CIGSLT) :=
  (ofRetypingPlan source.continuationRetyping).DeclaredCostConstructor

/-- Faithful wire rendering of exact declared Cost constructors. -/
def renderDeclaredCostConstructor (source : CIGSLT) :
    source.DeclaredCostConstructor → String :=
  (ofRetypingPlan source.continuationRetyping).renderDeclaredCostConstructor

theorem renderDeclaredCostConstructor_injective (source : CIGSLT) :
    Function.Injective source.renderDeclaredCostConstructor :=
  (ofRetypingPlan source.continuationRetyping).renderDeclaredCostConstructor_injective

/-- Classify a generated constructor by exact declaration identity.  No
string-prefix test participates in this mathematical classification. -/
def declaredCostConstructorRole (source : CIGSLT)
    (constructor : source.DeclaredCostConstructor) :
    GeneratedCostConstructorRole :=
  (ofRetypingPlan source.continuationRetyping).declaredCostConstructorRole constructor

/-- The role of a base copy: an interaction principal or a static base
constructor. -/
theorem declaredCostConstructorRole_base (source : CIGSLT)
    (constructor : DeclaredConstructor
      source.theory.presentation.presentation) :
    source.declaredCostConstructorRole ⟨.base constructor, True.intro⟩ =
      if constructor = source.cut.program.constructor ∨
          constructor = source.cut.environment.constructor then
        .interactionPrincipal
      else
        .static .base :=
  rfl

/-- Declared constructors with different semantic roles have different wire
renderings.  The role hypothesis is essential in the base namespace, where
static constructors and interaction principals share the same string tag. -/
theorem renderDeclaredCostConstructor_ne_of_role_ne (source : CIGSLT)
    {left right : source.DeclaredCostConstructor}
    (different : source.declaredCostConstructorRole left ≠
      source.declaredCostConstructorRole right) :
    source.renderDeclaredCostConstructor left ≠
      source.renderDeclaredCostConstructor right := by
  intro rendered
  exact different (congrArg source.declaredCostConstructorRole
    (source.renderDeclaredCostConstructor_injective rendered))

@[simp]
theorem declaredCostConstructorRole_wrapped (source : CIGSLT)
    (constructor : DeclaredConstructor
      source.theory.presentation.presentation)
    (membership : constructor ∈
      source.continuationRetyping.wrappedConstructors) :
    source.declaredCostConstructorRole
        ⟨.wrapped constructor, membership⟩ = .static .wrapped :=
  rfl

@[simp]
theorem declaredCostConstructorRole_apparatus (source : CIGSLT)
    (kind : CostApparatusConstructor) :
    source.declaredCostConstructorRole
        ⟨.apparatus kind, True.intro⟩ = .apparatus kind :=
  rfl

theorem declaredCostConstructorRole_base_of_nonprincipal (source : CIGSLT)
    (constructor : DeclaredConstructor
      source.theory.presentation.presentation)
    (notProgram : constructor ≠ source.cut.program.constructor)
    (notEnvironment : constructor ≠ source.cut.environment.constructor) :
    source.declaredCostConstructorRole
        ⟨.base constructor, True.intro⟩ = .static .base := by
  simp [declaredCostConstructorRole_base, notProgram, notEnvironment]

theorem declaredCostConstructorRole_base_of_principal (source : CIGSLT)
    (constructor : DeclaredConstructor
      source.theory.presentation.presentation)
    (principal : constructor = source.cut.program.constructor ∨
      constructor = source.cut.environment.constructor) :
    source.declaredCostConstructorRole
        ⟨.base constructor, True.intro⟩ = .interactionPrincipal := by
  simp [declaredCostConstructorRole_base, principal]

end CIGSLT

end Mettapedia.GSLT.LanguageDef
