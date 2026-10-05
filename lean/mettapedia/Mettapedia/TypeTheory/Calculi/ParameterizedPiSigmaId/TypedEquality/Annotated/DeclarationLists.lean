import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ExplicitDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationForms

/-!
# Lists of declarations: datatypes and definitions

A program is a sequence of declarations that use each other: datatypes, functions defined on
them, and further datatypes and functions over those. This module builds a package from such
a list and states when the list is admissible.

**A declaration** (`Declaration`) is

* a datatype (`Datatype`): its type, its constructors and its recursor (`withInductive`).
  A parameter telescope (`Parameterization`) may stand in front of them; the empty
  parameterization is the simple inductive, or
* a definition (`Definition`), of one of two kinds:
  * by structural recursion (`RecursiveDefinition`): a constant whose first argument is of a
    datatype and which computes by one written equation for each constructor, with its later
    arguments on the left (`laterEquations`);
  * explicit (`ExplicitDefinition`): a constant that computes by one equation over its
    arguments, without recursion (`explicitEquation`).

A definition of either kind is a name, a type and a list of equations (`Definition.name`,
`Definition.type`, `Definition.equations`), and extends a package by `withDefinition`.

**A list of declarations** (`withDeclarations`) extends a package one declaration after the
other; the head of the list is the declaration added last.

**Admissibility** is what a declaration checker verifies. A datatype is admissible over a
package (`Datatype.Admissible`) when its two universes are universes, its names are distinct
and new, and its closed field types have no abstraction and are types of the datatype's
universe in that package. A definition by recursion is admissible over a package
(`RecursiveDefinition.Admissible`) when its name is new, its declared type is a type, its
result family is a type over the inspected argument, and each right side is typed in the
context of its constructor's fields, of one hypothesis for each recursive field, and of the
later arguments. An explicit definition is admissible (`ExplicitDefinition.Admissible`) when
its name is new, the context of its arguments is formed, its result type is a type there and
its body has it. A list is admissible (`AdmissibleDeclarations`) when each declaration is
admissible over the package with the declarations before it, and each definition by recursion
recurses on a datatype declared before it.

For an admissible list, every declaration has its rules in the package of the whole list, at
arguments typed there:

* a datatype's type, constructors and recursor are typed (`AdmissibleDeclarations.type_typed`,
  `ctor_typed`, `ctor_spine_typed`, `rec_typed`, `rec_applied`) and its computation rules hold
  (`AdmissibleDeclarations.iota_holds`);
* a defined constant has its declared type (`AdmissibleDeclarations.definition_typed`) and
  its written equations hold at typed instances (`definition_equation_holds`).

Derivations of the base package and of every earlier stage persist
(`CDerivable.withDeclarations`, `withDeclarations_sub`). A later list extends an earlier one
(`Extends`) when its package contains the earlier package and it has every earlier
declaration; a list extends every list it ends with (`Extends.after`). A definition by
recursion admissible over a package is admissible over every larger package that does not
declare its name (`RecursiveDefinition.Admissible.mono`).

Positive examples: the empty list is admissible, and its package is the base package; an
explicit definition admissible over the base package is an admissible list of one declaration
(`admissible_explicit`). Negative examples: a list that declares the same datatype twice is
not admissible, because the second declaration's names are not new (`not_admissible_twice`);
neither is a list that defines the same constant twice (`not_admissible_defined_twice`), nor
a definition by recursion without the datatype it recurses on before it
(`not_admissible_without_datatype`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization
open TelescopeAbstraction (closeType)
open UniverseLevel (LevelOrder)

variable {Head : Type}

/-! ## Declarations -/

/-- A field of a constructor in a parameter context of length `p`. `uniform` is the datatype
applied to exactly those parameters. `plain` is a type in that context that does not mention
the datatype. -/
inductive OpenField (Head : Type) : Nat → Type where
  | uniform {p : Nat} : OpenField Head p
  | plain {p : Nat} (type : Tm Head p) : OpenField Head p

/-- A parameter telescope, outermost entry first. -/
structure ParameterTelescope (Head : Type) where
  count : Nat
  context : Ctx Head count

/-- Constructors whose fields may mention the parameters. The empty telescope with no
constructors here is the simple datatype, whose constructors are `Datatype.ctors`. -/
structure Parameterization (Head : Type) where
  telescope : ParameterTelescope Head
  constructors : List (DeclName × List (OpenField Head telescope.count))

/-- No parameters, and no open constructors. -/
def Parameterization.none : Parameterization Head where
  telescope := ⟨0, .nil⟩
  constructors := []

/-- **A datatype**: a type, its universe, constructors with their fields, and a recursor
with the universe of its motives. `parameters` is a parameter telescope. The empty
parameterization is the simple datatype. -/
structure Datatype (Head : Type) where
  type : DeclName
  typeUniverse : Head
  ctors : List (DeclName × List (Field Head))
  recursor : DeclName
  motiveUniverse : Head
  parameters : Parameterization Head := .none

/-- **A definition by structural recursion on a datatype**: the defined constant, the
datatype of its first argument, the telescope of its later arguments over that argument
(ending at `width` variables), the result type over all of them, and for each constructor the
right side over the fields, one hypothesis for each recursive field, and the later
arguments. -/
structure RecursiveDefinition (Head : Type) where
  name : DeclName
  datatype : Datatype Head
  width : Nat
  later : CTele Head 1 width
  result : CTm Head width
  body : (k : DeclName) → (fields : List (Field Head)) →
    CTm Head (later.endAt (fields.length + (recPositions fields).length))

/-- The declared type of the defined constant: a function of the inspected argument and the
later arguments. -/
abbrev RecursiveDefinition.type (δ : RecursiveDefinition Head) : CTm Head 0 :=
  .pi (.const δ.datatype.type) (δ.later.pis δ.result)

/-- The written equations of the definition, one for each constructor of its datatype. -/
abbrev RecursiveDefinition.equations (δ : RecursiveDefinition Head) :
    List (DefiningEquation Head) :=
  laterEquations δ.name δ.datatype.type δ.later δ.datatype.ctors δ.body

/-- **An explicit definition**: the defined constant, the telescope of its arguments (ending
at `width` variables), the result type over them, and the body over them. -/
structure ExplicitDefinition (Head : Type) where
  name : DeclName
  width : Nat
  arguments : CTele Head 0 width
  result : CTm Head width
  body : CTm Head width

/-- The declared type of the defined constant: a function of the arguments. -/
abbrev ExplicitDefinition.type (ε : ExplicitDefinition Head) : CTm Head 0 :=
  ε.arguments.pis ε.result

/-- The one equation of the definition. -/
abbrev ExplicitDefinition.equations (ε : ExplicitDefinition Head) :
    List (DefiningEquation Head) :=
  [explicitEquation ε.name ε.arguments ε.body]

/-- **A definition**: by structural recursion, or explicit. -/
inductive Definition (Head : Type) where
  | recursive (δ : RecursiveDefinition Head)
  | explicit (ε : ExplicitDefinition Head)

/-- The defined constant. -/
def Definition.name : Definition Head → DeclName
  | .recursive δ => δ.name
  | .explicit ε => ε.name

/-- The declared type of the defined constant. -/
def Definition.type : Definition Head → CTm Head 0
  | .recursive δ => δ.type
  | .explicit ε => ε.type

/-- The equations by which the defined constant computes. -/
def Definition.equations : Definition Head → List (DefiningEquation Head)
  | .recursive δ => δ.equations
  | .explicit ε => ε.equations

/-- **A declaration**: a datatype, or a definition. -/
inductive Declaration (Head : Type) where
  | datatype (d : Datatype Head)
  | definition (D : Definition Head)

/-! ## The package of a list of declarations -/

/-- The rules of a package with a list of declarations. The head of the list is the
declaration added last. -/
def rulesWith (R : Rules Head) : List (Declaration Head) → Rules Head
  | [] => R
  | .datatype d :: ds => Rules.sum (rulesWith R ds)
      (inductiveRules (rulesWith R ds) d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse)
  | .definition D :: ds => Rules.sum (rulesWith R ds)
      (definedRules (rulesWith R ds) D.name D.type D.equations)

variable {R : Rules Head}

/-- The universe rules of a package with declarations are those of the package. -/
theorem rulesWith_isUniverse (u : Head) :
    ∀ ds : List (Declaration Head), (rulesWith R ds).isUniverse u = R.isUniverse u
  | [] => rfl
  | .datatype _ :: ds => rulesWith_isUniverse u ds
  | .definition _ :: ds => rulesWith_isUniverse u ds

/-- **A package with a list of declarations**: each declaration extends the package with the
declarations before it. -/
def withDeclarations (B : ChurchRules R) :
    (ds : List (Declaration Head)) → ChurchRules (rulesWith R ds)
  | [] => B
  | .datatype d :: ds =>
      withInductive (withDeclarations B ds) d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse
  | .definition D :: ds => withDefinition (withDeclarations B ds) D.name D.type D.equations

/-- A level model of a package is one of the package with declarations. -/
def levelsWith {L : Type} [LevelOrder L] (levels : LevelModel R L) :
    (ds : List (Declaration Head)) → LevelModel (rulesWith R ds) L
  | [] => levels
  | .datatype d :: ds => LevelModel.sum (levelsWith levels ds)
      (inductiveRules (rulesWith R ds) d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse)
  | .definition D :: ds => LevelModel.sum (levelsWith levels ds)
      (definedRules (rulesWith R ds) D.name D.type D.equations)

/-- **The package with some declarations is contained in the package with more.** -/
theorem withDeclarations_sub (B : ChurchRules R) (post : List (Declaration Head)) :
    ∀ pre : List (Declaration Head),
      ChurchRulesSub (withDeclarations B post) (withDeclarations B (pre ++ post))
  | [] => ChurchRulesSub.refl _
  | .datatype _ :: pre => (withDeclarations_sub B post pre).trans (ChurchRulesSub.sum_left _ _)
  | .definition _ :: pre => (withDeclarations_sub B post pre).trans (ChurchRulesSub.sum_left _ _)

/-- The base package is contained in the package with declarations. -/
theorem withDeclarations_base (B : ChurchRules R) :
    ∀ ds : List (Declaration Head), ChurchRulesSub B (withDeclarations B ds)
  | [] => ChurchRulesSub.refl _
  | .datatype _ :: ds => (withDeclarations_base B ds).trans (ChurchRulesSub.sum_left _ _)
  | .definition _ :: ds => (withDeclarations_base B ds).trans (ChurchRulesSub.sum_left _ _)

/-- **Every derivation of the base package is one of the package with declarations.** -/
theorem CDerivable.withDeclarations {B : ChurchRules R} (ds : List (Declaration Head))
    {s : CStatement Head} (derivation : CDerivable B s) : CDerivable (withDeclarations B ds) s :=
  derivation.mono (withDeclarations_base B ds)

/-- **A later list of declarations**: the package of `post` is contained in that of `ds`, and
`ds` has every declaration of `post`. -/
structure Extends (B : ChurchRules R) (post ds : List (Declaration Head)) : Prop where
  sub : ChurchRulesSub (withDeclarations B post) (withDeclarations B ds)
  mem : ∀ {D : Declaration Head}, D ∈ post → D ∈ ds

theorem Extends.after {B : ChurchRules R} (pre post : List (Declaration Head)) :
    Extends B post (pre ++ post) :=
  ⟨withDeclarations_sub B post pre, fun member => List.mem_append_right pre member⟩

theorem Extends.refl {B : ChurchRules R} (ds : List (Declaration Head)) : Extends B ds ds :=
  ⟨ChurchRulesSub.refl _, id⟩

theorem Extends.trans {B : ChurchRules R} {a b c : List (Declaration Head)}
    (first : Extends B a b) (second : Extends B b c) : Extends B a c :=
  ⟨first.sub.trans second.sub, fun member => second.mem (first.mem member)⟩

/-- The computation steps of a datatype of a list are steps of the package of the list, with
the same premises. -/
theorem datatype_stepsWithin (B : ChurchRules R) (d : Datatype Head)
    (post : List (Declaration Head)) :
    ∀ pre : List (Declaration Head),
      StepsWithin
        (inductiveChurch (rulesWith R post) d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse)
        (withDeclarations B (pre ++ .datatype d :: post))
  | [] => StepsWithin.sum_right _ _
  | .datatype _ :: pre => (datatype_stepsWithin B d post pre).trans (StepsWithin.sum_left _ _)
  | .definition _ :: pre => (datatype_stepsWithin B d post pre).trans (StepsWithin.sum_left _ _)

/-- The computation steps of a definition of a list are steps of the package of the list,
with the same premises. -/
theorem definition_stepsWithin (B : ChurchRules R) (D : Definition Head)
    (post : List (Declaration Head)) :
    ∀ pre : List (Declaration Head),
      StepsWithin (definedChurch (rulesWith R post) D.name D.type D.equations)
        (withDeclarations B (pre ++ .definition D :: post))
  | [] => StepsWithin.sum_right _ _
  | .datatype _ :: pre => (definition_stepsWithin B D post pre).trans (StepsWithin.sum_left _ _)
  | .definition _ :: pre => (definition_stepsWithin B D post pre).trans (StepsWithin.sum_left _ _)

/-! ## Admissible declarations -/

/-- **A datatype is admissible over a package**: its two universes are universes, its names
are distinct and new to the package, and its closed field types have no abstraction and are
types of the datatype's universe in the package. -/
structure Datatype.Admissible (B : ChurchRules R) (d : Datatype Head) : Prop where
  typeUniverse : R.isUniverse d.typeUniverse
  motiveUniverse : R.isUniverse d.motiveUniverse
  distinct : DistinctNames d.type d.ctors d.recursor
  new : NewNames B d.type d.ctors d.recursor
  lamFree : FieldsLamFree d.ctors
  fields : ∀ entry ∈ d.ctors, ∀ F, (.closed F : Field Head) ∈ entry.2 →
    CTyped B .nil (liftTm F) (.head d.typeUniverse)

/-- The closed field types of an admissible datatype are types of the package. -/
theorem Datatype.Admissible.fieldsFormed {B : ChurchRules R} {d : Datatype Head}
    (admissible : d.Admissible B) : FieldsFormed B d.ctors :=
  fun entry member F field =>
    ⟨d.typeUniverse, admissible.typeUniverse, admissible.fields entry member F field⟩

/-- **A definition by structural recursion is admissible over a package**: its name is new,
its declared type is a type, its result family is a type over the inspected argument, and for
each constructor of its datatype the context of the right side is formed, the result type is
a type there, and the right side has it. -/
structure RecursiveDefinition.Admissible (B : ChurchRules R) (δ : RecursiveDefinition Head) :
    Prop where
  new : B.constantType δ.name = none
  typeFormed : CIsType B .nil δ.type
  family : CIsType B (.snoc .nil (.const δ.datatype.type)) (δ.later.pis δ.result)
  formed : ∀ {i : Nat} {k : DeclName} {fields : List (Field Head)},
    δ.datatype.ctors[i]? = some (k, fields) →
      CCtxFormed B (laterCtx δ.datatype.type δ.later δ.result k fields)
  resultType : ∀ {i : Nat} {k : DeclName} {fields : List (Field Head)},
    δ.datatype.ctors[i]? = some (k, fields) →
      CIsType B (laterCtx δ.datatype.type δ.later δ.result k fields)
        (laterResult δ.later δ.result k fields)
  bodies : ∀ {i : Nat} {k : DeclName} {fields : List (Field Head)},
    δ.datatype.ctors[i]? = some (k, fields) →
      CTyped B (laterCtx δ.datatype.type δ.later δ.result k fields) (δ.body k fields)
        (laterResult δ.later δ.result k fields)

/-- A definition by recursion admissible over a package is admissible over every package that
contains it and does not declare its name. -/
theorem RecursiveDefinition.Admissible.mono {R' : Rules Head} {Q : ChurchRules R}
    {P : ChurchRules R'} (sub : ChurchRulesSub Q P) {δ : RecursiveDefinition Head}
    (new : P.constantType δ.name = none) (admissible : δ.Admissible Q) : δ.Admissible P where
  new := new
  typeFormed :=
    let ⟨w, hw, typed⟩ := admissible.typeFormed
    ⟨w, sub.isUniverse hw, typed.mono sub⟩
  family :=
    let ⟨w, hw, typed⟩ := admissible.family
    ⟨w, sub.isUniverse hw, typed.mono sub⟩
  formed := fun entry => CCtxFormed.mono sub (admissible.formed entry)
  resultType := fun entry =>
    let ⟨w, hw, typed⟩ := admissible.resultType entry
    ⟨w, sub.isUniverse hw, typed.mono sub⟩
  bodies := fun entry => (admissible.bodies entry).mono sub

/-- **An explicit definition is admissible over a package**: its name is new, the context of
its arguments is formed, its result type is a type there, and its body has it. -/
structure ExplicitDefinition.Admissible (B : ChurchRules R) (ε : ExplicitDefinition Head) :
    Prop where
  new : B.constantType ε.name = none
  formed : CCtxFormed B (ε.arguments.extend .nil)
  resultType : CIsType B (ε.arguments.extend .nil) ε.result
  body : CTyped B (ε.arguments.extend .nil) ε.body ε.result

/-- **A definition is admissible over a package, after a list of declarations**: by
recursion, when its datatype is among the declarations and it is admissible over the package;
explicit, when it is admissible over the package. -/
def Definition.Admissible (B : ChurchRules R) (ds : List (Declaration Head)) :
    Definition Head → Prop
  | .recursive δ => Declaration.datatype δ.datatype ∈ ds ∧ δ.Admissible B
  | .explicit ε => ε.Admissible B

/-- The name of an admissible definition is new to the package. -/
theorem Definition.Admissible.new {B : ChurchRules R} {ds : List (Declaration Head)} :
    ∀ {D : Definition Head}, D.Admissible B ds → B.constantType D.name = none
  | .recursive _, admissible => admissible.2.new
  | .explicit _, admissible => ExplicitDefinition.Admissible.new admissible

/-- The declared type of an admissible definition is a type of the package. -/
theorem Definition.Admissible.typeFormed {L : Type} [LevelOrder L] (levels : LevelModel R L)
    {B : ChurchRules R} {ds : List (Declaration Head)} :
    ∀ {D : Definition Head}, D.Admissible B ds → CIsType B .nil D.type
  | .recursive _, admissible => admissible.2.typeFormed
  | .explicit _, admissible => explicitType_formed levels admissible.formed admissible.resultType

/-- **A list of declarations is admissible over a package**: each declaration is admissible
over the package with the declarations before it, and each definition by recursion recurses
on a datatype declared before it. -/
def AdmissibleDeclarations (B : ChurchRules R) : List (Declaration Head) → Prop
  | [] => True
  | .datatype d :: ds => AdmissibleDeclarations B ds ∧ d.Admissible (withDeclarations B ds)
  | .definition D :: ds => AdmissibleDeclarations B ds ∧ D.Admissible (withDeclarations B ds) ds

/-- The declarations before the last one of an admissible list are admissible. -/
theorem AdmissibleDeclarations.tail {B : ChurchRules R} {e : Declaration Head}
    {ds : List (Declaration Head)} (admissible : AdmissibleDeclarations B (e :: ds)) :
    AdmissibleDeclarations B ds := by
  cases e with
  | datatype d => exact admissible.1
  | definition D => exact admissible.1

/-- An initial part of an admissible list (the declarations made first) is admissible. -/
theorem AdmissibleDeclarations.after {B : ChurchRules R} {post : List (Declaration Head)} :
    ∀ {pre : List (Declaration Head)}, AdmissibleDeclarations B (pre ++ post) →
      AdmissibleDeclarations B post
  | [], admissible => admissible
  | _ :: pre, admissible => AdmissibleDeclarations.after (pre := pre) admissible.tail

/-- The declarations before a datatype of an admissible list are admissible, and the datatype
is admissible over the package with them. -/
theorem AdmissibleDeclarations.datatype_split {B : ChurchRules R} {d : Datatype Head}
    {pre post : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B (pre ++ .datatype d :: post)) :
    AdmissibleDeclarations B post ∧ d.Admissible (withDeclarations B post) :=
  admissible.after

/-- The declarations before a definition of an admissible list are admissible, and the
definition is admissible over the package with them, after them. -/
theorem AdmissibleDeclarations.definition_split {B : ChurchRules R}
    {D : Definition Head} {pre post : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B (pre ++ .definition D :: post)) :
    AdmissibleDeclarations B post ∧ D.Admissible (withDeclarations B post) post :=
  admissible.after

/-- The universe of the type of a datatype of an admissible list is a universe of the base
package. -/
theorem AdmissibleDeclarations.typeUniverse {B : ChurchRules R} {ds : List (Declaration Head)}
    {d : Datatype Head} (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) : R.isUniverse d.typeUniverse := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2.typeUniverse
  rwa [rulesWith_isUniverse] at stage

/-- The closed field types of a datatype of an admissible list are types of the package of
the list. -/
theorem AdmissibleDeclarations.fieldsFormed {B : ChurchRules R} {ds : List (Declaration Head)}
    {d : Datatype Head} (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) : FieldsFormed (withDeclarations B ds) d.ctors := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  intro entry memberEntry F field
  have sub := (withDeclarations_sub B post [.datatype d]).trans
    (withDeclarations_sub B (.datatype d :: post) pre)
  exact ⟨d.typeUniverse, sub.isUniverse stage.typeUniverse,
    CDerivable.mono sub (stage.fields entry memberEntry F field)⟩

/-- The type of a datatype of an admissible list is declared in the package of the list. -/
theorem AdmissibleDeclarations.type_declared {B : ChurchRules R} {ds : List (Declaration Head)}
    {d : Datatype Head} (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) :
    (withDeclarations B ds).constantType d.type = some (.head d.typeUniverse) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  exact (withDeclarations_sub B (.datatype d :: post) pre).constantType
    (sum_type_declared (withDeclarations B post) stage.new)

/-- The constant of a definition of an admissible list is declared at its type in the package
of the list. -/
theorem AdmissibleDeclarations.definition_declared {B : ChurchRules R}
    {ds : List (Declaration Head)} {D : Definition Head}
    (admissible : AdmissibleDeclarations B ds) (member : Declaration.definition D ∈ ds) :
    (withDeclarations B ds).constantType D.name = some D.type := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.definition_split.2
  exact (withDeclarations_sub B (.definition D :: post) pre).constantType
    (withDefinition_defined (withDeclarations B post) stage.new)

/-! ## The rules of a datatype of the list, in the package of the list -/

section Datatypes

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) {B : ChurchRules R}
  {ds : List (Declaration Head)} {d : Datatype Head}

include levels in
/-- **The type of a datatype of an admissible list** is a type of its universe in the package
of the list. -/
theorem AdmissibleDeclarations.type_typed (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) {n : Nat} {Γ : CCtx Head n} :
    CTyped (withDeclarations B ds) Γ (.const d.type) (.head d.typeUniverse) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  exact CDerivable.mono (withDeclarations_sub B (.datatype d :: post) pre)
    (Annotated.type_typed (levelsWith levels post) (withDeclarations B post) stage.typeUniverse
      stage.new)

include levels in
/-- **A constructor of a datatype of an admissible list** has its declared type in the
package of the list. -/
theorem AdmissibleDeclarations.ctor_typed (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) {i : Nat} {k : DeclName}
    {fields : List (Field Head)} (entry : d.ctors[i]? = some (k, fields)) {n : Nat}
    {Γ : CCtx Head n} :
    CTyped (withDeclarations B ds) Γ (.const k) (liftTm (ctorType d.type fields)).liftClosed := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  exact CDerivable.mono (withDeclarations_sub B (.datatype d :: post) pre)
    (Annotated.ctor_typed (levelsWith levels post) (withDeclarations B post) stage.typeUniverse
      stage.distinct stage.lamFree stage.new stage.fieldsFormed entry)

include levels in
/-- **A constructor applied to listed terms of the types of its fields**, typed in the
package of the list, is a term of the declared type. -/
theorem AdmissibleDeclarations.ctor_spine_typed (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) {i : Nat} {k : DeclName}
    {fields : List (Field Head)} (entry : d.ctors[i]? = some (k, fields)) {n : Nat}
    {Γ : CCtx Head n} {xs : List (Tm Head n)}
    (typed : List.Forall₂ (fun x (field : Field Head) =>
      CTyped (withDeclarations B ds) Γ (liftTm x) (liftTm (field.type d.type)).liftClosed)
      xs fields) :
    CTyped (withDeclarations B ds) Γ (liftTm (appSpine (.const k) xs)) (.const d.type) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  exact ctor_spine_typed_within (levelsWith levels post) (withDeclarations B post)
    (withDeclarations_sub B (.datatype d :: post) pre) stage.typeUniverse stage.distinct
    stage.lamFree stage.new stage.fieldsFormed entry typed

include levels in
/-- **The recursor of a datatype of an admissible list** has its declared type in the package
of the list. -/
theorem AdmissibleDeclarations.rec_typed (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) {n : Nat} {Γ : CCtx Head n} :
    CTyped (withDeclarations B ds) Γ (.const d.recursor)
      (liftTm (recType d.type d.motiveUniverse d.ctors)).liftClosed := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  exact CDerivable.mono (withDeclarations_sub B (.datatype d :: post) pre)
    (Annotated.rec_typed (levelsWith levels post) (withDeclarations B post) stage.typeUniverse
      stage.motiveUniverse stage.distinct stage.lamFree stage.new stage.fieldsFormed)

include levels in
/-- **The typing rule of the recursor of a datatype of an admissible list**: applied to a
motive, a method for each constructor and a term of the declared type, all typed in the
package of the list, it has the motive's type at that term. -/
theorem AdmissibleDeclarations.rec_applied (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) {n : Nat} {Γ : CCtx Head n}
    {σ : CSub Head (d.ctors.length + 2) n}
    (typed : CSubstMor (withDeclarations B ds)
      (liftCtx (recTele d.type d.motiveUniverse d.ctors)) Γ σ) :
    CTyped (withDeclarations B ds) Γ (applyAlong σ (.const d.recursor))
      (.app (σ (Fin.last (d.ctors.length + 1))) (σ 0)) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  exact rec_applied_within (levelsWith levels post) (withDeclarations B post)
    (withDeclarations_sub B (.datatype d :: post) pre) stage.typeUniverse stage.motiveUniverse
    stage.distinct stage.lamFree stage.new stage.fieldsFormed typed

include levels in
/-- **The computation rules of the recursor of a datatype of an admissible list** hold in the
package of the list, at arguments typed there. -/
theorem AdmissibleDeclarations.iota_holds (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) {i : Nat} {k : DeclName}
    {fields : List (Field Head)} (entry : d.ctors[i]? = some (k, fields)) {n : Nat}
    {Γ : CCtx Head n} (σ : CSub Head (1 + d.ctors.length + fields.length) n)
    (typed : CSubstMor (withDeclarations B ds)
      (liftCtx (iotaTele d.type d.motiveUniverse d.ctors fields)) Γ σ) :
    CEqual (withDeclarations B ds) Γ
      ((liftTm (iotaLeft d.recursor k d.ctors.length fields.length)).subst σ)
      ((liftTm (iotaRight d.recursor d.ctors.length i fields)).subst σ)
      ((liftTm (iotaTarget k d.ctors.length fields.length)).subst σ) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  exact iota_holds_within (levelsWith levels post) (withDeclarations B post)
    (withDeclarations_sub B (.datatype d :: post) pre) (datatype_stepsWithin B d post pre)
    stage.typeUniverse stage.motiveUniverse stage.distinct stage.lamFree stage.new
    stage.fieldsFormed entry σ typed

end Datatypes

/-! ## The rules of a definition of the list, in the package of the list -/

section Definitions

variable {L : Type} [LevelOrder L] (levels : LevelModel R L) {B : ChurchRules R}
  {ds : List (Declaration Head)} {D : Definition Head}

include levels in
/-- **The constant of a definition of an admissible list** has its declared type in the
package of the list. -/
theorem AdmissibleDeclarations.definition_typed (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.definition D ∈ ds) {n : Nat} {Γ : CCtx Head n} :
    CTyped (withDeclarations B ds) Γ (.const D.name) D.type.liftClosed := by
  have declared := admissible.definition_declared member
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  obtain ⟨u, isUniverse, formed⟩ :=
    admissible.definition_split.2.typeFormed (levelsWith levels post)
  have sub := (withDeclarations_sub B post [.definition D]).trans
    (withDeclarations_sub B (.definition D :: post) pre)
  exact Annotated.definition_typed declared (CDerivable.mono sub formed)
    (sub.isUniverse isUniverse)

/-- **The written equations of a definition of a list hold at their typed instances**, in the
package of the list: an instance of an equation at a substitution typed along the equation's
telescope is an equality at every type both sides have. -/
theorem definition_equation_holds (member : Declaration.definition D ∈ ds)
    {e : DefiningEquation Head} (equation : e ∈ D.equations) {n : Nat} {Γ : CCtx Head n}
    (σ : CSub Head e.arity n) (typed : CSubstMor (withDeclarations B ds) e.telescope Γ σ)
    {C : CTm Head n} (left : CTyped (withDeclarations B ds) Γ (e.left.subst σ) C)
    (right : CTyped (withDeclarations B ds) Γ (e.right.subst σ) C) :
    CEqual (withDeclarations B ds) Γ (e.left.subst σ) (e.right.subst σ) C := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  exact equation_holds _ (definition_stepsWithin B D post pre) equation σ typed left right

end Definitions

/-! ## Examples -/

/-- Positive example: the empty list is admissible over every package, and its package is the
package itself. -/
theorem admissible_nil (B : ChurchRules R) : AdmissibleDeclarations B [] := trivial

/-- Negative example: a list that declares the same datatype twice is not admissible, because
the names of the second declaration are not new. -/
theorem not_admissible_twice {B : ChurchRules R} (d : Datatype Head) :
    ¬ AdmissibleDeclarations B [.datatype d, .datatype d] := by
  rintro ⟨⟨-, first⟩, second⟩
  have declared : (withDeclarations B [.datatype d]).constantType d.type =
      some (.head d.typeUniverse) := sum_type_declared B first.new
  have new : (withDeclarations B [.datatype d]).constantType d.type = none := second.new.typeNew
  rw [declared] at new
  exact nomatch new

/-- Negative example: a list that defines the same constant twice is not admissible, because
the name of the second definition is not new. -/
theorem not_admissible_defined_twice {B : ChurchRules R} (D : Definition Head)
    (ds : List (Declaration Head)) :
    ¬ AdmissibleDeclarations B (.definition D :: .definition D :: ds) := by
  rintro ⟨⟨-, first⟩, second⟩
  have declared : (withDeclarations B (.definition D :: ds)).constantType D.name = some D.type :=
    withDefinition_defined (withDeclarations B ds) first.new
  have new : (withDeclarations B (.definition D :: ds)).constantType D.name = none := second.new
  rw [declared] at new
  exact nomatch new

/-- Negative example: a definition by recursion is not admissible without the datatype it
recurses on before it. -/
theorem not_admissible_without_datatype {B : ChurchRules R} (δ : RecursiveDefinition Head) :
    ¬ AdmissibleDeclarations B [.definition (.recursive δ)] :=
  fun admissible => nomatch admissible.2.1

/-- Positive example: an explicit definition admissible over a package is an admissible list
of one declaration; it needs no datatype. -/
theorem admissible_explicit {B : ChurchRules R} {ε : ExplicitDefinition Head}
    (admissible : ε.Admissible B) : AdmissibleDeclarations B [.definition (.explicit ε)] :=
  ⟨trivial, admissible⟩

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
