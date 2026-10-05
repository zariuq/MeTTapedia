import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetExplicitDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationLists

/-!
# A package with an admissible list of declarations has a set model

A program is a list of declarations that use each other: datatypes, functions defined by
structural recursion on them, and explicit definitions (`Declaration`, `withDeclarations`).
`SetInductive.lean` reads one datatype over a base assignment, `SetLaterArguments.lean` reads
one definition by recursion as the recursion's value, and `SetExplicitDefinitions.lean` reads
one explicit definition as the value of its body abstracted over its arguments
(`definitionValue`). This module repeats the steps along an admissible list
(`AdmissibleDeclarations`).

What makes the steps repeatable is that a model reads only the names its package declares. The
base package has a set model at every assignment that agrees with a given one on the names it
declares (for the object package of the MeTTa candidate this is `objectSetModel_agreeing`).
The package with an admissible list of declarations then has a set model at every assignment
that agrees, on the names *it* declares, with the assignment that reads the declarations one
after the other (`declarationsConsts`): `declarations_setModel`. The hypotheses are the
admissibility of the list, which a declaration checker verifies, and that the universe of each
datatype is read as a closed set that holds the natural numbers.

At a datatype (`admissible_setModel`), its closed field types are typed in the package before
it, so their values read only the names declared before (`CDerivable.ev_congr_declared`) and
lie in the set of the datatype's universe (soundness of the package before it). At a
definition by recursion, the datatype it recurses on was declared before it and is read there
(`declarations_reading`), and the right sides are typed in the package before it
(`laterArguments_setModel`); at an explicit definition the body is typed in the package before
it (`explicit_setModel`). Each datatype of the list is read at every assignment that agrees
on the declared names: its type is the carrier of its signature, its constructors and its
recursor are the graphs of their values. A constructor is read by its name, and the
constructor names of a datatype of an admissible list are distinct (`declarations_ctorsNodup`),
which the recursion on it needs.

Consequences: every derivable statement holds in the model (`declarations_sound`), and a
closed type with an empty set has no closed term (`declarations_no_closed_inhabitant`). The
assignment that reads an admissible list keeps the values of the names the base package
declares (`declarationsConsts_base`), and the assignment that reads a longer admissible list
keeps the values of the names declared before (`declarationsConsts_after`).

**A typed data term means its set** (`declarations_dataTerm_value`). A data term over the
datatypes of the list (`DataOver`: each name is a constructor of a datatype of the list, with
as many arguments as fields, and the closed fields of that constructor are datatypes of the
list) whose term has the type of a datatype of the list has, in the model, the set of the data
term as its value: the constructor value of the code of its name at the sets of its arguments.

Positive example: the empty list, whose model is the base package's
(`declarations_setModel_nil`). Negative examples: a datatype whose field type the package
before it does not type is not admissible, and neither is a definition before the datatype it
recurses on; over the object package these are shown in `ObjectDatatypes.lean` and
`ObjectPrograms.lean`, in the executable model of the candidate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Normalization (LevelModel)
open Mettapedia.Logic.HOL.Embedding
open UniverseLevel (LevelOrder)

universe u

local notation "DeclField" => TypedEquality.Normalization.Field

variable {Head : Type} (heads : Head → ZFSet.{u})

/-- **The value of a defined constant over an assignment**: by recursion, the value of the
recursion at the right sides abstracted over the later arguments; explicit, the value of the
body abstracted over the arguments. -/
noncomputable def definitionValue (prev : DeclName → ZFSet.{u}) : Definition Head → ZFSet.{u}
  | .recursive δ =>
      recursionValue heads prev δ.datatype.type (δ.later.pis δ.result) δ.datatype.ctors
        fun k fields => abstractedBody δ.later k fields (δ.body k fields)
  | .explicit ε => ev heads prev (ε.arguments.lams ε.body) Fin.elim0

/-- **The assignment that reads a list of declarations over a base**: each datatype is read
over the assignment that reads the declarations before it, and each defined constant has its
value there. -/
noncomputable def declarationsConsts (base : DeclName → ZFSet.{u}) :
    List (Declaration Head) → DeclName → ZFSet.{u}
  | [] => base
  | .datatype d :: ds =>
      inductiveConsts heads (declarationsConsts base ds) d.type d.motiveUniverse d.ctors d.recursor
  | .definition D :: ds =>
      Function.update (declarationsConsts base ds) D.name
        (definitionValue heads (declarationsConsts base ds) D)

variable {heads} {base : DeclName → ZFSet.{u}} {R : Rules Head}

/-! ## One datatype -/

section DatatypeStage

variable {B : ChurchRules R} {d : Datatype Head} {prev : DeclName → ZFSet.{u}}

/-- The names a package declares are not names of a datatype admissible over it. -/
theorem admissible_outside (stage : d.Admissible B) {c : DeclName}
    (declared : B.constantType c ≠ none) :
    c ≠ d.type ∧ c ∉ d.ctors.map (·.1) ∧ c ≠ d.recursor := by
  refine ⟨fun same => declared (same ▸ stage.new.typeNew), fun member => ?_,
    fun same => declared (same ▸ stage.new.recNew)⟩
  obtain ⟨entry, memberEntry, rfl⟩ := List.mem_map.mp member
  exact declared (stage.new.ctorsNew entry memberEntry)

/-- **A datatype admissible over a package is fresh over every assignment**: its closed field
types are typed in the package, so their sets read only the names the package declares. -/
theorem admissible_fresh (stage : d.Admissible B) :
    FreshDeclaration heads prev d.type d.ctors d.recursor :=
  { toDistinctNames := stage.distinct
    fields := fun _ agreesOutside entry member F field =>
      CDerivable.ev_congr_declared heads
        (fun c declared =>
          agreesOutside c (admissible_outside stage declared).1 (admissible_outside stage declared).2.1
            (admissible_outside stage declared).2.2)
        (stage.fields entry member F field) Fin.elim0 }

/-- The assignment that reads an admissible datatype over an assignment keeps the values of
the names the package declares. -/
theorem admissible_readKept (stage : d.Admissible B) {c : DeclName}
    (declared : B.constantType c ≠ none) :
    inductiveConsts heads prev d.type d.motiveUniverse d.ctors d.recursor c = prev c :=
  inductiveConsts_agrees heads prev d.type d.motiveUniverse d.ctors d.recursor c
    (admissible_outside stage declared).1 (admissible_outside stage declared).2.1 (admissible_outside stage declared).2.2

/-- A name the package declares is declared in the package with the datatype. -/
theorem declared_withInductive {c : DeclName} (declared : B.constantType c ≠ none) :
    (withInductive B d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse).constantType c ≠
      none := by
  cases found : B.constantType c with
  | none => exact absurd found declared
  | some type =>
    have known : (withInductive B d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).constantType c = some type := sumDecls_left found
    rw [known]
    exact Option.some_ne_none type

/-- **The reading of an admissible datatype at every assignment that agrees on its names and
on the names of the package** with the assignment that reads it over a given one. -/
theorem admissible_reading (stage : d.Admissible B) {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, (withInductive B d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).constantType c ≠ none →
      consts c = inductiveConsts heads prev d.type d.motiveUniverse d.ctors d.recursor c) :
    InductiveReading heads consts d.type d.motiveUniverse d.ctors d.recursor := by
  have agreesBefore : ∀ c, B.constantType c ≠ none → consts c = prev c := fun c declared =>
    (agrees c (declared_withInductive declared)).trans (admissible_readKept stage declared)
  have typeDeclared : (withInductive B d.type d.typeUniverse d.ctors d.recursor
      d.motiveUniverse).constantType d.type ≠ none := by
    rw [sum_type_declared B stage.new]
    exact Option.some_ne_none _
  have ctorDeclared : ∀ entry ∈ d.ctors, (withInductive B d.type d.typeUniverse d.ctors
      d.recursor d.motiveUniverse).constantType entry.1 ≠ none := by
    intro entry member
    obtain ⟨i, found⟩ := List.getElem?_of_mem member
    rw [sum_ctor_declared B stage.distinct stage.lamFree stage.new (k := entry.1)
      (fields := entry.2) found]
    exact Option.some_ne_none _
  have recDeclared : (withInductive B d.type d.typeUniverse d.ctors d.recursor
      d.motiveUniverse).constantType d.recursor ≠ none := by
    rw [sum_rec_declared B stage.distinct stage.lamFree stage.new]
    exact Option.some_ne_none _
  refine (inductiveConsts_reading (v := d.motiveUniverse) (admissible_fresh stage (prev := prev))).of_agrees
    (agrees d.type typeDeclared) (fun entry member => agrees entry.1 (ctorDeclared entry member))
    (agrees d.recursor recDeclared) fun entry member F field => ?_
  exact CDerivable.ev_congr_declared heads
    (fun c declared => (agreesBefore c declared).trans (admissible_readKept stage declared).symm)
    (stage.fields entry member F field) Fin.elim0

/-- **A package with one more admissible datatype has a set model**, at every assignment that
agrees on the names it declares with the assignment that reads the datatype over a given one:
the package before it has a set model at every assignment that agrees with that one on its
names, and the datatype's universe is read as a closed set that holds the natural numbers. -/
theorem admissible_setModel (stage : d.Admissible B)
    (before : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = prev c) → SetModel heads consts B)
    (closed : ZFSetUniverseClosure.Closed (heads d.typeUniverse))
    (omega : ZFSet.omega ∈ heads d.typeUniverse) (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withInductive B d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).constantType c ≠ none →
      consts c = inductiveConsts heads prev d.type d.motiveUniverse d.ctors d.recursor c) :
    SetModel heads consts
      (withInductive B d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) := by
  have agreesBefore : ∀ c, B.constantType c ≠ none → consts c = prev c := fun c declared =>
    (agrees c (declared_withInductive declared)).trans (admissible_readKept stage declared)
  have modelBefore : SetModel heads consts B := before consts agreesBefore
  have modelRead : SetModel heads prev B := before _ fun _ _ => rfl
  have typeDeclared : (withInductive B d.type d.typeUniverse d.ctors d.recursor
      d.motiveUniverse).constantType d.type ≠ none := by
    rw [sum_type_declared B stage.new]
    exact Option.some_ne_none _
  have fieldSets : ∀ entry ∈ d.ctors, ∀ F, (.closed F : DeclField Head) ∈ entry.2 →
      ev heads prev (liftTm F) Fin.elim0 ∈ heads d.typeUniverse := by
    intro entry member F field
    exact CDerivable.sound modelRead (stage.fields entry member F field) Fin.elim0
      (sat_nil heads _ Fin.elim0)
  have typeMember : consts d.type ∈ heads d.typeUniverse := by
    rw [agrees d.type typeDeclared]
    exact inductiveConsts_type_mem (admissible_fresh stage (prev := prev)) closed omega fieldSets
  exact extension_setModel_at B modelBefore stage.distinct stage.lamFree
    (admissible_reading stage agrees) typeMember

end DatatypeStage

/-! ## One definition -/

section DefinitionStage

variable {B : ChurchRules R} {f : DeclName} {A : CTm Head 0}
  {eqs : List (DefiningEquation Head)} {prev : DeclName → ZFSet.{u}} {value : ZFSet.{u}}

/-- A name the package declares is declared in the package with the definition. -/
theorem declared_withDefinition {c : DeclName} (declared : B.constantType c ≠ none) :
    (withDefinition B f A eqs).constantType c ≠ none := by
  cases found : B.constantType c with
  | none => exact absurd found declared
  | some type =>
    have known : (withDefinition B f A eqs).constantType c = some type := sumDecls_left found
    rw [known]
    exact Option.some_ne_none type

/-- The assignment that gives a new constant its value keeps the values of the names the
package declares. -/
theorem definition_readKept (new : B.constantType f = none) {c : DeclName}
    (declared : B.constantType c ≠ none) : Function.update prev f value c = prev c :=
  Function.update_of_ne (fun same : c = f => declared (by rw [same]; exact new)) _ _

end DefinitionStage

/-! ## Lists -/

/-- The constructors of a datatype of an admissible list have distinct names. -/
theorem declarations_ctorsNodup {B : ChurchRules R} {ds : List (Declaration Head)}
    {d : Datatype Head} (admissible : AdmissibleDeclarations B ds)
    (member : Declaration.datatype d ∈ ds) : (d.ctors.map (·.1)).Nodup := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  exact admissible.datatype_split.2.distinct.ctorsNodup

/-- **Every datatype of an admissible list is read at every assignment that agrees on the
names the package declares** with the assignment that reads the declarations: its type is the
carrier of its signature, its constructors are the graphs of their constructor values, and its
recursor is the graph of the recursion. -/
theorem declarations_reading (B : ChurchRules R) :
    ∀ ds : List (Declaration Head), AdmissibleDeclarations B ds →
      ∀ d : Datatype Head, Declaration.datatype d ∈ ds →
      ∀ consts : DeclName → ZFSet.{u},
        (∀ c, (withDeclarations B ds).constantType c ≠ none →
          consts c = declarationsConsts heads base ds c) →
        InductiveReading heads consts d.type d.motiveUniverse d.ctors d.recursor
  | [], _, _, member, _, _ => nomatch member
  | .datatype e :: ds, admissible, d, member, consts, agrees => by
    obtain ⟨earlier, stage⟩ := admissible
    rcases List.mem_cons.mp member with same | inRest
    · obtain rfl : d = e := by injection same
      exact admissible_reading stage agrees
    · exact declarations_reading B ds earlier d inRest consts fun c declared =>
        (agrees c (declared_withInductive declared)).trans (admissible_readKept stage declared)
  | .definition D :: ds, admissible, d, member, consts, agrees => by
    obtain ⟨earlier, stage⟩ := admissible
    rcases List.mem_cons.mp member with same | inRest
    · exact nomatch same
    · exact declarations_reading B ds earlier d inRest consts fun c declared =>
        (agrees c (declared_withDefinition declared)).trans
          (definition_readKept stage.new declared)

/-- A name a package declares is declared in the package with a list of declarations. -/
theorem declared_withDeclarations (B : ChurchRules R) {c : DeclName}
    (declared : B.constantType c ≠ none) :
    ∀ ds : List (Declaration Head), (withDeclarations B ds).constantType c ≠ none
  | [] => declared
  | .datatype _ :: ds => declared_withInductive (declared_withDeclarations B declared ds)
  | .definition _ :: ds => declared_withDefinition (declared_withDeclarations B declared ds)

/-- **The assignment that reads an admissible list of declarations keeps the values of the
names the package declares.** -/
theorem declarationsConsts_base (B : ChurchRules R) {c : DeclName}
    (declared : B.constantType c ≠ none) :
    ∀ ds : List (Declaration Head), AdmissibleDeclarations B ds →
      declarationsConsts heads base ds c = base c
  | [], _ => rfl
  | .datatype _ :: ds, admissible =>
      (admissible_readKept admissible.2 (declared_withDeclarations B declared ds)).trans
        (declarationsConsts_base B declared ds admissible.1)
  | .definition _ :: ds, admissible =>
      (definition_readKept admissible.2.new (declared_withDeclarations B declared ds)).trans
        (declarationsConsts_base B declared ds admissible.1)

/-- A name declared before some declarations is declared after them. -/
theorem declared_withDeclarations_after {B : ChurchRules R} (pre : List (Declaration Head))
    {post : List (Declaration Head)} {c : DeclName}
    (declared : (withDeclarations B post).constantType c ≠ none) :
    (withDeclarations B (pre ++ post)).constantType c ≠ none := by
  cases found : (withDeclarations B post).constantType c with
  | none => exact absurd found declared
  | some type =>
    rw [(withDeclarations_sub B post pre).constantType found]
    exact Option.some_ne_none type

/-- **The assignment that reads a longer admissible list keeps the values of the names
declared before.** -/
theorem declarationsConsts_after {B : ChurchRules R} {post : List (Declaration Head)} :
    ∀ pre : List (Declaration Head), AdmissibleDeclarations B (pre ++ post) →
      ∀ {c : DeclName}, (withDeclarations B post).constantType c ≠ none →
        declarationsConsts heads base (pre ++ post) c = declarationsConsts heads base post c
  | [], _, _, _ => rfl
  | .datatype _ :: pre, admissible, _, declared =>
      (admissible_readKept (heads := heads) admissible.2
        (declared_withDeclarations_after pre declared)).trans
        (declarationsConsts_after pre admissible.1 declared)
  | .definition _ :: pre, admissible, _, declared =>
      (definition_readKept admissible.2.new (declared_withDeclarations_after pre declared)).trans
        (declarationsConsts_after pre admissible.1 declared)

section Model

variable {L : Type} [LevelOrder L] (levels : LevelModel R L)

include levels in
/-- **A package with an admissible list of declarations has a set model**, at every
assignment that agrees on the names the package declares with the assignment that reads the
declarations. The base package has a set model at every assignment that agrees with the base
assignment on the names it declares, and the universe of each datatype is read as a closed
set that holds the natural numbers. -/
theorem declarations_setModel (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B) :
    ∀ ds : List (Declaration Head), AdmissibleDeclarations B ds →
      (∀ d : Datatype Head, Declaration.datatype d ∈ ds →
        ZFSetUniverseClosure.Closed (heads d.typeUniverse) ∧
          ZFSet.omega ∈ heads d.typeUniverse) →
      ∀ consts : DeclName → ZFSet.{u},
        (∀ c, (withDeclarations B ds).constantType c ≠ none →
          consts c = declarationsConsts heads base ds c) →
        SetModel heads consts (withDeclarations B ds)
  | [], _, _, consts, agrees => baseModel consts agrees
  | .datatype d :: ds, admissible, universes, consts, agrees => by
    obtain ⟨earlier, stage⟩ := admissible
    obtain ⟨closed, omega⟩ := universes d List.mem_cons_self
    exact admissible_setModel stage
      (declarations_setModel B baseModel ds earlier
        fun e member => universes e (List.mem_cons_of_mem _ member))
      closed omega consts agrees
  | .definition D :: ds, admissible, universes, consts, agrees => by
    obtain ⟨earlier, stage⟩ := admissible
    have before := declarations_setModel B baseModel ds earlier
      fun e member => universes e (List.mem_cons_of_mem _ member)
    cases D with
    | recursive δ =>
      obtain ⟨declaredBefore, stage⟩ := stage
      obtain ⟨w, -, family⟩ := stage.family
      have typeDeclared : (withDeclarations B ds).constantType δ.datatype.type ≠ none := by
        rw [earlier.type_declared declaredBefore]
        exact Option.some_ne_none _
      exact laterArguments_setModel (levelsWith levels ds) (withDeclarations B ds) before
        (declarations_ctorsNodup earlier declaredBefore)
        (fun consts agrees =>
          declarations_reading B ds earlier δ.datatype declaredBefore consts agrees)
        stage.new typeDeclared family (earlier.fieldsFormed declaredBefore) stage.formed
        stage.resultType stage.bodies consts agrees
    | explicit ε =>
      exact explicit_setModel (levelsWith levels ds) (withDeclarations B ds) before stage.new
        stage.formed stage.resultType stage.body consts agrees

include levels in
/-- The model at the assignment that reads the declarations. -/
theorem declarations_setModel_read (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    {ds : List (Declaration Head)} (admissible : AdmissibleDeclarations B ds)
    (universes : ∀ d : Datatype Head, Declaration.datatype d ∈ ds →
      ZFSetUniverseClosure.Closed (heads d.typeUniverse) ∧ ZFSet.omega ∈ heads d.typeUniverse) :
    SetModel heads (declarationsConsts heads base ds) (withDeclarations B ds) :=
  declarations_setModel levels B baseModel ds admissible universes _ fun _ _ => rfl

include levels in
/-- **Soundness**: every derivable statement of a package with an admissible list of
declarations holds in the model. -/
theorem declarations_sound (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    {ds : List (Declaration Head)} (admissible : AdmissibleDeclarations B ds)
    (universes : ∀ d : Datatype Head, Declaration.datatype d ∈ ds →
      ZFSetUniverseClosure.Closed (heads d.typeUniverse) ∧ ZFSet.omega ∈ heads d.typeUniverse)
    {s : CStatement Head} (derivation : CDerivable (withDeclarations B ds) s) :
    Holds heads (declarationsConsts heads base ds) s :=
  CDerivable.sound (declarations_setModel_read levels B baseModel admissible universes) derivation

include levels in
/-- **Consistency**: a closed type whose set is empty has no closed term in a package with an
admissible list of declarations. -/
theorem declarations_no_closed_inhabitant (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    {ds : List (Declaration Head)} (admissible : AdmissibleDeclarations B ds)
    (universes : ∀ d : Datatype Head, Declaration.datatype d ∈ ds →
      ZFSetUniverseClosure.Closed (heads d.typeUniverse) ∧ ZFSet.omega ∈ heads d.typeUniverse)
    {A : CTm Head 0}
    (empty : ∀ z, z ∉ ev heads (declarationsConsts heads base ds) A Fin.elim0) (t : CTm Head 0) :
    ¬ CTyped (withDeclarations B ds) .nil t A :=
  CDerivable.no_closed_inhabitant
    (declarations_setModel_read levels B baseModel admissible universes) empty t

include levels in
/-- Positive example: the model of the package with no declaration is the base package's. -/
theorem declarations_setModel_nil (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B) :
    SetModel heads base (withDeclarations B []) :=
  declarations_setModel_read levels B baseModel (ds := []) (admissible_nil B)
    (fun _ member => nomatch member)

end Model

/-! ## Data terms over the datatypes of a list -/

open ZFSetInductive (DataTerm) in
/-- **A data term over the datatypes of a list of declarations**: each of its names is a
constructor of a datatype of the list, with as many arguments as the constructor has fields,
and the closed fields of that constructor are the types of datatypes of the list. -/
inductive DataOver (ds : List (Declaration Head)) : DataTerm → Prop
  | app {d : Datatype Head} {i : Nat} {k : DeclName} {fields : List (DeclField Head)}
      {args : List DataTerm}
      (declared : Declaration.datatype d ∈ ds) (entry : d.ctors[i]? = some (k, fields))
      (length : args.length = fields.length)
      (pure : ∀ F, (.closed F : DeclField Head) ∈ fields →
        ∃ e : Datatype Head, Declaration.datatype e ∈ ds ∧ F = .const e.type)
      (rest : ∀ a ∈ args, DataOver ds a) : DataOver ds (.app k args)

open ZFSetInductive (DataTerm) in
/-- A data term over the datatypes of an admissible list is read by the constructors of every
assignment that agrees on the declared names with the assignment that reads the list. -/
theorem DataOver.read (B : ChurchRules R) {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, (withDeclarations B ds).constantType c ≠ none →
      consts c = declarationsConsts heads base ds c)
    {t : DataTerm} (covered : DataOver ds t) : DataRead heads consts t := by
  induction covered with
  | @app d i k fields args declared entry length pure _ ih =>
      have reading := declarations_reading (heads := heads) (base := base) B ds admissible d
        declared consts agrees
      refine .app (T := d.type) (reading.ctor entry) length (fun field member => ?_) ih
      cases field with
      | recursive => exact reading.empty_not_mem
      | closed F =>
          obtain ⟨e, declaredE, rfl⟩ := pure F member
          exact (declarations_reading (heads := heads) (base := base) B ds admissible e
            declaredE consts agrees).empty_not_mem

open ZFSetInductive (DataTerm) in
/-- **A typed data term means its set.** In a set model of a package with an admissible list
of declarations, at an assignment that reads the list: a data term over the datatypes of the
list whose term has the type of a datatype of the list has the set of the data term as its
value. -/
theorem declarations_dataTerm_value (B : ChurchRules R) {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, (withDeclarations B ds).constantType c ≠ none →
      consts c = declarationsConsts heads base ds c)
    (model : SetModel heads consts (withDeclarations B ds))
    {t : DataTerm} (covered : DataOver ds t) {e : Datatype Head}
    (declared : Declaration.datatype e ∈ ds)
    (typed : CTyped (withDeclarations B ds) .nil (liftTm (dataTm t)) (.const e.type)) :
    ev heads consts (liftTm (dataTm t : Tm Head 0)) Fin.elim0 = t.toSet :=
  (covered.read (heads := heads) (base := base) B admissible agrees).typed_value model typed
    (declarations_reading (heads := heads) (base := base) B ds admissible e declared consts
      agrees).empty_not_mem

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
