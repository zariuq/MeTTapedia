import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationComputation

/-!
# Proof-carrying indexed-family declarations

This module isolates the syntax-independent-of-any-particular-family portion
of Prime's native indexed-family mechanism.  A declaration candidate carries
formed global declarations, structurally positive constructor types, an
explicit eliminator declaration, and typed iota schemas.  Computation
authority is a separate field: formation cannot silently stand in for subject
preservation.

Strict positivity is checked on the shared open-term grammar.  Recursive
occurrences must be full applications of the declared family at exactly its
declared arity.  Unknown applications containing the family are rejected,
as are occurrences in a dependent-function domain.  Renaming preserves the
discipline; substitution preserves it when the substituted terms are free of
the family constant.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace Declaration
namespace IndexedFamily

open ComputationAuthority

/-! ## Absence of a recursive family constant -/

/-- A term contains no occurrence of the named family constant. -/
inductive FreeOf (family : DeclName) : Tm Head n → Prop where
  | var (index : Fin n) : FreeOf family (.var index)
  | const {name : DeclName} : name ≠ family → FreeOf family (.const name)
  | head (value : Head) : FreeOf family (.head value)
  | pi {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      FreeOf family domain → FreeOf family codomain →
        FreeOf family (.pi domain codomain)
  | sigma {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      FreeOf family domain → FreeOf family codomain →
        FreeOf family (.sigma domain codomain)
  | id {type left right : Tm Head n} :
      FreeOf family type → FreeOf family left → FreeOf family right →
        FreeOf family (.id type left right)
  | lam {body : Tm Head (n + 1)} :
      FreeOf family body → FreeOf family (.lam body)
  | app {function argument : Tm Head n} :
      FreeOf family function → FreeOf family argument →
        FreeOf family (.app function argument)
  | pair {first second : Tm Head n} :
      FreeOf family first → FreeOf family second →
        FreeOf family (.pair first second)
  | fst {pair : Tm Head n} : FreeOf family pair → FreeOf family (.fst pair)
  | snd {pair : Tm Head n} : FreeOf family pair → FreeOf family (.snd pair)
  | refl {term : Tm Head n} : FreeOf family term → FreeOf family (.refl term)

abbrev FreeSub (family : DeclName) (substitution : Sub Head n m) : Prop :=
  ∀ index, FreeOf family (substitution index)

def FreeOf.rename {term : Tm Head n} (free : FreeOf family term)
    (renameMap : Ren n m) : FreeOf family (Presentation.rename renameMap term) := by
  induction free generalizing m with
  | var index => exact .var _
  | const different => exact .const different
  | head value => exact .head value
  | pi domain codomain ihDomain ihCodomain =>
      exact .pi (ihDomain renameMap) (ihCodomain (liftRen renameMap))
  | sigma domain codomain ihDomain ihCodomain =>
      exact .sigma (ihDomain renameMap) (ihCodomain (liftRen renameMap))
  | id type left right ihType ihLeft ihRight =>
      exact .id (ihType renameMap) (ihLeft renameMap) (ihRight renameMap)
  | lam body ih => exact .lam (ih (liftRen renameMap))
  | app function argument ihFunction ihArgument =>
      exact .app (ihFunction renameMap) (ihArgument renameMap)
  | pair first second ihFirst ihSecond =>
      exact .pair (ihFirst renameMap) (ihSecond renameMap)
  | fst pair ih => exact .fst (ih renameMap)
  | snd pair ih => exact .snd (ih renameMap)
  | refl term ih => exact .refl (ih renameMap)

def FreeSub.lift {substitution : Sub Head n m}
    (free : FreeSub family substitution) :
    FreeSub family (liftSub substitution) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact .var 0
  · intro prior
    exact (free prior).rename wk

def FreeOf.substitute {term : Tm Head n} (free : FreeOf family term)
    {substitution : Sub Head n m} (substitutionFree : FreeSub family substitution) :
    FreeOf family (Presentation.subst substitution term) := by
  induction free generalizing m with
  | var index => exact substitutionFree index
  | const different => exact .const different
  | head value => exact .head value
  | pi domain codomain ihDomain ihCodomain =>
      exact .pi (ihDomain substitutionFree)
        (ihCodomain substitutionFree.lift)
  | sigma domain codomain ihDomain ihCodomain =>
      exact .sigma (ihDomain substitutionFree)
        (ihCodomain substitutionFree.lift)
  | id type left right ihType ihLeft ihRight =>
      exact .id (ihType substitutionFree) (ihLeft substitutionFree)
        (ihRight substitutionFree)
  | lam body ih => exact .lam (ih substitutionFree.lift)
  | app function argument ihFunction ihArgument =>
      exact .app (ihFunction substitutionFree) (ihArgument substitutionFree)
  | pair first second ihFirst ihSecond =>
      exact .pair (ihFirst substitutionFree) (ihSecond substitutionFree)
  | fst pair ih => exact .fst (ih substitutionFree)
  | snd pair ih => exact .snd (ih substitutionFree)
  | refl term ih => exact .refl (ih substitutionFree)

theorem not_free_family_constant :
    ¬ FreeOf (Head := Head) family (.const family : Tm Head n) := by
  intro free
  cases free with
  | const different => exact different rfl

/-! ## Proof-relevant constant occurrences and application heads -/

/-- A path to a named constant occurrence.  Unlike the support proposition
`¬ FreeOf`, this records where the occurrence was found. -/
inductive ConstantOccurrence (name : DeclName) : Tm Head n → Type where
  | here : ConstantOccurrence name (.const name)
  | piDomain {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      ConstantOccurrence name domain →
        ConstantOccurrence name (.pi domain codomain)
  | piCodomain {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      ConstantOccurrence name codomain →
        ConstantOccurrence name (.pi domain codomain)
  | sigmaDomain {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      ConstantOccurrence name domain →
        ConstantOccurrence name (.sigma domain codomain)
  | sigmaCodomain {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      ConstantOccurrence name codomain →
        ConstantOccurrence name (.sigma domain codomain)
  | idType {type left right : Tm Head n} :
      ConstantOccurrence name type →
        ConstantOccurrence name (.id type left right)
  | idLeft {type left right : Tm Head n} :
      ConstantOccurrence name left →
        ConstantOccurrence name (.id type left right)
  | idRight {type left right : Tm Head n} :
      ConstantOccurrence name right →
        ConstantOccurrence name (.id type left right)
  | lamBody {body : Tm Head (n + 1)} :
      ConstantOccurrence name body → ConstantOccurrence name (.lam body)
  | appFunction {function argument : Tm Head n} :
      ConstantOccurrence name function →
        ConstantOccurrence name (.app function argument)
  | appArgument {function argument : Tm Head n} :
      ConstantOccurrence name argument →
        ConstantOccurrence name (.app function argument)
  | pairFirst {first second : Tm Head n} :
      ConstantOccurrence name first →
        ConstantOccurrence name (.pair first second)
  | pairSecond {first second : Tm Head n} :
      ConstantOccurrence name second →
        ConstantOccurrence name (.pair first second)
  | fstPair {pair : Tm Head n} :
      ConstantOccurrence name pair → ConstantOccurrence name (.fst pair)
  | sndPair {pair : Tm Head n} :
      ConstantOccurrence name pair → ConstantOccurrence name (.snd pair)
  | reflTerm {term : Tm Head n} :
      ConstantOccurrence name term → ConstantOccurrence name (.refl term)

noncomputable def ConstantOccurrence.rename {term : Tm Head n}
    (occurrence : ConstantOccurrence name term) (renameMap : Ren n m) :
    ConstantOccurrence name (Presentation.rename renameMap term) := by
  induction occurrence generalizing m with
  | here => exact .here
  | piDomain occurrence ih => exact .piDomain (ih renameMap)
  | piCodomain occurrence ih => exact .piCodomain (ih (liftRen renameMap))
  | sigmaDomain occurrence ih => exact .sigmaDomain (ih renameMap)
  | sigmaCodomain occurrence ih => exact .sigmaCodomain (ih (liftRen renameMap))
  | idType occurrence ih => exact .idType (ih renameMap)
  | idLeft occurrence ih => exact .idLeft (ih renameMap)
  | idRight occurrence ih => exact .idRight (ih renameMap)
  | lamBody occurrence ih => exact .lamBody (ih (liftRen renameMap))
  | appFunction occurrence ih => exact .appFunction (ih renameMap)
  | appArgument occurrence ih => exact .appArgument (ih renameMap)
  | pairFirst occurrence ih => exact .pairFirst (ih renameMap)
  | pairSecond occurrence ih => exact .pairSecond (ih renameMap)
  | fstPair occurrence ih => exact .fstPair (ih renameMap)
  | sndPair occurrence ih => exact .sndPair (ih renameMap)
  | reflTerm occurrence ih => exact .reflTerm (ih renameMap)

noncomputable def ConstantOccurrence.substitute {term : Tm Head n}
    (occurrence : ConstantOccurrence name term)
    (substitution : Sub Head n m) :
    ConstantOccurrence name (Presentation.subst substitution term) := by
  induction occurrence generalizing m with
  | here => exact .here
  | piDomain occurrence ih => exact .piDomain (ih substitution)
  | piCodomain occurrence ih => exact .piCodomain (ih (liftSub substitution))
  | sigmaDomain occurrence ih => exact .sigmaDomain (ih substitution)
  | sigmaCodomain occurrence ih => exact .sigmaCodomain (ih (liftSub substitution))
  | idType occurrence ih => exact .idType (ih substitution)
  | idLeft occurrence ih => exact .idLeft (ih substitution)
  | idRight occurrence ih => exact .idRight (ih substitution)
  | lamBody occurrence ih => exact .lamBody (ih (liftSub substitution))
  | appFunction occurrence ih => exact .appFunction (ih substitution)
  | appArgument occurrence ih => exact .appArgument (ih substitution)
  | pairFirst occurrence ih => exact .pairFirst (ih substitution)
  | pairSecond occurrence ih => exact .pairSecond (ih substitution)
  | fstPair occurrence ih => exact .fstPair (ih substitution)
  | sndPair occurrence ih => exact .sndPair (ih substitution)
  | reflTerm occurrence ih => exact .reflTerm (ih substitution)

/-- The function spine of an application is headed by a named constant. -/
inductive ApplicationHead (name : DeclName) : Tm Head n → Type where
  | const : ApplicationHead name (.const name)
  | app {function argument : Tm Head n} :
      ApplicationHead name function →
        ApplicationHead name (.app function argument)

noncomputable def ApplicationHead.rename {term : Tm Head n}
    (head : ApplicationHead name term) (renameMap : Ren n m) :
    ApplicationHead name (Presentation.rename renameMap term) := by
  induction head with
  | const => exact .const
  | app head ih => exact .app ih

noncomputable def ApplicationHead.substitute {term : Tm Head n}
    (head : ApplicationHead name term) (substitution : Sub Head n m) :
    ApplicationHead name (Presentation.subst substitution term) := by
  induction head with
  | const => exact .const
  | app head ih => exact .app ih

/-! ## Exact family applications -/

/-- Apply a finite telescope of arguments from left to right. -/
def applyArgs (function : Tm Head n) : List (Tm Head n) → Tm Head n
  | [] => function
  | argument :: rest => applyArgs (.app function argument) rest

@[simp] theorem applyArgs_nil (function : Tm Head n) :
    applyArgs function [] = function := rfl

@[simp] theorem applyArgs_cons (function argument : Tm Head n)
    (rest : List (Tm Head n)) :
    applyArgs function (argument :: rest) =
      applyArgs (.app function argument) rest := rfl

@[simp] theorem rename_applyArgs (renameMap : Ren n m)
    (function : Tm Head n) (arguments : List (Tm Head n)) :
    Presentation.rename renameMap (applyArgs function arguments) =
      applyArgs (Presentation.rename renameMap function)
        (arguments.map (Presentation.rename renameMap)) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument rest ih =>
      simp only [applyArgs_cons, List.map_cons]
      exact ih (.app function argument)

@[simp] theorem subst_applyArgs (substitution : Sub Head n m)
    (function : Tm Head n) (arguments : List (Tm Head n)) :
    Presentation.subst substitution (applyArgs function arguments) =
      applyArgs (Presentation.subst substitution function)
        (arguments.map (Presentation.subst substitution)) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument rest ih =>
      simp only [applyArgs_cons, List.map_cons]
      exact ih (.app function argument)

def FreeOf.applyArgsFree {function : Tm Head n}
    {arguments : List (Tm Head n)}
    (functionFree : FreeOf family function)
    (argumentsFree : ∀ argument ∈ arguments, FreeOf family argument) :
    FreeOf family (applyArgs function arguments) := by
  induction arguments generalizing function with
  | nil => exact functionFree
  | cons argument rest ih =>
      apply ih
      · exact .app functionFree (argumentsFree argument (by simp))
      · intro later membership
        exact argumentsFree later (by simp [membership])

theorem FreeOf.function_of_applyArgs {function : Tm Head n}
    {arguments : List (Tm Head n)}
    (free : FreeOf family (applyArgs function arguments)) :
    FreeOf family function := by
  induction arguments generalizing function with
  | nil => exact free
  | cons argument rest ih =>
      have appliedFree : FreeOf family (.app function argument) :=
        ih (function := .app function argument) free
      cases appliedFree with
      | app functionFree _ => exact functionFree

/-- A family occurrence is a full application with exactly the declared
number of arguments, none of which recursively mentions the family. -/
inductive FamilyApplication (family : DeclName) (arity : Nat) :
    Tm Head n → Prop where
  | intro (arguments : List (Tm Head n))
      (length_eq : arguments.length = arity)
      (argumentsFree : ∀ argument ∈ arguments, FreeOf family argument)
      {term : Tm Head n}
      (equation : applyArgs (.const family) arguments = term) :
      FamilyApplication family arity term

theorem FamilyApplication.rename {term : Tm Head n}
    (application : FamilyApplication family arity term)
    (renameMap : Ren n m) :
    FamilyApplication family arity (Presentation.rename renameMap term) := by
  rcases application with ⟨arguments, length, argumentsFree, equation⟩
  refine .intro (arguments.map (Presentation.rename renameMap))
    (by simpa using length) ?_ ?_
  · intro argument membership
    rcases List.mem_map.mp membership with ⟨source, sourceMembership, rfl⟩
    exact (argumentsFree source sourceMembership).rename renameMap
  · calc
      applyArgs (.const family)
          (arguments.map (Presentation.rename renameMap)) =
          Presentation.rename renameMap
            (applyArgs (.const family) arguments) := by
        symm
        exact rename_applyArgs renameMap (.const family) arguments
      _ = Presentation.rename renameMap term :=
        congrArg (Presentation.rename renameMap) equation

theorem FamilyApplication.substitute {term : Tm Head n}
    (application : FamilyApplication family arity term)
    {substitution : Sub Head n m} (substitutionFree : FreeSub family substitution) :
    FamilyApplication family arity (Presentation.subst substitution term) := by
  rcases application with ⟨arguments, length, argumentsFree, equation⟩
  refine .intro (arguments.map (Presentation.subst substitution))
    (by simpa using length) ?_ ?_
  · intro argument membership
    rcases List.mem_map.mp membership with ⟨source, sourceMembership, rfl⟩
    exact (argumentsFree source sourceMembership).substitute substitutionFree
  · calc
      applyArgs (.const family)
          (arguments.map (Presentation.subst substitution)) =
          Presentation.subst substitution
            (applyArgs (.const family) arguments) := by
        symm
        exact subst_applyArgs substitution (.const family) arguments
      _ = Presentation.subst substitution term :=
        congrArg (Presentation.subst substitution) equation

theorem FamilyApplication.not_free {term : Tm Head n}
    (application : FamilyApplication family arity term) :
    ¬ FreeOf family term := by
  rcases application with ⟨arguments, _length, _argumentsFree, equation⟩
  intro free
  rw [← equation] at free
  exact not_free_family_constant
    (FreeOf.function_of_applyArgs free)

private theorem applyArgs_applied_ne_const
    (function argument : Tm Head n) (rest : List (Tm Head n))
    (name : DeclName) :
    applyArgs (.app function argument) rest ≠ (.const name : Tm Head n) := by
  induction rest generalizing function argument with
  | nil => intro equality; cases equality
  | cons next rest ih =>
      exact ih (.app function argument) next

private theorem applyArgs_applied_ne_pi
    (function argument : Tm Head n) (rest : List (Tm Head n))
    (domain : Tm Head n) (codomain : Tm Head (n + 1)) :
    applyArgs (.app function argument) rest ≠ .pi domain codomain := by
  induction rest generalizing function argument with
  | nil => intro equality; cases equality
  | cons next rest ih =>
      exact ih (.app function argument) next

theorem no_family_application_pi (family : DeclName) (arity : Nat)
    (domain : Tm Head n) (codomain : Tm Head (n + 1)) :
    FamilyApplication family arity (.pi domain codomain) → False := by
  rintro ⟨arguments, _length, _free, equation⟩
  cases arguments with
  | nil => cases equation
  | cons argument rest =>
      exact applyArgs_applied_ne_pi (.const family) argument rest
        domain codomain equation

theorem no_positive_arity_at_bare_family (arity : Nat) :
    FamilyApplication (Head := Head) family (arity + 1)
      (.const family : Tm Head n) → False := by
  rintro ⟨arguments, length, _free, equation⟩
  cases arguments with
  | nil =>
      change 0 = Nat.succ arity at length
      exact Nat.noConfusion length
  | cons argument rest =>
      exact applyArgs_applied_ne_const (.const family) argument rest family
        equation

/-! ## Structural strict positivity -/

/-- Strictly-positive occurrences in a type.  Function domains must be free
of the recursive family.  Sigma components are positive; identity endpoints
are ordinary terms and must be family-free.  Applications through an unknown
head are accepted only when entirely family-free. -/
inductive StrictlyPositive (family : DeclName) (arity : Nat) :
    Tm Head n → Type where
  | free {term : Tm Head n} : FreeOf family term →
      StrictlyPositive family arity term
  | recursive {term : Tm Head n} : FamilyApplication family arity term →
      StrictlyPositive family arity term
  | pi {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      FreeOf family domain → StrictlyPositive family arity codomain →
        StrictlyPositive family arity (.pi domain codomain)
  | sigma {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      StrictlyPositive family arity domain →
      StrictlyPositive family arity codomain →
        StrictlyPositive family arity (.sigma domain codomain)
  | id {type left right : Tm Head n} :
      StrictlyPositive family arity type →
      FreeOf family left → FreeOf family right →
        StrictlyPositive family arity (.id type left right)

noncomputable def StrictlyPositive.rename {term : Tm Head n}
    (positive : StrictlyPositive family arity term) (renameMap : Ren n m) :
    StrictlyPositive family arity (Presentation.rename renameMap term) := by
  induction positive generalizing m with
  | free free => exact .free (free.rename renameMap)
  | recursive application => exact .recursive (application.rename renameMap)
  | pi domainFree codomainPositive ih =>
      exact .pi (domainFree.rename renameMap) (ih (liftRen renameMap))
  | sigma domainPositive codomainPositive ihDomain ihCodomain =>
      exact .sigma (ihDomain renameMap) (ihCodomain (liftRen renameMap))
  | id typePositive leftFree rightFree ih =>
      exact .id (ih renameMap) (leftFree.rename renameMap)
        (rightFree.rename renameMap)

noncomputable def StrictlyPositive.substitute {term : Tm Head n}
    (positive : StrictlyPositive family arity term)
    {substitution : Sub Head n m} (substitutionFree : FreeSub family substitution) :
    StrictlyPositive family arity (Presentation.subst substitution term) := by
  induction positive generalizing m with
  | free free => exact .free (free.substitute substitutionFree)
  | recursive application =>
      exact .recursive (application.substitute substitutionFree)
  | pi domainFree codomainPositive ih =>
      exact .pi (domainFree.substitute substitutionFree)
        (ih substitutionFree.lift)
  | sigma domainPositive codomainPositive ihDomain ihCodomain =>
      exact .sigma (ihDomain substitutionFree)
        (ihCodomain substitutionFree.lift)
  | id typePositive leftFree rightFree ih =>
      exact .id (ih substitutionFree)
        (leftFree.substitute substitutionFree)
        (rightFree.substitute substitutionFree)

/-- A known recursive occurrence in a function domain is rejected.  This is
the contravariant negative control for the positivity discipline. -/
theorem recursivePiDomain_not_strictlyPositive
    {domain : Tm Head n} (recursive : FamilyApplication family arity domain)
    (codomain : Tm Head (n + 1)) :
    StrictlyPositive family arity (.pi domain codomain) → False := by
  intro positive
  cases positive with
  | free free =>
      cases free with
      | pi domainFree _ => exact recursive.not_free domainFree
  | recursive application =>
      exact no_family_application_pi family arity domain codomain application
  | pi domainFree _ => exact recursive.not_free domainFree

/-- A constructor telescope ends in the declared family and every field type
is strictly positive. -/
inductive ConstructorType (family : DeclName) (arity : Nat) :
    Tm Head n → Type where
  | result {term : Tm Head n} : FamilyApplication family arity term →
      ConstructorType family arity term
  | field {domain : Tm Head n} {codomain : Tm Head (n + 1)} :
      StrictlyPositive family arity domain →
      ConstructorType family arity codomain →
        ConstructorType family arity (.pi domain codomain)

noncomputable def ConstructorType.rename {term : Tm Head n}
    (constructor : ConstructorType family arity term) (renameMap : Ren n m) :
    ConstructorType family arity (Presentation.rename renameMap term) := by
  induction constructor generalizing m with
  | result application => exact .result (application.rename renameMap)
  | field positive _ ih =>
      exact .field (positive.rename renameMap) (ih (liftRen renameMap))

noncomputable def ConstructorType.substitute {term : Tm Head n}
    (constructor : ConstructorType family arity term)
    {substitution : Sub Head n m} (substitutionFree : FreeSub family substitution) :
    ConstructorType family arity (Presentation.subst substitution term) := by
  induction constructor generalizing m with
  | result application =>
      exact .result (application.substitute substitutionFree)
  | field positive _ ih =>
      exact .field (positive.substitute substitutionFree)
        (ih substitutionFree.lift)

/-! ## Proof-carrying declaration packages -/

structure ConstructorSpec (signature : Signature Head)
    (family : DeclName) (arity : Nat) where
  name : DeclName
  type : Tm Head 0
  declared : signature.typeOf? name = some type
  positive : ConstructorType family arity type

structure EliminatorSpec (signature : Signature Head) where
  name : DeclName
  type : Tm Head 0
  declared : signature.typeOf? name = some type

/-- A typed canonical computation schema retaining its exact rule witness.
Its proposition-valued declaration step is a derived support readout; no
endpoint-only rule may be listed here. -/
structure IotaSchema (base : Rules Head) (signature : Signature Head)
    (computation : ProofRelevantRootComputation Head) (arity : Nat) where
  context : Ctx Head arity
  left : Tm Head arity
  right : Tm Head arity
  type : Tm Head arity
  receipt : ProofRelevantStepReceipt base signature computation
    context left right type

/-- Forget the exact rule witness only at the logical computation boundary. -/
def IotaSchema.toDeclaredReceipt
    {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head} {arity : Nat}
    (schema : IotaSchema base signature computation arity)
    (supportEquation : signature.computation = computation.support) :
    DeclaredStepReceipt base signature schema.context schema.left
      schema.right schema.type :=
  schema.receipt.toDeclaredReceipt supportEquation

/-- A canonical computation schema connected to both the declared eliminator
at the application head and the constructor it eliminates. -/
structure IotaClause (base : Rules Head) (signature : Signature Head)
    (computation : ProofRelevantRootComputation Head)
    (constructorNames : List DeclName) (eliminatorName : DeclName) where
  constructorName : DeclName
  constructorDeclared : constructorName ∈ constructorNames
  arity : Nat
  schema : IotaSchema base signature computation arity
  eliminatorHead : ApplicationHead eliminatorName schema.left
  constructorOccurrence : ConstantOccurrence constructorName schema.left

/-- One formed family within a declaration signature: positive constructors,
a separately named eliminator, and its typed iota generators.  A signature may
carry several such families, so the listed schemas are family-specific rather
than a claim to exhaust the signature's computation relation.  This is the
informative pre-authority object. -/
structure Candidate (base : Rules Head) where
  signature : Signature Head
  formed : signature.Formed base
  computation : ProofRelevantRootComputation Head
  computationSupport : signature.computation = computation.support
  familyName : DeclName
  familyParameterCount : Nat
  familyIndexCount : Nat
  familyType : Tm Head 0
  familyDeclared : signature.typeOf? familyName = some familyType
  constructors : List
    (ConstructorSpec signature familyName
      (familyParameterCount + familyIndexCount))
  constructorNamesNodup : constructors.map ConstructorSpec.name |>.Nodup
  familyNotConstructor :
    ∀ constructor ∈ constructors, constructor.name ≠ familyName
  eliminator : EliminatorSpec signature
  eliminatorNotFamily : eliminator.name ≠ familyName
  eliminatorNotConstructor :
    ∀ constructor ∈ constructors, constructor.name ≠ eliminator.name
  iotaClauses : List
    (IotaClause base signature computation
      (constructors.map ConstructorSpec.name) eliminator.name)
  constructorsComputed :
    ∀ constructorName ∈ constructors.map ConstructorSpec.name,
      constructorName ∈ iotaClauses.map IotaClause.constructorName

def Candidate.familyArity {base : Rules Head} (candidate : Candidate base) : Nat :=
  candidate.familyParameterCount + candidate.familyIndexCount

/-- A family candidate receives computational authority only with a uniform
preservation proof for every raw declared equation. -/
structure Authorized (base : Rules Head) where
  candidate : Candidate base
  preserves : candidate.signature.DeclaredPreserves base

def Authorized.checkedSignature {base : Rules Head}
    (authorized : Authorized base) : CheckedSignature base where
  signature := authorized.candidate.signature
  wellFormed := authorized.candidate.formed.withPreservation
    authorized.preserves

/-! ## Positive and negative canaries -/

namespace Canary

def family : DeclName := `Prime.IndexedFamily.Canary

def indexedOccurrence : Tm Unit 1 :=
  .app (.const family) (.var 0)

def indexedApplication : FamilyApplication family 1 indexedOccurrence :=
  .intro [.var 0] rfl (by
    intro argument membership
    simp only [List.mem_singleton] at membership
    subst argument
    exact .var 0) rfl

def positiveRecursiveField : ConstructorType family 1
    (.pi indexedOccurrence
      (Presentation.rename wk indexedOccurrence)) :=
  .field (.recursive indexedApplication)
    (.result (indexedApplication.rename wk))

def negativeFunctionField : Tm Unit 1 :=
  .pi indexedOccurrence (.var 0)

theorem indexedOccurrence_not_free :
    ¬ FreeOf family indexedOccurrence :=
  indexedApplication.not_free

theorem negativeFunctionField_not_strictlyPositive
    (positive : StrictlyPositive family 1 negativeFunctionField) : False := by
  exact recursivePiDomain_not_strictlyPositive indexedApplication (.var 0)
    positive

theorem bareFamily_not_constructor_at_index_arity
    (constructor : ConstructorType family 1 (.const family : Tm Unit 0)) :
    False := by
  cases constructor with
  | result application =>
      exact no_positive_arity_at_bare_family
        (Head := Unit) (family := family) 0 application

end Canary

/-! ## Axiom audit -/

#print axioms FreeOf.substitute
#print axioms ConstantOccurrence.substitute
#print axioms ApplicationHead.rename
#print axioms FamilyApplication.rename
#print axioms no_positive_arity_at_bare_family
#print axioms StrictlyPositive.substitute
#print axioms recursivePiDomain_not_strictlyPositive
#print axioms ConstructorType.rename
#print axioms Authorized.checkedSignature
#print axioms Canary.positiveRecursiveField
#print axioms Canary.negativeFunctionField_not_strictlyPositive
#print axioms Canary.bareFamily_not_constructor_at_index_arity

end IndexedFamily
end Declaration
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
