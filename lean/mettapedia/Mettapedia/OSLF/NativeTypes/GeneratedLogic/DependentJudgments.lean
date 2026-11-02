import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Judgments
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution

/-!
# Dependent and parametric types in the generated type system

The native types of a language are the formulas of its generated logic Φ(L), and its open judgments read them at
the instances of open terms (`OpenTerms`, `Judgments`). Types there could depend on values only through families
supplied from outside. Here they depend on values syntactically, and the rules for them are generated uniformly for
every language:

- **Terms inside types** (`Formula.substTerms`): a formula's named terms may mention term variables, and a
  substitution gives them values; the identity substitution changes nothing (`substTerms_fvar`), substitutions
  compose (`substTerms_comp`), and only the variables a formula's terms mention matter (`substTerms_congr`). A family
  over a variable is a formula read at a value (`Formula.at`).
- **Dependent contexts** (`DepContext`): variables in order, each with its sort and a refinement that may mention
  the variables before it; a valuation gives each a closed value of its sort satisfying its refinement read at the
  earlier values (`DepValuation`). **The judgment `Γ ⊢ t : φ`** (`DepHolds`): at every valuation, the instance of
  the term satisfies the instance of the type.
- **Substitution in the index** (`depHolds_subst`): a substitution between dependent contexts carries a judgment
  along, substituting into the term and into the type alike.
- **Dependent products and sums** (`DepPi`, `DepSigma`) of a family over a refined sort, with their generated rules:
  introduction from the extended context (`depPi_intro`), elimination at a value (`depPi_elim`), introduction by a
  witness (`depSigma_intro`), elimination into a type that does not mention the variable (`depSigma_elim`). At the
  empty context they are the judgments over a type (`depPi_nil_iff`, `depSigma_nil_iff`), which the front door
  decides over complete fibres.
- **Parametric types** (`ParamHolds`, `SortParamHolds`): a formula in a type parameter holds of a term for every
  predicate as the parameter, or every predicate on a sort's values. Generated formulas are monotone in their
  variables, so the parameter is read with both polarities: the predicate at the positive variable `0`, its
  complement at the negative variable `1` (`polarEnv`). They are eliminated at any formula, or any type of the sort,
  with its dual at the negative variable (`paramHolds_instantiate`, `sortParamHolds_instantiate`), through the
  substitution lemma of the logic. A parameter that occurs only positively carries nothing: such a type is its
  instance at falsity (`covariantParamHolds_iff_bot`).
- **The front door for dependent judgments** (`askDep`): over complete fibres, a dependent judgment is checked at
  every candidate valuation, wherever the refinements hold (`depHolds_iff_candidates`). The front door asks each
  refinement and each instance of the type: a proof answers when every candidate is settled, a refutation answers at
  a candidate whose refinements it proves (`askDep_proved`, `askDep_refuted`), and when it decides every refinement
  and instance it decides the judgment (`askDep_decided`).
- **Parametric types at the front door** (`askSortParam`): over a discrete fibre, whose values are named by
  themselves alone (`DiscreteFibre`, `constantDiscreteFibres`), the predicates on the sort are the sublists of its
  values, so a bounded parametric type is its instances there (`sortParamHolds_iff_sublists`). The front door asks
  each: a proof when it proves all, a refutation at a predicate where it refutes one (`askSortParam_proved`,
  `askSortParam_refuted`), decided when each instance is (`askSortParam_decided`). A covariant type is decided at
  its least instance (`askCovariantParam`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.FiniteModels (Signature)

/-! ## Terms inside types -/

namespace Formula

mutual
/-- **Terms substituted into a formula**: its named terms, with values for their free variables. -/
def substTerms (assignment : String → Pattern) : {n : ℕ} → Formula n → Formula n
  | _, .top => .top
  | _, .bot => .bot
  | _, .and left right => .and (substTerms assignment left) (substTerms assignment right)
  | _, .or left right => .or (substTerms assignment left) (substTerms assignment right)
  | _, .var index => .var index
  | _, .mu inner => .mu (substTerms assignment inner)
  | _, .nu inner => .nu (substTerms assignment inner)
  | _, .possibly label inner => .possibly label (substTerms assignment inner)
  | _, .necessarily label inner => .necessarily label (substTerms assignment inner)
  | _, .sometimeBefore label inner => .sometimeBefore label (substTerms assignment inner)
  | _, .alwaysBefore label inner => .alwaysBefore label (substTerms assignment inner)
  | _, .atLeast count direction label inner => .atLeast count direction label (substTerms assignment inner)
  | _, .allButFewer count direction label inner => .allButFewer count direction label (substTerms assignment inner)
  | _, .built constructor arguments => .built constructor (substTermsList assignment arguments)
  | _, .everyBuilt constructor arguments => .everyBuilt constructor (substTermsList assignment arguments)
  | _, .split kind left right => .split kind (substTerms assignment left) (substTerms assignment right)
  | _, .everySplit kind left right => .everySplit kind (substTerms assignment left) (substTerms assignment right)
  | _, .empty kind => .empty kind
  | _, .nonEmpty kind => .nonEmpty kind
  | _, .single kind inner => .single kind (substTerms assignment inner)
  | _, .everySingle kind inner => .everySingle kind (substTerms assignment inner)
  | _, .body inner => .body (substTerms assignment inner)
  | _, .everyBody inner => .everyBody (substTerms assignment inner)
  | _, .multiBody arity inner => .multiBody arity (substTerms assignment inner)
  | _, .everyMultiBody arity inner => .everyMultiBody arity (substTerms assignment inner)
  | _, .bound index => .bound index
  | _, .notBound index => .notBound index
  | _, .typed type => .typed type
  | _, .untyped type => .untyped type
  | _, .is term => .is (freeSubst assignment term)
  | _, .isNot term => .isNot (freeSubst assignment term)
  | _, .mapsAll argument result => .mapsAll (substTerms assignment argument) (substTerms assignment result)
  | _, .mapsSome argument result => .mapsSome (substTerms assignment argument) (substTerms assignment result)
  | _, .someOf type inner => .someOf type (substTerms assignment inner)
  | _, .everyOf type inner => .everyOf type (substTerms assignment inner)
  | _, .inRelation relation => .inRelation relation
  | _, .notInRelation relation => .notInRelation relation

/-- Terms substituted into each formula of a list. -/
def substTermsList (assignment : String → Pattern) : {n : ℕ} → Formulas n → Formulas n
  | _, .nil => .nil
  | _, .cons formula formulas => .cons (substTerms assignment formula) (substTermsList assignment formulas)
end

mutual
/-- **The free variables of a formula's named terms lie among the names.** -/
def termsWithin (names : List String) : {n : ℕ} → Formula n → Bool
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right
  | _, .mapsAll left right | _, .mapsSome left right => termsWithin names left && termsWithin names right
  | _, .mu inner | _, .nu inner | _, .possibly _ inner | _, .necessarily _ inner | _, .sometimeBefore _ inner
  | _, .alwaysBefore _ inner | _, .atLeast _ _ _ inner | _, .allButFewer _ _ _ inner | _, .single _ inner
  | _, .everySingle _ inner | _, .body inner | _, .everyBody inner | _, .multiBody _ inner
  | _, .everyMultiBody _ inner | _, .someOf _ inner | _, .everyOf _ inner => termsWithin names inner
  | _, .built _ arguments | _, .everyBuilt _ arguments => termsWithinList names arguments
  | _, .is term | _, .isNot term => freeWithin names term
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _ | _, .typed _
  | _, .untyped _ | _, .inRelation _ | _, .notInRelation _ => true

/-- Every formula of a list has its terms' free variables among the names. -/
def termsWithinList (names : List String) : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => termsWithin names formula && termsWithinList names formulas
end

mutual
/-- **The identity substitution changes nothing.** -/
theorem substTerms_fvar : ∀ {n : ℕ} (formula : Formula n), substTerms Pattern.fvar formula = formula
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _ | _, .typed _
  | _, .untyped _ | _, .inRelation _ | _, .notInRelation _ => rfl
  | _, .is term | _, .isNot term => by simp only [substTerms, freeSubst_fvar]
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right
  | _, .mapsAll left right | _, .mapsSome left right => by
    simp only [substTerms, substTerms_fvar left, substTerms_fvar right]
  | _, .mu inner | _, .nu inner | _, .possibly _ inner | _, .necessarily _ inner | _, .sometimeBefore _ inner
  | _, .alwaysBefore _ inner | _, .atLeast _ _ _ inner | _, .allButFewer _ _ _ inner | _, .single _ inner
  | _, .everySingle _ inner | _, .body inner | _, .everyBody inner | _, .multiBody _ inner
  | _, .everyMultiBody _ inner | _, .someOf _ inner | _, .everyOf _ inner => by
    simp only [substTerms, substTerms_fvar inner]
  | _, .built _ arguments | _, .everyBuilt _ arguments => by simp only [substTerms, substTermsList_fvar arguments]

theorem substTermsList_fvar : ∀ {n : ℕ} (formulas : Formulas n), substTermsList Pattern.fvar formulas = formulas
  | _, .nil => rfl
  | _, .cons formula formulas => by simp only [substTermsList, substTerms_fvar formula, substTermsList_fvar formulas]
end

mutual
/-- **Substitutions compose.** -/
theorem substTerms_comp (first second : String → Pattern) : ∀ {n : ℕ} (formula : Formula n),
    substTerms second (substTerms first formula) = substTerms (fun name => freeSubst second (first name)) formula
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _ | _, .typed _
  | _, .untyped _ | _, .inRelation _ | _, .notInRelation _ => rfl
  | _, .is term | _, .isNot term => by simp only [substTerms, freeSubst_comp]
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right
  | _, .mapsAll left right | _, .mapsSome left right => by
    simp only [substTerms, substTerms_comp first second left, substTerms_comp first second right]
  | _, .mu inner | _, .nu inner | _, .possibly _ inner | _, .necessarily _ inner | _, .sometimeBefore _ inner
  | _, .alwaysBefore _ inner | _, .atLeast _ _ _ inner | _, .allButFewer _ _ _ inner | _, .single _ inner
  | _, .everySingle _ inner | _, .body inner | _, .everyBody inner | _, .multiBody _ inner
  | _, .everyMultiBody _ inner | _, .someOf _ inner | _, .everyOf _ inner => by
    simp only [substTerms, substTerms_comp first second inner]
  | _, .built _ arguments | _, .everyBuilt _ arguments => by
    simp only [substTerms, substTermsList_comp first second arguments]

theorem substTermsList_comp (first second : String → Pattern) : ∀ {n : ℕ} (formulas : Formulas n),
    substTermsList second (substTermsList first formulas) =
      substTermsList (fun name => freeSubst second (first name)) formulas
  | _, .nil => rfl
  | _, .cons formula formulas => by
    simp only [substTermsList, substTerms_comp first second formula, substTermsList_comp first second formulas]
end

mutual
/-- **Only the variables a formula's terms mention matter.** -/
theorem substTerms_congr {names : List String} {first second : String → Pattern}
    (agree : ∀ name ∈ names, first name = second name) :
    ∀ {n : ℕ} (formula : Formula n), termsWithin names formula = true →
      substTerms first formula = substTerms second formula
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .empty _, _ | _, .nonEmpty _, _ | _, .bound _, _
  | _, .notBound _, _ | _, .typed _, _ | _, .untyped _, _ | _, .inRelation _, _ | _, .notInRelation _, _ => rfl
  | _, .is term, within | _, .isNot term, within => by
    simp only [termsWithin] at within
    simp only [substTerms, freeSubst_congr agree within]
  | _, .and left right, within | _, .or left right, within | _, .split _ left right, within
  | _, .everySplit _ left right, within | _, .mapsAll left right, within | _, .mapsSome left right, within => by
    simp only [termsWithin, Bool.and_eq_true] at within
    simp only [substTerms, substTerms_congr agree left within.1, substTerms_congr agree right within.2]
  | _, .mu inner, within | _, .nu inner, within | _, .possibly _ inner, within | _, .necessarily _ inner, within
  | _, .sometimeBefore _ inner, within | _, .alwaysBefore _ inner, within | _, .atLeast _ _ _ inner, within
  | _, .allButFewer _ _ _ inner, within | _, .single _ inner, within | _, .everySingle _ inner, within
  | _, .body inner, within | _, .everyBody inner, within | _, .multiBody _ inner, within
  | _, .everyMultiBody _ inner, within | _, .someOf _ inner, within | _, .everyOf _ inner, within => by
    simp only [termsWithin] at within
    simp only [substTerms, substTerms_congr agree inner within]
  | _, .built _ arguments, within | _, .everyBuilt _ arguments, within => by
    simp only [termsWithin] at within
    simp only [substTerms, substTermsList_congr agree arguments within]

theorem substTermsList_congr {names : List String} {first second : String → Pattern}
    (agree : ∀ name ∈ names, first name = second name) :
    ∀ {n : ℕ} (formulas : Formulas n), termsWithinList names formulas = true →
      substTermsList first formulas = substTermsList second formulas
  | _, .nil, _ => rfl
  | _, .cons formula formulas, within => by
    simp only [termsWithinList, Bool.and_eq_true] at within
    simp only [substTermsList, substTerms_congr agree formula within.1, substTermsList_congr agree formulas within.2]
end

/-- **A family over a variable**: the formula read with the variable at a value. -/
def «at» (name : String) (value : Pattern) (formula : Formula 0) : Formula 0 :=
  formula.substTerms (_root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.single name value)

end Formula

/-- An assignment with one more variable. -/
def extendAt (assignment : String → Pattern) (name : String) (value : Pattern) : String → Pattern :=
  fun other => if other = name then value else assignment other

theorem freeSubst_single (assignment : String → Pattern) (name : String) (value : Pattern) :
    (fun other => freeSubst assignment (single name value other)) = extendAt assignment name (freeSubst assignment value) := by
  funext other
  by_cases same : other = name
  · simp [single, extendAt, same]
  · simp [single, extendAt, same, freeSubst]

/-! ## Dependent contexts and the judgment -/

/-- **A dependent context**: variables in order, each with its sort and a refinement that may mention the variables
before it. -/
abbrev DepContext := List (String × TypeExpr × Formula 0)

/-- The variables of a dependent context. -/
def DepContext.names (context : DepContext) : List String := context.map Prod.fst

variable (T : NativeStructure Pattern)

/-- **A valuation of a dependent context**: a closed value of each variable's sort satisfying its refinement read at
the valuation; every other name is left as it is. -/
def DepValuation (context : DepContext) (assignment : String → Pattern) : Prop :=
  (∀ entry ∈ context, ClosedValue (assignment entry.1) ∧ T.typed (assignment entry.1) entry.2.1 ∧
      T.sat Env.closed (entry.2.2.substTerms assignment) (assignment entry.1)) ∧
    ∀ name, name ∉ context.names → assignment name = .fvar name

/-- **The judgment `Γ ⊢ t : φ` over a dependent context**: at every valuation, the instance of the term satisfies the
instance of the type. -/
def DepHolds (context : DepContext) (formula : Formula 0) (term : Pattern) : Prop :=
  ∀ assignment, DepValuation T context assignment →
    T.sat Env.closed (formula.substTerms assignment) (freeSubst assignment term)

/-- **A substitution between dependent contexts**: images of the target's variables whose instances under every
valuation of the source form a valuation of the target. -/
def DepSubstitution (source target : DepContext) (images : String → Pattern) : Prop :=
  ∀ assignment, DepValuation T source assignment →
    DepValuation T target (fun name => if name ∈ target.names then freeSubst assignment (images name) else .fvar name)

variable {T}

/-- **Substitution in the index**: a judgment over the target carries to the source, substituted into the term and
into the type alike, when the term and the type's terms mention only the target's variables. -/
theorem depHolds_subst {source target : DepContext} {images : String → Pattern} {formula : Formula 0} {term : Pattern}
    (holds : DepHolds T target formula term) (termWithin : freeWithin target.names term = true)
    (formulaWithin : formula.termsWithin target.names = true) (substitution : DepSubstitution T source target images) :
    DepHolds T source (formula.substTerms images) (freeSubst images term) := by
  intro assignment valuation
  have instance' := holds _ (substitution assignment valuation)
  have agree : ∀ name ∈ target.names,
      (if name ∈ target.names then freeSubst assignment (images name) else .fvar name) =
        freeSubst assignment (images name) := fun name member => by simp only [member, if_true]
  rw [Formula.substTerms_congr agree formula formulaWithin, freeSubst_congr agree termWithin] at instance'
  rwa [Formula.substTerms_comp, freeSubst_comp]

/-! ## Dependent products and sums -/

variable (T)

/-- **The dependent product** of a family over a refined sort: at every valuation of the context and every closed value
of the sort satisfying the refinement, the instance of the term satisfies the family at that value. -/
def DepPi (context : DepContext) (name : String) (sort : TypeExpr) (refinement family : Formula 0) (term : Pattern) :
    Prop :=
  ∀ assignment, DepValuation T context assignment → ∀ value, ClosedValue value → T.typed value sort →
    T.sat Env.closed (refinement.substTerms assignment) value →
      T.sat Env.closed (family.substTerms (extendAt assignment name value)) (freeSubst assignment term)

/-- **The dependent sum** of a family over a refined sort: at every valuation, some closed value of the sort
satisfying the refinement has the instance of the term satisfy the family at it. -/
def DepSigma (context : DepContext) (name : String) (sort : TypeExpr) (refinement family : Formula 0) (term : Pattern) :
    Prop :=
  ∀ assignment, DepValuation T context assignment → ∃ value, ClosedValue value ∧ T.typed value sort ∧
    T.sat Env.closed (refinement.substTerms assignment) value ∧
      T.sat Env.closed (family.substTerms (extendAt assignment name value)) (freeSubst assignment term)

variable {T}

/-- **Π introduction**: a judgment in the context extended by the variable gives the dependent product. -/
theorem depPi_intro {context : DepContext} {name : String} {sort : TypeExpr} {refinement family : Formula 0}
    {term : Pattern} (fresh : name ∉ context.names)
    (entriesScoped : ∀ entry ∈ context, entry.2.2.termsWithin context.names = true)
    (refinementWithin : refinement.termsWithin context.names = true) (termWithin : freeWithin context.names term = true)
    (holds : DepHolds T (context ++ [(name, sort, refinement)]) family term) :
    DepPi T context name sort refinement family term := by
  intro assignment valuation value closedValue typedValue refined
  have agree : ∀ other ∈ context.names, extendAt assignment name value other = assignment other := fun other member => by
    have different : other ≠ name := fun same => fresh (same ▸ member)
    simp only [extendAt, different, if_false]
  have extended : DepValuation T (context ++ [(name, sort, refinement)]) (extendAt assignment name value) := by
    refine ⟨fun entry member => ?_, fun other outside => ?_⟩
    · rcases List.mem_append.mp member with inside | last
      · have entryName : entry.1 ∈ context.names := List.mem_map_of_mem inside
        rw [agree entry.1 entryName, Formula.substTerms_congr agree _ (entriesScoped entry inside)]
        exact valuation.1 entry inside
      · rw [List.mem_singleton.mp last]
        simp only [extendAt, if_true]
        rw [Formula.substTerms_congr agree _ refinementWithin]
        exact ⟨closedValue, typedValue, refined⟩
    · have notOld : other ∉ context.names := fun member => outside (by
        simp only [DepContext.names, List.map_append, List.mem_append]
        exact Or.inl member)
      have notNew : other ≠ name := fun same => outside (by
        simp only [DepContext.names, List.map_append, List.mem_append, List.map_cons, List.map_nil,
          List.mem_singleton]
        exact Or.inr same)
      simp only [extendAt, notNew, if_false]
      exact valuation.2 other notOld
  have instance' := holds _ extended
  rwa [freeSubst_congr agree termWithin] at instance'

/-- **Π elimination**: the dependent product read at a value of the sort satisfying the refinement. -/
theorem depPi_elim {context : DepContext} {name : String} {sort : TypeExpr} {refinement family : Formula 0}
    {term argument : Pattern} (product : DepPi T context name sort refinement family term)
    (argumentTyped : ∀ assignment, DepValuation T context assignment →
      ClosedValue (freeSubst assignment argument) ∧ T.typed (freeSubst assignment argument) sort ∧
        T.sat Env.closed (refinement.substTerms assignment) (freeSubst assignment argument)) :
    DepHolds T context (family.«at» name argument) term := by
  intro assignment valuation
  obtain ⟨closedValue, typedValue, refined⟩ := argumentTyped assignment valuation
  have instance' := product assignment valuation _ closedValue typedValue refined
  rwa [Formula.«at», Formula.substTerms_comp, freeSubst_single]

/-- **Σ introduction**: a witness of the sort satisfying the refinement at which the term has the family. -/
theorem depSigma_intro {context : DepContext} {name : String} {sort : TypeExpr} {refinement family : Formula 0}
    {term witness : Pattern}
    (witnessTyped : ∀ assignment, DepValuation T context assignment →
      ClosedValue (freeSubst assignment witness) ∧ T.typed (freeSubst assignment witness) sort ∧
        T.sat Env.closed (refinement.substTerms assignment) (freeSubst assignment witness))
    (holds : DepHolds T context (family.«at» name witness) term) :
    DepSigma T context name sort refinement family term := by
  intro assignment valuation
  obtain ⟨closedValue, typedValue, refined⟩ := witnessTyped assignment valuation
  have instance' := holds assignment valuation
  rw [Formula.«at», Formula.substTerms_comp, freeSubst_single] at instance'
  exact ⟨_, closedValue, typedValue, refined, instance'⟩

/-- **Σ elimination**: a type that every instance of the family implies, at every value, holds of the term. -/
theorem depSigma_elim {context : DepContext} {name : String} {sort : TypeExpr} {refinement family conclusion : Formula 0}
    {term : Pattern} (sum : DepSigma T context name sort refinement family term)
    (implies : ∀ assignment, DepValuation T context assignment → ∀ value, ClosedValue value → T.typed value sort →
      T.sat Env.closed (refinement.substTerms assignment) value →
      T.sat Env.closed (family.substTerms (extendAt assignment name value)) (freeSubst assignment term) →
        T.sat Env.closed (conclusion.substTerms assignment) (freeSubst assignment term)) :
    DepHolds T context conclusion term := by
  intro assignment valuation
  obtain ⟨value, closedValue, typedValue, refined, holds⟩ := sum assignment valuation
  exact implies assignment valuation value closedValue typedValue refined holds

/-! ## The judgments over a type, at the empty context -/

theorem depValuation_nil_iff (assignment : String → Pattern) : DepValuation T [] assignment ↔ assignment = .fvar := by
  constructor
  · rintro ⟨-, outside⟩
    funext name
    exact outside name (by simp [DepContext.names])
  · rintro rfl
    exact ⟨fun _ member => (nomatch member), fun _ _ => rfl⟩

theorem extendAt_fvar (name : String) (value : Pattern) : extendAt Pattern.fvar name value = single name value := by
  funext other
  simp only [extendAt, single]

/-- **At the empty context the dependent product is Π over the sort**, of the family read at each value. -/
theorem depPi_nil_iff {name : String} {sort : TypeExpr} {family : Formula 0} {term : Pattern} :
    DepPi T [] name sort .top family term ↔ PiHolds T sort (fun value => family.«at» name value) term := by
  constructor
  · intro product value closedValue typedValue
    have instance' := product _ ((depValuation_nil_iff _).mpr rfl) value closedValue typedValue trivial
    rwa [extendAt_fvar, freeSubst_fvar] at instance'
  · intro pi assignment valuation value closedValue typedValue _
    obtain rfl := (depValuation_nil_iff assignment).mp valuation
    rw [extendAt_fvar, freeSubst_fvar]
    exact pi value closedValue typedValue

/-- **At the empty context the dependent sum is Σ over the sort.** -/
theorem depSigma_nil_iff {name : String} {sort : TypeExpr} {family : Formula 0} {term : Pattern} :
    DepSigma T [] name sort .top family term ↔ SigmaHolds T sort (fun value => family.«at» name value) term := by
  constructor
  · intro sum
    obtain ⟨value, closedValue, typedValue, _, holds⟩ := sum _ ((depValuation_nil_iff _).mpr rfl)
    rw [extendAt_fvar, freeSubst_fvar] at holds
    exact ⟨value, closedValue, typedValue, holds⟩
  · rintro ⟨value, closedValue, typedValue, holds⟩ assignment valuation
    obtain rfl := (depValuation_nil_iff assignment).mp valuation
    refine ⟨value, closedValue, typedValue, trivial, ?_⟩
    rw [extendAt_fvar, freeSubst_fvar]
    exact holds

/-! ## Parametric types -/

section Parametric

/-- **A parameter read with both polarities**: a predicate at the positive variable `0` and its complement at the
negative variable `1`. -/
def polarEnv {Carrier : Type*} (predicate : Set Carrier) : Env Carrier 2 :=
  fun index => if index = 0 then predicate else predicateᶜ

/-- **The instance at a formula**: the formula at the positive variable, its dual at the negative one. -/
def polarSubst (argument : Formula 0) : Fin 2 → Formula 0 :=
  fun index => if index = 0 then argument else argument.dual

theorem truthSets_polarSubst (argument : Formula 0) :
    T.truthSets Env.closed (polarSubst argument) = polarEnv {element | T.sat Env.closed argument element} := by
  funext index
  by_cases positive : index = 0
  · simp [NativeStructure.truthSets, polarSubst, polarEnv, positive]
  · ext element
    simp [NativeStructure.truthSets, polarSubst, polarEnv, positive, T.sat_dual_closed]

variable (T)

/-- **A parametric type**: a formula in one type parameter, positive at `var 0` and negative at `var 1`, holds of a
term for every predicate as the parameter. -/
def ParamHolds (formula : Formula 2) (term : Pattern) : Prop :=
  ∀ predicate : Set Pattern, T.sat (polarEnv predicate) formula term

/-- **A parametric type bounded by a sort**: the parameter ranges over the predicates on the sort's closed values. -/
def SortParamHolds (sort : TypeExpr) (formula : Formula 2) (term : Pattern) : Prop :=
  ∀ predicate : Set Pattern, (∀ value ∈ predicate, ClosedValue value ∧ T.typed value sort) →
    T.sat (polarEnv predicate) formula term

/-- **A covariant parametric type**: the parameter occurs only positively. -/
def CovariantParamHolds (formula : Formula 1) (term : Pattern) : Prop :=
  ∀ predicate : Set Pattern, T.sat (fun _ => predicate) formula term

variable {T}

/-- **A parametric type is eliminated at any formula**: its instance there holds. -/
theorem paramHolds_instantiate {formula : Formula 2} {term : Pattern} (holds : ParamHolds T formula term)
    (argument : Formula 0) : T.sat Env.closed (formula.subst (polarSubst argument)) term := by
  rw [T.sat_subst, truthSets_polarSubst]
  exact holds _

theorem sortParamHolds_of_paramHolds {sort : TypeExpr} {formula : Formula 2} {term : Pattern}
    (holds : ParamHolds T formula term) : SortParamHolds T sort formula term :=
  fun predicate _ => holds predicate

/-- **A bounded parametric type is eliminated at any type of the sort.** -/
theorem sortParamHolds_instantiate {sort : TypeExpr} {formula : Formula 2} {term : Pattern}
    (holds : SortParamHolds T sort formula term) (argument : Formula 0)
    (within : ∀ value, T.sat Env.closed argument value → ClosedValue value ∧ T.typed value sort) :
    T.sat Env.closed (formula.subst (polarSubst argument)) term := by
  rw [T.sat_subst, truthSets_polarSubst]
  exact holds _ within

/-- **A covariant parametric type is eliminated at any formula.** -/
theorem covariantParamHolds_instantiate {formula : Formula 1} {term : Pattern}
    (holds : CovariantParamHolds T formula term) (argument : Formula 0) :
    T.sat Env.closed (formula.subst fun _ => argument) term :=
  (T.sat_subst (fun _ => argument) formula Env.closed term).mpr (holds _)

/-- **A covariant parametric type is its least instance**: every formula is monotone in its variables, so it holds
for every predicate exactly when it holds for the empty one, its instance at falsity. A parameter carries something
only through its negative occurrences. -/
theorem covariantParamHolds_iff_bot {formula : Formula 1} {term : Pattern} :
    CovariantParamHolds T formula term ↔ T.sat Env.closed (formula.subst fun _ => .bot) term := by
  refine ⟨fun holds => covariantParamHolds_instantiate holds .bot, fun least predicate => ?_⟩
  exact T.sat_mono formula (fun _ _ impossible => impossible.elim) term
    ((T.sat_subst (fun _ => .bot) formula Env.closed term).mp least)

end Parametric

/-! ## The front door for dependent judgments -/

section Candidates

/-- Every sort of the dependent context has a fibre. -/
def depCovered (fibreOf : (type : TypeExpr) → Option (Fibre T type)) (context : DepContext) : Bool :=
  context.all fun entry => (fibreOf entry.2.1).isSome

/-- **The candidate valuations of a dependent context**: a value from each variable's fibre, in order. -/
def depCandidates (fibreOf : (type : TypeExpr) → Option (Fibre T type)) : DepContext → List (List (String × Pattern))
  | [] => [[]]
  | (name, sort, _) :: context =>
    (fibreValues fibreOf sort).flatMap fun value => (depCandidates fibreOf context).map ((name, value) :: ·)

/-- The assignment a list of values gives: its value for each listed name, every other name left as it is. -/
def depAssignment (values : List (String × Pattern)) : String → Pattern :=
  fun name => (values.lookup name).getD (.fvar name)

theorem fibreValues_sound {fibreOf : (type : TypeExpr) → Option (Fibre T type)} {type : TypeExpr} {value : Pattern}
    (member : value ∈ fibreValues fibreOf type) : ClosedValue value ∧ T.typed value type := by
  unfold fibreValues at member
  split at member
  · rename_i fibre _
    exact fibre.sound value member
  · cases member

theorem fibreValues_complete {fibreOf : (type : TypeExpr) → Option (Fibre T type)} {type : TypeExpr}
    (covers : (fibreOf type).isSome = true) {value : Pattern} (closed : ClosedValue value) (typed : T.typed value type) :
    value ∈ fibreValues fibreOf type := by
  obtain ⟨fibre, found⟩ := Option.isSome_iff_exists.mp covers
  simp only [fibreValues, found]
  exact fibre.complete value closed typed

/-- A candidate valuation pairs each variable, in order, with a value of its fibre. -/
abbrev CandidateFor (fibreOf : (type : TypeExpr) → Option (Fibre T type)) (pair : String × Pattern)
    (entry : String × TypeExpr × Formula 0) : Prop :=
  pair.1 = entry.1 ∧ pair.2 ∈ fibreValues fibreOf entry.2.1

theorem mem_depCandidates_iff (fibreOf : (type : TypeExpr) → Option (Fibre T type)) :
    ∀ (context : DepContext) (values : List (String × Pattern)),
      values ∈ depCandidates fibreOf context ↔ List.Forall₂ (CandidateFor fibreOf) values context
  | [], values => by simp [depCandidates]
  | (name, sort, refinement) :: context, values => by
    simp only [depCandidates, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨value, member, rest, restMem, rfl⟩
      exact .cons ⟨rfl, member⟩ ((mem_depCandidates_iff fibreOf context rest).mp restMem)
    · rintro (_ | ⟨⟨same, member⟩, tail⟩)
      rename_i pair rest
      obtain ⟨key, value⟩ := pair
      obtain rfl : key = name := same
      exact ⟨value, member, rest, (mem_depCandidates_iff fibreOf context rest).mpr tail, rfl⟩

theorem lookup_of_candidate {fibreOf : (type : TypeExpr) → Option (Fibre T type)} :
    ∀ {values : List (String × Pattern)} {context : DepContext}, List.Forall₂ (CandidateFor fibreOf) values context →
      (DepContext.names context).Nodup → ∀ entry ∈ context,
        ∃ value, values.lookup entry.1 = some value ∧ value ∈ fibreValues fibreOf entry.2.1
  | _, _, .nil, _, _, member => nomatch member
  | (key, value) :: _, head :: context, .cons ⟨same, member⟩ tail, nodup, entry, entryMem => by
    have fresh : head.1 ∉ DepContext.names context := (List.nodup_cons.mp nodup).1
    rcases List.mem_cons.mp entryMem with rfl | inside
    · have beqTrue : (entry.1 == key) = true := beq_iff_eq.mpr same.symm
      exact ⟨value, by simp only [List.lookup, beqTrue], member⟩
    · have different : entry.1 ≠ key := fun equal =>
        fresh (same ▸ equal ▸ List.mem_map_of_mem (f := Prod.fst) inside)
      have beqFalse : (entry.1 == key) = false := beq_false_of_ne different
      obtain ⟨found, lookup, foundMem⟩ := lookup_of_candidate tail (List.nodup_cons.mp nodup).2 entry inside
      exact ⟨found, by simp only [List.lookup, beqFalse, lookup], foundMem⟩

theorem lookup_none_of_candidate {fibreOf : (type : TypeExpr) → Option (Fibre T type)} {name : String} :
    ∀ {values : List (String × Pattern)} {context : DepContext}, List.Forall₂ (CandidateFor fibreOf) values context →
      name ∉ context.names → values.lookup name = none
  | _, _, .nil, _ => rfl
  | (key, _) :: _, head :: _, .cons ⟨same, _⟩ tail, outside => by
    have different : name ≠ key := fun equal => outside (by subst equal; exact List.mem_cons.mpr (Or.inl same))
    have outside' : name ∉ DepContext.names _ := fun member => outside (List.mem_cons_of_mem _ member)
    have beqFalse : (name == key) = false := beq_false_of_ne different
    simp only [List.lookup, beqFalse, lookup_none_of_candidate tail outside']

theorem lookup_map_names (assignment : String → Pattern) (name : String) :
    ∀ context : DepContext, (context.map fun entry => (entry.1, assignment entry.1)).lookup name =
      if name ∈ context.names then some (assignment name) else none
  | [] => by simp [DepContext.names]
  | entry :: context => by
    by_cases same : name = entry.1
    · simp [same, DepContext.names]
    · have rest := lookup_map_names assignment name context
      have beqFalse : (name == entry.1) = false := beq_false_of_ne same
      simp only [DepContext.names] at rest
      simp only [List.map_cons, List.lookup, beqFalse, rest, DepContext.names, List.mem_cons, same, false_or]
      by_cases inside : name ∈ List.map Prod.fst context <;> simp [inside]

/-- **Over complete fibres, a dependent judgment is checked at every candidate valuation**: wherever the refinements
hold, the type's instance holds of the term's. -/
theorem depHolds_iff_candidates (fibreOf : (type : TypeExpr) → Option (Fibre T type)) {context : DepContext}
    {formula : Formula 0} {term : Pattern} (nodup : context.names.Nodup) (covers : depCovered fibreOf context = true) :
    DepHolds T context formula term ↔ ∀ values ∈ depCandidates fibreOf context,
      (∀ entry ∈ context, T.sat Env.closed (entry.2.2.substTerms (depAssignment values)) (depAssignment values entry.1)) →
        T.sat Env.closed (formula.substTerms (depAssignment values)) (freeSubst (depAssignment values) term) := by
  constructor
  · intro holds values member refined
    have candidate := (mem_depCandidates_iff fibreOf context values).mp member
    refine holds _ ⟨fun entry entryMem => ?_, fun name outside => ?_⟩
    · obtain ⟨value, lookup, valueMem⟩ := lookup_of_candidate candidate nodup entry entryMem
      have assigned : depAssignment values entry.1 = value := by simp [depAssignment, lookup]
      have third := refined entry entryMem
      rw [assigned] at third ⊢
      exact ⟨(fibreValues_sound valueMem).1, (fibreValues_sound valueMem).2, third⟩
    · simp [depAssignment, lookup_none_of_candidate candidate outside]
  · intro checks assignment valuation
    have recovered : depAssignment (context.map fun entry => (entry.1, assignment entry.1)) = assignment := by
      funext name
      simp only [depAssignment, lookup_map_names]
      split
      · rfl
      · rename_i outside
        exact (valuation.2 name outside).symm
    have member : (context.map fun entry => (entry.1, assignment entry.1)) ∈ depCandidates fibreOf context := by
      refine (mem_depCandidates_iff fibreOf context _).mpr (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr ?_))
      intro entry entryMem
      have covered : (fibreOf entry.2.1).isSome = true := List.all_eq_true.mp covers entry entryMem
      exact ⟨rfl, fibreValues_complete covered (valuation.1 entry entryMem).1 (valuation.1 entry entryMem).2.1⟩
    have instance' := checks _ member (by
      rw [recovered]
      exact fun entry entryMem => (valuation.1 entry entryMem).2.2)
    rwa [recovered] at instance'

end Candidates

/-! ## Discrete fibres -/

section Discrete

/-- **A discrete fibre**: each of its values is named by itself alone. -/
structure DiscreteFibre (T : NativeStructure Pattern) (type : TypeExpr) extends Fibre T type where
  named_iff : ∀ value ∈ values, ∀ other, T.named other value ↔ other = value

/-- The predicate a list of values names. -/
def namedBy (members : List Pattern) : Formula 0 := bigOr (members.map .is)

theorem sat_namedBy {type : TypeExpr} (fibre : DiscreteFibre T type) {members : List Pattern}
    (sub : members ⊆ fibre.values) (element : Pattern) :
    T.sat Env.closed (namedBy members) element ↔ element ∈ members := by
  rw [namedBy, sat_bigOr]
  constructor
  · rintro ⟨_, member, holds⟩
    obtain ⟨value, valueMem, rfl⟩ := List.mem_map.mp member
    simp only [NativeStructure.sat] at holds
    rw [(fibre.named_iff value (sub valueMem) element).mp holds]
    exact valueMem
  · intro member
    refine ⟨.is element, List.mem_map.mpr ⟨element, member, rfl⟩, ?_⟩
    simp only [NativeStructure.sat]
    exact (fibre.named_iff element (sub member) element).mpr rfl

/-- **Over a discrete fibre, a bounded parametric type is its instances at the predicates the sublists of the fibre
name.** -/
theorem sortParamHolds_iff_sublists {sort : TypeExpr} (fibre : DiscreteFibre T sort) (formula : Formula 2)
    (term : Pattern) :
    SortParamHolds T sort formula term ↔
      ∀ members ∈ fibre.values.sublists, T.sat Env.closed (formula.subst (polarSubst (namedBy members))) term := by
  constructor
  · intro holds members member
    have sub : members ⊆ fibre.values := (List.mem_sublists.mp member).subset
    exact sortParamHolds_instantiate holds _ fun value named =>
      fibre.sound value (sub ((sat_namedBy fibre sub value).mp named))
  · intro instances predicate within
    classical
    have sublist : List.Sublist (fibre.values.filter fun value => decide (value ∈ predicate)) fibre.values :=
      List.filter_sublist
    have holds := instances _ (List.mem_sublists.mpr sublist)
    rw [T.sat_subst, truthSets_polarSubst] at holds
    have same : {element | T.sat Env.closed (namedBy (fibre.values.filter fun value => decide (value ∈ predicate)))
        element} = predicate := by
      ext element
      rw [Set.mem_ofPred_eq, sat_namedBy fibre sublist.subset, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun found => found.2, fun inside =>
        ⟨fibre.complete element (within element inside).1 (within element inside).2, inside⟩⟩
    rwa [same] at holds

/-- **The discrete fibre of a constant sort** in an equation-free language. -/
def constantDiscreteFibre (relEnv : RelationEnv) (language : LanguageDef) (reading : LanguageReading) (sort : String)
    (constant : constantSort language sort = true) (free : language.isEquationFree = true) :
    DiscreteFibre (referenceStructure relEnv language reading) (.base sort) :=
  { constantFibre relEnv language reading sort constant free with
    named_iff := fun value member other => by
      constructor
      · rintro ⟨_, equivalent⟩
        exact (objectEquivalent_iff_eq_of_isEquationFree free).mp equivalent
      · intro same
        subst same
        exact ⟨((constantFibre relEnv language reading sort constant free).sound _ member).2.1,
          (objectEquivalent_iff_eq_of_isEquationFree free).mpr rfl⟩ }

/-- **The discrete fibres of the constant sorts** of an equation-free language. -/
def constantDiscreteFibres (relEnv : RelationEnv) (language : LanguageDef) (reading : LanguageReading) :
    (type : TypeExpr) → Option (DiscreteFibre (referenceStructure relEnv language reading) type)
  | .base sort => if h : constantSort language sort = true ∧ language.isEquationFree = true then
      some (constantDiscreteFibre relEnv language reading sort h.1 h.2) else none
  | _ => none

end Discrete

section Ask

variable (relEnv : RelationEnv) (signature : Signature) (language : LanguageDef) (fuel : ℕ)
  (forms : Option (CanonicalForms relEnv language fuel)) (hint : Option CertificateCandidate) (rounds : ℕ)

/-- The front door's verdict on a refinement at a candidate valuation. -/
def refinementAnswer (values : List (String × Pattern)) (entry : String × TypeExpr × Formula 0) : Answer :=
  ask relEnv signature language fuel (entry.2.2.substTerms (depAssignment values)) (depAssignment values entry.1) hint
    rounds forms

/-- The front door's verdict on the type's instance at the term's, at a candidate valuation. -/
def instanceAnswer (formula : Formula 0) (term : Pattern) (values : List (String × Pattern)) : Answer :=
  ask relEnv signature language fuel (formula.substTerms (depAssignment values)) (freeSubst (depAssignment values) term)
    hint rounds forms

/-- **A candidate valuation is settled** when the front door refutes one of its refinements, or proves all of them
and the type's instance. -/
def candidateSettled (context : DepContext) (formula : Formula 0) (term : Pattern) (values : List (String × Pattern)) :
    Bool :=
  context.any (fun entry => (refinementAnswer relEnv signature language fuel forms hint rounds values entry).refutation.isSome) ||
    (context.all (fun entry => (refinementAnswer relEnv signature language fuel forms hint rounds values entry).isProved) &&
      (instanceAnswer relEnv signature language fuel forms hint rounds formula term values).isProved)

/-- **A counterexample at a candidate valuation**: the front door proves its refinements and refutes the type's
instance. -/
def candidateCounter (context : DepContext) (formula : Formula 0) (term : Pattern) (values : List (String × Pattern)) :
    Option (Pattern × Evidence) :=
  if context.all (fun entry => (refinementAnswer relEnv signature language fuel forms hint rounds values entry).isProved) then
    (instanceAnswer relEnv signature language fuel forms hint rounds formula term values).refutation.map fun evidence =>
      (freeSubst (depAssignment values) term, evidence)
  else none

/-- **The front door for the dependent judgment `Γ ⊢ t : φ`**: over complete fibres, every candidate valuation
settled proves it, and a counterexample refutes it at its instance. -/
def askDep (fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type))
    (context : DepContext) (formula : Formula 0) (term : Pattern) : JudgmentAnswer :=
  if decide context.names.Nodup && depCovered fibreOf context then
    if (depCandidates fibreOf context).all (candidateSettled relEnv signature language fuel forms hint rounds context formula term)
    then .proved (.instances (depCandidates fibreOf context).length)
    else match (depCandidates fibreOf context).findSome?
        (candidateCounter relEnv signature language fuel forms hint rounds context formula term) with
      | some (instantiated, evidence) => .refuted (.atInstance instantiated evidence)
      | none => .unknown
  else .unknown

/-- **The front door for a covariant parametric type**: its verdict on the least instance. -/
def askCovariantParam (formula : Formula 1) (term : Pattern) : Answer :=
  ask relEnv signature language fuel (formula.subst fun _ => .bot) term hint rounds forms

/-- The front door's verdict on a parametric type's instance at the predicate a list of values names. -/
def predicateAnswer (formula : Formula 2) (term : Pattern) (members : List Pattern) : Answer :=
  ask relEnv signature language fuel (formula.subst (polarSubst (namedBy members))) term hint rounds forms

/-- A refutation at the predicate a list of values names. -/
def predicateCounter (formula : Formula 2) (term : Pattern) (members : List Pattern) : Option (List Pattern × Evidence) :=
  (predicateAnswer relEnv signature language fuel forms hint rounds formula term members).refutation.map
    fun evidence => (members, evidence)

/-- **The front door for a parametric type bounded by a sort**: over a discrete fibre, its verdict at the predicate
each sublist of the fibre names. -/
def askSortParam (fibreOf : (type : TypeExpr) → Option (DiscreteFibre (FrontStructure relEnv language fuel forms) type))
    (sort : TypeExpr) (formula : Formula 2) (term : Pattern) : JudgmentAnswer :=
  match fibreOf sort with
  | some fibre =>
    if fibre.values.sublists.all
        (fun members => (predicateAnswer relEnv signature language fuel forms hint rounds formula term members).isProved)
    then .proved (.instances fibre.values.sublists.length)
    else match fibre.values.sublists.findSome?
        (predicateCounter relEnv signature language fuel forms hint rounds formula term) with
      | some (members, evidence) => .refuted (.atPredicate members evidence)
      | none => .unknown
  | none => .unknown

variable {relEnv signature language fuel forms hint rounds}

/-- **A proved dependent judgment holds.** -/
theorem askDep_proved
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)}
    {context : DepContext} {formula : Formula 0} {term : Pattern} {evidence : JudgmentEvidence}
    (answered : askDep relEnv signature language fuel forms hint rounds fibreOf context formula term = .proved evidence) :
    DepHolds (FrontStructure relEnv language fuel forms) context formula term := by
  unfold askDep at answered
  split at answered
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    split at answered
    · rename_i all
      refine (depHolds_iff_candidates fibreOf guard.1 guard.2).mpr fun values member refined => ?_
      have settled := List.all_eq_true.mp all values member
      simp only [candidateSettled, Bool.or_eq_true, Bool.and_eq_true] at settled
      rcases settled with refutedSome | ⟨_, proved⟩
      · obtain ⟨entry, entryMem, isRefuted⟩ := List.any_eq_true.mp refutedSome
        obtain ⟨_, found⟩ := Option.isSome_iff_exists.mp isRefuted
        exact absurd (refined entry entryMem) (ask_refuted (Answer.refutation_eq found))
      · obtain ⟨_, found⟩ := Answer.isProved_iff.mp proved
        exact ask_proved found
    · split at answered <;> cases answered
  · cases answered

/-- **A refuted dependent judgment fails.** -/
theorem askDep_refuted
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)}
    {context : DepContext} {formula : Formula 0} {term : Pattern} {evidence : JudgmentEvidence}
    (answered : askDep relEnv signature language fuel forms hint rounds fibreOf context formula term = .refuted evidence) :
    ¬ DepHolds (FrontStructure relEnv language fuel forms) context formula term := by
  unfold askDep at answered
  split at answered
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    split at answered
    · cases answered
    · cases found : (depCandidates fibreOf context).findSome?
          (candidateCounter relEnv signature language fuel forms hint rounds context formula term) with
      | none => simp only [found] at answered; cases answered
      | some pair =>
        obtain ⟨values, member, counter⟩ := List.exists_of_findSome?_eq_some found
        unfold candidateCounter at counter
        split at counter
        · rename_i allProved
          obtain ⟨_, refutation, _⟩ := Option.map_eq_some_iff.mp counter
          intro holds
          refine ask_refuted (Answer.refutation_eq refutation)
            ((depHolds_iff_candidates fibreOf guard.1 guard.2).mp holds values member fun entry entryMem => ?_)
          obtain ⟨_, found⟩ := Answer.isProved_iff.mp (List.all_eq_true.mp allProved entry entryMem)
          exact ask_proved found
        · cases counter
  · cases answered

/-- **A proved covariant parametric type holds.** -/
theorem askCovariantParam_proved {formula : Formula 1} {term : Pattern} {evidence : Evidence}
    (answered : askCovariantParam relEnv signature language fuel forms hint rounds formula term = .proved evidence) :
    CovariantParamHolds (FrontStructure relEnv language fuel forms) formula term :=
  covariantParamHolds_iff_bot.mpr (ask_proved answered)

/-- **A refuted covariant parametric type fails.** -/
theorem askCovariantParam_refuted {formula : Formula 1} {term : Pattern} {evidence : Evidence}
    (answered : askCovariantParam relEnv signature language fuel forms hint rounds formula term = .refuted evidence) :
    ¬ CovariantParamHolds (FrontStructure relEnv language fuel forms) formula term :=
  fun holds => ask_refuted answered (covariantParamHolds_iff_bot.mp holds)

/-- **A proved bounded parametric type holds.** -/
theorem askSortParam_proved
    {fibreOf : (type : TypeExpr) → Option (DiscreteFibre (FrontStructure relEnv language fuel forms) type)}
    {sort : TypeExpr} {formula : Formula 2} {term : Pattern} {evidence : JudgmentEvidence}
    (answered : askSortParam relEnv signature language fuel forms hint rounds fibreOf sort formula term =
      .proved evidence) :
    SortParamHolds (FrontStructure relEnv language fuel forms) sort formula term := by
  unfold askSortParam at answered
  split at answered
  · rename_i fibre _
    split at answered
    · rename_i all
      refine (sortParamHolds_iff_sublists fibre formula term).mpr fun members member => ?_
      obtain ⟨_, found⟩ := Answer.isProved_iff.mp (List.all_eq_true.mp all members member)
      exact ask_proved found
    · split at answered <;> cases answered
  · cases answered

/-- **A refuted bounded parametric type fails**, at the predicate the refutation names. -/
theorem askSortParam_refuted
    {fibreOf : (type : TypeExpr) → Option (DiscreteFibre (FrontStructure relEnv language fuel forms) type)}
    {sort : TypeExpr} {formula : Formula 2} {term : Pattern} {evidence : JudgmentEvidence}
    (answered : askSortParam relEnv signature language fuel forms hint rounds fibreOf sort formula term =
      .refuted evidence) :
    ¬ SortParamHolds (FrontStructure relEnv language fuel forms) sort formula term := by
  unfold askSortParam at answered
  split at answered
  · rename_i fibre _
    split at answered
    · cases answered
    · cases found : fibre.values.sublists.findSome?
          (predicateCounter relEnv signature language fuel forms hint rounds formula term) with
      | none => simp only [found] at answered; cases answered
      | some pair =>
        obtain ⟨members, member, mapped⟩ := List.exists_of_findSome?_eq_some found
        obtain ⟨_, refutation, _⟩ := Option.map_eq_some_iff.mp mapped
        exact fun holds => ask_refuted (Answer.refutation_eq refutation)
          ((sortParamHolds_iff_sublists fibre formula term).mp holds members member)
  · cases answered

/-- A verdict the front door reaches: proved or refuted. -/
def Answer.Decided (answer : Answer) : Prop := answer.isProved = true ∨ answer.refutation.isSome = true

/-- **Exactness**: over complete fibres, when the front door decides every refinement and every instance of the type
at the candidate valuations, it decides the dependent judgment. -/
theorem askDep_decided
    {fibreOf : (type : TypeExpr) → Option (Fibre (FrontStructure relEnv language fuel forms) type)}
    {context : DepContext} {formula : Formula 0} {term : Pattern} (nodup : context.names.Nodup)
    (covers : depCovered fibreOf context = true)
    (decided : ∀ values ∈ depCandidates fibreOf context,
      (∀ entry ∈ context, (refinementAnswer relEnv signature language fuel forms hint rounds values entry).Decided) ∧
        (instanceAnswer relEnv signature language fuel forms hint rounds formula term values).Decided) :
    askDep relEnv signature language fuel forms hint rounds fibreOf context formula term ≠ .unknown := by
  unfold askDep
  rw [if_pos (by simp [nodup, covers])]
  split
  · exact JudgmentAnswer.noConfusion
  · rename_i notAll
    obtain ⟨values, member, unsettled⟩ := List.all_eq_false.mp (Bool.eq_false_iff.mpr notAll)
    have counter : (candidateCounter relEnv signature language fuel forms hint rounds context formula term values).isSome := by
      obtain ⟨refinements, instanceDecided⟩ := decided values member
      simp only [Bool.not_eq_true, candidateSettled, Bool.or_eq_false_iff, Bool.and_eq_false_iff, List.any_eq_false,
        Bool.not_eq_true] at unsettled
      have allProved : context.all (fun entry =>
          (refinementAnswer relEnv signature language fuel forms hint rounds values entry).isProved) = true :=
        List.all_eq_true.mpr fun entry entryMem =>
          (refinements entry entryMem).resolve_right (by simp [unsettled.1 entry entryMem])
      have refuted := instanceDecided.resolve_left (by
        rcases unsettled.2 with notAll | notProved
        · exact absurd allProved (by simp [notAll])
        · simp [notProved])
      simp only [candidateCounter, allProved, if_true, Option.isSome_map]
      exact refuted
    obtain ⟨pair, found⟩ := Option.isSome_iff_exists.mp
      (List.findSome?_isSome_iff.mpr ⟨values, member, counter⟩)
    rw [found]
    exact JudgmentAnswer.noConfusion

/-- **Exactness**: over a discrete fibre, when the front door decides the instance at every predicate on the sort,
it decides the bounded parametric type. -/
theorem askSortParam_decided
    {fibreOf : (type : TypeExpr) → Option (DiscreteFibre (FrontStructure relEnv language fuel forms) type)}
    {sort : TypeExpr} {formula : Formula 2} {term : Pattern}
    {fibre : DiscreteFibre (FrontStructure relEnv language fuel forms) sort} (found : fibreOf sort = some fibre)
    (decided : ∀ members ∈ fibre.values.sublists,
      (predicateAnswer relEnv signature language fuel forms hint rounds formula term members).Decided) :
    askSortParam relEnv signature language fuel forms hint rounds fibreOf sort formula term ≠ .unknown := by
  unfold askSortParam
  rw [found]
  dsimp only
  split
  · exact JudgmentAnswer.noConfusion
  · rename_i notAll
    obtain ⟨members, member, unproved⟩ := List.all_eq_false.mp (Bool.eq_false_iff.mpr notAll)
    have refuted := (decided members member).resolve_left (by simpa using unproved)
    have counter : (predicateCounter relEnv signature language fuel forms hint rounds formula term members).isSome := by
      simpa only [predicateCounter, Option.isSome_map] using refuted
    obtain ⟨pair, located⟩ := Option.isSome_iff_exists.mp
      (List.findSome?_isSome_iff.mpr ⟨members, member, counter⟩)
    rw [located]
    exact JudgmentAnswer.noConfusion

end Ask

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
