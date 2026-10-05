import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchRecursor
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchLists
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectAppendByEquations
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.SchemaDeterminism

/-!
# Adequacy at a declared datatype

Let `d` be a simple datatype admissible over the object package (`hd : d.Admissible objectChurch`):
a type in a universe, constructors whose fields are the datatype itself or closed types of the
object package, and a recursor with one computation rule for each constructor. This module proves
the fundamental lemma of the logical relation for the object package with `d` (`dataChurch d`), with
no hypothesis, for every such `d`, and draws its consequences.

**The extension.** The package with `d` is an extension of the object package
(`dataExtension hd`): its reading is the domain reading `dataReading d`, its roles make `d` an
inductive type with its constructors and its recursor a computing constant on its last argument
(`dataRoles d`), and its root steps are deterministic (`dataChurch_root_deterministic`, through the
determinacy of the recursor's computation rules, `iotaSchema_determinate`). The object package's
constants are adequate in every extension; what remains are the datatype, its constructors and its
recursor.

**The datatype and its constructors** (`constAdequateAt_dataType`, `constAdequateAt_ctor`). The
datatype's tokens are its tag and the tokens of its parameters, the closed field types, each a type
of the object package related to itself. A constructor at the variables of its fields reduces to
itself, and a token of its constructor element is its tag or a component token of a field.

**The recursor** (`constAdequateAt_rec`). Its spine at the variables of its context denotes
recursion over the datatype, projected onto the motive (`appSpine_recursor`); each token of the
recursion lies in an approximant, and the relation at the approximants is proved by induction on
the approximant (`dataRec_claim`). A token observing something names the tag of a constructor the
term reduces to; the element then lies below that constructor of its fields, and the token lies in
the constructor's method at the fields and at the previous approximant at the recursive fields. On
the term side the spine reduces, by the computation rule, to the method applied to the fields and
to the recursor at the recursive fields (`CRedTm.dataRec`, the rule being an equality by
`iota_holds`). The two sides are related through the context of the case (`caseEntry`): the
motive, the methods, the fields, and one hypothesis, the motive at the field, for each recursive
field. Over it the method applied to the fields and to the hypotheses is typed with no constant
(`caseBody_typed`, by `caseFields_applied`), hence adequate; its substitutions are related entry by
entry (`caseEntryRel`): the motive and the methods by the recursor's parameters, the fields by the
fields of related constructor forms, the hypotheses by the claim at the previous approximant
(`dataCase_rel`). The motive's adequacy converts the relation from the constructor form to the term.

**The consequences**, for every admissible `d`: every constant is adequate
(`dataChurch_constAdequate`), the fundamental lemma (`dataChurch_fundamental`), the facts about the
weak-head forms of the annotated types and the injectivity and no-confusion of the type formers
(`dataFormFacts`, `dataFormerFacts`), and the root steps of typed terms preserve typing, carry
their premises and are equalities (`dataRootPreserving`, `dataRootPremised`, `dataRootAdmitted`).

**The three faces.** This is the intensional face (the typed judgment) read in the domain, with
the operational face (the recursor's computation rules as weak-head steps) entering through head
expansion: a term related to a value is one that reduces to a related canonical form. The
extensional face of the same package is its set model, where the datatype is the least set closed
under its constructors.

Positive example: the lists of numbers are an instance (`listDecl_admissible`), so their package
admits its root steps. Negative example: the recursion's hypotheses are only at the recursive
fields, so the number in `cons` carries none (`flagPositions`). That closedness is needed for
canonicity, the recursor being stuck at a variable, is shown with the strong normalization of the
lists (`appendVarNil_not_canonical`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypedAt principal natI ctorI
  recI cpi)
open AlgebraicSchema (SchemaFamily)

/-! ## The computation rules of a recursor -/

section RecursorSchemas

variable {Head : Type}

theorem multiplicity_appSpine {N : Nat} (v : Fin N) :
    ∀ (ts : List (Tm Head N)) (f : Tm Head N),
      AlgebraicSchema.variableMultiplicity v (appSpine f ts) =
        AlgebraicSchema.variableMultiplicity v f +
          (ts.map (AlgebraicSchema.variableMultiplicity v)).sum
  | [], f => by simp
  | t :: ts, f => by
      rw [appSpine_cons, multiplicity_appSpine v ts (.app f t)]
      simp only [AlgebraicSchema.variableMultiplicity, List.map_cons, List.sum_cons]
      omega

theorem multiplicity_metaVars {N : Nat} (v : Fin N) :
    ((metaVars (Head := Head) N).map (AlgebraicSchema.variableMultiplicity v)).sum = 1 := by
  have zero : ∀ l : List (Fin N), v ∉ l →
      ((l.map Tm.var).map (AlgebraicSchema.variableMultiplicity (Head := Head) v)).sum = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons i l ih =>
        intro hv
        rw [List.map_cons, List.map_cons, List.sum_cons,
          ih fun m => hv (List.mem_cons_of_mem _ m)]
        show (if i = v then 1 else 0) + 0 = 0
        rw [if_neg fun e => hv (by rw [← e]; exact List.mem_cons_self)]
  have one : ∀ l : List (Fin N), l.Nodup → v ∈ l →
      ((l.map Tm.var).map (AlgebraicSchema.variableMultiplicity (Head := Head) v)).sum = 1 := by
    intro l
    induction l with
    | nil => intro _ m; exact nomatch m
    | cons i l ih =>
        intro nodup m
        rw [List.nodup_cons] at nodup
        rw [List.map_cons, List.map_cons, List.sum_cons]
        show (if i = v then 1 else 0) + _ = 1
        by_cases hi : i = v
        · subst hi
          rw [if_pos rfl, zero l nodup.1]
        · rw [if_neg hi, ih nodup.2 ((List.mem_cons.1 m).resolve_left (Ne.symm hi)), Nat.zero_add]
  rw [metaVars]
  exact one _ (List.nodup_reverse.2 (List.nodup_finRange N))
    (List.mem_reverse.2 (List.mem_finRange v))

/-- **Every metavariable of a recursor's computation rule occurs once in its left side.** -/
theorem multiplicity_iotaLeft (rec k : DeclName) (c a : Nat) (v : Fin (1 + c + a)) :
    AlgebraicSchema.variableMultiplicity v (iotaLeft (Head := Head) rec k c a) = 1 := by
  unfold iotaLeft recApp
  rw [multiplicity_appSpine, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton, multiplicity_appSpine]
  simp only [AlgebraicSchema.variableMultiplicity, Nat.zero_add]
  rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  exact multiplicity_metaVars v

/-- **The left sides of a recursor's rules are first-order and left-linear.** -/
theorem iotaSchema_firstOrder (rec : DeclName)
    (cs : List (DeclName × List (Normalization.Field Head))) :
    FirstOrderFamily (iotaSchema rec cs) := by
  intro k L R rule
  obtain ⟨i, c, fields, entry, e⟩ := rule
  cases e
  exact ⟨firstOrder_iotaLeft _ _ _ _, fun v => (multiplicity_iotaLeft _ _ _ _ v).le⟩

/-- Spines of two different constants are apart. -/
theorem apart_appSpine_const [DecidableEq Head] {N M : Nat} {k k' : DeclName} (h : k ≠ k') :
    ∀ (xs : List (Tm Head N)) (ys : List (Tm Head M)),
      Apart (appSpine (.const k) xs) (appSpine (.const k') ys) = true := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
      intro ys
      induction ys using List.reverseRecOn with
      | nil => simp [Apart, h]
      | append_singleton ys y _ => rw [appSpine_concat]; rfl
  | append_singleton xs x ih =>
      intro ys
      induction ys using List.reverseRecOn with
      | nil => rw [appSpine_concat]; rfl
      | append_singleton ys y _ =>
          rw [appSpine_concat, appSpine_concat, Apart.app_iff]
          exact .inl (ih ys)

/-- **A recursor's rules are determined by their left sides**: every metavariable occurs in its
left side, and the left sides at two constructors are apart. -/
theorem iotaSchema_determinate [DecidableEq Head] (rec : DeclName)
    (cs : List (DeclName × List (Normalization.Field Head)))
    (nodup : (cs.map Prod.fst).Nodup) : SchemaDeterminate (iotaSchema rec cs) where
  covers := by
    intro k L R rule v
    obtain ⟨i, c, fields, entry, e⟩ := rule
    cases e
    rw [multiplicity_iotaLeft]
    exact Nat.one_ne_zero
  leftUnique := by
    intro k₁ k₂ n L₁ R₁ L₂ R₂ rule₁ rule₂ τ₁ τ₂ e
    obtain ⟨i₁, c₁, fields₁, entry₁, e₁⟩ := rule₁
    obtain ⟨i₂, c₂, fields₂, entry₂, e₂⟩ := rule₂
    cases e₁
    cases e₂
    by_cases same : c₁ = c₂
    · subst same
      have e' : (c₁, fields₁) = (c₁, fields₂) :=
        List.inj_on_of_nodup_map nodup (List.mem_of_getElem? entry₁)
          (List.mem_of_getElem? entry₂) rfl
      cases e'
      rfl
    · exfalso
      refine Apart.subst_ne _ _ ?_ τ₁ τ₂ e
      unfold iotaLeft recApp
      rw [appSpine_concat, appSpine_concat, Apart.app_iff]
      exact .inr (apart_appSpine_const same _ _)

end RecursorSchemas

namespace CodeModel

/-! ## The roles of a package with a declared datatype -/

/-- The number of fields of the constructor `k`, if it is listed. -/
def ctorArity? : List (DeclName × List CtorField) → DeclName → Option Nat
  | [], _ => none
  | c :: cs, k => if k = c.1 then some c.2.length else ctorArity? cs k

theorem ctorArity?_getElem? : ∀ {cs : List (DeclName × List CtorField)} {i : Nat} {k : DeclName}
    {fs : List CtorField}, (cs.map Prod.fst).Nodup → cs[i]? = some (k, fs) →
      ctorArity? cs k = some fs.length
  | [], _, _, _, _, h => nomatch h
  | c :: cs, 0, k, fs, _, h => by
      cases h
      simp [ctorArity?]
  | c :: cs, i + 1, k, fs, nodup, h => by
      rw [List.map_cons, List.nodup_cons] at nodup
      have h' : cs[i]? = some (k, fs) := by simpa using h
      have hk : k ≠ c.1 := fun e =>
        nodup.1 (e ▸ List.mem_map.2 ⟨(k, fs), List.mem_of_getElem? h', rfl⟩)
      rw [ctorArity?, if_neg hk, ctorArity?_getElem? nodup.2 h']

theorem ctorArity?_none : ∀ {cs : List (DeclName × List CtorField)} {k : DeclName},
    k ∉ cs.map Prod.fst → ctorArity? cs k = none
  | [], _, _ => rfl
  | c :: cs, k, h => by
      rw [List.map_cons, List.mem_cons, not_or] at h
      rw [ctorArity?, if_neg h.1, ctorArity?_none h.2]

theorem ctorArity?_some : ∀ {cs : List (DeclName × List CtorField)} {k : DeclName} {a : Nat},
    ctorArity? cs k = some a → ∃ fs, (k, fs) ∈ cs ∧ a = fs.length
  | [], _, _, h => nomatch h
  | c :: cs, k, a, h => by
      unfold ctorArity? at h
      split_ifs at h with hk
      · cases h
        exact ⟨c.2, by rw [hk]; exact List.mem_cons_self, rfl⟩
      · obtain ⟨fs, hfs, rfl⟩ := ctorArity?_some h
        exact ⟨fs, List.mem_cons_of_mem _ hfs, rfl⟩

variable (d : Datatype Tower.Head)

/-- The names a declared datatype adds: its type, its recursor and its constructors. -/
def dataNames : List DeclName := d.type :: d.recursor :: d.ctors.map Prod.fst

/-- **The roles of a package with a declared datatype over the roles `base`**: the datatype is
an inductive type with its constructors, each constructor a constructor of its number of fields,
the recursor computes on its last argument after the motive and the methods, and every other name
has its role in `base`. -/
def dataRolesOver (base : Roles Tower.Head) : Roles Tower.Head := fun name =>
  if name = d.type then .inductive d.ctors
  else match ctorArity? d.ctors name with
    | some a => .constructor a
    | none =>
        if name = d.recursor then
          .computes (d.ctors.length + 2) (.split (d.ctors.length + 1) .constructor fun _ => .leaf)
        else base name

/-- **The roles of the object package with a declared datatype.** -/
abbrev dataRoles : Roles Tower.Head := dataRolesOver d objectRoles

/-- **The rules of the object package with a declared datatype.** -/
abbrev dataRules : Rules Tower.Head := rulesWith objectRules [.datatype d]

/-- The constructors of the numbers and of the datatype, with the shapes of their fields. -/
def dataCtor (T c : DeclName) (fs : List FieldShape) : Prop :=
  objectCtor T c fs ∨ (T = d.type ∧ ∃ i fields, d.ctors[i]? = some (c, fields) ∧
    fs = fieldShapes (paramTypes (d.ctors.take i)).length fields)

section Roles

variable {d} {base : Roles Tower.Head} (distinct : DistinctNames d.type d.ctors d.recursor)
include distinct

omit distinct in
theorem dataRoles_type : dataRolesOver d base d.type = .inductive d.ctors := if_pos rfl

theorem dataRoles_ctor {i : Nat} {k : DeclName} {fs : List CtorField}
    (h : d.ctors[i]? = some (k, fs)) : dataRolesOver d base k = .constructor fs.length := by
  have hk : k ≠ d.type := fun e => distinct.typeNotCtor
    (e ▸ List.mem_map.2 ⟨(k, fs), List.mem_of_getElem? h, rfl⟩)
  simp only [dataRolesOver, if_neg hk, ctorArity?_getElem? distinct.ctorsNodup h]

theorem dataRoles_rec :
    dataRolesOver d base d.recursor = .computes (d.ctors.length + 2)
      (.split (d.ctors.length + 1) .constructor fun _ => .leaf) := by
  simp only [dataRolesOver, if_neg distinct.recNotType, ctorArity?_none distinct.recNotCtor,
    if_true]

omit distinct in
theorem dataRoles_outside {c : DeclName} (h : c ∉ dataNames d) :
    dataRolesOver d base c = base c := by
  simp only [dataNames, List.mem_cons, not_or] at h
  simp only [dataRolesOver, if_neg h.1, ctorArity?_none h.2.2, if_neg h.2.1]

omit distinct in
/-- A name that is rigid in `base` whenever it is a name of the datatype keeps its role when it
is not rigid in `base`. -/
theorem dataRoles_of_nonrigid (baseRigid : ∀ {c : DeclName}, c ∈ dataNames d → base c = .rigid)
    {c : DeclName} (h : base c ≠ .rigid) : dataRolesOver d base c = base c :=
  dataRoles_outside fun mem => h (baseRigid mem)

omit distinct in
/-- The constructors of `base` stay constructors. -/
theorem dataRoles_keep (baseRigid : ∀ {c : DeclName}, c ∈ dataNames d → base c = .rigid)
    {c : DeclName} {arity : Nat} (h : base c = .constructor arity) :
    dataRolesOver d base c = .constructor arity :=
  (dataRoles_of_nonrigid baseRigid fun e => nomatch h.symm.trans e).trans h

theorem dataRoles_constructor {c : DeclName} {arity : Nat}
    (role : dataRolesOver d base c = .constructor arity) :
    (∃ fs, (c, fs) ∈ d.ctors ∧ arity = fs.length) ∨
      (c ∉ dataNames d ∧ base c = .constructor arity) := by
  unfold dataRolesOver at role
  by_cases h₁ : c = d.type
  · rw [if_pos h₁] at role
    cases role
  rw [if_neg h₁] at role
  cases found : ctorArity? d.ctors c with
  | some a =>
      simp only [found] at role
      cases role
      exact .inl (ctorArity?_some found)
  | none =>
      simp only [found] at role
      by_cases h₂ : c = d.recursor
      · rw [if_pos h₂] at role
        cases role
      rw [if_neg h₂] at role
      refine .inr ⟨fun mem => ?_, role⟩
      simp only [dataNames, List.mem_cons] at mem
      rcases mem with rfl | rfl | mem
      · exact h₁ rfl
      · exact h₂ rfl
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 mem
        obtain ⟨k, fs⟩ := e
        obtain ⟨i, hi⟩ := List.getElem?_of_mem he
        rw [ctorArity?_getElem? distinct.ctorsNodup hi] at found
        cases found

omit distinct in
/-- The inductive types are `base`'s and the datatype. -/
theorem dataRoles_inductive
    (baseInd : ∀ {T : DeclName} {cs : List (DeclName × List CtorField)},
      base T = .inductive cs → T = numN ∧ cs = ctors)
    {T : DeclName} {cs : List (DeclName × List CtorField)}
    (role : dataRolesOver d base T = .inductive cs) :
    (T = numN ∧ cs = ctors) ∨ (T = d.type ∧ cs = d.ctors) := by
  unfold dataRolesOver at role
  by_cases h₁ : T = d.type
  · rw [if_pos h₁] at role
    cases role
    exact .inr ⟨h₁, rfl⟩
  rw [if_neg h₁] at role
  cases found : ctorArity? d.ctors T with
  | some a =>
      simp only [found] at role
      cases role
  | none =>
      simp only [found] at role
      by_cases h₂ : T = d.recursor
      · rw [if_pos h₂] at role
        cases role
      rw [if_neg h₂] at role
      exact .inl (baseInd role)

/-- **The constructors of the numbers and of the datatype are declared**, when those of `base`
are, the numbers are its only inductive type and the datatype's names are rigid in it. -/
theorem dataConstructorsDeclaredOver
    (baseRigid : ∀ {c : DeclName}, c ∈ dataNames d → base c = .rigid)
    (declared : ConstructorsDeclared base) (num : base numN = .inductive ctors)
    (baseInd : ∀ {T : DeclName} {cs : List (DeclName × List CtorField)},
      base T = .inductive cs → T = numN ∧ cs = ctors) :
    ConstructorsDeclared (dataRolesOver d base) where
  arity := by
    intro T cs k fields role mem
    rcases dataRoles_inductive baseInd role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact dataRoles_keep baseRigid (declared.arity num mem)
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
      exact dataRoles_ctor distinct hi
  distinct := by
    intro T cs role
    rcases dataRoles_inductive baseInd role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact declared.distinct num
    · exact distinct.ctorsNodup

end Roles

/-! ## The object package's names -/

/-- **A name the object package does not declare is rigid in it.** -/
theorem objectRoles_undeclared {c : DeclName} (h : objectChurch.constantType c = none) :
    objectRoles c = .rigid := by
  have declared : ∀ {n : DeclName}, objectDeclared n = true → c ≠ n :=
    fun hn e => objectChurch_constantType_ne_none hn (e ▸ h)
  have hh : c ≠ holdsN := declared (by decide)
  have hi : c ≠ impN := declared (by decide)
  have ha : SetProfile.allInstance? c = none := by
    cases found : SetProfile.allInstance? c with
    | none => rfl
    | some type =>
        rw [SetProfile.allInstance?_eq_some found] at h
        cases (objectDecls_allName type).symm.trans h
  have he : SetProfile.eqInstance? c = none := by
    cases found : SetProfile.eqInstance? c with
    | none => rfl
    | some type =>
        rw [SetProfile.eqInstance?_eq_some found] at h
        cases (objectDecls_eqName type).symm.trans h
  rw [objectRoles_of hh hi ha he]
  refine roles_of_not_mem fun mem => ?_
  have all : ∀ n ∈ nonrigidNames, objectDeclared n = true := by decide
  exact declared (all c mem) rfl

variable {d} (hd : d.Admissible objectChurch)
include hd

/-- The names of an admissible datatype are new to the object package. -/
theorem dataNames_new {c : DeclName} (mem : c ∈ dataNames d) :
    objectChurch.constantType c = none := by
  simp only [dataNames, List.mem_cons] at mem
  rcases mem with rfl | rfl | mem
  · exact hd.new.typeNew
  · exact hd.new.recNew
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 mem
    exact hd.new.ctorsNew e he

/-- The names of an admissible datatype are rigid in the object package. -/
theorem objectRoles_dataName {c : DeclName} (mem : c ∈ dataNames d) : objectRoles c = .rigid :=
  objectRoles_undeclared (dataNames_new hd mem)

/-- **The object package's constants keep their roles.** -/
theorem dataRoles_object {c : DeclName} (h : (objectRules.constantType c).isSome = true) :
    dataRoles d c = objectRoles c :=
  dataRoles_outside fun mem => objectChurch_constantType_ne_none h (dataNames_new hd mem)

/-- **The constructors of the numbers and of the datatype are declared.** -/
theorem dataConstructorsDeclared : ConstructorsDeclared (dataRoles d) :=
  dataConstructorsDeclaredOver hd.distinct (objectRoles_dataName hd) objectConstructorsDeclared
    objectRoles_num objectRoles_inductive

/-! ## Root shape and determinism -/

/-- A root step of the object package is headed by a constant that computes in the object
package, so not by the recursor of the datatype. -/
theorem object_not_iota {n : Nat} {t u u' : Tower.Tm n} (step : objectRules.computation.step t u)
    (iota : IotaStep d.recursor d.ctors t u') : False := by
  obtain ⟨c, arity, inspect, args, role, rfl, -, -⟩ := objectShape.spine step
  obtain ⟨p, ms, i, k, fields, args', m, -, -, -, -, e, -⟩ := iota
  obtain ⟨rfl, -⟩ := appSpine_const_injective e
  exact nomatch role.symm.trans (objectRoles_dataName hd (by simp [dataNames]))

/-- **The package with a declared datatype has root shape** under its roles. -/
theorem dataShape : RootShape (dataRules d) (dataRoles d) where
  spine := by
    intro n t u step
    rcases step with step | step
    · obtain ⟨c, arity, inspect, args, role, rfl, length, accepts⟩ := objectShape.spine step
      exact ⟨c, arity, inspect, args,
        (dataRoles_of_nonrigid (objectRoles_dataName hd) fun e => nomatch role.symm.trans e).trans
          role,
        rfl, length, accepts.of_constructors (dataRoles_keep (objectRoles_dataName hd))
          (objectRoles_onlyConstructors role)⟩
    · exact IotaStep.spine (dataRoles_type (d := d)) (dataRoles_rec hd.distinct)
        (dataConstructorsDeclared hd) step
  deterministic := by
    intro n t u u' step step'
    rcases step with step | step <;> rcases step' with step' | step'
    · exact objectShape.deterministic step step'
    · exact (object_not_iota hd step step').elim
    · exact (object_not_iota hd step' step).elim
    · exact (IotaStep.deterministic (dataRoles_type (d := d)) (dataConstructorsDeclared hd)
        step step').symm

/-- **The annotated root steps of the package with a declared datatype are deterministic.** -/
theorem dataChurch_root_deterministic {n : Nat} {t u u' : CTm Tower.Head n}
    (first : (dataChurch d).computation.step t u)
    (second : (dataChurch d).computation.step t u') : u = u' := by
  rcases first with first | first <;> rcases second with second | second
  · exact objectChurch_root_deterministic first second
  · exact (object_not_iota hd (objectChurch.erase_step first)
      ((inductiveChurch objectRules d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).erase_step second)).elim
  · exact (object_not_iota hd (objectChurch.erase_step second)
      ((inductiveChurch objectRules d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).erase_step first)).elim
  · exact ChurchRules.ofSchemas_deterministic (iotaSchema d.recursor d.ctors)
      (iota_presents d.recursor d.ctors) (iotaSchema_firstOrder _ _)
      (iotaSchema_determinate _ _ hd.distinct.ctorsNodup)
      (fun s s' => (IotaStep.deterministic (dataRoles_type (d := d)) (dataConstructorsDeclared hd)
        s s').symm)
      first second

/-! ## The package with a declared datatype as an extension of the object package -/

/-- **The object package with an admissible declared datatype is an extension of the object
package**: its reading agrees with the object reading on the object package's constants, its
roles make the datatype an inductive type with its constructors, and its declared datatypes are
the numbers and the datatype, each read with its own tag. -/
def dataExtension : ObjectExtension where
  rules := dataRules d
  church := dataChurch d
  sub := withDeclarations_base objectChurch [.datatype d]
  within := StepsWithin.sum_left objectChurch _
  levels := levelsWith ConvRules.objectLevels [.datatype d]
  headTyping := id
  groundHeadEq := objectRules_groundHeadEq
  reading := dataReading d
  valid := dataReading_valid hd
  reading_head := rfl
  reading_const := fun h => dataReading_object hd (objectChurch_constantType_ne_none h)
  roles := dataRoles d
  roles_object := dataRoles_object hd
  shape := dataShape hd
  deterministic := dataChurch_root_deterministic hd
  data := fun T => T = numN ∨ T = d.type
  params := fun T => if T = d.type then (paramTypes d.ctors).map liftTm else []
  ctor := dataCtor d
  ctor_data := fun hc => by
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl rfl
    · exact .inr rfl
  zero_ctor := .inl ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  suc_ctor := .inl ⟨rfl, .inr ⟨rfl, rfl⟩⟩
  data_role := fun hT => by
    rcases hT with rfl | rfl
    · exact ⟨ctors, (dataRoles_object hd (by decide)).trans objectRoles_num⟩
    · exact ⟨d.ctors, dataRoles_type⟩
  ctor_role := fun hc => by
    rcases hc with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨-, i, fields, hi, rfl⟩
    · exact dataRoles_keep (objectRoles_dataName hd) objectRoles_zero
    · exact dataRoles_keep (objectRoles_dataName hd) objectRoles_suc
    · rw [fieldShapes_length]
      exact dataRoles_ctor hd.distinct hi
  inductivesRead := fun role => by
    rcases dataRoles_inductive objectRoles_inductive role with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · refine .inl ⟨rfl, ?_⟩
      rw [dataReading_object hd (objectChurch_constantType_ne_none (by decide)),
        objectChurchReading_num]
      exact Ideal.mem_principal_tag.2 rfl
    · refine .inr ⟨.inr rfl, ?_⟩
      rw [dataReading_type hd]
      exact Ideal.ctorI_mem_tag _ _

/-- The weak-head reduction of the package with a declared datatype. -/
abbrev dataHead : HeadReduction (dataChurch d) (dataExtension hd).rigid := (dataExtension hd).head

/-! ## Derivations of the object package in the extension -/

omit hd in
/-- A package is contained in itself restricted to its declared constants. -/
theorem restrict_declared_sub {R : Rules Tower.Head} (P : ChurchRules R) :
    ChurchRulesSub P (P.restrict fun c => (P.constantType c).isSome) :=
  ⟨id, id, id, id, id, fun {c} {D} h => by
      show (if (P.constantType c).isSome then P.constantType c else none) = some D
      rw [h]
      rfl,
    id, fun _ requires => ⟨_, requires, fun _ member => member⟩⟩

/-- **A typing of the object package is valid in the extension by a declared datatype**: its
constants are the object package's, adequate in every extension. -/
theorem dataExtension_valid_object {n : Nat} {Γ : CCtx Tower.Head n} {t A : CTm Tower.Head n}
    (typed : CTyped objectChurch Γ t A) (formed : CCtxFormed (dataChurch d) Γ) :
    (CStatement.typing Γ t A).Valid (dataExtension hd).reading (dataHead hd) :=
  (dataExtension hd).valid_within (allowed := fun c => (objectChurch.constantType c).isSome)
    (fun {c} h => by
      obtain ⟨D, hD⟩ := Option.isSome_iff_exists.1 h
      exact (dataExtension hd).objectConsts_adequate hD)
    (typed.mono (restrict_declared_sub objectChurch)) formed

/-- **A closed type of the object package is related to itself**, as far as its tokens
observe. -/
theorem RT.objectType_self {F : CTm Tower.Head 0} {u : Tower.Head}
    (typed : CTyped objectChurch .nil F (.head u)) (hu : objectRules.isUniverse u)
    {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ) {r : Tok}
    (hr : (cinterp (dataReading d) F Env.nil).Mem r) :
    RT (dataHead hd) Δ false r F.liftClosed F.liftClosed F.liftClosed := by
  have adequate := ((dataExtension_valid_object hd typed .nil).1).adequateType
    (dataExtension hd).levels (dataExtension hd).soundnessFacts hu
  have generated : Ideal.TypeGenerated (cinterp (dataReading d) F Env.nil) :=
    (dataExtension hd).soundnessFacts.typeGenerated_of_head hu (typed.mono (dataExtension hd).sub)
      (ρ := Env.nil) trivial
  obtain ⟨v, hv, e⟩ := generated r hr
  refine RT.closed' e fun t ht => ?_
  have h := adequate Env.nil trivial formed SubstRel.nil t (hv t ht).1 (hv t ht).2
  rwa [CTm.subst_closed] at h

end CodeModel

namespace CodeModel

/-! ## The datatype in the domain -/

section Domain

variable {d : Datatype Tower.Head}

/-- The only tag of the datatype is its own. -/
theorem dataTypeI_mem_tag {k : Kind} (h : (dataTypeI d).Mem (.tag k)) : k = .data d.type :=
  Ideal.ctorI_mem_tag_iff.1 h

/-- **The tokens typed at a compact type below the datatype**: the tags of its constructors,
and their component tokens of no dependency whose contents are typed at the field's type. -/
theorem tyTok_data_cases {a : List Tok} (ha : Ideal.Below a (dataTypeI d)) {g : Tok}
    (h : TyTok a g) :
    (∃ c fs, g = .tag (.ctor d.type c fs)) ∨
      ∃ c fs i s f, g = .arg (.ctor d.type c fs) i [] s ∧ fs[i]? = some f ∧
        TyTok (f.typeAt d.type a) s := by
  have nmem : ∀ {k : Kind}, k ≠ .data d.type → Tok.tag k ∉ a := fun hk h' =>
    hk (dataTypeI_mem_tag (ha _ h'))
  have nuniv : ¬ IsUniv a := fun h' => h'.elim (nmem (by simp)) (nmem (by simp))
  have dataName : ∀ {e : DeclName}, Tok.tag (.data e) ∈ a → e = d.type := fun hd => by
    have e := dataTypeI_mem_tag (ha _ hd)
    injection e
  cases g with
  | tag k =>
      rcases tag_cases k with hk | rfl | rfl | rfl | rfl | rfl | ⟨e, c, fs, rfl⟩
      · exact absurd ((tyTok_tag_former hk).1 h) nuniv
      · exact absurd (tyTok_tag_zero.1 h) (nmem (by simp))
      · exact absurd (tyTok_tag_succ.1 h) (nmem (by simp))
      · exact absurd (tyTok_tag_refl.1 h) (nmem (by simp))
      · exact absurd h tyTok_tag_lam
      · exact absurd h tyTok_tag_pair
      · obtain rfl := dataName (tyTok_tag_ctor.1 h)
        exact .inl ⟨c, fs, rfl⟩
  | arg k i C s =>
      rcases Decidable.em ((k, i) ∈ argSlots) with hs | hother
      swap
      · rcases decl_cases k with ⟨e, rfl⟩ | ⟨e, c, fs, rfl⟩ | hk
        · exact absurd (tyTok_param.1 h).1 nuniv
        · obtain ⟨hd, rfl, f, hf, hs⟩ := tyTok_field.1 h
          obtain rfl := dataName hd
          exact .inr ⟨c, fs, i, s, f, rfl, hf, hs⟩
        · exact absurd h (tyTok_arg_other hother hk)
      simp only [argSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd ((tyTok_dom (.inl rfl)).1 h).1 nuniv
      · exact absurd ((tyTok_dom (.inr (.inl rfl))).1 h).1 nuniv
      · exact absurd ((tyTok_dom (.inr (.inr rfl))).1 h).1 nuniv
      · exact absurd ((tyTok_endpoint (.inl rfl)).1 h).1 nuniv
      · exact absurd ((tyTok_endpoint (.inr rfl)).1 h).1 nuniv
      · exact absurd (tyTok_pred.1 h).1 (nmem (by simp))
      · exact absurd (tyTok_reflPoint.1 h).1 (nmem (by simp))
      · exact absurd (tyTok_fst.1 h).1 (nmem (by simp))
      · exact absurd (tyTok_snd.1 h).1 (nmem (by simp))
  | fn k C X Y =>
      rcases fn_cases k with hk | rfl | hother
      · exact absurd ((tyTok_family hk).1 h).1 nuniv
      · exact absurd (tyTok_lam.1 h).1 (nmem (by simp))
      · exact absurd h (tyTok_fn_other hother)

/-- A token typed at the datatype has no dependency. -/
theorem dep_of_typedAt_data {g : Tok} (h : TypedAt (dataTypeI d) g) : g.dep = [] := by
  obtain ⟨a, ha, -, hat⟩ := h
  rcases tyTok_data_cases ha hat with ⟨c, fs, rfl⟩ | ⟨c, fs, i, s, f, rfl, -, -⟩ <;> rfl

/-- A token of a parameter of the datatype, typed at a compact type below the datatype, is
typed at that parameter. -/
theorem typedAt_dataParam {a : List Tok} (ha : Ideal.Below a (dataTypeI d))
    (hau : Ty a Elem.univ) {j : Nat} {r : Tok} (hr : TyTok (args (.data d.type) j a) r) :
    TypedAt (((dataParams d)[j]?).getD Ideal.bot) r := by
  have hdep : ∀ t ∈ a, t.kind = .data d.type → t.dep = [] := by
    intro t ht hk
    cases t with
    | tag k => rfl
    | arg k j' C x =>
        cases hk
        exact (tyTok_param.1 (hau _ ht)).2.1
    | fn k C X Y =>
        cases hk
        exact absurd (hau _ ht) (tyTok_fn_other ⟨nofun, nofun, nofun⟩)
  refine ⟨args (.data d.type) j a, fun r' hr' => ?_, fun r' hr' => ?_, hr⟩
  · rcases mem_args_iff.1 hr' with ⟨C, hC⟩ | ⟨-, t, ht, hk, hd⟩
    · have h₁ : (Ideal.fieldI (Kind.data d.type) j (dataTypeI d)).Mem r' :=
        Ideal.subset_closure ⟨C, ha _ hC⟩
      rwa [dataTypeI, Ideal.fieldI_ctorI] at h₁
    · rw [hdep t ht hk] at hd
      exact absurd hd List.not_mem_nil
  · rcases mem_args_iff.1 hr' with ⟨C, hC⟩ | ⟨-, t, ht, hk, hd⟩
    · exact (tyTok_param.1 (hau _ hC)).2.2
    · rw [hdep t ht hk] at hd
      exact absurd hd List.not_mem_nil

/-- **The fields of an element of the datatype built by a constructor are elements of their
types.** -/
theorem projT_fieldI_data {ν : Ideal} (hν : projT (dataTypeI d) ν = ν) {c : DeclName}
    {fs : List FieldShape} {i : Nat} {f : FieldShape} (hf : fs[i]? = some f) :
    projT (f.typeI d.type (dataParams d)) (Ideal.fieldI (.ctor d.type c fs) i ν) =
      Ideal.fieldI (.ctor d.type c fs) i ν := by
  unfold Ideal.fieldI
  refine Ideal.projT_closure_eq fun g ⟨C, hg⟩ => ?_
  rw [← hν] at hg
  obtain ⟨u, hu, huT, e⟩ := Ideal.projT_eq_iSup.1 hg
  rw [ent_arg, Bool.and_eq_true] at e
  refine ⟨args (.ctor d.type c fs) i u, fun s hs => ?_, e.2⟩
  rcases mem_args_iff.1 hs with ⟨C', hC'⟩ | ⟨-, t, ht, -, hd⟩
  · refine ⟨Ideal.subset_closure ⟨C', hu _ hC'⟩, ?_⟩
    obtain ⟨a, ha, hau, hat⟩ := huT _ hC'
    rcases tyTok_data_cases ha hat with ⟨c', fs', he⟩ | ⟨c', fs', j, r, f', he, hf', hr⟩
    · cases he
    · injection he with e₁ e₂ e₃ e₄
      injection e₁ with _ e₁₂ e₁₃
      subst e₁₂ e₁₃ e₂ e₄
      rw [hf] at hf'
      cases hf'
      cases f with
      | self => exact ⟨a, ha, hau, hr⟩
      | param j => exact typedAt_dataParam ha hau hr
  · rw [dep_of_typedAt_data (huT t ht)] at hd
    exact absurd hd List.not_mem_nil

/-- **An element of the datatype whose typed tokens are the tag of one constructor, its
component tokens, or observe nothing, lies below that constructor of its fields.** -/
theorem le_ctorI_fields {ν : Ideal} (hν : projT (dataTypeI d) ν = ν) {c : DeclName}
    {fs : List FieldShape}
    (hg : ∀ g, ν.Mem g → TypedAt (dataTypeI d) g →
      g = .tag (.ctor d.type c fs) ∨ (∃ i s, g = .arg (.ctor d.type c fs) i [] s) ∨
        ent [] g = true) :
    ν ≤ ctorI (.ctor d.type c fs) (Ideal.fieldsI (.ctor d.type c fs) fs.length ν) := by
  intro t ht
  rw [← hν] at ht
  obtain ⟨u, hu, huT, e⟩ := Ideal.projT_eq_iSup.1 ht
  refine (ctorI _ _).closed (v := u) (fun g hgu => ?_) e
  rcases hg g (hu g hgu) (huT g hgu) with rfl | ⟨i, s, rfl⟩ | hv
  · exact Ideal.ctorI_mem_tag _ _
  · refine Ideal.mem_ctorI_arg ?_
    have hs : (Ideal.fieldI (.ctor d.type c fs) i ν).Mem s := Ideal.subset_closure ⟨[], hu _ hgu⟩
    have hi : i < fs.length := by
      obtain ⟨a, ha, -, hat⟩ := huT _ hgu
      rcases tyTok_data_cases ha hat with ⟨c', fs', he⟩ | ⟨c', fs', j, r, f, he, hf, -⟩
      · cases he
      · injection he with e₁ e₂
        injection e₁ with _ e₁₂ e₁₃
        subst e₁₃ e₂
        exact (List.getElem?_eq_some_iff.1 hf).1
    rw [Ideal.fieldsI, List.getElem?_map, List.getElem?_range hi]
    exact hs
  · exact (ctorI _ _).closed (v := []) (fun _ h => absurd h List.not_mem_nil) hv

end Domain

/-! ## Spines of a constant along a context -/

section Spines

theorem etaBody_snoc {Head : Type} : ∀ {n m : Nat} (tele : CTele Head n m) (A : CTm Head m)
    (h : CTm Head n), (tele.snoc A).etaBody h = .app ((tele.etaBody h).rename wk) (.var 0)
  | _, _, .nil, _, _ => rfl
  | _, _, .cons _ rest, A, h => etaBody_snoc rest A (.app (h.rename wk) (.var 0))

theorem metaVars_succ {Head : Type} (k : Nat) :
    metaVars (Head := Head) (k + 1) =
      (metaVars (Head := Head) k).map (Presentation.rename wk) ++ [.var 0] := by
  simp only [metaVars, List.finRange_succ, List.reverse_cons, List.map_append, List.map_reverse,
    List.map_map, List.map_cons, List.map_nil]
  rfl

/-- **The η-body of a constant along a context** is the constant applied to the context's
variables, oldest first. -/
theorem etaBody_toTele_const (c : DeclName) : ∀ {k : Nat} (Θ : CCtx Tower.Head k),
    (CCtx.toTele Θ).etaBody (.const c) = liftTm (appSpine (.const c) (metaVars k))
  | _, .nil => rfl
  | k + 1, .snoc Θ A => by
      show ((CCtx.toTele Θ).snoc A).etaBody (.const c) = _
      rw [etaBody_snoc, etaBody_toTele_const c Θ, ← liftTm_rename, metaVars_succ, appSpine_concat,
        rename_appSpine]
      rfl

end Spines

section Constructors

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- The datatype's type in every context, at its universe. -/
theorem dataType_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped (dataChurch d) Γ (.const d.type) (.head d.typeUniverse) :=
  Annotated.type_typed ConvRules.objectLevels objectChurch hd.typeUniverse hd.new

/-- The datatype reduces to itself. -/
theorem dataRed {m : Nat} {Δ : CCtx Tower.Head m} :
    CRedTy (dataHead hd) Δ (.const d.type : CTm Tower.Head m) (.const d.type) :=
  CRedTy.refl ⟨_, hd.typeUniverse, dataType_typed hd⟩

/-- The rigid parameters of the datatype are its closed field types. -/
theorem dataExtension_param {j : Nat} {n : Nat} {B : CTm Tower.Head n}
    (h : (dataExtension hd).rigid.param d.type j = some B) :
    ∃ F, (paramTypes d.ctors)[j]? = some F ∧ B = (liftTm F).liftClosed := by
  change (((if d.type = d.type then (paramTypes d.ctors).map liftTm else [])[j]?).map
    CTm.liftClosed) = some B at h
  rw [if_pos rfl, List.getElem?_map] at h
  cases e : (paramTypes d.ctors)[j]? with
  | none => rw [e] at h; cases h
  | some F =>
      rw [e] at h
      exact ⟨F, rfl, (Option.some.inj h).symm⟩

omit hd in
/-- A parameter of the datatype is a closed field type of one of its constructors. -/
theorem paramTypes_closed {j : Nat} {F : Tm Tower.Head 0} (h : (paramTypes d.ctors)[j]? = some F) :
    ∃ entry ∈ d.ctors, Field.closed F ∈ entry.2 := by
  obtain ⟨entry, hmem, hF⟩ := List.mem_flatMap.1 (List.mem_of_getElem? h)
  exact ⟨entry, hmem, closed_mem_of_closedTypes hF⟩

/-- **The type of the datatype is adequate**: its tag relates it to itself as the declared
datatype, and its parameter tokens relate its closed field types to themselves. -/
theorem adequateType_dataType {n : Nat} {Γ : CCtx Tower.Head n} :
    AdequateType (dataExtension hd).reading (dataHead hd) Γ (.const d.type) := by
  intro ρ _ m Δ σ σ' formed _ r hr _
  have hr' : (dataTypeI d).Mem r := by
    have h : ((dataReading d).const d.type).Mem r := hr
    rwa [dataReading_type hd] at h
  obtain ⟨v, hv, e⟩ := hr'
  refine RT.closed' e fun t ht => ?_
  rcases hv t ht with rfl | ⟨i, f, s, hf, hs, rfl⟩
  · exact RT.ty_data_iff.2 ⟨.inr rfl, dataRed hd, dataRed hd⟩
  · refine RT.ty_param_iff.2 (.inr ⟨⟨.inr rfl, dataRed hd, dataRed hd⟩,
      fun c hc => absurd hc List.not_mem_nil, fun B hB => ?_⟩)
    obtain ⟨F, hF, rfl⟩ := dataExtension_param hd hB
    obtain ⟨entry, hmem, hcl⟩ := paramTypes_closed hF
    have hf' : f = cinterp objectChurchReading (liftTm F) Env.nil := by
      rw [dataParams, List.getElem?_map, hF] at hf
      exact (Option.some.inj hf).symm
    subst hf'
    exact RT.objectType_self hd (hd.fields entry hmem F hcl) hd.typeUniverse formed
      (by rwa [dataReading_closedField hd hmem hcl])

/-- **The type of the datatype is adequate as a constant.** -/
theorem constAdequateAt_dataType :
    ConstAdequateAt (dataExtension hd).reading (dataHead hd) d.type :=
  ConstAdequateAt.of_adequate (sum_type_declared objectChurch hd.new)
    ((adequateType_dataType hd).adequate (dataExtension hd).levels
      (dataExtension hd).soundnessFacts hd.typeUniverse)

omit hd in
/-- The shapes of a constructor's fields, read in the syntax: a recursive field for the datatype
itself, the closed field type for a parameter. -/
theorem fieldShapes_syntax (ps : List (Tm Tower.Head 0)) :
    ∀ (j : Nat) (fs : List CtorField),
      (∀ q F, (closedTypes fs)[q]? = some F → ps[j + q]? = some F) →
      ∀ (p : Nat) (f : CtorField) (sh : FieldShape), fs[p]? = some f →
        (fieldShapes j fs)[p]? = some sh →
          (sh = .self ∧ f = .recursive) ∨ ∃ r F, sh = .param r ∧ f = .closed F ∧ ps[r]? = some F
  | _, [], _, _, _, _, h, _ => nomatch h
  | j, .recursive :: fs, hps, p, f, sh, hf, hsh => by
      cases p with
      | zero =>
          cases hf
          cases hsh
          exact .inl ⟨rfl, rfl⟩
      | succ p => exact fieldShapes_syntax ps j fs hps p f sh hf hsh
  | j, .closed F :: fs, hps, p, f, sh, hf, hsh => by
      cases p with
      | zero =>
          cases hf
          cases hsh
          have h0 := hps 0 F rfl
          rw [Nat.add_zero] at h0
          exact .inr ⟨j, F, rfl, rfl, h0⟩
      | succ p =>
          exact fieldShapes_syntax ps (j + 1) fs (fun q F' hq => by
            have := hps (q + 1) F' (by simpa [closedTypes] using hq)
            rwa [show j + (q + 1) = j + 1 + q by omega] at this) p f sh hf hsh

/-- **The type of a field, as the relation reads it, is the field's declared type.** -/
theorem dataFieldType {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) {p : Nat} {f : CtorField} {sh : FieldShape}
    (hf : fs[p]? = some f)
    (hsh : (fieldShapes (paramTypes (d.ctors.take i)).length fs)[p]? = some sh) {n : Nat} :
    (dataExtension hd).rigid.fieldType d.type sh =
      some ((liftTm (f.type d.type)).liftClosed : CTm Tower.Head n) := by
  rcases fieldShapes_syntax (paramTypes d.ctors) _ fs (fun q F hq => by
      rw [paramTypes_split entry, List.append_assoc, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, List.getElem?_append_left
          ((List.getElem?_eq_some_iff.1 hq).1)]
      exact hq) p f sh hf hsh with ⟨rfl, rfl⟩ | ⟨r, F, rfl, rfl, hF⟩
  · rfl
  · change (((if d.type = d.type then (paramTypes d.ctors).map liftTm else [])[r]?).map
      CTm.liftClosed) = _
    rw [if_pos rfl, List.getElem?_map, hF]
    rfl

omit hd in
/-- The variable of a constructor's field `p` has the field's type. -/
theorem ctorTele_lookup (T : DeclName) (fs : List CtorField) {p : Nat} (hp : p < fs.length) :
    (liftCtx (ctorTele T fs)).lookup (metaIdx fs.length p hp) =
      (liftTm (fs[p].type T)).liftClosed := by
  rw [liftCtx_lookup]
  have hl := ofEntries_lookup_closed (fun j => (fs.getD j .recursive).type T) fs.length
    (metaIdx fs.length p hp)
  rw [show ofEntries (fun j => Presentation.liftClosed ((fs.getD j .recursive).type T))
      fs.length = ctorTele T fs from rfl] at hl
  rw [hl, liftTm_liftClosed]
  have idx : fs.length - 1 - (metaIdx fs.length p hp).val = p := index_back _ _ hp
  rw [idx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]

omit hd in
/-- The variables of a constructor's context have the types of its fields. -/
theorem ctorVars_typed {R : Rules Tower.Head} {Q : ChurchRules R} (T : DeclName)
    (fs : List CtorField) :
    List.Forall₂ (fun x (field : CtorField) =>
      CTyped Q (liftCtx (ctorTele T fs)) (liftTm x) (liftTm (field.type T)).liftClosed)
      (metaVars fs.length) fs := by
  refine List.forall₂_iff_get.mpr ⟨length_metaVars _, fun p h₁ h₂ => ?_⟩
  have hp : p < fs.length := h₂
  have element : (metaVars (Head := Tower.Head) fs.length).get ⟨p, h₁⟩ =
      .var (metaIdx fs.length p hp) :=
    Option.some.inj ((List.getElem?_eq_getElem h₁).symm.trans (metaVars_get? hp))
  rw [element]
  have typed := CDerivable.var (P := Q) (Γ := liftCtx (ctorTele T fs)) (metaIdx fs.length p hp)
  rw [liftCtx_lookup] at typed
  have hl := ofEntries_lookup_closed (fun j => (fs.getD j .recursive).type T) fs.length
    (metaIdx fs.length p hp)
  rw [show ofEntries (fun j => Presentation.liftClosed ((fs.getD j .recursive).type T))
      fs.length = ctorTele T fs from rfl] at hl
  rw [hl, liftTm_liftClosed] at typed
  have idx : fs.length - 1 - (metaIdx fs.length p hp).val = p := index_back _ _ hp
  rw [idx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some] at typed
  exact typed

/-- **A term reducing to a constructor applied to fields related one by one** is related, as far
as every token of the constructor element of values related to the fields observes. -/
theorem RT.ofCtorRed {c : DeclName} {shapes : List FieldShape} {m : Nat} {Δ : CCtx Tower.Head m}
    {T' M M' : CTm Tower.Head m} {ms ms' : List (CTm Tower.Head m)}
    (red : CtorRed (dataHead hd) Δ d.type c shapes T' M M' ms ms') {αs : List Ideal}
    (hrel : ∀ p A x x', FieldAt (dataExtension hd).rigid d.type shapes ms ms' p A x x' →
      ∀ r, (αs.getD p Ideal.bot).Mem r → RT (dataHead hd) Δ true r A x x')
    {s : Tok} (hs : (ctorI (Kind.ctor d.type c shapes) αs).Mem s) :
    RT (dataHead hd) Δ true s T' M M' := by
  obtain ⟨v, hv, e⟩ := hs
  refine RT.closed' e fun t ht => ?_
  rcases hv t ht with rfl | ⟨p, f, r, hf, hr, rfl⟩
  · exact RT.tm_ctorTag_iff.2 ⟨ms, ms', red⟩
  · refine RT.tm_field_iff.2 (.inr ⟨ms, ms', red, fun _ h => absurd h List.not_mem_nil,
      fun A x x' hfa => hrel p A x x' hfa r ?_⟩)
    rw [List.getD_eq_getElem?_getD, hf]
    exact hr

omit hd in
/-- Fields equal one by one. -/
theorem fieldsEqual_of_get {R : Rules Tower.Head} {P : ChurchRules R} (K : RigidTypes P)
    {m : Nat} {Δ : CCtx Tower.Head m} (T : DeclName) :
    ∀ (shapes : List FieldShape) (ms ms' : List (CTm Tower.Head m)),
      shapes.length = ms.length → ms.length = ms'.length →
      (∀ (p : Nat) (sh : FieldShape) (x x' : CTm Tower.Head m), shapes[p]? = some sh →
        ms[p]? = some x → ms'[p]? = some x' →
        ∃ A, K.fieldType T sh = some A ∧ CEqual P Δ x x' A) →
      FieldsEqual K Δ T shapes ms ms'
  | [], [], [], _, _, _ => .nil
  | sh :: shapes, x :: ms, x' :: ms', h₁, h₂, h => by
      obtain ⟨A, hA, e⟩ := h 0 sh x x' rfl rfl rfl
      exact .cons hA e (fieldsEqual_of_get K T shapes ms ms' (Nat.succ.inj h₁)
        (Nat.succ.inj h₂) fun p sh' y y' hs hy hy' => h (p + 1) sh' y y' hs hy hy')
  | [], _ :: _, _, h₁, _, _ => (Nat.succ_ne_zero _ h₁.symm).elim
  | _ :: _, [], _, h₁, _, _ => (Nat.succ_ne_zero _ h₁).elim
  | _, [], _ :: _, _, h₂, _ => (Nat.succ_ne_zero _ h₂.symm).elim
  | _, _ :: _, [], _, h₂, _ => (Nat.succ_ne_zero _ h₂).elim

/-- **A constructor at its variables is adequate**: a token of the constructor element is its
tag, or a component token of a field, at which the substituted variables are related. -/
theorem adequate_ctorVars {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) :
    Adequate (dataExtension hd).reading (dataHead hd) (liftCtx (ctorTele d.type fs))
      (liftTm (appSpine (.const k) (metaVars fs.length))) (.const d.type) := by
  intro ρ fits m Δ σ σ' formed hσ s hs _
  have hlen : (metaVars (Head := Tower.Head) fs.length).length = fs.length := length_metaVars _
  have spine : CTyped (dataChurch d) (liftCtx (ctorTele d.type fs))
      (liftTm (appSpine (.const k) (metaVars fs.length))) (.const d.type) :=
    ctor_spine_typed ConvRules.objectLevels objectChurch hd.typeUniverse hd.distinct hd.lamFree
      hd.new hd.fieldsFormed entry (ctorVars_typed d.type fs)
  have eσ : ∀ τ : CSub Tower.Head fs.length m,
      (liftTm (appSpine (.const k) (metaVars fs.length))).subst τ =
        CTm.appSpine (.const k) ((metaVars fs.length).map fun t => (liftTm t).subst τ) :=
    fun τ => by rw [liftTm_appSpine, csubst_appSpine, List.map_map]; rfl
  have sσ := spine.substitute hσ.1.1
  have sσ' := spine.substitute (hσ.symm (dataExtension hd).levels formed).1.1
  rw [eσ] at sσ sσ' ⊢
  rw [eσ]
  rw [liftTm_appSpine, cinterp_appSpine] at hs
  change (Ideal.appSpine ((dataReading d).const k) _).Mem s at hs
  rw [dataReading_ctor hd entry, appSpine_ctorConstI_proj k _ (by
    rw [List.length_map, List.length_map, hlen, fieldShapes_length])] at hs
  have hshapes := dataShapes_typeI entry
  -- the fields, entry by entry
  have field : ∀ (p : Nat) (hp : p < fs.length),
      ((metaVars fs.length).map fun t => (liftTm t).subst σ)[p]? =
        some (σ (metaIdx fs.length p hp)) ∧
      ((metaVars fs.length).map fun t => (liftTm t).subst σ')[p]? =
        some (σ' (metaIdx fs.length p hp)) := fun p hp => by
    rw [List.getElem?_map, List.getElem?_map, metaVars_get? hp]
    exact ⟨rfl, rfl⟩
  have shapeAt : ∀ (p : Nat) (sh : FieldShape),
      (fieldShapes (paramTypes (d.ctors.take i)).length fs)[p]? = some sh →
        ∃ hp : p < fs.length, (dataExtension hd).rigid.fieldType d.type sh =
          some ((liftTm (fs[p].type d.type)).liftClosed : CTm Tower.Head m) := fun p sh hsh => by
    have hp : p < fs.length := by
      rw [← fieldShapes_length (paramTypes (d.ctors.take i)).length fs]
      exact (List.getElem?_eq_some_iff.1 hsh).1
    exact ⟨hp, dataFieldType hd entry (List.getElem?_eq_getElem hp) hsh⟩
  refine RT.ofCtorRed hd (ms := (metaVars fs.length).map fun t => (liftTm t).subst σ)
    (ms' := (metaVars fs.length).map fun t => (liftTm t).subst σ')
    ⟨.inr ⟨rfl, i, fs, entry, rfl⟩, dataRed hd, CRedTm.refl sσ, CRedTm.refl sσ', ?_⟩ ?_ hs
  · refine fieldsEqual_of_get _ _ _ _ _
      (by rw [fieldShapes_length, List.length_map, hlen])
      (by rw [List.length_map, List.length_map])
      fun p sh x x' hsh hx hx' => ?_
    obtain ⟨hp, hA⟩ := shapeAt p sh hsh
    obtain ⟨e₁, e₂⟩ := field p hp
    rw [e₁] at hx
    rw [e₂] at hx'
    cases hx
    cases hx'
    refine ⟨_, hA, ?_⟩
    have e := hσ.1.2 (metaIdx fs.length p hp)
    rwa [ctorTele_lookup, CTm.subst_liftClosed] at e
  · intro p A x x' hfa r hr
    obtain ⟨⟨sh, hsh, hA⟩, hx, hx'⟩ := hfa
    obtain ⟨hp, hA'⟩ := shapeAt p sh hsh
    rw [hA] at hA'
    cases hA'
    obtain ⟨e₁, e₂⟩ := field p hp
    rw [e₁] at hx
    rw [e₂] at hx'
    cases hx
    cases hx'
    have hp' : p < (fieldShapes (paramTypes (d.ctors.take i)).length fs).length := by
      rw [fieldShapes_length]; exact hp
    have hval : ((List.zipWith projT ((fieldShapes (paramTypes (d.ctors.take i)).length fs).map
        (FieldShape.typeI d.type (dataParams d)))
        ((metaVars fs.length).map liftTm |>.map
          fun x => cinterp (dataExtension hd).reading x ρ)).getD p Ideal.bot) =
        projT (cinterp (dataReading d) ((liftCtx (ctorTele d.type fs)).lookup
          (metaIdx fs.length p hp)) ρ) (ρ (metaIdx fs.length p hp)) := by
      rw [hshapes, ctorTele_lookup, cinterp_liftClosed,
        dataReading_fieldType hd (List.mem_of_getElem? entry) (List.getElem_mem hp),
        List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map,
        List.getElem?_eq_getElem hp, List.getElem?_map, List.getElem?_map, metaVars_get? hp]
      rfl
    rw [hval] at hr
    obtain ⟨v, hv, hvT, e⟩ := Ideal.projT_eq_iSup.1 hr
    refine RT.closed' e fun t ht => ?_
    have h := (hσ.2 (metaIdx fs.length p hp)).2.2 t (hv t ht) (hvT t ht)
    rwa [ctorTele_lookup, CTm.subst_liftClosed] at h

/-- A constructor is declared at the dependent function type over its fields. -/
theorem ctor_declared {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) :
    (dataChurch d).constantType k = some (pisCtx (liftCtx (ctorTele d.type fs)) (.const d.type)) :=
  (sum_ctor_declared (u := d.typeUniverse) (v := d.motiveUniverse) objectChurch hd.distinct
    hd.lamFree hd.new entry).trans (by rw [ctorType, liftTm_closeType]; rfl)

/-- A constructor at the variables of its fields is a term of the datatype. -/
theorem ctorSpine_typed {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) :
    CTyped (dataChurch d) (liftCtx (ctorTele d.type fs))
      ((CCtx.toTele (liftCtx (ctorTele d.type fs))).etaBody (.const k)) (.const d.type) := by
  rw [etaBody_toTele_const]
  exact ctor_spine_typed ConvRules.objectLevels objectChurch hd.typeUniverse hd.distinct
    hd.lamFree hd.new hd.fieldsFormed entry (ctorVars_typed d.type fs)

theorem adequate_ctorSpine {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) :
    Adequate (dataExtension hd).reading (dataHead hd) (liftCtx (ctorTele d.type fs))
      ((CCtx.toTele (liftCtx (ctorTele d.type fs))).etaBody (.const k)) (.const d.type) := by
  rw [etaBody_toTele_const]
  exact adequate_ctorVars hd entry

/-- **Every constructor of the datatype is adequate**, through its spine at the variables of
its fields. -/
theorem constAdequateAt_ctor {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) :
    ConstAdequateAt (dataExtension hd).reading (dataHead hd) k :=
  ConstAdequateAt.of_spine (dataExtension hd).levels (dataExtension hd).soundnessFacts
    (ctor_declared hd entry) (ctorSpine_typed hd entry) (adequate_ctorSpine hd entry)

end Constructors

/-! ## Telescopes given by their entries, one entry at a time

A context given by its entries (`ofEntries`), a substitution sending its variables to listed
terms (`listCSub`) and an environment sending them to listed values (`Env.ofArgs`) are related,
fit, and are typed entry by entry: the entry at position `q` sees the first `q` terms and
values. -/

section Entries

variable {Head : Type}

/-- The values of an environment, the oldest first. -/
def envArgs {N : Nat} (ρ : Env N) : List Ideal := (List.finRange N).reverse.map ρ

/-- The terms of a substitution, the oldest first. -/
def subArgs {N m : Nat} (σ : CSub Head N m) : List (CTm Head m) :=
  (List.finRange N).reverse.map σ

/-- The substitution sending the variables of a context of length `N`, the oldest first, to
listed terms. -/
def listCSub {m : Nat} (N : Nat) (ts : List (CTm Head m)) : CSub Head N m :=
  fun i => ts.getD (N - 1 - i.val) (.const .anonymous)

theorem finRange_reverse_getElem? {N q : Nat} (hq : q < N) :
    (List.finRange N).reverse[q]? = some (metaIdx N q hq) := by
  have hfin : q < (List.finRange N).length := by rw [List.length_finRange]; exact hq
  rw [List.getElem?_reverse hfin, List.length_finRange,
    List.getElem?_eq_getElem (by rw [List.length_finRange]; exact index_lt N q hq),
    List.getElem_finRange]
  rfl

theorem length_envArgs {N : Nat} (ρ : Env N) : (envArgs ρ).length = N := by
  rw [envArgs, List.length_map, List.length_reverse, List.length_finRange]

theorem length_subArgs {N m : Nat} (σ : CSub Head N m) : (subArgs σ).length = N := by
  rw [subArgs, List.length_map, List.length_reverse, List.length_finRange]

theorem envArgs_getElem? {N : Nat} (ρ : Env N) {q : Nat} (hq : q < N) :
    (envArgs ρ)[q]? = some (ρ (metaIdx N q hq)) := by
  rw [envArgs, List.getElem?_map, finRange_reverse_getElem? hq]
  rfl

theorem subArgs_getElem? {N m : Nat} (σ : CSub Head N m) {q : Nat} (hq : q < N) :
    (subArgs σ)[q]? = some (σ (metaIdx N q hq)) := by
  rw [subArgs, List.getElem?_map, finRange_reverse_getElem? hq]
  rfl

theorem ofArgs_envArgs {N : Nat} (ρ : Env N) : Env.ofArgs N (envArgs ρ) = ρ := by
  funext i
  show (envArgs ρ).getD (N - 1 - i.val) Ideal.bot = ρ i
  rw [List.getD_eq_getElem?_getD, envArgs_getElem? ρ (index_lt N i.val i.isLt), metaIdx_back]
  rfl

theorem listCSub_subArgs {N m : Nat} (σ : CSub Head N m) : listCSub N (subArgs σ) = σ := by
  funext i
  show (subArgs σ).getD (N - 1 - i.val) (.const .anonymous) = σ i
  rw [List.getD_eq_getElem?_getD, subArgs_getElem? σ (index_lt N i.val i.isLt), metaIdx_back]
  rfl

theorem ofArgs_metaIdx {N : Nat} (vs : List Ideal) {q : Nat} (hq : q < N) :
    Env.ofArgs N vs (metaIdx N q hq) = vs.getD q Ideal.bot := by
  show vs.getD (N - 1 - (N - 1 - q)) Ideal.bot = _
  rw [index_back N q hq]

theorem listCSub_metaIdx {N m : Nat} (ts : List (CTm Head m)) {q : Nat} (hq : q < N) :
    listCSub N ts (metaIdx N q hq) = ts.getD q (.const .anonymous) := by
  show ts.getD (N - 1 - (N - 1 - q)) _ = _
  rw [index_back N q hq]

theorem envArgs_ofArgs {N : Nat} {vs : List Ideal} (h : vs.length = N) :
    envArgs (Env.ofArgs N vs) = vs := by
  apply List.ext_getElem? fun q => ?_
  rcases Nat.lt_or_ge q N with hq | hq
  · rw [envArgs_getElem? _ hq, ofArgs_metaIdx vs hq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by rw [length_envArgs]; exact hq),
      List.getElem?_eq_none (by omega)]

theorem subArgs_listCSub {N m : Nat} {ts : List (CTm Head m)} (h : ts.length = N) :
    subArgs (listCSub N ts) = ts := by
  apply List.ext_getElem? fun q => ?_
  rcases Nat.lt_or_ge q N with hq | hq
  · rw [subArgs_getElem? _ hq, listCSub_metaIdx ts hq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by rw [length_subArgs]; exact hq),
      List.getElem?_eq_none (by omega)]

theorem envArgs_cons {N : Nat} (x : Ideal) (ρ : Env N) :
    envArgs (Env.cons x ρ) = envArgs ρ ++ [x] := by
  simp only [envArgs, List.finRange_succ, List.reverse_cons, List.map_append, List.map_reverse,
    List.map_map, List.map_cons, List.map_nil]
  rfl

theorem subArgs_consSub {N m : Nat} (L : CTm Head m) (σ : CSub Head N m) :
    subArgs (CTm.consSub L σ) = subArgs σ ++ [L] := by
  simp only [subArgs, List.finRange_succ, List.reverse_cons, List.map_append, List.map_reverse,
    List.map_map, List.map_cons, List.map_nil]
  rfl

theorem map_metaVars_subst {N m : Nat} (σ : CSub Head N m) :
    (metaVars N).map (fun t => (liftTm t).subst σ) = subArgs σ := by
  simp only [metaVars, subArgs, List.map_map]
  rfl

theorem map_metaVars_cinterp (Rd : Reading Head) {N : Nat} (ρ : Env N) :
    (metaVars N).map (fun t => cinterp Rd (liftTm t) ρ) = envArgs ρ := by
  simp only [metaVars, envArgs, List.map_map]
  rfl

theorem listCSub_shiftBy {N q m : Nat} (hq : q ≤ N) (ts : List (CTm Head m)) (i : Fin q) :
    listCSub N ts (shiftBy hq i) = listCSub q (ts.take q) i := by
  show ts.getD (N - 1 - (i.val + (N - q))) _ = (ts.take q).getD (q - 1 - i.val) _
  have hi := i.isLt
  rw [show N - 1 - (i.val + (N - q)) = q - 1 - i.val by omega, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]

theorem ofArgs_shiftBy {N q : Nat} (hq : q ≤ N) (vs : List Ideal) (i : Fin q) :
    Env.ofArgs N vs (shiftBy hq i) = Env.ofArgs q (vs.take q) i := by
  show vs.getD (N - 1 - (i.val + (N - q))) _ = (vs.take q).getD (q - 1 - i.val) _
  have hi := i.isLt
  rw [show N - 1 - (i.val + (N - q)) = q - 1 - i.val by omega, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]

/-- The entry at position `q` of a telescope, seen at its variable. -/
theorem lookup_ofEntries (e : (j : Nat) → Tm Head j) {M q : Nat} (hq : q < M) :
    (liftCtx (ofEntries e M)).lookup (metaIdx M q hq) =
      (liftTm (e q)).rename (shiftBy (Nat.le_of_lt hq)) := by
  rw [liftCtx_lookup, telescope_lookup e M q hq, liftTm_rename]

theorem lookup_ofEntries_subst (e : (j : Nat) → Tm Head j) {M q m : Nat} (hq : q < M)
    (ts : List (CTm Head m)) :
    ((liftCtx (ofEntries e M)).lookup (metaIdx M q hq)).subst (listCSub M ts) =
      (liftTm (e q)).subst (listCSub q (ts.take q)) := by
  rw [lookup_ofEntries, CTm.subst_rename]
  congr 1
  funext i
  exact listCSub_shiftBy _ ts i

theorem lookup_ofEntries_cinterp (Rd : Reading Head) (e : (j : Nat) → Tm Head j) {M q : Nat}
    (hq : q < M) (vs : List Ideal) :
    cinterp Rd ((liftCtx (ofEntries e M)).lookup (metaIdx M q hq)) (Env.ofArgs M vs) =
      cinterp Rd (liftTm (e q)) (Env.ofArgs q (vs.take q)) := by
  rw [lookup_ofEntries, cinterp_rename]
  congr 1
  funext i
  exact ofArgs_shiftBy _ vs i

theorem exists_metaIdx {M : Nat} (i : Fin M) : ∃ q, ∃ hq : q < M, i = metaIdx M q hq :=
  ⟨_, _, (metaIdx_back i).symm⟩

theorem ofEntries_congr {e e' : (j : Nat) → Tm Head j} :
    ∀ (M : Nat), (∀ j, j < M → e j = e' j) → ofEntries e M = ofEntries e' M
  | 0, _ => rfl
  | M + 1, h => by
      show Ctx.snoc (ofEntries e M) (e M) = Ctx.snoc (ofEntries e' M) (e' M)
      rw [ofEntries_congr M fun j hj => h j (Nat.lt_succ_of_lt hj), h M (Nat.lt_succ_self M)]

section Judgments

variable {R : Rules Head}

/-- **A context given by its entries is formed** when each entry is a type over the entries
before it. -/
theorem CCtxFormed.of_entries {P : ChurchRules R} (e : (j : Nat) → Tm Head j) :
    ∀ (M : Nat), (∀ q, q < M → CIsType P (liftCtx (ofEntries e q)) (liftTm (e q))) →
      CCtxFormed P (liftCtx (ofEntries e M))
  | 0, _ => .nil
  | M + 1, h => .snoc (CCtxFormed.of_entries e M fun q hq => h q (Nat.lt_succ_of_lt hq))
      (h M (Nat.lt_succ_self M))

/-- **A substitution of listed terms is typed along a context given by its entries** when each
term has its entry's type at the terms before it. -/
theorem CSubstMor.of_entries {P : ChurchRules R} (e : (j : Nat) → Tm Head j) {M m : Nat}
    {Δ : CCtx Head m} {ts : List (CTm Head m)}
    (h : ∀ q, q < M → CTyped P Δ (ts.getD q (.const .anonymous))
      ((liftTm (e q)).subst (listCSub q (ts.take q)))) :
    CSubstMor P (liftCtx (ofEntries e M)) Δ (listCSub M ts) := by
  intro i
  obtain ⟨q, hq, rfl⟩ := exists_metaIdx i
  rw [lookup_ofEntries_subst, listCSub_metaIdx]
  exact h q hq

theorem CSubstMor.entry {P : ChurchRules R} (e : (j : Nat) → Tm Head j) {M m : Nat}
    {Δ : CCtx Head m} {ts : List (CTm Head m)}
    (mor : CSubstMor P (liftCtx (Normalization.ofEntries e M)) Δ (listCSub M ts)) {q : Nat}
    (hq : q < M) :
    CTyped P Δ (ts.getD q (.const .anonymous)) ((liftTm (e q)).subst (listCSub q (ts.take q))) := by
  have h := mor (metaIdx M q hq)
  rw [lookup_ofEntries_subst, listCSub_metaIdx] at h
  exact h

/-- **An environment of listed values fits a context given by its entries** when each value is
an element of its entry's type at the values before it, which is a type. -/
theorem Fits.of_lookup (Rd : Reading Head) : ∀ {n : Nat} {Γ : CCtx Head n} {ρ : Env n},
    (∀ i, Ideal.TypeGenerated (cinterp Rd (Γ.lookup i) ρ) ∧
      projT (cinterp Rd (Γ.lookup i) ρ) (ρ i) = ρ i) → Fits Rd Γ ρ
  | _, .nil, _, _ => trivial
  | _, .snoc Γ A, ρ, h => by
      have h0 := h 0
      rw [CCtx.lookup_snoc_zero, cinterp_rename] at h0
      refine ⟨Fits.of_lookup Rd fun j => ?_, h0.1, h0.2⟩
      have hj := h j.succ
      rw [CCtx.lookup_snoc_succ, cinterp_rename] at hj
      exact hj

theorem Fits.of_entries (Rd : Reading Head) (e : (j : Nat) → Tm Head j) {M : Nat}
    {vs : List Ideal}
    (h : ∀ q, q < M → Ideal.TypeGenerated (cinterp Rd (liftTm (e q)) (Env.ofArgs q (vs.take q))) ∧
      projT (cinterp Rd (liftTm (e q)) (Env.ofArgs q (vs.take q))) (vs.getD q Ideal.bot) =
        vs.getD q Ideal.bot) :
    Fits Rd (liftCtx (ofEntries e M)) (Env.ofArgs M vs) := by
  refine Fits.of_lookup Rd fun i => ?_
  obtain ⟨q, hq, rfl⟩ := exists_metaIdx i
  rw [lookup_ofEntries_cinterp, ofArgs_metaIdx]
  exact h q hq

theorem Fits.entry (Rd : Reading Head) (e : (j : Nat) → Tm Head j) {M : Nat} {vs : List Ideal}
    (fits : Fits Rd (liftCtx (ofEntries e M)) (Env.ofArgs M vs)) {q : Nat} (hq : q < M) :
    Ideal.TypeGenerated (cinterp Rd (liftTm (e q)) (Env.ofArgs q (vs.take q))) ∧
      projT (cinterp Rd (liftTm (e q)) (Env.ofArgs q (vs.take q))) (vs.getD q Ideal.bot) =
        vs.getD q Ideal.bot := by
  have h := Fits.lookup fits (metaIdx M q hq)
  rwa [lookup_ofEntries_cinterp, ofArgs_metaIdx] at h

variable (Rd : Reading Head) {P : ChurchRules R} {K : RigidTypes P} (H : HeadReduction P K)

/-- **What related substitutions require at one entry**: the terms are typed and equal at the
entry's type, the entry's types under both substitutions are equal and related as far as its
type tokens observe, and the terms are related as far as the typed tokens of the value
observe. -/
def EntryRel {q m : Nat} (Δ : CCtx Head m) (A : CTm Head q) (ρ : Env q) (σ σ' : CSub Head q m)
    (v : Ideal) (t t' : CTm Head m) : Prop :=
  CTyped P Δ t (A.subst σ) ∧ CEqual P Δ t t' (A.subst σ) ∧
    CTypeEq P Δ (A.subst σ) (A.subst σ') ∧
    (∀ r, (cinterp Rd A ρ).Mem r → TyTok Elem.univ r →
      RT H Δ false r (A.subst σ) (A.subst σ) (A.subst σ')) ∧
    ∀ s, v.Mem s → TypedAt (cinterp Rd A ρ) s → RT H Δ true s (A.subst σ) t t'

/-- **Related substitutions of listed terms along a context given by its entries**, entry by
entry. -/
theorem SubstRel.of_entries (e : (j : Nat) → Tm Head j) {M m : Nat} {Δ : CCtx Head m}
    {vs : List Ideal} {ts ts' : List (CTm Head m)}
    (h : ∀ q, q < M → EntryRel Rd H Δ (liftTm (e q)) (Env.ofArgs q (vs.take q))
      (listCSub q (ts.take q)) (listCSub q (ts'.take q)) (vs.getD q Ideal.bot)
      (ts.getD q (.const .anonymous)) (ts'.getD q (.const .anonymous))) :
    SubstRel Rd H (liftCtx (ofEntries e M)) (Env.ofArgs M vs) Δ (listCSub M ts)
      (listCSub M ts') := by
  refine ⟨⟨fun i => ?_, fun i => ?_⟩, fun i => ?_⟩ <;> obtain ⟨q, hq, rfl⟩ := exists_metaIdx i <;>
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h q hq <;>
    simp only [lookup_ofEntries_subst, lookup_ofEntries_cinterp, listCSub_metaIdx,
      ofArgs_metaIdx]
  · exact h₁
  · exact h₂
  · exact ⟨h₃, h₄, h₅⟩

/-- **Related substitutions along a context given by its entries**, read entry by entry. -/
theorem SubstRel.entry (e : (j : Nat) → Tm Head j) {M m : Nat} {Δ : CCtx Head m}
    {vs : List Ideal} {ts ts' : List (CTm Head m)}
    (rel : SubstRel Rd H (liftCtx (ofEntries e M)) (Env.ofArgs M vs) Δ (listCSub M ts)
      (listCSub M ts')) {q : Nat} (hq : q < M) :
    EntryRel Rd H Δ (liftTm (e q)) (Env.ofArgs q (vs.take q))
      (listCSub q (ts.take q)) (listCSub q (ts'.take q)) (vs.getD q Ideal.bot)
      (ts.getD q (.const .anonymous)) (ts'.getD q (.const .anonymous)) := by
  have h₁ := rel.1.1 (metaIdx M q hq)
  have h₂ := rel.1.2 (metaIdx M q hq)
  have h₃ := rel.2 (metaIdx M q hq)
  simp only [lookup_ofEntries_subst, lookup_ofEntries_cinterp, listCSub_metaIdx,
    ofArgs_metaIdx] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

end Judgments

end Entries

/-! ## The recursor's spine -/

section Spine

variable (d : Datatype Tower.Head)

/-- The motive and the methods of the recursor: the first entries of its telescope. -/
abbrev recMethodsCtx : CCtx Tower.Head (d.ctors.length + 1) :=
  liftCtx (ofEntries (recEntry d.type d.motiveUniverse d.ctors) (d.ctors.length + 1))

/-- The context of the recursor's spine: the motive, the methods and an element of the
datatype. -/
abbrev recSpineCtx : CCtx Tower.Head (d.ctors.length + 2) :=
  liftCtx (recTele d.type d.motiveUniverse d.ctors)

/-- The recursor's spine at the variables of its context. -/
abbrev recSpineTm : CTm Tower.Head (d.ctors.length + 2) :=
  liftTm (appSpine (.const d.recursor) (metaVars (d.ctors.length + 2)))

/-- The motive at the element: the type of the recursor's spine. -/
abbrev recMotiveTm : CTm Tower.Head (d.ctors.length + 2) := liftTm (recBody d.ctors.length)

theorem recSpineCtx_eq : recSpineCtx d = .snoc (recMethodsCtx d) (.const d.type) := by
  show CCtx.snoc (recMethodsCtx d)
    (liftTm (recEntry d.type d.motiveUniverse d.ctors (d.ctors.length + 1))) = _
  rw [recEntry_scrutinee]
  rfl

theorem recSpineTm_subst {m : Nat} (L : CTm Tower.Head m)
    (τ : CSub Tower.Head (d.ctors.length + 1) m) :
    (recSpineTm d).subst (CTm.consSub L τ) =
      CTm.appSpine (.const d.recursor) (subArgs τ ++ [L]) := by
  rw [recSpineTm, liftTm_appSpine, csubst_appSpine, List.map_map]
  show CTm.appSpine (.const d.recursor) ((metaVars (d.ctors.length + 2)).map
    fun t => (liftTm t).subst (CTm.consSub L τ)) = _
  rw [map_metaVars_subst, subArgs_consSub]

theorem cinterp_recSpineTm (Rd : Reading Tower.Head) (x : Ideal)
    (ρ : Env (d.ctors.length + 1)) :
    cinterp Rd (recSpineTm d) (Env.cons x ρ) =
      Ideal.appSpine (Rd.const d.recursor) (envArgs ρ ++ [x]) := by
  rw [recSpineTm, liftTm_appSpine, cinterp_appSpine, List.map_map]
  show Ideal.appSpine (Rd.const d.recursor) ((metaVars (d.ctors.length + 2)).map
    fun t => cinterp Rd (liftTm t) (Env.cons x ρ)) = _
  rw [map_metaVars_cinterp, envArgs_cons]

theorem recMotiveTm_subst {m : Nat} (L : CTm Tower.Head m)
    (τ : CSub Tower.Head (d.ctors.length + 1) m) :
    (recMotiveTm d).subst (CTm.consSub L τ) = .app (τ (Fin.last d.ctors.length)) L :=
  rfl

/-- The motive at the element is a type of the motives' universe, derived with no constant. -/
theorem recMotiveTm_typed {R : Rules Tower.Head} {Q : ChurchRules R} :
    CTyped Q (recSpineCtx d) (recMotiveTm d) (.head d.motiveUniverse) := by
  have hq : 0 < d.ctors.length + 2 := Nat.succ_pos _
  have motive := CDerivable.var (P := Q)
    (Γ := liftCtx (ofEntries (recEntry d.type d.motiveUniverse d.ctors) (d.ctors.length + 2)))
    (metaIdx (d.ctors.length + 2) 0 hq)
  rw [lookup_ofEntries] at motive
  have last : metaIdx (d.ctors.length + 2) 0 hq = Fin.last (d.ctors.length + 1) :=
    Fin.ext (by show d.ctors.length + 2 - 1 - 0 = d.ctors.length + 1; omega)
  rw [last] at motive
  change CTyped Q (recSpineCtx d) (.var (Fin.last (d.ctors.length + 1)))
    (.pi (.const d.type) (.head d.motiveUniverse)) at motive
  rw [recSpineCtx_eq] at motive ⊢
  exact .appElim motive (.var 0)

variable {d} (hd : d.Admissible objectChurch)
include hd

/-- The recursor is declared at the dependent function type over the context of its spine. -/
theorem rec_declared' :
    (dataChurch d).constantType d.recursor = some (pisCtx (recSpineCtx d) (recMotiveTm d)) :=
  (sum_rec_declared (u := d.typeUniverse) (v := d.motiveUniverse) objectChurch hd.distinct
    hd.lamFree hd.new).trans (by rw [recType, liftTm_closeType])

/-- The entries of the recursor's telescope are types. -/
theorem recEntry_formed' (j : Nat) :
    CIsType (dataChurch d) (liftCtx (ofEntries (recEntry d.type d.motiveUniverse d.ctors) j))
      (liftTm (recEntry d.type d.motiveUniverse d.ctors j)) :=
  recEntry_formed ConvRules.objectLevels objectChurch hd.typeUniverse hd.motiveUniverse
    hd.distinct hd.lamFree hd.new hd.fieldsFormed j

theorem recSpineCtx_formed : CCtxFormed (dataChurch d) (recSpineCtx d) :=
  CCtxFormed.of_entries _ _ fun q _ => recEntry_formed' hd q

theorem recMethodsCtx_formed : CCtxFormed (dataChurch d) (recMethodsCtx d) :=
  CCtxFormed.of_entries _ _ fun q _ => recEntry_formed' hd q

/-- **The recursor's spine is typed** at the motive at the element. -/
theorem recSpineTm_typed :
    CTyped (dataChurch d) (recSpineCtx d) (recSpineTm d) (recMotiveTm d) := by
  have mor : CSubstMor (dataChurch d) (recSpineCtx d) (recSpineCtx d) CTm.ids := fun i => by
    rw [CTm.subst_ids]
    exact .var i
  have typed := rec_applied ConvRules.objectLevels objectChurch hd.typeUniverse hd.motiveUniverse
    hd.distinct hd.lamFree hd.new hd.fieldsFormed mor
  have ids : (fun i : Fin (d.ctors.length + 2) =>
      liftTm (Annotated.listSub (d.ctors.length + 2)
        (metaVars (Head := Tower.Head) (d.ctors.length + 2)) i)) =
      CTm.ids := by
    funext i
    show liftTm ((metaVars (d.ctors.length + 2)).getD (d.ctors.length + 2 - 1 - i.val) defaultTm) =
      CTm.ids i
    rw [List.getD_eq_getElem?_getD, metaVars_get? (index_lt _ i.val i.isLt), metaIdx_back]
    rfl
  have spine : applyAlong (fun i : Fin (d.ctors.length + 2) => liftTm (Annotated.listSub
      (d.ctors.length + 2) (metaVars (Head := Tower.Head) (d.ctors.length + 2)) i))
      (CTm.const d.recursor) = recSpineTm d :=
    applyAlong_listSub (Head := Tower.Head) (d.ctors.length + 2)
      (metaVars (d.ctors.length + 2)) (length_metaVars _) (.const d.recursor)
  rw [ids] at spine
  rw [spine] at typed
  exact typed

/-- The motives' universe is a universe of the package with the datatype. -/
theorem motiveUniverse_data : (dataRules d).isUniverse d.motiveUniverse :=
  (dataExtension hd).sub.isUniverse hd.motiveUniverse

/-- **The motive at the element is an adequate type.** -/
theorem adequateType_recMotive :
    AdequateType (dataExtension hd).reading (dataHead hd) (recSpineCtx d) (recMotiveTm d) :=
  ((dataExtension hd).valid_within (allowed := fun _ => false)
    (fun h => absurd h Bool.false_ne_true) (recMotiveTm_typed d)
    (recSpineCtx_formed hd)).1.adequateType
      (dataExtension hd).levels (dataExtension hd).soundnessFacts (motiveUniverse_data hd)

/-- **The element of the recursor's spine**: `rec P ms q ⟶ rec P ms q'` when `q ⟶ q'`. -/
theorem dataHead_rec {m : Nat} {pre : List (CTm Tower.Head m)}
    (hpre : pre.length = d.ctors.length + 1) {q q' : CTm Tower.Head m}
    (step : (dataHead hd).step q q') :
    (dataHead hd).step (CTm.appSpine (.const d.recursor) (pre ++ [q]))
      (CTm.appSpine (.const d.recursor) (pre ++ [q'])) :=
  CWhStepR.scrutinee (before := pre) (after := [])
    (by rw [hpre]; exact dataRoles_rec hd.distinct) (by rw [hpre]; rfl) step

theorem dataHead_rec_red {m : Nat} {pre : List (CTm Tower.Head m)}
    (hpre : pre.length = d.ctors.length + 1) {q q' : CTm Tower.Head m}
    (red : Relation.ReflTransGen (dataHead hd).step q q') :
    Relation.ReflTransGen (dataHead hd).step (CTm.appSpine (.const d.recursor) (pre ++ [q]))
      (CTm.appSpine (.const d.recursor) (pre ++ [q'])) :=
  Relation.ReflTransGen.lift (fun q => CTm.appSpine (.const d.recursor) (pre ++ [q]))
    (fun _ _ h => dataHead_rec hd hpre h) _ _ red

omit hd in
/-- **The computation rule of the recursor at a constructor**, as an annotated root step. -/
theorem dataChurch_iota_step {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) {m : Nat}
    (σ : CSub Tower.Head (1 + d.ctors.length + fs.length) m) :
    (dataChurch d).computation.step
      ((liftTm (iotaLeft d.recursor k d.ctors.length fs.length)).subst σ)
      ((liftTm (iotaRight d.recursor d.ctors.length i fs)).subst σ) := by
  have eL := elabLeft_firstOrder (elabDeclarations (inductiveRules (rulesWith objectRules [])
    d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse).constantType)
    (firstOrder_iotaLeft d.recursor k d.ctors.length fs.length)
  have eR : elabRight (elabDeclarations (inductiveRules (rulesWith objectRules []) d.type
      d.typeUniverse d.ctors d.recursor d.motiveUniverse).constantType)
      (iotaLeft d.recursor k d.ctors.length fs.length)
      (iotaRight d.recursor d.ctors.length i fs) =
      liftTm (iotaRight d.recursor d.ctors.length i fs) :=
    elab_lamFree _ (lamFree_iotaRight _ _ i fs) _ _ _
  have st : (dataChurch d).computation.step
      ((elabLeft (elabDeclarations (inductiveRules (rulesWith objectRules []) d.type
        d.typeUniverse d.ctors d.recursor d.motiveUniverse).constantType)
        (iotaLeft d.recursor k d.ctors.length fs.length)).subst σ)
      ((elabRight (elabDeclarations (inductiveRules (rulesWith objectRules []) d.type
        d.typeUniverse d.ctors d.recursor d.motiveUniverse).constantType)
        (iotaLeft d.recursor k d.ctors.length fs.length)
        (iotaRight d.recursor d.ctors.length i fs)).subst σ) :=
    .inr (.instantiate ⟨_, _, ⟨i, k, fs, entry, rfl⟩, rfl, rfl⟩ σ)
  rw [eL, eR] at st
  exact st

omit hd in
theorem liftTm_getD_subst {N m : Nat} (l : List (Tm Tower.Head N)) (j : Nat)
    (σ : CSub Tower.Head N m) :
    (liftTm (l.getD j defaultTm)).subst σ =
      (l.map fun t => (liftTm t).subst σ).getD j (.const .anonymous) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

omit hd in
theorem map_metaVars_listCSub {N m : Nat} {ts : List (CTm Tower.Head m)} (h : ts.length = N) :
    (metaVars N).map (fun t => (liftTm t).subst (listCSub N ts)) = ts := by
  rw [map_metaVars_subst, subArgs_listCSub h]

omit hd in
/-- The left side of the computation rule at the motive and methods `τ` and the fields `ms`. -/
theorem iotaLeft_listCSub {k : DeclName} {a m : Nat} (τ : CSub Tower.Head (d.ctors.length + 1) m)
    {ms : List (CTm Tower.Head m)} (hms : ms.length = a) :
    (liftTm (iotaLeft d.recursor k d.ctors.length a)).subst
        (listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms)) =
      CTm.appSpine (.const d.recursor) (subArgs τ ++ [CTm.appSpine (.const k) ms]) := by
  have hlen : (subArgs τ ++ ms).length = 1 + d.ctors.length + a := by
    rw [List.length_append, length_subArgs, hms]; omega
  rw [iotaLeft_subst, map_metaVars_listCSub hlen,
    List.take_left' (by rw [length_subArgs]; omega),
    List.drop_left' (by rw [length_subArgs]; omega)]

omit hd in
/-- The right side of the computation rule of the constructor at `i`, at the motive and methods
`τ` and the fields `ms`: the method applied to the fields and to the recursor at each recursive
field. -/
theorem iotaRight_listCSub {i : Nat} {fs : List CtorField} {m : Nat}
    (τ : CSub Tower.Head (d.ctors.length + 1) m) {ms : List (CTm Tower.Head m)}
    (hms : ms.length = fs.length) :
    (liftTm (iotaRight d.recursor d.ctors.length i fs)).subst
        (listCSub (1 + d.ctors.length + fs.length) (subArgs τ ++ ms)) =
      CTm.appSpine ((subArgs τ).getD (1 + i) (.const .anonymous))
        (ms ++ (Ideal.recFields (fs.map fieldFlag) ms).map
          fun t => CTm.appSpine (.const d.recursor) (subArgs τ ++ [t])) := by
  have hlen : (subArgs τ ++ ms).length = 1 + d.ctors.length + fs.length := by
    rw [List.length_append, length_subArgs, hms]; omega
  rw [iotaRight_subst, liftTm_getD_subst, List.map_take, map_metaVars_listCSub hlen,
    List.take_left' (by rw [length_subArgs]; omega),
    List.drop_left' (by rw [length_subArgs]; omega)]

/-- **The computation rule of the recursor at a constructor, as a weak-head step.** -/
theorem dataHead_iota {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) {m : Nat} (τ : CSub Tower.Head (d.ctors.length + 1) m)
    {ms : List (CTm Tower.Head m)} (hms : ms.length = fs.length) :
    (dataHead hd).step
      (CTm.appSpine (.const d.recursor) (subArgs τ ++ [CTm.appSpine (.const k) ms]))
      (CTm.appSpine ((subArgs τ).getD (1 + i) (.const .anonymous))
        (ms ++ (Ideal.recFields (fs.map fieldFlag) ms).map
          fun t => CTm.appSpine (.const d.recursor) (subArgs τ ++ [t]))) := by
  have st := dataChurch_iota_step entry
    (listCSub (1 + d.ctors.length + fs.length) (subArgs τ ++ ms))
  rw [iotaLeft_listCSub τ hms, iotaRight_listCSub τ hms] at st
  exact (dataHead hd).root st

end Spine

/-! ## The case of a constructor

At a constructor, the recursor computes by the constructor's method applied to the fields and to
the recursor at each recursive field. The method's application is typed, with no constant, over
the context of the case (`caseEntry`): the motive, the methods, the constructor's fields, and one
hypothesis, the motive at the field, for each recursive field. -/

section Lists

theorem getD_map_lt {α β : Type} (g : α → β) {l : List α} {j : Nat} (below : j < l.length)
    (dflt : α) (dflt' : β) : (l.map g).getD j dflt' = g (l.getD j dflt) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem below]
  rfl

theorem getD_append_lt {α : Type} {l : List α} {j : Nat} (below : j < l.length) (l' : List α)
    (dflt : α) : (l ++ l').getD j dflt = l.getD j dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left below]

theorem getD_append_ge {α : Type} {l : List α} {j : Nat} (above : l.length ≤ j) (l' : List α)
    (dflt : α) : (l ++ l').getD j dflt = l'.getD (j - l.length) dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right above]

/-- The positions of the set flags. -/
def flagPositions : List Bool → List Nat
  | [] => []
  | true :: bs => 0 :: (flagPositions bs).map (· + 1)
  | false :: bs => (flagPositions bs).map (· + 1)

/-- The entries at the set flags are the entries at their positions. -/
theorem recFields_eq_map {α : Type} (dflt : α) : ∀ (bs : List Bool) (xs : List α),
    xs.length = bs.length → Ideal.recFields bs xs = (flagPositions bs).map (xs.getD · dflt)
  | [], [], _ => rfl
  | true :: bs, x :: xs, h => by
      rw [Ideal.recFields, flagPositions, List.map_cons, List.map_map,
        recFields_eq_map dflt bs xs (Nat.succ.inj h)]
      rfl
  | false :: bs, x :: xs, h => by
      rw [Ideal.recFields, flagPositions, List.map_map,
        recFields_eq_map dflt bs xs (Nat.succ.inj h)]
      rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem length_recFields {α : Type} {bs : List Bool} {xs : List α} (h : xs.length = bs.length) :
    (Ideal.recFields bs xs).length = (flagPositions bs).length := by
  cases xs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => exact nomatch h
  | cons x xs => rw [recFields_eq_map x bs _ h, List.length_map]

/-- A position of a set flag carries a set flag. -/
theorem flagPositions_getElem? : ∀ {bs : List Bool} {p : Nat}, p ∈ flagPositions bs →
    bs[p]? = some true
  | [], _, h => nomatch h
  | true :: bs, p, h => by
      rcases List.mem_cons.1 h with rfl | h
      · rfl
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 h
        have e := flagPositions_getElem? hp'
        exact e
  | false :: bs, p, h => by
      obtain ⟨p', hp', rfl⟩ := List.mem_map.1 h
      have e := flagPositions_getElem? hp'
      exact e

/-- A position of a recursive field is the position of a recursive field. -/
theorem flagPositions_recursive {fs : List CtorField} {p : Nat}
    (h : p ∈ flagPositions (fs.map fieldFlag)) : fs[p]? = some .recursive := by
  have e := flagPositions_getElem? h
  rw [List.getElem?_map] at e
  cases hf : fs[p]? with
  | none => rw [hf] at e; cases e
  | some f =>
      rw [hf] at e
      cases f with
      | recursive => rfl
      | closed F => cases e

theorem flagPositions_getD_mem {bs : List Bool} {r : Nat} (hr : r < (flagPositions bs).length) :
    (flagPositions bs).getD r 0 ∈ flagPositions bs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact List.getElem_mem hr

theorem flagPositions_lt {fs : List CtorField} {p : Nat}
    (h : p ∈ flagPositions (fs.map fieldFlag)) : p < fs.length :=
  (List.getElem?_eq_some_iff.1 (flagPositions_recursive h)).1

end Lists

section Case

variable (d : Datatype Tower.Head) (fs : List CtorField)

/-- The number of recursive fields. -/
abbrev recCount : Nat := (flagPositions (fs.map fieldFlag)).length

/-- The position of the field of the hypothesis `r`. -/
abbrev hypField (r : Nat) : Nat := (flagPositions (fs.map fieldFlag)).getD r 0

/-- The number of variables of the case. -/
abbrev caseArity : Nat := 1 + d.ctors.length + fs.length + recCount fs

/-- **The telescope of the case of a constructor**: the motive, the methods and the fields, as in
the computation rule, then one hypothesis for each recursive field, the motive at the field. -/
def caseEntry (j : Nat) : Tm Tower.Head j :=
  if hj : j < 1 + d.ctors.length + fs.length then iotaEntry d.type d.motiveUniverse d.ctors fs j
  else .app (.var ⟨j - 1, by omega⟩)
    (.var ⟨j - 1 - (1 + d.ctors.length + hypField fs (j - (1 + d.ctors.length + fs.length))),
      by omega⟩)

theorem caseArity_eq : caseArity d fs = 1 + d.ctors.length + fs.length + recCount fs := rfl

/-- `omega` after unfolding the number of variables of a case. -/
local macro "arity_omega" : tactic => `(tactic| ((try simp only [caseArity] at *) <;> omega))

/-- The context of the case. -/
abbrev caseCtx : CCtx Tower.Head (caseArity d fs) :=
  liftCtx (ofEntries (caseEntry d fs) (caseArity d fs))

theorem caseEntry_method {j : Nat} (hj : j ≤ d.ctors.length) :
    caseEntry d fs j = recEntry d.type d.motiveUniverse d.ctors j := by
  rw [caseEntry, dif_pos (by omega), iotaEntry_of_le hj]

theorem caseEntry_field {p : Nat} (hp : p < fs.length) :
    caseEntry d fs (1 + d.ctors.length + p) =
      Presentation.liftClosed ((fs.getD p .recursive).type d.type) := by
  rw [caseEntry, dif_pos (by omega), Nat.add_comm 1 d.ctors.length, iotaEntry_field hp]

theorem caseEntry_prefix {q : Nat} (hq : q ≤ d.ctors.length + 1) :
    ofEntries (caseEntry d fs) q = ofEntries (recEntry d.type d.motiveUniverse d.ctors) q :=
  ofEntries_congr q fun j hj => caseEntry_method d fs (by omega)

/-- The hypothesis at `q`, substituted. -/
theorem caseEntry_hyp_subst {q m : Nat} (h₁ : 1 + d.ctors.length + fs.length ≤ q)
    (h₂ : hypField fs (q - (1 + d.ctors.length + fs.length)) < fs.length)
    (ts : List (CTm Tower.Head m)) :
    (liftTm (caseEntry d fs q)).subst (listCSub q ts) =
      .app (ts.getD 0 (.const .anonymous))
        (ts.getD (1 + d.ctors.length + hypField fs (q - (1 + d.ctors.length + fs.length)))
          (.const .anonymous)) := by
  have e₁ : q - 1 - (q - 1) = 0 := by omega
  have e₂ : q - 1 - (q - 1 - (1 + d.ctors.length +
      hypField fs (q - (1 + d.ctors.length + fs.length)))) =
      1 + d.ctors.length + hypField fs (q - (1 + d.ctors.length + fs.length)) := by omega
  rw [caseEntry, dif_neg (by omega)]
  exact congrArg₂ CTm.app (congrArg (fun j => ts.getD j _) e₁)
    (congrArg (fun j => ts.getD j _) e₂)

/-- The hypothesis at `q`, read. -/
theorem caseEntry_hyp_cinterp (Rd : Reading Tower.Head) {q : Nat}
    (h₁ : 1 + d.ctors.length + fs.length ≤ q)
    (h₂ : hypField fs (q - (1 + d.ctors.length + fs.length)) < fs.length) (vs : List Ideal) :
    cinterp Rd (liftTm (caseEntry d fs q)) (Env.ofArgs q vs) =
      Ideal.app (vs.getD 0 Ideal.bot)
        (vs.getD (1 + d.ctors.length + hypField fs (q - (1 + d.ctors.length + fs.length)))
          Ideal.bot) := by
  have e₁ : q - 1 - (q - 1) = 0 := by omega
  have e₂ : q - 1 - (q - 1 - (1 + d.ctors.length +
      hypField fs (q - (1 + d.ctors.length + fs.length)))) =
      1 + d.ctors.length + hypField fs (q - (1 + d.ctors.length + fs.length)) := by omega
  rw [caseEntry, dif_neg (by omega)]
  exact congrArg₂ Ideal.app (congrArg (fun j => vs.getD j _) e₁)
    (congrArg (fun j => vs.getD j _) e₂)

/-- The variables of the fields, the first one first. -/
def caseFieldVars : List (Tm Tower.Head (caseArity d fs)) :=
  ((metaVars (caseArity d fs)).drop (1 + d.ctors.length)).take fs.length

/-- The variables of the hypotheses. -/
def caseHypVars : List (Tm Tower.Head (caseArity d fs)) :=
  (metaVars (caseArity d fs)).drop (1 + d.ctors.length + fs.length)

/-- The variable of the motive. -/
def caseMotive : Tm Tower.Head (caseArity d fs) := (metaVars (caseArity d fs)).getD 0 defaultTm

/-- **The method of the constructor at `i` applied to the fields and to the hypotheses.** -/
def caseBody (i : Nat) : Tm Tower.Head (caseArity d fs) :=
  appSpine ((metaVars (caseArity d fs)).getD (i + 1) defaultTm)
    (caseFieldVars d fs ++ caseHypVars d fs)

/-- **The motive at the constructor `k` applied to the fields.** -/
def caseTarget (k : DeclName) : Tm Tower.Head (caseArity d fs) :=
  .app (caseMotive d fs) (appSpine (.const k) (caseFieldVars d fs))

theorem caseFieldVars_getElem? {p : Nat} (hp : p < fs.length) :
    (caseFieldVars d fs)[p]? =
      some (.var (metaIdx (caseArity d fs) (1 + d.ctors.length + p) (by arity_omega))) := by
  rw [caseFieldVars, List.getElem?_take_of_lt hp, List.getElem?_drop, metaVars_get?]

theorem length_caseFieldVars : (caseFieldVars d fs).length = fs.length := by
  rw [caseFieldVars, List.length_take, List.length_drop, length_metaVars]
  have := caseArity_eq d fs
  omega

theorem caseHypVars_getElem? {r : Nat} (hr : r < recCount fs) :
    (caseHypVars d fs)[r]? =
      some (.var (metaIdx (caseArity d fs) (1 + d.ctors.length + fs.length + r)
        (by arity_omega))) := by
  rw [caseHypVars, List.getElem?_drop, metaVars_get?]

theorem length_caseHypVars : (caseHypVars d fs).length = recCount fs := by
  rw [caseHypVars, List.length_drop, length_metaVars]
  have := caseArity_eq d fs
  omega

theorem caseMotive_eq : caseMotive d fs = .var (metaIdx (caseArity d fs) 0 (by arity_omega)) := by
  rw [caseMotive, List.getD_eq_getElem?_getD, metaVars_get?]
  rfl

theorem caseMethod_eq {i : Nat} (hi : i < d.ctors.length) :
    (metaVars (Head := Tower.Head) (caseArity d fs)).getD (i + 1) defaultTm =
      .var (metaIdx (caseArity d fs) (i + 1) (by arity_omega)) := by
  rw [List.getD_eq_getElem?_getD, metaVars_get?]
  rfl

/-- The recursive fields among the variables of the fields are the variables at the positions of
the recursive fields. -/
theorem recArgs_caseFieldVars :
    recArgs fs (caseFieldVars d fs) =
      (flagPositions (fs.map fieldFlag)).map ((caseFieldVars d fs).getD · defaultTm) := by
  rw [recArgs_eq_recFields, recFields_eq_map defaultTm _ _
    (by rw [length_caseFieldVars, List.length_map])]

omit d fs in
/-- A variable of a context given by its entries, typed at its entry at the earlier variables. -/
theorem var_ofEntries_typed {R : Rules Tower.Head} {P : ChurchRules R}
    (e : (j : Nat) → Tm Tower.Head j) {M q : Nat} (hq : q < M) :
    CTyped P (liftCtx (ofEntries e M)) (.var (metaIdx M q hq))
      ((liftTm (e q)).subst (listCSub q ((subArgs (CTm.ids : CSub Tower.Head M M)).take q))) := by
  have t := CDerivable.var (P := P) (Γ := liftCtx (ofEntries e M)) (metaIdx M q hq)
  rw [← CTm.subst_ids ((liftCtx (ofEntries e M)).lookup (metaIdx M q hq)),
    ← listCSub_subArgs (CTm.ids : CSub Tower.Head M M), lookup_ofEntries_subst] at t
  exact t

omit d fs in
theorem subArgs_ids_take_getD {M q j : Nat} (hj : j < q) (hq : q ≤ M) (dflt : CTm Tower.Head M) :
    ((subArgs (CTm.ids : CSub Tower.Head M M)).take q).getD j dflt =
      .var (metaIdx M j (by omega)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, subArgs_getElem? _ (by omega)]
  rfl

/-- The variable of a hypothesis is typed at the motive at its field, in every package. -/
theorem caseHyp_typed {R : Rules Tower.Head} {Q : ChurchRules R} {r : Nat}
    (hr : r < recCount fs) :
    CTyped Q (caseCtx d fs) (.var (metaIdx (caseArity d fs) (1 + d.ctors.length + fs.length + r)
        (by arity_omega)))
      (.app (.var (metaIdx (caseArity d fs) 0 (by arity_omega)))
        (.var (metaIdx (caseArity d fs) (1 + d.ctors.length + hypField fs r)
          (by
            have : hypField fs r < fs.length := flagPositions_lt (flagPositions_getD_mem hr)
            arity_omega)))) := by
  have hp : hypField fs r < fs.length := flagPositions_lt (flagPositions_getD_mem hr)
  have t := var_ofEntries_typed (P := Q) (caseEntry d fs)
    (M := caseArity d fs) (q := 1 + d.ctors.length + fs.length + r) (by arity_omega)
  have hidx : 1 + d.ctors.length + fs.length + r - (1 + d.ctors.length + fs.length) = r := by
    omega
  rw [caseEntry_hyp_subst d fs (by arity_omega) (by rw [hidx]; exact hp), hidx,
    subArgs_ids_take_getD (by arity_omega) (by arity_omega),
    subArgs_ids_take_getD (by arity_omega) (by arity_omega)] at t
  exact t

/-- **The method applied to the fields and to the hypotheses is typed at the motive at the
constructor applied to the fields**, in every package: the method has the type of the cases of
the constructor, the fields have their types, and each hypothesis is the motive at its field. -/
theorem caseBody_typed {R : Rules Tower.Head} {Q : ChurchRules R} {i : Nat} {k : DeclName}
    (entry : d.ctors[i]? = some (k, fs)) :
    CTyped Q (caseCtx d fs) (liftTm (caseBody d fs i)) (liftTm (caseTarget d fs k)) := by
  have hi : i < d.ctors.length := (List.getElem?_eq_some_iff.1 entry).1
  -- the method
  have method : CTyped Q (caseCtx d fs)
      (liftTm ((metaVars (caseArity d fs)).getD (i + 1) defaultTm))
      (liftTm (caseFields d.type k fs (caseMotive d fs) [] [])) := by
    have t := CDerivable.var (P := Q) (Γ := liftCtx (ofEntries (caseEntry d fs) (caseArity d fs)))
      (metaIdx (caseArity d fs) (i + 1) (by arity_omega))
    rw [lookup_ofEntries, caseEntry_method d fs (by arity_omega), recEntry_method _ _ _ entry,
      ← liftTm_rename, ← subst_renSub, subst_caseType] at t
    have motive : Presentation.subst (renSub (shiftBy (Nat.le_of_lt (show i + 1 < caseArity d fs
        by arity_omega)))) (Tm.var (Fin.last i)) = caseMotive d fs := by
      rw [caseMotive_eq]
      exact congrArg Tm.var (Fin.ext (by
        show i + (caseArity d fs - (i + 1)) = caseArity d fs - 1 - 0
        have := caseArity_eq d fs
        omega))
    rw [motive] at t
    rw [caseMethod_eq d fs hi]
    exact t
  -- the fields
  have fields : List.Forall₂ (fun x (field : CtorField) =>
      CTyped Q (caseCtx d fs) (liftTm x) (liftTm (field.type d.type)).liftClosed)
      (caseFieldVars d fs) fs := by
    refine List.forall₂_iff_get.mpr ⟨length_caseFieldVars d fs, fun p h₁ h₂ => ?_⟩
    have hp : p < fs.length := h₂
    have element : (caseFieldVars d fs).get ⟨p, h₁⟩ =
        .var (metaIdx (caseArity d fs) (1 + d.ctors.length + p) (by arity_omega)) :=
      Option.some.inj ((List.getElem?_eq_getElem h₁).symm.trans (caseFieldVars_getElem? d fs hp))
    rw [element]
    have t := CDerivable.var (P := Q) (Γ := liftCtx (ofEntries (caseEntry d fs) (caseArity d fs)))
      (metaIdx (caseArity d fs) (1 + d.ctors.length + p) (by arity_omega))
    rw [lookup_ofEntries, caseEntry_field d fs hp, liftTm_liftClosed, CTm.rename_liftClosed,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some] at t
    exact t
  -- the hypotheses
  have hyps : List.Forall₂ (fun h r => CTyped Q (caseCtx d fs) (liftTm h)
      (liftTm (.app (caseMotive d fs) r))) (caseHypVars d fs)
      ([] ++ recArgs fs (caseFieldVars d fs)) := by
    rw [List.nil_append, recArgs_caseFieldVars]
    refine List.forall₂_iff_get.mpr ⟨by rw [length_caseHypVars, List.length_map], fun r h₁ h₂ => ?_⟩
    have hr : r < recCount fs := by rw [length_caseHypVars] at h₁; exact h₁
    have hp : hypField fs r < fs.length := flagPositions_lt (flagPositions_getD_mem hr)
    have element : (caseHypVars d fs).get ⟨r, h₁⟩ =
        .var (metaIdx (caseArity d fs) (1 + d.ctors.length + fs.length + r) (by arity_omega)) :=
      Option.some.inj ((List.getElem?_eq_getElem h₁).symm.trans (caseHypVars_getElem? d fs hr))
    have target : ((flagPositions (fs.map fieldFlag)).map
        ((caseFieldVars d fs).getD · defaultTm)).get ⟨r, h₂⟩ =
        .var (metaIdx (caseArity d fs) (1 + d.ctors.length + hypField fs r) (by arity_omega)) := by
      have hr' : r < (flagPositions (fs.map fieldFlag)).length := hr
      have hget : hypField fs r = (flagPositions (fs.map fieldFlag))[r] := by
        show (flagPositions (fs.map fieldFlag)).getD r 0 = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
      rw [List.get_eq_getElem, List.getElem_map, ← hget, List.getD_eq_getElem?_getD,
        caseFieldVars_getElem? d fs hp, Option.getD_some]
    rw [element, target, caseMotive_eq]
    exact caseHyp_typed d fs hr
  have whole := caseFields_applied (Q := Q) d.type k fs (caseMotive d fs) [] []
    (caseFieldVars d fs) (caseHypVars d fs) ((metaVars (caseArity d fs)).getD (i + 1) defaultTm)
    method fields hyps
  rw [List.nil_append] at whole
  exact whole

omit d fs in
theorem subArgs_ids_getD {M j : Nat} (hj : j < M) (dflt : CTm Tower.Head M) :
    (subArgs (CTm.ids : CSub Tower.Head M M)).getD j dflt = .var (metaIdx M j hj) := by
  rw [List.getD_eq_getElem?_getD, subArgs_getElem? _ hj]
  rfl

/-- The hypothesis at `q` is the motive at its field. -/
theorem liftTm_caseEntry_hyp {q : Nat} (h₁ : 1 + d.ctors.length + fs.length ≤ q)
    (h₂ : hypField fs (q - (1 + d.ctors.length + fs.length)) < fs.length) :
    liftTm (caseEntry d fs q) = .app (.var (metaIdx q 0 (by omega)))
      (.var (metaIdx q (1 + d.ctors.length + hypField fs (q - (1 + d.ctors.length + fs.length)))
        (by omega))) := by
  have e := caseEntry_hyp_subst d fs h₁ h₂ (subArgs (CTm.ids : CSub Tower.Head q q))
  rw [listCSub_subArgs, CTm.subst_ids, subArgs_ids_getD (by omega),
    subArgs_ids_getD (by omega)] at e
  exact e

/-- The method applied to the fields and to the hypotheses, substituted. -/
theorem caseBody_subst {i m : Nat} (hi : i < d.ctors.length) {ts : List (CTm Tower.Head m)}
    (hts : ts.length = caseArity d fs) :
    (liftTm (caseBody d fs i)).subst (listCSub (caseArity d fs) ts) =
      CTm.appSpine (ts.getD (i + 1) (.const .anonymous))
        (((ts.drop (1 + d.ctors.length)).take fs.length) ++
          ts.drop (1 + d.ctors.length + fs.length)) := by
  simp only [caseBody, caseFieldVars, caseHypVars, liftTm_appSpine, csubst_appSpine, List.map_map,
    List.map_append, List.map_take, List.map_drop, Function.comp_def]
  rw [caseMethod_eq d fs hi, map_metaVars_listCSub hts]
  exact congrArg₂ CTm.appSpine (listCSub_metaIdx ts _) rfl

/-- The motive at the constructor applied to the fields, substituted. -/
theorem caseTarget_subst {k : DeclName} {m : Nat} {ts : List (CTm Tower.Head m)}
    (hts : ts.length = caseArity d fs) :
    (liftTm (caseTarget d fs k)).subst (listCSub (caseArity d fs) ts) =
      .app (ts.getD 0 (.const .anonymous))
        (CTm.appSpine (.const k) ((ts.drop (1 + d.ctors.length)).take fs.length)) := by
  have e : (liftTm (caseTarget d fs k)).subst (listCSub (caseArity d fs) ts) =
      .app ((liftTm (caseMotive d fs)).subst (listCSub (caseArity d fs) ts))
        ((liftTm (appSpine (.const k) (caseFieldVars d fs))).subst
          (listCSub (caseArity d fs) ts)) := rfl
  rw [e, caseMotive_eq]
  simp only [caseFieldVars, liftTm_appSpine, csubst_appSpine, List.map_map, List.map_take,
    List.map_drop, Function.comp_def]
  rw [map_metaVars_listCSub hts]
  exact congrArg₂ CTm.app (listCSub_metaIdx ts _) rfl

/-- The method applied to the fields and to the hypotheses, read. -/
theorem caseBody_cinterp (Rd : Reading Tower.Head) {i : Nat} (hi : i < d.ctors.length)
    {vs : List Ideal} (hvs : vs.length = caseArity d fs) :
    cinterp Rd (liftTm (caseBody d fs i)) (Env.ofArgs (caseArity d fs) vs) =
      Ideal.appSpine (vs.getD (i + 1) Ideal.bot)
        (((vs.drop (1 + d.ctors.length)).take fs.length) ++
          vs.drop (1 + d.ctors.length + fs.length)) := by
  simp only [caseBody, caseFieldVars, caseHypVars, liftTm_appSpine, cinterp_appSpine, List.map_map,
    List.map_append, List.map_take, List.map_drop, Function.comp_def]
  rw [caseMethod_eq d fs hi, map_metaVars_cinterp, envArgs_ofArgs hvs]
  exact congrArg₂ Ideal.appSpine (ofArgs_metaIdx vs _) rfl

/-- The motive at the constructor applied to the fields, read. -/
theorem caseTarget_cinterp (Rd : Reading Tower.Head) {k : DeclName} {vs : List Ideal}
    (hvs : vs.length = caseArity d fs) :
    cinterp Rd (liftTm (caseTarget d fs k)) (Env.ofArgs (caseArity d fs) vs) =
      Ideal.app (vs.getD 0 Ideal.bot)
        (Ideal.appSpine (Rd.const k) ((vs.drop (1 + d.ctors.length)).take fs.length)) := by
  have e : cinterp Rd (liftTm (caseTarget d fs k)) (Env.ofArgs (caseArity d fs) vs) =
      Ideal.app (cinterp Rd (liftTm (caseMotive d fs)) (Env.ofArgs (caseArity d fs) vs))
        (cinterp Rd (liftTm (appSpine (.const k) (caseFieldVars d fs)))
          (Env.ofArgs (caseArity d fs) vs)) := rfl
  rw [e, caseMotive_eq]
  simp only [caseFieldVars, liftTm_appSpine, cinterp_appSpine, List.map_map, List.map_take,
    List.map_drop, Function.comp_def]
  rw [map_metaVars_cinterp, envArgs_ofArgs hvs]
  exact congrArg₂ Ideal.app (ofArgs_metaIdx vs _) rfl

section Formed

variable {d fs} (hd : d.Admissible objectChurch) {i : Nat} {k : DeclName}
  (entry : d.ctors[i]? = some (k, fs))
include hd entry

/-- The type of a field is a type, in every context. -/
theorem caseFieldType_formed {p : Nat} (hp : p < fs.length) {n : Nat} {Γ : CCtx Tower.Head n} :
    CIsType (dataChurch d) Γ (liftTm ((fs.getD p .recursive).type d.type)).liftClosed :=
  (withInductive_declaresDataType (v := d.motiveUniverse) (rec := d.recursor) objectChurch
    hd.typeUniverse hd.new hd.fieldsFormed).fieldType_formed (dataExtension hd).levels
    (List.mem_of_getElem? entry)
    (.inr (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
      exact List.getElem_mem hp))

/-- **The context of the case is formed.** -/
theorem caseCtx_formed : CCtxFormed (dataChurch d) (caseCtx d fs) := by
  refine CCtxFormed.of_entries _ _ fun q hq => ?_
  rcases Nat.lt_or_ge q (d.ctors.length + 1) with h₁ | h₁
  · rw [caseEntry_method d fs (by omega), caseEntry_prefix d fs (by omega)]
    exact recEntry_formed' hd q
  rcases Nat.lt_or_ge q (1 + d.ctors.length + fs.length) with h₂ | h₂
  · obtain ⟨p, rfl⟩ : ∃ p, q = 1 + d.ctors.length + p := ⟨q - (1 + d.ctors.length), by omega⟩
    rw [caseEntry_field d fs (by omega), liftTm_liftClosed]
    exact caseFieldType_formed hd entry (by omega)
  · have hr : q - (1 + d.ctors.length + fs.length) < recCount fs := by
      have := caseArity_eq d fs
      omega
    have hp : hypField fs (q - (1 + d.ctors.length + fs.length)) < fs.length :=
      flagPositions_lt (flagPositions_getD_mem hr)
    rw [liftTm_caseEntry_hyp d fs h₂ hp]
    have motive : CTyped (dataChurch d) (liftCtx (ofEntries (caseEntry d fs) q))
        (.var (metaIdx q 0 (by omega))) (.pi (.const d.type) (.head d.motiveUniverse)) := by
      have t := var_ofEntries_typed (P := dataChurch d) (caseEntry d fs) (M := q) (q := 0)
        (by omega)
      rw [caseEntry_method d fs (Nat.zero_le _)] at t
      exact t
    have field := var_ofEntries_typed (P := dataChurch d) (caseEntry d fs) (M := q)
      (q := 1 + d.ctors.length + hypField fs (q - (1 + d.ctors.length + fs.length))) (by omega)
    rw [caseEntry_field d fs hp, liftTm_liftClosed, CTm.subst_liftClosed,
      List.getD_eq_getElem?_getD, flagPositions_recursive (flagPositions_getD_mem hr)] at field
    exact ⟨d.motiveUniverse, motiveUniverse_data hd, .appElim motive field⟩

end Formed

end Case

/-! ## The relation at the case of a constructor -/

section CaseRelation

theorem getD_take_of_lt {α : Type} {l : List α} {j n : Nat} (hj : j < n) (dflt : α) :
    (l.take n).getD j dflt = l.getD j dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

theorem tail_getD {α : Type} (l : List α) (i : Nat) (dflt : α) :
    l.tail.getD i dflt = l.getD (i + 1) dflt := by
  cases l <;> rfl

theorem headD_eq_getD {α : Type} (l : List α) (dflt : α) : l.headD dflt = l.getD 0 dflt := by
  cases l <;> rfl

theorem envArgs_getD_zero {N : Nat} (ρ : Env (N + 1)) :
    (envArgs ρ).getD 0 Ideal.bot = ρ (Fin.last N) := by
  rw [List.getD_eq_getElem?_getD, envArgs_getElem? ρ (Nat.succ_pos N)]
  exact congrArg ρ (Fin.ext (by show N + 1 - 1 - 0 = N; omega))

theorem subArgs_getD_zero {N m : Nat} (σ : CSub Tower.Head (N + 1) m) (dflt : CTm Tower.Head m) :
    (subArgs σ).getD 0 dflt = σ (Fin.last N) := by
  rw [List.getD_eq_getElem?_getD, subArgs_getElem? σ (Nat.succ_pos N)]
  exact congrArg σ (Fin.ext (by show N + 1 - 1 - 0 = N; omega))

/-- Fields equal one by one are equal at each field's type. -/
theorem FieldsEqual.get {R : Rules Tower.Head} {P : ChurchRules R} {K : RigidTypes P} {m : Nat}
    {Δ : CCtx Tower.Head m} {T : DeclName} :
    ∀ {shapes : List FieldShape} {ms ms' : List (CTm Tower.Head m)},
      FieldsEqual K Δ T shapes ms ms' → ∀ {p : Nat} {sh : FieldShape}, shapes[p]? = some sh →
        ∃ A, K.fieldType T sh = some A ∧
          CEqual P Δ (ms.getD p (.const .anonymous)) (ms'.getD p (.const .anonymous)) A
  | _, _, _, .nil, _, _, h => nomatch h
  | _, _, _, .cons hA e _, 0, _, h => by
      cases h
      exact ⟨_, hA, e⟩
  | _, _, _, .cons _ _ rest, p + 1, _, h => FieldsEqual.get rest h

/-- The type of a field, as the relation reads it. -/
abbrev fieldTypeC (d : Datatype Tower.Head) (fs : List CtorField) (p : Nat) {m : Nat} :
    CTm Tower.Head m :=
  (liftTm ((fs.getD p .recursive).type d.type)).liftClosed

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- The datatype is related to itself as far as its type tokens observe. -/
theorem RT.dataType_self {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ)
    {r : Tok} (hr : ((dataExtension hd).reading.const d.type).Mem r) (hrU : TyTok Elem.univ r) :
    RT (dataHead hd) Δ false r (.const d.type) (.const d.type) (.const d.type) :=
  adequateType_dataType hd (Γ := .nil) Env.nil trivial formed SubstRel.nil r hr hrU

/-- **The type of a field is related to itself** as far as its type tokens observe. -/
theorem RT.fieldType_self {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) {p : Nat} (hp : p < fs.length) {m : Nat}
    {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ) {r : Tok}
    (hr : (cinterp (dataExtension hd).reading (liftTm ((fs.getD p .recursive).type d.type))
      Env.nil).Mem r) (hrU : TyTok Elem.univ r) :
    RT (dataHead hd) Δ false r (fieldTypeC d fs p) (fieldTypeC d fs p) (fieldTypeC d fs p) := by
  have hmem : fs.getD p .recursive ∈ fs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    exact List.getElem_mem hp
  unfold fieldTypeC
  generalize fs.getD p .recursive = f at hr hmem
  cases f with
  | recursive => exact RT.dataType_self hd formed hr hrU
  | closed F =>
      exact RT.objectType_self hd (hd.fields _ (List.mem_of_getElem? entry) F hmem)
        hd.typeUniverse formed hr

/-- The type of a field is a type. -/
theorem typeGenerated_fieldType {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) {p : Nat} (hp : p < fs.length) :
    Ideal.TypeGenerated (cinterp (dataExtension hd).reading
      (liftTm ((fs.getD p .recursive).type d.type)) Env.nil) := by
  have hmem : fs.getD p .recursive ∈ fs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    exact List.getElem_mem hp
  generalize fs.getD p .recursive = f at hmem
  cases f with
  | recursive =>
      show Ideal.TypeGenerated ((dataReading d).const d.type)
      rw [dataReading_type hd]
      exact typeGenerated_dataTypeI hd
  | closed F =>
      exact (dataExtension hd).soundnessFacts.typeGenerated_of_head hd.typeUniverse
        ((hd.fields _ (List.mem_of_getElem? entry) F hmem).mono (dataExtension hd).sub)
        (ρ := Env.nil) trivial

/-- An environment of the motive and the methods, extended by an element of the datatype, fits
the context of the recursor's spine. -/
theorem fits_dataCons {ρ : Env (d.ctors.length + 1)}
    (fits : Fits (dataExtension hd).reading (recMethodsCtx d) ρ) {ν : Ideal}
    (hν : projT (dataTypeI d) ν = ν) :
    Fits (dataExtension hd).reading (recSpineCtx d) (Env.cons ν ρ) := by
  rw [recSpineCtx_eq]
  refine ⟨fits, ?_, ?_⟩
  · show Ideal.TypeGenerated ((dataReading d).const d.type)
    rw [dataReading_type hd]
    exact typeGenerated_dataTypeI hd
  · show projT ((dataReading d).const d.type) ν = ν
    rw [dataReading_type hd]
    exact hν

/-- **Related substitutions of the motive and the methods, extended by terms of the datatype**
related as far as an element observes. -/
theorem SubstRel.dataCons {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ)
    {ρ : Env (d.ctors.length + 1)} {τ τ' : CSub Tower.Head (d.ctors.length + 1) m}
    (hτ : SubstRel (dataExtension hd).reading (dataHead hd) (recMethodsCtx d) ρ Δ τ τ') {ν : Ideal}
    {L L' : CTm Tower.Head m} (hLL : CEqual (dataChurch d) Δ L L' (.const d.type))
    (hν : ∀ x, ν.Mem x → RT (dataHead hd) Δ true x (.const d.type) L L') :
    SubstRel (dataExtension hd).reading (dataHead hd) (recSpineCtx d) (Env.cons ν ρ) Δ
      (CTm.consSub L τ) (CTm.consSub L' τ') := by
  rw [recSpineCtx_eq]
  exact SubstRel.cons (dataExtension hd).levels formed hτ hLL
    ⟨_, (dataExtension hd).sub.isUniverse hd.typeUniverse, .refl (dataType_typed hd)⟩
    (fun r hr hrU => RT.dataType_self hd formed hr hrU) (fun s hs _ => hν s hs)

end CaseRelation

section CaseValues

variable (d : Datatype Tower.Head) (fs : List CtorField)

/-- **The values of the case**: the motive and the methods, the fields, and the recursive values
`rec x` at the recursive fields, read at the motive at the field. -/
def caseVals (ρ : Env (d.ctors.length + 1)) (xs : List Ideal) (rec : Ideal → Ideal) :
    List Ideal :=
  envArgs ρ ++ (xs ++ (Ideal.recFields (fs.map fieldFlag) xs).map
    fun x => projT (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) x) (rec x))

/-- **The terms of the case**: the motive and the methods, the fields, and the recursor at each
recursive field. -/
def caseTms {m : Nat} (τ : CSub Tower.Head (d.ctors.length + 1) m) (ms : List (CTm Tower.Head m)) :
    List (CTm Tower.Head m) :=
  subArgs τ ++ (ms ++ (Ideal.recFields (fs.map fieldFlag) ms).map
    fun t => CTm.appSpine (.const d.recursor) (subArgs τ ++ [t]))

theorem length_caseVals (ρ : Env (d.ctors.length + 1)) {xs : List Ideal}
    (hxs : xs.length = fs.length) (rec : Ideal → Ideal) :
    (caseVals d fs ρ xs rec).length = caseArity d fs := by
  rw [caseVals, List.length_append, List.length_append, List.length_map,
    length_recFields (by rw [hxs, List.length_map]), length_envArgs, hxs]
  have := caseArity_eq d fs
  have : recCount fs = (flagPositions (fs.map fieldFlag)).length := rfl
  omega

theorem length_caseTms {m : Nat} (τ : CSub Tower.Head (d.ctors.length + 1) m)
    {ms : List (CTm Tower.Head m)} (hms : ms.length = fs.length) :
    (caseTms d fs τ ms).length = caseArity d fs := by
  rw [caseTms, List.length_append, List.length_append, List.length_map,
    length_recFields (by rw [hms, List.length_map]), length_subArgs, hms]
  have := caseArity_eq d fs
  have : recCount fs = (flagPositions (fs.map fieldFlag)).length := rfl
  omega

theorem caseVals_take {ρ : Env (d.ctors.length + 1)} {xs : List Ideal} {rec : Ideal → Ideal}
    {q : Nat} (hq : q ≤ d.ctors.length + 1) :
    (caseVals d fs ρ xs rec).take q = (envArgs ρ).take q :=
  List.take_append_of_le_length (by rw [length_envArgs]; exact hq)

theorem caseTms_take {m : Nat} {τ : CSub Tower.Head (d.ctors.length + 1) m}
    {ms : List (CTm Tower.Head m)} {q : Nat} (hq : q ≤ d.ctors.length + 1) :
    (caseTms d fs τ ms).take q = (subArgs τ).take q :=
  List.take_append_of_le_length (by rw [length_subArgs]; exact hq)

theorem caseVals_getD_method {ρ : Env (d.ctors.length + 1)} {xs : List Ideal}
    {rec : Ideal → Ideal} {q : Nat} (hq : q < d.ctors.length + 1) :
    (caseVals d fs ρ xs rec).getD q Ideal.bot = (envArgs ρ).getD q Ideal.bot :=
  getD_append_lt (by rw [length_envArgs]; exact hq) _ _

theorem caseTms_getD_method {m : Nat} {τ : CSub Tower.Head (d.ctors.length + 1) m}
    {ms : List (CTm Tower.Head m)} {q : Nat} (hq : q < d.ctors.length + 1) :
    (caseTms d fs τ ms).getD q (.const .anonymous) = (subArgs τ).getD q (.const .anonymous) :=
  getD_append_lt (by rw [length_subArgs]; exact hq) _ _

theorem caseVals_getD_field {ρ : Env (d.ctors.length + 1)} {xs : List Ideal}
    (hxs : xs.length = fs.length) {rec : Ideal → Ideal} {p : Nat} (hp : p < fs.length) :
    (caseVals d fs ρ xs rec).getD (1 + d.ctors.length + p) Ideal.bot = xs.getD p Ideal.bot := by
  have hlen := length_envArgs ρ
  rw [caseVals, getD_append_ge (by omega),
    show 1 + d.ctors.length + p - (envArgs ρ).length = p by omega, getD_append_lt (by omega)]

theorem caseTms_getD_field {m : Nat} {τ : CSub Tower.Head (d.ctors.length + 1) m}
    {ms : List (CTm Tower.Head m)} (hms : ms.length = fs.length) {p : Nat} (hp : p < fs.length) :
    (caseTms d fs τ ms).getD (1 + d.ctors.length + p) (.const .anonymous) =
      ms.getD p (.const .anonymous) := by
  have hlen := length_subArgs τ
  rw [caseTms, getD_append_ge (by omega),
    show 1 + d.ctors.length + p - (subArgs τ).length = p by omega, getD_append_lt (by omega)]

theorem caseVals_getD_hyp {ρ : Env (d.ctors.length + 1)} {xs : List Ideal}
    (hxs : xs.length = fs.length) {rec : Ideal → Ideal} {r : Nat} (hr : r < recCount fs) :
    (caseVals d fs ρ xs rec).getD (1 + d.ctors.length + fs.length + r) Ideal.bot =
      projT (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) (xs.getD (hypField fs r) Ideal.bot))
        (rec (xs.getD (hypField fs r) Ideal.bot)) := by
  have hlen := length_envArgs ρ
  have hrl : r < (Ideal.recFields (fs.map fieldFlag) xs).length := by
    rw [length_recFields (by rw [hxs, List.length_map])]; exact hr
  rw [caseVals, getD_append_ge (by omega), getD_append_ge (by omega),
    show 1 + d.ctors.length + fs.length + r - (envArgs ρ).length - xs.length = r by omega,
    getD_map_lt _ hrl Ideal.bot,
    recFields_eq_map Ideal.bot _ _ (by rw [hxs, List.length_map]),
    getD_map_lt _ (show r < (flagPositions (fs.map fieldFlag)).length from hr) 0]

theorem caseTms_getD_hyp {m : Nat} {τ : CSub Tower.Head (d.ctors.length + 1) m}
    {ms : List (CTm Tower.Head m)} (hms : ms.length = fs.length) {r : Nat} (hr : r < recCount fs) :
    (caseTms d fs τ ms).getD (1 + d.ctors.length + fs.length + r) (.const .anonymous) =
      CTm.appSpine (.const d.recursor)
        (subArgs τ ++ [ms.getD (hypField fs r) (.const .anonymous)]) := by
  have hlen := length_subArgs τ
  have hrl : r < (Ideal.recFields (fs.map fieldFlag) ms).length := by
    rw [length_recFields (by rw [hms, List.length_map])]; exact hr
  have hrp : r < (flagPositions (fs.map fieldFlag)).length := hr
  rw [caseTms, getD_append_ge (by omega), getD_append_ge (by omega),
    show 1 + d.ctors.length + fs.length + r - (subArgs τ).length - ms.length = r by omega,
    getD_map_lt _ hrl (.const .anonymous),
    recFields_eq_map (.const .anonymous) _ _ (by rw [hms, List.length_map]),
    getD_map_lt _ hrp 0]

/-- The hypothesis of the recursive field `hypField fs r`, at the terms of the case. -/
theorem caseEntry_hyp_tms {m : Nat} (τ : CSub Tower.Head (d.ctors.length + 1) m)
    {ms : List (CTm Tower.Head m)} (hms : ms.length = fs.length) {r : Nat} (hr : r < recCount fs) :
    (liftTm (caseEntry d fs (1 + d.ctors.length + fs.length + r))).subst
        (listCSub (1 + d.ctors.length + fs.length + r)
          ((caseTms d fs τ ms).take (1 + d.ctors.length + fs.length + r))) =
      .app (τ (Fin.last d.ctors.length)) (ms.getD (hypField fs r) (.const .anonymous)) := by
  have hp : hypField fs r < fs.length := flagPositions_lt (flagPositions_getD_mem hr)
  have hidx : 1 + d.ctors.length + fs.length + r - (1 + d.ctors.length + fs.length) = r := by
    omega
  rw [caseEntry_hyp_subst d fs (by omega) (by rw [hidx]; exact hp), hidx,
    getD_take_of_lt (by omega), getD_take_of_lt (by omega),
    caseTms_getD_method d fs (Nat.succ_pos _), subArgs_getD_zero, caseTms_getD_field d fs hms hp]

/-- The hypothesis of the recursive field `hypField fs r`, at the values of the case. -/
theorem caseEntry_hyp_vals (Rd : Reading Tower.Head) (ρ : Env (d.ctors.length + 1))
    {xs : List Ideal} (hxs : xs.length = fs.length) (rec : Ideal → Ideal) {r : Nat}
    (hr : r < recCount fs) :
    cinterp Rd (liftTm (caseEntry d fs (1 + d.ctors.length + fs.length + r)))
        (Env.ofArgs (1 + d.ctors.length + fs.length + r)
          ((caseVals d fs ρ xs rec).take (1 + d.ctors.length + fs.length + r))) =
      Ideal.app ((envArgs ρ).getD 0 Ideal.bot) (xs.getD (hypField fs r) Ideal.bot) := by
  have hp : hypField fs r < fs.length := flagPositions_lt (flagPositions_getD_mem hr)
  have hidx : 1 + d.ctors.length + fs.length + r - (1 + d.ctors.length + fs.length) = r := by
    omega
  rw [caseEntry_hyp_cinterp d fs Rd (by omega) (by rw [hidx]; exact hp), hidx,
    getD_take_of_lt (by omega), getD_take_of_lt (by omega),
    caseVals_getD_method d fs (Nat.succ_pos _), caseVals_getD_field d fs hxs hp]

end CaseValues

/-! ## The adequacy of the case -/

section CaseAdequacy

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- **The substitutions of the case are related entry by entry**: the motive and the methods by
the related substitutions of the recursor's parameters, the fields by the fields of related
constructor forms, and the recursor at each recursive field by the recursion's hypothesis. -/
theorem caseEntryRel {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ)
    {ρ : Env (d.ctors.length + 1)} (fits : Fits (dataExtension hd).reading (recMethodsCtx d) ρ)
    {τ τ' : CSub Tower.Head (d.ctors.length + 1) m}
    (hτ : SubstRel (dataExtension hd).reading (dataHead hd) (recMethodsCtx d) ρ Δ τ τ')
    {i : Nat} {k : DeclName} {fs : List CtorField} (entry : d.ctors[i]? = some (k, fs))
    {ms ms' : List (CTm Tower.Head m)} {xs : List Ideal}
    (hms : ms.length = fs.length) (hms' : ms'.length = fs.length) (hxs : xs.length = fs.length)
    (eq : ∀ p, p < fs.length → CEqual (dataChurch d) Δ (ms.getD p (.const .anonymous))
      (ms'.getD p (.const .anonymous)) (fieldTypeC d fs p))
    (rel : ∀ p, p < fs.length → ∀ s, (xs.getD p Ideal.bot).Mem s →
      RT (dataHead hd) Δ true s (fieldTypeC d fs p) (ms.getD p (.const .anonymous))
        (ms'.getD p (.const .anonymous)))
    (elem : ∀ p, p < fs.length →
      projT (fieldTypeI d (fs.getD p .recursive)) (xs.getD p Ideal.bot) = xs.getD p Ideal.bot)
    {rec : Ideal → Ideal}
    (ih : ∀ p, fs[p]? = some .recursive → ∀ y, (rec (xs.getD p Ideal.bot)).Mem y →
      TypedAt (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) (xs.getD p Ideal.bot)) y →
      RT (dataHead hd) Δ true y
        ((recMotiveTm d).subst (CTm.consSub (ms.getD p (.const .anonymous)) τ))
        ((recSpineTm d).subst (CTm.consSub (ms.getD p (.const .anonymous)) τ))
        ((recSpineTm d).subst (CTm.consSub (ms'.getD p (.const .anonymous)) τ')))
    {q : Nat} (hq : q < caseArity d fs) :
    EntryRel (dataExtension hd).reading (dataHead hd) Δ (liftTm (caseEntry d fs q))
      (Env.ofArgs q ((caseVals d fs ρ xs rec).take q))
      (listCSub q ((caseTms d fs τ ms).take q)) (listCSub q ((caseTms d fs τ' ms').take q))
      ((caseVals d fs ρ xs rec).getD q Ideal.bot)
      ((caseTms d fs τ ms).getD q (.const .anonymous))
      ((caseTms d fs τ' ms').getD q (.const .anonymous)) := by
  rcases Nat.lt_or_ge q (d.ctors.length + 1) with h₁ | h₁
  · -- the motive and the methods
    have hτ₀ : SubstRel (dataExtension hd).reading (dataHead hd)
        (liftCtx (ofEntries (recEntry d.type d.motiveUniverse d.ctors) (d.ctors.length + 1)))
        (Env.ofArgs (d.ctors.length + 1) (envArgs ρ)) Δ
        (listCSub (d.ctors.length + 1) (subArgs τ))
        (listCSub (d.ctors.length + 1) (subArgs τ')) := by
      rw [ofArgs_envArgs, listCSub_subArgs, listCSub_subArgs]
      exact hτ
    rw [caseEntry_method d fs (by omega), caseVals_take d fs (q := q) (by omega),
      caseTms_take d fs (τ := τ) (q := q) (by omega),
      caseTms_take d fs (τ := τ') (q := q) (by omega),
      caseVals_getD_method d fs h₁, caseTms_getD_method d fs (τ := τ) h₁,
      caseTms_getD_method d fs (τ := τ') h₁]
    exact SubstRel.entry _ _ _ hτ₀ h₁
  rcases Nat.lt_or_ge q (1 + d.ctors.length + fs.length) with h₂ | h₂
  · -- a field
    obtain ⟨p, rfl⟩ : ∃ p, q = 1 + d.ctors.length + p := ⟨q - (1 + d.ctors.length), by omega⟩
    have hp : p < fs.length := by omega
    rw [caseEntry_field d fs hp, caseVals_getD_field d fs hxs hp, caseTms_getD_field d fs hms hp,
      caseTms_getD_field d fs hms' hp, liftTm_liftClosed]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [CTm.subst_liftClosed]
      exact (CEqual.typed (dataExtension hd).levels (eq p hp) formed).1
    · rw [CTm.subst_liftClosed]
      exact eq p hp
    · rw [CTm.subst_liftClosed, CTm.subst_liftClosed]
      exact CIsType.refl (caseFieldType_formed hd entry hp)
    · intro r hr hrU
      rw [cinterp_liftClosed] at hr
      rw [CTm.subst_liftClosed, CTm.subst_liftClosed]
      exact RT.fieldType_self hd entry hp formed hr hrU
    · intro s hs _
      rw [CTm.subst_liftClosed]
      exact rel p hp s hs
  · -- a hypothesis
    obtain ⟨r, rfl⟩ : ∃ r, q = 1 + d.ctors.length + fs.length + r :=
      ⟨q - (1 + d.ctors.length + fs.length), by omega⟩
    have hr : r < recCount fs := by
      have := caseArity_eq d fs
      omega
    have hpos := flagPositions_getD_mem hr
    have hp : hypField fs r < fs.length := flagPositions_lt hpos
    have hrec : fs[hypField fs r]? = some .recursive := flagPositions_recursive hpos
    have hfp : fs.getD (hypField fs r) .recursive = .recursive := by
      rw [List.getD_eq_getElem?_getD, hrec]
      rfl
    have eqT : CEqual (dataChurch d) Δ (ms.getD (hypField fs r) (.const .anonymous))
        (ms'.getD (hypField fs r) (.const .anonymous)) (.const d.type) := by
      have h := eq _ hp
      unfold fieldTypeC at h
      rw [hfp] at h
      exact h
    have relT : ∀ x, (xs.getD (hypField fs r) Ideal.bot).Mem x →
        RT (dataHead hd) Δ true x (.const d.type) (ms.getD (hypField fs r) (.const .anonymous))
          (ms'.getD (hypField fs r) (.const .anonymous)) := by
      have h := rel _ hp
      unfold fieldTypeC at h
      rw [hfp] at h
      exact h
    have elemT : projT (dataTypeI d) (xs.getD (hypField fs r) Ideal.bot) =
        xs.getD (hypField fs r) Ideal.bot := by
      have h := elem _ hp
      rw [hfp] at h
      exact h
    have hsub := SubstRel.dataCons hd formed hτ eqT relT
    have fits' := fits_dataCons hd fits elemT
    have tspine := (recSpineTm_typed hd).substitute hsub.1.1
    have espine := CDerivable.functional (recSpineTm_typed hd) hsub.1
    have emotive := CDerivable.functional (recMotiveTm_typed d (Q := dataChurch d)) hsub.1
    rw [recSpineTm_subst, recMotiveTm_subst] at tspine
    rw [recSpineTm_subst, recSpineTm_subst, recMotiveTm_subst] at espine
    rw [recMotiveTm_subst, recMotiveTm_subst] at emotive
    unfold EntryRel
    rw [caseEntry_hyp_tms d fs τ hms hr, caseEntry_hyp_tms d fs τ' hms' hr,
      caseEntry_hyp_vals d fs _ ρ hxs rec hr, caseVals_getD_hyp d fs hxs hr,
      caseTms_getD_hyp d fs hms hr, caseTms_getD_hyp d fs hms' hr]
    refine ⟨tspine, espine, ⟨_, motiveUniverse_data hd, emotive⟩, ?_, ?_⟩
    · intro r' hr' hrU
      rw [envArgs_getD_zero] at hr'
      exact adequateType_recMotive hd (Env.cons _ ρ) fits' formed hsub r' hr' hrU
    · intro s hs _
      obtain ⟨v, hv, hvT, e⟩ := Ideal.projT_eq_iSup.1 hs
      refine RT.closed' e fun g hg => ?_
      have h := ih _ hrec g (hv g hg) (hvT g hg)
      rw [recSpineTm_subst, recSpineTm_subst, recMotiveTm_subst] at h
      exact h

/-- **The values of the case fit its context.** -/
theorem caseFits {ρ : Env (d.ctors.length + 1)}
    (fits : Fits (dataExtension hd).reading (recMethodsCtx d) ρ)
    {i : Nat} {k : DeclName} {fs : List CtorField} (entry : d.ctors[i]? = some (k, fs))
    {xs : List Ideal} (hxs : xs.length = fs.length)
    (elem : ∀ p, p < fs.length →
      projT (fieldTypeI d (fs.getD p .recursive)) (xs.getD p Ideal.bot) = xs.getD p Ideal.bot)
    (rec : Ideal → Ideal) :
    Fits (dataExtension hd).reading (caseCtx d fs)
      (Env.ofArgs (caseArity d fs) (caseVals d fs ρ xs rec)) := by
  refine Fits.of_entries _ _ fun q hq => ?_
  rcases Nat.lt_or_ge q (d.ctors.length + 1) with h₁ | h₁
  · have fits₀ : Fits (dataExtension hd).reading
        (liftCtx (ofEntries (recEntry d.type d.motiveUniverse d.ctors) (d.ctors.length + 1)))
        (Env.ofArgs (d.ctors.length + 1) (envArgs ρ)) := by
      rw [ofArgs_envArgs]
      exact fits
    rw [caseEntry_method d fs (by omega), caseVals_take d fs (q := q) (by omega),
      caseVals_getD_method d fs h₁]
    exact Fits.entry _ _ fits₀ h₁
  rcases Nat.lt_or_ge q (1 + d.ctors.length + fs.length) with h₂ | h₂
  · obtain ⟨p, rfl⟩ : ∃ p, q = 1 + d.ctors.length + p := ⟨q - (1 + d.ctors.length), by omega⟩
    have hp : p < fs.length := by omega
    have hmem : fs.getD p .recursive ∈ (k, fs).2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
      exact List.getElem_mem hp
    rw [caseEntry_field d fs hp, caseVals_getD_field d fs hxs hp, liftTm_liftClosed,
      cinterp_liftClosed]
    refine ⟨typeGenerated_fieldType hd entry hp, ?_⟩
    have e : cinterp (dataExtension hd).reading (liftTm ((fs.getD p .recursive).type d.type))
        Env.nil = fieldTypeI d (fs.getD p .recursive) :=
      dataReading_fieldType hd (List.mem_of_getElem? entry) hmem
    rw [e]
    exact elem p hp
  · obtain ⟨r, rfl⟩ : ∃ r, q = 1 + d.ctors.length + fs.length + r :=
      ⟨q - (1 + d.ctors.length + fs.length), by omega⟩
    have hr : r < recCount fs := by
      have := caseArity_eq d fs
      omega
    have hpos := flagPositions_getD_mem hr
    have hp : hypField fs r < fs.length := flagPositions_lt hpos
    have hfp : fs.getD (hypField fs r) .recursive = .recursive := by
      rw [List.getD_eq_getElem?_getD, flagPositions_recursive hpos]
      rfl
    have elemT : projT (dataTypeI d) (xs.getD (hypField fs r) Ideal.bot) =
        xs.getD (hypField fs r) Ideal.bot := by
      have h := elem _ hp
      rw [hfp] at h
      exact h
    rw [caseEntry_hyp_vals d fs _ ρ hxs rec hr, caseVals_getD_hyp d fs hxs hr]
    refine ⟨?_, Ideal.projT_projT _ _⟩
    have h := (dataExtension hd).soundnessFacts.typeGenerated_of_head (motiveUniverse_data hd)
      (recMotiveTm_typed d) (fits_dataCons hd fits elemT)
    rw [envArgs_getD_zero]
    exact h

omit hd in
theorem drop_append_append {α : Type} {A B C : List α} {n : Nat} (h : n = A.length + B.length) :
    (A ++ (B ++ C)).drop n = C := by
  rw [← List.append_assoc]
  exact List.drop_left' (by rw [List.length_append]; exact h.symm)

omit hd in
theorem drop_take_append_append {α : Type} {A B C : List α} {n b : Nat} (h : n = A.length)
    (hb : B.length = b) : ((A ++ (B ++ C)).drop n).take b = B := by
  rw [List.drop_left' h.symm, List.take_left' hb]

/-- **The method of a constructor, applied to related fields and to the recursor at the recursive
fields, is related at the motive at the constructor applied to the fields**, as far as every
token of the method's value at the fields and at the recursive values observes: the method's
application is typed with no constant over the context of the case, so it is adequate there, and
the substitutions of the case are related entry by entry (`caseEntryRel`). -/
theorem dataCase_rel {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ)
    {ρ : Env (d.ctors.length + 1)} (fits : Fits (dataExtension hd).reading (recMethodsCtx d) ρ)
    {τ τ' : CSub Tower.Head (d.ctors.length + 1) m}
    (hτ : SubstRel (dataExtension hd).reading (dataHead hd) (recMethodsCtx d) ρ Δ τ τ')
    {i : Nat} {k : DeclName} {fs : List CtorField} (entry : d.ctors[i]? = some (k, fs))
    {ms ms' : List (CTm Tower.Head m)} {xs : List Ideal}
    (hms : ms.length = fs.length) (hms' : ms'.length = fs.length) (hxs : xs.length = fs.length)
    (eq : ∀ p, p < fs.length → CEqual (dataChurch d) Δ (ms.getD p (.const .anonymous))
      (ms'.getD p (.const .anonymous)) (fieldTypeC d fs p))
    (rel : ∀ p, p < fs.length → ∀ s, (xs.getD p Ideal.bot).Mem s →
      RT (dataHead hd) Δ true s (fieldTypeC d fs p) (ms.getD p (.const .anonymous))
        (ms'.getD p (.const .anonymous)))
    (elem : ∀ p, p < fs.length →
      projT (fieldTypeI d (fs.getD p .recursive)) (xs.getD p Ideal.bot) = xs.getD p Ideal.bot)
    {rec : Ideal → Ideal}
    (ih : ∀ p, fs[p]? = some .recursive → ∀ y, (rec (xs.getD p Ideal.bot)).Mem y →
      TypedAt (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) (xs.getD p Ideal.bot)) y →
      RT (dataHead hd) Δ true y
        ((recMotiveTm d).subst (CTm.consSub (ms.getD p (.const .anonymous)) τ))
        ((recSpineTm d).subst (CTm.consSub (ms.getD p (.const .anonymous)) τ))
        ((recSpineTm d).subst (CTm.consSub (ms'.getD p (.const .anonymous)) τ')))
    {y : Tok}
    (hy : (Ideal.appSpine ((envArgs ρ).getD (i + 1) Ideal.bot)
      (xs ++ (Ideal.recFields (fs.map fieldFlag) xs).map
        fun x => projT (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) x) (rec x))).Mem y)
    (hyT : TypedAt (Ideal.app ((envArgs ρ).getD 0 Ideal.bot)
      (Ideal.appSpine ((dataExtension hd).reading.const k) xs)) y) :
    RT (dataHead hd) Δ true y (.app (τ (Fin.last d.ctors.length)) (CTm.appSpine (.const k) ms))
      (CTm.appSpine ((subArgs τ).getD (1 + i) (.const .anonymous))
        (ms ++ (Ideal.recFields (fs.map fieldFlag) ms).map
          fun t => CTm.appSpine (.const d.recursor) (subArgs τ ++ [t])))
      (CTm.appSpine ((subArgs τ').getD (1 + i) (.const .anonymous))
        (ms' ++ (Ideal.recFields (fs.map fieldFlag) ms').map
          fun t => CTm.appSpine (.const d.recursor) (subArgs τ' ++ [t]))) := by
  have hi : i < d.ctors.length := (List.getElem?_eq_some_iff.1 entry).1
  have hvs := length_caseVals d fs ρ hxs rec
  have hts := length_caseTms d fs τ hms
  have hts' := length_caseTms d fs τ' hms'
  have hlenρ := length_envArgs ρ
  have hlenτ := length_subArgs τ
  have hlenτ' := length_subArgs τ'
  have hσ : SubstRel (dataExtension hd).reading (dataHead hd) (caseCtx d fs)
      (Env.ofArgs (caseArity d fs) (caseVals d fs ρ xs rec)) Δ
      (listCSub (caseArity d fs) (caseTms d fs τ ms))
      (listCSub (caseArity d fs) (caseTms d fs τ' ms')) :=
    SubstRel.of_entries _ _ _ fun q hq =>
      caseEntryRel hd formed fits hτ entry hms hms' hxs eq rel elem ih hq
  have adequate := ((dataExtension hd).valid_within (allowed := fun _ => false)
    (fun h => absurd h Bool.false_ne_true) (caseBody_typed d fs entry)
    (caseCtx_formed hd entry)).1
  have hmem : (cinterp (dataExtension hd).reading (liftTm (caseBody d fs i))
      (Env.ofArgs (caseArity d fs) (caseVals d fs ρ xs rec))).Mem y := by
    rw [caseBody_cinterp d fs _ hi hvs, caseVals_getD_method d fs (by omega), caseVals,
      drop_take_append_append (by omega) hxs,
      drop_append_append (by rw [hxs]; omega)]
    exact hy
  have htyped : TypedAt (cinterp (dataExtension hd).reading (liftTm (caseTarget d fs k))
      (Env.ofArgs (caseArity d fs) (caseVals d fs ρ xs rec))) y := by
    rw [caseTarget_cinterp d fs _ hvs, caseVals_getD_method d fs (Nat.succ_pos _), caseVals,
      drop_take_append_append (by omega) hxs]
    exact hyT
  have h := adequate _ (caseFits hd fits entry hxs elem rec) formed hσ y hmem htyped
  rw [caseTarget_subst d fs hts, caseBody_subst d fs hi hts, caseBody_subst d fs hi hts',
    caseTms_getD_method d fs (τ := τ) (q := i + 1) (by omega),
    caseTms_getD_method d fs (τ := τ') (q := i + 1) (by omega),
    caseTms_getD_method d fs (τ := τ) (q := 0) (Nat.succ_pos _), subArgs_getD_zero] at h
  simp only [caseTms] at h
  rw [drop_take_append_append (by omega) hms, drop_take_append_append (by omega) hms',
    drop_append_append (by rw [hms]; omega), drop_append_append (by rw [hms']; omega),
    Nat.add_comm i 1] at h
  exact h

end CaseAdequacy

/-! ## The recursor's spine at a constructor form -/

section Reduction

variable {d : Datatype Tower.Head}

/-- The type of both sides of the computation rule at the motive and methods `τ` and the fields
`ms`: the motive at the constructor applied to the fields. -/
theorem iotaTarget_listCSub {k : DeclName} {a m : Nat} (τ : CSub Tower.Head (d.ctors.length + 1) m)
    {ms : List (CTm Tower.Head m)} (hms : ms.length = a) :
    (liftTm (iotaTarget k d.ctors.length a)).subst
        (listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms)) =
      .app (τ (Fin.last d.ctors.length)) (CTm.appSpine (.const k) ms) := by
  have hlen : (subArgs τ ++ ms).length = 1 + d.ctors.length + a := by
    rw [List.length_append, length_subArgs, hms]; omega
  have e : (liftTm (iotaTarget k d.ctors.length a)).subst
      (listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms)) =
      .app (listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms) ⟨d.ctors.length + a, by omega⟩)
        ((liftTm (appSpine (.const k) ((metaVars (1 + d.ctors.length + a)).drop
          (1 + d.ctors.length)))).subst (listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms))) :=
    rfl
  rw [e, liftTm_appSpine, csubst_appSpine, List.map_map]
  have e' : List.map ((CTm.subst (listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms))) ∘ liftTm)
      ((metaVars (1 + d.ctors.length + a)).drop (1 + d.ctors.length)) = ms := by
    rw [List.map_drop]
    show ((metaVars (1 + d.ctors.length + a)).map
      fun t => (liftTm t).subst (listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms))).drop _ = ms
    rw [map_metaVars_listCSub hlen, List.drop_left' (by rw [length_subArgs]; omega)]
  rw [e']
  have e'' : listCSub (1 + d.ctors.length + a) (subArgs τ ++ ms) ⟨d.ctors.length + a, by omega⟩ =
      τ (Fin.last d.ctors.length) := by
    show (subArgs τ ++ ms).getD (1 + d.ctors.length + a - 1 - (d.ctors.length + a)) _ = _
    rw [show 1 + d.ctors.length + a - 1 - (d.ctors.length + a) = 0 by omega,
      getD_append_lt (by rw [length_subArgs]; omega), subArgs_getD_zero]
  rw [e'']
  rfl

/-- **A substitution of the motive, the methods and the fields is typed along the telescope of
the computation rule** when the motive and the methods are typed along the recursor's
telescope and the fields at their types. -/
theorem iota_mor {m : Nat} {Δ : CCtx Tower.Head m} {τ : CSub Tower.Head (d.ctors.length + 1) m}
    (mor : CSubstMor (dataChurch d) (recMethodsCtx d) Δ τ) {fs : List CtorField}
    {ms : List (CTm Tower.Head m)}
    (tms : ∀ p, p < fs.length →
      CTyped (dataChurch d) Δ (ms.getD p (.const .anonymous)) (fieldTypeC d fs p)) :
    CSubstMor (dataChurch d) (liftCtx (iotaTele d.type d.motiveUniverse d.ctors fs)) Δ
      (listCSub (1 + d.ctors.length + fs.length) (subArgs τ ++ ms)) := by
  have hlen := length_subArgs τ
  have mor₀ : CSubstMor (dataChurch d)
      (liftCtx (ofEntries (recEntry d.type d.motiveUniverse d.ctors) (d.ctors.length + 1))) Δ
      (listCSub (d.ctors.length + 1) (subArgs τ)) := by
    rw [listCSub_subArgs]
    exact mor
  refine CSubstMor.of_entries (iotaEntry d.type d.motiveUniverse d.ctors fs) fun q hq => ?_
  rcases Nat.lt_or_ge q (d.ctors.length + 1) with h₁ | h₁
  · rw [iotaEntry_of_le (by omega), List.take_append_of_le_length (by omega),
      getD_append_lt (by omega)]
    exact CSubstMor.entry _ mor₀ h₁
  · obtain ⟨p, rfl⟩ : ∃ p, q = d.ctors.length + 1 + p := ⟨q - (d.ctors.length + 1), by omega⟩
    have hp : p < fs.length := by omega
    rw [iotaEntry_field hp, liftTm_liftClosed, CTm.subst_liftClosed, getD_append_ge (by omega),
      show d.ctors.length + 1 + p - (subArgs τ).length = p by omega]
    exact tms p hp

variable (hd : d.Admissible objectChurch)
include hd

/-- **The recursor's spine at a term that reduces to a constructor form reduces to the
constructor's method applied to the fields and to the recursor at the recursive fields**, at
the motive at the term: the term reduces under the recursor, the computation rule applies, and
the rule is an equality (`iota_holds`). -/
theorem CRedTm.dataRec {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ)
    {τ : CSub Tower.Head (d.ctors.length + 1) m}
    (mor : CSubstMor (dataChurch d) (recMethodsCtx d) Δ τ)
    {i : Nat} {k : DeclName} {fs : List CtorField} (entry : d.ctors[i]? = some (k, fs))
    {L : CTm Tower.Head m} {ms : List (CTm Tower.Head m)} (hms : ms.length = fs.length)
    (tms : ∀ p, p < fs.length →
      CTyped (dataChurch d) Δ (ms.getD p (.const .anonymous)) (fieldTypeC d fs p))
    (hL : CRedTm (dataHead hd) Δ L (CTm.appSpine (.const k) ms) (.const d.type)) :
    CRedTm (dataHead hd) Δ ((recSpineTm d).subst (CTm.consSub L τ))
      (CTm.appSpine ((subArgs τ).getD (1 + i) (.const .anonymous))
        (ms ++ (Ideal.recFields (fs.map fieldFlag) ms).map
          fun t => CTm.appSpine (.const d.recursor) (subArgs τ ++ [t])))
      ((recMotiveTm d).subst (CTm.consSub L τ)) := by
  obtain ⟨tL, tK⟩ := CEqual.typed (dataExtension hd).levels hL.2 formed
  have hsub : CSubstEq (dataChurch d) (recSpineCtx d) Δ (CTm.consSub L τ)
      (CTm.consSub (CTm.appSpine (.const k) ms) τ) := by
    rw [recSpineCtx_eq]
    exact CSubstEq.cons ⟨mor, fun i => .refl (mor i)⟩ tL hL.2
  have e₁ := CDerivable.functional (recSpineTm_typed hd) hsub
  have e₂ := iota_holds ConvRules.objectLevels objectChurch hd.typeUniverse hd.motiveUniverse
    hd.distinct hd.lamFree hd.new hd.fieldsFormed entry _ (iota_mor mor tms)
  rw [iotaLeft_listCSub τ hms, iotaRight_listCSub τ hms, iotaTarget_listCSub τ hms] at e₂
  have eT := CDerivable.functional (recMotiveTm_typed d (Q := dataChurch d)) hsub
  rw [recMotiveTm_subst, recMotiveTm_subst] at eT
  rw [recSpineTm_subst, recSpineTm_subst, recMotiveTm_subst] at e₁
  rw [recSpineTm_subst, recMotiveTm_subst]
  exact ⟨(dataHead_rec_red hd (length_subArgs τ) hL.1).tail (dataHead_iota hd entry τ hms),
    .trans e₁ (.convEq e₂ (.symm eT) (motiveUniverse_data hd))⟩

end Reduction

/-! ## The recursor at the approximants of its recursion -/

section Claim

/-- **A token that observes something of a case analysis names a listed tag of the element**: a
generator of the token lies in one of the guarded branches. -/
theorem tag_of_joinList {ν : Ideal} {F : Kind × List Bool → Ideal} :
    ∀ {cs : List (Kind × List Bool)} {y : Tok},
      (Ideal.joinList (cs.map fun c => Ideal.whenTag c.1 ν (F c))).Mem y → ent [] y = false →
        ∃ c ∈ cs, ν.Mem (.tag c.1)
  | [], y, hy, hvac => by
      have h : ent [] y = true := hy
      rw [h] at hvac
      cases hvac
  | c :: cs, y, hy, hvac => by
      obtain ⟨v, hv, e⟩ := hy
      obtain ⟨g, hg, -, hgn⟩ := source_of_ent e hvac
      rcases hv g hg with ⟨w, hw, ew⟩ | hrest
      · cases w with
        | nil => rw [ew] at hgn; cases hgn
        | cons r _ => exact ⟨c, List.mem_cons_self, (hw r List.mem_cons_self).1⟩
      · obtain ⟨c', hc', h⟩ := tag_of_joinList hrest hgn
        exact ⟨c', List.mem_cons_of_mem _ hc', h⟩

theorem recApprox_succ (cs : List (Kind × List Bool)) (M : Ideal.Methods Kind) (n : Nat)
    (ν : Ideal) :
    Ideal.recApprox cs M (n + 1) ν = Ideal.joinList (cs.map fun c =>
      Ideal.whenTag c.1 ν (Ideal.methodAt M (Ideal.recApprox cs M n) c ν)) :=
  rfl

theorem fieldsI_getD (k : Kind) {n p : Nat} (hp : p < n) (ν : Ideal) :
    (Ideal.fieldsI k n ν).getD p Ideal.bot = Ideal.fieldI k p ν := by
  rw [Ideal.fieldsI, getD_map_lt _ (by rw [List.length_range]; exact hp) 0,
    List.getD_eq_getElem?_getD, List.getElem?_range hp, Option.getD_some]

theorem length_fieldsI (k : Kind) (n : Nat) (ν : Ideal) : (Ideal.fieldsI k n ν).length = n := by
  rw [Ideal.fieldsI, List.length_map, List.length_range]

theorem zipWith_projT_self {As xs : List Ideal} (h : As.length = xs.length)
    (hp : ∀ p, p < xs.length →
      projT (As.getD p Ideal.bot) (xs.getD p Ideal.bot) = xs.getD p Ideal.bot) :
    List.zipWith projT As xs = xs := by
  apply List.ext_getElem (by rw [List.length_zipWith, h, Nat.min_self])
  intro p h₁ h₂
  rw [List.getElem_zipWith]
  have e := hp p h₂
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at e
  exact e

variable {d : Datatype Tower.Head}

/-- The constructor at `i`, as recursion reads it. -/
theorem dataCs_getElem? {i : Nat} {k : DeclName} {fs : List CtorField}
    (h : d.ctors[i]? = some (k, fs)) :
    (dataCs d)[i]? = some
      (Kind.ctor d.type k (fieldShapes (paramTypes (d.ctors.take i)).length fs),
        fs.map fieldFlag) := by
  unfold dataCs Ideal.dataCtors
  rw [List.getElem?_map, ctorShapes_getElem? 0 h, Nat.zero_add, Option.map_some,
    fieldShapes_flags]

/-- The constructors recursion reads are the datatype's. -/
theorem mem_dataCs {c : Kind × List Bool} (h : c ∈ dataCs d) :
    ∃ i k fs, d.ctors[i]? = some (k, fs) ∧
      c = (Kind.ctor d.type k (fieldShapes (paramTypes (d.ctors.take i)).length fs),
        fs.map fieldFlag) := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem h
  have hlt : j < d.ctors.length := by
    rw [← dataCs_length d]
    exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨k, fs⟩ := d.ctors[j]
  have he : d.ctors[j]? = some (d.ctors[j].1, d.ctors[j].2) := List.getElem?_eq_getElem hlt
  rw [dataCs_getElem? he] at hj
  exact ⟨j, _, _, he, (Option.some.inj hj).symm⟩

variable (hd : d.Admissible objectChurch)
include hd

/-- **A constructor of the datatype has one list of field shapes.** -/
theorem dataCtor_unique {k : DeclName} {fs₁ fs₂ : List FieldShape}
    (h₁ : dataCtor d d.type k fs₁) (h₂ : dataCtor d d.type k fs₂) : fs₁ = fs₂ := by
  have notNum : d.type ≠ numN := fun e =>
    objectChurch_constantType_ne_none (c := numN) (by decide) (e ▸ hd.new.typeNew)
  rcases h₁ with ⟨e, -⟩ | ⟨-, i₁, f₁, e₁, rfl⟩
  · exact absurd e notNum
  rcases h₂ with ⟨e, -⟩ | ⟨-, i₂, f₂, e₂, rfl⟩
  · exact absurd e notNum
  have n₁ : (d.ctors.map Prod.fst)[i₁]? = some k := by rw [List.getElem?_map, e₁]; rfl
  have n₂ : (d.ctors.map Prod.fst)[i₂]? = some k := by rw [List.getElem?_map, e₂]; rfl
  obtain rfl := nodup_getElem?_inj hd.distinct.ctorsNodup n₁ n₂
  rw [e₁] at e₂
  cases e₂
  rfl

/-- A constructor of the datatype, related at its tag to a term that reduces to the constructor
form of `k`, is `k` with its field shapes. -/
theorem ctor_of_red {m : Nat} {Δ : CCtx Tower.Head m} {L L' T₁ T₂ : CTm Tower.Head m}
    {k k' : DeclName} {sh sh' : List FieldShape} {ms ms₁ ms₁' : List (CTm Tower.Head m)}
    (hc : (dataExtension hd).rigid.ctor d.type k sh)
    (hL : CRedTm (dataHead hd) Δ L (CTm.appSpine (.const k) ms) T₁) (hlen : ms.length = sh.length)
    (h : CtorRed (dataHead hd) Δ d.type k' sh' T₂ L L' ms₁ ms₁') : k' = k ∧ sh' = sh := by
  have e := CRedTm.nf_unique hL h.2.2.1 (fun u => (dataHead hd).ctor_normal u hc hlen)
    (fun u => (dataHead hd).ctor_normal u h.1 h.2.2.2.2.length.1)
  obtain ⟨rfl, -⟩ := CTm.appSpine_const_injective e
  exact ⟨rfl, dataCtor_unique hd h.1 hc⟩

/-- **The recursor at the approximants of its recursion.** Let the substitutions of the motive
and the methods be related over an environment fitting them. For terms of the datatype related
as far as an element observes, the recursor's spines at them are related at the motive at the
left term, as far as every token of the `n`-th approximant of the recursion at the element,
typed at the motive there, observes.

A token observing something names a tag of the element, the tag of a constructor that the left
term reduces to. The element then lies below that constructor of its fields, and the token lies in
the approximant there: the constructor's method at the fields and at the previous approximant at
the recursive fields. The spines reduce to the method applied to the fields and to the spines at
the recursive fields, related at the motive at the constructor form (`dataCase_rel`, the recursive
values related by the claim at the previous approximant); the motive's adequacy converts the
relation to the motive at the term. -/
theorem dataRec_claim {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed (dataChurch d) Δ)
    {ρ : Env (d.ctors.length + 1)} (fits : Fits (dataExtension hd).reading (recMethodsCtx d) ρ)
    {τ τ' : CSub Tower.Head (d.ctors.length + 1) m}
    (hτ : SubstRel (dataExtension hd).reading (dataHead hd) (recMethodsCtx d) ρ Δ τ τ') :
    ∀ (n : Nat) (ν : Ideal) (L L' : CTm Tower.Head m), projT (dataTypeI d) ν = ν →
      CEqual (dataChurch d) Δ L L' (.const d.type) →
      (∀ x, ν.Mem x → RT (dataHead hd) Δ true x (.const d.type) L L') →
      ∀ y, (Ideal.recApprox (dataCs d)
          (methodsAt ((envArgs ρ).getD 0 Ideal.bot) (dataCs d) (envArgs ρ).tail) n ν).Mem y →
        TypedAt (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) ν) y →
        RT (dataHead hd) Δ true y ((recMotiveTm d).subst (CTm.consSub L τ))
          ((recSpineTm d).subst (CTm.consSub L τ)) ((recSpineTm d).subst (CTm.consSub L' τ'))
  | 0, _, _, _, _, _, _, _, hy, _ => RT.of_vacuous hy
  | n + 1, ν, L, L', hνT, hLL, hν, y, hy, hyT => by
      cases hvac : ent [] y with
      | true => exact RT.of_vacuous hvac
      | false =>
      have hM := contList_methodsAt ((envArgs ρ).getD 0 Ideal.bot) (dataCs d) (envArgs ρ).tail
      have nodup := dataCs_nodup d hd.distinct.ctorsNodup
      rw [recApprox_succ] at hy
      obtain ⟨c₀, hc₀, htag⟩ := tag_of_joinList hy hvac
      rw [← recApprox_succ] at hy
      obtain ⟨i, kn, fs, entry, rfl⟩ := mem_dataCs hc₀
      -- the constructor form the term reduces to
      obtain ⟨ms, ms', hcr⟩ := RT.tm_ctorTag_iff.1 (hν _ htag)
      have hshl := fieldShapes_length (paramTypes (d.ctors.take i)).length fs
      obtain ⟨hlen, hlen'⟩ := hcr.2.2.2.2.length
      have hms : ms.length = fs.length := hlen.trans hshl
      have hms' : ms'.length = fs.length := hlen'.trans hshl
      have hL := hcr.2.2.1
      have hL' := hcr.2.2.2.1
      -- the fields of the element
      have hxs : (Ideal.fieldsI
          (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
          (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν).length = fs.length := by
        rw [length_fieldsI, hshl]
      have shapeAt : ∀ p, p < fs.length → ∃ sh,
          (fieldShapes (paramTypes (d.ctors.take i)).length fs)[p]? = some sh ∧
            sh.typeI d.type (dataParams d) = fieldTypeI d (fs.getD p .recursive) ∧
            (dataExtension hd).rigid.fieldType d.type sh =
              some (fieldTypeC d fs p : CTm Tower.Head m) := by
        intro p hp
        have hp' : p < (fieldShapes (paramTypes (d.ctors.take i)).length fs).length := by
          rw [hshl]; exact hp
        refine ⟨_, List.getElem?_eq_getElem hp', ?_, ?_⟩
        · have e := congrArg (fun l => l[p]?) (dataShapes_typeI entry)
          simp only [List.getElem?_map, List.getElem?_eq_getElem hp',
            List.getElem?_eq_getElem hp, Option.map_some, Option.some.injEq] at e
          rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
        · rw [dataFieldType hd entry (List.getElem?_eq_getElem hp) (List.getElem?_eq_getElem hp')]
          unfold fieldTypeC
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
      have elem : ∀ p, p < fs.length →
          projT (fieldTypeI d (fs.getD p .recursive))
            ((Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν).getD p Ideal.bot) =
            (Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν).getD p Ideal.bot := by
        intro p hp
        obtain ⟨sh, hsh, hT, -⟩ := shapeAt p hp
        rw [fieldsI_getD _ (by rw [hshl]; exact hp), ← hT]
        exact projT_fieldI_data hνT hsh
      have eq : ∀ p, p < fs.length → CEqual (dataChurch d) Δ (ms.getD p (.const .anonymous))
          (ms'.getD p (.const .anonymous)) (fieldTypeC d fs p) := by
        intro p hp
        obtain ⟨sh, hsh, -, hA⟩ := shapeAt p hp
        obtain ⟨A, hA', e⟩ := FieldsEqual.get hcr.2.2.2.2 hsh
        obtain rfl := Option.some.inj (hA'.symm.trans hA)
        exact e
      have rel : ∀ p, p < fs.length → ∀ s,
          ((Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
            (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν).getD p
              Ideal.bot).Mem s →
          RT (dataHead hd) Δ true s (fieldTypeC d fs p) (ms.getD p (.const .anonymous))
            (ms'.getD p (.const .anonymous)) := by
        intro p hp s hs
        rw [fieldsI_getD _ (by rw [hshl]; exact hp)] at hs
        obtain ⟨sh, hsh, -, hA⟩ := shapeAt p hp
        obtain ⟨v, hv, e⟩ := hs
        refine RT.closed' e fun t ht => ?_
        obtain ⟨C, hC⟩ := hv t ht
        rcases RT.tm_field_iff.1 (hν _ hC) with hvac' | ⟨ms₁, ms₁', hcr₁, -, hrel⟩
        · exact RT.of_vacuous (vacuous_arg hvac')
        · obtain ⟨rfl, rfl⟩ := hcr.align hcr₁
          exact hrel _ _ _ ⟨⟨sh, hsh, hA⟩,
            by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl,
            by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl⟩
      -- the recursive values, by the claim at the previous approximant
      have ih : ∀ p, fs[p]? = some .recursive → ∀ y,
          (Ideal.recApprox (dataCs d) (methodsAt ((envArgs ρ).getD 0 Ideal.bot) (dataCs d)
            (envArgs ρ).tail) n
            ((Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν).getD p
                Ideal.bot)).Mem y →
          TypedAt (Ideal.app ((envArgs ρ).getD 0 Ideal.bot)
            ((Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν).getD p Ideal.bot)) y →
          RT (dataHead hd) Δ true y
            ((recMotiveTm d).subst (CTm.consSub (ms.getD p (.const .anonymous)) τ))
            ((recSpineTm d).subst (CTm.consSub (ms.getD p (.const .anonymous)) τ))
            ((recSpineTm d).subst (CTm.consSub (ms'.getD p (.const .anonymous)) τ')) := by
        intro p hrec
        have hp : p < fs.length := (List.getElem?_eq_some_iff.1 hrec).1
        have hfp : fs.getD p .recursive = .recursive := by
          rw [List.getD_eq_getElem?_getD, hrec]
          rfl
        have e₁ := eq p hp
        have r₁ := rel p hp
        have m₁ := elem p hp
        unfold fieldTypeC at e₁ r₁
        rw [hfp] at e₁ r₁ m₁
        exact dataRec_claim formed fits hτ n _ _ _ m₁ e₁ r₁
      -- the element lies below the constructor of its fields
      have hle : ν ≤ ctorI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
          (Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
            (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν) :=
        le_ctorI_fields hνT fun g hg hgT => by
          obtain ⟨a, ha, -, hat⟩ := hgT
          rcases tyTok_data_cases ha hat with ⟨c, fs₁, rfl⟩ | ⟨c, fs₁, j, s, f, rfl, -, -⟩
          · obtain ⟨ms₁, ms₁', hcr₁⟩ := RT.tm_ctorTag_iff.1 (hν _ hg)
            obtain ⟨rfl, rfl⟩ := ctor_of_red hd hcr.1 hL hlen hcr₁
            exact .inl rfl
          · rcases RT.tm_field_iff.1 (hν _ hg) with hvac' | ⟨ms₁, ms₁', hcr₁, -, -⟩
            · exact .inr (.inr hvac')
            · obtain ⟨rfl, rfl⟩ := ctor_of_red hd hcr.1 hL hlen hcr₁
              exact .inr (.inl ⟨j, s, rfl⟩)
      -- the token at the constructor form
      have hy₁ := (Ideal.cont_recApprox hM (n + 1)).mono hle y hy
      rw [Ideal.recApprox_ctorI _ hc₀ nodup (by rw [hxs, List.length_map]),
        methodsAt_getElem _ _ nodup (dataCs_getElem? entry),
        caseValue_eval _ _ _ (by rw [hxs, List.length_map]), tail_getD] at hy₁
      have hyT₁ := Ideal.TypedAt.mono (Ideal.app_mono (Ideal.le_refl _) hle) hyT
      have hctor : Ideal.appSpine ((dataExtension hd).reading.const kn)
          (Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
            (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν) =
          ctorI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
            (Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν) := by
        show Ideal.appSpine ((dataReading d).const kn) _ = _
        rw [dataReading_ctor hd entry, appSpine_ctorConstI_proj kn _ (length_fieldsI _ _ _)]
        congr 1
        refine zipWith_projT_self (by rw [List.length_map, length_fieldsI]) fun p hp => ?_
        rw [hxs] at hp
        obtain ⟨sh, hsh, hT, -⟩ := shapeAt p hp
        rw [getD_map_lt _ (by rw [hshl]; exact hp) .self, List.getD_eq_getElem?_getD, hsh,
          Option.getD_some, hT]
        exact elem p hp
      have hcase := dataCase_rel hd formed fits hτ entry hms hms' hxs eq rel elem ih hy₁
        (by rw [hctor]; exact hyT₁)
      -- the motive at the constructor form and at the term
      obtain ⟨tL, -⟩ := CEqual.typed (dataExtension hd).levels hLL formed
      have tK := (CEqual.typed (dataExtension hd).levels hL.2 formed).2
      have redc : CtorRed (dataHead hd) Δ d.type kn
          (fieldShapes (paramTypes (d.ctors.take i)).length fs) (.const d.type)
          (CTm.appSpine (.const kn) ms) L ms ms :=
        ⟨hcr.1, dataRed hd, CRedTm.refl tK, hL, hcr.2.2.2.2.left⟩
      have hsub : SubstRel (dataExtension hd).reading (dataHead hd) (recSpineCtx d)
          (Env.cons (ctorI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
            (Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν)) ρ) Δ
          (CTm.consSub (CTm.appSpine (.const kn) ms) τ) (CTm.consSub L τ) :=
        SubstRel.dataCons hd formed hτ.left (.symm hL.2) fun x hx =>
          RT.ofCtorRed hd redc (fun p A z z' hfa r hr => by
            obtain ⟨⟨sh', hsh', hA⟩, hz, hz'⟩ := hfa
            have hp : p < fs.length := by
              rw [← hshl]
              exact (List.getElem?_eq_some_iff.1 hsh').1
            obtain ⟨sh, hsh, -, hA₀⟩ := shapeAt p hp
            rw [hsh] at hsh'
            cases hsh'
            obtain rfl := Option.some.inj (hA.symm.trans hA₀)
            have ez : z = ms.getD p (.const .anonymous) := by
              rw [List.getD_eq_getElem?_getD, hz]
              rfl
            have ez' : z' = ms.getD p (.const .anonymous) := by
              rw [List.getD_eq_getElem?_getD, hz']
              rfl
            subst ez ez'
            exact RT.left (rel p hp r hr)) hx
      have hcT : projT (dataTypeI d)
          (ctorI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
            (Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν)) =
          ctorI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
            (Ideal.fieldsI (.ctor d.type kn (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν) :=
        Ideal.projT_data_ctorI fun p x hx => by
          have hp : p < fs.length := by
            rw [← hxs]
            exact (List.getElem?_eq_some_iff.1 hx).1
          obtain ⟨sh, hsh, hT, -⟩ := shapeAt p hp
          refine ⟨sh, hsh, ?_⟩
          have ex : x = (Ideal.fieldsI (.ctor d.type kn
              (fieldShapes (paramTypes (d.ctors.take i)).length fs))
              (fieldShapes (paramTypes (d.ctors.take i)).length fs).length ν).getD p Ideal.bot := by
            rw [List.getD_eq_getElem?_getD, hx]
            rfl
          rw [ex, hT]
          exact elem p hp
      have fitsC := fits_dataCons hd fits hcT
      obtain ⟨a, ha, hau, hta⟩ := hyT₁
      have hπ : (envArgs ρ).getD 0 Ideal.bot = ρ (Fin.last d.ctors.length) := envArgs_getD_zero ρ
      have hN := (RT.conv_iff (dataExtension hd).levels formed hau hta
        (fun r hr => adequateType_recMotive hd _ fitsC formed hsub r
          (by have h := ha r hr; rw [hπ] at h; exact h) (hau r hr))
        ⟨_, motiveUniverse_data hd, CDerivable.functional (recMotiveTm_typed d) hsub.1⟩).1 hcase
      -- the spines reduce to the method's applications
      have mor' := (hτ.symm (dataExtension hd).levels formed).1.1
      have hsubL : CSubstEq (dataChurch d) (recSpineCtx d) Δ (CTm.consSub L τ)
          (CTm.consSub L' τ') := by
        rw [recSpineCtx_eq]
        exact CSubstEq.cons hτ.1 tL hLL
      have eMotive : CTypeEq (dataChurch d) Δ ((recMotiveTm d).subst (CTm.consSub L' τ'))
          ((recMotiveTm d).subst (CTm.consSub L τ)) :=
        ⟨_, motiveUniverse_data hd, .symm (CDerivable.functional (recMotiveTm_typed d) hsubL)⟩
      exact RT.expand (dataExtension hd).levels formed
        (CRedTm.dataRec hd formed hτ.1.1 entry hms
          (fun p hp => (CEqual.typed (dataExtension hd).levels (eq p hp) formed).1) hL)
        ((CRedTm.dataRec hd formed mor' entry hms'
          (fun p hp => (CEqual.typed (dataExtension hd).levels (eq p hp) formed).2) hL').convType
            eMotive) hN

end Claim

/-! ## The recursor is adequate -/

section Recursor

theorem envArgs_succ {N : Nat} (ρ : Env (N + 1)) :
    envArgs ρ = envArgs (fun i : Fin N => ρ i.succ) ++ [ρ 0] := by
  simp only [envArgs, List.finRange_succ, List.reverse_cons, List.map_append, List.map_reverse,
    List.map_map, List.map_cons, List.map_nil]
  rfl

/-- **The values of an environment fitting a context given by its entries are a spine of the
dependent function type over the context.** -/
theorem spineTyped_of_fits (Rd : Reading Tower.Head) (e : (j : Nat) → Tm Tower.Head j) :
    ∀ (M : Nat) (C : Tm Tower.Head M) {ρ : Env M}, Fits Rd (liftCtx (ofEntries e M)) ρ →
      Ideal.SpineTyped
        (cinterp Rd (liftTm (TelescopeAbstraction.closeType (ofEntries e M) C)) Env.nil)
        (envArgs ρ)
  | 0, _, ρ, _ => by
      rw [List.eq_nil_of_length_eq_zero (length_envArgs ρ)]
      trivial
  | M + 1, C, ρ, fits => by
      have ih := spineTyped_of_fits Rd e M (.pi (e M) C) fits.1
      rw [envArgs_succ, closeType_ofEntries_succ, Ideal.spineTyped_append]
      refine ⟨ih, ?_⟩
      rw [instPi_cinterp_ofEntries _ _ _ _ _ (length_envArgs _), Ideal.projArgs_of_spineTyped ih,
        ofArgs_envArgs]
      exact (spineTyped_cinterp_pi _ _ _ _ _ _).2 ⟨fits.2.2, trivial⟩

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- **The recursor's spine is adequate** at the motive at the element: its denotation is
recursion over the datatype at the element, projected onto the motive there, and each token of
the recursion lies in an approximant (`dataRec_claim`). -/
theorem adequate_dataRecSpine :
    Adequate (dataExtension hd).reading (dataHead hd) (recSpineCtx d) (recSpineTm d)
      (recMotiveTm d) := by
  intro ρ' fits' m Δ σ σ' formed hσ s hs hsT
  obtain ⟨x, ρ, rfl⟩ : ∃ x ρ, ρ' = Env.cons x ρ := ⟨_, _, env_eq_cons_tail ρ'⟩
  obtain ⟨L, τ, rfl⟩ : ∃ L τ, σ = CTm.consSub L τ := ⟨_, _, CTm.eq_consSub_tail σ⟩
  obtain ⟨L', τ', rfl⟩ : ∃ L' τ', σ' = CTm.consSub L' τ' := ⟨_, _, CTm.eq_consSub_tail σ'⟩
  rw [recSpineCtx_eq] at fits' hσ
  obtain ⟨hτ, hLL, hLx⟩ := SubstRel.of_cons hσ
  have fits : Fits (dataExtension hd).reading (recMethodsCtx d) ρ := fits'.1
  have hx : projT (dataTypeI d) x = x := by
    have h : projT ((dataReading d).const d.type) x = x := fits'.2.2
    rwa [dataReading_type hd] at h
  -- the denotation of the spine
  have spine : Ideal.SpineTyped (recTypeI d) (envArgs ρ) :=
    spineTyped_of_fits (dataReading d) (recEntry d.type d.motiveUniverse d.ctors)
      (d.ctors.length + 1) (.pi (recEntry d.type d.motiveUniverse d.ctors (d.ctors.length + 1))
        (recBody d.ctors.length)) fits
  have den : cinterp (dataExtension hd).reading (recSpineTm d) (Env.cons x ρ) =
      projT (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) x)
        (recI (dataCs d)
          (methodsAt ((envArgs ρ).getD 0 Ideal.bot) (dataCs d) (envArgs ρ).tail) x) := by
    rw [cinterp_recSpineTm]
    have h := appSpine_recursor hd (length_envArgs ρ) spine hx
    rw [headD_eq_getD] at h
    exact h
  rw [den] at hs
  have hsT' : TypedAt (Ideal.app ((envArgs ρ).getD 0 Ideal.bot) x) s := by
    rw [envArgs_getD_zero]
    exact hsT
  obtain ⟨v, hvI, hvT, e⟩ := Ideal.projT_eq_iSup.1 hs
  refine RT.closed' e fun g hg => ?_
  obtain ⟨k, hk⟩ := (Ideal.mem_recI (contList_methodsAt _ _ _)).1 (hvI g hg)
  have hν : ∀ y, x.Mem y → RT (dataHead hd) Δ true y (.const d.type) L L' := by
    intro y hy
    rw [← hx] at hy
    obtain ⟨w, hw, hwT, ew⟩ := Ideal.projT_eq_iSup.1 hy
    refine RT.closed' ew fun t ht => ?_
    refine hLx t (hw t ht) ?_
    show TypedAt ((dataReading d).const d.type) t
    rw [dataReading_type hd]
    exact hwT t ht
  exact dataRec_claim hd formed fits hτ k x L L' hx hLL hν g hk (hvT g hg)

omit hd in
/-- The recursor's spine, as the η-body of the recursor along its context. -/
theorem recSpine_eta :
    (CCtx.toTele (recSpineCtx d)).etaBody (.const d.recursor) = recSpineTm d :=
  etaBody_toTele_const d.recursor (recSpineCtx d)

theorem recEta_typed :
    CTyped (dataChurch d) (recSpineCtx d)
      ((CCtx.toTele (recSpineCtx d)).etaBody (.const d.recursor)) (recMotiveTm d) := by
  rw [recSpine_eta]
  exact recSpineTm_typed hd

theorem adequate_recEta :
    Adequate (dataExtension hd).reading (dataHead hd) (recSpineCtx d)
      ((CCtx.toTele (recSpineCtx d)).etaBody (.const d.recursor)) (recMotiveTm d) := by
  rw [recSpine_eta]
  exact adequate_dataRecSpine hd

/-- **The recursor of the datatype is adequate**, through its spine at the variables of its
context. -/
theorem constAdequateAt_rec : ConstAdequateAt (dataExtension hd).reading (dataHead hd) d.recursor :=
  ConstAdequateAt.of_spine (dataExtension hd).levels (dataExtension hd).soundnessFacts
    (rec_declared' hd) (recEta_typed hd) (adequate_recEta hd)

end Recursor

/-! ## Every constant of the package with the datatype is adequate -/

section Consequences

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- **Every constant of the object package with an admissible datatype is adequate**: the object
package's constants, by their adequacy in every extension, and the datatype, its constructors
and its recursor. -/
theorem dataChurch_constAdequate : ConstAdequate (dataExtension hd).reading (dataHead hd) := by
  intro c D u declared
  have declared' : sumDecls objectChurch.constantType
      (inductiveChurch objectRules d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).constantType c = some D := declared
  cases hobj : objectChurch.constantType c with
  | some D₀ =>
    exact ((dataExtension hd).objectConsts_adequate hobj : ConstAdequateAt _ _ c) declared
  | none =>
    rw [sumDecls_right hobj] at declared'
    rcases inductiveChurch_constantType objectRules hd.lamFree declared' with
      ⟨rfl, rfl⟩ | ⟨i, fields, entry, rfl⟩ | ⟨rfl, rfl⟩
    · exact (constAdequateAt_dataType hd : ConstAdequateAt _ _ d.type) declared
    · exact (constAdequateAt_ctor hd entry : ConstAdequateAt _ _ c) declared
    · exact (constAdequateAt_rec hd : ConstAdequateAt _ _ d.recursor) declared

/-- **The fundamental lemma at the object package with an admissible datatype**, with no
hypothesis: every derivable statement is valid over a formed context. -/
theorem dataChurch_fundamental {J : CStatement Tower.Head}
    (derivation : CDerivable (dataChurch d) J)
    (formed : J.CtxFormed (dataChurch d)) : J.Valid (dataExtension hd).reading (dataHead hd) :=
  CDerivable.valid_of_constAdequate (dataExtension hd).levels (dataExtension hd).valid
    (dataExtension hd).groundHeads (dataExtension hd).groundHeadEq (dataExtension hd).decoderStuck
    (dataChurch_constAdequate hd) derivation formed

/-- **The facts about the weak-head forms of the annotated types of the package with an
admissible datatype**, with no hypothesis. -/
theorem dataFormFacts : CFormFacts (dataChurch d) (dataRoles d) :=
  ObjectExtension.formFacts (X := dataExtension hd) (dataChurch_constAdequate hd)

/-- **The injectivity and no-confusion of the annotated type formers of the package with an
admissible datatype.** -/
theorem dataFormerFacts : CFormerFacts (dataChurch d) :=
  ObjectExtension.formerFacts (X := dataExtension hd) (dataChurch_constAdequate hd)

end Consequences

/-! ## Root steps with a declared datatype -/

section RootSteps

variable {d : Datatype Tower.Head} (admissible : d.Admissible objectChurch)
  (facts : CFormerFacts (withDeclarations objectChurch [.datatype d]))

include admissible facts in
/-- **The root steps of the object package with an admissible datatype preserve typing** in
formed contexts, given the injectivity and no-confusion of its annotated type formers: the
object package's steps by their typed templates, the recursor's rules by pattern inversion. -/
theorem objectDatatype_rootPreserving :
    CRootPreserving (withDeclarations objectChurch [.datatype d]) := by
  intro n Γ l r A formed step typing
  rcases step with step | step
  · exact objectChurch_preservesIn (withDeclarations_base objectChurch _) facts
      (levelsWith ConvRules.objectLevels [.datatype d]) formed step typing
  · exact iota_preservesIn ConvRules.objectLevels objectChurch (ChurchRulesSub.refl _)
      admissible.typeUniverse admissible.motiveUniverse admissible.distinct admissible.lamFree
      admissible.new admissible.fieldsFormed facts (levelsWith ConvRules.objectLevels [.datatype d])
      formed step typing

include admissible facts in
/-- **The typing of a redex of the object package with an admissible datatype gives the
premises of its root step**, by pattern inversion. -/
theorem objectDatatype_rootPremised :
    CRootPremised (withDeclarations objectChurch [.datatype d]) := by
  intro n Γ l r A formed step typing
  rcases step with step | step
  · exact objectChurch_premisedIn (withDeclarations_base objectChurch _)
      (StepsWithin.sum_left _ _) facts (levelsWith ConvRules.objectLevels [.datatype d]) formed
      step typing
  · exact iota_premisedIn objectChurch (ChurchRulesSub.refl _) (StepsWithin.sum_right _ _)
      admissible.new facts (levelsWith ConvRules.objectLevels [.datatype d]) formed step typing

variable (hd : d.Admissible objectChurch)
include hd

omit admissible facts in
/-- **The root steps of the package with an admissible datatype preserve typing**, with no
hypothesis. -/
theorem dataRootPreserving : CRootPreserving (dataChurch d) :=
  objectDatatype_rootPreserving hd (dataFormerFacts hd)

omit admissible facts in
/-- **The typing of a redex of the package with an admissible datatype gives the premises of its
root step**, with no hypothesis. -/
theorem dataRootPremised : CRootPremised (dataChurch d) :=
  objectDatatype_rootPremised hd (dataFormerFacts hd)

omit admissible facts in
/-- **The root steps of typed terms of the package with an admissible datatype are
equalities**, with no hypothesis. -/
theorem dataRootAdmitted : CRootAdmitted (dataChurch d) :=
  CRootPreserving.admitted (dataRootPreserving hd) (dataRootPremised hd)

end RootSteps

/-! ## Examples -/

/-- Positive: the package with the lists of numbers admits its root steps. -/
example : CRootAdmitted (dataChurch listDecl) := dataRootAdmitted listDecl_admissible

/-- Positive: the constants of the package with the lists of numbers are adequate. -/
example :
    ConstAdequate (dataExtension listDecl_admissible).reading (dataHead listDecl_admissible) :=
  dataChurch_constAdequate listDecl_admissible

/-- Positive: the hypothesis of `cons` is at its second field, the list. -/
example : flagPositions ([.closed (.const numN), .recursive].map fieldFlag) = [1] := rfl

/-- Negative: the number in `cons` carries no hypothesis. -/
example : 0 ∉ flagPositions ([.closed (.const numN), .recursive].map fieldFlag) := by decide

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
