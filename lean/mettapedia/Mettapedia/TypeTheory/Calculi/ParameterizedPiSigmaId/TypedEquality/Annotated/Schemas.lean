import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Elaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Structural
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicSchema
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DeclaredComputations

/-!
# Annotated rewrite schemas

A root computation is *presented* by a family of rewrite schemas when its steps
are exactly the instances of the schemas (`Presents`). The annotation of such a
computation is derived from the presentation, not written by hand:

* each schema is elaborated (`elaborateFamily`): its left side synthesizes its
  type from the declared type of its head, and its right side is elaborated
  against that type, with each metavariable typed as its position in the left
  side requires;
* the annotated root steps are the instances of the elaborated schemas by
  annotated substitutions (`CSchemaFamily.computation`), closed under renaming
  and substitution by construction.

**Erasure** (`CSchemaStep.erase_elaborate`): an annotated step erases to an
instance of the schema it elaborates, so to a root step of the computation.

**Lifting** (`elaborateFamily_lift`): when the left sides are first-order and
left-linear (`FirstOrderFamily`), every root step of the erasure of an annotated
term is the erasure of an annotated root step of that term. The annotated term
is matched against the elaborated left side (`match_firstOrder`), and the
matched parts are substituted into the elaborated right side: arguments are
carried with their own annotations, and only the right side's own abstractions
receive elaborated ones.

**Premises** (`patternPremises`, `CSchemaRequires`): an instance of a schema
requires the typings of the instances of its metavariables at the types the left
side's positions require, and the equations of its reflexivity positions. A
package admits the instance in a context where these hold
(`CSchemaRequires.admits`).

`ChurchRules.ofSchemas` is the resulting annotation of a rule package: its
declared types elaborated, its root steps the instances of its elaborated
schemas, each requiring the premises of its instance.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open AlgebraicSchema (SchemaFamily SchemaStep LeftLinear variableMultiplicity)

variable {Head : Type}

/-! ## Annotated schema families -/

/-- A family of annotated rewrite schemas: a left and a right side over their own
metavariables. -/
abbrev CSchemaFamily (Head : Type) :=
  {arity : Nat} → CTm Head arity → CTm Head arity → Prop

/-- One annotated root step: a schema instantiated by an annotated substitution. -/
inductive CSchemaStep (S : CSchemaFamily Head) {n : Nat} : CTm Head n → CTm Head n → Prop
  | instantiate {arity : Nat} {left right : CTm Head arity} (rule : S left right)
      (σ : CSub Head arity n) : CSchemaStep S (left.subst σ) (right.subst σ)

/-- The annotated root computation whose steps are the instances of the schemas. -/
def CSchemaFamily.computation (S : CSchemaFamily Head) : CRootComputation Head where
  step := CSchemaStep S
  rename := by
    intro n m ρ l r step
    cases step with
    | instantiate rule σ =>
        rw [CTm.rename_subst, CTm.rename_subst]
        exact .instantiate rule _
  substitute := by
    intro n m τ l r step
    cases step with
    | instantiate rule σ =>
        rw [CTm.subst_comp, CTm.subst_comp]
        exact .instantiate rule _

/-- **The elaboration of a schema family**: each schema's left side and its right
side elaborated against the left side's type. -/
def elaborateFamily (decls : DeclName → Option (CTm Head 0)) (S : SchemaFamily Head) :
    CSchemaFamily Head :=
  fun {_} left right => ∃ L R, S L R ∧ left = elabLeft decls L ∧ right = elabRight decls L R

/-- **Erasure**: an instance of an elaborated schema erases to an instance of the
schema. -/
theorem CSchemaStep.erase_elaborate {decls : DeclName → Option (CTm Head 0)}
    {S : SchemaFamily Head} {n : Nat} {l r : CTm Head n}
    (step : CSchemaStep (elaborateFamily decls S) l r) : SchemaStep S l.erase r.erase := by
  cases step with
  | instantiate rule σ =>
      obtain ⟨L, R, hS, rfl, rfl⟩ := rule
      rw [CTm.erase_subst, CTm.erase_subst, erase_elabLeft, erase_elabRight]
      exact SchemaStep.instantiate hS _

/-! ## Matching first-order left sides -/

theorem variableMultiplicity_app {k : Nat} (i : Fin k) (f a : Tm Head k) :
    variableMultiplicity i (.app f a) = variableMultiplicity i f + variableMultiplicity i a := rfl

theorem LeftLinear.app_left {k : Nat} {f a : Tm Head k} (linear : LeftLinear (.app f a)) :
    LeftLinear f := fun i => by
  have := linear i
  rw [variableMultiplicity_app] at this
  omega

theorem LeftLinear.app_right {k : Nat} {f a : Tm Head k} (linear : LeftLinear (.app f a)) :
    LeftLinear a := fun i => by
  have := linear i
  rw [variableMultiplicity_app] at this
  omega

theorem LeftLinear.refl_inner {k : Nat} {a : Tm Head k} (linear : LeftLinear (.refl a)) :
    LeftLinear a :=
  linear

/-- Substituting into a first-order term depends only on its variables. -/
theorem subst_annotateWith_congr {k n : Nat} {L : Tm Head k} (fo : firstOrder L = true)
    {σ σ' : CSub Head k n} (agree : ∀ i, variableMultiplicity i L ≠ 0 → σ i = σ' i) :
    (CTm.annotateWith CTm.unknown L).subst σ = (CTm.annotateWith CTm.unknown L).subst σ' := by
  induction L with
  | var i =>
      exact agree i (by simp [variableMultiplicity])
  | const => rfl
  | head => rfl
  | pi => cases fo
  | sigma => cases fo
  | id => cases fo
  | lam => cases fo
  | pair => cases fo
  | fst => cases fo
  | snd => cases fo
  | app f a ihf iha =>
      simp only [firstOrder, Bool.and_eq_true] at fo
      simp only [CTm.annotateWith, CTm.subst]
      rw [ihf fo.1 fun i h => agree i (by rw [variableMultiplicity_app]; omega),
        iha fo.2 fun i h => agree i (by rw [variableMultiplicity_app]; omega)]
  | refl a ih =>
      simp only [CTm.annotateWith, CTm.subst]
      rw [ih fo fun i h => agree i h]

/-- **Matching**: an annotated term whose erasure is an instance of a first-order,
left-linear term is an instance of that term's annotation, by an annotated
substitution erasing to the instance's. -/
theorem match_firstOrder {k n : Nat} {L : Tm Head k} (fo : firstOrder L = true)
    (linear : LeftLinear L) {l : CTm Head n} {τ : Sub Head k n}
    (e : l.erase = Presentation.subst τ L) :
    ∃ σ : CSub Head k n, (CTm.annotateWith CTm.unknown L).subst σ = l ∧
      ∀ i, (σ i).erase = τ i := by
  induction L generalizing l with
  | var i =>
      refine ⟨fun j => if j = i then l else CTm.annotateWith CTm.unknown (τ j), ?_, ?_⟩
      · simp [CTm.annotateWith, CTm.subst]
      · intro j
        by_cases h : j = i
        · subst h
          simpa using e
        · simp [h]
  | const c =>
      obtain rfl := CTm.erase_eq_const e
      exact ⟨fun j => CTm.annotateWith CTm.unknown (τ j), rfl, fun j => by simp⟩
  | head h =>
      obtain rfl := CTm.erase_eq_head e
      exact ⟨fun j => CTm.annotateWith CTm.unknown (τ j), rfl, fun j => by simp⟩
  | pi => cases fo
  | sigma => cases fo
  | id => cases fo
  | lam => cases fo
  | pair => cases fo
  | fst => cases fo
  | snd => cases fo
  | app f a ihf iha =>
      simp only [firstOrder, Bool.and_eq_true] at fo
      obtain ⟨l₁, l₂, rfl, e₁, e₂⟩ := CTm.erase_eq_app e
      obtain ⟨σ₁, h₁, er₁⟩ := ihf fo.1 (LeftLinear.app_left linear) e₁
      obtain ⟨σ₂, h₂, er₂⟩ := iha fo.2 (LeftLinear.app_right linear) e₂
      refine ⟨fun j => if variableMultiplicity j f = 0 then σ₂ j else σ₁ j, ?_, ?_⟩
      · simp only [CTm.annotateWith, CTm.subst]
        rw [subst_annotateWith_congr fo.1 (σ' := σ₁) (fun j hj => by simp [hj]),
          subst_annotateWith_congr fo.2 (σ' := σ₂) (fun j hj => by
            have := linear j
            rw [variableMultiplicity_app] at this
            have hf : variableMultiplicity j f = 0 := by omega
            simp [hf]), h₁, h₂]
      · intro j
        by_cases hj : variableMultiplicity j f = 0
        · simp [hj, er₂]
        · simp [hj, er₁]
  | refl a ih =>
      obtain ⟨l₁, rfl, e₁⟩ := CTm.erase_eq_refl e
      obtain ⟨σ, h, er⟩ := ih fo (LeftLinear.refl_inner linear) e₁
      exact ⟨σ, by simp only [CTm.annotateWith, CTm.subst, h], er⟩

/-! ## Lifting -/

/-- Schema families whose left sides are first-order and left-linear. -/
def FirstOrderFamily (S : SchemaFamily Head) : Prop :=
  ∀ {k : Nat} {L R : Tm Head k}, S L R → firstOrder L = true ∧ LeftLinear L

/-- Whether a term is first-order and left-linear, by evaluation. -/
def firstOrderLinear {k : Nat} (L : Tm Head k) : Bool :=
  firstOrder L && (List.finRange k).all fun i => decide (variableMultiplicity i L ≤ 1)

theorem firstOrderLinear_spec {k : Nat} {L : Tm Head k} (h : firstOrderLinear L = true) :
    firstOrder L = true ∧ LeftLinear L := by
  simp only [firstOrderLinear, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun i => h.2 i (List.mem_finRange i)⟩

/-- **Lifting**: an instance of a first-order, left-linear schema at the erasure
of an annotated term is the erasure of an instance of the elaborated schema at
that term. -/
theorem elaborateFamily_lift {decls : DeclName → Option (CTm Head 0)} {S : SchemaFamily Head}
    (fo : FirstOrderFamily S) {n : Nat} {l : CTm Head n} {r₀ : Tm Head n}
    (step : SchemaStep S l.erase r₀) :
    ∃ r, CSchemaStep (elaborateFamily decls S) l r ∧ r.erase = r₀ := by
  generalize hl : l.erase = l₀ at step
  cases step with
  | instantiate rule τ =>
      rename_i k L R
      obtain ⟨hfo, hlin⟩ := fo rule
      obtain ⟨σ, hσ, er⟩ := match_firstOrder hfo hlin hl
      refine ⟨(elabRight decls L R).subst σ, ?_, ?_⟩
      · have step := CSchemaStep.instantiate (S := elaborateFamily decls S)
          ⟨L, R, rule, rfl, rfl⟩ σ
        rwa [elabLeft_firstOrder decls hfo, hσ] at step
      · rw [CTm.erase_subst, erase_elabRight]
        exact Presentation.subst_ext (fun i => er i) R

/-! ## Typed right sides -/

/-- **The elaborated right side of a schema is typed**: in a context whose
variables have the types the left side's positions require, at the type the left
side synthesizes. -/
def TemplateTyped {R : Rules Head} (P : ChurchRules R) (decls : DeclName → Option (CTm Head 0))
    {k : Nat} (L R' : Tm Head k) : Prop :=
  ∃ (Θ : CCtx Head k) (T : CTm Head k),
    (∀ i, patternKnowledge decls none L i = some (Θ.lookup i)) ∧ leftType decls L = some T ∧
      CTyped P Θ (elabRight decls L R') T

/-! ## Presentations -/

/-- A root computation is presented by a schema family when its steps are exactly
the instances of the schemas. -/
def Presents (c : RootComputation Head) (S : SchemaFamily Head) : Prop :=
  ∀ {n : Nat} {l r : Tm Head n}, c.step l r ↔ SchemaStep S l r

/-- The union of two schema families. -/
def schemaUnion (S S' : SchemaFamily Head) : SchemaFamily Head :=
  fun L R => S L R ∨ S' L R

/-- The empty schema family. -/
def schemaEmpty : SchemaFamily Head := fun _ _ => False

theorem SchemaStep.union_iff {S S' : SchemaFamily Head} {n : Nat} {l r : Tm Head n} :
    SchemaStep (schemaUnion S S') l r ↔ SchemaStep S l r ∨ SchemaStep S' l r := by
  constructor
  · intro step
    cases step with
    | instantiate rule τ =>
        rcases rule with h | h
        · exact .inl (.instantiate h τ)
        · exact .inr (.instantiate h τ)
  · rintro (step | step)
    · cases step with
      | instantiate rule τ => exact .instantiate (Or.inl rule) τ
    · cases step with
      | instantiate rule τ => exact .instantiate (Or.inr rule) τ

theorem Presents.union {c c' : RootComputation Head} {S S' : SchemaFamily Head}
    (h : Presents c S) (h' : Presents c' S') :
    Presents (Normalization.RootComputation.union c c') (schemaUnion S S') := by
  intro n l r
  rw [SchemaStep.union_iff]
  exact or_congr h h'

theorem Presents.empty : Presents (RootComputation.empty : RootComputation Head)
    schemaEmpty := by
  intro n l r
  constructor
  · intro step
    exact step.elim
  · intro step
    cases step with
    | instantiate rule _ => exact rule.elim

/-- The union of the listed schema families. -/
def schemaUnionAll : List (DeclName × SchemaFamily Head) → SchemaFamily Head
  | [] => schemaEmpty
  | entry :: rest => schemaUnion entry.2 (schemaUnionAll rest)

/-- The union of computations presented entry by entry is presented by the union
of the presentations. -/
theorem Presents.unionAll :
    ∀ {cs : List (DeclName × RootComputation Head)} {ss : List (DeclName × SchemaFamily Head)},
      List.Forall₂ (fun c s => Presents c.2 s.2) cs ss →
        Presents (Normalization.RootComputation.unionAll cs) (schemaUnionAll ss)
  | [], [], .nil => Presents.empty
  | _ :: _, _ :: _, .cons h rest => Presents.union h (Presents.unionAll rest)

theorem FirstOrderFamily.union {S S' : SchemaFamily Head} (h : FirstOrderFamily S)
    (h' : FirstOrderFamily S') : FirstOrderFamily (schemaUnion S S') := by
  intro k L R rule
  rcases rule with r | r
  · exact h r
  · exact h' r

theorem FirstOrderFamily.unionAll :
    ∀ {ss : List (DeclName × SchemaFamily Head)}, (∀ s ∈ ss, FirstOrderFamily s.2) →
      FirstOrderFamily (schemaUnionAll ss)
  | [], _ => fun rule => rule.elim
  | s :: _, h => FirstOrderFamily.union (h s (List.mem_cons_self ..))
      (FirstOrderFamily.unionAll fun s' mem => h s' (List.mem_cons_of_mem _ mem))

/-! ## The premises of a schema instance -/

/-- **The premises of an instance of a left side**: the typing of each metavariable's
instance at the type its position requires (`patternKnowledge`), and the equations of its
reflexivity positions (`patternEquations`), instantiated. -/
def patternPremises (decls : DeclName → Option (CTm Head 0)) {k n : Nat} (L : Tm Head k)
    (σ : CSub Head k n) : List (CPremise Head n) :=
  ((List.finRange k).filterMap fun i =>
      (patternKnowledge decls none L i).map fun T => CPremise.typing (σ i) (T.subst σ)) ++
    (patternEquations decls none L).map fun e =>
      CPremise.equality (e.1.subst σ) (e.2.1.subst σ) (e.2.2.subst σ)

/-- A premise of an instance is the typing of a metavariable's instance or an equation of a
reflexivity position. -/
theorem mem_patternPremises {decls : DeclName → Option (CTm Head 0)} {k n : Nat}
    {L : Tm Head k} {σ : CSub Head k n} {premise : CPremise Head n} :
    premise ∈ patternPremises decls L σ ↔
      (∃ i T, patternKnowledge decls none L i = some T ∧
        premise = .typing (σ i) (T.subst σ)) ∨
      ∃ e ∈ patternEquations decls none L,
        premise = .equality (e.1.subst σ) (e.2.1.subst σ) (e.2.2.subst σ) := by
  unfold patternPremises
  rw [List.mem_append, List.mem_filterMap, List.mem_map]
  constructor
  · rintro (⟨i, -, found⟩ | ⟨e, member, rfl⟩)
    · obtain ⟨T, known, rfl⟩ := Option.map_eq_some_iff.1 found
      exact .inl ⟨i, T, known, rfl⟩
    · exact .inr ⟨e, member, rfl⟩
  · rintro (⟨i, T, known, rfl⟩ | ⟨e, member, rfl⟩)
    · exact .inl ⟨i, List.mem_finRange i, by rw [known]; rfl⟩
    · exact .inr ⟨e, member, rfl⟩

/-- The premises of an instance, substituted, are the premises of the composed instance. -/
theorem patternPremises_subst (decls : DeclName → Option (CTm Head 0)) {k n m : Nat}
    (L : Tm Head k) (σ : CSub Head k n) (τ : CSub Head n m) :
    (patternPremises decls L σ).map (CPremise.subst τ) =
      patternPremises decls L fun i => (σ i).subst τ := by
  unfold patternPremises
  rw [List.map_append, List.map_filterMap, List.map_map]
  congr 1
  · refine List.filterMap_congr fun i _ => ?_
    cases patternKnowledge decls none L i with
    | none => rfl
    | some T => simp only [Option.map_some, CPremise.subst, CTm.subst_comp]
  · refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply, CPremise.subst, CTm.subst_comp]

/-- The premises of an instance, renamed, are the premises of the renamed instance. -/
theorem patternPremises_rename (decls : DeclName → Option (CTm Head 0)) {k n m : Nat}
    (L : Tm Head k) (σ : CSub Head k n) (ρ : Ren n m) :
    (patternPremises decls L σ).map (CPremise.rename ρ) =
      patternPremises decls L fun i => (σ i).rename ρ := by
  unfold patternPremises
  rw [List.map_append, List.map_filterMap, List.map_map]
  congr 1
  · refine List.filterMap_congr fun i _ => ?_
    cases patternKnowledge decls none L i with
    | none => rfl
    | some T => simp only [Option.map_some, CPremise.rename, CTm.rename_subst]
  · refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply, CPremise.rename, CTm.rename_subst]

/-- **The premises the instances of a schema family require**: an instance of a schema by a
substitution requires the premises of its left side at that substitution. -/
inductive CSchemaRequires (decls : DeclName → Option (CTm Head 0)) (S : SchemaFamily Head)
    {n : Nat} : CTm Head n → CTm Head n → List (CPremise Head n) → Prop
  | instantiate {k : Nat} {L R : Tm Head k} (rule : S L R) (σ : CSub Head k n) :
      CSchemaRequires decls S ((elabLeft decls L).subst σ) ((elabRight decls L R).subst σ)
        (patternPremises decls L σ)

/-- **The annotated root computation of a schema family**: its steps are the instances of
the elaborated schemas, and each instance requires the premises of its left side. -/
def elaboratedComputation (decls : DeclName → Option (CTm Head 0)) (S : SchemaFamily Head) :
    CRootComputation Head where
  step := CSchemaStep (elaborateFamily decls S)
  rename := (CSchemaFamily.computation (elaborateFamily decls S)).rename
  substitute := (CSchemaFamily.computation (elaborateFamily decls S)).substitute
  requires := CSchemaRequires decls S
  requires_rename := by
    rintro n m ρ _ _ _ ⟨rule, σ⟩
    rw [CTm.rename_subst, CTm.rename_subst, patternPremises_rename]
    exact .instantiate rule _
  requires_substitute := by
    rintro n m τ _ _ _ ⟨rule, σ⟩
    rw [CTm.subst_comp, CTm.subst_comp, patternPremises_subst]
    exact .instantiate rule _

/-- **An instance of a schema is admitted** by a package that requires the premises of the
family's instances, in a context where the instances of the schema's metavariables have the
types its left side's positions require and the equations of its reflexivity positions
hold. -/
theorem CSchemaRequires.admits {R' : Rules Head} {Q : ChurchRules R'}
    {decls : DeclName → Option (CTm Head 0)} {S : SchemaFamily Head}
    (contains : ∀ {n : Nat} {l r : CTm Head n} {premises : List (CPremise Head n)},
      CSchemaRequires decls S l r premises → Q.computation.requires l r premises)
    {k n : Nat} {L R : Tm Head k} (rule : S L R) {Γ : CCtx Head n} (σ : CSub Head k n)
    (typings : ∀ i T, patternKnowledge decls none L i = some T → CTyped Q Γ (σ i) (T.subst σ))
    (equations : ∀ e ∈ patternEquations decls none L,
      CEqual Q Γ (e.1.subst σ) (e.2.1.subst σ) (e.2.2.subst σ)) :
    Q.Admits Γ ((elabLeft decls L).subst σ) ((elabRight decls L R).subst σ) :=
  ⟨patternPremises decls L σ, contains (.instantiate rule σ), fun premise member => by
    rcases mem_patternPremises.1 member with ⟨i, T, known, rfl⟩ | ⟨e, mem, rfl⟩
    · exact typings i T known
    · exact equations e mem⟩

/-- A typed substitution along the telescope a left side's positions require types the
instances of the metavariables as the positions require. -/
theorem CSubstMor.patternTypings {R' : Rules Head} {Q : ChurchRules R'}
    {decls : DeclName → Option (CTm Head 0)} {k n : Nat} {L : Tm Head k} {Θ : CCtx Head k}
    {Γ : CCtx Head n} {σ : CSub Head k n}
    (known : ∀ i, patternKnowledge decls none L i = some (Θ.lookup i))
    (mor : CSubstMor Q Θ Γ σ) :
    ∀ i T, patternKnowledge decls none L i = some T → CTyped Q Γ (σ i) (T.subst σ) := by
  intro i T found
  rw [known i] at found
  cases found
  exact mor i

/-! ## The annotation of a presented rule package -/

variable {R : Rules Head}

/-- **The annotation of a rule package presented by a schema family**: its
declared types elaborated, as root steps the instances of its elaborated
schemas, and as the premises of a step those of its instance: the typings of the
instances of its metavariables and the equations of its reflexivity positions. -/
def ChurchRules.ofSchemas (R : Rules Head) (S : SchemaFamily Head)
    (present : Presents R.computation S) : ChurchRules R where
  constantType := elabDeclarations R.constantType
  computation := elaboratedComputation (elabDeclarations R.constantType) S
  erase_constantType := erase_elabDeclarations R.constantType
  erase_step := fun step => present.2 (CSchemaStep.erase_elaborate step)

theorem ChurchRules.ofSchemas_constantType (S : SchemaFamily Head)
    (present : Presents R.computation S) (c : DeclName) :
    (ChurchRules.ofSchemas R S present).constantType c = elabDeclarations R.constantType c :=
  rfl

/-- The annotated root steps are the instances of the elaborated schemas. -/
theorem ChurchRules.ofSchemas_step_iff (S : SchemaFamily Head)
    (present : Presents R.computation S) {n : Nat} {l r : CTm Head n} :
    (ChurchRules.ofSchemas R S present).computation.step l r ↔
      CSchemaStep (elaborateFamily (elabDeclarations R.constantType) S) l r :=
  Iff.rfl

/-- The premises a step of the annotation requires are those of its schema instance. -/
theorem ChurchRules.ofSchemas_requires_iff (S : SchemaFamily Head)
    (present : Presents R.computation S) {n : Nat} {l r : CTm Head n}
    {premises : List (CPremise Head n)} :
    (ChurchRules.ofSchemas R S present).computation.requires l r premises ↔
      CSchemaRequires (elabDeclarations R.constantType) S l r premises :=
  Iff.rfl

/-- **Root lifting** for a presented rule package with first-order, left-linear
left sides: every root step of the erasure of an annotated term is the erasure of
an annotated root step of that term. -/
theorem ChurchRules.ofSchemas_lift (S : SchemaFamily Head) (present : Presents R.computation S)
    (fo : FirstOrderFamily S) {n : Nat} {l : CTm Head n} {r₀ : Tm Head n}
    (step : R.computation.step l.erase r₀) :
    ∃ r, (ChurchRules.ofSchemas R S present).computation.step l r ∧ r.erase = r₀ :=
  elaborateFamily_lift fo (present.1 step)

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
