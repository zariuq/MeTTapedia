import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Schemas

/-!
# Elaboration commutes with a map of heads

A package is moved to a larger language of heads by mapping its heads: the tower into the
tower with level names, the finite levels into the ordinal notations. Its rewrite schemas are
written without annotations and elaborated against its declared types. This module shows that
mapping the heads and elaborating commute: the elaboration of a mapped term, against the
mapped declared types and the mapped knowledge of the variables, is the mapped elaboration
(`elaborate_mapHead`). Hence the two sides of a schema, the types the positions of its left
side require, the equations of its reflexivity positions, and the elaborated declared types
of the mapped package are the mapped ones (`elabLeft_mapHead`, `elabRight_mapHead`,
`patternKnowledge_mapHead`, `patternEquations_mapHead`, `elabDeclarations_mapHead`).

A package presented by a schema family therefore has a mapped package, with the declared types
and the schemas mapped under the universe rules of a target (`ChurchRules.mapSchemas`), and
maps into it (`ChurchRules.mapSchemas_morphism`): the instances of the mapped schemas at terms
of the target's language are steps there, with the mapped premises
(`patternPremises_mapHead`).

Positive example: the unannotated identity checked at the functions on a universe, with its
heads mapped, is the identity elaborated at the mapped universe. Negative example: elaboration
reads the declared types; the argument of a constant that takes a function is annotated from
the constant's declared type and, without that declaration, with the unknown domain.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open AlgebraicSchema (SchemaFamily SchemaStep)

variable {HeadOne HeadTwo : Type}

/-! ## Knowledge and declared types at the mapped heads -/

namespace Knowledge

/-- What is known of the types of the variables, at the mapped heads. -/
def mapHead (g : HeadOne → HeadTwo) {n : Nat} (K : Knowledge HeadOne n) : Knowledge HeadTwo n :=
  fun i => (K i).map (CTm.mapHead g)

@[simp] theorem mapHead_empty (g : HeadOne → HeadTwo) {n : Nat} :
    (Knowledge.empty : Knowledge HeadOne n).mapHead g = Knowledge.empty :=
  rfl

theorem mapHead_cons (g : HeadOne → HeadTwo) {n : Nat} (type : Option (CTm HeadOne n))
    (K : Knowledge HeadOne n) :
    (K.cons type).mapHead g = (K.mapHead g).cons (type.map (CTm.mapHead g)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show (type.map (CTm.rename wk)).map (CTm.mapHead g) =
      (type.map (CTm.mapHead g)).map (CTm.rename wk)
    cases type with
    | none => rfl
    | some T => exact congrArg some (CTm.mapHead_rename g wk T)
  · show ((K j).map (CTm.rename wk)).map (CTm.mapHead g) =
      ((K j).map (CTm.mapHead g)).map (CTm.rename wk)
    cases K j with
    | none => rfl
    | some T => exact congrArg some (CTm.mapHead_rename g wk T)

theorem mapHead_merge (g : HeadOne → HeadTwo) {n : Nat} (K K' : Knowledge HeadOne n) :
    (K.merge K').mapHead g = (K.mapHead g).merge (K'.mapHead g) := by
  funext i
  show (match K i with
      | some T => some T
      | none => K' i).map (CTm.mapHead g) =
    match (K i).map (CTm.mapHead g) with
    | some T => some T
    | none => (K' i).map (CTm.mapHead g)
  cases K i <;> rfl

end Knowledge

/-- The declared types at the mapped heads. -/
def mapDecls (g : HeadOne → HeadTwo) (decls : DeclName → Option (CTm HeadOne 0)) :
    DeclName → Option (CTm HeadTwo 0) :=
  fun c => (decls c).map (CTm.mapHead g)

/-- Annotating every abstraction with one domain commutes with a map of heads. -/
theorem mapHead_annotateWith (g : HeadOne → HeadTwo) (domain : CTm HeadOne 0) :
    ∀ {n : Nat} (t : Tm HeadOne n),
      (CTm.annotateWith domain t).mapHead g = CTm.annotateWith (domain.mapHead g) (t.mapHead g)
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .head _ => rfl
  | _, .pi A B => by
    show CTm.pi _ _ = CTm.pi _ _
    rw [mapHead_annotateWith g domain A, mapHead_annotateWith g domain B]
  | _, .sigma A B => by
    show CTm.sigma _ _ = CTm.sigma _ _
    rw [mapHead_annotateWith g domain A, mapHead_annotateWith g domain B]
  | _, .id A a b => by
    show CTm.id _ _ _ = CTm.id _ _ _
    rw [mapHead_annotateWith g domain A, mapHead_annotateWith g domain a,
      mapHead_annotateWith g domain b]
  | _, .lam b => by
    show CTm.lam _ _ = CTm.lam _ _
    rw [mapHead_annotateWith g domain b, CTm.mapHead_liftClosed]
  | _, .app f a => by
    show CTm.app _ _ = CTm.app _ _
    rw [mapHead_annotateWith g domain f, mapHead_annotateWith g domain a]
  | _, .pair a b => by
    show CTm.pair _ _ = CTm.pair _ _
    rw [mapHead_annotateWith g domain a, mapHead_annotateWith g domain b]
  | _, .fst p => by
    show CTm.fst _ = CTm.fst _
    rw [mapHead_annotateWith g domain p]
  | _, .snd p => by
    show CTm.snd _ = CTm.snd _
    rw [mapHead_annotateWith g domain p]
  | _, .refl a => by
    show CTm.refl _ = CTm.refl _
    rw [mapHead_annotateWith g domain a]

/-- The annotation with the unknown domain commutes with a map of heads. -/
theorem mapHead_liftTm (g : HeadOne → HeadTwo) {n : Nat} (t : Tm HeadOne n) :
    (liftTm t).mapHead g = liftTm (t.mapHead g) :=
  mapHead_annotateWith g CTm.unknown t

/-! ## Elaboration -/

/-- **Elaboration commutes with a map of heads.** -/
theorem elaborate_mapHead (g : HeadOne → HeadTwo) (decls : DeclName → Option (CTm HeadOne 0)) :
    ∀ {n : Nat} (t : Tm HeadOne n) (K : Knowledge HeadOne n)
      (expected hint : Option (CTm HeadOne n)),
      elaborate (mapDecls g decls) (K.mapHead g) (expected.map (CTm.mapHead g))
          (hint.map (CTm.mapHead g)) (t.mapHead g) =
        ((elaborate decls K expected hint t).1.mapHead g,
          (elaborate decls K expected hint t).2.map (CTm.mapHead g)) := by
  intro n t
  induction t with
  | var i =>
    intro K expected hint
    rfl
  | const c =>
    intro K expected hint
    show ((CTm.const c : CTm HeadTwo _), ((decls c).map (CTm.mapHead g)).map CTm.liftClosed) =
      (CTm.const c, ((decls c).map CTm.liftClosed).map (CTm.mapHead g))
    cases decls c with
    | none => rfl
    | some T => simp only [Option.map_some, CTm.mapHead_liftClosed]
  | head h =>
    intro K expected hint
    rfl
  | pi A B ihA ihB =>
    intro K expected hint
    have a := ihA K none none
    have b := ihB (K.cons (some (elaborate decls K none none A).1)) none none
    rw [Knowledge.mapHead_cons] at b
    simp only [Option.map_none, Option.map_some] at a b
    simp only [Tm.mapHead, elaborate, a, b, CTm.mapHead, Option.map_none]
  | sigma A B ihA ihB =>
    intro K expected hint
    have a := ihA K none none
    have b := ihB (K.cons (some (elaborate decls K none none A).1)) none none
    rw [Knowledge.mapHead_cons] at b
    simp only [Option.map_none, Option.map_some] at a b
    simp only [Tm.mapHead, elaborate, a, b, CTm.mapHead, Option.map_none]
  | id A a b ihA iha ihb =>
    intro K expected hint
    have carrier := ihA K none none
    have left := iha K (some (elaborate decls K none none A).1) none
    have right := ihb K (some (elaborate decls K none none A).1) none
    simp only [Option.map_none, Option.map_some] at carrier left right
    simp only [Tm.mapHead, elaborate, carrier, left, right, CTm.mapHead, Option.map_none]
  | lam b ih =>
    intro K expected hint
    cases expected with
    | none =>
      cases hint with
      | none =>
        have body := ih (K.cons none) none none
        rw [Knowledge.mapHead_cons] at body
        simp only [Option.map_none] at body
        simp only [Tm.mapHead, elaborate, Option.map_none, body, CTm.mapHead]
        rfl
      | some D =>
        have body := ih (K.cons (some D)) none none
        rw [Knowledge.mapHead_cons] at body
        simp only [Option.map_none, Option.map_some] at body
        simp only [Tm.mapHead, elaborate, Option.map_none, Option.map_some, body, CTm.mapHead]
        cases (elaborate decls (K.cons (some D)) none none b).2 <;> rfl
    | some x =>
      cases x with
      | pi D B =>
        have body := ih (K.cons (some D)) (some B) none
        rw [Knowledge.mapHead_cons] at body
        simp only [Option.map_none, Option.map_some] at body
        simp only [Tm.mapHead, elaborate, Option.map_some, CTm.mapHead, body]
      | _ =>
        cases hint with
        | none =>
          have body := ih (K.cons none) none none
          rw [Knowledge.mapHead_cons] at body
          simp only [Option.map_none] at body
          simp only [Tm.mapHead, elaborate, Option.map_none, Option.map_some, body, CTm.mapHead]
          rfl
        | some D =>
          have body := ih (K.cons (some D)) none none
          rw [Knowledge.mapHead_cons] at body
          simp only [Option.map_none, Option.map_some] at body
          simp only [Tm.mapHead, elaborate, Option.map_some, body, CTm.mapHead]
          cases (elaborate decls (K.cons (some D)) none none b).2 <;> rfl
  | app f a ihf iha =>
    intro K expected hint
    have argument := iha K none none
    simp only [Option.map_none] at argument
    have function := ihf K none (elaborate decls K none none a).2
    simp only [Option.map_none] at function
    simp only [Tm.mapHead, elaborate, argument, function]
    cases found : (elaborate decls K none (elaborate decls K none none a).2 f).2 with
    | none => rfl
    | some x =>
      cases x with
      | pi D B =>
        have checked := iha K (some D) none
        simp only [Option.map_none, Option.map_some] at checked
        simp only [Option.map_some, CTm.mapHead, checked, CTm.mapHead_inst0]
      | _ => rfl
  | pair a b iha ihb =>
    intro K expected hint
    cases expected with
    | none =>
      have first := iha K none none
      have second := ihb K none none
      simp only [Option.map_none] at first second
      simp only [Tm.mapHead, elaborate, Option.map_none, first, second, CTm.mapHead]
    | some x =>
      cases x with
      | sigma A B =>
        have first := iha K (some A) none
        simp only [Option.map_none, Option.map_some] at first
        have second := ihb K (some (CTm.inst0 (elaborate decls K (some A) none a).1 B)) none
        simp only [Option.map_none, Option.map_some, CTm.mapHead_inst0] at second
        simp only [Tm.mapHead, elaborate, Option.map_some, CTm.mapHead, first, second]
      | _ =>
        have first := iha K none none
        have second := ihb K none none
        simp only [Option.map_none] at first second
        simp only [Tm.mapHead, elaborate, Option.map_some, CTm.mapHead, first, second,
          Option.map_none]
  | fst p ih =>
    intro K expected hint
    have inner := ih K none none
    simp only [Option.map_none] at inner
    simp only [Tm.mapHead, elaborate, inner]
    cases found : (elaborate decls K none none p).2 with
    | none => rfl
    | some x => cases x <;> rfl
  | snd p ih =>
    intro K expected hint
    have inner := ih K none none
    simp only [Option.map_none] at inner
    simp only [Tm.mapHead, elaborate, inner]
    cases found : (elaborate decls K none none p).2 with
    | none => rfl
    | some x =>
      cases x with
      | sigma A B => simp only [Option.map_some, CTm.mapHead, CTm.mapHead_inst0]
      | _ => rfl
  | refl a ih =>
    intro K expected hint
    cases expected with
    | none =>
      have inner := ih K none none
      simp only [Option.map_none] at inner
      simp only [Tm.mapHead, elaborate, Option.map_none, inner]
      cases (elaborate decls K none none a).2 <;> rfl
    | some x =>
      cases x with
      | id A x y =>
        have inner := ih K (some A) none
        simp only [Option.map_none, Option.map_some] at inner
        simp only [Tm.mapHead, elaborate, Option.map_some, CTm.mapHead, inner]
      | _ =>
        have inner := ih K none none
        simp only [Option.map_none] at inner
        simp only [Tm.mapHead, elaborate, Option.map_some, CTm.mapHead, inner]
        cases (elaborate decls K none none a).2 <;> rfl

/-! ## Schemas -/

/-- The elaborated left side of a mapped schema is the mapped elaborated left side. -/
theorem elabLeft_mapHead (g : HeadOne → HeadTwo) (decls : DeclName → Option (CTm HeadOne 0))
    {k : Nat} (L : Tm HeadOne k) :
    elabLeft (mapDecls g decls) (L.mapHead g) = (elabLeft decls L).mapHead g :=
  congrArg Prod.fst (elaborate_mapHead g decls L Knowledge.empty none none)

/-- The type the left side of a mapped schema synthesizes is the mapped one. -/
theorem leftType_mapHead (g : HeadOne → HeadTwo) (decls : DeclName → Option (CTm HeadOne 0))
    {k : Nat} (L : Tm HeadOne k) :
    leftType (mapDecls g decls) (L.mapHead g) = (leftType decls L).map (CTm.mapHead g) :=
  congrArg Prod.snd (elaborate_mapHead g decls L Knowledge.empty none none)

/-- The types the positions of a mapped left side require are the mapped ones. -/
theorem patternKnowledge_mapHead (g : HeadOne → HeadTwo)
    (decls : DeclName → Option (CTm HeadOne 0)) :
    ∀ {k : Nat} (L : Tm HeadOne k) (expected : Option (CTm HeadOne k)),
      patternKnowledge (mapDecls g decls) (expected.map (CTm.mapHead g)) (L.mapHead g) =
        (patternKnowledge decls expected L).mapHead g := by
  intro k L
  induction L with
  | var i =>
    intro expected
    funext j
    show (if j = i then expected.map (CTm.mapHead g) else none) =
      (if j = i then expected else none).map (CTm.mapHead g)
    by_cases same : j = i
    · rw [if_pos same, if_pos same]
    · rw [if_neg same, if_neg same]
      rfl
  | app f a ihf iha =>
    intro expected
    have function := ihf none
    simp only [Option.map_none] at function
    have synthesized := congrArg Prod.snd (elaborate_mapHead g decls f Knowledge.empty none none)
    simp only [Option.map_none, Knowledge.mapHead_empty] at synthesized
    simp only [Tm.mapHead, patternKnowledge, function, synthesized, Knowledge.mapHead_merge]
    cases found : (elaborate decls Knowledge.empty none none f).2 with
    | none =>
      have argument := iha none
      simp only [Option.map_none] at argument
      simp only [Option.map_none, argument]
    | some x =>
      cases x with
      | pi D B =>
        have argument := iha (some D)
        simp only [Option.map_some] at argument
        simp only [Option.map_some, CTm.mapHead, argument]
      | _ =>
        have argument := iha none
        simp only [Option.map_none] at argument
        simp only [Option.map_some, CTm.mapHead, argument]
  | refl a ih =>
    intro expected
    cases expected with
    | none =>
      have inner := ih none
      simp only [Option.map_none] at inner
      simp only [Tm.mapHead, patternKnowledge, Option.map_none, inner]
    | some x =>
      cases x with
      | id A x y =>
        have inner := ih (some A)
        simp only [Option.map_some] at inner
        simp only [Tm.mapHead, patternKnowledge, Option.map_some, CTm.mapHead, inner]
      | _ =>
        have inner := ih none
        simp only [Option.map_none] at inner
        simp only [Tm.mapHead, patternKnowledge, Option.map_some, CTm.mapHead, inner]
  | _ =>
    intro expected
    rfl

/-- A triple of an equation at the mapped heads. -/
def mapEquation (g : HeadOne → HeadTwo) {k : Nat}
    (e : CTm HeadOne k × CTm HeadOne k × CTm HeadOne k) :
    CTm HeadTwo k × CTm HeadTwo k × CTm HeadTwo k :=
  (e.1.mapHead g, e.2.1.mapHead g, e.2.2.mapHead g)

/-- The equations of the reflexivity positions of a mapped left side are the mapped ones. -/
theorem patternEquations_mapHead (g : HeadOne → HeadTwo)
    (decls : DeclName → Option (CTm HeadOne 0)) :
    ∀ {k : Nat} (L : Tm HeadOne k) (expected : Option (CTm HeadOne k)),
      patternEquations (mapDecls g decls) (expected.map (CTm.mapHead g)) (L.mapHead g) =
        (patternEquations decls expected L).map (mapEquation g) := by
  intro k L
  induction L with
  | app f a ihf iha =>
    intro expected
    have function := ihf none
    simp only [Option.map_none] at function
    have synthesized := congrArg Prod.snd (elaborate_mapHead g decls f Knowledge.empty none none)
    simp only [Option.map_none, Knowledge.mapHead_empty] at synthesized
    simp only [Tm.mapHead, patternEquations, function, synthesized, List.map_append]
    cases found : (elaborate decls Knowledge.empty none none f).2 with
    | none =>
      have argument := iha none
      simp only [Option.map_none] at argument
      simp only [Option.map_none, argument]
    | some x =>
      cases x with
      | pi D B =>
        have argument := iha (some D)
        simp only [Option.map_some] at argument
        simp only [Option.map_some, CTm.mapHead, argument]
      | _ =>
        have argument := iha none
        simp only [Option.map_none] at argument
        simp only [Option.map_some, CTm.mapHead, argument]
  | refl a ih =>
    intro expected
    cases expected with
    | none =>
      have inner := ih none
      simp only [Option.map_none] at inner
      simp only [Tm.mapHead, patternEquations, Option.map_none, inner, List.nil_append]
    | some x =>
      cases x with
      | id A x y =>
        have inner := ih (some A)
        simp only [Option.map_some] at inner
        simp only [Tm.mapHead, patternEquations, Option.map_some, CTm.mapHead, inner,
          List.map_append, List.map_cons, List.map_nil, mapEquation, mapHead_liftTm]
      | _ =>
        have inner := ih none
        simp only [Option.map_none] at inner
        simp only [Tm.mapHead, patternEquations, Option.map_some, CTm.mapHead, inner,
          List.nil_append]
  | _ =>
    intro expected
    rfl

/-- The elaborated right side of a mapped schema is the mapped elaborated right side. -/
theorem elabRight_mapHead (g : HeadOne → HeadTwo) (decls : DeclName → Option (CTm HeadOne 0))
    {k : Nat} (L R : Tm HeadOne k) :
    elabRight (mapDecls g decls) (L.mapHead g) (R.mapHead g) = (elabRight decls L R).mapHead g := by
  have knowledge := patternKnowledge_mapHead g decls L none
  simp only [Option.map_none] at knowledge
  unfold elabRight
  rw [knowledge, leftType_mapHead g decls L]
  have key := elaborate_mapHead g decls R (patternKnowledge decls none L) (leftType decls L) none
  simp only [Option.map_none] at key
  exact congrArg Prod.fst key

/-! ## Declared types -/

/-- The declared types read without elaboration, at the mapped heads. -/
theorem naiveDeclarations_mapHead (g : HeadOne → HeadTwo)
    (declared : DeclName → Option (Tm HeadOne 0)) :
    naiveDeclarations (fun c => (declared c).map (Tm.mapHead g)) =
      mapDecls g (naiveDeclarations declared) := by
  funext c
  show ((declared c).map (Tm.mapHead g)).map liftTm = ((declared c).map liftTm).map (CTm.mapHead g)
  cases declared c with
  | none => rfl
  | some T => exact congrArg some (mapHead_liftTm g T).symm

/-- **The elaborated declared types of a mapped package are the mapped elaborated declared
types.** -/
theorem elabDeclarations_mapHead (g : HeadOne → HeadTwo)
    (declared : DeclName → Option (Tm HeadOne 0)) :
    elabDeclarations (fun c => (declared c).map (Tm.mapHead g)) =
      mapDecls g (elabDeclarations declared) := by
  funext c
  show ((declared c).map (Tm.mapHead g)).map
      (elabClosed (naiveDeclarations fun c => (declared c).map (Tm.mapHead g))) =
    ((declared c).map (elabClosed (naiveDeclarations declared))).map (CTm.mapHead g)
  rw [naiveDeclarations_mapHead]
  cases declared c with
  | none => rfl
  | some T =>
    exact congrArg some (congrArg Prod.fst
      (elaborate_mapHead g (naiveDeclarations declared) T Knowledge.empty none none))

/-! ## Schema families and their packages along a map of heads -/

/-- A schema family along a map of heads. -/
def mapFamily (g : HeadOne → HeadTwo) (S : SchemaFamily HeadOne) : SchemaFamily HeadTwo :=
  fun {_} L' R' => ∃ L R, S L R ∧ L' = L.mapHead g ∧ R' = R.mapHead g

/-- **The premises of an instance of a mapped schema are the mapped premises of the
instance.** -/
theorem patternPremises_mapHead (g : HeadOne → HeadTwo)
    (decls : DeclName → Option (CTm HeadOne 0)) {k n : Nat} (L : Tm HeadOne k)
    (σ : CSub HeadOne k n) :
    patternPremises (mapDecls g decls) (L.mapHead g) (fun i => (σ i).mapHead g) =
      (patternPremises decls L σ).map (CPremise.mapHead g) := by
  have knowledge := patternKnowledge_mapHead g decls L none
  have equations := patternEquations_mapHead g decls L none
  simp only [Option.map_none] at knowledge equations
  unfold patternPremises
  rw [knowledge, equations, List.map_append, List.map_filterMap, List.map_map, List.map_map]
  congr 1
  · congr 1
    funext i
    show ((patternKnowledge decls none L i).map (CTm.mapHead g)).map
        (fun T => CPremise.typing ((σ i).mapHead g) (T.subst fun j => (σ j).mapHead g)) =
      ((patternKnowledge decls none L i).map
        fun T => CPremise.typing (σ i) (T.subst σ)).map (CPremise.mapHead g)
    cases patternKnowledge decls none L i with
    | none => rfl
    | some T =>
      show some (CPremise.typing _ _) = some (CPremise.typing _ _)
      rw [CTm.mapHead_subst]
  · congr 1
    funext e
    show CPremise.equality _ _ _ = CPremise.equality _ _ _
    rw [CTm.mapHead_subst, CTm.mapHead_subst, CTm.mapHead_subst]
    rfl

/-- **The rules of a package presented by a schema family, along a map of heads**: under the
universe rules of a target, its declared types and its schemas with their heads mapped. -/
def Rules.mapSchemas (g : HeadOne → HeadTwo) (target : Rules HeadTwo) (R : Rules HeadOne)
    (S : SchemaFamily HeadOne) : Rules HeadTwo :=
  { target with
    constantType := fun c => (R.constantType c).map (Tm.mapHead g)
    computation := SchemaFamily.computation (mapFamily g S) }

theorem Rules.mapSchemas_presents (g : HeadOne → HeadTwo) (target : Rules HeadTwo)
    (R : Rules HeadOne) (S : SchemaFamily HeadOne) :
    Presents (Rules.mapSchemas g target R S).computation (mapFamily g S) :=
  Iff.rfl

/-- The annotated package of the mapped schemas. -/
def ChurchRules.mapSchemas (g : HeadOne → HeadTwo) (target : Rules HeadTwo) (R : Rules HeadOne)
    (S : SchemaFamily HeadOne) : ChurchRules (Rules.mapSchemas g target R S) :=
  ChurchRules.ofSchemas (Rules.mapSchemas g target R S) (mapFamily g S)
    (Rules.mapSchemas_presents g target R S)

/-- Its declared types are the mapped elaborated declared types. -/
theorem ChurchRules.mapSchemas_constantType (g : HeadOne → HeadTwo) (target : Rules HeadTwo)
    (R : Rules HeadOne) (S : SchemaFamily HeadOne) :
    (ChurchRules.mapSchemas g target R S).constantType =
      mapDecls g (elabDeclarations R.constantType) := by
  show (elabDeclarations fun c => (R.constantType c).map (Tm.mapHead g)) = _
  exact elabDeclarations_mapHead g R.constantType

/-- **A package presented by a schema family maps into the package of its mapped schemas**,
along a map of heads under which its universe rules hold in the target. Every derivation of
the package is then a derivation of the mapped package (`CDerivable.mapHead`). -/
theorem ChurchRules.mapSchemas_morphism (g : HeadOne → HeadTwo) (target : Rules HeadTwo)
    (R : Rules HeadOne) (S : SchemaFamily HeadOne) (present : Presents R.computation S)
    (headTyping : ∀ {h u : HeadOne}, R.headTyping h u → target.headTyping (g h) (g u))
    (isUniverse : ∀ {u : HeadOne}, R.isUniverse u → target.isUniverse (g u))
    (join : ∀ {u v w : HeadOne}, R.join u v w → target.join (g u) (g v) (g w))
    (cumulative : ∀ {u v : HeadOne}, R.cumulative u v → target.cumulative (g u) (g v))
    (headEq : ∀ {h h' : HeadOne}, R.headEq h h' → target.headEq (g h) (g h')) :
    (ChurchRules.ofSchemas R S present).Morphism (ChurchRules.mapSchemas g target R S) g where
  headTyping := headTyping
  isUniverse := isUniverse
  join := join
  cumulative := cumulative
  headEq := headEq
  constantType := by
    intro c T known
    rw [ChurchRules.mapSchemas_constantType]
    show (elabDeclarations R.constantType c).map (CTm.mapHead g) = some (T.mapHead g)
    have known' : elabDeclarations R.constantType c = some T := known
    rw [known']
    rfl
  computation := by
    intro n l r step
    show CSchemaStep (elaborateFamily
      (elabDeclarations fun c => (R.constantType c).map (Tm.mapHead g)) (mapFamily g S)) _ _
    rw [elabDeclarations_mapHead]
    have step' : CSchemaStep (elaborateFamily (elabDeclarations R.constantType) S) l r := step
    cases step' with
    | instantiate rule σ =>
      obtain ⟨L, R', known, rfl, rfl⟩ := rule
      rw [CTm.mapHead_subst, CTm.mapHead_subst, ← elabLeft_mapHead, ← elabRight_mapHead]
      exact .instantiate ⟨L.mapHead g, R'.mapHead g, ⟨L, R', known, rfl, rfl⟩, rfl, rfl⟩ _
  requires := by
    intro n l r premises _ required
    have required' : CSchemaRequires (elabDeclarations R.constantType) S l r premises := required
    cases required' with
    | @instantiate k L R' rule σ =>
      refine ⟨(patternPremises (elabDeclarations R.constantType) L σ).map (CPremise.mapHead g),
        ?_, fun premise mem => ?_⟩
      · show CSchemaRequires (elabDeclarations fun c => (R.constantType c).map (Tm.mapHead g))
          (mapFamily g S) _ _ _
        rw [elabDeclarations_mapHead, CTm.mapHead_subst, CTm.mapHead_subst,
          ← elabLeft_mapHead, ← elabRight_mapHead, ← patternPremises_mapHead]
        exact .instantiate ⟨L, R', rule, rfl, rfl⟩ _
      · obtain ⟨source, member, rfl⟩ := List.mem_map.mp mem
        exact ⟨source, member, rfl⟩

/-! ## Examples -/

section Examples

/-- The unannotated identity, checked at the functions on the universe `3`. -/
def identityOnThree : CTm Nat 0 :=
  (elaborate (fun _ => none) Knowledge.empty (some (.pi (.head 3) (.head 3))) none
    (.lam (.var 0))).1

/-- Its abstraction is annotated with the universe. -/
example : identityOnThree = .lam (.head 3) (.var 0) := rfl

/-- Positive: with the heads raised by one it is the identity elaborated at the universe
`4`. -/
example : identityOnThree.mapHead (· + 1) =
    (elaborate (fun _ => none) Knowledge.empty (some (.pi (.head 4) (.head 4))) none
      (.lam (.var 0))).1 :=
  rfl

/-- A constant `f` that takes a function on the universe `1`. -/
def takesFunction : DeclName → Option (CTm Nat 0) := fun c =>
  if c = `f then some (.pi (.pi (.head 1) (.head 1)) (.head 0)) else none

/-- Against that declaration the argument's abstraction is annotated with the universe. -/
example : (elaborate takesFunction Knowledge.empty none none
    (.app (.const `f) (.lam (.var 0)) : Tm Nat 0)).1 =
      .app (.const `f) (.lam (.head 1) (.var 0)) := by
  decide

/-- Negative: without the declaration the annotation is the unknown domain, so the declared
types must be mapped with the term. -/
example : (elaborate (fun _ => none) Knowledge.empty none none
    (.app (.const `f) (.lam (.var 0)) : Tm Nat 0)).1 ≠
      .app (.const `f) (.lam (.head 1) (.var 0)) := by
  decide

end Examples

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
