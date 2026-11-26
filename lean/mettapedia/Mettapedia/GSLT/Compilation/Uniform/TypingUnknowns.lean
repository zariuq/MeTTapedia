import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.Logic.LP.UnificationComplete

/-!
# Typing under unknown contexts, by equations

A pattern has a type under some free and some bound contexts exactly when the equations it generates have a unifier
(`typed_iff`). The generation reads the pattern once (`Generates`): a name's type is the unknown of that name, a loose
index's type is the unknown of that index, and each binder, substitution and collection introduces unknowns at its
position. A constructor's arguments are checked against the types of its declared parameters.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.TypingUnknowns

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Logic.LP (LPSignature Subst Unifies)

/-! ## Types as first-order terms -/

/-- The heads of composite types. -/
inductive TypeHead where
  | arrow
  | multiBinder
  | collection (kind : CollType)
  deriving DecidableEq

/-- The number of arguments of a head. -/
def TypeHead.arity : TypeHead → ℕ
  | .arrow => 2
  | .multiBinder => 1
  | .collection _ => 1

/-- **The unknowns of a typing**: the type of a free name, of a loose index, or one at a position of the pattern. -/
inductive TypeUnknown where
  | free (name : String)
  | loose (index : ℕ)
  | node (path : List ℕ) (slot : ℕ)
  deriving DecidableEq

/-- The signature of types: base categories are constants, and composite types apply heads. -/
def typeSignature : LPSignature where
  constants := String
  vars := TypeUnknown
  relationSymbols := Empty
  relationArity := fun e => nomatch e
  functionSymbols := TypeHead
  functionArity := TypeHead.arity

instance : DecidableEq typeSignature.vars := inferInstanceAs (DecidableEq TypeUnknown)
instance : DecidableEq typeSignature.constants := inferInstanceAs (DecidableEq String)
instance : DecidableEq typeSignature.functionSymbols := inferInstanceAs (DecidableEq TypeHead)

/-- A type with unknowns. -/
abbrev TypeTerm := Mettapedia.Logic.LP.Term typeSignature

/-- An unknown as a type. -/
def unknown (u : TypeUnknown) : TypeTerm := .var u

/-- Two arguments. -/
def twoArgs (first second : TypeTerm) (i : Fin 2) : TypeTerm := if i.val = 0 then first else second

/-- The arrow between two types. -/
def arrowTerm (domain codomain : TypeTerm) : TypeTerm :=
  .app (σ := typeSignature) TypeHead.arrow (twoArgs domain codomain)

/-- The type of a binder of several names. -/
def binderTerm (body : TypeTerm) : TypeTerm := .app (σ := typeSignature) TypeHead.multiBinder fun _ => body

/-- The type of a collection of a kind. -/
def collectionTerm (kind : CollType) (element : TypeTerm) : TypeTerm :=
  .app (σ := typeSignature) (TypeHead.collection kind) fun _ => element

/-- **A type as a term.** -/
def typeTerm : TypeExpr → TypeTerm
  | .base name => .const name
  | .arrow domain codomain => arrowTerm (typeTerm domain) (typeTerm codomain)
  | .multiBinder body => binderTerm (typeTerm body)
  | .collection kind element => collectionTerm kind (typeTerm element)

/-- **A term read as a type**; an unknown is read as the empty base category. -/
def decodeType : TypeTerm → TypeExpr
  | .var _ => .base ""
  | .const name => .base name
  | .app TypeHead.arrow ts => .arrow (decodeType (ts ⟨0, by decide⟩)) (decodeType (ts ⟨1, by decide⟩))
  | .app TypeHead.multiBinder ts => .multiBinder (decodeType (ts ⟨0, by decide⟩))
  | .app (TypeHead.collection kind) ts => .collection kind (decodeType (ts ⟨0, Nat.one_pos⟩))

@[simp] theorem decodeType_arrowTerm (domain codomain : TypeTerm) :
    decodeType (arrowTerm domain codomain) = .arrow (decodeType domain) (decodeType codomain) := rfl

@[simp] theorem decodeType_binderTerm (body : TypeTerm) :
    decodeType (binderTerm body) = .multiBinder (decodeType body) := rfl

@[simp] theorem decodeType_collectionTerm (kind : CollType) (element : TypeTerm) :
    decodeType (collectionTerm kind element) = .collection kind (decodeType element) := rfl

@[simp] theorem decodeType_typeTerm : ∀ type : TypeExpr, decodeType (typeTerm type) = type
  | .base _ => rfl
  | .arrow domain codomain => by
      rw [typeTerm, decodeType_arrowTerm, decodeType_typeTerm domain, decodeType_typeTerm codomain]
  | .multiBinder body => by rw [typeTerm, decodeType_binderTerm, decodeType_typeTerm body]
  | .collection kind element => by rw [typeTerm, decodeType_collectionTerm, decodeType_typeTerm element]

@[simp] theorem applyTerm_arrowTerm (θ : Subst typeSignature) (domain codomain : TypeTerm) :
    θ.applyTerm (arrowTerm domain codomain) = arrowTerm (θ.applyTerm domain) (θ.applyTerm codomain) := by
  simp only [arrowTerm, Subst.applyTerm]
  congr 1
  funext i
  simp only [twoArgs]
  split <;> rfl

@[simp] theorem applyTerm_binderTerm (θ : Subst typeSignature) (body : TypeTerm) :
    θ.applyTerm (binderTerm body) = binderTerm (θ.applyTerm body) := rfl

@[simp] theorem applyTerm_collectionTerm (θ : Subst typeSignature) (kind : CollType) (element : TypeTerm) :
    θ.applyTerm (collectionTerm kind element) = collectionTerm kind (θ.applyTerm element) := rfl

/-- A type has no unknowns, so every substitution keeps it. -/
@[simp] theorem applyTerm_typeTerm (θ : Subst typeSignature) : ∀ type : TypeExpr,
    θ.applyTerm (typeTerm type) = typeTerm type
  | .base _ => rfl
  | .arrow domain codomain => by
      rw [typeTerm, applyTerm_arrowTerm, applyTerm_typeTerm θ domain, applyTerm_typeTerm θ codomain]
  | .multiBinder body => by rw [typeTerm, applyTerm_binderTerm, applyTerm_typeTerm θ body]
  | .collection kind element => by rw [typeTerm, applyTerm_collectionTerm, applyTerm_typeTerm θ element]

/-! ## The equations a pattern generates -/

variable (language : LanguageDef)

mutual
  /-- **The equations a pattern generates** at an expected type, under the types of the binders around it, at a
  position. -/
  inductive Generates : Pattern → TypeTerm → List TypeTerm → List ℕ → List (TypeTerm × TypeTerm) → Prop
    | bvarInside {index : ℕ} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} {T : TypeTerm} :
        ctx[index]? = some T → Generates (.bvar index) τ ctx π [(τ, T)]
    | bvarLoose {index : ℕ} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} :
        ctx.length ≤ index → Generates (.bvar index) τ ctx π [(τ, unknown (.loose (index - ctx.length)))]
    | fvar {name : String} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} :
        Generates (.fvar name) τ ctx π [(τ, unknown (.free name))]
    | lambda {binder : Option String} {body : Pattern} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ}
        {E : List (TypeTerm × TypeTerm)} :
        Generates body (unknown (.node π 1)) (unknown (.node π 0) :: ctx) (0 :: π) E →
        Generates (.lambda binder body) τ ctx π ((τ, arrowTerm (unknown (.node π 0)) (unknown (.node π 1))) :: E)
    | multiLambda {arity : ℕ} {binders : List String} {body : Pattern} {τ : TypeTerm} {ctx : List TypeTerm}
        {π : List ℕ} {E : List (TypeTerm × TypeTerm)} :
        Generates body (unknown (.node π 1)) (List.replicate arity (unknown (.node π 0)) ++ ctx) (0 :: π) E →
        Generates (.multiLambda arity binders body) τ ctx π
          ((τ, arrowTerm (binderTerm (unknown (.node π 0))) (unknown (.node π 1))) :: E)
    | subst {body replacement : Pattern} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ}
        {E₁ E₂ : List (TypeTerm × TypeTerm)} :
        Generates body τ (unknown (.node π 0) :: ctx) (0 :: π) E₁ →
        Generates replacement (unknown (.node π 0)) ctx (1 :: π) E₂ →
        Generates (.subst body replacement) τ ctx π (E₁ ++ E₂)
    | collection {kind : CollType} {elements : List Pattern} {rest : Option String} {τ : TypeTerm}
        {ctx : List TypeTerm} {π : List ℕ} {E : List (TypeTerm × TypeTerm)} :
        ElementsGenerate elements (unknown (.node π 0)) ctx π 0 E →
        Generates (.collection kind elements rest) τ ctx π ((τ, collectionTerm kind (unknown (.node π 0))) :: E)
    | collectionConstructor {rule : GrammarRule} {parameterName : String} {kind : CollType}
        {elementType : TypeExpr} {elements : List Pattern} {rest : Option String} {τ : TypeTerm}
        {ctx : List TypeTerm} {π : List ℕ} {E : List (TypeTerm × TypeTerm)} :
        rule ∈ language.terms → rule.bareParams = [.simple parameterName (.collection kind elementType)] →
        ElementsGenerate elements (typeTerm elementType) ctx π 0 E →
        Generates (.collection kind elements rest) τ ctx π ((τ, .const rule.category) :: E)
    | constructor {rule : GrammarRule} {arguments : List Pattern} {τ : TypeTerm} {ctx : List TypeTerm}
        {π : List ℕ} {E : List (TypeTerm × TypeTerm)} :
        rule ∈ language.terms → ¬ UsesBareCollection rule →
        ArgumentsGenerate arguments rule.params ctx π 0 E →
        Generates (.apply rule.label arguments) τ ctx π ((τ, .const rule.category) :: E)

  /-- The equations the elements of a collection generate, each at its own position. -/
  inductive ElementsGenerate : List Pattern → TypeTerm → List TypeTerm → List ℕ → ℕ →
      List (TypeTerm × TypeTerm) → Prop
    | nil {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} {index : ℕ} : ElementsGenerate [] τ ctx π index []
    | cons {element : Pattern} {elements : List Pattern} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ}
        {index : ℕ} {E₁ E₂ : List (TypeTerm × TypeTerm)} :
        Generates element τ ctx (index :: π) E₁ → ElementsGenerate elements τ ctx π (index + 1) E₂ →
        ElementsGenerate (element :: elements) τ ctx π index (E₁ ++ E₂)

  /-- The equations the arguments of a constructor generate at the types of its parameters. -/
  inductive ArgumentsGenerate : List Pattern → List TermParam → List TypeTerm → List ℕ → ℕ →
      List (TypeTerm × TypeTerm) → Prop
    | nil {ctx : List TypeTerm} {π : List ℕ} {index : ℕ} : ArgumentsGenerate [] [] ctx π index []
    | cons {argument : Pattern} {arguments : List Pattern} {parameter : TermParam} {parameters : List TermParam}
        {expected : TypeExpr} {ctx : List TypeTerm} {π : List ℕ} {index : ℕ} {E₁ E₂ : List (TypeTerm × TypeTerm)} :
        MatchesParameterRepresentation parameter argument → parameterType? parameter = some expected →
        Generates argument (typeTerm expected) ctx (index :: π) E₁ →
        ArgumentsGenerate arguments parameters ctx π (index + 1) E₂ →
        ArgumentsGenerate (argument :: arguments) (parameter :: parameters) ctx π index (E₁ ++ E₂)
end

/-! ## Indices below a bound -/

mutual
  /-- Every index of a pattern is below a bound. -/
  def IndicesBelow (bound : ℕ) : Pattern → Prop
    | .bvar index => index < bound
    | .fvar _ => True
    | .apply _ arguments => IndicesBelowList bound arguments
    | .lambda _ body => IndicesBelow bound body
    | .multiLambda _ _ body => IndicesBelow bound body
    | .subst body replacement => IndicesBelow bound body ∧ IndicesBelow bound replacement
    | .collection _ elements _ => IndicesBelowList bound elements

  def IndicesBelowList (bound : ℕ) : List Pattern → Prop
    | [] => True
    | pattern :: patterns => IndicesBelow bound pattern ∧ IndicesBelowList bound patterns
end

mutual
  theorem indicesBelow_exists : ∀ p : Pattern, ∃ bound, IndicesBelow bound p
    | .bvar index => ⟨index + 1, by simp [IndicesBelow]⟩
    | .fvar _ => ⟨0, trivial⟩
    | .apply _ arguments => by
        obtain ⟨bound, below⟩ := indicesBelowList_exists arguments
        exact ⟨bound, below⟩
    | .lambda _ body => by
        obtain ⟨bound, below⟩ := indicesBelow_exists body
        exact ⟨bound, below⟩
    | .multiLambda _ _ body => by
        obtain ⟨bound, below⟩ := indicesBelow_exists body
        exact ⟨bound, below⟩
    | .subst body replacement => by
        obtain ⟨first, firstBelow⟩ := indicesBelow_exists body
        obtain ⟨second, secondBelow⟩ := indicesBelow_exists replacement
        exact ⟨max first second, indicesBelow_mono (le_max_left _ _) body firstBelow,
          indicesBelow_mono (le_max_right _ _) replacement secondBelow⟩
    | .collection _ elements _ => by
        obtain ⟨bound, below⟩ := indicesBelowList_exists elements
        exact ⟨bound, below⟩

  theorem indicesBelowList_exists : ∀ ps : List Pattern, ∃ bound, IndicesBelowList bound ps
    | [] => ⟨0, trivial⟩
    | p :: ps => by
        obtain ⟨first, firstBelow⟩ := indicesBelow_exists p
        obtain ⟨second, secondBelow⟩ := indicesBelowList_exists ps
        exact ⟨max first second, indicesBelow_mono (le_max_left _ _) p firstBelow,
          indicesBelowList_mono (le_max_right _ _) ps secondBelow⟩

  theorem indicesBelow_mono {small large : ℕ} (le : small ≤ large) : ∀ p : Pattern, IndicesBelow small p →
      IndicesBelow large p
    | .bvar _, below => lt_of_lt_of_le below le
    | .fvar _, below => below
    | .apply _ arguments, below => indicesBelowList_mono le arguments below
    | .lambda _ body, below => indicesBelow_mono le body below
    | .multiLambda _ _ body, below => indicesBelow_mono le body below
    | .subst body replacement, below => ⟨indicesBelow_mono le body below.1, indicesBelow_mono le replacement below.2⟩
    | .collection _ elements _, below => indicesBelowList_mono le elements below

  theorem indicesBelowList_mono {small large : ℕ} (le : small ≤ large) : ∀ ps : List Pattern,
      IndicesBelowList small ps → IndicesBelowList large ps
    | [], _ => trivial
    | p :: ps, below => ⟨indicesBelow_mono le p below.1, indicesBelowList_mono le ps below.2⟩
end

/-! ## A unifier gives a typing -/

/-- A term read as a type after a substitution. -/
def decodeUnder (θ : Subst typeSignature) (t : TypeTerm) : TypeExpr := decodeType (θ.applyTerm t)

/-- The free context a substitution gives. -/
def freeContext (θ : Subst typeSignature) : FreeTypeContext :=
  fun name => some (decodeUnder θ (unknown (.free name)))

/-- The bound context a substitution gives, for the indices below a bound. -/
def boundContext (θ : Subst typeSignature) (bound : ℕ) : List TypeExpr :=
  (List.range bound).map fun j => decodeUnder θ (unknown (.loose j))

theorem unifies_cons {θ : Subst typeSignature} {a b : TypeTerm} {E : List (TypeTerm × TypeTerm)}
    (unified : Unifies θ ((a, b) :: E)) : θ.applyTerm a = θ.applyTerm b ∧ Unifies θ E :=
  ⟨unified (a, b) List.mem_cons_self, fun q inside => unified q (List.mem_cons_of_mem _ inside)⟩

theorem boundContext_get {θ : Subst typeSignature} {bound j : ℕ} (below : j < bound) :
    (boundContext θ bound)[j]? = some (decodeUnder θ (unknown (.loose j))) := by
  simp [boundContext, below]

theorem unifies_append {θ : Subst typeSignature} {E₁ E₂ : List (TypeTerm × TypeTerm)}
    (unified : Unifies θ (E₁ ++ E₂)) : Unifies θ E₁ ∧ Unifies θ E₂ :=
  ⟨fun q inside => unified q (List.mem_append_left _ inside), fun q inside => unified q (List.mem_append_right _ inside)⟩

variable {language}

mutual
  /-- **A unifier of the generated equations gives a typing**, under the contexts it determines. -/
  theorem generates_sound (θ : Subst typeSignature) (bound : ℕ) :
      ∀ {p : Pattern} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} {E : List (TypeTerm × TypeTerm)},
      Generates language p τ ctx π E → Unifies θ E → IndicesBelow bound p →
      HasType language (freeContext θ) (ctx.map (decodeUnder θ) ++ boundContext θ bound) p (decodeUnder θ τ)
    | _, _, ctx, _, _, .bvarInside (index := index) (T := T) found, unified, _ => by
        have same := (unifies_cons unified).1
        refine .bvar ?_
        have inside : index < ctx.length := (List.getElem?_eq_some_iff.mp found).1
        rw [List.getElem?_append_left (by simpa using inside), List.getElem?_map, found]
        simp only [Option.map_some, decodeUnder, same]
    | _, _, ctx, _, _, .bvarLoose (index := index) outside, unified, below => by
        have same := (unifies_cons unified).1
        refine .bvar ?_
        have lengths : (ctx.map (decodeUnder θ)).length = ctx.length := List.length_map _
        rw [List.getElem?_append_right (by simpa using outside), lengths]
        simp only [IndicesBelow] at below
        rw [boundContext_get (by omega)]
        simp only [decodeUnder, same]
    | _, _, _, _, _, .fvar (name := name), unified, _ => by
        have same := (unifies_cons unified).1
        refine .fvar ?_
        simp only [freeContext, decodeUnder, same]
    | _, τ, ctx, π, _, .lambda (body := body) generated, unified, below => by
        obtain ⟨same, rest⟩ := unifies_cons unified
        have inner := generates_sound θ bound generated rest below
        simp only [List.map_cons, List.cons_append] at inner
        have typeIs : decodeUnder θ τ = .arrow (decodeUnder θ (unknown (.node π 0))) (decodeUnder θ (unknown (.node π 1))) := by
          simp only [decodeUnder, same, applyTerm_arrowTerm, decodeType_arrowTerm]
        rw [typeIs]
        exact .lambda inner
    | _, τ, ctx, π, _, .multiLambda (arity := arity) (body := body) generated, unified, below => by
        obtain ⟨same, rest⟩ := unifies_cons unified
        have inner := generates_sound θ bound generated rest below
        simp only [List.map_append, List.map_replicate, List.append_assoc] at inner
        have typeIs : decodeUnder θ τ =
            .arrow (.multiBinder (decodeUnder θ (unknown (.node π 0)))) (decodeUnder θ (unknown (.node π 1))) := by
          simp only [decodeUnder, same, applyTerm_arrowTerm, applyTerm_binderTerm, decodeType_arrowTerm,
            decodeType_binderTerm]
        rw [typeIs]
        exact .multiLambda inner
    | _, _, ctx, π, _, .subst first second, unified, below => by
        obtain ⟨firstUnified, secondUnified⟩ := unifies_append unified
        have body := generates_sound θ bound first firstUnified below.1
        have replacement := generates_sound θ bound second secondUnified below.2
        simp only [List.map_cons, List.cons_append] at body
        exact .subst body replacement
    | _, τ, ctx, π, _, .collection (kind := kind) generated, unified, below => by
        obtain ⟨same, rest⟩ := unifies_cons unified
        have typeIs : decodeUnder θ τ = .collection kind (decodeUnder θ (unknown (.node π 0))) := by
          simp only [decodeUnder, same, applyTerm_collectionTerm, decodeType_collectionTerm]
        rw [typeIs]
        exact .collection (elementsGenerate_sound θ bound generated rest below)
    | _, τ, ctx, π, _, .collectionConstructor (rule := rule) member shape generated, unified, below => by
        obtain ⟨same, rest⟩ := unifies_cons unified
        have typeIs : decodeUnder θ τ = .base rule.category := by
          simp only [decodeUnder, same]
          rfl
        rw [typeIs]
        have elementsTyped := elementsGenerate_sound θ bound generated rest below
        simp only [decodeUnder, applyTerm_typeTerm, decodeType_typeTerm] at elementsTyped
        exact .collectionConstructor member shape elementsTyped
    | _, τ, ctx, π, _, .constructor (rule := rule) member notBare generated, unified, below => by
        obtain ⟨same, rest⟩ := unifies_cons unified
        have typeIs : decodeUnder θ τ = .base rule.category := by
          simp only [decodeUnder, same]
          rfl
        rw [typeIs]
        exact .constructor member notBare (argumentsGenerate_sound θ bound generated rest below)

  theorem elementsGenerate_sound (θ : Subst typeSignature) (bound : ℕ) :
      ∀ {elements : List Pattern} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} {index : ℕ}
      {E : List (TypeTerm × TypeTerm)},
      ElementsGenerate language elements τ ctx π index E → Unifies θ E → IndicesBelowList bound elements →
      ElementsHaveType language (freeContext θ) (ctx.map (decodeUnder θ) ++ boundContext θ bound) elements
        (decodeUnder θ τ)
    | _, _, _, _, _, _, .nil, _, _ => .nil _ _
    | _, _, _, _, _, _, .cons first second, unified, below => by
        obtain ⟨firstUnified, secondUnified⟩ := unifies_append unified
        exact .cons (generates_sound θ bound first firstUnified below.1)
          (elementsGenerate_sound θ bound second secondUnified below.2)

  theorem argumentsGenerate_sound (θ : Subst typeSignature) (bound : ℕ) :
      ∀ {arguments : List Pattern} {parameters : List TermParam} {ctx : List TypeTerm} {π : List ℕ} {index : ℕ}
      {E : List (TypeTerm × TypeTerm)},
      ArgumentsGenerate language arguments parameters ctx π index E → Unifies θ E → IndicesBelowList bound arguments →
      ArgumentsHaveTypes language (freeContext θ) (ctx.map (decodeUnder θ) ++ boundContext θ bound) arguments parameters
    | _, _, _, _, _, _, .nil, _, _ => .nil
    | _, _, _, _, _, _, .cons representation expectedIs first second, unified, below => by
        obtain ⟨firstUnified, secondUnified⟩ := unifies_append unified
        have typed := generates_sound θ bound first firstUnified below.1
        simp only [decodeUnder, applyTerm_typeTerm, decodeType_typeTerm] at typed
        exact .cons representation expectedIs typed (argumentsGenerate_sound θ bound second secondUnified below.2)
end

/-! ## A typing gives a unifier -/

/-- **A substitution agrees with contexts**: on the binders around, the loose indices beyond them, and the free
names. -/
structure Agrees (free : FreeTypeContext) (Γ : List TypeExpr) (ctx : List TypeTerm) (θ : Subst typeSignature) :
    Prop where
  short : ctx.length ≤ Γ.length
  binders : ∀ (i : ℕ) (type : TypeExpr), Γ[i]? = some type → i < ctx.length →
    ∃ entry, ctx[i]? = some entry ∧ θ.applyTerm entry = typeTerm type
  loose : ∀ (j : ℕ) (type : TypeExpr), Γ[ctx.length + j]? = some type → θ (.loose j) = typeTerm type
  names : ∀ (name : String) (type : TypeExpr), free name = some type → θ (.free name) = typeTerm type

theorem Agrees.cons {free : FreeTypeContext} {Γ : List TypeExpr} {ctx : List TypeTerm} {θ : Subst typeSignature}
    (agrees : Agrees free Γ ctx θ) {entry : TypeTerm} {type : TypeExpr} (entryIs : θ.applyTerm entry = typeTerm type) :
    Agrees free (type :: Γ) (entry :: ctx) θ where
  short := by simpa using agrees.short
  binders := fun i other found inside => by
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact ⟨entry, rfl, entryIs⟩
    | succ i => exact agrees.binders i other (by simpa using found) (by simpa using inside)
  loose := fun j other found => agrees.loose j other (by simpa [Nat.add_right_comm] using found)
  names := agrees.names

theorem Agrees.replicate {free : FreeTypeContext} {Γ : List TypeExpr} {ctx : List TypeTerm} {θ : Subst typeSignature}
    (agrees : Agrees free Γ ctx θ) {entry : TypeTerm} {type : TypeExpr} (entryIs : θ.applyTerm entry = typeTerm type) :
    ∀ arity : ℕ, Agrees free (List.replicate arity type ++ Γ) (List.replicate arity entry ++ ctx) θ
  | 0 => by simpa using agrees
  | arity + 1 => by
      have shorter := Agrees.replicate agrees entryIs arity
      simpa [List.replicate_succ] using shorter.cons entryIs

theorem suffix_heads {i j : ℕ} {π path : List ℕ} (first : (i :: π) <:+ path) (second : (j :: π) <:+ path) :
    i = j := by
  obtain ⟨t₁, firstIs⟩ := first
  obtain ⟨t₂, secondIs⟩ := second
  have same := firstIs.trans secondIs.symm
  have lengths : t₁.length = t₂.length := by
    have counted := congrArg List.length same
    simp only [List.length_append, List.length_cons] at counted
    omega
  have tails := (List.append_inj same lengths).2
  simpa using tails

/-- The bound context a typing gives, read at an index. -/
noncomputable def boundAt (bound : List TypeExpr) (j : ℕ) : TypeExpr := (bound[j]?).getD (.base "")

open Classical in
mutual
  /-- **A typing gives a unifier of the generated equations**: the types of the derivation, at the unknowns of the
  positions under the current one. -/
  theorem generates_complete {free : FreeTypeContext} :
      ∀ {Γ : List TypeExpr} {p : Pattern} {T : TypeExpr}, HasType language free Γ p T →
      ∀ (ctx : List TypeTerm) (τ : TypeTerm) (π : List ℕ), ∃ E, Generates language p τ ctx π E ∧
        ∃ nodes : List ℕ → ℕ → TypeExpr, ∀ θ : Subst typeSignature, Agrees free Γ ctx θ →
          θ.applyTerm τ = typeTerm T → (∀ path slot, π <:+ path → θ (.node path slot) = typeTerm (nodes path slot)) →
          Unifies θ E
    | _, _, _, .bvar (index := index) (type := type) found, ctx, τ, π => by
        by_cases inside : index < ctx.length
        · obtain ⟨entry, entryAt⟩ : ∃ entry, ctx[index]? = some entry :=
            ⟨ctx[index], List.getElem?_eq_getElem inside⟩
          refine ⟨_, .bvarInside entryAt, fun _ _ => .base "", fun θ agrees τIs _ => ?_⟩
          obtain ⟨entry', entry'At, entryIs⟩ := agrees.binders index type found inside
          rw [entryAt] at entry'At
          cases entry'At
          intro q member
          simp only [List.mem_singleton] at member
          subst member
          rw [τIs, entryIs]
        · refine ⟨_, .bvarLoose (by omega), fun _ _ => .base "", fun θ agrees τIs _ => ?_⟩
          intro q member
          simp only [List.mem_singleton] at member
          subst member
          have looseIs := agrees.loose (index - ctx.length) type (by rw [Nat.add_sub_cancel' (by omega)]; exact found)
          simp only [unknown, Subst.applyTerm, τIs, looseIs]
    | _, _, _, .fvar (name := name) (type := type) found, ctx, τ, π => by
        refine ⟨_, .fvar, fun _ _ => .base "", fun θ agrees τIs _ => ?_⟩
        intro q member
        simp only [List.mem_singleton] at member
        subst member
        simp only [unknown, Subst.applyTerm, τIs, agrees.names name type found]
    | _, _, _, .constructor (rule := rule) member notBare typed, ctx, τ, π => by
        obtain ⟨E, generated, nodes, unifies⟩ := argumentsHaveTypes_complete typed ctx π 0
        refine ⟨_, .constructor member notBare generated, nodes, fun θ agrees τIs agreeNodes => ?_⟩
        intro q inside
        rcases List.mem_cons.mp inside with rfl | later
        · simp only [τIs]
          rfl
        · exact (unifies θ agrees fun path slot under =>
            agreeNodes path slot (by obtain ⟨i, -, below⟩ := under; exact (List.suffix_cons _ _).trans below)) q later
    | _, _, _, .lambda (domain := domain) (codomain := codomain) typed, ctx, τ, π => by
        obtain ⟨E, generated, nodes, unifies⟩ :=
          generates_complete typed (unknown (.node π 0) :: ctx) (unknown (.node π 1)) (0 :: π)
        refine ⟨_, .lambda generated,
          fun path slot => if path = π then (if slot = 0 then domain else codomain) else nodes path slot,
          fun θ agrees τIs agreeNodes => ?_⟩
        have domainIs : θ (.node π 0) = typeTerm domain := by simpa using agreeNodes π 0 (List.suffix_refl π)
        have codomainIs : θ (.node π 1) = typeTerm codomain := by simpa using agreeNodes π 1 (List.suffix_refl π)
        intro q inside
        rcases List.mem_cons.mp inside with rfl | later
        · simp only [τIs, applyTerm_arrowTerm, unknown, Subst.applyTerm, domainIs, codomainIs]
          rfl
        · refine unifies θ (agrees.cons (by simpa [unknown, Subst.applyTerm] using domainIs))
            (by simpa [unknown, Subst.applyTerm] using codomainIs) (fun path slot under => ?_) q later
          have notHere : path ≠ π := fun same => by
            subst same
            have := under.length_le
            simp at this
          simpa [notHere] using agreeNodes path slot ((List.suffix_cons _ _).trans under)
    | _, _, _, .multiLambda (arity := arity) (domain := domain) (codomain := codomain) typed, ctx, τ, π => by
        obtain ⟨E, generated, nodes, unifies⟩ :=
          generates_complete typed (List.replicate arity (unknown (.node π 0)) ++ ctx) (unknown (.node π 1)) (0 :: π)
        refine ⟨_, .multiLambda generated,
          fun path slot => if path = π then (if slot = 0 then domain else codomain) else nodes path slot,
          fun θ agrees τIs agreeNodes => ?_⟩
        have domainIs : θ (.node π 0) = typeTerm domain := by simpa using agreeNodes π 0 (List.suffix_refl π)
        have codomainIs : θ (.node π 1) = typeTerm codomain := by simpa using agreeNodes π 1 (List.suffix_refl π)
        intro q inside
        rcases List.mem_cons.mp inside with rfl | later
        · simp only [τIs, applyTerm_arrowTerm, applyTerm_binderTerm, unknown, Subst.applyTerm, domainIs, codomainIs]
          rfl
        · refine unifies θ (agrees.replicate (by simpa [unknown, Subst.applyTerm] using domainIs) arity)
            (by simpa [unknown, Subst.applyTerm] using codomainIs) (fun path slot under => ?_) q later
          have notHere : path ≠ π := fun same => by
            subst same
            have := under.length_le
            simp at this
          simpa [notHere] using agreeNodes path slot ((List.suffix_cons _ _).trans under)
    | _, _, _, .subst (domain := domain) bodyTyped replacementTyped, ctx, τ, π => by
        obtain ⟨E₁, first, nodes₁, unifies₁⟩ := generates_complete bodyTyped (unknown (.node π 0) :: ctx) τ (0 :: π)
        obtain ⟨E₂, second, nodes₂, unifies₂⟩ := generates_complete replacementTyped ctx (unknown (.node π 0)) (1 :: π)
        refine ⟨_, .subst first second,
          fun path slot => if path = π then domain else if (0 :: π) <:+ path then nodes₁ path slot
            else nodes₂ path slot,
          fun θ agrees τIs agreeNodes => ?_⟩
        have domainIs : θ (.node π 0) = typeTerm domain := by simpa using agreeNodes π 0 (List.suffix_refl π)
        intro q inside
        rcases List.mem_append.mp inside with inFirst | inSecond
        · refine unifies₁ θ (agrees.cons (by simpa [unknown, Subst.applyTerm] using domainIs)) τIs
            (fun path slot under => ?_) q inFirst
          have notHere : path ≠ π := fun same => by
            subst same
            have := under.length_le
            simp at this
          simpa [notHere, under] using agreeNodes path slot ((List.suffix_cons _ _).trans under)
        · refine unifies₂ θ agrees (by simpa [unknown, Subst.applyTerm] using domainIs)
            (fun path slot under => ?_) q inSecond
          have notHere : path ≠ π := fun same => by
            subst same
            have := under.length_le
            simp at this
          have notFirst : ¬ (0 :: π) <:+ path := fun first => by
            have := suffix_heads first under
            omega
          simpa [notHere, notFirst] using agreeNodes path slot ((List.suffix_cons _ _).trans under)
    | _, _, _, .collection (collectionType := kind) (elementType := elementType) typed, ctx, τ, π => by
        obtain ⟨E, generated, nodes, unifies⟩ := elementsHaveType_complete typed ctx (unknown (.node π 0)) π 0
        refine ⟨_, .collection generated,
          fun path slot => if path = π then elementType else nodes path slot,
          fun θ agrees τIs agreeNodes => ?_⟩
        have elementIs : θ (.node π 0) = typeTerm elementType := by simpa using agreeNodes π 0 (List.suffix_refl π)
        intro q inside
        rcases List.mem_cons.mp inside with rfl | later
        · simp only [τIs, applyTerm_collectionTerm, unknown, Subst.applyTerm, elementIs]
          rfl
        · refine unifies θ agrees (by simpa [unknown, Subst.applyTerm] using elementIs)
            (fun path slot under => ?_) q later
          obtain ⟨i, -, below⟩ := under
          have notHere : path ≠ π := fun same => by
            subst same
            have := below.length_le
            simp at this
          simpa [notHere] using agreeNodes path slot ((List.suffix_cons _ _).trans below)
    | _, _, _, .collectionConstructor (rule := rule) member shape typed, ctx, τ, π => by
        obtain ⟨E, generated, nodes, unifies⟩ := elementsHaveType_complete typed ctx _ π 0
        refine ⟨_, .collectionConstructor member shape generated, nodes, fun θ agrees τIs agreeNodes => ?_⟩
        intro q inside
        rcases List.mem_cons.mp inside with rfl | later
        · simp only [τIs]
          rfl
        · exact unifies θ agrees (applyTerm_typeTerm θ _) (fun path slot under =>
            agreeNodes path slot (by obtain ⟨i, -, below⟩ := under; exact (List.suffix_cons _ _).trans below)) q later

  theorem elementsHaveType_complete {free : FreeTypeContext} :
      ∀ {Γ : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr},
      ElementsHaveType language free Γ elements elementType →
      ∀ (ctx : List TypeTerm) (τ : TypeTerm) (π : List ℕ) (index : ℕ),
        ∃ E, ElementsGenerate language elements τ ctx π index E ∧ ∃ nodes : List ℕ → ℕ → TypeExpr,
          ∀ θ : Subst typeSignature, Agrees free Γ ctx θ → θ.applyTerm τ = typeTerm elementType →
            (∀ path slot, (∃ i, index ≤ i ∧ (i :: π) <:+ path) → θ (.node path slot) = typeTerm (nodes path slot)) →
            Unifies θ E
    | _, _, _, .nil _ _, ctx, τ, π, index => ⟨[], .nil, fun _ _ => .base "", fun _ _ _ _ _ inside => nomatch inside⟩
    | _, _, _, .cons headTyped restTyped, ctx, τ, π, index => by
        obtain ⟨E₁, first, nodes₁, unifies₁⟩ := generates_complete headTyped ctx τ (index :: π)
        obtain ⟨E₂, second, nodes₂, unifies₂⟩ := elementsHaveType_complete restTyped ctx τ π (index + 1)
        refine ⟨_, .cons first second,
          fun path slot => if (index :: π) <:+ path then nodes₁ path slot else nodes₂ path slot,
          fun θ agrees τIs agreeNodes => ?_⟩
        intro q inside
        rcases List.mem_append.mp inside with inFirst | inSecond
        · refine unifies₁ θ agrees τIs (fun path slot under => ?_) q inFirst
          simpa [under] using agreeNodes path slot ⟨index, le_rfl, under⟩
        · refine unifies₂ θ agrees τIs (fun path slot later => ?_) q inSecond
          obtain ⟨i, above, under⟩ := later
          have notFirst : ¬ (index :: π) <:+ path := fun first => by
            have := suffix_heads first under
            omega
          simpa [notFirst] using agreeNodes path slot ⟨i, by omega, under⟩

  theorem argumentsHaveTypes_complete {free : FreeTypeContext} :
      ∀ {Γ : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free Γ arguments parameters →
      ∀ (ctx : List TypeTerm) (π : List ℕ) (index : ℕ),
        ∃ E, ArgumentsGenerate language arguments parameters ctx π index E ∧ ∃ nodes : List ℕ → ℕ → TypeExpr,
          ∀ θ : Subst typeSignature, Agrees free Γ ctx θ →
            (∀ path slot, (∃ i, index ≤ i ∧ (i :: π) <:+ path) → θ (.node path slot) = typeTerm (nodes path slot)) →
            Unifies θ E
    | _, _, _, .nil, ctx, π, index => ⟨[], .nil, fun _ _ => .base "", fun _ _ _ _ inside => nomatch inside⟩
    | _, _, _, .cons representation expectedIs headTyped restTyped, ctx, π, index => by
        obtain ⟨E₁, first, nodes₁, unifies₁⟩ := generates_complete headTyped ctx _ (index :: π)
        obtain ⟨E₂, second, nodes₂, unifies₂⟩ := argumentsHaveTypes_complete restTyped ctx π (index + 1)
        refine ⟨_, .cons representation expectedIs first second,
          fun path slot => if (index :: π) <:+ path then nodes₁ path slot else nodes₂ path slot,
          fun θ agrees agreeNodes => ?_⟩
        intro q inside
        rcases List.mem_append.mp inside with inFirst | inSecond
        · refine unifies₁ θ agrees (applyTerm_typeTerm θ _) (fun path slot under => ?_) q inFirst
          simpa [under] using agreeNodes path slot ⟨index, le_rfl, under⟩
        · refine unifies₂ θ agrees (fun path slot later => ?_) q inSecond
          obtain ⟨i, above, under⟩ := later
          have notFirst : ¬ (index :: π) <:+ path := fun first => by
            have := suffix_heads first under
            omega
          simpa [notFirst] using agreeNodes path slot ⟨i, by omega, under⟩
end

/-- **A pattern has a type under some contexts exactly when the equations it generates have a unifier.** -/
theorem typed_iff (p : Pattern) (T : TypeExpr) :
    (∃ E, Generates language p (typeTerm T) [] [] E ∧ ∃ θ : Subst typeSignature, Unifies θ E) ↔
      ∃ (free : FreeTypeContext) (bound : List TypeExpr), HasType language free bound p T := by
  constructor
  · rintro ⟨E, generated, θ, unified⟩
    obtain ⟨bound, below⟩ := indicesBelow_exists p
    have typed := generates_sound θ bound generated unified below
    simp only [List.map_nil, List.nil_append, decodeUnder, applyTerm_typeTerm, decodeType_typeTerm] at typed
    exact ⟨_, _, typed⟩
  · rintro ⟨free, bound, typed⟩
    obtain ⟨E, generated, nodes, unifies⟩ := generates_complete typed [] (typeTerm T) []
    refine ⟨E, generated, fun u => match u with
      | .free name => typeTerm ((free name).getD (.base ""))
      | .loose j => typeTerm (boundAt bound j)
      | .node path slot => typeTerm (nodes path slot), unifies _ ?_ (applyTerm_typeTerm _ T) fun _ _ _ => rfl⟩
    refine ⟨by simp, fun i _ _ inside => absurd inside (by simp), fun j type found => ?_, fun name type found => ?_⟩
    · simp only [List.length_nil, Nat.zero_add] at found
      simp [boundAt, found]
    · simp [found]

end Mettapedia.GSLT.Compilation.Uniform.TypingUnknowns

#print axioms Mettapedia.GSLT.Compilation.Uniform.TypingUnknowns.typed_iff
